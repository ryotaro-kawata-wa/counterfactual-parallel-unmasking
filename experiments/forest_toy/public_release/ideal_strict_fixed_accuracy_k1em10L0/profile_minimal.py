"""Freeze data-only unary calibration and describe the resulting target laws."""
import hashlib
import json
from pathlib import Path

import numpy as np

from minimal_oracle import ChainEvaluator, make_target

ROOT = Path(__file__).parent
OUTPUT = ROOT/'results'/'minimal_pilot'
SIGMA = 8.85
LEVELS = (.1, .25, .5, .75, .9, .95, .99)


def weighted_summary(groups):
    values = np.concatenate([np.asarray(x) for x in groups])
    weights = np.concatenate([np.full(len(x), 1/len(x)/len(groups)) for x in groups])
    order = np.argsort(values, kind='stable')
    cdf = np.cumsum(weights[order])
    return {'count': len(values), 'mean': float(np.dot(values, weights)),
            'min': float(values.min()), 'max': float(values.max()),
            'quantiles': {str(q): float(values[order[min(np.searchsorted(cdf, q), len(values)-1)]])
                          for q in LEVELS},
            'fraction_ge': {str(q): float(weights[values >= q].sum()) for q in (.95, .99, .999)},
            'fraction_lt_001': float(weights[values < .001].sum())}


def initial_edges(oracle):
    evaluator = ChainEvaluator(oracle)
    total, rows, costs = evaluator.evaluate(np.full(oracle.n, -1), np.arange(oracle.n))
    # Please map chain-adjacent pair KL back to the canonical hidden edge order.
    by_edge = {}
    for i in range(1, oracle.n):
        if evaluator.strengths[i-1] != 0:
            u, v = int(evaluator.order[i-1]), int(evaluator.order[i])
            by_edge[tuple(sorted((u, v)))] = costs[v]
    weights = np.array([by_edge.get(tuple(map(int, e)), 0.) for e in oracle.edges])
    return rows, weights, total


def main():
    data = json.loads((OUTPUT/'data_profile_input.json').read_text())
    confidence = weighted_summary([x['confidence'] for x in data['docs'].values()])
    edge = weighted_summary(list(data['edge_weights'].values()))
    median = confidence['quantiles']['0.5']
    t = (-.5+np.sqrt(4/median-3.75))/2
    fitted = float(-np.log(t)/.6744897501960817)
    profile = {'calibration': {'sigma': SIGMA, 'unrounded_sigma': fitted,
                 'criterion': 'Match the DocRED document-equal median initial confidence with the '
                              'uncoupled unary model; round sigma to two decimals, without sampler outcomes.',
                 'confidence_definition': 'Maximum individual-token conditional probability.',
                 'unary': 'mu_i proportional to (.4 exp(h_i), .4 exp(-h_i), .2); h_i iid Normal(0,sigma^2). '
                          'The third probability is spread uniformly over V-2 tail tokens.',
                 'limitations': 'Only median confidence is calibrated. Coupled marginal quantiles, entropy, '
                                'and strong edge-KL tails need not match DocRED. No oracle noise is added.'},
               'docred': {'documents': len(data['docs']), 'confidence': confidence, 'edge_kl': edge,
                          'entropy': None, 'entropy_reason': 'Full initial rows are not in the saved trace.',
                          'source_sha256': data['source_sha256']}, 'targets': []}
    for target in ('matching', 'path'):
        for biased in (False, True):
            for tail in (False, True):
                for repeat in range(2):
                    oracle, _ = make_target(target, 16384, repeat, biased, tail, SIGMA)
                    rows, weights, total = initial_edges(oracle)
                    path = OUTPUT/'target_profiles'/f'{target}_bias{int(biased)}_tail{int(tail)}_seed{repeat}.npz'
                    path.parent.mkdir(parents=True, exist_ok=True)
                    np.savez_compressed(path, edges=oracle.edges, theta=oracle.edge_strengths,
                                        fields=oracle.fields, initial_rows=rows, initial_edge_kl=weights)
                    profile['targets'].append({'target': target, 'biased': biased, 'weak_tail': tail,
                        'repeat': repeat, 'n': oracle.n, 'sigma': SIGMA if biased else 0.,
                        'tail_shape_b': oracle.tail_shape, 'log_z': oracle.log_z,
                        'confidence': weighted_summary([rows[:, :2].max(axis=1)]),
                        'theta': weighted_summary([oracle.edge_strengths]),
                        'edge_kl': weighted_summary([weights]), 'all_at_once_kl': total,
                        'all_at_once_kl_per_token': total/oracle.n,
                        'entropy_mean': float(np.mean(-np.sum(rows*np.log(rows), axis=1)+
                                                      rows[:, 2]*np.log(oracle.vocab-2))),
                        'snapshot': str(path.relative_to(OUTPUT))})
    (OUTPUT/'data_profile.json').write_text(json.dumps(profile, indent=2, allow_nan=False)+'\n')
    print(json.dumps({'sigma': SIGMA, 'docred_median': median,
                      'targets': [{k: x[k] for k in ('target', 'biased', 'weak_tail', 'repeat',
                                 'all_at_once_kl_per_token')} for x in profile['targets']]}, indent=2))


if __name__ == '__main__':
    main()
