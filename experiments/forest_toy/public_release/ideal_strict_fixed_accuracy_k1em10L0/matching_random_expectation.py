"""Exact schedule-averaged KL for balanced random batches on a matching.

An edge contributes its initial reverse pair KL exactly when both endpoints
are committed together. Averaging uniformly over permutations gives the
same-batch probability sum_b s_b(s_b-1)/(N(N-1)). Values sampled elsewhere
cannot affect an unresolved matching component. This is a passive diagnostic.
"""
from itertools import permutations
import json
from math import fsum

import numpy as np

from explore_minimal import OUTPUT
from validate import digest, read_runs


def same_batch_probability(n, batches):
    if not 1 <= batches <= n or n < 2:
        raise ValueError('Please use N>=2 and 1<=B<=N.')
    small, extra = divmod(n, batches)
    numerator = extra*(small+1)*small+(batches-extra)*small*(small-1)
    return numerator/(n*(n-1))


def enumeration_check():
    """Please independently enumerate all six-token schedules to check the formula."""
    n, edges, weights = 6, [(0, 1), (2, 3), (4, 5)], [.2, .5, .8]
    errors = []
    for batches in range(1, n+1):
        small, extra = divmod(n, batches)
        costs = []
        for order in permutations(range(n)):
            membership, start = {}, 0
            for step in range(batches):
                size = small+(step < extra)
                for vertex in order[start:start+size]:
                    membership[vertex] = step
                start += size
            costs.append(fsum(w for (u, v), w in zip(edges, weights) if membership[u] == membership[v])/n)
        enumerated = fsum(costs)/len(costs)
        formula = fsum(weights)/n*same_batch_probability(n, batches)
        errors.append(abs(enumerated-formula))
    assert max(errors) < 1e-15
    return {'N': n, 'all_permutations_per_budget': 720, 'budgets_checked': 6,
            'maximum_absolute_error': max(errors)}


def main():
    result = {'formula': 'E_random KL/token = (sum initial_edge_kl / N) * sum_b size_b(size_b-1)/(N(N-1))',
              'scope': 'Matching only. Exact over all random balanced partitions and sample values, conditional on each fixed target. Average across the saved target seeds only.',
              'enumeration_check': enumeration_check(), 'stages': {}}
    for stage in ('coarse_n4096', 'confirm_n16384'):
        output = OUTPUT/stage
        profiles = [r for r in json.loads((output/'target_profiles.json').read_text()) if r['target'] == 'matching']
        n = profiles[0]['n']
        baselines = [r for r in read_runs(output/'baseline_runs.jsonl') if r['target'] == 'matching']
        budgets = sorted({r['budget'] for r in baselines} | set(np.geomspace(1, n, 200).round().astype(int)))
        mass = []
        for p in profiles:
            with np.load(output/p['snapshot']) as data:
                mass.append(fsum(data['initial_edge_kl'])/n)
        result['stages'][stage] = {'n': n, 'repeat_ids': [p['repeat'] for p in profiles],
            'all_at_once_kl_per_token': mass,
            'target_profile_sha256': digest(output/'target_profiles.json'),
            'points': [{'budget': int(b), 'mean': float(np.mean(mass))*same_batch_probability(n, int(b)),
                        'individual': [x*same_batch_probability(n, int(b)) for x in mass]}
                       for b in budgets]}
    (OUTPUT/'matching_random_expectation.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'verification': result['enumeration_check'],
                      'confirm_initial_KL_per_token': result['stages']['confirm_n16384']['all_at_once_kl_per_token']}))


if __name__ == '__main__':
    main()
