"""Report the strong-path control without mixing its target with the earlier toy."""
from collections import defaultdict
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

import report_row_cap_grid as shared
from validate import read_runs


FLOOR = 1e-12


def plot(out, phase, groups, baselines, known, n):
    fig, axes = plt.subplots(1, 2, figsize=(12.5, 5.4))
    for ax, axis in zip(axes, ('Q', 'T')):
        complete = [r for rows in groups.values() for r in rows if not r['censored']]
        limit = max([r[axis] for r in complete]+[known['Q']])*1.08
        for variant, rows in groups.items():
            local = [r for r in rows if not r['censored']]
            ax.scatter([r[axis] for r in local], [max(FLOOR, r['KL']) for r in local],
                       color=shared.COLORS[variant], marker='o' if variant == 'reference' else '^',
                       label='Row discard' if variant == 'reference' else 'Keep top-d', s=29, alpha=.65)
        for policy, color, style in (('random', '#333333', '--'), ('confidence', '#9959ac', ':')):
            by_budget = defaultdict(list)
            for row in baselines:
                if row['baseline'] == policy and row['budget'] <= limit:
                    by_budget[row['budget']].append(row['kl_per_token'])
            points = shared.averaged([(q, float(np.mean(v))) for q, v in by_budget.items()])
            if points:
                ax.plot([x for x, _ in points], [max(FLOOR, y) for _, y in points], style, color=color, label=policy)
        ax.scatter([known['Q']], [max(FLOOR, known['KL'])], color='#218468', marker='s', s=55,
                   label='Known path: extra graph information', zorder=5)
        right_edge = known['Q'] > .75*limit
        ax.annotate(f'Known path: {known["Q"]:g} queries', (known['Q'], max(FLOOR, known['KL'])),
                    xytext=(-8 if right_edge else 8, 10), ha='right' if right_edge else 'left',
                    textcoords='offset points', fontsize=8, color='#218468')
        ax.set(xlabel='Mean total queries Q' if axis == 'Q' else 'Mean sequential depth T',
               ylabel='Mean conditional KL / token (nats)', xlim=(0, limit), yscale='log', ylim=(FLOOR*.7, None))
        ax.grid(alpha=.18)
    fig.legend(*axes[0].get_legend_handles_labels(), loc='lower center', ncol=3, fontsize=9)
    fig.suptitle(f'Strong path | theta = 0.25 | h uniform [-1, 1] | N = {n:,} | {phase}', fontsize=13)
    fig.text(.5, .115, 'Completed settings only; censored runs are separate. Values below 1e-12 share the plot floor.', ha='center', fontsize=8)
    fig.tight_layout(rect=(0, .15, 1, .94))
    for ext in ('png', 'svg'):
        fig.savefig(out/f'{phase}_tradeoff.{ext}', dpi=160, bbox_inches='tight')
    plt.close(fig)


def report(out):
    out = Path(out)
    config = json.loads((out/'design.json').read_text())
    known_rows = read_runs(out/'known_graph'/'runs.jsonl')
    all_pairs = {}
    for phase in ('explore', 'confirm'):
        groups = {v: shared.aggregate(read_runs(out/phase/v/'proposal_runs.jsonl')) for v in shared.COLORS}
        pairs = shared.pair_rows(groups)
        all_pairs[phase] = pairs
        shared.write_csv(out/f'{phase}_paired.csv', pairs)
        shared.write_csv(out/f'{phase}_censored.csv', [r for r in pairs if not r['both_complete']])
        (out/f'{phase}_aggregates.json').write_text(json.dumps(groups, indent=2, allow_nan=False)+'\n')
        seeds = config['explore_seeds'] if phase == 'explore' else config['confirm_seeds']
        known = [r for r in known_rows if r['repeat'] in seeds]
        proposals = {v: read_runs(out/phase/v/'proposal_runs.jsonl') for v in groups}
        lookup = {r['repeat']: r for r in known}
        for rows in proposals.values():
            for row in rows:
                for key in ('edges_sha256', 'weights_sha256', 'fields_sha256'):
                    assert row[key] == lookup[row['repeat']][key]
                assert row['case'] == config['target_law'] and not row['weak_tail'] and row['sigma'] is None
        mean_known = {'Q': float(np.mean([r['total'] for r in known])),
                      'KL': float(np.mean([r['kl_per_token'] for r in known]))}
        plot(out, phase, groups, read_runs(out/phase/'baselines'/'baseline_runs.jsonl'), mean_known, config['n'])
    shared.write_csv(out/'known_graph.csv', [{k: r[k] for k in ('repeat', 'total', 'depth', 'kl_per_token', 'unsafe_batches', 'information')}
                                           for r in known_rows])
    lines = ['# 強依存pathの対照実験', '',
        f'N={config["n"]:,}・全辺theta=0.25・h=Uniform[-1,1]・厳密oracle・first-bank draft・J=1・TV閾値0.001なのじゃ。',
        '探索seed 0でp/M/dを振り、両版の候補と固定対照を選抜してからseed 10/11で確認したのじゃ。Q≤N打切りは別表なのじゃ。',
        '真のpath順序はランダムに隠したのじゃ。既知graphのcentroidだけは真の隣接情報を無償で与える診断用参考値なのじゃ。', '',
        '[探索の図](explore_tradeoff.png)・[確認とbaselineの図](confirm_tradeoff.png)・[既知graph参考値](known_graph.csv)',
        '[探索全対応](explore_paired.csv)・[確認全対応](confirm_paired.csv)・[探索打切り](explore_censored.csv)・[確認打切り](confirm_censored.csv)', '',
        '| phase | 対応設定数 | 両版完走 | KL改善 / 悪化 / 同じ（1e-12 floor） |', '|---|---:|---:|---|']
    for phase, pairs in all_pairs.items():
        complete = [r for r in pairs if r['both_complete']]
        ratios = [r['KL_ratio_reference_over_topd_floor1e12'] for r in complete]
        wins, losses = sum(r > 1 for r in ratios), sum(r < 1 for r in ratios)
        lines.append(f'| {phase} | {len(pairs)} | {len(complete)} | {wins} / {losses} / {len(ratios)-wins-losses} |')
    lines += ['', '同じハイパラでのKL改善と、同じqueryでの優位性は別なのじゃ。対応CSVのQ・screen・peel・repair・cycleと、確認のbaseline比較を併せて読むのじゃ。',
              'これは強依存の動作確認であり、以前のDocREDを目安にした弱辺targetでの改善を意味しないのじゃ。',
              '図・レポートは自動出力で、実行後の解釈と図の確認はまだ行っていないのじゃ。', '']
    (out/'report_ja.md').write_text('\n'.join(lines))


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    report(parser.parse_args().output)
