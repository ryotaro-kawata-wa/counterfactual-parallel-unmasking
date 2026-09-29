"""Write all paired outcomes and candidate curves after the background grid."""
from collections import defaultdict
import csv
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

import explore_minimal as base
from validate import read_runs


FLOOR = 1e-12
COLORS = {'reference': '#355caa', 'topd': '#df8331'}


def write_csv(path, rows):
    if not rows:
        path.write_text('')
        return
    with path.open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=sorted({k for r in rows for k in r}))
        writer.writeheader()
        writer.writerows(rows)


def aggregate(rows):
    groups, result = defaultdict(list), []
    for row in rows:
        groups[base.setting_key(row)].append(row)
    for key, group in sorted(groups.items()):
        group.sort(key=lambda r: r['repeat'])
        item = dict(zip(('target', 'p', 'M', 'd', 'TV'), key))
        complete = all(r['status'] == 'complete' for r in group)
        item.update(key=key, seeds=[r['repeat'] for r in group],
                    censored=sum(r['status'] != 'complete' for r in group),
                    Q=float(np.mean([r['total'] for r in group])),
                    Q_median=float(np.median([r['total'] for r in group])),
                    Q_p90=float(np.quantile([r['total'] for r in group], .9)),
                    T=float(np.mean([r['depth'] for r in group])),
                    KL=float(np.mean([r['kl_per_token'] for r in group])) if complete else None,
                    Qcf=float(np.mean([r['counterfactual'] for r in group])),
                    seconds=float(np.mean([r['seconds'] for r in group])),
                    screens=float(np.mean([r['screen_calls'] for r in group])))
        for name in ('peel', 'repair', 'centroid', 'fallback'):
            item[name] = float(np.mean([r['repair_diagnostics']['roles'].get(name, 0) for r in group]))
        for name, section, field in (
                ('first_cycles', 'strength_diagnostics', 'cycle_rank'),
                ('first_false_edges', 'strength_diagnostics', 'false_edges'),
                ('first_kl_recall', 'initial_kl_diagnostics', 'kl_recall')):
            values = [r[section]['stages'][0][field] for r in group if r[section]['stages']]
            item[name] = float(np.mean(values)) if len(values) == len(group) and None not in values else None
        result.append(item)
    return result


def pair_rows(groups):
    lookup = {tuple(r['key']): r for r in groups['reference']}
    pairs = []
    for b in groups['topd']:
        a = lookup[tuple(b['key'])]
        row = {k: b[k] for k in ('target', 'p', 'M', 'd', 'TV')}
        row['both_complete'] = not (a['censored'] or b['censored'])
        for name in ('Q', 'Q_median', 'Q_p90', 'T', 'KL', 'Qcf', 'seconds', 'screens',
                     'peel', 'repair', 'centroid', 'fallback', 'first_cycles',
                     'first_false_edges', 'first_kl_recall', 'censored'):
            row['reference_'+name], row['topd_'+name] = a[name], b[name]
        row['Q_ratio_topd_over_reference'] = b['Q']/a['Q']
        row['KL_ratio_reference_over_topd_floor1e12'] = (
            max(FLOOR, a['KL'])/max(FLOOR, b['KL']) if row['both_complete'] else None)
        pairs.append(row)
    return pairs


def averaged(points):
    """Please merge nearby x values arithmetically before joining baseline points."""
    groups = []
    for point in sorted(points):
        if not groups or point[0] > 1.02*groups[-1][0][0]:
            groups.append([])
        groups[-1].append(point)
    return [(float(np.mean([x for x, _ in g])), float(np.mean([y for _, y in g]))) for g in groups]


def plot(out, phase, groups, baselines, axis):
    fig, axes = plt.subplots(1, 2, figsize=(12, 5.2))
    for ax, target in zip(axes, ('matching', 'path')):
        for variant, rows in groups.items():
            local = [r for r in rows if r['target'] == target and not r['censored']]
            ax.scatter([r[axis] for r in local], [max(FLOOR, r['KL']) for r in local],
                       s=22, alpha=.6, color=COLORS[variant],
                       marker='o' if variant == 'reference' else '^', label=variant)
        for policy, color, style in (('random', '#333333', '--'), ('confidence', '#9959ac', ':')):
            by_budget = defaultdict(list)
            for row in baselines:
                if row['target'] == target and row['baseline'] == policy:
                    by_budget[row['budget']].append(row['kl_per_token'])
            raw = [(q, float(np.mean(values))) for q, values in by_budget.items()]
            points = averaged(raw)
            if points:
                ax.scatter([x for x, _ in raw], [max(FLOOR, y) for _, y in raw], color=color, s=7, alpha=.18)
                ax.plot([x for x, _ in points], [max(FLOOR, y) for _, y in points], style, color=color, label=policy)
        ax.set(title=target.capitalize(), xlabel='Mean total queries Q' if axis == 'Q' else 'Mean sequential depth T',
               ylabel='Mean conditional KL / token (nats)', yscale='log', ylim=(FLOOR*.75, None))
        ax.set_xlim(left=0)
        if not any(r['target'] == target and not r['censored'] for rows in groups.values() for r in rows):
            ax.text(.5, .5, 'No complete setting', transform=ax.transAxes, ha='center')
        ax.grid(alpha=.18)
    legend = {}
    for ax in axes:
        handles, labels = ax.get_legend_handles_labels()
        legend.update(zip(labels, handles))
    fig.legend(list(legend.values()), list(legend), loc='lower center', ncol=4)
    fig.suptitle(f'Keep top-d vs row discard | {phase} | first-bank draft', fontsize=14)
    fig.text(.5, .08, 'All completed settings; censored runs are separate. Values below 1e-12 share the plot floor.', ha='center', fontsize=8)
    fig.tight_layout(rect=(0, .12, 1, .93))
    for ext in ('png', 'svg'):
        fig.savefig(out/f'{phase}_{axis}.{ext}', dpi=160, bbox_inches='tight')
    plt.close(fig)


def report(out):
    out = Path(out)
    design = json.loads((out/'design.json').read_text())
    all_pairs = {}
    for phase in ('explore', 'confirm'):
        groups = {v: aggregate(read_runs(out/phase/v/'proposal_runs.jsonl')) for v in COLORS}
        pairs = pair_rows(groups)
        all_pairs[phase] = pairs
        write_csv(out/f'{phase}_paired.csv', pairs)
        write_csv(out/f'{phase}_censored.csv', [r for r in pairs if not r['both_complete']])
        with (out/f'{phase}_aggregates.json').open('w') as stream:
            json.dump(groups, stream, indent=2, allow_nan=False)
        baselines = read_runs(out/phase/'baselines'/'baseline_runs.jsonl')
        plot(out, phase, groups, baselines, 'Q')
        if phase == 'confirm':
            plot(out, phase, groups, baselines, 'T')
    lines = ['# Keep top-dのparameter探索', '',
             f'N={design["n"]:,}、first-bank draft・J=1・target固定で旧row全破棄とtop-dを比較したのじゃ。',
             'Q=3,000は打切りにも選抜上限にも使っていないのじゃ。Q≤Nで停止したrunはKLを補完せず別表へ残したのじゃ。',
             '探索はseed 0、選抜を固定した後の確認はseed 10/11なのじゃ。少数seedのPDCA結果であり、全設定での改善保証ではないのじゃ。',
             '確認候補には両版の精度・コスト候補、改善比の最大・最小例、前回の固定7設定を含めたのじゃ。', '',
             '[探索全点](explore_Q.png)・[確認と同予算baseline](confirm_Q.png)・[逐次T](confirm_T.png)', '',
             '[探索の全対応比較](explore_paired.csv)・[確認の全対応比較](confirm_paired.csv)・[探索の打切り](explore_censored.csv)・[確認の打切り](confirm_censored.csv)', '',
             '図のproposalは異なるハイパラを線で結ばず全点を表示したのじゃ。baselineは同じ予算のseed平均を先に取り、2%以内の近接xを算術平均して結んだのじゃ。rawの値は保存してあるのじゃ。', '',
             '| phase | target | 対応設定数 | 両版完走 | top-dのKLが小さい / 大きい / 同じ（1e-12 floor） | QもKLも増えない設定 |',
             '|---|---|---:|---:|---|---:|']
    for phase, pairs in all_pairs.items():
        for target in ('matching', 'path'):
            local = [r for r in pairs if r['target'] == target]
            complete = [r for r in local if r['both_complete']]
            ratios = [r['KL_ratio_reference_over_topd_floor1e12'] for r in complete]
            wins, losses = sum(v > 1 for v in ratios), sum(v < 1 for v in ratios)
            dominates = sum(r['topd_Q'] <= r['reference_Q'] and max(FLOOR, r['topd_KL']) <= max(FLOOR, r['reference_KL'])
                            for r in complete)
            lines.append(f'| {phase} | {target} | {len(local)} | {len(complete)} | {wins} / {losses} / {len(ratios)-wins-losses} | {dominates} |')
    lines += ['', '「KLが小さい設定数」は同じハイパラでの比較であり、同じqueryでの優位性を意味しないのじゃ。Q比・再screen・cycle・repair・強辺KL mass保持率を対応CSVで併せて確認するのじゃ。',
              '全対応の初回raw vote・target hash一致と、overflowがない対照の不変性は各phaseのpaired_audit.jsonで機械検証したのじゃ。',
              'このレポートと図はジョブの自動出力で、実行後の人手による図の確認・結果の解釈はまだ行っていないのじゃ。', '']
    (out/'report_ja.md').write_text('\n'.join(lines))


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    report(parser.parse_args().output)
