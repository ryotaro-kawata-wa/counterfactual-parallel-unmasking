"""Report local hyperparameter robustness and the crossed target/RNG control."""
from collections import defaultdict
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import LogNorm, Normalize
import numpy as np

import explore_minimal as base
import report_row_cap_grid as shared
from validate import read_runs


FLOOR = 1e-12
LABELS = {'reference': 'Row discard', 'topd': 'Keep top-d'}


def exact_run(row):
    return (row['status'] == 'complete' and row['kl_per_token'] <= FLOOR
            and row['unsafe_batches'] == 0 and not row.get('fallback'))


def aggregate(rows):
    lookup = defaultdict(list)
    for row in rows:
        lookup[base.setting_key(row)].append(row)
    result = shared.aggregate(rows)
    for item in result:
        group = lookup[tuple(item['key'])]
        item.update(runs=len(group), exact_runs=sum(exact_run(r) for r in group),
                    fallback_runs=sum(bool(r.get('fallback')) for r in group),
                    complete_runs=sum(r['status'] == 'complete' for r in group))
        for field in ('data_repeat', 'algorithm_repeat'):
            item[field+'s'] = [r[field] for r in group]
    return result


def save_figure(fig, out, name):
    for ext in ('png', 'svg'):
        fig.savefig(out/f'{name}.{ext}', dpi=160, bbox_inches='tight')
    plt.close(fig)


def pivot_plot(out, rows_by_variant):
    data = sorted({r['data_repeat'] for r in rows_by_variant['topd']})
    algorithms = sorted({r['algorithm_repeat'] for r in rows_by_variant['topd']})
    values = [r['total'] for rows in rows_by_variant.values() for r in rows]
    low, high = min(values), max(values)
    norm = Normalize(low-.5 if low == high else low, high+.5 if low == high else high)
    fig, axes = plt.subplots(1, 2, figsize=(9, max(3.7, 1.0*len(data)+1.4)))
    for ax, variant in zip(axes, LABELS):
        lookup = {(r['data_repeat'], r['algorithm_repeat']): r for r in rows_by_variant[variant]}
        matrix = np.array([[lookup[d, a]['total'] for a in algorithms] for d in data])
        picture = ax.imshow(matrix, aspect='auto', cmap='Blues', norm=norm)
        for y, d in enumerate(data):
            for x, a in enumerate(algorithms):
                row = lookup[d, a]
                error = f'KL={row["kl_per_token"]:.2g}' if row['status'] == 'complete' else 'CENSORED'
                if row.get('fallback'):
                    error += ' / fallback'
                ax.text(x, y, f'Q={row["total"]}\n{error}', ha='center', va='center', fontsize=9,
                        color='white' if norm(row['total']) > .65 else '#222222')
        ax.set(xticks=range(len(algorithms)), xticklabels=algorithms, xlabel='Algorithm repeat',
               yticks=range(len(data)), yticklabels=data, ylabel='Target repeat', title=LABELS[variant])
    fig.suptitle('Fixed pivot: target repeats crossed with algorithm repeats', fontsize=12)
    fig.tight_layout(rect=(0, 0, .9, .95))
    bar_ax = fig.add_axes([.92, .16, .018, .64])
    fig.colorbar(picture, cax=bar_ax, label='Total Q')
    save_figure(fig, out, 'pivot_seeds')


def grid_plot(out, groups):
    local = {v: [r for r in rows if r['d'] == 18 and r['TV'] == .001]
             for v, rows in groups.items()}
    palettes = sorted({r['p'] for rows in local.values() for r in rows})
    counts = sorted({r['M'] for rows in local.values() for r in rows})
    fig, axes = plt.subplots(2, 3, figsize=(13, 7))
    costs = [r['Q'] for rows in local.values() for r in rows]
    norms = [Normalize(0, max(costs)), LogNorm(FLOOR, .1), Normalize(0, 1)]
    for y, variant in enumerate(LABELS):
        lookup = {(r['p'], r['M']): r for r in local[variant]}
        for col, metric in enumerate(('Q', 'KL', 'exact_fraction')):
            ax = axes[y, col]
            matrix = np.full((len(palettes), len(counts)), np.nan)
            for iy, p in enumerate(palettes):
                for ix, m in enumerate(counts):
                    row = lookup.get((p, m))
                    if row is None:
                        continue
                    value = row['exact_runs']/row['runs'] if metric == 'exact_fraction' else row[metric]
                    if value is not None:
                        matrix[iy, ix] = max(FLOOR, value) if metric == 'KL' else value
                    text = (f'{row["exact_runs"]}/{row["runs"]}' if metric == 'exact_fraction'
                            else f'{value:.2g}' if metric == 'KL' and value is not None
                            else f'{value:.0f}' if value is not None else 'C')
                    if row['censored'] and metric == 'Q':
                        text += '*'
                    ax.text(ix, iy, text, ha='center', va='center', fontsize=8, zorder=3)
            cmap = plt.get_cmap('YlOrRd' if metric != 'exact_fraction' else 'YlGn').copy()
            cmap.set_bad('#dddddd')
            picture = ax.imshow(matrix, aspect='auto', cmap=cmap, norm=norms[col], alpha=.68)
            ax.set(xticks=range(len(counts)), xticklabels=counts, xlabel='M',
                   yticks=range(len(palettes)), yticklabels=palettes, ylabel='p',
                   title=LABELS[variant]+' | '+('Mean KL/token' if metric == 'KL' else
                         'Exact structural runs' if metric == 'exact_fraction' else 'Mean Q'))
            fig.colorbar(picture, ax=ax, shrink=.8)
    fig.suptitle('Local p/M exploration | d=18 | TV=0.001', fontsize=13)
    fig.text(.5, .025, 'C: at least one censored run; *: capped cost included. Exact: KL<=1e-12, no unsafe batch, no fallback.',
             ha='center', fontsize=9)
    fig.tight_layout(rect=(0, .06, 1, .94))
    save_figure(fig, out, 'explore_p_M')


def sweeps_plot(out, groups):
    fig, axes = plt.subplots(2, 2, figsize=(11, 7))
    for variant, rows in groups.items():
        style = '--' if variant == 'reference' else '-'
        local = sorted([r for r in rows if r['p'] == 8 and r['M'] == 53 and r['TV'] == .001], key=lambda r: r['d'])
        for ax, metric in zip(axes[0], ('Q', 'KL')):
            ax.plot([r['d'] for r in local], [r[metric] if metric == 'Q' else
                    max(FLOOR, r['KL']) if r['KL'] is not None else np.nan for r in local],
                    style+'o', color=shared.COLORS[variant], label=LABELS[variant], markersize=4)
        for m, color in ((45, '#2980b9'), (53, '#d47b20'), (61, '#2c9c70')):
            local = sorted([r for r in rows if r['p'] == 8 and r['M'] == m and r['d'] == 18], key=lambda r: r['TV'])
            for ax, metric in zip(axes[1], ('Q', 'KL')):
                ax.plot([r['TV'] for r in local], [r[metric] if metric == 'Q' else
                        max(FLOOR, r['KL']) if r['KL'] is not None else np.nan for r in local],
                        style+'o', color=color, label=f'M={m} / {LABELS[variant]}', markersize=4)
    for ax in axes.flat:
        ax.grid(alpha=.18)
    for ax in axes[0]:
        ax.set(xlabel='d', title='p=8, M=53, TV=0.001')
    for ax in axes[1]:
        ax.set(xlabel='TV threshold', xscale='log', title='p=8, d=18')
    for ax in axes[:, 0]:
        ax.set_ylabel('Mean total Q (capped costs included)')
    for ax in axes[:, 1]:
        ax.set(ylabel='Mean conditional KL/token', yscale='log', ylim=(FLOOR*.7, None))
    axes[0, 0].legend(fontsize=8)
    axes[1, 0].legend(fontsize=7, ncol=2)
    fig.suptitle('Sensitivity to d and TV threshold | exploratory pairs', fontsize=13)
    fig.text(.5, .025, 'KL is omitted if any run was censored. Values below 1e-12 share the plot floor.', ha='center', fontsize=9)
    fig.tight_layout(rect=(0, .06, 1, .94))
    save_figure(fig, out, 'explore_d_TV')


def tradeoff(out, phase, groups, baselines, pivot):
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))
    for ax, metric in zip(axes, ('Q', 'T')):
        completed = [r for rows in groups.values() for r in rows if not r['censored']]
        limit = 1.08*max([r[metric] for r in completed] or [1])
        errors = [r['KL'] for r in completed]
        annotated = set()
        for variant, rows in groups.items():
            complete = [r for r in rows if not r['censored']]
            ax.scatter([r[metric] for r in complete], [max(FLOOR, r['KL']) for r in complete],
                       marker='o' if variant == 'reference' else '^', color=shared.COLORS[variant],
                       label=LABELS[variant], s=36, alpha=.65)
            for row in complete:
                position = (row[metric], max(FLOOR, row['KL']))
                if tuple(row['key']) == tuple(pivot) and position not in annotated:
                    ax.annotate('pivot', (row[metric], max(FLOOR, row['KL'])), xytext=(8, 10),
                                textcoords='offset points', fontsize=9)
                    annotated.add(position)
        for policy, color, style in (('random', '#333333', '--'), ('confidence', '#9959ac', ':')):
            by_budget = defaultdict(list)
            for row in baselines:
                if row['baseline'] == policy and row['budget'] <= limit:
                    by_budget[row['budget']].append(row['kl_per_token'])
            points = shared.averaged([(q, float(np.mean(v))) for q, v in by_budget.items()])
            errors.extend(point[1] for point in points)
            if points:
                ax.plot([p[0] for p in points], [max(FLOOR, p[1]) for p in points], style+'o',
                        color=color, label=policy, markersize=3)
        ax.set(xlabel='Mean total Q' if metric == 'Q' else 'Mean sequential depth T',
               ylabel='Mean conditional KL/token (nats)', yscale='log',
               ylim=(FLOOR*.7, max([FLOOR*10]+[e*5 for e in errors])), xlim=(0, limit))
        ax.grid(alpha=.18)
    fig.legend(*axes[0].get_legend_handles_labels(), loc='lower center', ncol=4, fontsize=9)
    fig.suptitle(f'Strong-path robustness | {phase} | completed settings', fontsize=13)
    fig.text(.5, .10, 'Baseline curves merge nearby Q arithmetically; censored settings are reported separately.', ha='center', fontsize=8)
    fig.tight_layout(rect=(0, .14, 1, .94))
    save_figure(fig, out, phase+'_tradeoff')


def report(out):
    out = Path(out)
    config = json.loads((out/'design.json').read_text())
    all_groups, all_records = {}, {}
    for phase in ('pivot', 'explore', 'confirm'):
        records = {v: read_runs(out/phase/v/'proposal_runs.jsonl') for v in LABELS}
        groups = {v: aggregate(rows) for v, rows in records.items()}
        all_groups[phase], all_records[phase] = groups, records
        paired = shared.pair_rows(groups)
        shared.write_csv(out/f'{phase}_paired.csv', paired)
        shared.write_csv(out/f'{phase}_censored.csv', [r for r in paired if not r['both_complete']])
        (out/f'{phase}_aggregates.json').write_text(json.dumps(groups, indent=2, allow_nan=False)+'\n')
        shared.write_csv(out/f'{phase}_summary.csv', [dict(variant=v, **r) for v, rows in groups.items() for r in rows])
        if phase != 'explore':
            tradeoff(out, phase, groups, read_runs(out/phase/'baselines'/'baseline_runs.jsonl'), config['pivot'])
    fields = ('data_repeat', 'algorithm_repeat', 'status', 'total', 'depth', 'kl_per_token', 'unsafe_batches', 'fallback')
    shared.write_csv(out/'pivot_individual.csv', [dict(variant=v, **{k: row.get(k) for k in fields})
                     for v, rows in all_records['pivot'].items() for row in rows])
    per_target = []
    for variant, rows in all_records['pivot'].items():
        for data in sorted({r['data_repeat'] for r in rows}):
            local = [r for r in rows if r['data_repeat'] == data]
            per_target.append({'variant': variant, 'data_repeat': data, 'runs': len(local),
                'Q_mean': float(np.mean([r['total'] for r in local])),
                'Q_algorithm_range': max(r['total'] for r in local)-min(r['total'] for r in local),
                'exact_runs': sum(exact_run(r) for r in local),
                'KL_mean': float(np.mean([r['kl_per_token'] for r in local])) if all(r['status'] == 'complete' for r in local) else None})
    shared.write_csv(out/'pivot_by_target.csv', per_target)
    pivot_plot(out, all_records['pivot'])
    if not config['smoke']:
        grid_plot(out, all_groups['explore'])
        sweeps_plot(out, all_groups['explore'])
    lines = ['# 強依存path：pivotのrobustness', '',
        f'N={config["n"]:,}、theta=0.25、h=Uniform[-1,1]、first-bank draft、J=1なのじゃ。',
        'targetのrepeat IDとalgorithmのrepeat IDを分離したのじゃ。前者は頂点の並べ替えと単点bias、後者は色分け・生成値samplingを変えるのじゃ。',
        'baselineも同じtargetを使うのじゃ。baselineの乱数はalgorithm repeatとbatch予算に依存するのじゃ。',
        ('pivotの10 runsは5 targets×2 algorithm repeatsであり、10個の独立なtargetとして信頼区間を計算していないのじゃ。'
         if not config['smoke'] else 'smokeでは1 target×2 algorithm repeatsを使うのじゃ。'),
        '探索・確認のtarget/algorithm repeatはpivotと分離し、確認候補は探索の結果だけから固定したのじゃ。', '',
        '[pivotの各seed](pivot_seeds.png)・[pivot同予算比較](pivot_tradeoff.png)・[確認のtrade-off](confirm_tradeoff.png)',
        '[p/M近傍](explore_p_M.png)・[d/TVの感度](explore_d_TV.png)' if not config['smoke'] else '小Nのpipeline smoke出力なのじゃ。',
        '[pivot個票](pivot_individual.csv)・[targetごとの集計](pivot_by_target.csv)・[seedとtraceの検証](audit.json)', '',
        '| phase | 版 | 完走/全run | 構造・KL成功 | fallback | 打切り |',
        '|---|---|---:|---:|---:|---:|']
    for phase, records in all_records.items():
        for variant, rows in records.items():
            complete = sum(r['status'] == 'complete' for r in rows)
            lines.append(f'| {phase} | {variant} | {complete}/{len(rows)} | {sum(exact_run(r) for r in rows)} | '
                         f'{sum(bool(r.get("fallback")) for r in rows)} | {len(rows)-complete} |')
    lines += ['', '「構造・KL成功」は完走、KL/token≤1e-12、unsafe batch=0、fallbackなしを全て満たすrunなのじゃ。誤差の平均値と個票も保存し、成功率だけでは比較しないのじゃ。',
        '打切りを含む設定の無条件の平均KLは欠測とし、成功runだけの平均で置き換えていないのじゃ。Q平均には実際に使った打切り時のQも含むのじゃ。', '',
        '| pivotの版 | 平均Q | 中央値Q | p90 Q | 平均KL/token |', '|---|---:|---:|---:|---:|']
    for variant, rows in all_groups['pivot'].items():
        for row in rows:
            error = '欠測（打切りあり）' if row['KL'] is None else f'{row["KL"]:.8g}'
            lines.append(f'| {variant} | {row["Q"]:.2f} | {row["Q_median"]:.2f} | {row["Q_p90"]:.2f} | {error} |')
    lines += ['', '[探索全対応](explore_paired.csv)・[探索打切り](explore_censored.csv)・[確認全対応](confirm_paired.csv)・[確認打切り](confirm_censored.csv)',
              'query内訳・初期偽辺・cycle rank・真辺KL mass保持率は各summaryとpaired CSVに保存してあるのじゃ。',
              '自動集計・機械検証までの結果なのじゃ。図の目視確認と実験の解釈は完了後に行うのじゃ。', '']
    (out/'report_ja.md').write_text('\n'.join(lines))


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    report(parser.parse_args().output)
