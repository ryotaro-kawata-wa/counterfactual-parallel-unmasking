"""Report fixed ordering and EB controls without mixing exploration and confirmation."""
from collections import defaultdict
import csv
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

from strong_path_baseline_study import aggregate, setting_key
from validate import read_runs


FLOOR = 1e-12
LABELS = {'fixed_random': 'Random / balanced', 'fixed_confidence': 'Confidence / balanced',
    'fixed_margin': 'Margin / balanced', 'fixed_entropy': 'Entropy / balanced',
    'eb_confidence': 'EB / confidence', 'eb_margin': 'EB / margin', 'eb_entropy': 'EB / entropy'}
COLORS = {'random': '#333333', 'confidence': '#9b59b6', 'margin': '#c98312', 'entropy': '#15988a'}


def write_csv(path, rows):
    rows = list(rows)
    if not rows:
        path.write_text('')
        return
    keys = list(dict.fromkeys(k for row in rows for k in row))
    with path.open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=keys)
        writer.writeheader()
        for row in rows:
            writer.writerow({k: json.dumps(v) if isinstance(v, (list, dict)) else v for k, v in row.items()})


def merge_x(points):
    """Please merge equal mean costs before drawing, without rounding nearby costs."""
    groups = defaultdict(list)
    for x, y in points:
        groups[float(x)].append(float(y))
    return [(x, float(np.mean(ys))) for x, ys in sorted(groups.items())]


def plot(out, phase, groups, config):
    fig, axes = plt.subplots(1, 2, figsize=(13, 5.6), sharey=True)
    errors = [r['KL'] for r in groups if not r['censored']]
    for ax, metric in zip(axes, ('Q', 'T')):
        for method, label in LABELS.items():
            local = [r for r in groups if r['method'] == method and not r['censored']]
            points = merge_x([(r[metric], r['KL']) for r in local])
            if not points:
                continue
            family, ordering = method.split('_', 1)
            ax.plot([x for x, _ in points], [max(FLOOR, y) for _, y in points],
                color=COLORS[ordering], linestyle='-' if family == 'eb' else '--',
                marker='s' if family == 'eb' else 'o', markersize=3.5, linewidth=1.4,
                label=label, alpha=.9)
        for tau, marker, label in ((.03, '*', 'Proposal: TV=0.03'), (.001, '^', 'Proposal: TV=0.001')):
            local = [r for r in groups if r['method'] == 'proposal' and not r['censored'] and r['key'][-1] == tau]
            points = merge_x([(r[metric], r['KL']) for r in local])
            if points:
                ax.scatter([x for x, _ in points], [max(FLOOR, y) for _, y in points],
                    color='#d5443e', marker=marker, s=90 if marker == '*' else 38,
                    edgecolors='white', linewidths=.5, label=label, zorder=5)
        ax.set(yscale='log', ylim=(FLOOR*.55, max(errors+[FLOOR])*2),
               xlabel='Mean total queries Q' if metric == 'Q' else 'Mean sequential depth T (log scale)')
        if metric == 'Q':
            ax.set_xlim(0, config['n']*1.025)
        else:
            ax.set_xscale('log')
            ax.set_xlim(.8, config['n']*1.15)
        ax.grid(alpha=.2)
        ax.set_title('Total query cost' if metric == 'Q' else 'Sequential depth')
    axes[0].set_ylabel('Mean conditional reverse KL / token (nats)')
    count = len(config[phase+'_pairs'])
    fig.suptitle(f'Strong path | exact oracle | N={config["n"]:,} | {phase} ({count} runs/setting)', fontsize=13)
    fig.legend(*axes[0].get_legend_handles_labels(), loc='lower center', bbox_to_anchor=(.5, .025),
               ncol=3, fontsize=9)
    fig.text(.5, .012, 'Fixed: balanced batches. EB: realized Q at each gamma. Values <= 1e-12 share the display floor; raw values are saved.',
             ha='center', fontsize=8)
    fig.tight_layout(rect=(0, .18, 1, .94))
    for suffix in ('png', 'svg'):
        fig.savefig(out/f'{phase}_tradeoff.{suffix}', dpi=160, bbox_inches='tight')
    plt.close(fig)


def report(out, phases=('explore', 'confirm')):
    out = Path(out)
    config = json.loads((out/'design.json').read_text())
    lines = ['# Strong-path baseline comparison', '',
        '既存の提案設定を固定し、random・confidence・margin・entropyのbalanced batchと、3種類のorderingを使うEB-Samplerを比較するのじゃ。', '',
        f'N={config["n"]:,}、全辺 θ=0.25、単点場 h_i~Uniform[-1,1]、厳密oracle、値はtemperature=1のsamplingなのじゃ。', '',
        '提案法はkeep-top-d・first-bank draft・J=1を維持し、このstudyでは新たな提案ハイパラ探索をしていないのじゃ。', '',
        'EBは、選択順のprefixについて ΣH−max H≤γ を満たす最大batchを使うのじゃ。entropyは圧縮tailの語彙数を復元して計算し、位置選択と値のsamplingに同じ現在historyの応答を使うのじゃ。γはquery数ではなく、横軸には実測Qを使うのじゃ。', '',
        '探索は既存の2組のdata/algorithm seed、確認は新しい5 data seeds × 2 algorithm seedsなのじゃ（smokeでは縮小）。確認用の設定は探索のみから手法ごとに固定し、確認結果で並べ方を選び直さないのじゃ。', '',
        'KLは各batchの条件付きreverse KLを厳密に計算した和/tokenで、生成履歴についてはrun平均による推定なのじゃ。5×2は10個の独立targetではないため、iidの標準誤差は付けず、target別の平均も保存するのじゃ。', '',
        '同じ横軸の点は手法内で算術平均して描き、元の設定別数値は集計表に残すのじゃ。打切り設定は別表とし、KLを補完しないのじゃ。', '']
    for phase in phases:
        records = read_runs(out/phase/'proposals'/'runs.jsonl')+read_runs(out/phase/'baselines'/'runs.jsonl')
        groups = aggregate(records)
        (out/f'{phase}_aggregates.json').write_text(json.dumps(groups, indent=2, allow_nan=False)+'\n')
        write_csv(out/f'{phase}_summary.csv', groups)
        write_csv(out/f'{phase}_censored.csv', [r for r in groups if r['censored']])
        write_csv(out/f'{phase}_individual.csv', [dict(setting=list(setting_key(r)),
            **{k: r.get(k) for k in ('method', 'data_repeat', 'algorithm_repeat', 'status',
                                    'total', 'depth', 'kl_per_token', 'sample_seconds', 'evaluation_seconds')})
            for r in records])
        by_target = []
        for data in sorted({r['data_repeat'] for r in records}):
            by_target.extend(dict(data_repeat=data, **r) for r in aggregate(
                [r for r in records if r['data_repeat'] == data]))
        write_csv(out/f'{phase}_by_target.csv', by_target)
        plot(out, phase, groups, config)
        lines += [f'## {phase}', '', f'![{phase} tradeoff]({phase}_tradeoff.png)', '',
                  '| Method / setting | Mean Q | Median / p90 Q | Mean T | Mean KL/token | Complete |',
                  '|---|---:|---:|---:|---:|---:|']
        for row in groups:
            description = ('proposal '+str(row['key'][1:]) if row['method'] == 'proposal'
                           else LABELS[row['method']]+' / '+str(row['key'][1]))
            kl = 'censored' if row['KL'] is None else f'{row["KL"]:.6g}'
            lines.append(f'| {description} | {row["Q"]:.1f} | {row["Q_median"]:.1f} / {row["Q_p90"]:.1f} '
                         f'| {row["T"]:.1f} | {kl} | {row["complete"]}/{row["runs"]} |')
        lines += ['', f'設定別raw集計: `{phase}_summary.csv`、個別run: `{phase}_individual.csv`、target別: `{phase}_by_target.csv`。', '']
    lines += ['## Interpretation and references', '',
        '今回の比較は、厳密oracleで依存関係を利用した並列化に価値があるかを調べるものなのじゃ。MDMのモデル誤差はなく、原論文のタスク精度・temperature=0実験を再現したという主張はしないのじゃ。EBの理論で用いるforward KLと、ここで測るreverse KLも区別するのじゃ。', '',
        f'- Margin: {config["references"]["margin"]}',
        f'- EB-Sampler (NeurIPS 2025): {config["references"]["eb"]}',
        f'- EB rule / pseudocode: {config["references"]["eb_algorithm"]}', '']
    (out/'report_ja.md').write_text('\n'.join(lines))


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    report(parser.parse_args().output)
