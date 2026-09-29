"""Create audit tables and figures for the cellwise fixed-accuracy rescue."""

from __future__ import annotations

import csv
import json
from math import ceil
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import Normalize
import numpy as np

import row_cap_grid_study as grid
import sublinear_pilot_study as phase1
from validate import digest


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT/'results'/'fixed_accuracy_rescue'
LABELS = {'matching': 'Matching', 'path': 'Path', 'binary': 'Binary tree',
          'stars_original': 'Growing stars'}
FLOOR = 1e-8


def load_json(path):
    return json.loads(Path(path).read_text())


def scalar(value):
    if isinstance(value, (list, dict)):
        return json.dumps(value, separators=(',', ':'), sort_keys=True)
    return value


def write_table(path, rows, fields=None):
    fields = fields or (list(rows[0]) if rows else [])
    with Path(path).open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, extrasaction='ignore')
        writer.writeheader()
        for row in rows:
            writer.writerow({name: scalar(row.get(name)) for name in fields})


def write_csvs(out, screen, development, confirmation, selection, combined):
    write_table(out/'screen_records.csv', screen)
    write_table(out/'development_summary.csv', development)
    write_table(out/'confirmation_records.csv', confirmation)
    frozen = [{'cell': key, **value} for key, value in sorted(selection.items())]
    write_table(out/'final_selection.csv', frozen)
    write_table(out/'combined_scaling.csv', combined['points'])
    write_table(out/'combined_slopes.csv', combined['slopes'])


def plot_screen_ribbons(out, config, screen, selection):
    for target in phase1.TARGETS:
        ns = [cell['n'] for cell in config['cells'] if cell['target'] == target]
        if not ns:
            continue
        columns = min(3, len(ns))
        rows = ceil(len(ns)/columns)
        fig, axes = plt.subplots(rows, columns, figsize=(4.3*columns, 3.4*rows),
                                 squeeze=False, constrained_layout=True)
        lambdas = sorted({row['lambda'] for row in screen if row['target'] == target})
        norm = Normalize(min(lambdas), max(lambdas)) if len(lambdas) > 1 else Normalize(0, 1)
        cmap = plt.get_cmap('coolwarm')
        for ax, n in zip(axes.flat, ns):
            chosen = selection[f'{target}|{n}']
            p, _, d, _ = chosen['setting']
            local = [row for row in screen if row['target'] == target and row['n'] == n
                     and row['p'] == p and row['d'] == d]
            for lam in sorted({row['lambda'] for row in local}):
                values = sorted([row for row in local if row['lambda'] == lam],
                                key=lambda row: row['q0_over_N'])
                complete = [row for row in values if row['normalized_K_upper'] is not None]
                if complete:
                    ax.plot([row['q0_over_N'] for row in complete],
                            [max(FLOOR, row['normalized_K_upper']) for row in complete],
                            '-o', ms=3, lw=1.1, color=cmap(norm(lam)), label=f'{lam:g}')
                censored = [row for row in values if row['normalized_K_upper'] is None]
                if censored:
                    ax.scatter([row['q0_over_N'] for row in censored],
                               [1e3]*len(censored), marker='v', facecolors='none',
                               edgecolors=cmap(norm(lam)), s=28)
            ax.axhline(1., color='black', ls='--', lw=.8)
            ax.set_yscale('log')
            ax.set_ylim(FLOOR*.7, 2e3)
            ax.grid(alpha=.2)
            ax.set_title(f'{LABELS[target]}, N={n}\nselected facet p={p}, d={d}')
            ax.set_xlabel(r'preprocessing $q_0/N$')
            ax.set_ylabel(r'$(K+2SE)/K_\star$')
            ax.legend(title=r'$\lambda=\tau/X$', fontsize=7, title_fontsize=7)
        for ax in list(axes.flat)[len(ns):]:
            ax.axis('off')
        fig.suptitle('Hardest-pair screen: lambda ribbons on the selected facet')
        fig.savefig(out/f'screen_lambda_ribbons_{target}.png', dpi=190)
        plt.close(fig)


def plot_confirmation_heatmap(out, config, confirmation_summary):
    n_grid = list(phase1.N_GRID)
    values = {(row['target'], row['n']): row for row in confirmation_summary}
    matrix = np.full((len(phase1.TARGETS), len(n_grid)), -1., dtype=float)
    text = np.full(matrix.shape, 'not tuned', dtype=object)
    for i, target in enumerate(phase1.TARGETS):
        for j, n in enumerate(n_grid):
            row = values.get((target, n))
            if row is not None:
                matrix[i, j] = row['successes']/row['runs']
                text[i, j] = f'{row["successes"]}/{row["runs"]}'
    cmap = plt.get_cmap('viridis').copy()
    cmap.set_bad('#d9d9d9')
    visible = np.ma.masked_less(matrix, 0.)
    fig, ax = plt.subplots(figsize=(12, 3.8), constrained_layout=True)
    ax.imshow(visible, cmap=cmap, vmin=0., vmax=1., aspect='auto')
    for i in range(matrix.shape[0]):
        for j in range(matrix.shape[1]):
            ax.text(j, i, text[i, j], ha='center', va='center', fontsize=7,
                    color='white' if 0 <= matrix[i, j] < .62 else 'black')
    ax.set_xticks(range(len(n_grid)), n_grid, rotation=35)
    ax.set_yticks(range(len(phase1.TARGETS)),
                  [LABELS[target] for target in phase1.TARGETS])
    ax.set_xlabel('N')
    ax.set_title('Untouched-seed rescue confirmation (grey = already confirmed / not retuned)')
    # Please use a standard scalar colorbar for the non-grey success range.
    scalar_map = plt.cm.ScalarMappable(norm=Normalize(0, 1), cmap='viridis')
    fig.colorbar(scalar_map, ax=ax, label='success fraction', shrink=.82)
    fig.savefig(out/'rescue_confirmation_heatmap.png', dpi=190)
    plt.close(fig)


def plot_combined_scaling(out, combined):
    fig, axes = plt.subplots(2, 2, figsize=(10.5, 7.5), squeeze=False,
                             constrained_layout=True)
    slope = {row['target']: row for row in combined['slopes']}
    n_grid = list(phase1.N_GRID)
    for ax, target in zip(axes.flat, phase1.TARGETS):
        local = [row for row in combined['points'] if row['target'] == target]
        confirmed = [row for row in local if row['confirmed']]
        failed = [row for row in local if not row['confirmed']]
        if confirmed:
            ax.errorbar([row['n'] for row in confirmed],
                        [row['mean_Q'] for row in confirmed],
                        yerr=[row['Q_se'] or 0. for row in confirmed],
                        color='#0072b2', marker='o', lw=1.5, capsize=2.5,
                        label='6/6 confirmed')
        if failed:
            ax.scatter([row['n'] for row in failed],
                       [row['mean_Q_spent'] for row in failed], marker='x',
                       color='#d55e00', s=38, label='not 6/6')
            for row in failed:
                ax.annotate(f'{row["successes"]}/{row["runs"]}',
                            (row['n'], row['mean_Q_spent']), xytext=(2, 4),
                            textcoords='offset points', fontsize=6)
        fit = slope[target]
        if fit['OLS_exponent'] is not None:
            xs = np.asarray([point[0] for point in fit['points']], dtype=float)
            ys = np.exp(fit['OLS_intercept'])*xs**fit['OLS_exponent']
            ax.plot(xs, ys, ':', color='#0072b2', lw=1.1,
                    label=f'fit a={fit["OLS_exponent"]:.2f}')
        ax.plot(n_grid, n_grid, '--', color='black', lw=.8, label='Q=N cap')
        ax.set_xscale('log', base=2)
        ax.set_yscale('log', base=2)
        ax.set_xticks(n_grid, [str(n) for n in n_grid], rotation=35)
        ax.grid(alpha=.2)
        ax.set_title(LABELS[target])
        ax.set_xlabel('N')
        ax.set_ylabel('mean Q')
        ax.legend(fontsize=7)
    fig.suptitle('Combined fixed-accuracy scaling after cellwise rescue')
    fig.savefig(out/'combined_fixed_accuracy_Q_vs_N.png', dpi=190)
    plt.close(fig)


def write_memo(out, config, development, confirmation, selection, combined):
    confirmation_by_cell = {(row['target'], row['n']): row for row in confirmation}
    lines = ['# 固定精度 cellwise rescue', '',
        ('既存確認で6/6に届かなかったcellだけを対象とした。最も厳しかった既存seed 1組で'
         '連続gridをscreenし、上位候補を既存6組でtuningした後、設定を凍結して未使用6組で確認した。'), '',
        '## fresh確認', '',
        '| tree | N | setting | dev成功 | fresh成功 | mean Q | Q/N |',
        '|---|---:|---|---:|---:|---:|---:|']
    for cell in config['cells']:
        target, n = cell['target'], cell['n']
        selected = selection[f'{target}|{n}']
        row = confirmation_by_cell[(target, n)]
        lines.append(f'| {LABELS[target]} | {n} | `{selected["setting"]}` | '
                     f'{selected["successes"]}/{selected["runs"]} | '
                     f'{row["successes"]}/{row["runs"]} | {row["mean_Q"]:.1f} | '
                     f'{row["mean_Q_over_N"]:.3f} |')
    lines.extend(['', '## combined scaling', '',
                  '| tree | confirmed points | OLS slope | confirmed N |',
                  '|---|---:|---:|---|'])
    for row in combined['slopes']:
        slope = '--' if row['OLS_exponent'] is None else f'{row["OLS_exponent"]:.3f}'
        ns = ', '.join(str(point[0]) for point in row['points']) or '--'
        lines.append(f'| {LABELS[row["target"]]} | {row["confirmed_points"]}/8 | '
                     f'{slope} | {ns} |')
    failed = [row for row in confirmation if not row['confirmed']]
    lines.extend(['', '## なお未確認', ''])
    if failed:
        lines.extend(f'- {LABELS[row["target"]]} N={row["n"]}: '
                     f'{row["successes"]}/{row["runs"]}' for row in failed)
    else:
        lines.append('- なし')
    lines.extend(['',
        '選択に使ったdevelopment結果とfresh確認結果を混ぜて平均していない。'
        '失敗run・Q=N直前のcensorも保存している。', '',
        '**Phase boundary:** このreport生成時点ではedge-tail / oracle noiseをまだ開始していない。', ''])
    (out/'report_ja.md').write_text('\n'.join(lines))


def report(output=OUTPUT):
    out = Path(output)
    config = load_json(out/'design.json')
    screen = load_json(out/'screen_records.json')
    development = load_json(out/'development_summary.json')
    confirmation_records = load_json(out/'confirmation_records.json')
    confirmation = load_json(out/'confirmation_summary.json')
    selection = load_json(out/'final_selection.json')
    combined = load_json(out/'combined_scaling.json')
    write_csvs(out, screen, development, confirmation_records, selection, combined)
    plot_screen_ribbons(out, config, screen, selection)
    plot_confirmation_heatmap(out, config, confirmation)
    plot_combined_scaling(out, combined)
    write_memo(out, config, development, confirmation, selection, combined)
    names = ['screen_records.csv', 'development_summary.csv',
             'confirmation_records.csv', 'final_selection.csv',
             'combined_scaling.csv', 'combined_slopes.csv',
             'rescue_confirmation_heatmap.png', 'combined_fixed_accuracy_Q_vs_N.png',
             'report_ja.md']
    names.extend(f'screen_lambda_ribbons_{target}.png' for target in phase1.TARGETS
                 if any(cell['target'] == target for cell in config['cells']))
    manifest = {'study': config['study'], 'noise_started': False,
        'source_sha256': config['source_sha256'],
        'artifacts_sha256': {name: digest(out/name) for name in names}}
    grid.atomic_json(out/'report_manifest.json', manifest)
    return manifest


if __name__ == '__main__':
    report()
