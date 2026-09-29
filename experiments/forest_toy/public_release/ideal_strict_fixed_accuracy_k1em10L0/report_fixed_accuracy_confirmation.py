"""Render compact tables and figures for the fixed-accuracy confirmation."""

from __future__ import annotations

import csv
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

import row_cap_grid_study as grid
from validate import digest


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT/'results'/'fixed_accuracy_confirmation'
TARGETS = ('matching', 'path', 'binary', 'stars_original')
ROLES = ('frontier', 'exact')
LABELS = {'matching': 'Matching', 'path': 'Path', 'binary': 'Binary tree',
          'stars_original': 'Growing stars'}
ROLE_LABELS = {'frontier': 'Frozen threshold frontier',
               'exact': 'Frozen exact-zero setting'}
ROLE_COLORS = {'frontier': '#0072b2', 'exact': '#d55e00'}
ROLE_MARKERS = {'frontier': 'o', 'exact': 's'}
ROLE_LINESTYLES = {'frontier': '-', 'exact': '--'}
FAIL_MARKERS = {'frontier': 'x', 'exact': '+'}


def load_json(path):
    return json.loads(Path(path).read_text())


def scalar(value):
    """Please serialize structured cells explicitly for stable CSV output."""
    if isinstance(value, (list, dict)):
        return json.dumps(value, separators=(',', ':'), sort_keys=True)
    return value


def write_table(path, rows, fields=None):
    if fields is None:
        fields = list(rows[0]) if rows else []
    with Path(path).open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, extrasaction='ignore')
        writer.writeheader()
        for row in rows:
            writer.writerow({field: scalar(row.get(field)) for field in fields})


def write_csvs(out, selection, records, summary, slopes):
    record_fields = ['target', 'n', 'role', 'data_repeat', 'algorithm_repeat',
        'setting', 'status', 'Q', 'Q_over_N', 'K', 'K_mc_se', 'K_upper',
        'K_threshold', 'threshold_success_raw', 'threshold_success_conservative',
        'exact_zero', 'rho', 'committed_fraction', 'abort_stage', 'job_key']
    write_table(out/'records.csv', records, record_fields)

    summary_fields = ['target', 'n', 'role', 'runs', 'complete',
        'threshold_success_raw', 'threshold_success_conservative', 'exact_zero',
        'K_threshold', 'mean_Q_spent', 'mean_Q_success', 'mean_Q_confirmed',
        'Q_se_confirmed', 'mean_Q_over_N_confirmed', 'maximum_K_upper']
    write_table(out/'summary.csv', summary, summary_fields)
    write_table(out/'slopes.csv', slopes)

    frozen = []
    for cell in sorted(selection.values(), key=lambda row: (row['target'], row['n'])):
        for role in ROLES:
            item = cell[role]
            frozen.append({'target': cell['target'], 'n': cell['n'], 'role': role,
                'K_threshold': cell['K_threshold'], 'setting': item['setting'],
                'phase1_job_key': item['phase1_job_key'],
                'phase1_status': item['phase1_status'], 'phase1_Q': item['phase1_Q'],
                'phase1_K': item['phase1_K'], 'phase1_rho': item['phase1_rho'],
                'phase1_attained_role': item['phase1_attained_role'],
                'phase1_stages': item['phase1_stages'], 'reason': item['reason']})
    write_table(out/'frozen_selection.csv', frozen)


def target_axes():
    fig, axes = plt.subplots(2, 2, figsize=(10.5, 7.5), squeeze=False,
                             constrained_layout=True)
    return fig, axes.flat


def plot_q_scaling(out, config, summary, slopes):
    slope_lookup = {(row['target'], row['role']): row for row in slopes}
    fig, axes = target_axes()
    n_grid = config['n_grid']
    for ax, target in zip(axes, TARGETS):
        for role in ROLES:
            local = sorted((row for row in summary
                            if row['target'] == target and row['role'] == role),
                           key=lambda row: row['n'])
            confirmed = [row for row in local if row['mean_Q_confirmed'] is not None]
            failed = [row for row in local if row['mean_Q_confirmed'] is None]
            if confirmed:
                ax.errorbar([row['n'] for row in confirmed],
                    [row['mean_Q_confirmed'] for row in confirmed],
                    yerr=[row['Q_se_confirmed'] or 0. for row in confirmed],
                    color=ROLE_COLORS[role], marker=ROLE_MARKERS[role],
                    markerfacecolor=(ROLE_COLORS[role] if role == 'frontier' else 'none'),
                    linestyle=ROLE_LINESTYLES[role], lw=1.5, capsize=2.5,
                    label=ROLE_LABELS[role])
            if failed:
                xshift = .985 if role == 'frontier' else 1.015
                ax.scatter([xshift*row['n'] for row in failed],
                           [row['mean_Q_spent'] for row in failed],
                           marker=FAIL_MARKERS[role], s=38, color=ROLE_COLORS[role])
                for row in failed:
                    ax.annotate(f'{row["threshold_success_conservative"]}/{row["runs"]}',
                                (xshift*row['n'], row['mean_Q_spent']),
                                xytext=(2, 4 if role == 'frontier' else -9),
                                textcoords='offset points', fontsize=6,
                                color=ROLE_COLORS[role])
            slope = slope_lookup[(target, role)]
            if slope['OLS_exponent'] is not None:
                xs = np.asarray([point[0] for point in slope['points']], dtype=float)
                ys = np.exp(slope['OLS_intercept'])*xs**slope['OLS_exponent']
                ax.plot(xs, ys, ':', lw=1., color=ROLE_COLORS[role],
                        label=f'{role} fit a={slope["OLS_exponent"]:.2f}')
        ax.plot(n_grid, n_grid, '--', color='black', lw=.8, alpha=.65,
                label='Q=N cap')
        ax.set_xscale('log', base=2)
        ax.set_yscale('log', base=2)
        ax.set_xticks(n_grid, [str(n) for n in n_grid], rotation=35)
        ax.grid(alpha=.2)
        ax.set_title(LABELS[target])
        ax.set_xlabel('N')
        ax.set_ylabel('mean Q')
        handles, labels = ax.get_legend_handles_labels()
        unique = dict(zip(labels, handles))
        ax.legend(unique.values(), unique.keys(), fontsize=7)
    fig.suptitle('Fresh-seed fixed-accuracy scaling (x = not confirmed on every seed)')
    fig.savefig(out/'fixed_accuracy_Q_vs_N.png', dpi=190)
    plt.close(fig)


def plot_q_fraction(out, config, summary):
    fig, axes = target_axes()
    for ax, target in zip(axes, TARGETS):
        for role in ROLES:
            local = sorted((row for row in summary
                            if row['target'] == target and row['role'] == role
                            and row['mean_Q_over_N_confirmed'] is not None),
                           key=lambda row: row['n'])
            if local:
                ax.plot([row['n'] for row in local],
                        [row['mean_Q_over_N_confirmed'] for row in local],
                        color=ROLE_COLORS[role], marker=ROLE_MARKERS[role],
                        markerfacecolor=(ROLE_COLORS[role] if role == 'frontier' else 'none'),
                        linestyle=ROLE_LINESTYLES[role], lw=1.5,
                        label=ROLE_LABELS[role])
        ax.axhline(1., color='black', ls='--', lw=.8)
        ax.set_xscale('log', base=2)
        ax.set_xticks(config['n_grid'], [str(n) for n in config['n_grid']], rotation=35)
        ax.set_ylim(bottom=0.)
        ax.grid(alpha=.2)
        ax.set_title(LABELS[target])
        ax.set_xlabel('N')
        ax.set_ylabel('mean Q / N')
        handles, labels = ax.get_legend_handles_labels()
        if handles:
            ax.legend(handles, labels, fontsize=7)
    fig.suptitle('Confirmed fixed-accuracy query fraction')
    fig.savefig(out/'fixed_accuracy_Q_fraction.png', dpi=190)
    plt.close(fig)


def plot_rate_heatmap(out, config, summary, metric, filename, title):
    n_grid = config['n_grid']
    fig, axes = plt.subplots(1, 2, figsize=(12, 3.8), constrained_layout=True)
    image = None
    for ax, role in zip(axes, ROLES):
        matrix = np.zeros((len(TARGETS), len(n_grid)), dtype=float)
        labels = np.empty(matrix.shape, dtype=object)
        for i, target in enumerate(TARGETS):
            for j, n in enumerate(n_grid):
                row = next(item for item in summary if item['target'] == target
                           and item['n'] == n and item['role'] == role)
                matrix[i, j] = row[metric]/row['runs']
                labels[i, j] = f'{row[metric]}/{row["runs"]}'
        image = ax.imshow(matrix, vmin=0., vmax=1., cmap='viridis', aspect='auto')
        for i in range(len(TARGETS)):
            for j in range(len(n_grid)):
                ax.text(j, i, labels[i, j], ha='center', va='center', fontsize=7,
                        color='white' if matrix[i, j] < .62 else 'black')
        ax.set_xticks(range(len(n_grid)), n_grid, rotation=35)
        ax.set_yticks(range(len(TARGETS)), [LABELS[target] for target in TARGETS])
        ax.set_xlabel('N')
        ax.set_title(ROLE_LABELS[role])
    fig.colorbar(image, ax=axes, label='fresh-seed success fraction', shrink=.82)
    fig.suptitle(title)
    fig.savefig(out/filename, dpi=190)
    plt.close(fig)


def format_slope(row):
    value = row['OLS_exponent']
    return f'{value:.3f}' if value is not None else '--'


def write_memo(out, config, summary, slopes):
    lines = [
        '# 固定精度・fresh-seed 確認', '',
        ('各 tree の絶対閾値を phase 1 の N=2048 における '
         '`K_star = 1e-3 * L0_total` として固定した。設定は phase 1 の proposal '
         'のみから凍結し、確認データによる再 tuning はしていない。'), '',
        '## 閾値', '',
        '| tree | K_star |', '|---|---:|']
    for target in TARGETS:
        threshold = config['accuracy']['K_thresholds'][target]
        lines.append(f'| {LABELS[target]} | {threshold:.6g} |')
    lines.extend(['', '## 確認結果', '',
        '| tree | frozen role | 全 seed 成功 cell | slope | 成功 N |',
        '|---|---|---:|---:|---|'])
    slope_lookup = {(row['target'], row['role']): row for row in slopes}
    for target in TARGETS:
        for role in ROLES:
            local = [row for row in summary
                     if row['target'] == target and row['role'] == role]
            confirmed = [row['n'] for row in local if row['mean_Q_confirmed'] is not None]
            slope = slope_lookup[(target, role)]
            ns = ', '.join(map(str, confirmed)) if confirmed else '--'
            lines.append(f'| {LABELS[target]} | {role} | {len(confirmed)}/{len(local)} '
                         f'| {format_slope(slope)} | {ns} |')
    failures = [row for row in summary if row['mean_Q_confirmed'] is None]
    lines.extend(['', '## 未確認 cell', ''])
    if failures:
        for row in failures:
            lines.append(f'- {LABELS[row["target"]]}, N={row["n"]}, {row["role"]}: '
                         f'{row["threshold_success_conservative"]}/{row["runs"]} 成功 '
                         f'(complete {row["complete"]}/{row["runs"]})')
    else:
        lines.append('- なし')
    lines.extend(['',
        '成功判定は `complete` かつ `K + 2 * conditional MC SE <= K_star`。'
        'slope は全 fresh seed で成功した N のみを使う記述的 OLS log-log 傾きで、'
        '3点未満なら表示しない。', '',
        '**Phase boundary:** noisy oracle / Beta-tail 実験はまだ開始していない。', ''])
    (out/'report_ja.md').write_text('\n'.join(lines))


def report(output=OUTPUT):
    out = Path(output)
    config = load_json(out/'design.json')
    selection = load_json(out/'selection.json')
    records = load_json(out/'records.json')
    summary = load_json(out/'summary.json')
    slopes = load_json(out/'slopes.json')
    write_csvs(out, selection, records, summary, slopes)
    plot_q_scaling(out, config, summary, slopes)
    plot_q_fraction(out, config, summary)
    plot_rate_heatmap(out, config, summary, 'threshold_success_conservative',
                      'fixed_accuracy_success_heatmap.png',
                      'Conservative fixed-accuracy success')
    plot_rate_heatmap(out, config, summary, 'exact_zero',
                      'exact_zero_success_heatmap.png',
                      'Structural exact-zero success')
    write_memo(out, config, summary, slopes)
    names = ('records.csv', 'summary.csv', 'slopes.csv', 'frozen_selection.csv',
             'fixed_accuracy_Q_vs_N.png', 'fixed_accuracy_Q_fraction.png',
             'fixed_accuracy_success_heatmap.png', 'exact_zero_success_heatmap.png',
             'report_ja.md')
    manifest = {'study': config['study'], 'phase2_started': False,
        'source_sha256': config['source_sha256'],
        'artifacts_sha256': {name: digest(out/name) for name in names}}
    grid.atomic_json(out/'report_manifest.json', manifest)
    return manifest


if __name__ == '__main__':
    report()
