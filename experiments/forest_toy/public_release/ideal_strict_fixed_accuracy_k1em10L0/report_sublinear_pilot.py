"""Create the compact audit tables and phase-1 figures for the sublinear pilot."""

from __future__ import annotations

from collections import defaultdict
import csv
import json
from pathlib import Path
import shutil

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import BoundaryNorm, ListedColormap, Normalize
import numpy as np

import strong_path_baseline_study as controls
from validate import digest


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT/'results'/'sublinear_pilot_study'
TARGETS = ('matching', 'path', 'binary', 'stars_original')
LABELS = {'matching': 'Matching', 'path': 'Path', 'binary': 'Binary tree',
          'stars_original': 'Growing stars'}
FLOOR = 1e-16


def load_json(path):
    return json.loads(Path(path).read_text())


def origins_for(row, plan, stage=None):
    origins = plan.get(row['proposal_job_key'], {}).get('origins', [])
    return [origin for origin in origins if stage is None or origin['stage'] == stage]


def stage_entries(rows, plan, stage):
    return [(row, origin) for row in rows for origin in origins_for(row, plan, stage)]


def axes_grid(rows, columns, *, width=4., height=3.1):
    fig, axes = plt.subplots(rows, columns, figsize=(width*columns, height*rows),
                             squeeze=False, constrained_layout=True)
    return fig, axes


def lambda_colors(values):
    values = sorted(set(values))
    norm = Normalize(min(values), max(values)) if len(values) > 1 else Normalize(0, 1)
    cmap = plt.get_cmap('coolwarm')
    return {value: cmap(norm(value)) if len(values) > 1 else cmap(.5) for value in values}


def write_csvs(out, rows, plan):
    fields = ['target', 'n', 'stages', 'status', 'p', 'M', 'd', 'lambda', 'q0',
              'q0_over_N', 'Q', 'Q_over_N', 'KL_per_token', 'KL_total',
              'relative_KL', 'proposal_mc_se', 'random_mean', 'random_combined_se',
              'random_count', 'random_over_proposal', 'win_factor3',
              'win_conservative', 'committed_fraction', 'abort_stage',
              'first_screen_incomplete', 'proposal_job_key']
    with (out/'proposal_points.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        for row in sorted(rows, key=lambda r: (r['target'], r['n'], r['Q'],
                                                r['p'], r['M'], r['d'], r['lambda'])):
            random = row['random'] or {}
            writer.writerow({**{name: row.get(name) for name in fields},
                'stages': '|'.join(sorted({o['stage'] for o in origins_for(row, plan)})),
                'random_mean': random.get('mean'),
                'random_combined_se': random.get('combined_se'),
                'random_count': random.get('count')})

    unique_random = {}
    for row in rows:
        random = row['random']
        if random is not None:
            unique_random[(row['target'], row['n'], row['Q'])] = random
    random_fields = ['target', 'n', 'budget', 'count', 'mean', 'schedule_se',
                     'measurement_se', 'combined_se', 'minimum', 'maximum', 'formula']
    with (out/'random_summary.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=random_fields)
        writer.writeheader()
        for key in sorted(unique_random):
            writer.writerow({name: unique_random[key].get(name) for name in random_fields})

    cells = []
    for target in TARGETS:
        for n in sorted({row['n'] for row in rows}):
            local = [row for row in rows if row['target'] == target and row['n'] == n]
            complete = [row for row in local if row['status'] == 'complete']
            wins = [row for row in complete if row['win_factor3']]
            cells.append({'target': target, 'n': n, 'planned': len(local),
                'complete': len(complete), 'censored': len(local)-len(complete),
                'outcome': 'complete-win' if wins else 'complete-lose' if complete else 'censored',
                'minimum_win_Q': min((row['Q'] for row in wins), default=None),
                'best_KL_per_token': min((row['KL_per_token'] for row in complete), default=None),
                'best_relative_KL': min((row['relative_KL'] for row in complete), default=None)})
    with (out/'cell_summary.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(cells[0]))
        writer.writeheader()
        writer.writerows(cells)

    scaling = []
    for target in TARGETS:
        points = []
        for n in sorted({row['n'] for row in rows}):
            wins = [row for row in rows if row['target'] == target and row['n'] == n
                    and row['win_factor3']
                    and any(o['stage'] == 'anchor' for o in origins_for(row, plan))]
            if wins:
                points.append((n, min(row['Q'] for row in wins)))
        slope = (float(np.polyfit(np.log([x for x, _ in points]),
                                  np.log([y for _, y in points]), 1)[0])
                 if len(points) > 1 else None)
        scaling.append({'target': target, 'anchor_factor3_OLS_slope': slope,
                        'points': json.dumps(points, separators=(',', ':')),
                        'interpretation': 'exploratory matched-random gate; not fixed accuracy'})
    with (out/'factor3_scaling.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(scaling[0]))
        writer.writeheader()
        writer.writerows(scaling)
    return cells


def plot_rescue_ribbons(out, rows, plan, small_n):
    entries = stage_entries(rows, plan, 'rescue_C')
    fig, axes = axes_grid(len(TARGETS), len(small_n))
    for i, target in enumerate(TARGETS):
        for j, n in enumerate(small_n):
            ax = axes[i, j]
            local = [(row, origin) for row, origin in entries
                     if row['target'] == target and row['n'] == n]
            colors = lambda_colors([origin['lambda'] for _, origin in local] or [0.])
            for lam in sorted(colors):
                complete = sorted([(origin['actual_r'], row['KL_per_token'])
                    for row, origin in local if origin['lambda'] == lam
                    and row['status'] == 'complete'], key=lambda x: x[0])
                if complete:
                    ax.plot([x for x, _ in complete], [max(FLOOR, y) for _, y in complete],
                            '-o', ms=3, lw=1.3, color=colors[lam], label=f'{lam:g}')
            post_censored = [(origin['actual_r'], row) for row, origin in local
                             if row['status'] == 'censored'
                             and not row['first_screen_incomplete']]
            if post_censored:
                y = max([row['KL_per_token'] for row, _ in local
                         if row['KL_per_token'] is not None] or [1.])
                ax.scatter([x for x, _ in post_censored], [y]*len(post_censored),
                           marker='v', facecolors='none', edgecolors='black', s=35,
                           label='post-screen censor')
            ax.set_yscale('log')
            ax.grid(alpha=.2)
            ax.set_title(f'{LABELS[target]}, N={n}')
            if i == len(TARGETS)-1:
                ax.set_xlabel(r'actual $q_0/N$')
            if j == 0:
                ax.set_ylabel('proposal KL/token')
            if local:
                ax.legend(title=r'$\lambda=\tau/X$', fontsize=7, title_fontsize=7)
            else:
                ax.text(.5, .5, 'no rescue', ha='center', va='center', transform=ax.transAxes)
    fig.savefig(out/'rescue_lambda_ribbons.png', dpi=180)
    plt.close(fig)


def plot_query_mapping(out, rows, plan, small_n):
    entries = stage_entries(rows, plan, 'rescue_C')
    fig, axes = axes_grid(len(TARGETS), len(small_n))
    for i, target in enumerate(TARGETS):
        for j, n in enumerate(small_n):
            ax = axes[i, j]
            local = [(row, origin) for row, origin in entries
                     if row['target'] == target and row['n'] == n]
            colors = lambda_colors([origin['lambda'] for _, origin in local] or [0.])
            for lam in sorted(colors):
                points = sorted([(origin['actual_r'], row['Q_over_N'], row)
                    for row, origin in local if origin['lambda'] == lam
                    and not row['first_screen_incomplete']], key=lambda x: x[0])
                if points:
                    ax.plot([x for x, _, _ in points], [y for _, y, _ in points],
                            '-', lw=1.1, color=colors[lam])
                    for x, y, row in points:
                        ax.scatter(x, y, marker='o' if row['status'] == 'complete' else 'v',
                                   facecolors=colors[lam] if row['status'] == 'complete' else 'none',
                                   edgecolors=colors[lam], s=25)
            ax.axhline(1., color='black', ls=':', lw=.8)
            ax.grid(alpha=.2)
            ax.set_title(f'{LABELS[target]}, N={n}')
            if i == len(TARGETS)-1:
                ax.set_xlabel(r'actual $q_0/N$')
            if j == 0:
                ax.set_ylabel(r'actual $Q/N$')
            if not local:
                ax.text(.5, .5, 'no rescue', ha='center', va='center', transform=ax.transAxes)
    fig.savefig(out/'rescue_query_mapping.png', dpi=180)
    plt.close(fig)


def plot_advantage(out, rows, plan, small_n):
    entries = stage_entries(rows, plan, 'rescue_C')
    fig, axes = axes_grid(len(TARGETS), len(small_n))
    for i, target in enumerate(TARGETS):
        for j, n in enumerate(small_n):
            ax = axes[i, j]
            local = [(row, origin) for row, origin in entries
                     if row['target'] == target and row['n'] == n
                     and row['status'] == 'complete' and row['random'] is not None]
            colors = lambda_colors([origin['lambda'] for _, origin in local] or [0.])
            for lam in sorted(colors):
                points = []
                for row, origin in local:
                    if origin['lambda'] != lam:
                        continue
                    random = row['random']
                    proposal = max(row['KL_per_token'], FLOOR)
                    center = max(random['mean'], FLOOR)/proposal
                    lower = max(random['mean']-2*random['combined_se'], FLOOR)/proposal
                    upper = max(random['mean']+2*random['combined_se'], FLOOR)/proposal
                    points.append((row['Q_over_N'], np.log10(center),
                                   np.log10(lower), np.log10(upper)))
                points.sort(key=lambda x: x[0])
                if not points:
                    continue
                xs = [x for x, _, _, _ in points]
                ys = [y for _, y, _, _ in points]
                ax.plot(xs, ys,
                        '-o', ms=3, lw=1.2, color=colors[lam], label=f'{lam:g}')
                ax.fill_between(xs, [low for _, _, low, _ in points],
                                [high for _, _, _, high in points],
                                color=colors[lam], alpha=.16, linewidth=0)
            ax.axhline(np.log10(3), color='black', ls='--', lw=.8, label='3x gate')
            ax.set_ylim(-14, 8)
            ax.grid(alpha=.2)
            ax.set_title(f'{LABELS[target]}, N={n}')
            if i == len(TARGETS)-1:
                ax.set_xlabel(r'actual $Q/N$')
            if j == 0:
                ax.set_ylabel(r'$\log_{10}(KL_{random}/KL_{proposal})$')
            if local:
                ax.legend(fontsize=7)
            else:
                ax.text(.5, .5, 'no matched points', ha='center', va='center',
                        transform=ax.transAxes)
    fig.savefig(out/'random_advantage.png', dpi=180)
    plt.close(fig)


def plot_facets(out, rows, plan, small_n):
    entries = stage_entries(rows, plan, 'rescue_A')+stage_entries(rows, plan, 'rescue_B')
    fig, axes = axes_grid(len(TARGETS), len(small_n))
    markers = {'rescue_A': 'o', 'rescue_B': 's'}
    for i, target in enumerate(TARGETS):
        for j, n in enumerate(small_n):
            ax = axes[i, j]
            local = [(row, origin) for row, origin in entries
                     if row['target'] == target and row['n'] == n]
            facets = sorted({(origin['p'], origin['d']) for _, origin in local})
            colors = plt.get_cmap('tab10')
            palette = {facet: colors(k % 10) for k, facet in enumerate(facets)}
            for row, origin in local:
                if row['status'] != 'complete':
                    continue
                facet = origin['p'], origin['d']
                ax.scatter(origin['actual_r'], max(FLOOR, row['KL_per_token']),
                           marker=markers[origin['stage']], color=palette[facet], s=25,
                           label=f'p{facet[0]}/d{facet[1]}' if origin['stage'] == 'rescue_A' else None)
            ax.set_yscale('log')
            ax.grid(alpha=.2)
            ax.set_title(f'{LABELS[target]}, N={n}')
            if i == len(TARGETS)-1:
                ax.set_xlabel(r'actual $q_0/N$')
            if j == 0:
                ax.set_ylabel('proposal KL/token')
            if facets:
                handles, labels = ax.get_legend_handles_labels()
                unique = dict(zip(labels, handles))
                ax.legend(unique.values(), unique.keys(), fontsize=6, ncol=2)
            else:
                ax.text(.5, .5, 'no rescue', ha='center', va='center', transform=ax.transAxes)
    fig.savefig(out/'rescue_facet_screen.png', dpi=180)
    plt.close(fig)


def plot_outcomes(out, cells, n_grid):
    code = {'censored': 0, 'complete-lose': 1, 'complete-win': 2}
    matrix = np.asarray([[code[next(row['outcome'] for row in cells
                         if row['target'] == target and row['n'] == n)]
                         for n in n_grid] for target in TARGETS])
    fig, ax = plt.subplots(figsize=(10, 3.2), constrained_layout=True)
    cmap = ListedColormap(['#8f8f8f', '#d95f5f', '#4daf4a'])
    ax.imshow(matrix, aspect='auto', cmap=cmap, norm=BoundaryNorm([-.5, .5, 1.5, 2.5], 3))
    for i in range(len(TARGETS)):
        for j in range(len(n_grid)):
            ax.text(j, i, ('censor', 'lose', 'win')[matrix[i, j]], ha='center',
                    va='center', fontsize=8, color='white' if matrix[i, j] != 2 else 'black')
    ax.set_xticks(range(len(n_grid)), n_grid)
    ax.set_yticks(range(len(TARGETS)), [LABELS[t] for t in TARGETS])
    ax.set_xlabel('N')
    ax.set_title('Phase-1 outcome: factor-three gate against matched random')
    fig.savefig(out/'phase_outcomes.png', dpi=180)
    plt.close(fig)


def lower_envelope(points):
    best, result = float('inf'), []
    for x, y in sorted(points):
        if y < best:
            best = y
            result.append((x, y))
    return result


def plot_n_overlay(out, rows, plan, n_grid):
    fig, axes = axes_grid(2, 2, width=5., height=4.)
    colors = {n: plt.get_cmap('viridis')(k/max(1, len(n_grid)-1))
              for k, n in enumerate(n_grid)}
    for ax, target in zip(axes.flat, TARGETS):
        for n in n_grid:
            anchor = [row for row in rows if row['target'] == target and row['n'] == n
                      and row['status'] == 'complete'
                      and any(o['stage'] == 'anchor' for o in origins_for(row, plan))]
            anchor.sort(key=lambda row: row['Q_over_N'])
            if anchor:
                ax.plot([row['Q_over_N'] for row in anchor],
                        [max(FLOOR, row['KL_per_token']) for row in anchor],
                        '-o', ms=2.5, lw=1., color=colors[n], label=f'N={n}')
            rescue = [row for row in rows if row['target'] == target and row['n'] == n
                      and row['status'] == 'complete'
                      and any(o['stage'].startswith('rescue_') for o in origins_for(row, plan))]
            envelope = lower_envelope([(row['Q_over_N'], max(FLOOR, row['KL_per_token']))
                                       for row in rescue])
            if envelope:
                ax.plot([x for x, _ in envelope], [y for _, y in envelope], '--',
                        lw=1.5, color=colors[n])
        ax.set_yscale('log')
        ax.grid(alpha=.2)
        ax.set_title(LABELS[target])
        ax.set_xlabel(r'actual $Q/N$')
        ax.set_ylabel('KL/token')
        handles, labels = ax.get_legend_handles_labels()
        if handles:
            ax.legend(fontsize=6, ncol=2)
        ax.text(.02, .02, 'solid: common anchors\ndashed: per-N rescue envelope',
                transform=ax.transAxes, fontsize=7, va='bottom')
    fig.savefig(out/'full_N_anchor_and_retuned_overlay.png', dpi=180)
    plt.close(fig)


def plot_win_scaling(out, rows, n_grid):
    fig, axes = plt.subplots(1, 2, figsize=(10, 4), constrained_layout=True)
    for target in TARGETS:
        points = []
        for n in n_grid:
            wins = [row for row in rows if row['target'] == target and row['n'] == n
                    and row['win_factor3']]
            if wins:
                best = min(wins, key=lambda row: (row['Q'], row['KL_per_token']))
                points.append((n, best['Q']))
        if points:
            axes[0].plot([x for x, _ in points], [y for _, y in points], '-o',
                         label=LABELS[target])
            axes[1].plot([x for x, _ in points], [y/x for x, y in points], '-o',
                         label=LABELS[target])
    axes[0].set(xscale='log', yscale='log', xlabel='N', ylabel='minimum winning Q',
                title='Exploratory factor-three gate (not fixed accuracy)')
    axes[1].set(xscale='log', xlabel='N', ylabel='Q/N',
                title='Winning query fraction')
    for ax in axes:
        ax.grid(alpha=.2)
        handles, labels = ax.get_legend_handles_labels()
        if handles:
            ax.legend(fontsize=8)
    fig.savefig(out/'factor3_win_scaling_diagnostic.png', dpi=180)
    plt.close(fig)


def write_plan_memo(out, summary, cells, rows, plan):
    common = summary['minimum_common_N_factor3']
    failures = [(row['target'], row['n']) for row in cells if row['outcome'] != 'complete-win']
    common_text = str(common) if common is not None else '未発見'
    failure_text = ', '.join(f'{LABELS[t]}@{n}' for t, n in failures) or 'なし'
    minima = {target: min((row['n'] for row in cells
                           if row['target'] == target and row['outcome'] == 'complete-win'),
                          default=None) for target in TARGETS}
    slopes = {}
    for target in TARGETS:
        points = []
        for n in sorted({row['n'] for row in rows}):
            wins = [row for row in rows if row['target'] == target and row['n'] == n
                    and row['win_factor3']
                    and any(o['stage'] == 'anchor' for o in origins_for(row, plan))]
            if wins:
                points.append((n, min(row['Q'] for row in wins)))
        slopes[target] = (float(np.polyfit(np.log([x for x, _ in points]),
                                           np.log([y for _, y in points]), 1)[0])
                          if len(points) > 1 else None)
    minima_text = ', '.join(f'{LABELS[t]}={minima[t]}' for t in TARGETS)
    slope_text = ', '.join(f'{LABELS[t]}={slopes[t]:.2f}' for t in TARGETS
                           if slopes[t] is not None)
    text = f"""# Phase 1 計画memo

## 仮説
4種類のforestで、同じquery予算のbalanced randomよりproposalが低KLとなる小さなNを探索するのじゃ。

## 軸
主図は縦軸KL/token・横軸Q、補助にtotal KLとL/L0を保存したのじゃ。N scalingは固定精度をまだ選ばず、factor-three gateを探索診断にだけ使うのじゃ。

## jobs・seed・停止
exact oracle、constant edge、1 target seed、1 proposal seed、randomは8 schedule（matchingのみ解析期待値）、各runはQ>N直前でcensorなのじゃ。small Nの失敗cellだけproposal-onlyでA/B/C救済し、phase 2は開始しないのじゃ。

## 結果
4 tree共通の最小N（暫定factor-three基準）は **{common_text}**、tree別最小は **{minima_text}** なのじゃ。未勝利またはcensorのcellは **{failure_text}** なのじゃ。clean anchorの暫定log-log傾きは **{slope_text}** だが、固定accuracyのscaling主張には使わないのじゃ。

## 次
treeごとに固定absolute/relative KL閾値をこの曲線から選び、独立seedでQ-vs-Nを確認してからBeta edge tailとnoisy oracleへ進むのじゃ。
"""
    (out/'plan_ja.md').write_text(text)


def report(output=OUTPUT):
    out = Path(output)
    design = load_json(out/'design.json')
    summary = load_json(out/'summary.json')
    rows = load_json(out/'comparisons.json')
    plan = load_json(out/'proposal_plan.json')['jobs']
    cells = write_csvs(out, rows, plan)
    n_grid = design['n_grid']
    small_n = design['small_n']
    plot_rescue_ribbons(out, rows, plan, small_n)
    plot_query_mapping(out, rows, plan, small_n)
    plot_advantage(out, rows, plan, small_n)
    plot_facets(out, rows, plan, small_n)
    plot_outcomes(out, cells, n_grid)
    plot_n_overlay(out, rows, plan, n_grid)
    plot_win_scaling(out, rows, n_grid)
    write_plan_memo(out, summary, cells, rows, plan)
    files = ['proposal_points.csv', 'random_summary.csv', 'cell_summary.csv',
             'factor3_scaling.csv',
             'rescue_lambda_ribbons.png', 'rescue_query_mapping.png',
             'random_advantage.png', 'rescue_facet_screen.png', 'phase_outcomes.png',
             'full_N_anchor_and_retuned_overlay.png',
             'factor3_win_scaling_diagnostic.png', 'plan_ja.md']
    frozen_report = out/'sources'/'report_sublinear_pilot.py'
    current_digest = digest(ROOT/'report_sublinear_pilot.py')
    revision_source = out/'sources'/f'report_sublinear_pilot_{current_digest[:12]}.py'
    if not revision_source.exists():
        shutil.copyfile(ROOT/'report_sublinear_pilot.py', revision_source)
    assert digest(revision_source) == current_digest
    manifest = {'files': [{'path': name, 'sha256': digest(out/name)} for name in files],
                'report_source_current_sha256': current_digest,
                'report_source_frozen_at_generation_sha256': (digest(frozen_report)
                    if frozen_report.exists() else None),
                'report_revision_source': str(revision_source.relative_to(out)),
                'generation_results_changed_by_revision': False,
                'interpretation': 'Dashed rescue envelopes are per-N retuned and are not clean scaling-regression evidence.'}
    (out/'report_manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    return manifest


def main():
    manifest = report()
    print(json.dumps(manifest, indent=2))


if __name__ == '__main__':
    main()
