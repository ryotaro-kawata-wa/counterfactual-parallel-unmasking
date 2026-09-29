"""Render the confirmed ideal random complexity beside the proposal scaling."""

from __future__ import annotations

import csv
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

import report_fixed_accuracy_rescue as proposal_report
import row_cap_grid_study as grid
import sublinear_pilot_study as phase1
from validate import digest


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT/'results'/'random_fixed_accuracy_scaling'
RESCUE = ROOT/'results'/'fixed_accuracy_rescue'
LABELS = proposal_report.LABELS


def load_json(path):
    return json.loads(Path(path).read_text())


def write_csv(path, rows):
    fields = list(rows[0]) if rows else []
    with Path(path).open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def slope_rows(final):
    rows = []
    for target in phase1.TARGETS:
        local = sorted([row for row in final
                        if row['target'] == target and row['confirmed']],
                       key=lambda row: row['n'])
        if len(local) >= 2:
            fit = np.polyfit(np.log([row['n'] for row in local]),
                             np.log([row['budget'] for row in local]), 1)
            exponent, intercept = map(float, fit)
        else:
            exponent = intercept = None
        rows.append({'target': target, 'confirmed_points': len(local),
                     'OLS_exponent': exponent, 'OLS_intercept': intercept})
    return rows


def plot_scaling(out, combined, final, slopes):
    fig, axes = plt.subplots(2, 2, figsize=(10.5, 7.5), squeeze=False,
                             constrained_layout=True)
    proposal_slopes = {row['target']: row for row in combined['slopes']}
    random_slopes = {row['target']: row for row in slopes}
    n_grid = list(phase1.N_GRID)
    for ax, target in zip(axes.flat, phase1.TARGETS):
        proposal = [row for row in combined['points'] if row['target'] == target]
        confirmed = [row for row in proposal if row['confirmed']]
        failed = [row for row in proposal if not row['confirmed']]
        if confirmed:
            ax.errorbar([row['n'] for row in confirmed],
                        [row['mean_Q'] for row in confirmed],
                        yerr=[row['Q_se'] or 0. for row in confirmed],
                        color='#0072b2', marker='o', lw=1.5, capsize=2.5,
                        label='proposal 6/6')
        if failed:
            ax.scatter([row['n'] for row in failed],
                       [row['mean_Q_spent'] for row in failed], marker='x',
                       color='#d55e00', s=38, label='proposal not 6/6')
            for row in failed:
                ax.annotate(f'{row["successes"]}/{row["runs"]}',
                            (row['n'], row['mean_Q_spent']), xytext=(2, 4),
                            textcoords='offset points', fontsize=6)
        proposal_fit = proposal_slopes[target]
        if proposal_fit['OLS_exponent'] is not None:
            xs = np.asarray([point[0] for point in proposal_fit['points']], dtype=float)
            ys = np.exp(proposal_fit['OLS_intercept'])*xs**proposal_fit['OLS_exponent']
            ax.plot(xs, ys, ':', color='#0072b2', lw=1.0,
                    label=f'proposal fit a={proposal_fit["OLS_exponent"]:.2f}')

        random = sorted([row for row in final if row['target'] == target],
                        key=lambda row: row['n'])
        random_ok = [row for row in random if row['confirmed']]
        random_bad = [row for row in random if not row['confirmed']]
        if random_ok:
            ax.plot([row['n'] for row in random_ok],
                    [row['budget'] for row in random_ok], '--s',
                    color='#4d4d4d', markerfacecolor='white', markersize=4.5,
                    lw=1.35, label='random raw Q* (6/6)')
        if random_bad:
            ax.scatter([row['n'] for row in random_bad],
                       [row['budget'] for row in random_bad], marker='x',
                       color='#7f3c8d', s=38, label='random not 6/6')
        random_fit = random_slopes[target]
        if random_fit['OLS_exponent'] is not None:
            xs = np.asarray([row['n'] for row in random_ok], dtype=float)
            ys = np.exp(random_fit['OLS_intercept'])*xs**random_fit['OLS_exponent']
            ax.plot(xs, ys, ':', color='#4d4d4d', lw=.9,
                    label=f'random fit a={random_fit["OLS_exponent"]:.2f}')
        ax.plot(n_grid, n_grid, '--', color='black', lw=.8, label='Q=N cap')
        ax.set_xscale('log', base=2)
        ax.set_yscale('log', base=2)
        ax.set_xticks(n_grid, [str(n) for n in n_grid], rotation=35)
        ax.grid(alpha=.2)
        ax.set_title(LABELS[target])
        ax.set_xlabel('N')
        ax.set_ylabel('raw Q at fixed accuracy')
        ax.legend(fontsize=6.5)
    fig.suptitle('Noiseless constant-edge fixed-accuracy scaling: proposal and random')
    path = out/'ideal_fixed_accuracy_with_random_Q.png'
    fig.savefig(path, dpi=190)
    plt.close(fig)
    return path


def write_report(out, final, slopes):
    slope = {row['target']: row for row in slopes}
    lines = ['# Noiseless constant-edge random complexity', '',
        ('各treeで既存の絶対K_starを固定し、balanced random batchの最小query数を'
         'developmentで探索した後、未使用seedで確認した。比率ではなくraw Qを報告する。'), '',
        '| tree | confirmed | random slope | Q*(N=2048) | Q*(N=16384) |',
        '|---|---:|---:|---:|---:|']
    for target in phase1.TARGETS:
        local = sorted([row for row in final if row['target'] == target],
                       key=lambda row: row['n'])
        exponent = slope[target]['OLS_exponent']
        slope_text = '--' if exponent is None else f'{exponent:.3f}'
        if local:
            lines.append(f'| {LABELS[target]} | '
                         f'{sum(row["confirmed"] for row in local)}/{len(local)} | '
                         f'{slope_text} | {local[0]["budget"]} | '
                         f'{local[-1]["budget"]} |')
        else:
            # Smoke configurations intentionally omit some production targets.
            lines.append(f'| {LABELS[target]} | 0/0 | -- | -- | -- |')
    lines.extend(['',
        '主図ではproposalとrandomの両方を同じraw-Q軸へ置いた。randomの選択にfresh結果を'
        '混ぜず、rescueが必要なcellでは第一確認群をdevelopmentへ降格し、第二確認群を使った。', ''])
    (out/'report_ja.md').write_text('\n'.join(lines))


def report(output=OUTPUT):
    out = Path(output)
    final = load_json(out/'final_summary.json')
    combined = load_json(RESCUE/'combined_scaling.json')
    slopes = slope_rows(final)
    write_csv(out/'random_fixed_accuracy_summary.csv', final)
    write_csv(out/'random_fixed_accuracy_slopes.csv', slopes)
    figure = plot_scaling(out, combined, final, slopes)
    write_report(out, final, slopes)
    names = [figure.name, 'random_fixed_accuracy_summary.csv',
             'random_fixed_accuracy_slopes.csv', 'report_ja.md']
    manifest = {
        'study': load_json(out/'design.json')['study'],
        'artifacts_sha256': {name: digest(out/name) for name in names},
    }
    grid.atomic_json(out/'report_manifest.json', manifest)
    return manifest


if __name__ == '__main__':
    report()
