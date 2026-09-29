"""Render the paper-facing strict fixed-accuracy figure in a 1-by-4 layout.

This script is a layout-only companion to
``report_ideal_strict_fixed_accuracy.py``.  It reads the same frozen summary
data and neither reruns nor retunes either sampler.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np


ROOT = Path(__file__).resolve().parent
DEFAULT_RESULTS = (
    ROOT
    / "results"
    / "ideal_capless_fixed_accuracy_scaling"
    / "random_per_run_threshold_search_k1em5L0"
)
OUTPUT_STEM = "ideal_strict_fixed_accuracy_linear_errorbars_1x4"


def load_json(path):
    return json.loads(Path(path).read_text())


def digest(path):
    value = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            value.update(block)
    return value.hexdigest()


def segment_styles(rows):
    """Use dashed segments only next to an unconfirmed point."""
    return [
        "-" if rows[index]["confirmed"] and rows[index + 1]["confirmed"] else "--"
        for index in range(len(rows) - 1)
    ]


def draw_curve(ax, rows, color, error_color, method, large_text=False):
    """Draw one method while preserving the frozen means and min--max ranges."""
    line_width = 1.7 if large_text else 1.35
    marker_area = 29 if large_text else 19
    open_marker_area = 30 if large_text else 20
    triangle_area = 36 if large_text else 25
    marker_edge_width = 1.15 if large_text else 0.9
    error_line_width = 0.9 if large_text else 0.7
    error_cap_size = 2.1 if large_text else 1.7
    ordered = sorted(rows, key=lambda row: row["n"])
    true_x = np.asarray([row["n"] for row in ordered], dtype=float)
    display_factor = 0.994 if method == "proposal" else 1.006
    x = true_x * display_factor
    y = np.asarray([row["Q"] for row in ordered], dtype=float)
    lower = y - np.asarray([row["Q_min"] for row in ordered], dtype=float)
    upper = np.asarray([row["Q_max"] for row in ordered], dtype=float) - y

    for index, style in enumerate(segment_styles(ordered)):
        ax.plot(
            x[index : index + 2],
            y[index : index + 2],
            color=color,
            linestyle=style,
            linewidth=line_width,
            zorder=3,
        )

    confirmed = np.asarray([row["confirmed"] for row in ordered], dtype=bool)
    if method == "proposal":
        ax.scatter(
            x[confirmed], y[confirmed], color=color, marker="o",
            s=marker_area, zorder=5,
        )
    else:
        ax.scatter(
            x[confirmed],
            y[confirmed],
            facecolors="white",
            edgecolors=color,
            marker="s",
            linewidths=marker_edge_width,
            s=open_marker_area,
            zorder=5,
        )
    ax.scatter(
        x[~confirmed],
        y[~confirmed],
        facecolors="white",
        edgecolors=color,
        marker="^",
        linewidths=marker_edge_width,
        s=triangle_area,
        zorder=5,
    )

    # Draw the range above each marker.  The contrasting cap records even the
    # proposal ranges that are shorter than a marker without enlarging them.
    ax.errorbar(
        x,
        y,
        yerr=np.vstack([lower, upper]),
        fmt="none",
        ecolor=error_color,
        elinewidth=error_line_width,
        capthick=error_line_width,
        capsize=error_cap_size,
        zorder=6,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--results",
        type=Path,
        default=DEFAULT_RESULTS,
        help="Result directory containing figure_data.json and design.json.",
    )
    parser.add_argument(
        "--large-text",
        action="store_true",
        help="Render a small-inclusion variant with larger type and marks.",
    )
    args = parser.parse_args()
    results = args.results.resolve()
    input_path = results / "figure_data.json"
    design_path = results / "design.json"
    output_stem = OUTPUT_STEM + ("_large_text" if args.large_text else "")
    stem = results / output_stem

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    from matplotlib.ticker import FuncFormatter

    data = load_json(input_path)
    design = load_json(design_path) if design_path.exists() else {}
    proposal, random_rows = data["proposal"], data["random"]
    targets = ["matching", "path", "binary", "stars_original"]
    titles = {
        "matching": "(a) Matching",
        "path": "(b) Path",
        "binary": "(c) Binary tree",
        "stars_original": "(d) Growing stars",
    }
    blue, blue_dark = "#0072B2", "#003F66"
    orange, orange_dark = "#D55E00", "#803800"
    style = {
        "title": 9.4 if args.large_text else 8.0,
        "tick": 7.3 if args.large_text else 6.1,
        "axis_label": 9.0 if args.large_text else 7.2,
        "legend": 6.7 if args.large_text else 5.4,
        "legend_marker": 5.0 if args.large_text else 4.0,
        "line": 1.7 if args.large_text else 1.35,
        "reference_line": 1.25 if args.large_text else 1.0,
        "spine": 0.8 if args.large_text else 0.65,
    }

    # The physical size targets a two-column paper width.  Shared axes and a
    # common x label keep all four narrow panels legible after PDF inclusion.
    fig, axes = plt.subplots(1, 4, figsize=(7.2, 1.95), sharex=True, sharey=True)
    maximum = max(
        max(row["Q_max"] for row in proposal + random_rows), max(data["n_grid"])
    )
    for ax, target in zip(axes, targets):
        p_rows = [row for row in proposal if row["target"] == target]
        r_rows = [row for row in random_rows if row["target"] == target]
        draw_curve(ax, p_rows, blue, blue_dark, "proposal", args.large_text)
        draw_curve(ax, r_rows, orange, orange_dark, "random", args.large_text)
        bounds = np.asarray(data["n_grid"], dtype=float)
        ax.plot(
            bounds, bounds, color=".45", linestyle=":",
            linewidth=style["reference_line"],
        )
        ax.set_title(titles[target], fontsize=style["title"], pad=1.5)
        ax.grid(alpha=0.23, linewidth=0.45)
        ax.set_xlim(min(data["n_grid"]) - 500, max(data["n_grid"]) + 500)
        ax.set_ylim(0, maximum * 1.08)
        ax.set_xticks(data["n_grid"])
        ax.xaxis.set_major_formatter(
            FuncFormatter(lambda value, _position: f"{value / 1024:g}k")
        )
        ax.yaxis.set_major_formatter(
            FuncFormatter(lambda value, _position: f"{int(value):,}")
        )
        ax.tick_params(
            axis="both", labelsize=style["tick"], length=2.8,
            width=style["spine"],
        )
        for spine in ax.spines.values():
            spine.set_linewidth(style["spine"])

    y_label = (
        "Mean total oracle rounds\n" + r"$Q_{\mathrm{tot}}$"
        if args.large_text
        else r"Mean total oracle rounds $Q_{\mathrm{tot}}$"
    )
    axes[0].set_ylabel(
        y_label,
        fontsize=style["axis_label"],
        labelpad=3.0,
    )
    fig.supxlabel(r"Sequence length $N$", fontsize=style["axis_label"], y=0.012)

    handles = [
        Line2D(
            [0],
            [0],
            color=blue,
            marker="o",
            linewidth=style["line"],
            markersize=style["legend_marker"],
            label="Proposal",
        ),
        Line2D(
            [0],
            [0],
            color=orange,
            marker="s",
            markerfacecolor="white",
            linewidth=style["line"],
            markersize=style["legend_marker"],
            label="Random",
        ),
        Line2D(
            [0],
            [0],
            color=".45",
            linestyle=":",
            linewidth=style["reference_line"],
            label=r"$Q_{\mathrm{tot}}=N$",
        ),
    ]
    axes[0].legend(
        handles=handles,
        loc="upper left",
        ncol=1,
        frameon=False,
        fontsize=style["legend"],
        handlelength=1.7,
        labelspacing=0.2,
        handletextpad=0.45,
        borderpad=0.15,
    )
    if args.large_text:
        fig.subplots_adjust(left=0.09, right=0.995, bottom=0.25, top=0.87, wspace=0.16)
    else:
        fig.subplots_adjust(left=0.075, right=0.995, bottom=0.22, top=0.88, wspace=0.14)
    fig.savefig(stem.with_suffix(".png"), dpi=300, bbox_inches="tight", pad_inches=0.015)
    fig.savefig(stem.with_suffix(".pdf"), bbox_inches="tight", pad_inches=0.015)
    plt.close(fig)

    metadata = {
        "input": str(input_path.relative_to(ROOT)),
        "input_sha256": digest(input_path),
        "design": str(design_path.relative_to(ROOT)) if design_path.exists() else None,
        "design_sha256": digest(design_path) if design_path.exists() else None,
        "relative_L0_factor": design.get("relative_L0_factor"),
        "script": str(Path(__file__).resolve().relative_to(ROOT)),
        "script_sha256": digest(__file__),
        "png": str(stem.with_suffix(".png").relative_to(ROOT)),
        "pdf": str(stem.with_suffix(".pdf").relative_to(ROOT)),
        "layout": "1x4",
        "figure_size_inches": [7.2, 1.95],
        "presentation_variant": "large_text" if args.large_text else "standard",
        "font_sizes_points": {
            "panel_title": style["title"],
            "tick": style["tick"],
            "axis_label": style["axis_label"],
            "legend": style["legend"],
        },
        "axes": "linear-linear",
        "x_tick_display": "N / 1024, with k suffix",
        "in_figure_title": None,
        "in_figure_setting_annotation": None,
        "setting_location": "external paper caption and appendix",
        "vertical_quantity": "mean total oracle rounds, Q_tot = Q_pre + Q_cf + R",
        "point": "mean total oracle-round count over six evaluation pairs",
        "error_bar": "minimum--maximum over the same six evaluation pairs",
        "error_bar_is_not": "standard error or confidence interval",
        "proposal_note": (
            "Small proposal ranges are drawn above markers in a darker hue; "
            "their data-space lengths are not enlarged."
        ),
        "random_estimand": data["random_estimand"],
    }
    stem.with_suffix(".json").write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False) + "\n"
    )


if __name__ == "__main__":
    main()
