"""Report standard shapes with conditional KL measurement error kept explicit."""
from collections import defaultdict
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

from report_strong_path_baselines import COLORS, FLOOR, LABELS, write_csv
from standard_tree_study import aggregate
from strong_path_baseline_study import setting_key
from validate import read_runs

NAMES={'matching':'Matching','binary':'Binary tree','stars_original':'Star forest'}


def points_with_error(rows,metric):
    """Please average identical x coordinates before connecting the plotted points.

    The mean of component SEs is a conservative measurement SE after merging:
    unlike a quadrature rule it does not assume independent evaluations of two
    parameter settings that may in fact produce identical trajectories.
    """
    grouped=defaultdict(list)
    for row in rows:
        grouped[float(row[metric])].append(row)
    return [(x,float(np.mean([r['KL'] for r in group])),
             float(np.mean([r['KL_mc_SE'] for r in group])))
            for x,group in sorted(grouped.items())]


def plot(out,phase,by_shape,config,metric):
    targets=config['targets']
    fig,axes=plt.subplots(1,len(targets),figsize=(6*len(targets),5.8),squeeze=False)
    handles={}
    for ax,target in zip(axes[0],targets):
        groups=[r for r in by_shape.get(target,[]) if not r['censored']]
        for method,label in {**LABELS,'proposal':'Proposal / keep-top-d'}.items():
            local=[r for r in groups if r['method']==method]
            points=points_with_error(local,metric)
            if not points:
                continue
            x,raw,se=map(np.asarray,zip(*points))
            y=np.maximum(raw,FLOOR)
            lo=np.maximum(raw-2*se,FLOOR)
            hi=np.maximum(raw+2*se,FLOOR)
            if method=='proposal':
                color,style,marker,size='#d5443e','none','*',9
            else:
                family,ordering=method.split('_',1)
                color=COLORS[ordering]
                style,marker,size=('-','s',3.5) if family=='eb' else ('--','o',3.5)
            artist=ax.errorbar(x,y,yerr=np.vstack((y-lo,hi-y)),color=color,linestyle=style,
                marker=marker,markersize=size,linewidth=1.3,elinewidth=.8,capsize=2,
                alpha=.9,label=label,zorder=5 if method=='proposal' else 2)
            handles.setdefault(label,artist)
        high=max([r['KL']+2*r['KL_mc_SE'] for r in groups]+[FLOOR])*2
        ax.set(yscale='log',ylim=(FLOOR*.55,high),title=NAMES[target],
               xlabel='Mean total queries Q' if metric=='Q' else 'Mean sequential depth T (log scale)')
        if metric=='Q':
            ax.set_xlim(0,config['n']*1.025)
        else:
            ax.set_xscale('log');ax.set_xlim(.8,config['n']*1.15)
        ax.set_ylabel('Mean conditional reverse KL / token (nats)')
        ax.grid(alpha=.2)
        if not groups:
            ax.text(.5,.5,'Pending',transform=ax.transAxes,ha='center')
    fig.suptitle(f'Standard trees | exact oracle | N={config["n"]:,} | {phase} '
                 f'({len(config[phase+"_pairs"])} runs/setting)',fontsize=14)
    if handles:
        fig.legend(list(handles.values()),list(handles),loc='lower center',bbox_to_anchor=(.5,.047),ncol=4,fontsize=9)
    fig.text(.5,.016,'Bars: ±2 MC measurement SE only. Values <= 1e-12 share the display floor. '
             'Censored settings are listed separately.',ha='center',fontsize=9)
    fig.tight_layout(rect=(0,.18,1,.94))
    stem=f'{phase}_tradeoff' if metric=='Q' else f'{phase}_depth'
    for suffix in ('png','svg'):
        fig.savefig(out/f'{stem}.{suffix}',dpi=160,bbox_inches='tight')
    plt.close(fig)


def report(out):
    out=Path(out)
    config=json.loads((out/'design.json').read_text())
    lines=['# Standard-tree comparison','',
        '木の形をmatching・binary tree・従来のstar forestへ広げるのじゃ。pathは先行するstrong_path_baseline_studyで確認済みなのじゃ。','',
        f'N={config["n"]:,}、語彙2,048、単点場 h_i~Uniform[-1,1]、厳密oracle、temperature=1のsamplingを固定するのじゃ。',
        '結合は全辺一定のθ=0.5/最大次数なのじゃ。従来の次数に応じた規則なので、木を変えるとθも変わる点を区別して読むのじゃ。単点場は同じdata seedの公開位置ごとに木をまたいで共有するのじゃ。','',
        '提案法はkeep-top-d・first-bank draft・J=1・union採用・既存の次数優先cycle repairを維持するのじゃ。p・M・d・TV閾値を木ごとに探索し、探索結果のみから確認設定を固定するのじゃ。',
        '比較相手はrandom・confidence・margin・entropyのbalanced batchと、confidence/margin/entropy順のEB-Samplerなのじゃ。EBのentropyは元の2,048語彙上で計算するのじゃ。','',
        '探索は2組のdata/algorithm seeds、確認は5 data seeds×2 algorithm seedsなのじゃ（smokeは縮小）。target別平均・個別runも残し、10個の独立targetとしては扱わないのじゃ。','',
        'KLは各batchで product of current marginals から真の同時条件付き分布へのreverse KLを測り、和/tokenを取るのじゃ。matchingは厳密計算、一般の木は未選択成分の境界factorへ分解し、境界4頂点以下を厳密計算・それ以上を独立Monte Carloで評価するのじゃ。',
        f'大きなfactorごとに{config["evaluation"]["samples_per_large_factor"]}標本を用い、±2 MC標準誤差を図示するのじゃ。これは実現したhistoryに条件づけた測定誤差で、targetや生成乱択によるばらつきの信頼区間ではないのじゃ。構造的に独立なbatchのKL=0は厳密に判定するのじゃ。',
        '評価は生成後に別の乱数列で行い、controllerに情報を渡さずquery数にも加算しないのじゃ。評価時間は別列に記録するのじゃ。','',
        '同じ横軸の点は手法内で算術平均し、提案法は異なるハイパラの点なので線で結ばないのじゃ。Q=Nで打ち切った設定は別表に残し、KLを補完しないのじゃ。','']
    for phase in ('explore','confirm'):
        by_shape={}
        for target in config['targets']:
            local=out/target
            records=read_runs(local/phase/'proposals'/'runs.jsonl')+read_runs(local/phase/'baselines'/'runs.jsonl')
            if not records:
                continue
            groups=aggregate(records);by_shape[target]=groups
            (local/f'{phase}_aggregates.json').write_text(json.dumps(groups,indent=2,allow_nan=False)+'\n')
            write_csv(local/f'{phase}_summary.csv',groups)
            write_csv(local/f'{phase}_censored.csv',[r for r in groups if r['censored']])
            write_csv(local/f'{phase}_individual.csv',[dict(setting=list(setting_key(r)),
                **{k:r.get(k) for k in ('method','data_repeat','algorithm_repeat','status','total','depth',
                    'kl_per_token','kl_mc_se_per_token','kl_evaluation','unsafe_batches','fallback',
                    'sample_seconds','evaluation_seconds')}) for r in records])
            by_data=[]
            for data in sorted({r['data_repeat'] for r in records}):
                by_data.extend(dict(data_repeat=data,**r) for r in aggregate([r for r in records if r['data_repeat']==data]))
            write_csv(local/f'{phase}_by_target.csv',by_data)
        if not by_shape:
            continue
        for metric in ('Q','T'):
            plot(out,phase,by_shape,config,metric)
        lines += [f'## {phase}','',f'![{phase}]({phase}_tradeoff.png)','']
        for target,groups in by_shape.items():
            lines += [f'### {NAMES[target]}','',
                '| Method / setting | Mean Q | Median / p90 Q | Mean T | Mean KL/token ± MC SE | Complete |',
                '|---|---:|---:|---:|---:|---:|']
            for row in groups:
                description=('proposal '+str(row['key'][1:]) if row['method']=='proposal'
                             else LABELS[row['method']]+' / '+str(row['key'][1]))
                kl='censored' if row['KL'] is None else f'{row["KL"]:.6g} ± {row["KL_mc_SE"]:.2g}'
                lines.append(f'| {description} | {row["Q"]:.1f} | {row["Q_median"]:.1f} / {row["Q_p90"]:.1f} '
                    f'| {row["T"]:.1f} | {kl} | {row["complete"]}/{row["runs"]} |')
            lines += ['',f'設定別・個別run・target別・打切りの表は `{target}/{phase}_*.csv` に保存するのじゃ。','']
    lines += ['## References','',
        '厳密forest oracle上でsampling規則を比較する実験であり、元のMDM論文のタスク精度の再現ではないのじゃ。EBのforward-KL保証と今回のreverse-KL評価は区別するのじゃ。','',
        f'- Margin: {config["references"]["margin"]}',
        f'- EB-Sampler: {config["references"]["eb"]}',
        f'- EB rule: {config["references"]["eb_algorithm"]}','']
    (out/'report_ja.md').write_text('\n'.join(lines))


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output',type=Path)
    report(parser.parse_args().output)
