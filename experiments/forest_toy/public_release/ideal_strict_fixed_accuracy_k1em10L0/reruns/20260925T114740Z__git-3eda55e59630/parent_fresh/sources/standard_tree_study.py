"""Extend the noiseless bounded-bias experiment to standard forest shapes.

Please vary topology with a fixed unary law, vocabulary, and coupling rule.
The sampler and seven baseline policies are reused through worker-local adapters.
General-tree measurement uses exact small factors plus a reported MC standard
error; no passive evaluation call contributes information to the controller.
"""
import argparse
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from contextlib import contextmanager
import fcntl
from functools import partial
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
from time import perf_counter
import traceback

import numpy as np

import explore_minimal as base
import minimal_study
import row_cap_grid_study as grid
import strong_path_baseline_study as controls
import strong_path_pivot_study as pivot
from forest_kl import ForestRecorder, initial_edges, load_backend
from minimal_oracle import MinimalOracle, field_seed, load_backend as load_oracle_backend
from profile_minimal import weighted_summary
from robustness_study import seeds_for
from validate import digest, freeze_json, read_runs
from weighted_oracle import make_weighted_target


ROOT=Path(__file__).resolve().parent
OUTPUT=ROOT/'results'/'standard_tree_study'
CASE='standard_constant_coupling_uniform1'
TARGETS=('matching','binary','stars_original')
SOURCES=tuple(dict.fromkeys((*controls.SOURCES,'forest_kl.py','forest_batch_kl.c',
    'test_forest_kl.py','standard_tree_study.py','test_standard_trees.py','report_standard_trees.py')))


def make_target(target,n,repeat,biased=True,weak_tail=False,sigma=None,kind='proposal',budget=0):
    data,algorithm=pivot.seed_pair(repeat)
    prototype,data_seeds=make_weighted_target(target,n,data,'original_uniform',kind,budget)
    # Please pair the fields at each public position across all tree shapes.
    # This also preserves the previously evaluated path law exactly.
    unary_seed=field_seed('path',n,data)
    fields=np.random.default_rng(unary_seed).uniform(-1.,1.,n)
    oracle=MinimalOracle(n,prototype.edges,np.full(len(prototype.edges),prototype.theta),
                         prototype.theta,fields,vocab=2048)
    oracle.weight_seed=None
    oracle.field_seed=unary_seed
    oracle.tail_shape=None
    oracle.target_law=CASE
    sampler=seeds_for('path',n,algorithm,kind,budget)
    return oracle,[data_seeds[0],*sampler[1:]]


def evaluation_seed(job):
    payload=('standard-tree-passive-kl-v1|'+controls.job_key(job)).encode()
    return int.from_bytes(hashlib.sha256(payload).digest()[:8],'little')


@contextmanager
def adapters(job):
    target=job['target']
    saved=(base.make_target,base.MinimalRecorder,minimal_study.case_name,
           pivot.make_target,pivot.tag,controls.MinimalRecorder)
    factory=lambda _target,*args,**kwargs: make_target(target,*args,**kwargs)
    recorder=partial(ForestRecorder,seed=evaluation_seed(job),samples=job['evaluation_samples'],
                     exact_arity=job['evaluation_exact_arity'])
    base.make_target= pivot.make_target = factory
    base.MinimalRecorder= controls.MinimalRecorder = recorder
    minimal_study.case_name=lambda *_: CASE
    pivot.tag=lambda row: row
    try:
        yield
    finally:
        (base.make_target,base.MinimalRecorder,minimal_study.case_name,
         pivot.make_target,pivot.tag,controls.MinimalRecorder)=saved


def run_job(job,output,query_limit='target_n'):
    with adapters(job):
        if job['kind']=='proposal':
            repeat=pivot.repeat_id(job['data'],job['algorithm'])
            legacy=base.proposal_job(job['target'],job['n'],repeat,tuple(job['setting']))
            row=grid.run_proposal(legacy,Path(output),'topd',query_limit=query_limit)
            row.update(study_job=job,method='proposal',source_job=row['job'])
        else:
            row=controls.run_job(job,Path(output))
    row.update(target=job['target'],case=CASE,target_law=CASE,weak_tail=False,sigma=None,
        field_distribution='Uniform[-1,1]',theta_distribution='constant 0.5 / maximum degree',
        theta_reference=row['weight_max'],tail_shape_b=None,data_repeat=job['data'],
        algorithm_repeat=job['algorithm'],graph_seed=row['seeds'][0],
        controller_seed=row['seeds'][1],commit_seed=row['seeds'][2],
        seed_design='Shared public-position fields and algorithm streams across shapes; separate hidden graph seed.',
        evaluation_seed=evaluation_seed(job))
    return row


def proposal_settings(target,smoke=False):
    if smoke:
        return [(3,7,18,.001),(3,11,36,.001)]
    if target=='matching':
        plans={3:(25,41,57),4:(21,33,45),6:(17,25,33)}
        chosen={(p,m,d,.03) for p,ms in plans.items() for m in ms for d in (9,18)}
        chosen.update((4,33,d,.001) for d in (9,18))
    elif target=='binary':
        plans={8:(53,65,77),10:(41,53,65),12:(33,41,49)}
        chosen={(p,m,d,.01) for p,ms in plans.items() for m in ms for d in (18,36)}
        chosen.update((p,m,18,tau) for p,m in ((8,65),(10,53)) for tau in (.001,.02))
    elif target=='stars_original':
        theta=.5/128
        plans={4:(17,25,33),6:(17,25,33,41),8:(13,21,29)}
        chosen={(p,m,d,.04*theta) for p,ms in plans.items() for m in ms for d in (17,36)}
        chosen.update((6,25,36,ratio*theta) for ratio in (.004,.12))
    else:
        raise ValueError('Please use a supported extension shape.')
    return sorted(chosen)


def design(targets=TARGETS,smoke=False):
    config=controls.design(smoke)
    for key in ('proposal_settings','proposal_pivot','proposal_selection','target','target_law','theta'):
        config.pop(key,None)
    config.update(study='standard_tree_shapes',version=1,n=512 if smoke else 16384,
        targets=list(targets),target_law=CASE,
        coupling_rule='theta=0.5/maximum degree, constant on all edges of a target',
        shape_definitions={'matching':'Disjoint pairs, plus one isolate if N is odd.',
            'binary':'Complete binary tree in breadth-first order, then hidden relabeling.',
            'stars_original':'Star forest with max(16,ceil(sqrt(N))) leaves per full component, then hidden relabeling.'},
        field_pairing='h_i are the same Uniform[-1,1] draws at each public position across shapes and the previous path.',
        proposal_grids={t:proposal_settings(t,smoke) for t in targets},
        evaluation={'samples_per_large_factor':128,'exact_boundary_arity':4,
            'oracle':'Exact and noiseless throughout generation.',
            'metric':'Same conditional reverse KL as the path study. Factor boundaries of size <=4 are enumerated; larger ones use independent product-marginal MC.',
            'uncertainty':'Report conditional measurement SE separately from per-target/algorithm variation; combine independent factor and batch variances.',
            'structural_zero':'One selected vertex per remaining true component gives exact KL=0; no MC is needed.'},
        fixed_budgets=[4,32] if smoke else [1,64,256,1024,4096,8192,12288],
        eb_gammas=[1.5,4.] if smoke else [1.,1.5,1.75,2.,2.5,3.,4.,8.,16.,64.],
        proposal_selection={'controls':'Cheapest complete setting; minimum Q at mean KL plus 2 measurement SE <=1e-6 and <=1e-10; minimum depth at <=1e-10. At most four per shape.',
            'failure':'If no exploratory run setting completes, retain the cheapest censored setting as an explicit failure control.',
            'freeze':'Use exploration only. Do not select on confirmation seeds or baseline outcomes.'},
        selection_rule={'baseline':'Per method: minimum KL upper estimate at Q<=N/4; minimum Q reaching KL upper estimate <=1e-6 and <=1e-10. At most three per method; retain minimum-error setting when a level is unattained.',
            'upper_estimate':'Mean conditional KL + 2 times MC measurement SE; this is not a success-probability confidence bound.',
            'freeze':'Freeze each method separately before confirmation; no post-confirmation ordering selection.'},
        source_sha256={name:digest(ROOT/name) for name in SOURCES})
    config['matched_budget']='Also include rounded exploratory mean Q of the cheapest complete proposal reaching KL upper<=1e-6, or the cheapest complete proposal if none reaches it.'
    config['seed_roles']['data']='Hidden relabeling of the selected shape and unary fields; paired across methods and parameters. Public-position fields are also paired across shapes.'
    config['metrics']['KL']=config['evaluation']['metric']
    return config


def make_jobs(config,target,pairs,settings,kind):
    common={'n':config['n'],'target':target,
            'evaluation_samples':config['evaluation']['samples_per_large_factor'],
            'evaluation_exact_arity':config['evaluation']['exact_boundary_arity']}
    return [dict(common,kind=kind,data=data,algorithm=algorithm,
                 **({'setting':list(setting)} if kind=='proposal' else
                    {k:setting[k] for k in ('family','ordering','parameter')}))
            for setting in settings for data,algorithm in pairs]


def ensure_profiles(jobs,output):
    entries=[]
    for target,n,data,algorithm in sorted({(j['target'],j['n'],j['data'],j['algorithm']) for j in jobs}):
        repeat=pivot.repeat_id(data,algorithm)
        oracle,seeds=make_target(target,n,repeat)
        rows,weights,total=initial_edges(oracle)
        path=output/'target_profiles'/f'{target}_{CASE}_seed{repeat}.npz'
        path.parent.mkdir(parents=True,exist_ok=True)
        arrays=dict(edges=oracle.edges,theta=oracle.edge_strengths,fields=oracle.fields,
                    initial_rows=rows,initial_edge_kl=weights)
        if path.exists():
            with np.load(path) as saved:
                for name,values in arrays.items(): np.testing.assert_array_equal(saved[name],values)
        else:
            np.savez_compressed(path,**arrays)
        entries.append({'target':target,'n':n,'repeat':repeat,'data_repeat':data,'algorithm_repeat':algorithm,
            'theta':oracle.theta,'maximum_degree':oracle.max_degree,'seeds':seeds,
            'fields_sha256':controls.array_hash(oracle.fields,'<f8'),
            'all_at_once_kl_per_token':total/n,'confidence':weighted_summary([rows[:,:2].max(axis=1)]),
            'snapshot':str(path.relative_to(output)),'sha256':digest(path)})
    freeze_json(output/'target_profiles.json',entries)


def aggregate(rows):
    groups=defaultdict(list)
    for row in rows: groups[controls.setting_key(row)].append(row)
    result=controls.aggregate(rows)
    for item in result:
        group=groups[tuple(item['key'])]
        item['KL_mc_SE']=(float(np.sqrt(sum(r.get('kl_mc_se_per_token',0.)**2 for r in group))/len(group))
                           if not item['censored'] else None)
        item['KL_upper']=item['KL']+2*item['KL_mc_SE'] if item['KL'] is not None else None
        item['exact_evaluation_runs']=sum(r.get('kl_evaluation_exact',False) for r in group)
        item['unsafe_runs']=sum(bool(r.get('unsafe_batches')) for r in group)
        item['fallback_runs']=sum(bool(r.get('fallback')) for r in group)
        for name in ('preprocessing','counterfactual','rounds','screen_calls'):
            item[name]=float(np.mean([r.get(name,0) for r in group]))
    return result


def select_proposals(rows):
    groups=aggregate(rows)
    good=[r for r in groups if not r['censored']]
    if not good:
        fallback=min(groups,key=lambda r:(r['Q'],r['key']))
        return {'settings':[fallback['key'][1:]],'reasons':['No complete setting; censored failure control.']}
    cost=lambda r:(r['Q'],max(1e-12,r['KL_upper']),r['key'])
    chosen={tuple(min(good,key=cost)['key'][1:]):['cheapest complete']}
    for epsilon in (1e-6,1e-10):
        eligible=[r for r in good if r['KL_upper']<=epsilon]
        if eligible:
            row=min(eligible,key=cost)
            chosen.setdefault(tuple(row['key'][1:]),[]).append(f'min Q at KL upper<={epsilon:g}')
    eligible=[r for r in good if r['KL_upper']<=1e-10]
    if eligible:
        row=min(eligible,key=lambda r:(r['T'],*cost(r)))
        chosen.setdefault(tuple(row['key'][1:]),[]).append('min depth at KL upper<=1e-10')
    return {'settings':sorted(chosen),'reasons':[{'setting':k,'reasons':v} for k,v in sorted(chosen.items())]}


def initial_baselines(config,proposals):
    budgets=set(config['fixed_budgets'])
    good=[r for r in aggregate(proposals) if not r['censored']]
    eligible=[r for r in good if r['KL_upper']<=1e-6]
    if good:
        row=min(eligible or good,key=lambda r:(r['Q'],r['KL_upper'],r['key']))
        budgets.add(int(np.floor(row['Q']+.5)))
    return ([{'family':'fixed','ordering':policy,'parameter':b}
             for policy in config['fixed_orderings'] for b in sorted(budgets)]
            +[{'family':'eb','ordering':policy,'parameter':gamma}
              for policy in config['eb_orderings'] for gamma in config['eb_gammas']])


def select_baselines(config,rows):
    groups=aggregate(rows); chosen={}
    for method in sorted({r['method'] for r in groups}):
        local=[r for r in groups if r['method']==method]
        quality=lambda r:(max(1e-12,r['KL_upper']),r['Q'],r['key'][1])
        cost=lambda r:(r['Q'],max(1e-12,r['KL_upper']),r['key'][1])
        bounded=[r for r in local if r['Q']<=config['n']/4]
        selected=[(min(bounded,key=quality) if bounded else min(local,key=cost),'Q<=N/4 control')]
        for epsilon in (1e-6,1e-10):
            eligible=[r for r in local if r['KL_upper']<=epsilon]
            selected.append((min(eligible,key=cost) if eligible else min(local,key=quality),
                             f'KL upper<={epsilon:g}' if eligible else f'unattained {epsilon:g}; minimum error'))
        for row,reason in selected:
            key=tuple(row['key'])
            if key not in chosen:
                family,ordering=method.split('_',1)
                chosen[key]={'family':family,'ordering':ordering,'parameter':key[1],
                             'reasons':[],'explore_Q':row['Q'],'explore_KL':row['KL'],
                             'explore_KL_mc_SE':row['KL_mc_SE']}
            chosen[key]['reasons'].append(reason)
    return {'settings':[chosen[k] for k in sorted(chosen)],'rule':config['selection_rule']}


def execute(out,config,target,phase,kind,jobs,workers,state):
    local=out/target/phase/kind; local.mkdir(parents=True,exist_ok=True)
    freeze_json(local/'jobs.json',jobs)
    if kind=='proposals': ensure_profiles(jobs,local)
    path=local/'runs.jsonl'; rows=read_runs(path)
    done={controls.job_key(r['study_job']) for r in rows}
    wanted={controls.job_key(j) for j in jobs}
    assert len(done)==len(rows) and done<=wanted and len(wanted)==len(jobs)
    state.update(target=target,stage=phase+'_'+kind,stage_jobs=len(jobs),stage_finished=len(rows),updated_utc=grid.utc())
    grid.atomic_json(out/'status.json',state)
    with ProcessPoolExecutor(max_workers=workers) as pool,path.open('a') as stream:
        futures=[pool.submit(run_job,j,local) for j in jobs if controls.job_key(j) not in done]
        for future in as_completed(futures):
            row=future.result(); rows.append(row)
            stream.write(json.dumps(row,separators=(',',':'),allow_nan=False)+'\n');stream.flush()
            state.update(stage_finished=len(rows),updated_utc=grid.utc())
            grid.atomic_json(out/'status.json',state)
            if len(rows)%10==0 or len(rows)==len(jobs):
                print(f'{target}/{phase}/{kind} {len(rows)}/{len(jobs)} {row["method"]} '
                      f'Q={row["total"]} KL/N={row["kl_per_token"]} '
                      f'MC_SE={row.get("kl_mc_se_per_token")} {row["status"]}',flush=True)
    return rows


def audit(out,config,target,records):
    # Please reuse the existing trajectory and cost audit, then check the new
    # measurement fields and that evaluation did not charge generation queries.
    result=controls.audit(out/target,config,records)
    measured=exact=0
    for phase,kinds in records.items():
        for kind,rows in kinds.items():
            for row in rows:
                assert row['target']==target and row['theta_reference']*row['max_degree']<=.5+1e-12
                if row['status']!='complete': continue
                assert np.isfinite(row['kl_mc_se_per_token']) and row['kl_mc_se_per_token']>=0
                measured+=1
                exact+=row['kl_evaluation_exact']
                if row['kl_evaluation']=='exact_chain': continue
                with np.load(out/target/phase/kind/row['trace']) as saved:
                    variance=saved['batch_mc_variance']
                    assert len(variance)==row['rounds'] and (variance>=0).all()
                    np.testing.assert_allclose(variance.sum(),row['kl_mc_variance'],atol=1e-20,rtol=1e-12)
                    assert abs(np.sqrt(variance.sum())/row['n']-row['kl_mc_se_per_token'])<1e-16
    freeze_json(out/target/'evaluation_audit.json',{'completed_scores':measured,'exact_scores':int(exact),
        'oracle_exact':True,'measurement_variances_valid':True})
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--targets',nargs='+',choices=TARGETS,default=list(TARGETS))
    parser.add_argument('--workers',type=int,default=6)
    parser.add_argument('--output',type=Path,default=OUTPUT)
    parser.add_argument('--smoke',action='store_true')
    parser.add_argument('--prepare-only',action='store_true')
    parser.add_argument('--plan-only',action='store_true')
    args=parser.parse_args()
    if args.workers<1 or len(set(args.targets))!=len(args.targets): parser.error('Please use distinct targets and positive workers.')
    config=design(tuple(args.targets),args.smoke)
    if args.plan_only: print(json.dumps(config,indent=2)); return
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    with (out/'runner.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        freeze_json(out/'design.json',config)
        sources=out/'sources';sources.mkdir(exist_ok=True)
        for name,checksum in config['source_sha256'].items():
            dest=sources/name
            if not dest.exists(): shutil.copyfile(ROOT/name,dest)
            assert digest(dest)==checksum
        if args.prepare_only:
            grid.atomic_json(out/'status.json',{'status':'prepared','stage':'prepared','output':str(out),'updated_utc':grid.utc()});return
        started=perf_counter()
        state={'status':'running','stage':'preparing','pid':os.getpid(),'workers':args.workers,
               'targets':args.targets,'completed_targets':[],'started_utc':grid.utc(),'output':str(out)}
        grid.atomic_json(out/'status.json',state)
        try:
            load_backend();load_oracle_backend()
            total_proposals=total_baselines=0
            for target in args.targets:
                local=out/target;local.mkdir(exist_ok=True)
                records={'explore':{},'confirm':{}}
                records['explore']['proposals']=execute(out,config,target,'explore','proposals',
                    make_jobs(config,target,config['explore_pairs'],config['proposal_grids'][target],'proposal'),args.workers,state)
                proposal_selection=select_proposals(records['explore']['proposals'])
                freeze_json(local/'proposal_selection.json',proposal_selection)
                baseline_grid=initial_baselines(config,records['explore']['proposals'])
                freeze_json(local/'explore_baseline_settings.json',baseline_grid)
                records['explore']['baselines']=execute(out,config,target,'explore','baselines',
                    make_jobs(config,target,config['explore_pairs'],baseline_grid,'baseline'),args.workers,state)
                selection=select_baselines(config,records['explore']['baselines'])
                freeze_json(local/'baseline_selection.json',selection)
                records['confirm']['proposals']=execute(out,config,target,'confirm','proposals',
                    make_jobs(config,target,config['confirm_pairs'],proposal_selection['settings'],'proposal'),args.workers,state)
                records['confirm']['baselines']=execute(out,config,target,'confirm','baselines',
                    make_jobs(config,target,config['confirm_pairs'],selection['settings'],'baseline'),args.workers,state)
                audit(out,config,target,records)
                from report_standard_trees import report
                report(out)
                state['completed_targets'].append(target)
                total_proposals+=sum(len(r['proposals']) for r in records.values())
                total_baselines+=sum(len(r['baselines']) for r in records.values())
                state.update(proposal_runs=total_proposals,baseline_runs=total_baselines,updated_utc=grid.utc())
                grid.atomic_json(out/'status.json',state)
            for name,checksum in config['source_sha256'].items(): assert digest(ROOT/name)==checksum
            state.update(status='complete',stage='complete',finished_utc=grid.utc(),seconds=perf_counter()-started)
            grid.atomic_json(out/'status.json',state)
            print(json.dumps(state,indent=2),flush=True)
        except BaseException as error:
            state.update(status='failed',error=repr(error),traceback=traceback.format_exc(),updated_utc=grid.utc())
            grid.atomic_json(out/'status.json',state);raise


if __name__=='__main__':
    main()
