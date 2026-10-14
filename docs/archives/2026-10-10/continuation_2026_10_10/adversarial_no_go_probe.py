"""Independent finite probes for the full-beta material-factor obstruction.
Not a mechanized universal proof. Uses existing typed syntax/cut enumeration.
"""
import sys
from pathlib import Path
from collections import Counter
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'research_2026_10_10/material_bridge_client'))
import check_bridge as k
from dynamic_safe_experiment import root_reduce


def full_normal(t):
    children=tuple(full_normal(c) for c in t.children)
    t=k.T(t.kind,t.uid,t.typ,children,t.meta)
    reduct=root_reduce(t)
    return full_normal(reduct) if reduct is not None else t


def prof(t, leaves_only=False):
    ans=Counter()
    for forest,residual,_ in k.coaction(t):
        if leaves_only and any(p.children for p in forest):
            continue
        fs=tuple(sorted((k.key(p) for p in forest),key=repr))
        ans[(fs,k.key(full_normal(residual)))]+=1
    return ans


def make(shape,prefix='t'):
    return k.prim(prefix,'r' if shape else 'delta',('p',)*len(shape),'p',
                  *(make(s,prefix+str(i)) for i,s in enumerate(shape)))


def main():
    shapes=[(), ((),), ((),()), (((),),()), ((),((),())), (((),()),((),())),
            ((((),),()),((),(),()))]
    checked=0
    for shape in shapes[1:]:
        original=make(shape)
        # Includes every actual material-opening residual with positive root.
        for _,target,roots in k.coaction(original):
            if target.kind!='prim': continue
            for j,arg in enumerate(target.children):
                x=k.var('fresh_x','p')
                args=list(target.children); args[j]=x
                body=k.T(target.kind,target.uid,target.typ,tuple(args),target.meta)
                source=k.app('fresh_app',k.lam('fresh_lam',x,body),arg)
                assert k.check(source)==k.check(target)==()
                assert k.key(full_normal(source))==k.key(full_normal(target))
                before,after=prof(source),prof(target)
                diff=Counter({p:after[p]-before[p] for p in before.keys()|after.keys()
                              if after[p]!=before[p]})
                endpoint=k.T('hole',target.uid,target.typ,(),())
                expected=Counter({((k.key(target),),k.key(endpoint)):1})
                assert diff==expected,(shape,roots,j,diff,expected)
                assert prof(source,True)==prof(target,True)
                checked+=1
    print({'actual_typed_beta_pairs':checked,
           'full_defect':'exactly target_material_tree tensor complete_endpoint',
           'leaf_only_defect':0})

if __name__=='__main__': main()
