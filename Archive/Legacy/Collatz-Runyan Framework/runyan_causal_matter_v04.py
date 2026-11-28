"""Restricted 4D foliated triangulations and Kähler-Dirac determinant tests.
Not full CDT Monte Carlo, not physical Lorentzian spinors, no continuum claim.
Python 3, numpy, scipy. All masses dimensionless. Seed fixed.
"""
import itertools as it
import json, math
from pathlib import Path
import numpy as np
from scipy.sparse import coo_matrix, eye, bmat
from scipy.sparse.linalg import splu
from scipy.sparse.csgraph import shortest_path
from scipy.special import logsumexp

OUT=Path(__file__).resolve().parent

def sphere3(k):
    tets=[tuple(c) for c in it.combinations(range(5),4)]
    for j in range(k):
        t=tets.pop(0); v=5+j
        tets.extend(tuple(sorted(c+(v,))) for c in it.combinations(t,3))
    return tets,5+k

def foliated(tets,nv,nt,orders):
    # Staircase triangulation of each tetrahedron x interval; common order
    # on every tetrahedron in one slab ensures consistency on shared faces.
    cells=[]
    for t in range(nt):
        u=(t+1)%nt; rank=np.argsort(orders[t])
        for tet in tets:
            x=sorted(tet,key=lambda v:rank[v])
            for k in range(4):
                s=tuple(sorted([t*nv+v for v in x[:k+1]]+[u*nv+v for v in x[k:]]))
                cells.append(s)
                assert len(s)==5 and {v//nv for v in s}=={t,u}
    assert len(set(cells))==len(cells)
    return cells

def operators(cells):
    faces=[sorted({f for s in cells for f in it.combinations(s,p+1)}) for p in range(5)]
    idx=[{f:i for i,f in enumerate(fs)} for fs in faces]
    ns=[len(fs) for fs in faces]
    bs=[]
    for p in range(1,5):
        rr=[]; cc=[]; vv=[]
        for j,f in enumerate(faces[p]):
            for k in range(p+1):
                rr.append(idx[p-1][f[:k]+f[k+1:]]); cc.append(j); vv.append((-1)**k)
        bs.append(coo_matrix((vv,(rr,cc)),shape=(ns[p-1],ns[p]),dtype=float).tocsc())
    for p in range(3):
        z=bs[p]@bs[p+1]; z.eliminate_zeros(); assert z.nnz==0
    assert np.all(np.asarray(abs(bs[3]).sum(axis=1)).ravel()==2)
    # Orientability check by propagating consistent orientation signs across shared tetrahedra.
    B=bs[3].tocsr(); orient={0:1}; stack=[0]; BT=bs[3].T.tocsr()
    while stack:
        j=stack.pop()
        for i in BT.indices[BT.indptr[j]:BT.indptr[j+1]]:
            js=B.indices[B.indptr[i]:B.indptr[i+1]]; vs=B.data[B.indptr[i]:B.indptr[i+1]]
            j0,j1=js; k=j1 if j0==j else j0
            sign=-orient[j]*int(vs[0]*vs[1]);
            if k in orient: assert orient[k]==sign
            else: orient[k]=sign;stack.append(k)
    assert len(orient)==ns[4]
    laps=[]
    for p in range(5):
        L=coo_matrix((ns[p],ns[p])).tocsc()
        if p>0: L=L+bs[p-1].T@bs[p-1]
        if p<4: L=L+bs[p]@bs[p].T
        laps.append(L.tocsc())
    blocks=[[None]*5 for _ in range(5)]
    for p in range(5): blocks[p][p]=coo_matrix((ns[p],ns[p])).tocsc()
    for p,b in enumerate(bs): blocks[p][p+1]=b;blocks[p+1][p]=-b.T
    D=bmat(blocks,format='csc'); z=D+D.T;z.eliminate_zeros();assert z.nnz==0
    adj=abs(bs[3]).T@abs(bs[3])-5*eye(ns[4]);adj.eliminate_zeros();assert np.all(adj.sum(axis=1).A1==5)
    ds=shortest_path(adj,directed=False,unweighted=True);assert np.isfinite(ds).all()
    return ns,laps,D,float(ds.sum()/(ns[4]*(ns[4]-1))),faces

def logdet(A):
    f=splu(A.tocsc()); return float(np.log(np.abs(f.U.diagonal())).sum())

def evaluate(cells,masses,check_betti=False):
    ns,L,D,dist,faces=operators(cells); chi=sum((-1)**p*n for p,n in enumerate(ns)); rows=[]
    if check_betti:
        betti=[int(np.sum(np.linalg.eigvalsh(x.toarray())<1e-8)) for x in L]
    else: betti=None
    for m in masses:
        logs=[logdet(L[p]+m*m*eye(ns[p],format='csc')) for p in (0,2,4)]
        ferm=logdet(D+m*eye(sum(ns),format='csc'))
        balanced=ferm-sum(logs); expected=-chi*math.log(m)
        assert abs(balanced-expected)<1e-8
        # One complex KD = 4 Dirac on flat 4D; 16 real vertex scalars match
        # continuum flat degree count, NOT necessarily finite-mesh spectrum.
        rows.append(dict(m=m,log_ferm=ferm,log_even_bos=sum(logs),log_vertex_bos=8*logs[0],log_exact=balanced,log_scalar_only=ferm-8*logs[0],resid=balanced-expected))
    return dict(f_vector=ns,chi=chi,dist=dist,betti=betti,weights=rows)

def main():
    rng=np.random.default_rng(20261124); masses=[.01*(math.sqrt(234)-10),.01*(math.sqrt(234)+10)]; rows=[]
    print('Arithmetic lattice masses:',masses,'product',math.prod(masses),'expected',134*.01**2)
    print('Geometry: S^3 x S^1, sampled slab orderings; periodic time is Euclidean trace.')
    print('Measure: uniform independent slab permutations, not full CDT symmetry-factor measure.')
    print('Incidence Hodge inner products unweighted; no Lorentzian spinor reconstruction.')
    for k,nt,reps in [(0,4,16),(1,4,16),(2,6,16)]:
        tets,nv=sphere3(k); group=[]
        for i in range(reps):
            cells=foliated(tets,nv,nt,[rng.permutation(nv) for _ in range(nt)])
            r=evaluate(cells,masses,check_betti=(k==0 and i==0)); r.update(k=k,nt=nt,rep=i)
            assert r['chi']==0
            if r['betti'] is not None: assert r['betti']==[1,1,0,1,1]
            counts=[0]*5
            for s in cells:
                tset={v//nv for v in s}; t=next(t for t in tset if (t+1)%nt in tset)
                counts[sum(v//nv==t for v in s)]+=1
            assert counts[1:]==[len(tets)*nt]*4
            r['N41']=counts[1]+counts[4];r['N32']=counts[2]+counts[3]
            group.append(r);rows.append(r)
        assert len({tuple(r['f_vector']) for r in group})==1
        d=np.array([r['dist'] for r in group]); logs=np.array([sum(w['log_scalar_only'] for w in r['weights']) for r in group]); p=np.exp(logs-logsumexp(logs)); residual=max(abs(w['resid']) for r in group for w in r['weights'])
        print('N4',group[0]['f_vector'][4], 'f-vector',group[0]['f_vector'],'N41,N32',group[0]['N41'],group[0]['N32'],'reps',reps)
        print('  distance min,mean,max',d.min(),d.mean(),d.max(),'exact pairing residual',residual)
        print('  scalar-only match logweight range (max-min)',np.ptp(logs),'ESS',1/(p@p),'weighted distance',p@d)
        print('  betti first if computed',group[0]['betti'],flush=True)
    # Non-CDT topological control: S4 as boundary of a 5-simplex.
    s4=evaluate(list(it.combinations(range(6),5)),masses,True)
    assert s4['chi']==2 and s4['betti']==[1,0,0,0,1]
    print('S4 topology control f-vector',s4['f_vector'],'Betti',s4['betti'],'chi',s4['chi'])
    print('  combined log exact weight',sum(w['log_exact'] for w in s4['weights']),'expected',-2*math.log(math.prod(masses)))
    print('All implemented assertions passed. No phase transition or continuum limit inferred.')
    (OUT/'runyan_causal_matter_v04_data.json').write_text(json.dumps({'masses':masses,'samples':rows,'s4_control':s4},indent=2))
if __name__=='__main__':main()
