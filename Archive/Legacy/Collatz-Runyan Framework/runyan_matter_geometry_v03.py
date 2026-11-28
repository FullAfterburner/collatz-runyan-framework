"""Restricted fixed-volume ordered refinement ensemble on periodic T4 dual graphs.
Scalar graph determinant proxy; not a covariant matter or quantum gravity simulation.
"""
import numpy as np
from itertools import permutations,product
from scipy.sparse import csr_matrix,eye
from scipy.sparse.linalg import splu
from scipy.sparse.csgraph import shortest_path
from scipy.special import gammaln,logsumexp
from pathlib import Path
import json
P=list(permutations(range(4))); PI={p:i for i,p in enumerate(P)}
def seed(L):
    cells=list(product(range(L),repeat=4)); idx={c:i for i,c in enumerate(cells)}; adj=np.empty((24*L**4,5),int)
    for c in cells:
        for p in P:
            i=idx[c]*24+PI[p]
            for j in range(1,4):
                q=list(p); q[j-1],q[j]=q[j],q[j-1]; adj[i,j]=idx[c]*24+PI[tuple(q)]
            d=list(c); d[p[0]]=(d[p[0]]+1)%L; adj[i,0]=idx[tuple(d)]*24+PI[p[1:]+p[:1]]
            d=list(c); d[p[-1]]=(d[p[-1]]-1)%L; adj[i,4]=idx[tuple(d)]*24+PI[p[-1:]+p[:-1]]
    return adj
def forest(k,r,rng):
    w=np.r_[np.ones(k,int),np.zeros(4*k+r,int)]; rng.shuffle(w); S=np.r_[0,np.cumsum(5*w-1)]
    p=np.r_[np.inf,np.minimum.accumulate(S[:-2])]; s=np.r_[np.minimum.accumulate(S[-2:0:-1])[::-1],np.inf]
    valid=np.flatnonzero((S[:-1]<p)&(s>S[:-1]-r)); assert len(valid)==r
    w=np.roll(w,-rng.choice(valid)); assert min(r+np.cumsum(5*w-1)[:-1])>0
    return w
def graph(base,w):
    r=len(base); k=int(w.sum()); nbr=np.full((r+5*k,5),-1,int); nbr[:r]=base; stack=list(range(r-1,-1,-1)); leaves=[]; nxt=r
    for b in w:
        x=stack.pop()
        if not b: leaves.append(x); continue
        ch=np.arange(nxt,nxt+5); nxt+=5; old=nbr[x].copy()
        for i,c in enumerate(ch):
            nbr[c]=ch; nbr[c,i]=old[i]; port=np.flatnonzero(nbr[old[i]]==x); assert len(port)==1; nbr[old[i],port[0]]=c
        stack.extend(ch[::-1])
    assert not stack
    ix=np.full(len(nbr),-1); ix[leaves]=np.arange(len(leaves)); adj=ix[nbr[leaves]]; N=len(leaves)
    assert N==r+4*k and adj.min()>=0
    A=csr_matrix((np.ones(5*N),(np.repeat(np.arange(N),5),adj.ravel())),shape=(N,N))
    assert (A!=A.T).nnz==0 and A.diagonal().sum()==0 and np.all(A.sum(1).A1==5)
    return A
def ld(A,m):
    L=(1+m*m)*eye(A.shape[0],format='csc')-A.tocsc()/5
    U=splu(L,permc_spec='MMD_AT_PLUS_A',diag_pivot_thresh=0).U.diagonal(); assert np.all(U>0)
    return float(np.log(U).sum())
def entropy(k,r):
    return float(np.log(r/(5*k+r))+gammaln(5*k+r+1)-gammaln(k+1)-gammaln(4*k+r+1))
def run():
    rng=np.random.default_rng(20261124); rows=[]
    for N in [384,1944,6144]:
        for L in [l for l in (1,2,3,4) if 24*l**4<=N]:
            base=seed(L); r=len(base); k=(N-r)//4; assert r+4*k==N
            reps=1 if k==0 else (32 if N<6144 else 16)
            for i in range(reps):
                A=graph(base,forest(k,r,rng)); dist=shortest_path(A,directed=False,indices=rng.choice(N,24,replace=False),unweighted=True); assert np.isfinite(dist).all()
                logs=[ld(A,m) for m in [.1,.5,.01*(np.sqrt(234)-10),.01*(np.sqrt(234)+10)]]
                if N==384 and i==0: assert abs(logs[0]-np.linalg.slogdet(1.01*np.eye(N)-A.toarray()/5)[1])<1e-8
                rows.append(dict(N=N,L=L,k=k,N2=50*L**4+10*k,entropy=entropy(k,r),dist=float(dist.sum()/(24*(N-1))),logs=logs))
            a=[v for v in rows if v['N']==N and v['L']==L]
            print('N,L,k,reps',N,L,k,reps,'mean dist',np.mean([v['dist'] for v in a]),'logdet/N',np.mean([v['logs'] for v in a],axis=0)/N,'entropy/N',a[0]['entropy']/N,flush=True)
    (Path(__file__).resolve().parent/'runyan_matter_geometry_v03_data.json').write_text(json.dumps(rows,indent=2)); return rows
def analyze(rows):
    print('Scalar determinant reweighting, uniform ordered forests, equal seed prior.')
    for N in sorted({r['N'] for r in rows}):
        ls=sorted({r['L'] for r in rows if r['N']==N}); print('N=',N)
        for mi,m in enumerate([.1,.5]):
            for ns in [0,1,2,4,8]:
                sectors=[]
                for L in ls:
                    a=[v for v in rows if v['N']==N and v['L']==L]; w=-ns/2*np.array([v['logs'][mi] for v in a]); norm=logsumexp(w); p=np.exp(w-norm)
                    sectors.append((L,a[0]['N2'],a[0]['entropy']+norm-np.log(len(a)),1/np.sum(p*p),float(p@np.array([v['dist'] for v in a])),len(a)))
                lo,hi=sectors[0],sectors[-1]; cross=(hi[2]-lo[2])/(lo[1]-hi[1]); winner=max(sectors,key=lambda x:x[2])[0]
                print('m,ns',m,ns,'winner kappa2=0',winner,'pair crossing',round(cross,6),'ESS',[(s[0],round(s[3],1),s[5]) for s in sectors],'weighted distances',[(s[0],round(s[4],4)) for s in sectors],flush=True)
                if m==.1 and ns in [0,2,8]:
                    for kap in [-10,-5,-2,0,1,3]:
                        l=np.array([s[2]+kap*s[1] for s in sectors]); print(' kappa2',kap,'dominant L',ls[int(np.argmax(l))], 'logZ/N',np.round((l-l.max())/N,5).tolist())
def arithmetic_and_rg(rows):
    print("\nArithmetic two-scalar mass pair: illustrative M*a=0.01, not fixed by arithmetic")
    print("masses", .01*(np.sqrt(234)-10), .01*(np.sqrt(234)+10))
    for N in sorted({r['N'] for r in rows}):
        ls=sorted({r['L'] for r in rows if r['N']==N}); S=[]
        for L in ls:
            a=[v for v in rows if v['N']==N and v['L']==L]
            w=-.5*np.array([sum(v['logs'][2:]) for v in a]); norm=logsumexp(w); p=np.exp(w-norm)
            S.append((L,a[0]['N2'],a[0]['entropy']+norm-np.log(len(a)),1/np.sum(p*p),float(p@np.array([v['dist'] for v in a]))))
        lo,hi=S[0],S[-1]
        print('N',N,'winner at zero',max(S,key=lambda x:x[2])[0],'pair crossing',(hi[2]-lo[2])/(lo[1]-hi[1]),'ESS and distance by seed',[(x[0],x[3],x[4]) for x in S])
    print('\nExact scalar Gaussian decimation of five child vertices (K5):')
    for m in [0,.1,.5]:
        b=1.2+m*m; c=.2+m*m
        C=b*np.eye(5)-np.ones((5,5))/5
        correction=-np.linalg.inv(C)/25
        off=-1/(125*b*c)
        logdet=4*np.log(b)+np.log(c)
        assert np.max(abs(correction[~np.eye(5,dtype=bool)]-off))<1e-14
        assert abs(np.linalg.slogdet(C)[1]-logdet)<1e-14
        print('mass',m,'induced off-diagonal stiffness',off,'diagonal correction',correction[0,0],'logdet child block',logdet)
if __name__=='__main__':
    rows=run(); analyze(rows); arithmetic_and_rg(rows)
