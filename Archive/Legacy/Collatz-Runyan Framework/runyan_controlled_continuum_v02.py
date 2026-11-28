"""Deterministic smooth-mesh and free overlap benchmark; not a quantum gravity simulation.
Requirements numpy scipy.  Unit coordinate T^4, periodic Freudenthal triangulation.
Edge lengths are straight-coordinate segment lengths in a prescribed conformal metric,
not exact geodesic distances.  Transverse translations are summed analytically.
"""
from itertools import permutations, combinations, product
from collections import defaultdict
from pathlib import Path
import numpy as np
from scipy.integrate import quad
from numpy.polynomial.legendre import leggauss
from math import pi, sqrt, factorial

PERMS=list(permutations(range(4)))
PAIRS=list(combinations(range(5),2)); TRIS=list(combinations(range(5),3))
q,w=leggauss(12); q=(q+1)/2; w=w/2

def mesh(N,eps):
    a=1/N; angles=defaultdict(float); areas={}; vol=0.; scalar=0.; min_eig=1e100
    for cell in range(N):
        for p in PERMS:
            v=np.vstack([np.zeros(4,int),np.cumsum(np.eye(4,dtype=int)[list(p)],axis=0)])
            x=a*(cell+v[:,0]); L=np.zeros((5,5))
            for i,j in PAIRS:
                length=a*np.linalg.norm(v[j]-v[i])*np.dot(w,np.exp(eps*np.cos(2*pi*(x[i]+q*(x[j]-x[i])))))
                L[i,j]=L[j,i]=length**2
            G=(L[0,1:,None]+L[0,None,1:]-L[1:,1:])/2
            min_eig=min(min_eig,np.linalg.eigvalsh(G/a**2)[0]); inv=np.linalg.inv(G)
            V=sqrt(np.linalg.det(G))/factorial(4); vol+=V
            psi=np.sin(2*pi*x); d=psi[1:]-psi[0]; scalar+=V*d@inv@d
            J=np.vstack([-np.ones(4),np.eye(4)]); H=J@inv@J.T
            for tri in TRIS:
                i,j,k=tri; r,s=[t for t in range(5) if t not in tri]
                theta=np.arccos(np.clip(-H[r,s]/sqrt(H[r,r]*H[s,s]),-1,1))
                key=((cell+int(v[i,0]))%N,tuple((v[j]-v[i]).tolist()),tuple((v[k]-v[i]).tolist()))
                b=L[i,j]; c=L[i,k]; dot=(b+c-L[j,k])/2; area=.5*sqrt(b*c-dot*dot)
                if key in areas: assert abs(areas[key]-area)<1e-11
                areas[key]=area; angles[key]+=theta
    deficits=np.array([2*pi-angles[k] for k in areas]); curvature=2*N**3*sum(areas[k]*(2*pi-angles[k]) for k in areas)
    return curvature,vol*N**3,scalar*N**3,float(max(abs(deficits))),min_eig

def continuum(eps):
    omega=lambda x:eps*np.cos(2*pi*x)
    R=6*quad(lambda x:np.exp(2*omega(x))*(2*pi*eps*np.sin(2*pi*x))**2,0,1,epsabs=1e-12)[0]
    V=quad(lambda x:np.exp(4*omega(x)),0,1,epsabs=1e-12)[0]
    S=quad(lambda x:np.exp(2*omega(x))*(2*pi*np.cos(2*pi*x))**2,0,1,epsabs=1e-12)[0]
    return np.array([R,V,S])

# Hermitian Euclidean Clifford generators; dimensionless overlap A=aD.
s1=np.array([[0,1],[1,0]],complex); s2=np.array([[0,-1j],[1j,0]],complex); s3=np.diag([1,-1]); I2=np.eye(2); I4=np.eye(4)
gamma=np.array([np.kron(s1,s1),np.kron(s1,s2),np.kron(s1,s3),np.kron(s2,I2)])
g5=gamma[0]@gamma[1]@gamma[2]@gamma[3]
def overlap(k):
    s=np.sin(k); b=np.sum(1-np.cos(k))-1
    return I4+(b*I4+1j*np.einsum('i,ijk->jk',s,gamma))/sqrt(b*b+s@s)

def main():
    print('CONTROLLED CONTINUUM BENCHMARK v0.2')
    for i,j in product(range(4),repeat=2): assert np.allclose(gamma[i]@gamma[j]+gamma[j]@gamma[i],2*I4*(i==j))
    flat=mesh(4,0); print('flat N=4 R,V,scalar,max deficit,min normalized Gram eigenvalue:',flat)
    assert abs(flat[0])<1e-10 and abs(flat[1]-1)<1e-10
    for eps in [.1,.2]:
        ref=continuum(eps); print('eps',eps,'continuum [integrated R,volume,scalar kinetic]',ref)
        old=None
        for N in [4,8,16,32,64]:
            out=mesh(N,eps); err=abs(np.array(out[:3])/ref-1)
            print('N',N,'simplices',24*N**4,'R,V,S',*[f'{x:.12g}' for x in out[:3]],'relative errors',*[f'{x:.8g}' for x in err],'max deficit',f'{out[3]:.8g}','min Gram',f'{out[4]:.8g}',flush=True)
            if old is not None: assert np.all(err<old)
            old=err
        assert max(err)<.01
    rng=np.random.default_rng(20261124); gw=herm=0.
    for k in rng.uniform(-pi,pi,(1000,4)):
        D=overlap(k); gw=max(gw,np.linalg.norm(g5@D+D@g5-D@g5@D,ord=2)); herm=max(herm,np.linalg.norm(D.conj().T-g5@D@g5,ord=2))
    zeros=sum(np.linalg.norm(overlap(np.array(k)))<1e-10 for k in product([0,pi],repeat=4))
    print('overlap GW residual',gw,'gamma5-hermiticity residual',herm,'zero corners',zeros)
    assert gw<1e-12 and herm<1e-12 and zeros==1
    p=np.array([.7,-.3,.4,.5]); p2=p@p
    for a in [.2,.1,.05,.025,.0125]:
        D=overlap(a*p); Dc=D@np.linalg.inv(I4-D/2)/a
        lam=np.trace(Dc.conj().T@Dc).real/4
        print('a',a,'chirally symmetric kernel p^2 relative error',abs(lam/p2-1))
    print('arithmetic mass eigenvalues',np.linalg.eigvalsh([[3,sqrt(185)],[sqrt(185),17]]))
    print('Scope: fixed smooth Euclidean geometry, scalar finite element energy, free overlap fermions on flat vertex lattice. No metric fluctuations, chiral gauge measure, RG fixed point or Lorentzian graviton test.')
if __name__=='__main__':main()
