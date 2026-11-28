"""Finite-lattice U(1) overlap index benchmark on a prescribed flat periodic T^4.
No chiral gauge path integral or dynamical gravity. Requires numpy and scipy.
"""
from itertools import product
from math import pi
import numpy as np
from scipy.linalg import eigh
from runyan_controlled_continuum_v02 import gamma,g5,I4

def test(N,n12,n34):
    coords=np.array(list(product(range(N),repeat=4))); V=len(coords); ids=np.arange(V); shape=(N,)*4
    link=np.ones((V,4),complex)
    for u,v,n in [(0,1,n12),(2,3,n34)]:
        link[:,u]=np.exp(-2j*pi*n*coords[:,v]/N**2)
        link[:,v]=np.where(coords[:,v]==N-1,np.exp(2j*pi*n*coords[:,u]/N),1.)
    plus=[]; minus=[]
    for mu in range(4):
        p=coords.copy();p[:,mu]=(p[:,mu]+1)%N; plus.append(np.ravel_multi_index(p.T,shape))
        m=coords.copy();m[:,mu]=(m[:,mu]-1)%N; minus.append(np.ravel_multi_index(m.T,shape))
    for mu,nu,n in [(0,1,n12),(2,3,n34)]:
        plaq=link[:,mu]*link[plus[mu],nu]*link[plus[nu],mu].conj()*link[:,nu].conj()
        assert np.max(abs(plaq-np.exp(2j*pi*n/N**2)))<1e-12
    A=np.kron(np.eye(V),3*I4).astype(complex)
    for mu in range(4):
        for i in ids:
            j=plus[mu][i]; k=minus[mu][i]
            A[4*i:4*i+4,4*j:4*j+4]-=.5*link[i,mu]*(I4-gamma[mu])
            A[4*i:4*i+4,4*k:4*k+4]-=.5*link[k,mu].conj()*(I4+gamma[mu])
    G=np.kron(np.eye(V),g5); H=G@A
    assert np.max(abs(H-H.conj().T))<1e-12
    eig,vec=eigh(H,check_finite=False); gap=min(abs(eig)); assert gap>1e-6
    sign=np.sign(eig); index=int(-sign.sum()/2)
    Q=(vec*sign)@vec.conj().T; D=np.eye(4*V)+G@Q
    gw=np.max(abs(G@D+D@G-D@G@D)); assert gw<1e-11
    # H_ov = gamma5 D is Hermitian. Its zero-mode subspace admits a chirality basis.
    eig2,vec2=eigh(G@D,check_finite=False); z=vec2[:,abs(eig2)<1e-8]
    chir=np.linalg.eigvalsh(z.conj().T@G@z); nzp=int(sum(chir>.9)); nzm=int(sum(chir<-.9))
    assert nzp-nzm==index and abs(index)==abs(n12*n34)
    print(f'N={N} flux=({n12},{n34}) dim={4*V} Wilson gap={gap:.9f} index={index} zero modes (+,-)=({nzp},{nzm}) GW max entry residual={gw:.3e}',flush=True)
    return index
if __name__=='__main__':
    print('Gamma5 convention index = n_plus - n_minus; overall sign orientation-dependent.')
    idx=test(4,1,1); assert test(4,1,-1)==-idx; assert test(4,1,0)==0
    assert test(5,1,1)==idx
    print('All finite-lattice checks passed. Index magnitude equals |n12*n34| for tested sectors. No full chiral gauge theory inferred.')
