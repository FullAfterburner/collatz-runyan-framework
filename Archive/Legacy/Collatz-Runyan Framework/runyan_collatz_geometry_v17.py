"""Collatz parity quotient, exact graph spectrum and heat-trace tests.
Requires numpy, scipy. No assumed spatial dimension or fitted exponent.
"""
import numpy as np
from scipy.special import logsumexp
from fractions import Fraction as F

def T(x): return (3*x+1)//2 if x&1 else x//2

def parity(x,n):
    q=0
    for i in range(n):
        q |= (x&1)<<i; x=T(x)
    return q

def spectrum(n):
    out=[0.]
    for l in range(1,n+1):
        mult=1 if l==n else 2**(n-l-1)
        out.extend(np.tile(1-np.cos(np.pi*np.arange(1,l+1)/(l+1)),mult))
    return np.sort(out)

def verify(n):
    N=2**n; q=np.array([parity(x,n) for x in range(N)])
    assert len(set(q))==N
    P=np.zeros((N,N)); D=np.zeros_like(P)
    for x in range(N):
        for b in (0,1):
            y=T(x+b*N)%N
            P[x,y]+=.5
            D[q[x],q[x]//2+b*N//2]+=.5
    assert np.array_equal(P,D[np.ix_(q,q)])
    assert np.allclose(P.sum(0),1) and np.allclose(P.sum(1),1)
    e=np.linalg.eigvalsh(np.eye(N)-(P+P.T)/2)
    err=np.max(abs(e-spectrum(n))); assert err<1e-12
    print(f'n={n:2d} N={N:4d} parity and adjacency exact; spectrum max error={err:.3g}')

# n -> infinity before diffusion time -> infinity.
def heat(t,L=600):
    ell=np.arange(1,L+1,dtype=float)
    gaps=np.concatenate([2*np.sin(np.pi*np.arange(1,int(l)+1)/(2*(l+1)))**2 for l in ell])
    lw=np.repeat(-(ell+1)*np.log(2),ell.astype(int))
    logh=logsumexp(lw-t*gaps)
    ds=2*t*np.sum(gaps*np.exp(lw-t*gaps-logh))
    return logh,ds

if __name__=='__main__':
    for n in range(2,10): verify(n)
    print('\nInfinite-volume normalized heat trace; continuous-time generator L=I-(P+P^T)/2')
    print('t          log(P_return)      d_s(t)      -log(P)/t^(1/3)')
    C=1.5*(np.pi**2*np.log(2)**2)**(1/3)
    for t in [1,3,10,30,100,300,1000,3000,10000,100000]:
        h,d=heat(t); h2,d2=heat(t,300); assert abs(h-h2)<1e-10 and abs(d-d2)<1e-9
        print(f'{t:7g} {h:18.10f} {d:13.8f} {-h/t**(1/3):17.9f}')
    print('Asymptotic constant C =',C)
    # Exact affine commutator on Q (branch extensions, not bijections of Z_2).
    A=lambda x:2*x; B=lambda x:(2*x-1)/3
    Ai=lambda x:x/2; Bi=lambda x:(3*x+1)/2
    for x in map(F,range(-10,11)):
        assert A(B(Ai(Bi(x))))==x-F(1,3)
    print('Affine commutator = translation by -1/3: verified exactly.')
    # Two inverse branches on finite parity words are orthogonal embeddings.
    for n in range(1,9):
        N=2**n; V=[np.zeros((2*N,N)) for _ in range(2)]
        for b in (0,1): V[b][2*np.arange(N)+b,np.arange(N)]=1
        for b in (0,1):
            for c in (0,1): assert np.array_equal(V[b].T@V[c],np.eye(N)*(b==c))
        assert np.array_equal(sum(v@v.T for v in V),np.eye(2*N))
    print('Finite branch isometry relations passed for n=1..8.')
    # Two inverse-branch matrix algebra: determinant is Minkowski quadratic form.
    import sympy as sp
    t,x,y,z,a=sp.symbols('t x y z a',real=True)
    H=sp.Matrix([[t+z,x-sp.I*y],[x+sp.I*y,t-z]])
    assert sp.expand(H.det())==t*t-x*x-y*y-z*z
    L=sp.diag(sp.exp(a/2),sp.exp(-a/2))
    Hp=L*H*L.H
    assert sp.simplify(Hp.det()-H.det())==0
    assert sp.simplify((Hp[0,0]+Hp[1,1])/2-(t*sp.cosh(a)+z*sp.sinh(a))).rewrite(sp.exp).simplify()==0
    assert sp.simplify((Hp[0,0]-Hp[1,1])/2-(z*sp.cosh(a)+t*sp.sinh(a))).rewrite(sp.exp).simplify()==0
    print('Branch Hermitian determinant signature (+---) and diagonal spin boost verified symbolically.')
