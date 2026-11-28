"""One-loop spin-2 dispersive benchmark, not full quantum gravity.
Units E_UV=1. Continuum subtracted free-field form factor matched to v0.8
local proper-time coefficients; NOT a finite-cutoff nonlocal determinant.
Requires numpy, scipy, sympy. No graviton loops or independent higher operators.
"""
import numpy as np
import sympy as sp
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import exp1
from math import sqrt, pi, exp
v=sp.symbols('v', real=True)
assert sp.simplify(v**5/30+v**3*(5-2*v**2)/60-v**3/12)==0
# density convention: Im F(-s-i0)=-pi*rho(s)
C=1/(384*pi*pi)
def params(q):
    m=q*np.array([sqrt(234)-10,sqrt(234)+10]); x=m*m
    P2=sum(np.exp(-x)-x*exp1(x))/(48*pi*pi)
    b0=-C*sum(exp1(x))
    return m,P2,b0

def H(z,m):
    return quad(lambda v: 2*z*v**4/(4*m*m+z*(1-v*v)),0,1,epsabs=1e-12,epsrel=1e-12)[0]
def Hprime(z,m):
    return quad(lambda v: 8*m*m*v**4/(4*m*m+z*(1-v*v))**2,0,1,epsabs=1e-12)[0]
def Hclosed(z,m):
    a=sqrt(1+4*m*m/z)
    return 2*(a**3*np.arctanh(1/a)-a*a-1/3)
def rho(s,m):
    return C*sum(max(0,1-4*x*x/s)**1.5 for x in m) if s>0 else 0

def benchmark(q):
    m,P2,b0=params(q); A=P2/4
    F=lambda z:b0+C*sum(H(z,x) for x in m)
    B=lambda z:A+z*F(z)
    dB=lambda z:F(z)+z*C*sum(Hprime(z,x) for x in m)
    zmin=brentq(dB,0,4)
    zlocal=-A/b0
    roots=[]
    if B(zmin)<0:
        roots=[brentq(B,0,zmin),brentq(B,zmin,16)]
    # Strict positivity of second derivative follows from positive dispersion measure.
    slope=C*sum(1/(10*x*x) for x in m)
    for x in m:
        assert abs(H(0.3,x)-Hclosed(0.3,x))<1e-9
    assert abs((F(1e-8)-b0)/1e-8/slope-1)<1e-4
    assert B(zlocal)>0
    # Bound |z F(z)| throughout the disk |z|< first pair threshold squared.
    zth=4*m[0]**2
    disk_bound=zth*(abs(b0)+C*sum(-H(-zth,x) for x in m))/A
    print(f'first-cut disk bound |zF|/A <= {disk_bound:.12g}; B(1)/A={B(1)/A:.12g}; Bprime(1)/A={dB(1)/A:.12g}')
    if q==.01:
        assert disk_bound<1 and B(1)>0 and dB(1)<0
    print(f'q={q:g}, masses={m}, thresholds={2*m}')
    print(f'P2={P2:.12g}, b0={b0:.12g}, Fprime0={slope:.12g}')
    print(f'local pole p={sqrt(zlocal):.12g}, Bfull/A there={B(zlocal)/A:.12g}')
    print(f'min p={sqrt(zmin):.12g}, min B/A={B(zmin)/A:.12g}, real Euclidean roots p={[sqrt(z) for z in roots]}')
    print('p, local B/A, dispersive B/A, F(p^2)')
    for p in [0,.05,.1,.2,.3,.4,.5,.6,.686779641011,.8,1,1.5,2]:
        z=p*p;print(f'{p:.9g} {1+z*b0/A:.12g} {B(z)/A:.12g} {F(z):.12g}')
    print('normalized spectral weight rho/C vs timelike energy')
    for e in [.05,.1,.11,.15,.2,.3,.5,.51,.6,.8,1,2,10]:
        print(f'{e:g} {rho(e*e,m)/C:.12g}')
    return B(zmin)/A
if __name__=='__main__':
    print('Spin-two spectral pairing: 4 scalars + 1 Dirac = beta^3/12 exactly.')
    for q in [.001,.01,.03,.1]: benchmark(q)
    print('All assertions passed. No complex-plane pole search; no UV completion claimed.')
