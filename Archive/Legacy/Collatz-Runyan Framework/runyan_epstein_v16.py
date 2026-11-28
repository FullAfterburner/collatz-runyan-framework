"""Arithmetic circle and torus determinants; 5D free-field radion benchmark.
Run with Python 3, numpy, scipy, sympy. Units M=1; reference radius 1/M.
No supergravity embedding or full quantum vacuum prediction is implied.
"""
import numpy as np
import sympy as sp
from scipy.special import kv, zeta
from scipy.optimize import brentq, minimize_scalar
from scipy.integrate import quad
from math import pi, sqrt, log, exp, tanh

mlo,mhi=sqrt(234)-10,sqrt(234)+10
masses=(mlo,mhi)
print('ARITHMETIC EPSTEIN / CASIMIR BENCHMARK v1.6')
print('m/M =',masses)
# Circle inverse-mass sums, tail-corrected direct sum.
r=.1
n=np.arange(-100000,100001,dtype=float)
for m in masses:
    for a in (0.,.5):
        exact=pi*r/m*(1/tanh(pi*r*m) if a==0 else tanh(pi*r*m))
        N=100000
        numerical=np.sum(1/(m*m+(n+a)**2/r**2))+r*r*(zeta(2,N+1+a)+zeta(2,N+1-a))
        assert abs(exact-numerical)<1e-12
        print('circle Z(1), m,a:',m,a,'exact',format(exact,'.12g'),'error',abs(exact-numerical))
# Exact small-radius coefficients using Bernoulli/zeta moments.
M,R=sp.symbols('M R', positive=True)
S1=sp.Rational(167,4489)
print('circle sum expansion:',S1/M**2+2*sp.pi**2*R**2/3-668*sp.pi**4*R**4*M**2/45)
# Rectangular massless determinant / physical area (zero mode removed).
# log(det'/A)=log y - pi*y/3 +4 sum log(1-exp(-2*pi*y*n)).
# Relative massive log determinant periodic/antiperiodic along long circle.
print('\nTORUS D, log(detprime/A), detprime/A, massive log determinant ratio P/AP')
for D in (3,37,137):
    y=sqrt(D)
    k=np.arange(1,101,dtype=float)
    ld=log(y)-pi*y/3+4*np.log1p(-np.exp(-2*pi*y*k)).sum()
    derivative=1/y-pi/3+8*pi*np.sum(k/np.expm1(np.minimum(2*pi*y*k,700)))
    assert derivative<0
    r=.025
    vals=[]
    for m in masses:
        n=np.arange(-100,101,dtype=float)
        e=np.exp(-2*pi*y*np.sqrt((r*m)**2+n*n))
        product=2*np.sum(np.log1p(-e)-np.log1p(e))
        w1,w2=np.meshgrid(np.arange(-180,181),np.arange(-61,62,2)) # odd w2 only
        ell=np.sqrt(w1*w1+D*w2*w2)
        winding=-4*r*y*m*np.sum(kv(1,2*pi*r*m*ell)/ell)
        assert abs(winding-product)<1e-10*max(abs(product),1e-30)
        vals.append(product)
    print(D,format(ld,'.12g'),format(exp(ld),'.12g'),*[format(x,'.12g') for x in vals])

# Jordan V per real scalar = -sum cos(2pi n a) exp(-x)(3+3x+x^2)/(64 pi^6 r^4 n^5).
# Einstein V adds r^-2. D(m,r) = magnitude for 4 P bosons + 4 AP fermions.
# Return value and first two derivatives with respect to log r.
odd=np.arange(1,2002,2,dtype=float)
def D(m,r):
    x=2*pi*m*r*odd
    e=np.exp(-x)/odd**5
    f=(3+3*x+x*x)*e
    df=-x*x*(1+x)*e
    ddf=(x**4-2*x**3-2*x*x)*e
    return np.array([f.sum(),(df-6*f).sum(),(ddf-12*df+36*f).sum()])/(8*pi**6*r**6)
# independent proper time check per real scalar, difference, at one point.
r=.03;m=mlo
# t=R^2*u; integrate via log u
# D_E = 4*r^-2*(r sqrt(pi)/(32 pi^2))* sum w [1-(-1)^w] integral t^-7/2 exp(-m^2*t-pi^2*r^2*w^2/t)
def integ(v):
    u=exp(v)
    return u**(-2.5)*exp(-(m*r)**2*u)*np.exp(-pi*pi*odd[:100]**2/u).sum()
proper=4*4/(32*pi**1.5*r**6)*quad(integ,-20,20,epsabs=1e-13,epsrel=1e-11)[0]
assert abs(proper/D(m,r)[0]-1)<1e-9
print('\nProper-time vs elementary Casimir relative error',abs(proper/D(m,r)[0]-1))
# Five physical 5D graviton polarizations, all periodic. Gravity Casimir only.
Cg=15*zeta(5,1)/(64*pi**6)
def grav(r):return -Cg/r**6*np.array([1.,-6.,36.])
# Minimal opposite twist: -Dlight + Dheavy always negative and increasing.
for r in np.geomspace(.001,1,100):
    q=-D(mlo,r)+D(mhi,r)
    assert q[0]<0 and q[1]>0
print('Equal-copy opposite twist: sampled negative/increasing on [.001,1]')
# Modified model: two copies heavy positive, one light negative, periodic graviton.
def U(r):return -D(mlo,r)+2*D(mhi,r)+grav(r)
# Small-r coefficient in Einstein potential.
Csmall=3*zeta(5,1)/(64*pi**6)*(4*31/16-5)
assert Csmall>0
print('Small-r coefficient Csmall =',Csmall,'graviton coefficient',Cg)
rmin=brentq(lambda r:U(r)[1],.001,.1,xtol=1e-15)
print('AdS radial minimum r, U, dU/dlogr, d2U/dlogr2:',rmin,*U(rmin))
assert U(rmin)[0]<0 and U(rmin)[2]>0
# A/r bulk cosmological constant uplift; stationary Minkowski at maximum -r*U.
rmink=brentq(lambda r:U(r)[0]+U(r)[1],.001,.1,xtol=1e-15)
Acrit=-rmink*U(rmink)[0]
def total(r,A):return U(r)+A/r*np.array([1.,-1.,1.])
assert Acrit>0 and abs(total(rmink,Acrit)[0])<1e-9*abs(U(rmink)[0]) and total(rmink,Acrit)[2]>0
print('Minkowski r, Acrit, U, dU/dlogr, d2U/dlogr2:',rmink,Acrit,*total(rmink,Acrit))
for factor in (.99,1.,1.01):
    A=Acrit*factor
    rstar=brentq(lambda r:total(r,A)[1],.001,.012,xtol=1e-15)
    print('uplift factor, r, U, curvature:',factor,rstar,total(rstar,A)[0],total(rstar,A)[2])
# finite grid is not a uniqueness proof
rr=np.geomspace(.0005,10,4000)
obj=np.array([-r*U(r)[0] for r in rr]);print('sampled max -rU at',rr[obj.argmax()],obj.max())
print('\nPROFILE: r, original opposite twist (no gravity), modified with gravity, uplifted')
for r in (.008,.01,.012,.015,.018,.02,.025,.03,.04,.05,.075,.1,.2):
    print(f'{r:.3f} {(-D(mlo,r)+D(mhi,r))[0]:.9g} {U(r)[0]:.9g} {total(r,Acrit)[0]:.9g}')
print('All implemented assertions passed.')
