"""Checks for the proposed 4D Collatz–Runyan EFT, not a UV completion.
Requires NumPy, SciPy, SymPy and runyan_modular_yukawa.py.
No experimental particle data used. Test coefficients are illustrative only.
"""
from fractions import Fraction as F
from math import prod, sqrt
import numpy as np
import sympy as sp
from runyan_modular_yukawa import forms, weight4, S, T

# All fermions are left-handed Weyl fields. X is the composite modular phase charge.
fields=[]
for gen in range(3):
    x=2 if gen==2 else 0
    fields += [('Q',3,2,F(1,6),x,1),('u^c',3,1,F(-2,3),-x,-1),
               ('d^c',3,1,F(1,3),-x,-1),('L',1,2,F(-1,2),-2,0),
               ('e^c',1,1,F(1),2,0),('N^c',1,1,F(0),2,0)]
a={}
for i, qname in [(3,'Y'),(4,'X')]:
    a['grav^2 '+qname]=sum(c*w*f[i] for f in fields for _,c,w,*_r in [f])
    a[qname+'^3']=sum(f[1]*f[2]*f[i]**3 for f in fields)
    a['SU3^2 '+qname]=sum(f[2]*f[i]*F(1,2) for f in fields if f[1]==3)
    a['SU2^2 '+qname]=sum(f[1]*f[i]*F(1,2) for f in fields if f[2]==2)
a['SU3^3']=sum(f[2]*f[5] for f in fields)
a['Y^2 X']=sum(c*w*y*y*x for _,c,w,y,x,_ in fields)
a['Y X^2']=sum(c*w*y*x*x for _,c,w,y,x,_ in fields)
assert all(v==0 for v in a.values())
nd=sum(c for _,c,w,*_ in fields if w==2); assert nd%2==0
print('Continuous local anomaly coefficients (including formal composite U(1)_X):',a)
print('SU2 Weyl doublets:',nd,'even. Global modular anomalies not tested.')

# Modular covariance of canonically normalized weight-four tensors,
# sterile Majorana tensor, Weinberg operator, and charged-lepton Yukawa example.
def tensors(z):
    return [z.imag**2*m for m in weight4(forms(z))]
def mat(z):
    p=tensors(z); return p[0]+(.3+.2j)*p[1]-.4*p[2]
def charged(z):
    p=tensors(z); return np.eye(3)+p[0].conj().T@p[0]+.2*p[1].conj().T@p[1]
def err(a,b): return np.max(np.abs(a-b))/max(1,np.max(np.abs(b)))
worst=np.zeros(4)
for z in [.23+1.17j,-.42+.96j,1j,.12+2.4j, .4+1.1j]:
    for zz,J,rho in [(-1/z,z,S),(z+1,1,T)]:
        phase=J/abs(J); L=phase**(-2)*rho; N=phase**2*rho.conj()
        worst=np.maximum(worst,[err(L.T@mat(zz)@L,mat(z)),
            err(N.T@mat(zz).conj()@N,mat(z).conj()),
            err(N.T@charged(zz)@L,charged(z)),err(N.T@L,np.eye(3))])
assert max(worst)<1e-10
print('Canonical modular covariance max errors: Weinberg, sterile Majorana, charged Yukawa, Dirac identity:',worst)

# Composite connection and Poincare metric: check S explicitly on real differentials.
x,y,dx,dy=sp.symbols('x y dx dy',real=True); R=x*x+y*y
xp=-x/R; yp=y/R
dxp=sp.diff(xp,x)*dx+sp.diff(xp,y)*dy
dyp=sp.diff(yp,x)*dx+sp.diff(yp,y)*dy
assert sp.simplify((dxp**2+dyp**2)/yp**2-(dx**2+dy**2)/y**2)==0
assert sp.simplify(dxp/(2*yp)-dx/(2*y)-(x*dy-y*dx)/R)==0
print('Exact S check: target metric invariant and Q transforms by +d arg(tau). T trivial.')

# Exact rank-one identity and full polynomial trace constraint are inherited from prior work.
a,b,c=sp.symbols('a b c'); vv=sp.Matrix([a,c,b]); P=sp.Matrix([[1,0,0],[0,0,1],[0,1,0]]); P2=sp.Matrix([[0,0,1],[0,1,0],[1,0,0]])
f1,f2,f3=a*a-b*c,c*c-a*b,b*b-a*c
MF=sp.Matrix([[2*f1,-f3,-f2],[-f3,2*f2,-f1],[-f2,-f1,2*f3]])
assert all(sp.rem(sp.expand(z),b*b+2*a*c,b)==0 for z in MF+(a*a+2*b*c)*P+(c*c+2*a*b)*P2-3*vv*vv.T)
print('Exact rank-one texture identity verified modulo Y2^2 + 2Y1Y3.')

# Class-number counts by elementary reduced-form enumeration.
from math import isqrt,gcd
for D in (3,37,137):
    disc=-4*D; fs=[]
    for aa in range(1,isqrt(-disc//3)+1):
        for bb in range(-aa,aa+1):
            if (bb*bb-disc)%(4*aa): continue
            cc=(bb*bb-disc)//(4*aa)
            if cc<aa or gcd(gcd(aa,bb),cc)>1 or ((abs(bb)==aa or aa==cc) and bb<0): continue
            fs.append((aa,bb,cc))
    print('CM D =',D,'h =',len(fs),'forms =',fs)
    assert len(fs)=={3:1,37:2,137:8}[D]

# One-loop vacuum energy scale derivative (constant mass background, MS scheme).
m,mu=sp.symbols('m mu',positive=True); V=m**4*(sp.log(m**2/mu**2)-sp.Rational(3,2))/(64*sp.pi**2)
assert sp.simplify(mu*sp.diff(V,mu)+m**4/(32*sp.pi**2))==0
print('One real bosonic mode: d V1 / d ln mu = -m^4/(32 pi^2). Fermionic sign opposite.')
P0=prod((3,37,137)); print('Conditional covering-torus G4 Ms^2 =',1/(8*P0**1.5),'/ r^6 (not a global compactification).')
print('All assertions passed. No physical masses fitted; no UV, global anomaly, flux completion or vacuum-energy cancellation established.')
