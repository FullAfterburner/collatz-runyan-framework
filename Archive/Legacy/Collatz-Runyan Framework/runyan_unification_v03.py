"""Audit of four unification targets; independent toy tests, not a UV completion.
Python 3 standard library only. All physical scales remain conditional.
"""
from math import pi, sqrt, acos, prod, fsum
from fractions import Fraction
from itertools import product

D=(3,37,137); P=prod(D); gs=1/sqrt(P)
# One real matched boson/fermion degree of freedom, one compact circle.
# Poisson resummation: omit common zero-winding local term.
zeta5=fsum(1/k**5 for k in range(1,10001))
casimir=-93*zeta5/(1024*pi**6)
odd=fsum(2/k**5 for k in range(1,10001,2))
assert abs(casimir+3*odd/(64*pi**6))<1e-16
print('ONE-LOOP CASIMIR: V R^4 =',casimir,'(one real matched pair; half-shift fermion)')
# Full six-circle field theory toy: half-shift on largest circle (index 5).
# Sum over winding cube: sign exact; finite sums only, no tail certificate.
metric=(1,3,1,37,1,137)
coef=-3*sqrt(P)/(4*pi**9)
for N in (1,2,3,4):
    total=fsum(2/(sum(d*k*k for d,k in zip(metric,w))**5)
               for w in product(range(-N,N+1),repeat=6) if w[-1]%2)
    print('T6 winding cutoff',N,'V R^4 partial =',coef*total)
# Gravity: string frame radii, constant dilaton, covering torus.
C=1/(8*P**1.5)
print('g_s =',gs,'G4 M_s^2 =',C,'/ r^6')
print('G4 m_KK^2 =',C/137,'/ r^8')
print('At r=1: Ms/MPlanck =',sqrt(C),'mKK/MPlanck =',sqrt(C/137))
# q=6Y; all fields in left handed convention. Index for L^q = q^3 index(L).
fields=[('Q',3,2,1,1),('u^c',3,1,-4,-1),('d^c',3,1,2,-1),('L',1,2,-3,0),('e^c',1,1,6,0)]
assert sum(c*w*q for _,c,w,q,_ in fields)==0
assert sum(c*w*q**3 for _,c,w,q,_ in fields)==0
assert sum(w*q for _,c,w,q,_ in fields if c==3)==0
assert sum(c*q for _,c,w,q,_ in fields if w==2)==0
assert sum(w*a for _,c,w,q,a in fields)==0
assert sum(c for _,c,w,q,_ in fields if w==2)%2==0
print('SM one-generation anomaly sums: zero (including SU2 global parity)')
for name,c,w,q,_ in fields: print(name,'q=',q,'index=',3*q**3)
# Regge: boundary 5-simplex; repeated 1->5 moves at fixed equilateral length.
# One distinct combinatorial triangulation for each k, unit weights.
th=acos(1/4); area=sqrt(3)/4; vol=sqrt(5)/96
slope_curv=area*(20*pi-40*th)
threshold=slope_curv/(4*vol)
print('Regge fixed-length stacked family: delta N2=10, delta N4=4')
print('Convergence threshold Lambda a^2 >',threshold)
for lam in (1,threshold,2*threshold):
    # dimensionless action increment in units a^2/(8 pi G)
    print('Lambda a^2=',lam,'scaled delta action=',4*vol*lam-slope_curv)
assert threshold>0
print('No absolute G, physical positive Lambda, SM compactification, or continuum quantum gravity derived.')
