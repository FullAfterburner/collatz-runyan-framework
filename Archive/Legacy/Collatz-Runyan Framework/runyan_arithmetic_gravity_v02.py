"""Restricted arithmetic flux, chirality and Euclidean Regge benchmarks.
Requires sympy. No experimental measurements used. Not a global string vacuum.
"""
from itertools import combinations, product
from fractions import Fraction
from math import prod, sqrt, log, acos, pi
import sympy as sp

D=(3,37,137); P=prod(D)
a,b,c=sp.symbols('a b c', positive=True, real=True)
u=[a,b,c]; s=a*b*c; I=sp.I
S,U,V,Z=sp.symbols('S U V Z'); z=[S,U,V,Z]; us=z[1:]
H=1+sum(us); F=prod(us)-sum(u[i]**2*prod(us[j] for j in range(3) if i!=j) for i in range(3))
W=F-S*H; point=dict(zip(z,[I*s,I*a,I*b,I*c])); scale=[s,a,b,c]
W0=sp.simplify(W.subs(point)); residual=[sp.simplify(sp.diff(W,zi).subs(point)-W0/(2*I*sc)) for zi,sc in zip(z,scale)]
assert residual==[0]*4
print('D =',D,'P =',P,'g_s =',1/sqrt(P)); print('F terms:',residual,'W/s =',sp.expand(W0/s))
# Jacobian: f_i = scale_i D_i W/s; z_i = scale_i (i + delta_i)
A=sp.zeros(4); B=sp.zeros(4)
for i in range(4):
 for j in range(4):
  A[i,j]=sp.simplify(scale[i]*scale[j]*sp.diff(W,z[i],z[j]).subs(point)/s + W0/(4*s)*(1-int(i==j)))
  B[i,j]=W0/(4*s)*int(i==j)
C=A+B; E=I*(A-B)
J=C.applyfunc(sp.re).row_join(E.applyfunc(sp.re)).col_join(C.applyfunc(sp.im).row_join(E.applyfunc(sp.im)))
det=sp.factor(J.det(method='domain-ge')); assert det==-16*a*a*b*b*c*c
print('Exact normalized real Jacobian determinant:',det,'=',det.subs(dict(zip(u,map(sp.sqrt,D)))))
# Hodge-star pairing charge: k=saxiodilaton * sqrt(P), each H monomial y subset J has F/H ratio k/D_J (absolute).
patterns=list(product((0,1),repeat=3)); divs=[prod(d for d,j in zip(D,pat) if j) for pat in patterns]
# For arbitrary rational k, clipping p-adic valuations to [0,1] and removing other primes cannot increase any charge weight.
# Therefore enumerate only divisors of P; require full rank in log-saxion equations.
fullrank=[ids for ids in combinations(range(8),4) if sp.Matrix([[1]+[1-2*j for j in patterns[i]] for i in ids]).det()!=0]
answers=[]
for k in divs:
 weights=[Fraction(k,v).numerator*Fraction(k,v).denominator for v in divs]
 for ids in fullrank: answers.append((sum(weights[i] for i in ids),k,ids))
minimum=min(x[0] for x in answers); assert minimum==178
print('Restricted minimum flux charge:',minimum,'; full-rank support sets:',len(fullrank),' ; minimizing choices:',sum(x[0]==minimum for x in answers))
print('Example charge:',1+sum(D),'(covering torus unit convention; orientifold quantization may increase it)')
# Chiral index and slope-zero benchmark, with independent Kähler area A3.
flux=(-1,-1,3); A1,A2=sqrt(3),sqrt(37); A3=3/(1/A1+1/A2)
assert prod(flux)==3 and abs(sum(n/A for n,A in zip(flux,[A1,A2,A3])))<1e-14
print('Chiral index:',prod(flux),'slope-zero areas:',A1,A2,A3)
# Pell units: multiplicative independence follows from intersection of distinct quadratic fields.
for d,x,y in [(3,2,1),(37,73,12),(137,6083073,519712)]:
 assert x*x-d*y*y==1
 print('Pell rapidity',d,log(x+y*sqrt(d)))
# Boundary of a 5-simplex, equilateral Euclidean Regge action scale sector.
delta=2*pi-3*acos(1/4); Acoeff=20*sqrt(3)/4*delta; Vcoeff=6*sqrt(5)/96
print('Regge: 6 vertices, 15 edges, 20 triangles, 15 tetrahedra, 6 four-simplices')
print('Deficit:',delta,'; A_delta coefficient:',Acoeff,'; volume coefficient:',Vcoeff)
print('Stationary Lambda*a^2:',Acoeff/(2*Vcoeff))
print('No-scale volume remains flat. Positive uplift alone is runaway. No global string embedding, observed Lambda, or independent quantum gravity derived.')
