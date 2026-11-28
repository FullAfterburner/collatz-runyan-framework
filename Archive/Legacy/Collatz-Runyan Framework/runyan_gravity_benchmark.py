"""Arithmetic T^6 benchmark; not a derivation of physical constants.
Uses SI for observational benchmarks, dimensionless radii for the internal geometry.
Requires only Python standard library.
"""
from math import sqrt, pi, log, prod, tanh, log10
from fractions import Fraction
D=(3,37,137)
units=((2,1),(73,12),(6083073,519712))
for d,(x,y) in zip(D,units):
    assert x*x-d*y*y==1
    # Integer preservation of diag(1,-D), extended by two spatial directions.
    L=((x,d*y,0,0),(y,x,0,0),(0,0,1,0),(0,0,0,1))
    g=(1,-d,-1,-1)
    assert all(sum(g[k]*L[k][i]*L[k][j] for k in range(4))==(g[i] if i==j else 0) for i in range(4) for j in range(4))
    print(f'D={d}: exact Pell and extended Lorentz isometry; rapidity={log(x+y*sqrt(d)):.12g}; 1-beta={1/(x*(x+y*sqrt(d))):.12g}')
N=prod(D); assert N==15207
radii=(1,sqrt(3),1,sqrt(37),1,sqrt(137))
print('det dimensionless internal metric:',N)
print('volume factor relative to equal radii:',sqrt(N))
print('G4 ratio at fixed G10 and R:',1/sqrt(N))
print('V6/R^6 with 2pi-periodic angles:',(2*pi)**6*sqrt(N))
print('pure KK masses squared in units 1/R^2:',[str(Fraction(1,d)) for d in D])
print('lightest pure KK mass in units 1/R:',1/sqrt(max(D)))
# Count integer momentum states at exact first three pure KK levels.
from itertools import product
from collections import Counter
metric=(1,3,1,37,1,137)
cut=Fraction(1,3)
# range from exact upper bound: |n|^2 <= cut*d
from math import isqrt
ranges=[range(-isqrt((cut*d).numerator//(cut*d).denominator),isqrt((cut*d).numerator//(cut*d).denominator)+1) for d in metric]
levels=Counter()
for n in product(*ranges):
    q=sum((Fraction(k*k,d) for k,d in zip(n,metric)),Fraction(0))
    if q<=cut: levels[q]+=1
print('First six nonzero pure KK levels (mass squared, momentum multiplicity):',sorted(levels.items())[1:7])
G=6.67430e-11; c=299792458.; hbar=1.054571817e-34; eV=1.602176634e-19
H0=67.4*1000/3.085677581491367e22; omega=0.685
Lam=3*omega*H0**2/c**2
lp2=hbar*G/c**3
rho=Lam*c**4/(8*pi*G)
energy=(rho*(hbar*c)**3)**.25/eV
print('Planck LCDM benchmark Lambda [m^-2]:',Lam)
print('Lambda*lP^2:',Lam*lp2)
print('Vacuum energy density [J/m^3]:',rho)
print('Vacuum energy fourth-root [eV]:',energy)
print('EW scale (100 GeV)^4 / observed vacuum density:',(1e11/energy)**4)
print('Unmodified flat supersymmetric torus: Lambda=0, moduli unfixed; no prediction of G4.')
