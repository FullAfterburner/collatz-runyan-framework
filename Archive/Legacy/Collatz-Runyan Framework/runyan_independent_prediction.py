"""Test the pre-existing (1,1,0) modular Yukawa texture; no fit.
Requires mpmath and sympy. Imports earlier CM implementation.
Benchmarks: NuFIT 6.1 IC23 without SK; ATLAS PDG2024 constants.
"""
import mpmath as mp
import sympy as s
from runyan_cm_hierarchy import reduced,tau_of,forms,pieces,masses
mp.mp.dps=80
x,y,z,t=s.symbols('x y z t'); v=s.Matrix([x,z,y]); P=s.Matrix([[0,0,1],[0,1,0],[1,0,0]]); B=z*z+2*x*y
M=3*v*v.T+t*B*P
assert s.expand(M.det()+t*t*(t+3)*B**3)==0
print('det(3 vv^T+t B P)=-t^2(t+3)B^3, symbolic verification passed.')
print('g=(1,1,0); middle singular value = |B|; m1*m3=2*m2^2.')
# Tests from the entire predetermined CM set. No data used to construct masses.
rows=[]
for D in (3,37,137):
    for f in reduced(-4*D):
        tau=tau_of(-4*D,f); F,A,C,_,B=pieces(forms(tau)); a,b,c=masses(F+A)
        assert abs(b-abs(B))/abs(B)<mp.mpf('1e-65')
        assert abs(a*c/(2*b*b)-1)<mp.mpf('1e-55')
        p,r=a/c,b/c
        R=(r*r-p*p)/(1-p*p)
        rows.append((D,f,p,r,R))
print('D | reduced form | m1/m3 | m2/m3 | R_NO')
for D,f,p,r,R in rows:
    print(D,f,*[mp.nstr(z,14) for z in (p,r,R)],sep=' | ')
# Comparison stage only
sol,atm=mp.mpf('75.37'),mp.mpf('2521')
R0=sol/atm; Rlo=mp.mpf('72.36')/2592; Rhi=mp.mpf('78.23')/2454
print('NuFIT R_NO central, conservative marginal envelope:',*[mp.nstr(z,14) for z in (R0,Rlo,Rhi)])
print('Number of CM points in envelope:',sum(Rlo<=row[-1]<=Rhi for row in rows))
print('Closest point(s):',[(D,f,mp.nstr(R,14)) for D,f,p,r,R in rows if abs(R-R0)==min(abs(row[-1]-R0) for row in rows)])
me,mm,mt=map(mp.mpf,('0.51099895','105.6583755','1776.93'))
print('Charged lepton m_e*m_tau/m_mu^2:',mp.nstr(me*mt/mm**2,14),'texture requires 2')
print('Texture charged lepton e/tau if mu/tau measured:',mp.nstr(2*(mm/mt)**2,14),'observed:',mp.nstr(me/mt,14))
r0=(mp.sqrt(234)+10)/(mp.sqrt(234)-10); q=1/(2*r0); p=2*q*q
print('Original m2/m1:',mp.nstr(r0,14),'implies R_NO:',mp.nstr((q*q-p*p)/(1-p*p),14))
for sign in (-1,1):
    w=(1+sign*mp.sqrt(1-16*R0*(1-R0)))/(8*(1-R0)); r=mp.sqrt(w); p=2*w; scale=mp.sqrt(atm/(1-p*p)); m=[p*scale,r*scale,scale]
    print('Conditional continuous texture solution, fitted to splittings, meV:',*[mp.nstr(z,12) for z in m], 'sum:',mp.nstr(sum(m),12))
print('All numerical checks passed. No CM vacuum selected after comparison; no new successful independent physical prediction.')
