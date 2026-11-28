"""Pell projective A4 and conditional one-rotation PMNS test.
Requires Python 3 and NumPy. Run alongside runyan_neutrino_validation.py.
Reference: Feruglio arXiv:1706.08749; NuFIT 6.1 IC23 Nov 2025.
This is NOT a derived A4 Yukawa model; the mixing ansatz is independent.
"""
import math as m
import numpy as np
from itertools import product
from collections import Counter
from runyan_neutrino_validation import calibrated, observables

P=185/234
s0=(1-7/m.sqrt(234))/2
th=m.asin(m.sqrt(s0))
I=(1,0,0,1)
PELL={3:(2,1),37:(73,12),137:(6083073,519712)}
def canonical(a):
    a=tuple(x%3 for x in a); return min(a,tuple(-x%3 for x in a))
def mul(a,b):
    x,y,z,w=a; e,f,g,h=b
    return canonical((x*e+y*g,x*f+y*h,z*e+w*g,z*f+w*h))
def order(a):
    p=canonical(I)
    for k in range(1,25):
        p=mul(p,a)
        if p==canonical(I): return k
    raise RuntimeError('order')
def perm(a):
    # P^1(F3): 0,1,2,infinity; action on homogeneous columns
    pts=[(0,1),(1,1),(2,1),(1,0)]
    r=[]
    for x,y in pts:
        u=(a[0]*x+a[1]*y)%3; v=(a[2]*x+a[3]*y)%3
        r.append(3 if v==0 else u*pow(v,-1,3)%3)
    return tuple(r)
def parity(p): return sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))%2

def pmns(s12,s13,sign):
    # U=R12(eps,phi)^dagger R23(pi/4) R12(th)
    se=m.sqrt(2*s13); ce=m.sqrt(1-se*se); a=m.sin(th); b=m.cos(th)
    cosphi=(ce*ce*a*a+se*se*b*b/2-s12*(1-s13))/(m.sqrt(2)*ce*se*a*b)
    if abs(cosphi)>1: raise ValueError('infeasible')
    phi=sign*m.acos(cosphi)
    E=np.array([[ce,se*np.exp(-1j*phi),0],[-se*np.exp(1j*phi),ce,0],[0,0,1]])
    R23=np.array([[1,0,0],[0,1/m.sqrt(2),1/m.sqrt(2)],[0,-1/m.sqrt(2),1/m.sqrt(2)]])
    R12=np.array([[b,a,0],[-a,b,0],[0,0,1]])
    U=E.conj().T@R23@R12
    s23=abs(U[1,2])**2/(1-s13)
    J=(U[0,0]*U[1,1]*U[0,1].conj()*U[1,0].conj()).imag
    den=m.sqrt(s12*(1-s12)*s23*(1-s23)*s13)*(1-s13)
    cosd=(s12*s23+(1-s12)*(1-s23)*s13-s0/2)/(2*m.sqrt(s12*(1-s12)*s23*(1-s23)*s13))
    d=m.degrees(m.atan2(J/den,cosd))%360
    assert np.allclose(U.conj().T@U,np.eye(3))
    assert np.isclose(abs(U[0,1])**2/(1-s13),s12)
    assert np.isclose(abs(U[0,2])**2,s13)
    assert np.isclose(abs(U[2,0])**2,s0/2)
    assert np.isclose((J/den)**2+cosd**2,1)
    return U, s23,d,J,m.degrees(m.asin(se)),m.degrees(phi)

def main():
    gens=[]
    for D,(x,y) in PELL.items():
        assert x*x-D*y*y==1
        a=canonical((x,D*y,y,x));gens.append(a)
        print('Pell',D,'mod 3',tuple(k%3 for k in (x,D*y,y,x)),'projective order',order(a),'permutation',perm(a))
    G={canonical(I)}
    while True:
        H=G|{mul(a,b) for a in G for b in gens}
        if H==G: break
        G=H
    assert len(G)==12 and len({perm(a) for a in G})==12 and all(parity(perm(a))==0 for a in G)
    print('Generated group: A4; size',len(G),'element order counts',dict(sorted(Counter(map(order,G)).items())))
    print('Pell fixed points are +/-sqrt(D), real, not interior modular vacua.')
    print('One charged-lepton 12 rotation: fixed original neutrino angle',m.degrees(th),'and maximal bare 23; bare 13=0')
    print('Fit only sin^2 theta12=.3088 and sin^2 theta13=.02249; theta23 and CP phase outputs')
    masses=calibrated(75.37,2521.)
    for sign in (1,-1):
        U,s23,d,J,eps,phi=pmns(.3088,.02249,sign)
        print(f'eps={eps:.9f} phi={phi:.9f} sin^2 theta23={s23:.12f} theta23={m.degrees(m.asin(m.sqrt(s23))):.9f} delta={d:.9f} J={J:.12f}')
        print('abs(U)^2=\n',abs(U)**2)
        M=U.conj()@np.diag(masses)@U.conj().T
        assert np.allclose(U.T@M@U,np.diag(masses))
        print('Majorana example matrix in meV (arbitrary zero extra column phases) =\n',M)
        print('This matrix is reconstructed, not derived from A4 or CFT.')
    # Grid illustrates independent marginal intervals, not a likelihood region.
    scan=[pmns(a,b,1)[1:3] for a in np.linspace(.2893,.3295,201) for b in np.linspace(.02070,.02420,201)]
    print('Grid over independent marginal 3sigma input ranges: s23 min/max',min(x[0] for x in scan),max(x[0] for x in scan))
    print('delta (positive phi) sampled min/max',min(x[1] for x in scan),max(x[1] for x in scan))
    print('TM1 and TM2 benchmark solar values at measured reactor angle:',1-2/(3*(1-.02249)),1/(3*(1-.02249)))
    print('Conditional masses (meV):',masses,'sum, beta, Majorana freely varying min/max:',observables(masses,.3088,.02249))
    print('All assertions passed. No flavor mechanism derived, no independent CFT mass mapping.')
if __name__=='__main__': main()
