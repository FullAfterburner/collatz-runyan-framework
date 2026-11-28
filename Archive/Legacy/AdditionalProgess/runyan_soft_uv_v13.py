"""Leading soft-graviton inclusive factor and massless two-loop R^3 running.
No massive two-loop computation. References: Weinberg PR 140 B516 (1965);
Bern et al. PRD 95 046013 (2017), eqs. 13,14,29-35.
Units hbar=c=1. s is positive CM energy squared, G=1 for numerical ratios.
"""
import math
import numpy as np
import sympy as sp
from scipy.special import roots_legendre
from fractions import Fraction

def soft_B(theta, beta=1., s=1., G=1., n=320):
    # Incoming massless pair; outgoing equal-mass pair with speed beta.
    x,w=roots_legendre(n); phi=(np.arange(2*n)+.37)*np.pi/n
    X,Y,Z=np.broadcast_arrays(np.sqrt(1-x[:,None]**2)*np.cos(phi),np.sqrt(1-x[:,None]**2)*np.sin(phi),x[:,None])
    nh=np.stack((X,Y,Z),axis=-1)
    v=np.array([[0.,0.,1.],[0.,0.,-1.],[beta*math.sin(theta),0.,beta*math.cos(theta)],[-beta*math.sin(theta),0.,-beta*math.cos(theta)]])
    J=np.zeros(nh.shape[:-1]+(3,3)); E=math.sqrt(s)/2
    for vi,eta in zip(v,[-1,-1,1,1]):
        c=nh@vi; vp=vi-c[...,None]*nh
        J+=eta*E*vp[..., :,None]*vp[...,None,:]/(1-c[...,None,None])
    norm=np.sum(J*J,axis=(-1,-2))-.5*np.trace(J,axis1=-2,axis2=-1)**2
    assert np.min(norm)>-1e-12*s
    # helicity tensors normalized to unit norm, Lorentz invariant d^3q/(2omega(2pi)^3)
    return (32*math.pi*G/4)/(2*(2*math.pi)**3)*np.sum(w[:,None]*norm)*math.pi/n

def entropy(theta):
    x=(1-math.cos(theta))/2
    return -x*math.log(x)-(1-x)*math.log1p(-x)

def cut_hat(theta,n=48):
    # Bern et al eq.29; symmetric azimuthal integral.
    x,w=roots_legendre(n); ph=(np.arange(2*n)+.5)*math.pi/n
    a=math.cos(theta)**2*(1-x[:,None]**2)-math.sin(theta)**2*(1-x[:,None]**2)*np.cos(ph)**2-.5*math.sin(2*theta)*2*x[:,None]*np.sqrt(1-x[:,None]**2)*np.cos(ph)
    return np.sum(w[:,None]*a/(1-x[:,None]))/(2*(2*n)*16*math.pi)

if __name__=='__main__':
    print('Massless elastic soft coefficient B/(Gs): angle, numeric, closed form, relative error')
    for deg in [15,30,45,60,90,120,150]:
        th=math.radians(deg); calc=soft_B(th); exact=4/math.pi*entropy(th)
        err=abs(calc/exact-1); assert err<5e-4
        print(deg, f'{calc:.10f}',f'{exact:.10f}',f'{err:.3e}')
    print('Threshold soft factor (incoming massless, outgoing at rest) B/(Gs):',soft_B(.7,0.))
    assert abs(soft_B(.7,0.)-1/math.pi)<1e-12
    m=np.array([math.sqrt(234)-10,math.sqrt(234)+10]); s=4*m*m
    vals=[soft_B(.7,.6,si/(1-.6**2)) for si in s]
    ratio=vals[1]/vals[0]; exact=(m[1]/m[0])**2
    assert abs(ratio/exact-1)<1e-12
    print('Arithmetic pair-production soft factors at beta=.6, theta=.7, G M^2=1:',vals,'ratio',ratio)
    print('Threshold limiting B/(G M^2) =',list(s/math.pi))
    print('Inclusive soft factors: Gs=.01, theta=90deg, Delta/Esoft=.01')
    B=.01*4/math.pi*math.log(2)
    for lam in [1e-4,1e-8,1e-12,1e-30]:
        virtual=B*math.log(lam); real=B*math.log(.01/lam)
        result=math.exp(virtual+real); assert abs(result-(.01)**B)<1e-14
        print(lam,math.exp(virtual),math.exp(real),result)
    print('IR-subtracted 2-body cut angular integral (Bern eq 29):')
    for deg in [0,15,30,45,60,90,120,150,180]:
        th=math.radians(deg); calc=cut_hat(th); target=(3*math.cos(th)**2-1)/(32*math.pi)
        assert abs(calc-target)<1e-14
        print(deg,calc,target)
    s,t=sp.symbols('s t'); u=-s-t
    assert sp.expand(s*(s*s-6*t*u)+t*(t*t-6*s*u)+u*(u*u-6*s*t)+15*s*t*u)==0
    print('Crossed channel polynomial = -15 s t u (exact)')
    print('Massless R^3 running normalized by (kappa/2)^2/(4pi)^4:')
    for name,nb,nf in [('Einstein',2,0),('arithmetic matter alone',8,8),('Einstein + arithmetic',10,8),('plus one massless Majorana spinor',10,10)]:
        print(name,nb,nf,'beta coefficient',Fraction(nb-nf,240),'amplitude ln coefficient',Fraction(-(nb-nf),8))
    print('All assertions passed. No massive two-loop amplitude, finite R^3 matching, or all-order UV completion claimed.')
