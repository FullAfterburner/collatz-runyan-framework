"""One-loop EH amplitudes and massive t-channel discontinuity. BKZ arXiv:2103.12728 F12,F15,F16,F33-F36. No UV completion claim."""
import math, cmath
from fractions import Fraction as Q
from scipy.integrate import quad
import numpy as np
from runyan_four_graviton_v11 import remainder
m2s=[(math.sqrt(234)-10)**2,(math.sqrt(234)+10)**2]

def box_im(t,a,m2):
    if t<=4*m2: return 0.
    b=math.sqrt(1-4*m2/t)
    return 4*math.pi*b/t**2*quad(lambda x:1/(1-b*b-4*b*b*a/t*x*(1-x)),0,1,epsabs=1e-11)[0]

def matter_im(t,c):
    s=-t*(1-c)/2; u=-t-s
    return sum(2*m2**3/t**3*(box_im(t,s,m2)+box_im(t,u,m2)) for m2 in m2s)

def gr(t,c,mu2=1):
    # F35, common factor rGamma/(4pi)^(2-eps)*(kappa/2)^2*Mtree removed.
    s=-t*(1-c)/2; u=-t-s
    l_s=math.log(-s/mu2); l_u=math.log(-u/mu2); l_t=math.log(t/mu2)-1j*math.pi
    L=math.log(s/u)
    A=4*s**6+14*s**5*u+28*s**4*u**2+35*s**3*u**3+28*s**2*u**4+14*s*u**5+4*u**6
    B=(s-u)*(261*s**4+809*s**3*u+1126*s**2*u**2+809*s*u**3+261*u**4)
    C=1682*s**4+5303*s**3*u+7422*s**2*u**2+5303*s*u**3+1682*u**4
    pole=2*(s*l_s+t*l_t+u*l_u)
    finite=2*(u*l_t*l_s+t*l_s*l_u+s*l_t*l_u)+s*t*u*(A/t**8*(L**2+math.pi**2)+B/(30*t**7)*L+C/(180*t**6))
    return pole,finite

if __name__=='__main__':
    print('masses squared/M^2:',m2s)
    print('t/(4m_-^2), c, Im stripped matter/K (cut), independent contour, relative error')
    for x in [.75,1.2,2.,25.]:
        t=4*m2s[0]*x
        for c in [0.,.5]:
            s=-t*(1-c)/2; u=-t-s
            cut=matter_im(t,c)
            if x<=2:
                ref=2*sum(remainder(s,u,m2,40,.55)[1] for m2 in m2s)
                err=abs(ref.imag-cut)/max(abs(cut),1e-12)
                assert err<.005
                print(x,c,cut,float(ref.imag),float(err))
            else: print(x,c,cut,'not integrated')
    print('Forward absorptive moment check: integral Im f(t,1)/t /pi, t channel only')
    # f(t,1) has both right and left cuts: this is only one moment, not full Wilson sum rule.
    for m2 in m2s:
        # Im f=2 m^6/t^3*(boxes), change variable y=4m^2/t
        val=quad(lambda y: (2*m2**3/(4*m2/y)**3*(box_im(4*m2/y,0,m2)+box_im(4*m2/y,-4*m2/y,m2)))/y/math.pi,0,1,epsabs=1e-13)[0]
        exact=1/(700*m2*m2)
        assert abs(val/exact-1)<1e-8
        print(m2,val,'scaled',val*m2*m2)
    print('Forward tree phase-space optical test (kappa/2=1)')
    for x in [1.01,1.2,2.,25.]:
        t=4*m2s[0]*x
        rhs=0.
        for m2 in m2s:
            if t<=4*m2: continue
            b=math.sqrt(1-4*m2/t)
            # 4 real scalars with identical final-state factor 1/2;
            # one Dirac pair: spin sum of massive chiral bracket = t-2m^2.
            rhs+=b/(8*math.pi)*quad(lambda c: (2+(t-2*m2)/m2)*(4*m2**2/t/(1-b*b*c*c))**2,0,1)[0]
        lhs=2*t**4/(16*math.pi**2)*matter_im(t,1.)
        assert abs(lhs/rhs-1)<1e-10
        print(x,lhs,rhs)
    import sympy as sp
    b=sp.symbols('b',real=True)
    exact=(sp.integrate(b*b*(1-b*b)**3,(b,0,1))+sp.integrate((1-b*b)**4,(b,0,1))/10)/64
    assert exact==sp.Rational(1,700)
    print('Exact one-sided dispersive moment:',exact)
    print('Pure EH reduced MHV ratio: t=mu^2=1 (prefactor removed)')
    for c in [0,.25,.5,.75,.9]:
        p,f=gr(1,c); p2,f2=gr(1,-c)
        assert abs(p-p2)<1e-10 and abs(f-f2)<1e-10
        assert abs(p.imag+2*math.pi)<1e-12
        print(c,p,f)
    # All-plus and single-minus absolute amplitudes / (K t^2), physical region.
    # |[12]<13>[14]|^4=|stu|^2, hence ratio 3.
    for c in [0,.5,.9]:
        s=-(1-c)/2; u=-(1+c)/2; a=(s*s+1+u*u)/120; b=a/3
        print('rational channels:',c,a,b)
    print('All implemented checks passed.')
