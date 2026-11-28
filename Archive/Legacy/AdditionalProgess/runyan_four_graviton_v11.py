"""Matched massive matter 4-graviton amplitude, real and deformed contour numerical evaluation.
Uses Bern, Kosmopoulos, Zhiboedov arXiv:2103.12728v2, eqs 32,34,242,245,246,278,298.
No graviton loops, no independent higher-curvature Wilson coefficients.
All invariants use the source's labeling, t=-s-u. Set M=1.
"""
import numpy as np
from scipy.special import roots_legendre
from math import factorial
from fractions import Fraction as Q
from functools import lru_cache

@lru_cache(None)
def simplex(n,order):
    if n==1: return np.ones((1,1),dtype=np.longdouble),np.ones(1,dtype=np.longdouble)
    x,w=roots_legendre(order); x=(x.astype(np.longdouble)+1)/2; w=w.astype(np.longdouble)/2
    xs=np.meshgrid(*([x]*(n-1)),indexing='ij'); ws=np.meshgrid(*([w]*(n-1)),indexing='ij')
    rem=np.ones_like(xs[0]); weight=np.ones_like(rem); coords=[]
    for j in range(n-1):
        coords.append(rem*xs[j]); weight*=rem*ws[j]; rem*=1-xs[j]
    coords.append(rem)
    return np.array([v.ravel() for v in coords]),weight.ravel()

def integral(n,d,m2,a=0,b=0,order=32,deform=0):
    x,w=simplex(n,order); q=np.full(w.shape,m2,dtype=np.longdouble)
    if n==2: q-=a*x[0]*x[1]
    if n>=3: q-=a*x[0]*x[2]
    if n==4: q-=b*x[1]*x[3]
    if deform and n>1:
        # Deform the simplex tangentially; each boundary is preserved.
        # Im Q = -deform/m2 * weighted variance of gradient (exact for quadratic Q).
        H=np.zeros((n,n),dtype=np.longdouble)
        if n==2: H[0,1]=H[1,0]=-a
        if n>=3: H[0,2]=H[2,0]=-a
        if n==4: H[1,3]=H[3,1]=-b
        g=H@x; mean=np.sum(x*g,axis=0); V=x*(g-mean)
        dh=H[:,:-1]-H[:,[-1]]; dm=2*(g[:-1]-g[-1])
        J=np.empty((len(w),n-1,n-1),dtype=complex)
        for i in range(n-1):
            for j in range(n-1):
                dv=(g[i]-mean)*(i==j)+x[i]*(dh[i,j]-dm[j])
                J[:,i,j]=(i==j)-1j*deform/m2*dv
        w=w*np.linalg.det(J)
        y=x-1j*deform/m2*V
        q=m2+np.sum(y*(H@y),axis=0)/2
        assert np.max(q.imag)<1e-10
    elif np.min(q)<=0: raise ValueError('Threshold crossed: enable contour deformation')
    k=n-d//2
    if k>0: return np.array([0,np.dot(w,factorial(k-1)*q**(-k))],dtype=np.clongdouble if deform else np.longdouble)
    l=-k; r=(-1)**l*q**l/factorial(l); h=sum(Q(1,j) for j in range(1,l+1))
    # finite part in a common convention with Euler constant removed; pole cancels in amplitude
    return np.array([np.dot(w,r),np.dot(w,r*(float(h)-np.log(q)))],dtype=np.clongdouble if deform else np.longdouble)

def remainder(s,u,m2,order=32,deform=0):
    s,u,m2=map(np.longdouble,(s,u,m2)); t=-s-u
    def I(n,d,a=0,b=0): return integral(n,d,m2,a,b,order,deform)
    F1=(4*s*s+7*s*u+4*u*u)/(8*t*t)*I(1,4)+(s-u)**2*t/(16*s*u)*I(2,4,t)+3*I(2,6,t)/4
    F1+=(s**5+u**5)*t/(32*s*s*u*u)*I(3,4,t)+(s**3+u**3)/(4*s*u)*I(3,6,t)-15*I(3,8,t)/8
    F1+=-s**4*u**4/(64*t**5)*I(4,4,s,u)+15*s**3*u**3/(32*t**4)*I(4,6,s,u)-45*s*s*u*u/(16*t**3)*I(4,8,s,u)+15*s*u/(8*t*t)*I(4,10,s,u)
    def F2(s,u):
        return (s**3*(s+2*u)*(s*s+2*s*u+2*u*u)/(16*u*t**4)*I(2,4,s)
        +(3*s**3+7*s*s*u+12*s*u*u+2*u**3)/(4*t**3)*I(2,6,s)
        -s**4*(s+2*u)*(s**4+3*s**3*u+4*s*s*u*u+2*s*u**3+u**4)/(32*u*u*t**5)*I(3,4,s)
        -s**3*(2*s**3+6*s*s*u+6*s*u*u-5*u**3)/(8*u*t**4)*I(3,6,s)
        -3*s*s*(5*s+16*u)/(8*t**3)*I(3,8,s)
        +s**4*t/(64*u*u)*I(4,4,s,t)+3*s**3/(32*u)*I(4,6,s,t)+9*s*s/(16*t)*I(4,8,s,t)+15*s*u/(8*t*t)*I(4,10,s,t))
    return -(F1+F2(s,u)+F2(u,s))/(s*t*u)

def eft(s,u,m2):
    t=-s-u
    return (1/(1120*m2**2)+t/(8400*m2**3)+(15*(s*s+u*u)+28*s*u)/(554400*m2**4)+t*(153*(s*s+u*u)+313*s*u)/(30270240*m2**5))

if __name__=='__main__':
    m=np.array([(np.sqrt(np.longdouble(234))-10)**2,(np.sqrt(np.longdouble(234))+10)**2])
    S=[Q(2),Q(668,17956)]
    for i in range(2,7): S.append((668*S[-1]-S[-2])/17956)
    for n,x in enumerate(S): assert np.isclose(float(x),np.sum(m**(-n)),rtol=1e-13)
    print('m^2/M^2:',m)
    print('Exact inverse-mass moments:',S)
    print('Leading coefficient S2/560:',S[2]/560,float(S[2]/560))
    print('R^4 lower-sector fraction:', float(m[0]**-2/np.sum(m**-2)))
    # energy variable t>0, s,u negative, fixed angle; amplitude f/K with M=1
    print('t/(4m_-^2), cos(theta), f_CR/K, EFT through degree 3, rel.diff, quadrature rel.diff, pole residual')
    for e in [.1,.25,.5,.75,.9]:
        for c in [0.,.5]:
            t=4*m[0]*e; s=-t*(1-c)/2; u=-t*(1+c)/2
            v=2*sum((remainder(s,u,mi,32) for mi in m)); w=2*sum((remainder(s,u,mi,48) for mi in m)); low=2*sum(eft(s,u,mi) for mi in m)
            err=abs((v[1]-w[1])/w[1]); pole=abs(w[0]); diff=abs((low-w[1])/w[1]);
            assert err<2e-4 and pole<1e-10 and w[1]>0
            assert np.isclose(w[1],2*sum(remainder(u,s,mi,32)[1] for mi in m),rtol=2e-4)
            print(f'{e:.2f} {c:.1f} {float(w[1]):.12g} {float(low):.12g} {float(diff):.6g} {float(err):.6g} {float(pole):.6g}')
    print('Complex contour tests, t/(4m_-^2), f_CR/K, relative variation under quadrature/deformation:')
    for e in [.75,1.2,2.]:
        t=4*m[0]*e; s=u=-t/2
        vv=[]
        for order,deform in [(16,.35),(24,.35),(32,.55)]:
            v=2*sum((remainder(s,u,mi,order,deform) for mi in m)); vv.append(v[1])
        diff=max(abs((x-vv[-1])/vv[-1]) for x in vv[:-1]); print(e,complex(vv[-1]),float(diff))
        if e<1: assert abs(vv[-1].imag)<1e-10
    print('Below-threshold assertions passed; complex contour results are convergence diagnostics, not certified. Pure gravity loops excluded.')
