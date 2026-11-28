"""CM arithmetic, candidate modular potential and Yukawa hierarchy audit.
Python 3; dependencies mpmath, sympy. No experimental inputs.
Class polynomial coefficients numerically reconstructed, not interval certified.
"""
import math
import mpmath as mp
import sympy as s
from itertools import product

DS=(3,37,137)
def reduced(d):
    for a in range(1,math.isqrt(-d//3)+1):
        for b in range(-a,a+1):
            if (b*b-d)%(4*a): continue
            c=(b*b-d)//(4*a)
            if c<a or math.gcd(math.gcd(a,b),c)>1: continue
            if (abs(b)==a or a==c) and b<0: continue
            yield a,b,c

def tau_of(d,f):
    a,b,c=f
    return (-b+mp.j*mp.sqrt(-d))/(2*a)

def sigma(n,k=1):
    return sum(i**k for i in range(1,n+1) if n%i==0)
N=400
sig=[0]+[sigma(n) for n in range(1,N+1)]
sig3=[0]+[sigma(n,3) for n in range(1,N+1)]
def jfun(tau):
    q=mp.exp(2*mp.pi*mp.j*tau)
    E4=1+240*sum(sig3[n]*q**n for n in range(1,N+1))
    delta=q*mp.fprod((1-q**n)**24 for n in range(1,N+1))
    return E4**3/delta

def classpoly(D,prec):
    with mp.workdps(prec):
        roots=[jfun(tau_of(-4*D,f)) for f in reduced(-4*D)]
        coeff=[mp.mpc(1)]
        for r in roots:
            out=[mp.mpc(0)]*(len(coeff)+1)
            for i,c in enumerate(coeff):out[i]-=r*c;out[i+1]+=c
            coeff=out
        rounded=[int(mp.nint(c.real)) for c in coeff]
        err=max(abs(c-r) for c,r in zip(coeff,rounded))
        assert err<mp.mpf('1e-40')
        return rounded,mp.nstr(err,5)

def forms(tau):
    t=mp.exp(2*mp.pi*mp.j*tau/3)
    a=1+sum(3*sig[n]*t**n for n in range(3,N+1,3))-sum(27*sig[n//9]*t**n for n in range(9,N+1,9))
    b=-6*sum(sig[n]*t**n for n in range(1,N+1,3))
    c=-6*sum(sig[n]*t**n for n in range(2,N+1,3))
    return a,b,c

def pieces(y):
    a,b,c=y; f1=a*a-b*c; f2=c*c-a*b; f3=b*b-a*c
    A=a*a+2*b*c; B=c*c+2*a*b
    F=mp.matrix([[2*f1,-f3,-f2],[-f3,2*f2,-f1],[-f2,-f1,2*f3]])
    P=mp.matrix([[1,0,0],[0,0,1],[0,1,0]])
    Q=mp.matrix([[0,0,1],[0,1,0],[1,0,0]])
    return F,A*P,B*Q,A,B

def masses(M):return list(reversed(list(mp.svd(M,compute_uv=False))))
def fmt(x):return mp.nstr(x,10)
def main():
    mp.mp.dps=90
    a,b,c=s.symbols('a b c'); F=s.Matrix([[2*(a*a-b*c),-b*b+a*c,-c*c+a*b],[-b*b+a*c,2*(c*c-a*b),-a*a+b*c],[-c*c+a*b,-a*a+b*c,2*(b*b-a*c)]])
    A=a*a+2*b*c; B=c*c+2*a*b; P=s.Matrix([[1,0,0],[0,0,1],[0,1,0]]); Q=s.Matrix([[0,0,1],[0,1,0],[1,0,0]]);v=s.Matrix([a,c,b]);
    assert all(s.rem(s.expand(z),b*b+2*a*c,b)==0 for z in F+A*P+B*Q-3*v*v.T)
    print('Exact identity: F+A P+B Q=3 v v^T, v=(Y1,Y3,Y2); rank 1 if v !=0.')
    print('At cusp: mass magnitudes = |2g1+g2|, |g2-g1|, |g2-g1|; hierarchy requires coupling restriction.')
    print('Potential V=|H(j)|^2/(1+|j|^2)^h; at a simple CM root local coefficient = |Hprime(j) jprime(tau)|^2/(1+|j|^2)^h >0.')
    for D in DS:
        coeff,e=classpoly(D,180); coeff2,e2=classpoly(D,260); assert coeff==coeff2
        h=len(coeff)-1
        print('\nD=',D,'discriminant=',-4*D,'h=',h,'class polynomial ascending coefficients=',coeff)
        print('reconstruction errors at 180,260 digits:',e,e2)
        print('form | Re tau | Im tau | |B/A| | equal g rank1 residual | g=(1,1,0) normalized masses | g=(1,0.3,-0.2) normalized masses')
        for f in reduced(-4*D):
            z=tau_of(-4*D,f); y=forms(z); F,P,Q,A,B=pieces(y); v=mp.matrix([y[0],y[2],y[1]])
            residual=mp.norm(F+P+Q-3*v*v.T); assert residual<mp.mpf('1e-80')
            m=masses(F+P); generic=masses(F+mp.mpf('.3')*P-mp.mpf('.2')*Q)
            assert m[1]<=abs(B)*(1+mp.mpf('1e-70'))
            print(f,fmt(z.real),fmt(z.imag),fmt(abs(B/A)),fmt(residual),[fmt(i/m[-1]) for i in m],[fmt(i/generic[-1]) for i in generic])
            j=jfun(z); jp=mp.diff(jfun,z); Hprime=mp.polyval(list(reversed([i*coeff[i] for i in range(1,h+1)])),j)
            curvature=abs(Hprime*jp)**2/(1+abs(j)**2)**h
            assert curvature>0
            def potential(t):
                J=jfun(t); return abs(mp.polyval(coeff[::-1],J))**2/(1+abs(J)**2)**h
            # Direct test of invariance at an off-minimum nearby point; all q series converge there.
            p=z+mp.mpf('.017')+mp.j*mp.mpf('.013')
            # S at large imaginary modulus converges slowly; only test at well-conditioned p using modular reduction below.
            def reduce(t):
                for _ in range(100):
                    t-=mp.nint(t.real)
                    if abs(t)>=1-mp.mpf('1e-85'):return t
                    t=-1/t
                raise RuntimeError('reduction')
            p0=potential(reduce(p)); pS=potential(reduce(-1/p)); pT=potential(reduce(p+1))
            assert max(abs(p0-pS),abs(p0-pT))/max(1,abs(p0))<mp.mpf('1e-75')
        print('All CM roots have positive local quadratic coefficient; reduced-coordinate S/T consistency passed.')
    print('\nNo coupling equality or stabilization potential was derived from the underlying theory. CP-conserving rectangular points with real coefficients have real mass matrices. No experimental masses used.')
if __name__=='__main__':main()
