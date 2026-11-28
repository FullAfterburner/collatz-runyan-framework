"""Independent arithmetic and local-geometry audit, not an independent amplitude derivation.
Requires sympy and mpmath. All inputs are from the supplied cross-audit.
"""
import sympy as s
import mpmath as mp
from fractions import Fraction
from math import isqrt
mp.mp.dps=80
R=s.Rational
# Exact decimal input fourth moments (billions of GeV^4).
terms=[R('125.25')**4,6*R('80.377')**4,3*R('91.1876')**4,-12*R('172.5')**4]
Q=sum(terms); f2=R('246.22')**2+1000**2
print('Higgs, W, Z, top fourth moments / 1e9:',*[s.N(t/10**9,15) for t in terms])
print('Qmin, threshold, m_s^2 at X=500, Vmin:',*[s.N(t,15) for t in [Q,(-Q)**R(1,4),(Q+500**4)/(8*s.pi**2*f2),-(Q+500**4)/(128*s.pi**2)]])
# Minimal units in integer Pell lattice: enumerate y up to given solution.
for D, x0, y0, x1,y1 in [(3,2,1,2,1),(37,6,1,73,12),(137,1744,149,6083073,519712)]:
    first=None
    for y in range(1,y0+1):
        for norm in [-1,1]:
            x=isqrt(D*y*y+norm)
            if x*x-D*y*y==norm:
                first=(x,y,norm); break
        if first:break
    assert first[:2]==(x0,y0) and x1*x1-D*y1*y1==1
    if first[2]==-1:
        assert (x0*x0+D*y0*y0,2*x0*y0)==(x1,y1)
    print('Pell D, fundamental integer-lattice unit (x,y,norm), norm-one unit:',D,first,(x1,y1))
# Inverse-mass moment chain
m2=[334-20*s.sqrt(234),334+20*s.sqrt(234)]
assert s.simplify(sum(m2))==668 and s.prod(m2).expand()==17956
mom=[R(2),R(668,17956)]
for n in range(2,7):mom.append((668*mom[-1]-mom[-2])/17956)
for n,v in enumerate(mom):assert s.simplify(sum(m**(-n) for m in m2)-v)==0
print('Mass moments S0..6:',mom)
print('Leading coefficient:',mom[2]/560,'one-sided:',mom[2]/700)
assert (mom[2]/700)/(mom[2]/560)==R(4,5)
b=s.symbols('b',positive=True)
# Substitute t=4m^2/(1-beta^2) into forward discontinuity moment; integrate by parts.
J=s.integrate(b*b*(1-b*b)**3+R(1,10)*(1-b*b)**4,(b,0,1))/64
assert J==R(1,700)
print('Forward moment integral (times m^4):',J)
# Soft factor: invariant massless elastic IR relation; crossing polynomial.
a,t,u=s.symbols('s t u'); assert s.expand((a*(a*a-6*t*u)+t*(t*t-6*a*u)+u*(u*u-6*a*t)+15*a*t*u).subs(u,-a-t))==0
print('Massless 2-loop log coefficient state-count beta: Einstein+matched',R(10-8,240),'with extra Majorana',R(10-10,240))
# Polonyi mass supertraces, direct physical eigenvalue sums.
g,M=s.symbols('g M',positive=True); z=s.sqrt(3)-1
hidden=[2*s.sqrt(3)*g*g,(4-2*s.sqrt(3))*g*g]
for c,k in [(0,0),(R(1,3),R(1,3))]:
    soft=(1-3*c)*g*g
    B=s.sqrt(3)*(k+(1-2*c)*z)-1
    st2=sum(hidden)-4*g*g; st4=sum(h*h for h in hidden)-4*g**4
    for mass in [M*(s.sqrt(234)-10),M*(s.sqrt(234)+10)]:
        ms=[mass**2+soft+B*g*mass,mass**2+soft-B*g*mass]
        st2+=2*sum(ms)-4*mass**2;st4+=2*sum(x*x for x in ms)-4*mass**4
    print('Polonyi c,k:',c,k,'soft:',s.simplify(soft),'B/gm:',s.simplify(B),'Str2:',s.simplify(st2),'Str4:',s.simplify(st4.expand()))
# v1.5 independent local potential expansion and mass eigenvalues.
q,r,alpha,w,a,b,c=s.symbols('q r alpha w a b c',real=True)
W=w+a*q+b*q*q/2+c*q**3/6; Wbar=W.subs(q,r)
K=q*r+(R(1,6)-alpha)*q*q*r*r
# expansion of e^K, g^{-1} and K_q to relevant order only
V=s.Poly(s.expand((1+q*r)*((1-(R(2,3)-4*alpha)*q*r)*(s.diff(W,q)+r*W)*(s.diff(Wbar,r)+q*Wbar)-3*W*Wbar)),q,r)
get=lambda i,j:s.simplify(V.coeff_monomial(q**i*r**j))
assert s.simplify(get(1,0)-a*(b-2*w))==0
assert s.simplify(2*get(2,0)-(a*c-b*w))==0
assert s.simplify(get(1,1).subs(b,2*w)-(2*w*w-(R(2,3)-4*alpha)*a*a))==0
A=s.sqrt(2)/12
print('No-scale alpha:',s.N(A,15),'Str2/g^2:',s.simplify(24*A-4),'Str4/g^4:',s.simplify(288*A*A-4),'finite CW/g^4:',s.N(s.log(2)/(32*s.pi**2),15))
# Independent metric-sign test using modular theta constants.
def j(tau):
    z=mp.exp(mp.pi*1j*tau); l=(mp.jtheta(2,0,z)/mp.jtheta(3,0,z))**4
    return 256*(1-l+l*l)**3/(l*l*(1-l)**2)
for D in [3,37,137]:
    y0=mp.sqrt(D); tau0=1j*y0; j0=j(tau0); jq=mp.diff(j,tau0)*2j*y0/mp.sqrt(3)
    J=lambda tau:(j(tau)-j0)/jq
    tau=1j*(y0+1); y=tau.imag; g0=3/(4*y*y)
    metric=g0-4*mp.sqrt(2)/12*abs(J(tau)*mp.diff(J,tau))**2
    assert metric<0
    print('D=',D,'metric/base metric at Im tau=sqrt(D)+1:',mp.nstr(metric/g0,14))
print('Independent checks passed; full diagrams, full corpus and duplicate file not independently rederived/available.')
