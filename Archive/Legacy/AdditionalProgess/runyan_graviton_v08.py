"""Arithmetic matter, vacuum RG and linearized graviton EFT benchmark.
Requires sympy, scipy, mpmath. No full gravitational RG or microscopic geometry.
Conventions: Euclidean Gamma=-P^2 R/2+b C^2; proper-time cutoff E=1.
All bare higher-curvature coefficients set to zero for illustrative matching only.
"""
import sympy as s
import mpmath as mp
from scipy.special import exp1
from math import sqrt,pi,exp
mp.mp.dps=70
# Linearized vacuum Einstein equations at a null momentum in signature -+++.
eta=s.diag(-1,1,1,1); k=s.Matrix([-1,0,0,1]); ku=eta*k
pairs=[(i,j) for i in range(4) for j in range(i,4)]
v=s.symbols('h:10'); h=s.zeros(4)
for (i,j),a in zip(pairs,v):h[i,j]=h[j,i]=a
tr=s.trace(eta*h); k2=(k.T*eta*k)[0]; hk=h*ku
# Overall Fourier sign immaterial for kernel
Ric=(k2*h-k*hk.T-hk*k.T+k*k.T*tr)/2
E=Ric-eta*s.trace(eta*Ric)/2
A=s.linear_eq_to_matrix([E[i,j] for i,j in pairs],v)[0]
xi=s.Matrix(s.symbols('x:4')); gauge=k*xi.T+xi*k.T
G=s.linear_eq_to_matrix([gauge[i,j] for i,j in pairs],list(xi))[0]
plus=s.diag(0,1,-1,0); cross=s.zeros(4);cross[1,2]=cross[2,1]=1
vec=lambda h:s.Matrix([h[i,j] for i,j in pairs])
assert A*G==s.zeros(10,4)
assert A*vec(plus)==s.zeros(10,1) and A*vec(cross)==s.zeros(10,1)
assert A.rank()==4 and G.rank()==4 and G.row_join(vec(plus)).row_join(vec(cross)).rank()==6
print('Null-momentum linearized Einstein equation rank:',A.rank(),'kernel:',10-A.rank(),'gauge rank:',G.rank(),'physical quotient:',10-A.rank()-G.rank())
# Trace anomaly for one 4-real-scalar + Dirac sector in massless UV limit
cS,aS=s.Rational(1,120),s.Rational(1,360)
cF,aF=s.Rational(1,20),s.Rational(11,360)
C=4*cS+cF; AA=4*aS+aF
assert C==s.Rational(1,12) and AA==s.Rational(1,24)
print('UV conformal anomaly (c,a) per sector:',C,AA,'two sectors:',2*C,2*AA)
# dimensionless cutoff integrals and induced coefficients
print('q=M/E, P^2/E^2, b_C, p_formal/E, p_formal/(2*m_light), R^2 derivative expansion ratio at p=m_light/10')
for q in [.001,.01,.03,.1]:
 m=[q*(sqrt(234)-10),q*(sqrt(234)+10)]; xs=[x*x for x in m]
 I=sum(exp(-x)-x*exp1(x) for x in xs); J=sum(exp1(x) for x in xs)
 P2=I/(48*pi*pi); b=-J/(384*pi*pi)
 p=sqrt(P2/(4*abs(b))); ratio=4*abs(b)*(m[0]/10)**2/P2
 print(f'{q:.3g} {P2:.12g} {b:.12g} {p:.12g} {p/(2*m[0]):.12g} {ratio:.12g}')
 assert P2>0 and b<0
# vacuum beta and GW threshold with same archived inputs
v,mh,mw,mz,mt,mX=map(mp.mpf,['246.22','125.25','80.377','91.1876','172.5','500'])
Qsm=mh**4+6*mw**4+3*mz**4-12*mt**4; Q=Qsm+mX**4
P=1/mp.sqrt(8*mp.pi*mp.mpf('6.708e-39')); dark=mp.mpf('2.6e-47')
print('SM fourth moment:',mp.nstr(Qsm,14),'threshold:',mp.nstr((-Qsm)**mp.mpf('.25'),14))
print('Full benchmark Q:',mp.nstr(Q,14),'vacuum beta (fixed masses, MS):',mp.nstr(Q/(32*mp.pi**2),14),'GeV^4')
print('beta / observed rho:',mp.nstr(Q/(32*mp.pi**2*dark),14))
print('Hubble scale H_Lambda [GeV]:',mp.nstr(mp.sqrt(dark/(3*P**2)),14))
# RG improved scale-invariant potential with running couplings
lam,z,bl,bz=s.symbols('lambda zeta beta_lambda beta_zeta',real=True); U=lam/(4*z*z)
bU=s.diff(U,lam)*bl+s.diff(U,z)*bz
assert s.simplify(bU-(bl/(4*z*z)-lam*bz/(2*z**3)))==0
assert s.simplify(bU.subs(lam,0)-bl/(4*z*z))==0
print('dimensionless potential:',U,'RG slope:',bU)
print('All assertions passed. Flat graviton test presupposes a tuned Minkowski background. Anomaly is UV conformal limit, not finite massive trace. No graviton-loop computation, full RG fixed point, or dynamical continuum limit.')
