"""Arithmetic twistor and helicity benchmarks. Requires numpy, sympy, scipy, matplotlib.
Free flat-space matter cuts, classical twistor kinematics; no quantum gravity UV claim.
Run from any directory. Optional --figure PATH produces the paper's plot.
"""
import argparse
import sympy as S
import numpy as np
from numpy.linalg import norm
from scipy.special import beta as beta_fn
from scipy.integrate import quad
from math import pi, sqrt

simp=lambda x:S.simplify(S.expand(x))
def zero(M): return all(simp(x)==0 for x in M)
def bracket(a,b): return S.det(S.Matrix.hstack(a,b))
I=S.I
Pell=[(3,2,1,(S.sqrt(6)+S.sqrt(2))/2),(37,73,12,6+S.sqrt(37)),(137,6083073,519712,1744+149*S.sqrt(137))]
X=S.Matrix([[5,1+2*I],[1-2*I,3]])
lam=S.Matrix([1,2+I]); p=lam*lam.conjugate().T
pi0=S.Matrix([2-I,1]); omega=I*X*pi0
print('Exact Pell lifts, determinant, twistor incidence and null separation')
for D,x,y,a in Pell:
    assert x*x-D*y*y==1 and simp(a*a-x-y*S.sqrt(D))==0
    # reciprocal in exact radical form
    ai=S.radsimp(1/a); L=S.diag(a,ai); Linv=S.diag(ai,a)
    Xp=L*X*L.conjugate().T; pip=Linv.conjugate().T*pi0
    assert simp(Xp.det()-X.det())==0
    assert zero(I*Xp*pip-L*omega)
    assert simp(p.det())==0
    # twistor on null-separated lines: choose covector annihilated by p
    cov=S.Matrix([-lam.conjugate()[1],lam.conjugate()[0]])
    assert zero(p*cov) and zero(I*(X+7*p)*cov-I*X*cov)
    print(f'D={D}: spin lift a={a}, rapidity={float(S.log(x+y*S.sqrt(D))):.12g}, checks PASS')
# two-chart Penrose transform, homogeneous degree -6: f=1/(pi_0^5 pi_1)
t=S.symbols('t'); residues=[S.residue(t**k/t,t,0) for k in range(5)]
assert residues==[1,0,0,0,0]
print('Penrose contour spinor components:',residues)
# Complex three-graviton kinematics (all momenta outgoing)
l=[S.Matrix([1,0]),S.Matrix([0,1]),S.Matrix([-1,-1])]; r=[S.Matrix([1,2])]*3
assert zero(sum((a*b.T for a,b in zip(l,r)),S.zeros(2)))
def amp(l): return simp(bracket(l[0],l[1])**6/(bracket(l[1],l[2])**2*bracket(l[2],l[0])**2))
assert amp(l)==1
for D,x,y,a in Pell:
    L=S.diag(a,S.radsimp(1/a)); assert simp(amp([L*v for v in l])-1)==0
sc=[S.Rational(2),S.Rational(3),S.Rational(5)]
assert simp(amp([a*v for a,v in zip(sc,l)])-sc[0]**4*sc[1]**4/sc[2]**4)==0
print('Complex 3-point Einstein amplitude / (kappa/2):',amp(l),'little-group rescaling:',amp([a*v for a,v in zip(sc,l)]))
# Independent exact symbolic trace in standard Minkowski Dirac basis
sig=[S.Matrix([[0,1],[1,0]]),S.Matrix([[0,-I],[I,0]]),S.diag(1,-1)]
g0=S.diag(1,1,-1,-1); g=[g0]+[S.BlockMatrix([[S.zeros(2),a],[-a,S.zeros(2)]]).as_explicit() for a in sig]
e,px,py,pz,m=S.symbols('e px py pz m',real=True); pvec=[px,py,pz]; slash1=e*g[0]-sum((pvec[i]*g[i+1] for i in range(3)),S.zeros(4)); slash2=e*g[0]+sum((pvec[i]*g[i+1] for i in range(3)),S.zeros(4));
for i in range(3):
    for j in range(3):
        tr=S.expand(S.trace((slash1+m*S.eye(4))*g[i+1]*(slash2-m*S.eye(4))*g[j+1]))
        tr=S.expand(tr.subs(m*m,e*e-px*px-py*py-pz*pz))
        assert simp(tr-(8*e*e*int(i==j)-8*pvec[i]*pvec[j]))==0
print('All 9 spatial Dirac spin-sum traces verified exactly.')
# Numerical check arbitrary complex normalized spin-2 polarizations and helicity cuts
rng=np.random.default_rng(20261124)
gn=[np.array(a,dtype=complex) for a in g]; eye=np.eye(4)
max_trace=max_pair=max_cross=0.
eplus=np.array([1,1j,0])/sqrt(2); eminus=eplus.conj(); helic=[np.outer(eplus,eplus),np.outer(eminus,eminus)]
for k in range(300):
    m0=rng.uniform(.1,2); p0=rng.normal(size=3); E=np.sqrt(m0*m0+p0@p0); s=4*E*E
    a=E*gn[0]-sum(p0[i]*gn[i+1] for i in range(3)); b=E*gn[0]+sum(p0[i]*gn[i+1] for i in range(3));
    trace=np.array([[np.trace((a+m0*eye)@gn[i+1]@(b-m0*eye)@gn[j+1]) for j in range(3)] for i in range(3)])
    target=2*s*np.eye(3)-8*np.outer(p0,p0)
    max_trace=max(max_trace,norm(trace-target)/max(norm(target),1))
    def random_pol():
        q=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));q=(q+q.T)/2;q-=np.trace(q)*np.eye(3)/3;return q/norm(q)
    def cut(A,B):
        # four real species, each with identical-particle phase-space factor 1/2
        u=A@p0;v=B@p0
        scalar=8*(p0@u)*(p0@v).conjugate(); fermion=u@trace@v.conj()
        return scalar+fermion, 2*s*(u@v.conj())
    for A,B in [(random_pol(),random_pol()),(helic[0],helic[0]),(helic[0],helic[1])]:
        val,ref=cut(A,B);max_pair=max(max_pair,abs(val-ref)/max(2*s*(p0@p0),1))
    v,_=cut(*helic);max_cross=max(max_cross,abs(v)/max(2*s*(p0@p0),1))
assert max(max_trace,max_pair,max_cross)<1e-12
print(f'300 seeded physical momenta: trace residual={max_trace:.3e}, paired cut residual={max_pair:.3e}, opposite-projection residual={max_cross:.3e}')
# Angular integral and moment expansion
c,beta=S.symbols('c beta',real=True); ss=S.symbols('s',positive=True); pp2=ss*beta**2/4
BS=2*pp2**2*(1-c*c)**2; FS=ss*pp2*(1-c*c)-BS
bs=S.integrate(BS,(c,-1,1))/2; fs=S.integrate(FS,(c,-1,1))/2
assert simp(bs/(bs+fs)-2*beta**2/5)==0
assert simp(bs+fs-ss**2*beta**2/6)==0
print('Angular integrated boson fraction:',simp(bs/(bs+fs)))
# Dispersion moments H(z,m) = sum (-1)^(n-1) z^n B(n,5/2)/(4m^2)^n
q=.01; masses=q*np.array([sqrt(234)-10,sqrt(234)+10]); coeff=1/(384*pi*pi)
print('masses:',masses,'pair threshold ratio:',masses[1]/masses[0])
for n in range(1,5):
    exact=S.simplify(S.beta(n,S.Rational(5,2)).expand(func=True)/4**n)
    # rationalize beta integral directly
    exact=S.integrate(2*t**4*(1-t*t)**(n-1),(t,0,1))/4**n
    print(f'n={n}, moment factor B(n,5/2)/4^n={exact}, total F coefficient={(-1)**(n-1)*coeff*beta_fn(n,2.5)*sum((4*masses*masses)**(-n)):.12g}')
# Check rational recurrence against exact arithmetic roots.
roots=[1/(S.sqrt(234)-10)**2,1/(S.sqrt(234)+10)**2]
seq=[S.Integer(2),S.Rational(668,17956)]
for n in range(2,7): seq.append((668*seq[-1]-seq[-2])/17956)
for n in range(7): assert simp(seq[n]-sum(r**n for r in roots))==0
print('Exact rational inverse-mass moment recurrence verified for n=0,...,6.')
z=.3*4*masses[0]**2
H=lambda z,m:quad(lambda v:2*z*v**4/(4*m*m+z*(1-v*v)),0,1,epsabs=1e-13)[0]
val=coeff*sum(H(z,m) for m in masses)
series=sum((-1)**(n-1)*coeff*beta_fn(n,2.5)*sum((z/(4*masses*masses))**n) for n in range(1,25))
assert abs(val-series)<1e-14
print(f'Dispersive series check z/s_min=0.3: {val:.12g}, abs error={abs(val-series):.3e}')
print('All assertions passed. No interacting graviton loop or UV completion tested.')
parser=argparse.ArgumentParser();parser.add_argument('--figure');args=parser.parse_args()
if args.figure:
    import matplotlib;matplotlib.use('Agg');import matplotlib.pyplot as plt
    fig,ax=plt.subplots(1,2,figsize=(10,3.65),layout='constrained')
    x=np.linspace(-1,1,301);bt=.9;p2=bt**2/4
    B=2*p2**2*(1-x*x)**2;F=p2*(1-x*x)-B
    ax[0].plot(x,B,label='4 real scalars');ax[0].plot(x,F,label='Dirac fermion');ax[0].plot(x,B+F,label='Matched total',lw=2.5,color='black');ax[0].set(xlabel=r'$\cos\theta$',ylabel=r'Cut weight / $s^2$',title=r'Angular response ($\beta=0.9$)');ax[0].legend(frameon=False,fontsize=9);ax[0].grid(alpha=.18)
    en=np.linspace(.001,.9,500)
    for mass,label in zip(masses,['Lower sector','Upper sector']): ax[1].plot(en,np.maximum(0,1-(2*mass/en)**2)**1.5,label=label)
    ax[1].plot(en,sum(np.maximum(0,1-(2*m/en)**2)**1.5 for m in masses),color='black',lw=2.5,label='Total');ax[1].set(xlabel=r'$\sqrt{s}/E_{\rm UV}$',ylabel=r'$384\pi^2\rho_2(s)$',title='Arithmetic pair thresholds');ax[1].legend(frameon=False,fontsize=9);ax[1].grid(alpha=.18)
    fig.savefig(args.figure,bbox_inches='tight')
