"""One-loop radiative consistency audit of CR common action.
Requires mpmath and sympy; no experimental inputs. A single Majorana eigenmode,
not the full model. Finite matching prescription: MS-bar, mu=m(tau0), no
additional finite modulus-dependent counterterm at that scale in this test.
Run: python runyan_quantum_action_v02.py
"""
import mpmath as mp
import sympy as sp
from runyan_cm_hierarchy import forms, jfun, classpoly

# A rank-one canonical Majorana texture has one nonzero singular value M F(tau).
def F(tau):
    return 3*tau.imag**2*sum(abs(z)**2 for z in forms(tau))

def reduce_tau(tau):
    for _ in range(100):
        tau -= mp.nint(tau.real)
        if abs(tau)>=1: return tau
        tau=-1/tau
    raise RuntimeError('modular reduction failed')

# Symbolic CW differentiation and one-loop explicit scale running.
m,mu=sp.symbols('m mu',positive=True)
V=-m**4/(32*sp.pi**2)*(sp.log(m*m/(mu*mu))-sp.Rational(3,2))
assert sp.simplify(sp.diff(V,m)+m**3/(8*sp.pi**2)*(sp.log(m*m/(mu*mu))-1))==0
assert sp.simplify(mu*sp.diff(V,mu)-m**4/(16*sp.pi**2))==0
print('One Majorana degree pair: dV1/dln(mu)=+m^4/(16 pi^2).')
print('Counterterm beta at fixed background and mass function = -m^4/(16 pi^2).')
print('If Vtree=c M^4 F^4+..., beta_c=-1/(16 pi^2) for this loop alone.')
print('F~3 y^2 at cusp; original bounded class-polynomial potentials cannot absorb F^4 running.')
mp.mp.dps=85
# directly check S,T without modular reduction at points where q series converge
for z in [mp.mpc('.23','1.17'),mp.mpc('-.42','.96'),mp.mpc('.12','2.4')]:
    assert abs(F(-1/z)/F(z)-1)<mp.mpf('1e-75')
    assert abs(F(z+1)/F(z)-1)<mp.mpf('1e-75')
print('F modular invariant: direct numerical S,T checks passed.')

def fmt(x):return mp.nstr(x,13)
print('D | m*/M | k=d ln m/d ln y | f^2 m_phi,tree^2/A | shift coeff (delta ln y / epsilon) | linear shift (epsilon=.01) | numerical local shift')
for D in (3,37,137):
    y0=mp.sqrt(D); tau0=mp.j*y0
    coeff,e=classpoly(D,180); coeff2,_=classpoly(D,260); assert coeff==coeff2
    h=len(coeff)-1; j0=jfun(tau0); jp=mp.diff(jfun,tau0)
    Hp=mp.polyval([i*coeff[i] for i in range(h,0,-1)],j0)
    C=2*y0**2*abs(Hp*jp)**2/(1+abs(j0)**2)**h
    def mass(x): return F(mp.j*y0*mp.exp(x))
    M0=mass(0)
    k=mp.diff(lambda x: mp.log(mass(x)),0)
    # second derivative via analytic H'(j) and independent direct potential differentiation
    def tree(x):
        j=jfun(mp.j*y0*mp.exp(x))
        return abs(mp.polyval(coeff[::-1],j))**2/(1+abs(j)**2)**h
    assert abs(mp.diff(tree,0,2)/C-1)<mp.mpf('1e-65')
    # real x=ln(y/y0), epsilon=m*^4/A, fixed mu=m*.
    eps=mp.mpf('.01')
    def loop(x):
        r=mass(x)/M0
        return -eps*r**4/(32*mp.pi**2)*(2*mp.log(r)-mp.mpf('1.5'))
    slope=mp.diff(loop,0)
    assert abs(slope-eps*k/(8*mp.pi**2))<mp.mpf('1e-75')
    shift_coeff=-k/(8*mp.pi**2*C)
    dx=eps*shift_coeff
    potential=lambda x:tree(x)+loop(x)
    root=mp.findroot(lambda x:mp.diff(potential,x),(dx,0))
    assert mp.diff(potential,root,2)>0 and abs(root/dx-1)<mp.mpf('.01')
    # CP: real-part derivative vanishes at imaginary-axis point in this real-coupling test
    assert abs(mp.diff(lambda u:F(u+tau0),0))<mp.mpf('1e-75')
    print(' | '.join(map(str,[D,*map(fmt,[M0,k,C,shift_coeff,dx,root])])))
print('All assertions passed. The shift is prescription-dependent; allowed finite counterterms can change it.')
print('This rank-one test retains two massless sterile modes if used as a sterile-neutrino mass matrix; it does not justify integrating all three out.')
print('No full RG flow, UV completion, realistic masses, or cosmological constant prediction.')
