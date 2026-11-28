"""Physical spinor selective cancellation benchmark on S^3 x S^1.
Free Euclidean fields on smooth prescribed product metrics, NOT CDT simulation.
Python 3, NumPy, SciPy. Units E_UV=1, proper-time cutoff t>=1.
References: Vassilevich hep-th/0306138; Camporesi/Higuchi gr-qc/9505009.
"""
import math
import numpy as np
from scipy.integrate import quad
from scipy.special import exp1

PI=math.pi
M=.01
masses=M*np.array([math.sqrt(234)-10,math.sqrt(234)+10])
assert np.isclose(np.prod(masses),134*M*M)
I=np.exp(-masses**2)-masses**2*exp1(masses**2)

def traces(t,r,beta,xi=0,twist=0,tail=80):
    """Heat traces, without common mass. 4 real scalar degrees and 4-spinor.
    beta is circle circumference; twist 0 periodic or .5 antiperiodic fermion.
    tail is exponential cutoff, not certified interval arithmetic.
    """
    u=t/r**2
    j=np.arange(1,max(3,math.ceil(math.sqrt(tail/u))+3),dtype=float)
    scalar=np.sum(j*j*np.exp(-u*(j*j-1+6*xi)))
    k=j+.5
    spin=4*np.sum((k*k-.25)*np.exp(-u*k*k))
    v=t*(2*PI/beta)**2
    n=np.arange(-max(2,math.ceil(math.sqrt(tail/v))+2),max(2,math.ceil(math.sqrt(tail/v))+2)+1,dtype=float)
    c0=np.sum(np.exp(-v*n*n)); cf=np.sum(np.exp(-v*(n+twist)**2))
    return 4*scalar*c0,spin*cf

def normalized(t,r,beta,xi,twist=0,tail=80):
    vol=2*PI**2*r**3*beta
    b,f=traces(t,r,beta,xi,twist,tail)
    return (4*PI*t)**2/vol*(b-f)

def action(r,beta,xi,twist=0,tail=80):
    end=math.log(tail/min(masses)**2)
    def integrand(z):
        t=math.exp(z)
        b,f=traces(t,r,beta,xi,twist,tail)
        return -.5*(b-f)*np.exp(-t*masses**2).sum()
    return quad(integrand,0,end,epsabs=2e-8,epsrel=2e-10,limit=200)[0]

print('SELECTIVE VACUUM CANCELLATION v0.5: smooth S3 x S1 benchmark')
print('M/cutoff=',M,'masses/cutoff=',masses,'product=',np.prod(masses))
print('No bare gravitational term assumed; cutoff and mass scale not predicted.')
print('Heat expansion normalized: a0=0, a1=6(1-4xi)/r^2, a2=2(1-6xi)^2/r^4 on this background.')
print('General integrated a2 density (up to total derivative): ((15-240xi+720xi^2)R^2+15 Riem^2)/360.')
print('xi, u=t/r^2, extracted a1*r^2, extracted a2*r^4')
for xi in [0,1/6,1/4,1/3]:
    for u in [.01,.003,.001,.0003]:
        h=normalized(u,1,2*PI,xi)
        a1=6*(1-4*xi); a2=2*(1-6*xi)**2
        print(f'{xi:.9f} {u:.4g} {h/u:.10f} {(h-a1*u)/u**2:.10f}')
    assert abs(h/u-a1)<.001
    assert abs((h-a1*u)/u**2-a2)<.002
    ha=normalized(u,1,2*PI,xi,.5)
    assert abs(ha-h)<1e-12
print('Both circle spin structures give the same local UV coefficients.')
print('\nxi, G_ind E_UV^2 (signed; infinity means no induced R term)')
for xi in [0,1/6,1/4,1/3]:
    c=1-4*xi
    print(f'{xi:.9f}',2*PI/(c*sum(I)) if c else math.inf)
print('\nPeriodic spin structure; beta=2*pi*r, xi=0:')
print('r, Gamma, -Gamma/int R, local predicted coefficient, rel error')
expected=sum(I)/(32*PI**2)
for r in [4,8,16,32,64,128]:
    beta=2*PI*r; intR=2*PI**2*r**3*beta*6/r**2
    g=action(r,beta,0); coeff=-g/intR
    print(f'{r:3d} {g:.10f} {coeff:.12f} {expected:.12f} {abs(coeff/expected-1):.8g}')
assert abs(coeff/expected-1)<.001
print('\nSpin-structure difference at fixed r=8 (finite IR / global effect):')
print('beta/r, Gamma(periodic), Gamma(antiperiodic), difference')
for rat in [.5,1,2,4,2*PI]:
    b=8*rat; gp=action(8,b,0); ga=action(8,b,0,.5)
    print(f'{rat:.9f} {gp:.10f} {ga:.10f} {ga-gp:.10f}')
    assert ga<gp
# Cutoff and tail convergence at representative background.
g1=action(16,32,0,tail=60); g2=action(16,32,0,tail=100)
print('Numerical tail-cutoff difference:',abs(g1-g2)); assert abs(g1-g2)<1e-6
print('\nAt xi=1/6, the curvature-squared coefficient vanishes on S3xS1 but not S4: a2*r^4=-1 on S4.')
print('At xi=1/4, a1=0 yet a2*r^4=1/2 on S3xS1. No universal complete spectral cancellation.')
print('All assertions passed. No dynamical triangulations, quantum gravitons, interacting SUSY, or physical Lambda prediction.')

# Independent product-sphere and round-sphere spectral checks of a2.
print('\nIndependent curved-space a2 checks: xi=1/6; u, S4, S2xS2')
xi=1/6
for u in [.01,.003,.001,.0003]:
    l=np.arange(math.ceil(math.sqrt(80/u))+5,dtype=float)
    scalar4=np.sum((l+1)*(l+2)*(2*l+3)/6*np.exp(-u*(l*(l+3)+12*xi)))
    spin4=np.sum(4*(l+1)*(l+2)*(l+3)/3*np.exp(-u*(l+2)**2))
    h4=6*u*u*(4*scalar4-spin4)
    s2=np.sum((2*l+1)*np.exp(-u*l*(l+1)))
    f2=np.sum(4*(l+1)*np.exp(-u*(l+1)**2))
    h22=u*u*(4*s2*s2*np.exp(-4*xi*u)-f2*f2)
    c4=(h4-4*u)/u**2
    c22=(h22-(4/3)*u)/u**2
    print(f'{u:.4g} {c4:.10f} {c22:.10f}')
assert abs(c4+1)<.002 and abs(c22-1/9)<.002
print('Independent checks passed: conformal scalar coupling does not remove universal curvature-squared terms.')
