"""Arithmetic induced-gravity benchmark, not a full microscopic gravity theory.
Requires numpy, scipy. All quantities in cutoff units unless noted.
"""
import math
import numpy as np
from scipy.special import exp1
from scipy.integrate import quad

# Original weighted symmetric arithmetic operator; physical masses are singular values.
A=np.array([[3., math.sqrt(185.)],[math.sqrt(185.),17.]])
mu=np.sort(np.abs(np.linalg.eigvalsh(A)))
assert np.allclose(mu,[math.sqrt(234)-10,math.sqrt(234)+10])
# Illustrative choice, NOT determined by arithmetic.
M_over_cutoff=.01
masses=mu*M_over_cutoff

def heat_supertrace_s4(u):
    """4 minimally coupled real scalar heat traces minus 1 Dirac trace on unit S^4.
    u=t/r^2. Traces include both Dirac signs. Common mass factored out.
    Exponential tail cutoff exp(-80); numerical, not interval certified.
    """
    l=np.arange(max(12,int(math.ceil(math.sqrt(80/u)))+5),dtype=float)
    scalar=(l+1)*(l+2)*(2*l+3)/6
    spinor=4*(l+1)*(l+2)*(l+3)/3
    return float(np.sum(4*scalar*np.exp(-u*l*(l+3))-spinor*np.exp(-u*(l+2)**2)))

# For proper-time cutoff t>=1, I(m) = int dt/t^2 exp(-m^2 t).
I=np.exp(-masses**2)-masses**2*exp1(masses**2)
G=2*math.pi/sum(I)
print('Arithmetic eigenvalue magnitudes:',mu)
print('Chosen M/cutoff:',M_over_cutoff)
print('Masses/cutoff:',masses)
print('Curvature integrals / cutoff^2:',I)
print('Induced G * cutoff^2:',G)
print('Flat vacuum trace: 4 real scalars - 4 Dirac components = 0 for each mass.')
print('\nS^4 test: u * supertrace should approach 2, not zero:')
for u in [.1,.03,.01,.003,.001,.0003]:
    print(f'{u:.4g} {u*heat_supertrace_s4(u):.12f}')
assert abs(.0003*heat_supertrace_s4(.0003)-2)<.001

# On S^4, induced action Gamma=-1/2 int dt/t sum exp(-tm^2)*K(t/r^2).
# Substitution t=e^z, truncate where smallest mass suppression is exp(-80).
print('\nRadius in cutoff lengths | Gamma | -Gamma/r^2 | predicted limiting sum I')
for r in [2,4,8,16,32,64]:
    end=math.log(80/min(masses)**2)
    def f(z):
        t=math.exp(z)
        return -.5*float(np.exp(-t*masses**2).sum())*heat_supertrace_s4(t/r**2)
    gamma,err=quad(f,0,end,epsabs=1e-8,epsrel=1e-9,limit=200)
    print(f'{r:3} {gamma:16.8f} {-gamma/r**2:.10f} {sum(I):.10f} (quadrature error {err:.2g})')
assert abs(-gamma/r**2-sum(I))<.01

# Separate fixed-flat-lattice Wilson kernel benchmark (massless, Wilson r=1).
# D_W^dag D_W = [sum sin^2(ap)+ (sum(1-cos(ap)))^2]/a^2 * identity.
print('\nFlat Wilson kernel: a, lambda(p=1)/p^2, error')
for a in [.2,.1,.05,.025]:
    val=(math.sin(a)**2+(1-math.cos(a))**2)/a**2
    print(f'{a:.3f} {val:.12f} {abs(1-val):.6g}')
from itertools import product
corners=[]
for b in product([0,1],repeat=4):
    w=(2*sum(b))**2
    corners.append(w)
assert corners.count(0)==1
print('Wilson massless Brillouin corners: 1 zero, 15 lifted (not a chiral gauge theory).')
print('Scope: flat lattice benchmark and round-sphere continuum heat kernels only; no dynamical triangulation or Lorentzian continuum proof.')
