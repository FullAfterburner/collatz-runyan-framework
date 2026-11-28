"""Arithmetic endpoint algebra and harmonic-chain benchmark (v2.0).
Model inputs: real time, quadratic nearest-neighbor Hamiltonian, L=c=hbar=1.
No fundamental string or gauge dynamics is claimed.
"""
from fractions import Fraction as F
import numpy as np
from math import pi, sqrt, tan

def comp(g,h): return g[0]*h[0],g[0]*h[1]+g[1]
def inv(g): return 1/g[0],-g[1]/g[0]
def comm(g,h): return comp(comp(comp(g,h),inv(g)),inv(h))
for a in (3,5,7):
    C=comm((F(2),F(0)),(F(2,a),F(-1,a)))
    assert C==(1,F(-1,a))
    print('multiplier',a,'affine commutator',C)
    for k in range(1,11):
        N=2**k; step=-pow(a,-1,N)%N
        assert len({j*step%N for j in range(N)})==N
print('\nPeriodic arithmetic Laplacian: direct matrix vs Fourier')
for N in (8,16,32,64,128,256):
    step=-pow(3,-1,N)%N
    P=np.eye(N)[(np.arange(N)+step)%N]
    L=2*np.eye(N)-P-P.T
    exact=np.sort(4*np.sin(pi*np.arange(N)/N)**2)
    err=np.max(np.abs(np.linalg.eigvalsh(L)-exact))
    assert err<1e-12
    print(f'N={N:4} step={step:4} max error={err:.3e}')
print('\nContinuum benchmark: L=c=hbar=1; p=1; vacuum energy subtract bulk (and open boundary)')
for N in (16,32,64,128,256,512,1024):
    wc=2*N*np.sin(pi/N); wo=2*N*np.sin(pi/(2*N))
    ec=N/tan(pi/(2*N))-2*N*N/pi
    eo=N/2*(1/tan(pi/(4*N))-1)-2*N*N/pi+N/2
    ec_sum=N*np.sin(pi*np.arange(1,N)/N).sum()-2*N*N/pi
    eo_sum=N*np.sin(pi*np.arange(1,N)/(2*N)).sum()-2*N*N/pi+N/2
    assert abs(ec_sum-ec)<1e-8 and abs(eo_sum-eo)<1e-8
    print(f'N={N:4} omegaC/(2pi)={wc/(2*pi):.10f} omegaO/pi={wo/pi:.10f} EC={ec:.10f} EO={eo:.10f}')
assert abs(ec+pi/6)<1e-6 and abs(eo+pi/24)<1e-6
print('\nMixed translation benchmark: low-mode speed ratio sqrt(1+a^2), assuming equal springs')
for a in (3,5,7):
    N=1024
    w=2*N*sqrt(np.sin(pi/N)**2+np.sin(a*pi/N)**2)
    print(f'a={a} finite ratio={w/(2*pi):.9f} limit={sqrt(1+a*a):.9f}')
print('\nMatrix endpoint mass operator: A tensor identity, ad_A^2')
A=np.array([[3.,sqrt(185)],[sqrt(185),17.]])
for k in (1,2,3,4):
    d=2**(k-1); N=2*d; X=np.kron(A,np.eye(d))
    C=np.kron(np.eye(N),X)-np.kron(X.T,np.eye(N))
    eig=np.linalg.eigvalsh(C@C)
    expected=np.repeat([0.,936.],2*d*d)
    assert np.max(np.abs(eig-expected))<1e-9
    print(f'k={k} N={N} zero={2*d*d} massive={2*d*d} mass2/M2=936')
print('\nArithmetic torus calibration test: squarefree independent D=3,37,137')
# Im product(n_i+i sqrt(D_i) m_i) has independent basis sqrt(D_i), sqrt(D1 D2 D3).
# Nonzero primitive pairs with each coefficient zero imply axis-aligned cycles with even number of vertical axes.
from itertools import product
pairs=[(n,m) for n,m in product(range(-2,3),repeat=2) if (n or m) and __import__('math').gcd(n,m)==1]
count=0
for (n1,m1),(n2,m2),(n3,m3) in product(pairs,repeat=3):
    zero=(m1*n2*n3==n1*m2*n3==n1*n2*m3==m1*m2*m3==0)
    axis=all(n*m==0 for n,m in ((n1,m1),(n2,m2),(n3,m3))) and sum(n==0 for n in (n1,n2,n3))%2==0
    assert zero==axis
    count+=zero
print('primitive signed triples in [-2,2]:',len(pairs)**3,'phase-real:',count)
print('All assertions passed.')
