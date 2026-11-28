"""Arithmetic coupling audit. No experimental values used to construct couplings.
Requires numpy, sympy; uses forms and tensors from runyan_modular_yukawa.py.
Run: python runyan_arithmetic_couplings.py
"""
import numpy as np
import sympy as s
from runyan_modular_yukawa import forms, weight4
from itertools import product

# Verify Pell matrices and their finite projective image.
I=(1,0,0,1)
def canon(A):
    A=tuple(int(v)%3 for v in A)
    return min(A,tuple(-v%3 for v in A))
def mul(A,B):
    return canon((np.array(A).reshape(2,2)@np.array(B).reshape(2,2)).ravel())
gens=[]
for D,x,y in [(3,2,1),(37,73,12),(137,6083073,519712)]:
    assert x*x-D*y*y==1
    gens.append(canon((x,D*y,y,x)))
    print('Pell D, trace, projective mod 3:',D,2*x,gens[-1])
G={canon(I)}
while True:
    H=G|{mul(a,b) for a,b in product(G,gens)}
    if G==H: break
    G=H
assert len(G)==12
print('Projective group size:',len(G))

# Symbolic fixed point forms; common factor Y1(i)^2 removed.
r=s.sqrt(3); p=s.sqrt(185); w=s.sqrt(234)
y=s.Matrix([1,1-r,r-2]); Y1,Y2,Y3=y
F=s.Matrix([Y1**2-Y2*Y3,Y3**2-Y1*Y2,Y2**2-Y1*Y3]).applyfunc(s.simplify)
A=s.simplify(Y1**2+2*Y2*Y3); B=s.simplify(Y3**2+2*Y1*Y2)
f=F[0]
assert F==s.Matrix([f,f,f]) and s.simplify(A-r*f)==0 and s.simplify(B+r*f)==0
print('At i: F/f=(1,1,1), A/f=sqrt(3), B/f=-sqrt(3)')
P=s.Matrix([[1,0,0],[0,0,1],[0,1,0]])
P2=s.Matrix([[0,0,1],[0,1,0],[1,0,0]])
E=s.Matrix([[2/s.sqrt(6),0,1/r],[-1/s.sqrt(6),1/s.sqrt(2),1/r],[-1/s.sqrt(6),-1/s.sqrt(2),1/r]])
assert s.simplify(E.T*E)==s.eye(3)
k,a,b=s.symbols('k a b',real=True)
M=k*(3*s.eye(3)-s.ones(3))+a*P+b*P2
block=s.simplify(E.T*M*E)
print('Exact residual block:'); print(block)
sol=s.solve([3*k-10,a-b/2+7,-r*b/2-p],[k,a,b])
assert s.simplify(block.subs(sol)[:2,:2]-s.Matrix([[3,p],[p,17]]))==s.zeros(2)
ratios=[s.Integer(1),s.simplify(sol[a]/(r*sol[k])),s.simplify(-sol[b]/(r*sol[k]))]
print('Coupling ratios g/g1:',ratios,[float(v) for v in ratios])
m1=w-10;m2=w+10;m3=s.simplify(abs(sol[a]+sol[b]))
print('Dimensionless masses:',[float(v) for v in [m1,m2,m3]])
print('Solar/atmospheric splitting ratio, exact embedding:',float((m2*m2-m1*m1)/(m3*m3-m1*m1)))
# Fixed i + real orthogonal identification gives a^2-ab+b^2=234.
assert s.expand(4*(a*a-a*b+b*b)-(a+b)**2-3*(a-b)**2)==0
bound=s.simplify((m2*m2-m1*m1)/(4*w*w-m1*m1))
print('Orientation-independent lower bound (normal ordering, same pair):',bound,float(bound))
# More general complex symmetric block matching only the two singular values.
complexbound=s.simplify((m2*m2-m1*m1)/(m1*m1+2*m2*m2))
print('Complex-coupling lower bound matching only pair singular values:',float(complexbound))
# Independently evaluate the existing numerical modular forms and ranks.
for D in (1,3,37,137):
    tau=1j*np.sqrt(D)
    tensors=weight4(forms(tau))
    mat=np.column_stack([v.ravel() for v in tensors]); rank=np.linalg.matrix_rank(mat)
    assert rank==3
    print(f'tau=i sqrt({D}): rank={rank}; B/A={tensors[2][0,2]/tensors[1][0,0]:.12g}')
T=weight4(forms(1j)); N=sum(float(g)*v for g,v in zip(ratios,T)); N=N*(10/3)/(T[0][0,0].real/2)
expected=np.array(block.subs(sol)).astype(float)
assert np.allclose(np.array(E).astype(float).T@N@np.array(E).astype(float),expected,atol=1e-12)
print('Numerical weight-four reconstruction: passed')
print('No experimental inputs used. Fixed i, residual basis and matching rule are additional hypotheses.')
