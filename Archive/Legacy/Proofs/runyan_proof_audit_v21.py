"""Independent finite checks for v2.1R. Checks support, not replace, proofs."""
from itertools import combinations, product
from fractions import Fraction as F
from math import gcd
import mpmath as mp
import sympy as s

# 2-adic cylinders: each length-k word determines exactly one residue mod 2^k.
for k in range(1,11):
    N=2**k
    words=[]
    for n in range(N):
        x=n; w=[]
        for _ in range(k):
            b=x%2; w.append(b); x=(3*x+1)//2 if b else x//2
        words.append(tuple(w))
    assert len(set(words))==N
print('Parity cylinder bijection: k=1..10 passed.')
# Exact Pauli determinant, affine commutator (independent symbolic evaluation).
t,x,y,z,q=s.symbols('t x y z q', real=True)
X=s.Matrix([[t+z,x-s.I*y],[x+s.I*y,t-z]])
assert s.expand(X.det())==t*t-x*x-y*y-z*z
C=2*((2*((q*x+1)/2/2)-1)/q)
assert s.simplify(C-x+1/q)==0
print('Hermitian determinant and general odd-multiplier affine commutator: exact.')
for q in (3,5,7,9):
    for k in range(1,13):
        N=2**k; step=-pow(q,-1,N)%N
        assert len({j*step%N for j in range(N)})==N
print('Cyclic orbit checks: q=3,5,7,9; k=1..12 passed.')
# Homology H_3(T^6,Z) exterior basis in coordinate order x1,y1,x2,y2,x3,y3.
B=list(combinations(range(6),3)); n=len(B)
def wedge_sign(a,b):
    if set(a)&set(b): return 0
    return (-1)**sum(i>j for i in a for j in b)
J=s.Matrix(n,n,lambda i,j:wedge_sign(B[i],B[j]))
assert J.T==-J and J.det()==1
# Independent radical coefficients of omega wedge each integral coordinate 1-form.
rows=[]
for i in range(3):
    for a in range(6):
        triple=(2*i,2*i+1,a)
        if len(set(triple))<3: continue
        row=[0]*n; row[B.index(tuple(sorted(triple)))]=(-1)**sum(triple[j]>triple[l] for j in range(3) for l in range(j+1,3)); rows.append(row)
L=s.Matrix(rows)
assert L.rank()==12
# Independent radical coefficients of Im Omega: one row for each odd y count.
for bits in product((0,1),repeat=3):
    if sum(bits)%2:
        row=[0]*n; row[B.index(tuple(2*i+bits[i] for i in range(3)))]=(-1 if sum(bits)==3 else 1); rows.append(row)
A=s.Matrix(rows); K=s.Matrix.hstack(*A.nullspace())
assert A.rank()==16 and K.shape==(20,4) and K.T*J*K==s.zeros(4)
labels=['x1','y1','x2','y2','x3','y3']
print('H3 rank:',n,'intersection determinant:',J.det())
print('Lagrangian constraints rank:',L.rank(),'combined rank:',A.rank(),'kernel rank:',K.cols)
print('Kernel basis:',[','.join(labels[j] for j in B[next(i for i in range(n) if K[i,c])]) for c in range(K.cols)])
print('Restricted pairing:',K.T*J*K)
# Exact primitive signed factorized triples, phase-real and phase-positive.
pairs=[(a,b) for a,b in product(range(-2,3),repeat=2) if gcd(a,b)==1]
real=pos=0
for ps in product(pairs,repeat=3):
    (a,b),(c,d),(e,f)=ps
    ok=(b*c*e==a*d*e==a*c*f==b*d*f==0)
    axis=all(i*j==0 for i,j in ps) and sum(i==0 for i,j in ps)%2==0
    assert ok==axis
    if ok:
        real+=1
        sign=(-1)**(sum(i==0 for i,j in ps)//2)
        for i,j in ps: sign*=i or j
        pos+=sign>0
print('Factorized signed triples:',len(pairs)**3,'phase-real:',real,'phase-zero positive:',pos)
# High precision finite sums and asymptotics (avoids cancellation in float).
mp.mp.dps=70
print('N     closed renormalized       open renormalized')
for N in (4,8,16,32,64,128,256,512,1024):
    ec=N*mp.cot(mp.pi/(2*N))-2*N*N/mp.pi
    eo=N/2*mp.cot(mp.pi/(4*N))-2*N*N/mp.pi
    dc=N*sum(mp.sin(mp.pi*p/N) for p in range(1,N))-2*N*N/mp.pi
    do=N*sum(mp.sin(mp.pi*p/(2*N)) for p in range(1,N))-2*N*N/mp.pi+mp.mpf(N)/2
    assert abs(ec-dc)<mp.mpf('1e-60') and abs(eo-do)<mp.mpf('1e-60')
    print(f'{N:4}  {mp.nstr(ec,17):>21}  {mp.nstr(eo,17):>21}')
print('Limits:',mp.nstr(-mp.pi/6,20),mp.nstr(-mp.pi/24,20))
assert abs(ec+mp.pi/6)<mp.mpf('1e-7') and abs(eo+mp.pi/24)<mp.mpf('1e-8')
print('All assertions passed.')
