#!/usr/bin/env python3
"""Exact Collatz residue certificates and a tilted 3-adic random operator.
No assertion of a universal Collatz proof. Python standard library only.
"""
from fractions import Fraction as F
from math import log, sqrt
from collections import defaultdict

def T(n): return (3*n+1)//2 if n&1 else n//2

def first_descent(n, limit=100000):
    x=n
    for k in range(1,limit+1):
        x=T(x)
        if x<n: return k
    return None

def tree(K):
    # (residue, odd multiplier, offset) for words not yet coefficient-contracting
    frontier=[(0,1,0)]
    exceptions=[]; certs=0; print('k, survivor_classes, fraction, new_certificates, finite_exceptions')
    for k in range(1,K+1):
        old=1<<(k-1); mod=old*2; nxt=[]; new=0; exc=0
        for r,p,c in frontier:
            y=(p*r+c)//old
            assert (p*r+c)%old==0
            for bit in (0,1):
                R=r+bit*old; b=(y+bit*p)&1
                P,C=(3*p,3*c+old) if b else (p,c)
                assert (P*R+C)%mod==0
                if P<mod:
                    new+=1
                    # exceptional positive seeds n>1 for which strict inequality fails
                    lo=R if R>=2 else R+mod
                    if lo<=C//(mod-P):
                        for n in range(lo,C//(mod-P)+1,mod):
                            assert (P*n+C)//mod>=n
                            exceptions.append((k,n)); exc+=1
                else: nxt.append((R,P,C))
        certs+=new; frontier=nxt
        if k in (1,2,3,4,5,10,15,20,K):
            print(k,len(nxt),f'{len(nxt)/mod:.12f}',new,exc)
    print('prefix certificates:',certs,'exception seeds:',len(exceptions),'unique:',len(set(n for k,n in exceptions)))
    assert all(first_descent(n) is not None for k,n in exceptions)
    print('all finite exceptions descended:',len(exceptions))
    if exceptions: print('exception seeds and actual descent:',[(k,n,first_descent(n)) for k,n in exceptions[:20]])
    print('smallest positive unresolved residue representative >1:',min(r if r>=2 else r+(1<<K) for r,p,c in frontier))
    print('seed 27 actual shortcut first descent:',first_descent(27))
    print('Bernoulli seed actual shortcut first descent:',first_descent(305065927))
    return len(frontier)

def survivor_dp(K):
    d={0:1}
    for k in range(1,K+1):
        nxt=defaultdict(int)
        for m,N in d.items():
            for j in (m,m+1):
                if 3**j>=2**k: nxt[j]+=N
        d=nxt
    return sum(d.values())

def crt_check(K,B):
    mod3=3**B
    for n in range(1<<K):
        p,c=1,0; y=n
        for j in range(K):
            if y&1:p,c=3*p,3*c+(1<<j)
            y=T(y)
        assert 2**K*y==p*n+c
        # lift into each initial residue mod 3^B; endpoint determined mod p*3^B
        for a in range(mod3):
            N=n+(1<<K)*((a-n)*pow(1<<K,-1,mod3)%mod3)
            Y=(p*N+c)//(1<<K)
            assert (p*N+c)%(1<<K)==0
            assert Y%(p*mod3)==(p*a+c)*pow(1<<K,-1,p*mod3)%(p*mod3)
    print('CRT lifts checked:',(1<<K)*mod3)

def matrix(b):
    N=3**b; L=2*3**(b-1)
    # q=0 weights sum over geometric tail by exponent residue modulo L
    weights=[F(2**(L-a),2**L-1) for a in range(1,L+1)]
    invs=[pow(2,-a,N) for a in range(1,L+1)]
    P=[[F(0) for _ in range(N)] for _ in range(N)]
    for x in range(N):
        for w,i in zip(weights,invs):P[x][((3*x+1)*i)%N]+=w
        assert sum(P[x])==1
    return P

def matmul(A,B):
    N=len(A); C=[[F(0) for _ in range(N)] for _ in range(N)]
    for i,row in enumerate(A):
        for k,a in enumerate(row):
            if a:
                for j,b in enumerate(B[k]):
                    if b:C[i][j]+=a*b
    return C

def random_operator():
    for b in range(1,4):
        P=matrix(b); Q=P
        for _ in range(1,b): Q=matmul(Q,P)
        assert all(r==Q[0] for r in Q)
        pi=Q[0]; assert [sum(pi[i]*P[i][j] for i in range(len(pi))) for j in range(len(pi))]==pi
        print('3-adic modulus',3**b,'exact rank-one power',b,'stationary mod3',[str(sum(pi[j] for j in range(r,len(pi),3))) for r in range(3)])
    q=log(log(3)/log(1.5),2)-1
    for t in (0,q,.5,1): print('tilt',t,'spectral radius',3**t/(2**(1+t)-1))
    # Finite size uniform bound for expectation at q=1/2, random exponent model
    print('random-model contraction factor at n>=3, q=1/2:',sqrt(3+1/3)/(2**1.5-1))

if __name__=='__main__':
    K=20
    print('EXACT DESCENT CERTIFICATE TREE')
    a=tree(K); assert a==survivor_dp(K)
    for k in (30,50,100,200,500):
        a=survivor_dp(k); print('DP depth',k,'survivors',a,'fraction',float(F(a,2**k)))
    print('\nCRT COMPATIBILITY'); crt_check(9,3)
    print('\n3-ADIC RANDOM OPERATOR'); random_operator()
    print('\nALL-ODD OBSTRUCTION')
    for k in (1,5,10,20):
        # same residue -1 mod 2^4*3^3 throughout k steps
        n=2**(k+4)*3**3-1; y=n
        for j in range(k):
            assert y%432==431 and y&1
            y=T(y); assert y>n
        assert y==3**k*2**4*3**3-1 and y%432==431
        print(k,'seed',n,'last',y)
    print('All implemented assertions passed.')
