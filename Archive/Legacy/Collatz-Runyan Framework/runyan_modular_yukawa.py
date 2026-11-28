"""Runyan modular flavor audit: weight-2 no-go and weight-4 extension.
Requires Python 3, numpy, scipy, sympy. No fitted new Yukawa coefficients.
Reference: Feruglio arXiv:1706.08749; Criado & Feruglio arXiv:1807.01125.
Benchmark retained from prior run: NuFIT 6.1 NO, solar 75.37, atm 2521 meV^2.
"""
import numpy as np
import sympy as sp
from scipy.optimize import brentq
from pathlib import Path
from math import sqrt

W=np.exp(2j*np.pi/3)
S=np.array([[-1,2,2],[2,-1,2],[2,2,-1]])/3
T=np.diag([1,W,W**2])
P=np.array([[1,0,0],[0,0,1],[0,1,0]])
P2=np.array([[0,0,1],[0,1,0],[1,0,0]])

def sigma(n):
    return sum(k for k in range(1,n+1) if n%k==0)
SIG=np.array([0]+[sigma(n) for n in range(1,301)])

def forms(tau):
    t=np.exp(2j*np.pi*tau/3)
    a=np.arange(1,301)
    p=t**a
    y1=1+3*np.sum(SIG[a[a%3==0]]*p[a%3==0])-27*np.sum(SIG[a[a%9==0]//9]*p[a%9==0])
    y2=-6*np.sum(SIG[a[a%3==1]]*p[a%3==1])
    y3=-6*np.sum(SIG[a[a%3==2]]*p[a%3==2])
    return np.array([y1,y2,y3])

def texture(y):
    a,b,c=y
    return np.array([[2*a,-c,-b],[-c,2*b,-a],[-b,-a,2*c]])

def weight4(y):
    a,b,c=y
    return texture([a*a-b*c,c*c-a*b,b*b-a*c]), (a*a+2*b*c)*P, (c*c+2*a*b)*P2

def masses(M): return np.sort(np.linalg.svd(M,compute_uv=False))
def res(a,b): return np.max(np.abs(a-b))/max(1,np.max(np.abs(b)))

def main():
    # symbolic proof, no modular-form relation needed
    a,b,c,A,B,C=sp.symbols('a b c A B C')
    M=sp.Matrix([[2*a,-c,-b],[-c,2*b,-a],[-b,-a,2*c]])
    H=M*sp.Matrix([[2*A,-C,-B],[-C,2*B,-A],[-B,-A,2*C]])
    tr=sp.expand(sp.trace(H)); tr2=sp.expand(sp.trace(H*H))
    assert sp.expand(tr-6*(a*A+b*B+c*C))==0
    assert sp.expand(tr2-18*(a*A+b*B+c*C)**2)==0
    print('Exact symbolic proof: Tr H = 6 sum |Y|^2; Tr H^2 = 18 (sum |Y|^2)^2.')
    print('Hence largest singular value = sum of other two (Heron identity).')
    worst=np.zeros(5)
    for tau in [0.23+1.17j,-.42+.96j,1j,.5+sqrt(3)*.5j,.12+2.4j]:
        y=forms(tau); ys=forms(-1/tau); yt=forms(tau+1)
        e=[abs(y[1]**2+2*y[0]*y[2]),res(ys,tau**2*S@y),res(yt,T@y)]
        for label,r,z,f in [('S',S,ys,tau**4),('T',T,yt,1)]:
            e.append(max(res(r.T@v@r,f*u) for u,v in zip(weight4(y),weight4(z))))
        worst=np.maximum(worst,e)
    assert max(worst)<1e-11
    print('Max errors at 5 modular points: Y relation, S, T, weight4 S covariance, weight4 T covariance:',worst)
    sol,atm=75.37,2521.
    scale=sqrt(sol/(120*sqrt(26)))
    m=np.array([scale*(sqrt(234)-10),scale*(sqrt(234)+10),sqrt((scale*(sqrt(234)-10))**2+atm)])
    r=m[1]/m[0]
    print('Original conditional masses meV:',m,'ratio:',r,'sum:',sum(m))
    print('Direct texture mass sum residual m3-m2-m1:',m[2]-m[1]-m[0])
    print('Restricted inverse texture residual 1/m1-1/m2-1/m3 (1/meV):',1/m[0]-1/m[1]-1/m[2])
    print('Direct NO predicted solar/atmospheric ratio with original r:',(r*r-1)/((1+r)**2-1),'measured ratio:',sol/atm)
    print('Inverse NO requires 1 < r < 2; original r:',r)
    direct=brentq(lambda x: sqrt(x*x+atm)-sqrt(x*x+sol)-x,0,100)
    inv=brentq(lambda x: 1/x-1/sqrt(x*x+sol)-1/sqrt(x*x+atm),.001,100)
    for label,x in [('Direct texture NO necessary mass solution',direct),('Restricted inverse texture NO necessary mass solution',inv)]:
        v=[x,sqrt(x*x+sol),sqrt(x*x+atm)]
        print(label, 'meV:',v,'sum:',sum(v),'m2/m1:',v[1]/v[0])
    # No coefficients fitted; example demonstrates that extra allowed tensors remove identity.
    tau=.23+1.17j
    pieces=weight4(forms(tau)); v=masses(pieces[0]+.3*pieces[1]-.2*pieces[2])
    print('Weight4 illustrative only, tau=',tau,'coefficients (1, 0.3, -0.2); dimensionless masses:',v,'sum-rule residual:',v[2]-v[1]-v[0])
    assert abs(v[2]-v[1]-v[0])>1e-5
    print('No weight4 fit performed. No modulus stabilization, no CFT-to-particle map.')
    print('All assertions passed.')
if __name__=='__main__': main()
