"""Local modular N=1 supergravity benchmark. Planck units, no gauge sector.
Requires sympy and mpmath. No claim of global metric positivity or loop protection.
"""
import sympy as s
import mpmath as mp
mp.mp.dps=110
# Exact local expansion in Kähler normal coordinates
q,r,w,a,b,c,A=s.symbols('q r w a b c alpha', real=True)
K=q*r+(s.Rational(1,6)-A)*q*q*r*r
W=w+a*q+b*q*q/2+c*q**3/6
Wb=W.subs(q,r)
g=s.diff(K,q,r)
# Only terms through total degree 2 are needed for the vacuum Hessian.
V=(1+q*r)*((1-(s.Rational(2,3)-4*A)*q*r)*(s.diff(W,q)+r*W)*(s.diff(Wb,r)+q*Wb)-3*W*Wb)
V=s.Poly(s.expand(V),q,r)
coeff=lambda i,j:s.simplify(V.coeff_monomial(q**i*r**j))
assert coeff(0,0)==a*a-3*w*w
assert s.simplify(coeff(1,0)-a*(b-2*w))==0
assert s.simplify(2*coeff(2,0)-(a*c-b*w))==0
assert s.simplify(coeff(1,1).subs(b,2*w)-(2*w*w-(s.Rational(2,3)-4*A)*a*a))==0
print('Exact local stationary-point and Hessian identities passed.')
print('Canonical scalar mass squares / gravitino mass squared: 12 alpha (1+gamma) - 2 gamma')
# Direct no-scale scalar potential identity at arbitrary Q for one representative multiplet
T,Tb,Q,Qb,W0,W0b,Wq,Wqb=s.symbols('T Tb Q Qb W0 W0b Wq Wqb')
X=T+Tb-Q*Qb/3
K0=-3*s.log(X); zz=[T,Q]; zb=[Tb,Qb]
G=s.Matrix([[s.diff(K0,i,j) for j in zb] for i in zz])
D=s.Matrix([s.diff(K0,T)*W0,Wq+s.diff(K0,Q)*W0])
Db=s.Matrix([s.diff(K0,Tb)*W0b,Wqb+s.diff(K0,Qb)*W0b])
assert s.simplify((Db.T*G.inv()*D)[0]-3*W0*W0b-X*Wq*Wqb)==0
print('Exact no-scale matter potential identity passed.')
# Modular functions computed from theta constants / Euler product.
def eta(t):
    z=mp.exp(2*mp.pi*1j*t)
    return mp.exp(mp.pi*1j*t/12)*mp.qp(z,z)
def j(t):
    z=mp.exp(mp.pi*1j*t)
    l=(mp.jtheta(2,0,z)/mp.jtheta(3,0,z))**4
    return 256*(1-l+l*l)**3/(l*l*(1-l)**2)
def poly(co,x): return sum(v*x**i for i,v in enumerate(co))
def interpolate(target,J,n):
    # triangular Hermite interpolation in local modular invariant J, J(0)=0, J'(0)=1
    co=[]
    for k in range(n+1):
        v=mp.diff(lambda x:target(x)-poly(co,J(x)),0,k)/mp.factorial(k)
        co.append(v)
    return co
alpha=mp.sqrt(2)/12
for D in [3,37,137]:
    y0=mp.sqrt(D); t0=1j*y0
    tau=lambda q:t0+(2j*y0)*(q/mp.sqrt(3))/(1-q/mp.sqrt(3))
    j0=j(t0); jq=mp.diff(lambda q:j(tau(q)),0)
    Jt=lambda t:(j(t)-j0)/jq
    J=lambda q:Jt(tau(q))
    e0=eta(t0)
    print('D',D,'j0',mp.nstr(j0.real,18),'normalized derivative',mp.nstr(mp.diff(J,0),8))
    for gamma in [mp.mpf(0),mp.mpf('0.01')]:
        aa=-mp.sqrt(3*(1+gamma)); bb=mp.mpf(2); cc=2/aa
        target=lambda q:1+aa*q+bb*q*q/2+cc*q**3/6
        # Wnorm = (1-q/sqrt(3))^3 (eta0/eta(tau))^6 P(J), with Wnorm(0)=1.
        targetP=lambda q:target(q)*(eta(tau(q))/e0)**6/(1-q/mp.sqrt(3))**3
        co=interpolate(targetP,J,3)
        Wn=lambda q:(1-q/mp.sqrt(3))**3*(e0/eta(tau(q)))**6*poly(co,J(q))
        for k in range(4): assert abs(mp.diff(Wn,0,k)-mp.diff(target,0,k))<mp.mpf('1e-60')
        def pot(q):
            Jq=J(q); dJ=mp.diff(J,q); r=abs(q)**2
            K=-3*mp.log(1-r/3)-alpha*abs(Jq)**4
            Kq=mp.conj(q)/(1-r/3)-2*alpha*abs(Jq)**2*mp.conj(Jq)*dJ
            metric=1/(1-r/3)**2-4*alpha*abs(Jq*dJ)**2
            W=Wn(q); DW=mp.diff(Wn,q)+Kq*W
            return mp.exp(K)*(abs(DW)**2/metric-3*abs(W)**2)
        v=pot(0); masses=[mp.diff(lambda h:pot(h*d),0,2)/2 for d in [1,1j]]
        expected=12*alpha*(1+gamma)-2*gamma
        assert abs(v-3*gamma)<mp.mpf('1e-60')
        assert all(abs(m-expected)<mp.mpf('1e-60') for m in masses)
        assert all(abs(mp.diff(lambda h:pot(h*d),0))<mp.mpf('1e-60') for d in [1,1j])
        # Classical modular invariance of G=K+log|W|^2 under S and T generators.
        def Gfun(t):
            return -3*mp.log(2*t.imag)-alpha*abs(Jt(t))**4+mp.log(abs((2*y0)**mp.mpf('1.5')*(e0/eta(t))**6*poly(co,Jt(t)))**2)
        tt=tau(mp.mpc('.02','.01'))
        err=max(abs(Gfun(tt+1)-Gfun(tt)),abs(Gfun(-1/tt)-Gfun(tt)))
        print(' modular G residual',mp.nstr(err,8))
        assert err<mp.mpf('1e-60')
        print(' gamma',mp.nstr(gamma),'V/g^2',mp.nstr(v,12),'mass^2/g^2',*[mp.nstr(m,14) for m in masses])
        print(' normalized W polynomial coefficients',*[mp.nstr(v,14) for v in co])
    # For gamma=0, mu(t) weight -1, matching a constant through order 1.
    cmu=interpolate(lambda q:(eta(tau(q))/e0)**2,J,1)
    mu=lambda q:(e0/eta(tau(q)))**2*poly(cmu,J(q))
    assert abs(mu(0)-1)<mp.mpf('1e-60') and abs(mp.diff(mu,0))<mp.mpf('1e-60')
    print(' normalized mass polynomial coefficients',*[mp.nstr(v,14) for v in cmu])
    # Full matter Hessian at the fixed modulus; correction and its first two
    # derivatives vanish there. g=1 and M/g=1 for ratios, not Planck-scale input.
    X0=2*y0
    for gamma in [mp.mpf(0),mp.mpf('0.01')]:
        a0=-mp.sqrt(3*(1+gamma))
        W0=X0**mp.mpf('1.5')
        WT=W0*(a0+mp.sqrt(3))*mp.sqrt(3)/X0
        for m in [mp.sqrt(234)-10,mp.sqrt(234)+10]:
            mu0=m*mp.sqrt(X0)
            def matter_potential(Q):
                X=X0-abs(Q)**2/3
                W=W0+mu0*Q**2/2
                G=mp.matrix([[3/X**2,-Q/X**2],[-mp.conj(Q)/X**2,1/X+abs(Q)**2/(3*X**2)]])
                dv=mp.matrix([WT-3*W/X,mu0*Q+mp.conj(Q)*W/X])
                return mp.re((dv.H*G**-1*dv)[0]-3*abs(W)**2)/X**3
            vals=[mp.diff(lambda t:matter_potential(d*t*mp.sqrt(X0/2)),0,2) for d in [1,1j]]
            assert min(vals)>0
            if gamma==0: assert max(abs(v-m*m) for v in vals)<mp.mpf('1e-60')
            print(' matter gamma',mp.nstr(gamma),'fermion/g',mp.nstr(m,12),'scalar/g',*[mp.nstr(mp.sqrt(v),12) for v in vals])

# Physical mass moment diagnostics at broken Minkowski vacuum, matched spectators cancel.
grav=s.symbols('g', positive=True)
str2=(24*A-4)*grav**2; str4=(288*A*A-4)*grav**4
assert s.simplify(str4.subs(A,s.sqrt(2)/12))==0
print('Str m^2/g^2 at fourth moment cancellation:',s.simplify(str2.subs(A,s.sqrt(2)/12)/grav**2))
print('Str m^4/g^4:',str4/grav**4)
print('Equal-subtraction flat-space CW diagnostic at fourth moment cancellation, V/g^4:',mp.nstr(mp.log(2)/(32*mp.pi**2),16))
print('All assertions passed. Classical local benchmark only; no full quantum gravity calculation.')
