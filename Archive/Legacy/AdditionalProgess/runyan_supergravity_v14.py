"""Polonyi N=1 SUGRA arithmetic spectator benchmark. Planck units in potential.
K=|z|^2+Z(z,zbar)|q|^2, W=f(z+b)+mu(z)q^2/2.
Two copies q per arithmetic mass. No gauge fields or loop amplitudes.
"""
import sympy as s
import mpmath as mp
mp.mp.dps=100
r=s.sqrt(3); z0=r-1; b0=2-r
x,y,b=s.symbols('x y b',real=True)
# Hidden potential divided by f^2; remove exp at vacuum only after differentiating
V=s.exp(x*x+y*y)*((1+x*(x+b)+y*y)**2+(b*y)**2-3*((x+b)**2+y*y))
sub={x:z0,y:0,b:b0}
E=s.exp(z0**2)
assert s.simplify(V.subs(sub))==0
assert all(s.simplify(s.diff(V,k).subs(sub))==0 for k in (x,y))
hess=s.simplify(s.hessian(V,(x,y)).subs(sub)/(2*E))
assert hess==s.diag(2*r,4-2*r)
assert s.simplify(s.diff(V,b).subs(sub)/E)==-2*r
print('Hidden canonically normalized mass squares / gravitino mass squared:', hess)
print('dV/db /(m32^2 Mp^2):',s.simplify(s.diff(V,b).subs(sub)/E))
# Direct potential check: Kähler metric and inverse, exact high-precision Hessian
# q canonically normalized at z0; mu is holomorphic exp(k z)
def potential(q,z,bb,f,mu0,k,c):
    Z=mp.exp(c*abs(z)**2)
    mu=mu0*mp.exp(k*(z-z0n))
    W=f*(z+bb)+mu*q*q/2
    K=abs(z)**2+Z*abs(q)**2
    Kz=mp.conj(z)*(1+c*Z*abs(q)**2)
    Kq=Z*mp.conj(q)
    Dz=f+k*mu*q*q/2+Kz*W
    Dq=mu*q+Kq*W
    G=mp.matrix([[1+(c+c*c*abs(z)**2)*Z*abs(q)**2,c*mp.conj(z)*Z*q],[c*z*Z*mp.conj(q),Z]])
    D=mp.matrix([Dz,Dq]); out=(D.H*(G**-1)*D)[0]
    return mp.re(mp.exp(K)*(out-3*abs(W)**2))
z0n=mp.sqrt(3)-1; b0n=2-mp.sqrt(3); g=mp.mpf('0.03'); f=g*mp.exp(-z0n*z0n/2)
for c,k in [(mp.mpf(0),mp.mpf(0)),(mp.mpf(1)/3,mp.mpf(1)/3)]:
    print('Kahler metric exponent c, holomorphic mass slope k:',mp.nstr(c,12),mp.nstr(k,12))
    for mass in [(mp.sqrt(234)-10)*mp.mpf('.01'),(mp.sqrt(234)+10)*mp.mpf('.01')]:
        Z=mp.exp(c*z0n*z0n); mu0=mass*Z*mp.exp(-z0n*z0n/2)
        diag=mass**2+(1-3*c)*g*g
        B=g*mass*(mp.sqrt(3)*(k+(1-2*c)*z0n)-1)
        vals=[]
        for direction in [1,1j]:
            val=mp.diff(lambda t: potential(direction*t/mp.sqrt(2*Z),z0n,b0n,f,mu0,k,c),mp.mpf(0),2)
            vals.append(val)
        assert abs(vals[0]-(diag+B))<mp.mpf('1e-90')
        assert abs(vals[1]-(diag-B))<mp.mpf('1e-90')
        assert min(vals)>0
        print('fermion mass, two scalar masses:',*[mp.nstr(v,16) for v in [mass,*map(mp.sqrt,vals)]])
# Supertrace over physical modes (not a full curved-space effective action)
M,gS=s.symbols('M g',positive=True); d=2-r
mminus=M*(s.sqrt(234)-10); mplus=M*(s.sqrt(234)+10)
str2=0;str4=0
for m in [mminus,mplus]:
    for copy in range(2):
        for sign in [-1,1]:
            ms=m*m+gS*gS+sign*d*gS*m
            str2+=ms; str4+=ms**2
        str2-=2*m*m;str4-=2*m**4
# two hidden real scalars, massive gravitino four helicities, massless graviton
for h in [2*r,4-2*r]:str2+=h*gS*gS;str4+=h*h*gS**4
str2-=4*gS*gS;str4-=4*gS**4
assert s.simplify(str2-8*gS*gS)==0
expected=(8+4*d*d)*668*M*M*gS*gS+(44-16*r)*gS**4
assert s.simplify(str4-expected)==0
print('canonical full physical Str m^2:',s.simplify(str2))
print('canonical full physical Str m^4:',s.factor(s.simplify(str4)))
print('sequestered spectator full physical Str m^4:', (36-16*r)*gS**4)
# Classical positive uplift at small b shift using exact hidden-sector minimization
Mp=mp.mpf('2.435e18'); grav=mp.mpf('1000'); rho=mp.mpf('2.6e-47')
shift=-rho/(2*mp.sqrt(3)*grav**2*Mp**2)
print('b shift for rho observed (linear):',mp.nstr(shift,20))
# finite controlled dS example and hidden masses; no claim of physical dark energy prediction
bb=b0n-mp.mpf('0.0001')
f0=mp.exp(-z0n*z0n/2)
fun=lambda zz: potential(0,zz,bb,f0,0,0,0)
zz=mp.findroot(lambda zz:mp.diff(fun,zz),(z0n-mp.mpf('.01'),z0n+mp.mpf('.01')))
assert fun(zz)>0
assert mp.diff(fun,zz,2)>0
assert mp.diff(lambda yy:potential(0,zz+1j*yy,bb,f0,0,0,0),mp.mpf(0),2)>0
print('example positive vacuum b-b0=-0.0001, z, V/(g0^2 Mp^2):',mp.nstr(zz,16),mp.nstr(fun(zz),16))
print('hidden only Str m^4/(32pi^2), g=1 TeV [GeV^4]:',mp.nstr((36-16*mp.sqrt(3))*grav**4/(32*mp.pi**2),16))
print('All assertions passed.')
