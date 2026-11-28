"""Restricted scalar-tensor Gildener-Weinberg test; not full RG or quantum gravity.
Conventions: Lorentzian action F R/2 - (dphi)^2/2 - V, F=c phi^2.
Jordan-frame fixed renormalization scale, fixed angular direction, fixed c.
"""
import sympy as s
import mpmath as mp
mp.mp.dps=90
x,B,r,C=s.symbols('x B r C', positive=True)
# x = phi/f. U = B f^4 u, with r=rho0/(B f^4), C=quartic shift/B.
u=s.log(x**2)-s.Rational(1,2)+r/x**4+C
assert s.simplify(s.diff(u,x)-(2/x-4*r/x**5))==0
assert s.simplify(s.diff(u,x,2).subs(r,x**4/2)-8/x**2)==0
assert s.simplify(u.subs(r,x**4/2)-s.log(x**2)-C)==0
assert s.simplify(s.diff(u,x).subs(r,0)-2/x)==0
# canonical radial normalization from scalar-tensor Weyl rescaling
c,P,phi=s.symbols('c P phi',positive=True)
F=c*phi**2
K=s.simplify(P**2*(1/F+s.Rational(3,2)*(s.diff(F,phi)/F)**2))
assert s.simplify(K-P**2*(1/c+6)/phi**2)==0
# double-log extension, dimensionless Einstein potential shape
A,b,d,L=s.symbols('A b d L',real=True)
g=A+b*L+d*L**2
assert s.simplify(g.subs(L,-b/(2*d))-(A-b*b/(4*d)))==0
print('Symbolic derivative, stationary Hessian, canonical normalization and double-log checks passed.')
v=mp.mpf('246.22'); mh=mp.mpf('125.25'); mw=mp.mpf('80.377'); mz=mp.mpf('91.1876'); mt=mp.mpf('172.5'); mx=mp.mpf(500)
G=mp.mpf('6.708e-39'); P=1/mp.sqrt(8*mp.pi*G); dark=mp.mpf('2.6e-47')
Q=mh**4+6*mw**4+3*mz**4-12*mt**4+mx**4
Rvac=Q/(128*mp.pi**2)
fmt=lambda z: mp.nstr(z,12)
print('Inputs: v,mh,mW,mZ,mt,mX=',*[str(z) for z in (v,mh,mw,mz,mt,mx)])
print('Reduced Planck mass (matching input):',fmt(P),'GeV')
print('Q=',fmt(Q),'GeV^4; negative Jordan GW vacuum contribution:',fmt(-Rvac),'GeV^4')
print('Vacuum tuning fraction dark/|V|:',fmt(dark/Rvac))
print('zeta, w, lambda_H, lambda_HS, lambda_S, lambda_XS, flat-direction m^2 (no gravity)')
for zeta in map(mp.mpf,['0.01','1','100']):
 w=P/mp.sqrt(zeta); f=mp.sqrt(w*w+v*v); c=zeta*w*w/f**2
 lp=-mh**2/(2*f*f); lh=-lp*w*w/v**2; ls=-lp*v*v/w**2; lx=mx**2/w**2
 Bnum=Q/(64*mp.pi**2*f**4)
 print(*map(fmt,(zeta,w,lh,lp,ls,lx,8*Bnum*f*f)))
 if zeta==1:
  # Tune rho0 so U_min = dark, holding the original GW reference f and C=0 fixed.
  # At x^4=2r, U_min=Rvac*ln(2r); inversion uses high precision.
  r=mp.exp(dark/Rvac)/2; rho0=2*Rvac*r; x=mp.power(2*r,mp.mpf(1)/4)
  Umin=Rvac*mp.log(2*r)
  assert abs(Umin/dark-1)<mp.mpf('1e-32')
  mE=mp.sqrt(8*Bnum*f**4/(P**2*(6+1/c)))
  print('  B:',fmt(Bnum),'c:',fmt(c),'radial Einstein mass at fixed angular direction:',fmt(mE),'GeV')
  print('  tuned additive Jordan rho0:',fmt(rho0),'GeV^4; fractional excess:',fmt((rho0-Rvac)/Rvac))
  print('  x_min-1:',fmt(x-1),'U_min:',fmt(Umin),'GeV^4')
  print('  dimensionless observed vacuum / reduced Planck^4:',fmt(dark/P**4))
  print('  if fixed Einstein-frame potential is shifted by dark, the required shift is an independent parameter.')
  print('  shared X-loop mixed quartic beta for lambda_XH=0.1:',fmt(lx*mp.mpf('.1')/(8*mp.pi**2)), 'ratio to |portal|:',fmt(lx*mp.mpf('.1')/(8*mp.pi**2*abs(lp))))
print('No additive Jordan constant: for B>0 the Einstein potential is monotonic, no finite radial stationary point.')
print('All checks passed. Matching uses observed G and electroweak masses; no absolute prediction. Angular shifts, running F, graviton loops and higher operators excluded.')
