"""Conditional neutrino tests of the Runyan two-state matrix; no CFT-to-mass map.
Run with Python 3 (standard library only). Benchmark: NuFIT 6.1, IC23 NO,
https://www.nu-fit.org/sites/default/files/v61.tbl-parameters.pdf
All masses in meV, splittings in meV^2. Measured angles and splittings are inputs
only where indicated. The original L/R labels are not established flavors.
"""
from math import sqrt, asin, degrees, isclose
from itertools import product

OMEGA = sqrt(234)
P = 185/234
S = (1-7/OMEGA)/2
A, B = OMEGA-10, OMEGA+10
SOLAR, ATM = 75.37, 2521.0
S12, S13, S23 = .3088, .02249, .470
RANGES = [(72.36,78.23),(2454.,2592.),(.2893,.3295),(.02070,.02420)]


def masses(scale, atm=ATM):
    a,b=scale*A,scale*B
    return a,b,sqrt(a*a+atm)


def observables(m, s12, s13):
    w=((1-s13)*(1-s12),(1-s13)*s12,s13)
    terms=[a*b for a,b in zip(w,m)]
    return sum(m), sqrt(sum(a*b*b for a,b in zip(w,m))), max(0,2*max(terms)-sum(terms)), sum(terms)


def calibrated(solar, atm):
    return masses(sqrt(solar/(120*sqrt(26))),atm)


def report():
    print('COLLATZ-RUNYAN NEUTRINO VALIDATION — conditional tests, not a CFT-derived particle model')
    print('Benchmark: NuFIT 6.1 (Nov 2025), IC23 without SK-atm, normal ordering')
    print(f'P={P:.12f}; smaller sin^2 theta={S:.12f}; theta={degrees(asin(sqrt(S))):.9f} deg')
    print(f'Complementary angle={90-degrees(asin(sqrt(S))):.9f} deg')
    for name,lo,hi in [('solar',.2893,.3295),('reactor',.02070,.02420),('atmospheric',.432,.587)]:
        print(f'Direct isolated {name} angle: both branches outside 3sigma = {not any(lo<=x<=hi for x in (S,1-S))}')
    print(f'm2/m1 = {B/A:.12f}; m1^2 / solar splitting = {A*A/(B*B-A*A):.12f}')
    for n in (114,243):
        m=masses(40/n)
        print(f'Legacy scale S={n}: masses={m}; solar={m[1]**2-m[0]**2:.9f}; atmospheric input={ATM}')
    m=calibrated(SOLAR,ATM)
    print('Conditional normal-ordering prediction: solar and atmospheric inputs, original eigenvalue ratio retained')
    print(f'M0={sqrt(SOLAR/(120*sqrt(26))):.12f}; equivalent 40/M0={40/sqrt(SOLAR/(120*sqrt(26))):.9f}')
    print('masses=',m)
    print('Using measured mixing angles: sum, beta mass, Majorana effective mass min/max =',observables(m,S12,S13))
    print('Using original solar angle with measured reactor angle (excluded direct identification):',observables(m,S,S13))
    print('Inverted ordering with original pair assigned m1,m2 is impossible at this calibration: m1^2 < |atmospheric splitting|.')
    corners=[(calibrated(a,b),c,d) for a,b,c,d in product(*RANGES)]
    print('Mass ranges over independent 3sigma benchmark intervals (not joint confidence intervals):')
    for i in range(3):
        print(i+1,min(m[i] for m,_,_ in corners),max(m[i] for m,_,_ in corners))
    print('sum mass range:',min(sum(m) for m,_,_ in corners),max(sum(m) for m,_,_ in corners))
    assert isclose(P,4*S*(1-S))
    assert isclose(B*B-A*A,120*sqrt(26))
    assert isclose(m[1]**2-m[0]**2,SOLAR)
    assert isclose(m[2]**2-m[0]**2,ATM)
    assert m[0]**2<2500
    print('All algebraic assertions passed. No independent CFT-to-spacetime mass or flavor map established.')

if __name__=='__main__': report()
