#!/usr/bin/env python3
"""Supporting exact algebra and negative controls, outside all Lean proof inputs.
Requires SymPy. Run normally and with python -O; all acceptance checks are explicit.
"""

from fractions import Fraction as F
from itertools import combinations
import sympy as s


def require(ok,why):
    if not ok:raise ArithmeticError(why)

a,b,alpha=s.symbols('a b alpha',real=True)
K=(b-a)**2*(1-alpha*a*b)
expected=2/(b-a)**2-alpha/(1-alpha*a*b)**2
require(s.factor(s.diff(s.log(K),a,b)-expected)==0,'log-kernel mixed derivative')
require(s.expand((1-alpha*a*b)**2-alpha*(b-a)**2
                 -(1-alpha*a*a)*(1-alpha*b*b))==0,'strict positive numerator')
require(s.factor(s.diff(s.log(K),a,b)+expected)!=0,'reject mixed-derivative sign mutation')

# Direct edge gradients in an arbitrary centered mass coordinate.
u,v,q,x=s.symbols('u v q x',positive=True)
S=u+v;Y=(u-v)/S
phi=(u-v)*S**(q-1)
# The adjacent mass coordinates are x-1/2 and x+1/2.
first=s.diff(phi,u)*u*(x-s.Rational(1,2))+s.diff(phi,v)*v*(x+s.Rational(1,2))
second=s.diff(phi,u)*u*(x-s.Rational(1,2))**2+s.diff(phi,v)*v*(x+s.Rational(1,2))**2
require(s.simplify(first/S**q-(q*x*Y-(1-(1-q)*Y**2)/2))==0,'centered first kernel')
require(s.simplify(second/S**q-(q*Y*(x*x+s.Rational(1,4))-x*(1-(1-q)*Y**2)))==0,'centered second kernel')
require(s.simplify(u*v/S**2-(1-Y*Y)/4)==0,'cubic score normalization')

# Each law has exact mean zero and nonzero second moment.
laws=[([F(-1,2),F(0),F(1)],[F(1,2),F(1,4),F(1,4)]),
      ([F(-1),F(-1,3),F(1,4),F(1)],[F(1,4),F(1,4),F(2,9),F(5,18)]),
      ([F(-1),F(0),F(1)],[F(1,4),F(1,2),F(1,4)])]
checks=0
for ys,mu in laws:
    require(sum(mu)==1 and sum(p*y for p,y in zip(mu,ys))==0,'literal law and zero mean')
    for al in [F(0),F(1,2),F(9,10)]:
        for xs in [[y for y in ys],[(y+2)**2 for y in ys],[max(y,F(0))+y/3 for y in ys]]:
            E=lambda z:sum(p*t for p,t in zip(mu,z))
            m2=E([y*y for y in ys]);m3=E([y**3 for y in ys]);c=E([x*y for x,y in zip(xs,ys)])
            ex=E(xs);var=E([x*x for x in xs])-ex*ex
            evx=E([x*(1-al*y*y) for x,y in zip(xs,ys)])
            cs=(1-al*m2)*E([y*x*x for y,x in zip(ys,xs)])-2*c*evx
            pairs=[]
            for i,j in combinations(range(len(ys)),2):
                w=mu[i]*mu[j]*(ys[j]-ys[i])**2*(1-al*ys[i]*ys[j])
                f=ys[i]+ys[j];h=((xs[j]-xs[i])/(ys[j]-ys[i]))**2
                pairs.append((w,f,h))
            W=sum(w for w,f,h in pairs)
            require(W==m2*(1+al*m2),'pair total')
            require(sum(w*f for w,f,h in pairs)==m3*(1+al*m2),'pair center')
            require(sum(w*h for w,f,h in pairs)==var+al*c*c,'pair slope square')
            require(sum(w*f*h for w,f,h in pairs)==cs,'pair covariance numerator')
            require(cs>=m3/m2*(var+al*c*c),'association inequality control')
            if m3>0:require(cs>0,'strict positive third moment')
            checks+=1
        kernel=lambda i,j:(ys[j]-ys[i])**2*(1-al*ys[i]*ys[j])
        for i,ip,j,jp in combinations(range(len(ys)),4):
            require(kernel(i,j)*kernel(ip,jp)>=kernel(i,jp)*kernel(ip,j),'ordered support MTP2')

# Convexity is material: the same inequality reverses strictly for this
# increasing, strictly concave transform, rather than being universal.
ys,mu=laws[0];xs=[y-y*y/4 for y in ys];al=F(1,2)
E=lambda z:sum(p*t for p,t in zip(mu,z))
m2=E([y*y for y in ys]);m3=E([y**3 for y in ys]);c=E([x*y for x,y in zip(xs,ys)])
var=E([x*x for x in xs])-E(xs)**2
cs=(1-al*m2)*E([y*x*x for y,x in zip(ys,xs)])-2*c*E([x*(1-al*y*y) for x,y in zip(xs,ys)])
require(cs<m3/m2*(var+al*c*c),'reject omitted convexity hypothesis')

# Sharp simple convexity control with symmetric Y.
ys=[F(-1),F(0),F(1)];mu=[F(1,4),F(1,2),F(1,4)];al=F(1,2)
E=lambda z:sum(p*t for p,t in zip(mu,z))
for xs,expected in [([F(0),F(1),F(1)],F(-1,8)),([F(0),F(0),F(1)],F(1,8))]:
    c=E([x*y for x,y in zip(xs,ys)]);m2=E([y*y for y in ys])
    cs=(1-al*m2)*E([y*x*x for y,x in zip(ys,xs)])-2*c*E([x*(1-al*y*y) for x,y in zip(xs,ys)])
    require(cs==expected,'symmetric convex/concave orientation control')
# Without zero mean, the pair expansion contains an additional term.
ys=[F(0),F(1)];mu=[F(1,2),F(1,2)];xs=ys;al=F(1,2)
E=lambda z:sum(p*t for p,t in zip(mu,z))
cs=(1-al*E([y*y for y in ys]))*E([y*x*x for y,x in zip(ys,xs)])-2*E([y*x for y,x in zip(ys,xs)])*E([x*(1-al*y*y) for x,y in zip(xs,ys)])
pair=mu[0]*mu[1]*(ys[0]+ys[1])*(1-al*ys[0]*ys[1])*(xs[0]-xs[1])**2
require(pair-cs==E(ys)*E([x*x*(1-al*y*y) for x,y in zip(xs,ys)])>0,'reject omitted zero mean')

# The stationarity substitution has the exact positive factor 2c.
m2,m3,c,q,M,Z=s.symbols('m2 m3 c q M Z',nonzero=True)
u,v=s.symbols('u v')
A=1-(1-q)*m2
require(s.expand((A*u-2*c*v-2*c*(q*u-v)).subs(c,A/(2*q)))==0,'contact factor 2c')
require(s.expand((A*u-2*c*v-c*(q*u-v)).subs(c,A/(2*q)))!=0,'reject missing factor two')
print('PASS: inverse-score association algebra,',checks,'literal probability controls, contact normalization and mutations')


"""Exact independent-copy pair identities with generic joint moments."""
import sympy as s

def require(ok,why):
    if not ok: raise ArithmeticError(why)

Y,X,Yp,Xp,alpha=s.symbols('Y X Yp Xp alpha')
def M(i,j):
    return s.Integer(1) if (i,j)==(0,0) else s.Symbol(f'M_{i}_{j}')

def pair_expect(poly):
    # (Y,X) and (Yp,Xp) are independent copies. For a deterministic
    # X=phi(Y), the symmetric zero-diagonal expressions below give
    # sum_{i<j} after the factor 1/2.
    ans=0
    for (iy,ix,jy,jx),coeff in s.Poly(s.expand(poly),Y,X,Yp,Xp).terms():
        ans+=coeff*M(iy,ix)*M(jy,jx)/2
    return s.expand(ans)

kernel=(Y-Yp)**2*(1-alpha*Y*Yp)
pair_polys=[kernel,(Y+Yp)*kernel,
            (1-alpha*Y*Yp)*(X-Xp)**2,
            (Y+Yp)*(1-alpha*Y*Yp)*(X-Xp)**2]
raw=[pair_expect(p) for p in pair_polys]
mean,m2,m3,c,ex=M(1,0),M(2,0),M(3,0),M(1,1),M(0,1)
var=M(0,2)-ex**2
A=1-alpha*m2
Cstar=A*M(1,2)-2*c*(ex-alpha*M(2,1))
expected=[m2*(1+alpha*m2),(1+alpha*m2)*m3,
          var+alpha*c**2,Cstar]
# Full generic nonzero-mean correction terms, independently retained.
drifts=[-mean**2-alpha*mean*m3,
        -mean*(m2+alpha*M(4,0)),
        -alpha*mean*M(1,2),
        mean*(M(0,2)-alpha*M(2,2))]
for i,(got,want,drift) in enumerate(zip(raw,expected,drifts),1):
    require(s.expand(got-want-drift)==0,f'generic independent-copy identity {i}')
    require(s.expand(got.subs(mean,0)-want)==0,f'zero-mean pair identity {i}')
    require(s.expand(2*got.subs(mean,0)-want)!=0,f'reject missing unordered-pair factor {i}')
require(s.expand(raw[3]-Cstar)!=0,'reject omitted zero-mean hypothesis')
require(s.expand(raw[2].subs(mean,0)-(var-alpha*c**2))!=0,'reject reversed alpha correction')
# Association after clearing the positive pair mass has this exact factor.
require(s.expand(expected[3]*expected[0]-expected[1]*expected[2]
                 -(1+alpha*m2)*(m2*Cstar-m3*(var+alpha*c*c)))==0,
        'association-to-moment normalization')
# Contact stationarity has precisely the multiplier 2 E[YX].
q=s.symbols('q')
M2scaled=q*M(1,2)-(ex-(1-q)*M(2,1))
require(s.expand(Cstar.subs(alpha,1-q)-2*c*M2scaled
                 -(1-(1-q)*m2-2*q*c)*M(1,2))==0,'general contact factor identity')
require(s.expand((Cstar.subs(alpha,1-q)-2*c*M2scaled)
                 .subs(c,(1-(1-q)*m2)/(2*q)))==0,'stationary contact factor')
require(s.expand((Cstar.subs(alpha,1-q)-c*M2scaled)
                 .subs(c,(1-(1-q)*m2)/(2*q)))!=0,'reject missing contact factor two')
print('PASS: four generic joint-moment pair identities, nonzero-mean corrections, contact factors and mutations')
