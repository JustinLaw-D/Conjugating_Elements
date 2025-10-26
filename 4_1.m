load "PiToAlgebraAndVariety.m"; // This defines a free group with generators g,h and inverses gi, hi. We use this later to write down the single relation in the knot group, and to describe the images of the generators under the actions.

load "GetAndValuateConjugatingElements.m";

w4_1:= hi*gi*h*g*hi*g*h*gi*hi*g;
X4_1:=charVarTwoGenGroup(w4_1);
cRing4_1<I_g,I_gh>:=CoordinateRing(X4_1); // for later use. I_g is the trace of m_g, I_gh that of m_gh.
QA4_1:=tautologicalQuaternionAlgebra(X4_1);

tgsi:=gi*h*g; thsi:=h*gi*h*g*hi;
csi:=conjugatingElementForAutomorphism(QA4_1,tgsi,thsi);
ncsi:=Norm(csi);

f1:=I_gh - I_g^2 +2; // this condition defines exactly the reducible representations in the canonical component.
f2:=I_gh-2; // This can be ignored for the current group, since all nonabelian representations satisfy I_gh \neq 2. 

valsi:=valuationInFF(f1, ncsi);
printf "strong inversion valuation: %m.\n", valsi ;


tg2p:=gi; th2p:=gi^2*hi*g^2;
c2p:=conjugatingElementForAutomorphism(QA4_1,tg2p,th2p);
nc2p:=Norm(c2p);

val2p:=valuationInFF(f1, nc2p);
printf "2-periodicity valuation: %m.\n", val2p ;
