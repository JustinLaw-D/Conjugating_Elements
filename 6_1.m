load "PiToAlgebraAndVariety.m"; // This defines a free group with generators g,h and inverses gi, hi. We use this later to write down the single relation in the knot group, and to describe the images of the generators under the actions.

load "GetAndValuateConjugatingElements.m";

w6_1:=  h^(-1)*g*(h^(-1))*((g^(-1))*h)^2*(g^(-1))*((h^(-1))*g)^2*(h*(g^(-1)))^2*h*g;
X6_1:=charVarTwoGenGroup(w6_1);
cRing6_1<I_g,I_gh>:=CoordinateRing(X6_1); // for later use. I_g is the trace of m_g, I_gh that of m_gh.
QA6_1:=tautologicalQuaternionAlgebra(X6_1);

tgsi:=g*h^(-1)*g*h^(-1)*g^(-1)*h*g^(-1)*h*g^(-1); 
thsi:=g*h^(-1)*g*h^(-1)*g*h^(-1)*g^(-1)*h*g^(-1)*h*g^(-1);
csi:=conjugatingElementForAutomorphism(QA6_1,tgsi,thsi);
ncsi:=Norm(csi);

f1:=I_gh - I_g^2 +2; // this condition defines exactly the reducible representations in the canonical component.
f2:=I_gh-2; // This can be ignored for the current group, since all nonabelian representations satisfy I_gh \neq 2. 

valsi:=valuationInFF(f1, ncsi);
printf "strong inversion valuation: %m.\n", valsi ;
