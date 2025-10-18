Attach("QAforKG.m");

// This code sets up the Quaternion Algebra above for the group 6_1
// First we set up the fundamental group
// 6_1
// We use the presentation
// < a, b | B*a*B*(A*b)^2*A*(B*a)^2*(b*A)^2*b*a >

Pi1<g,h> := FPGroup<g,h | h = g*(h^(-1))*((g^(-1))*h)^2*(g^(-1))*((h^(-1))*g)^2*(h*(g^(-1)))^2*h*g>;

GroundField := Rationals();

// Now we set up the coordinate ring of the canonical component of the character variety

ring := PolynomialRing(GroundField,4);
temp_f<x,r,q,w> := FieldOfFractions(ring);
rhog := Matrix([[x, 1], [0, x^(-1)]]);
rhoh := Matrix([[x, 0], [r, x^(-1)]]);
rhoG := rhog^(-1);
rhoH := rhoh^(-1);
rel := rhoH*rhog*rhoH*(rhoG*rhoh)^2*rhoG*(rhoH*rhog)^2*(rhoh*rhoG)^2*rhoh*rhog - ScalarMatrix(ring,2,1); // enforcing relation
polys := {};
for i in {1,2} do
	for j in {1,2} do
		if rel[i,j] ne 0 then
			Include(~polys,ring ! Numerator(rel[i,j]));
		end if;
	end for;
end for;
eigenvalue_variety := GCD(polys);
eigenvalue_variety;
assert IsPrime(eigenvalue_variety); // This need not be the case in general
intermediate1 := Resultant(eigenvalue_variety, ring ! (x^4+x^2*r+1 - w*x^2), 2); // Overkill for this, but to be consistent, enforces trace relation
intermediate2 := Resultant(intermediate1, ring ! (x^2 + 1 - q*x), 1); // enforces q = x + x^-1
factors,char_var := Factorization(intermediate2);
for poly in factors do
	if poly[2] ge 1 then
		char_var := char_var * poly[1]; // remove multiplicities
	end if;
end for;
char_var;
assert IsPrime(char_var);
ring_2<a,b> := PolynomialRing(GroundField,2); // for some type conversion trickery
conv_map := hom<ring -> ring_2 | 0, 0, a, b>;
aff_spc := AffineSpace(ring_2);
can_comp<q,w> := Scheme(aff_spc,conv_map(char_var)); // assumes char_var is in GF<q,w>
can_comp;

// Finally we set up the quaternion algebra and the group rep
ff<qbar,wbar> := FieldOfFractions(CoordinateRing(can_comp));
I_g := qbar;
I_h := qbar;
I_gh := wbar;
qa6_1<i,j,k> := QuaternionAlgebra<ff | I_g^2-4, -(I_g^2-4)*(I_h^2-4)+(2*I_gh-I_g*I_h)^2>;

ff;

// With this in hand, we can start doing the valuation checks for the symmetry of 6_1
m_g := (i+I_g)/2;
Q := (2*I_gh-I_g*I_h)/(I_g*I_h-4);
m_h := -(i*j)/(2*I_g^2-8) + (i*Q)/2 + I_h/2;
tg := m_g*(m_h^(-1))*m_g*(m_h^(-1))*(m_g^(-1))*m_h*(m_g^(-1))*m_h*(m_g^(-1)); 
th := m_g*(m_h^(-1))*m_g*(m_h^(-1))*m_g*(m_h^(-1))*(m_g^(-1))*m_h*(m_g^(-1))*m_h*(m_g^(-1));
c := automorphismConjugatingElement(qa6_1,tg,th);

c;
assert c*m_g/c eq tg; // check this worked
assert c*m_h/c eq th;

cNorm := Norm(c);
ff :=  Parent(Numerator(cNorm));
r := ring.4-ring.3^2+2; // This condition picks out the reducible representations
val := valuationInFF(ring,r,cNorm);
val;

