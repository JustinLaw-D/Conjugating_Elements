Attach("QAforKG.m");

// This code sets up the Quaternion Algebra above for the group 4_1
// First we set up the fundamental group
// 4_1
// We use the presentation
// < a, b | B*A*b*a*B*a*b*A*B*a >

Pi1<g,h> := FPGroup<g,h | g*h = h*g*(h^(-1))*g*h*(g^(-1))*(h^(-1))*g>;

GroundField := Rationals();

// Now we set up the coordinate ring of the canonical component of the character variety

ring := PolynomialRing(GroundField,4);
temp_f<x,r,q,w> := FieldOfFractions(ring);
rhog := Matrix([[x, 1], [0, x^(-1)]]);
rhoh := Matrix([[x, 0], [r, x^(-1)]]);
rhoG := rhog^(-1);
rhoH := rhoh^(-1);
rel := rhoH*rhoG*rhoh*rhog*rhoH*rhog*rhoh*rhoG*rhoH*rhog - ScalarMatrix(ring,2,1); // group pres. relation
polys := {};
for i in {1,2} do
	for j in {1,2} do
		if rel[i,j] ne 0 then
			Include(~polys,ring ! Numerator(rel[i,j])); // need all relations to hold (i.e. entries to be zero)
		end if;
	end for;
end for;
eigenvalue_variety := GCD(polys); // this is the simplest condition enforcing the relation
eigenvalue_variety;
assert IsPrime(eigenvalue_variety); // This need not be the case in general
intermediate1 := Resultant(eigenvalue_variety, ring ! (x^4+x^2*r+1 - w*x^2), 2); // Overkill for this, but to be consistent, enforcing trace relation
intermediate2 := Resultant(intermediate1, ring ! (x^2 + 1 - q*x), 1); // enforcing q = x+x^-1
factors,char_var := Factorization(intermediate2);
for poly in factors do
	if poly[2] ge 1 then
		char_var := char_var * poly[1]; // getting rid of multiplicities
	end if;
end for;
char_var;
assert IsPrime(char_var); // this is not generically true
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
qa4_1<i,j,k> := QuaternionAlgebra<ff | I_g^2-4, -(I_g^2-4)*(I_h^2-4)+(2*I_gh-I_g*I_h)^2>;

ff;

// With this in hand, we can start doing the valuation checks for the symmetries of 4_1
// First we do the valuation check for the strong inversion on 4_1
m_g := (i+I_g)/2;
Q := (2*I_gh-I_g*I_h)/(I_g*I_h-4);
m_h := -(i*j)/(2*I_g^2-8) + (i*Q)/2 + I_h/2;
tg := m_g^(-1); th := (m_g^(-1))*(m_g^(-1))*(m_h^(-1))*m_g*m_g;
c := automorphismConjugatingElement(qa4_1,tg,th);

c;
assert c*m_g/c eq tg; // check this worked
assert c*m_h/c eq th;

cNorm := Norm(c);
ff :=  Parent(Numerator(cNorm));
r := ring.4-ring.3^2+2; // This condition picks out the reducible representations
val := valuationInFF(ring,r,cNorm);
val;

// Now we do the code for the 2 periodicity on 4_1
tg := (m_g^(-1))*m_h*m_g; th := m_h*(m_g^(-1))*m_h*m_g*(m_h^(-1));
c := automorphismConjugatingElement(qa4_1,tg,th);

c;
assert c*m_g/c eq tg; // check this worked
assert c*m_h/c eq th;

cNorm := Norm(c);
ff :=  Parent(Numerator(cNorm));
r := ring.4-ring.3^2+2; // This condition picks out the reducible representations
val := valuationInFF(ring,r,cNorm);
val;
