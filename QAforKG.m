
intrinsic valuationInFF(rng_org::RngMPol,f::RngMPolElt,x::RngFunFracElt) -> RngIntElt
{Explanation in Title}	
	numr := Numerator(x); denr := Denominator(x);
	rng := Parent(numr);
	conv_map := hom<rng_org -> rng | 0, 0, rng.1, rng.2>;
	f := conv_map(f);
	I := ideal< rng | f >;
	I_new := I;
	i_n := 0;
	while numr in I_new do
		i_n := i_n + 1;
		I_new := I_new*I;
	end while;
	I_new := I;
        i_d := 0;
        while denr in I_new do
                i_d := i_d + 1;
                I_new := I_new*I;
        end while;
	return i_n - i_d;

end intrinsic;

matrixOfRelations := function(quat_alg,tg,th)

	// Set up quaternion algebra and important elements
	i := quat_alg.1; j := quat_alg.2; k := quat_alg.3; // setup quaternion algebra
	qbar := BaseField(quat_alg).1; wbar := BaseField(quat_alg).2;
	I_g := qbar;
	I_h := qbar;
	I_gh := wbar;
	m_g := (i+I_g)/2;
	Q := (2*I_gh-I_g*I_h)/(I_g*I_h-4);
	m_h := -(i*j)/(2*I_g^2-8) + (i*Q)/2 + I_h/2;
	A := -Norm(i);
	B := -Norm(j);

	g_const,g_i,g_j,g_k := Explode(Coordinates(m_g));
	h_const,h_i,h_j,h_k := Explode(Coordinates(m_h));
	tg_const,tg_i,tg_j,tg_k := Explode(Coordinates(tg));
	th_const,th_i,th_j,th_k := Explode(Coordinates(th));

	g_const_row := [tg_i*A-g_i*A, tg_j*B-g_j*B, -tg_k*A*B+g_k*A*B]; // relations coming from conjugation
        g_i_row := [tg_const-g_const, -tg_k*B-g_k*B, tg_j*B+g_j*B];
        g_j_row := [tg_k*A+g_k*A, tg_const-g_const, -tg_i*A-g_i*A];
        g_k_row := [tg_j+g_j, -tg_i-g_i, tg_const-g_const];

	h_const_row := [th_i*A-h_i*A, th_j*B-h_j*B, -th_k*A*B+h_k*A*B];
        h_i_row := [th_const-h_const, -th_k*B-h_k*B, th_j*B+h_j*B];
        h_j_row := [th_k*A+h_k*A, th_const-h_const, -th_i*A-h_i*A];
        h_k_row := [th_j+h_j, -th_i-h_i, th_const-h_const];

	// return matrix

	return Matrix([g_const_row, g_i_row, g_j_row, g_k_row,h_const_row, h_i_row, h_j_row, h_k_row]);

end function;

intrinsic automorphismConjugatingElement(quat_alg::AlgQuat,tg::AlgQuatElt,th::AlgQuatElt) -> AlgQuatElt
{Explanation in Title}
	i := quat_alg.1; j := quat_alg.2; k := quat_alg.3; // setup quaternion algebra
	M := matrixOfRelations(quat_alg,tg,th); // get matrix of relations
	M_eche := EchelonForm(M); // work around the null space operation failing
	fld := BaseField(quat_alg);
	// WARNING : IF THE MATRIX HAS 1-DIM NULL SPACE, THIS MAY GIVE THE WRONG ANSWER
	v := [fld ! 0,fld ! 0,fld ! 0];
	if M_eche[1,1] eq 0 then
		v[1] := 1;
	elif M_eche[2,2] eq 0 then
		v[2] := 1;
		v[1] := -M_eche[1,2];
	else
		v[3] := 1;
		v[2] := -M_eche[2,3];
		v[1] := -M_eche[1,3]-v[2]*M_eche[1,2];
	end if;
	test := Matrix([[v[1]],[v[2]],[v[3]]]);
	assert M*test eq ZeroMatrix(fld,8,1); // just check that nothing went wrong
	return v[1]*i + v[2]*j + v[3]*k; // we can assume constant term is zero

end intrinsic;
