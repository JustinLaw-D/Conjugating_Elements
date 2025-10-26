automorphismConjugatingElement:=function(QA,tg,th)
	i := QA.1; j := QA.2; k := QA.3; // set up quaternion algebra
	M := matrixOfRelations(QA,tg,th); // get matrix of relations
	M_eche := EchelonForm(M); // workaround for the failure of the nullspace operation
	fld := BaseField(QA);
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
end function;

conjugatingElementForAutomorphism:=function(QA,tg,th) // takes a quaternion algebra and two targets for g, h. Again, g,h are assumed conjugate.
    gS:=SetToIndexedSet(Generators(QA));
    u:=gS[1];
    i:=gS[2];
    j:=gS[3];

    FF<I_g, I_gh>:=BaseRing(QA);
    
    m_g := (i+I_g*u)/2; //
    Q := (2*I_gh*u-I_g*I_g*u)/(I_g*I_g*u-4*u);
    m_h := -(i*j)/((2*I_g^2-8)*u) + (i*Q)/2*u + (I_g/2)*u;

    // m_g and m_h represent the images of g,h under a generic representation whose character is in this character variety
    // we use a very ugly process to figure out where their targets are
    m_tg := u;
    tg_sequence:=ElementToSequence(tg);
    for term in tg_sequence do
	if term eq 1 then
	    m_tg:=m_tg*m_g;
	elif term eq -1 then
	    m_tg:=m_tg*(m_g)^(-1);
	elif term eq 2 then
	    m_tg:=m_tg*m_h;
	elif term eq -2 then
	    m_tg:=m_tg*(m_h)^(-1);
	end if;
    end for;

    m_th := u;
    th_sequence:=ElementToSequence(th);
    for term in th_sequence do 
	if term eq 1 then
	    m_th:=m_th*m_g;
	elif term eq -1 then
	    m_th:=m_th*(m_g)^(-1);
	elif term eq 2 then
	    m_th:=m_th*m_h;
	elif term eq -2 then
	    m_th:=m_th*(m_h)^(-1);
	end if;
    end for;
    
    c := automorphismConjugatingElement(QA,m_tg,m_th);

    return c;
end function;



matrixOfRelations := function(quat_alg,tg,th)
	// Set up quaternion algebra and important elements
	i := quat_alg.1; j := quat_alg.2; k := quat_alg.3; // set up quaternion algebra
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


valuationInFF:=function(f,x)
  // Calculates the valuation of the field element x at f
  // f must be an element in the same ring as numr and denomr below, typically the coordinate ring of the variety in the problem.
	numr := Numerator(x); denr := Denominator(x);
	rng := Parent(numr);
	I := ideal< rng | f >;
	if not IsProper(I) then
	   return 0;
	end if;
	
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
end function;
