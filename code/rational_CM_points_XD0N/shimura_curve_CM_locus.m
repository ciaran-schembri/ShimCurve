// The aim of this code is to compute the Delta-CM locus on X^D_0(N)
// for any imaginary quadratic discriminant Delta and positive integer N coprime to
// a given quaternion discriminant D. We also provide functions e.g. for computing all primitive
// (degrees of) residue fields of Delta-CM points on X^D_0(N). 

// This is done via an isogeny-volcano approach, based on
// work of Clark--Saia 2022 in the D=1 case and work of Saia 2022 in the D>1 case 


//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// CM Points on X^D_0(N)
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////


// CM_points_XD0_prime_power
// Input: factorization of quaternion discriminant D (even product of primes), CM conductor f, fundamental discriminant d_K, 
// prime l, exponent a at least 1
// Ouput: A pair of sequences of sequences [conductor, ram, degree, number],
// with the first sequence in the pair giving the sequence of index 2 subfields of
// ring class fields (as described in work of Jordan and Gonzalez--Rotger) which 
// arise as residue fields of f^2d_K-CM points on X^D_0(l^a) via 
    // the CM conductor of the ring class field, 
    // the ramification index w.r.t. X^D_0(l^a)-->X^D(1) (which is 1, 2, or 3), 
    // the degree over Q of the residue field, and 
    // the number of points with this residue field and ramification index. 
// The second sequence gives the same ordered information for ring class fields
// which arise as residue fields of such points.  

// Note: the elliptic-modular D=1 case of X^1_0(N) = Y_0(N) is allowed!

CM_points_XD0_prime_power := function(D_Fact, f, d_K, l, a)

    L := Valuation(f,l); // "level" of d in G_{K,l,f_0}
    f_0 := IntegerRing()!(f/l^L); // coprime to l part of conductor f

    // checking that D is a quaternion discriminant and l doesn't divide D
    if #D_Fact mod 2 eq 1 then 
        return "D not a quaternion discriminant!";
    end if;

    for pair in D_Fact do 
        if pair[2] gt 1 then 
            return "D not a quaternion discriminant!";
        end if; 

        if pair[1] eq l then 
            return "level not coprime to quaternion discriminant D";
        end if; 
    end for; 

    // checking that K splits the quaternion algebra and computing
    // b = number of primes dividing D which are inert in K
    b := 0; 
    for pair in D_Fact do 
        if KroneckerSymbol(d_K,pair[1]) eq 1 then 
            return "K does not split the quaternion algebra of discriminant D";
        elif KroneckerSymbol(d_K,pair[1]) eq -1 then 
            b := b+1; 
        end if;
    end for; 

    // initializing CM points list 
    points := [*[],[]*];

    // setting splitting behavior of l in K, to be used often
    symbol_l_K := KroneckerSymbol(d_K,l);

    // D_check: true if all primes dividing D are ramified in K, false otherwise 
    D_check := true; 
    for pair in D_Fact do
        if (KroneckerSymbol(d_K,pair[1]) eq -1) then
            D_check := false;
            break;
        end if;
    end for; 


    // Case all primes dividing D ramify in K
    if D_check eq true then 
        
        // 6.1: General Case 

        // Type I
        if (f_0^2*d_K eq -4) and (L eq 0) then
            Append(~points[1],[l^a*f,2,ClassNumber((l^(a)*f)^2*d_K),2^b]); 
        elif (f_0^2*d_K eq -3) and (L eq 0) then
            Append(~points[1],[l^a*f,3,ClassNumber((l^(a)*f)^2*d_K),2^b]); 
        else 
            Append(~points[1],[l^a*f,1,ClassNumber((l^(a)*f)^2*d_K),2^b]); 
        end if; 

        // Type II
        if a le L then
            Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]); 
        end if;

        if L eq 0 then 

            if (f_0^2*d_K eq -4) then 
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[1],[l^(a-1)*f,2,ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,2,2*ClassNumber((l^(a-h)*f)^2*d_K),2^b]);
                    end for;
                end if;

            elif (f_0^2*d_K eq -3) then
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[1],[l^(a-1)*f,3,ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,3,2*ClassNumber((l^(a-h)*f)^2*d_K),2^b]);
                    end for;
                end if;

            else 
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[1],[l^(a-1)*f,1,ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,1,2*ClassNumber((l^(a-h)*f)^2*d_K),2^b]);
                    end for;
                end if;
            end if; 

        end if;

        // Type X
        if (L ge 1) and (a gt L) and (symbol_l_K eq 1) then
            Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]); 
        end if;

        // 6.2: l > 2
        if l gt 2 then 

            // Type V
            if (L ge 2) then 
                for c in [1..Min(a-1,L-1)] do 
                    Append(~points[2],[l^(Max(a-2*c,0))*f,1,2*ClassNumber((l^(Max(a-2*c,0))*f)^2*d_K),2^b*((l-1)/2)*l^(Min(c,a-c)-1)]);
                end for;
            end if;

            // Type VI
            if (a gt L+1) and (L ge 1) and (symbol_l_K eq -1) then 
                Append(~points[1],[l^(Max(a-2*L,0))*f,1,ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b]);
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*(l^(Min(L,a-L))-1)/2]);
            end if; 

            if (a ge L+1) and (L ge 1) and (symbol_l_K eq 0) then 

                // Type VII
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*((l-1)/2)*l^(Min(L,a-L)-1)]);

                // Type VIII
                Append(~points[1],[l^(Max(a-2*L-1,0))*f,1,ClassNumber((l^(Max(a-2*L-1,0))*f)^2*d_K),2^b]);
                if (a-L-1 gt 0) then 
                    Append(~points[2],[l^(Max(a-2*L-1,0))*f,1,2*ClassNumber((l^(Max(a-2*L-1,0))*f)^2*d_K),2^b*(l^(Min(L,a-L-1))-1)/2]);
                end if; 

            end if; 
             
            if (a ge L+1) and (L ge 1) and (symbol_l_K eq 1) then

                // Type IX
                Append(~points[1],[l^(Max(a-2*L,0))*f,1,ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b]);
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*((l-2)*l^(Min(L,a-L)-1)-1)/2]);

                // Type XI
                if (a ge L+2) then 
                    for h in [1..a-L-1] do 
                        Append(~points[2],[l^(Max(a-2*L-h,0))*f,1,2*ClassNumber((l^(Max(a-2*L-h,0))*f)^2*d_K),2^b*(l-1)*l^(Min(L,a-L-h)-1)]);
                    end for;
                end if;

            end if;

        elif l eq 2 then 

            // 6.3: l=2, unramified 
            if symbol_l_K ne 0 then 

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if;

                // Type V_2
                if (L ge a) and (a ge 3) then 
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                if (a ge L+1) and (L ge 3) then 
                    Append(~points[1],[2^(Max(a-2*L+2,0))*f,1,ClassNumber((2^(Max(a-2*L+2,0))*f)^2*d_K),2^b*2]);
                    Append(~points[2],[2^(Max(a-2*L+2,0))*f,1,2*ClassNumber((2^(Max(a-2*L+2,0))*f)^2*d_K),2^b*(2^(Min(a-L+1,L-1)-2)-1)]);
                end if;

                // Type V_4
                for c in [2..Min(L-2,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^b*2^(Min(c,a-c)-2)]);
                end for; 

                // Type VI
                if (a ge L+1) and (L ge 1) and (symbol_l_K eq -1) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^b*2^(Min(L,a-L)-1)]);
                end if;

                // Type XI
                if (a ge L+2) and (L ge 1) and (symbol_l_K eq 1) then 
                    for h in [1..a-L-1] do 
                        Append(~points[2],[2^(Max(a-2*L-h,0))*f,1,2*ClassNumber((2^(Max(a-2*L-h,0))*f)^2*d_K),2^b*2^(Min(L,a-L-h)-1)]);
                    end for;
                end if;

            // 6.4: l=2, ord_2(d_K) = 2
            elif Valuation(d_K,2) eq 2 then

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type V_2
                if (L ge a) and (a ge 3) then
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                for c in [2..Min(L-1,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^b*2^(Min(c,a-c)-2)]);
                end for;

                // Type VI_1
                if (L eq 1) and (a ge 2) then
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type VI_2
                if (a eq L+1) and (L ge 2) then 
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if; 

                // Type VI_3
                if (a ge L+2) and (L ge 2) then 
                    Append(~points[1],[2^(Max(a-2*L,0))*f,1,ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^b*2]);
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^b*(2^(Min(L,a-L)-2)-1)]);
                end if; 

                // Type VIII

                if L ge 1 then 

                    // Type VIII_1
                    if a eq L+1 then 
                        Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                    end if; 

                    // Type VIII_2
                    if a ge L+2 then 
                        Append(~points[2],[2^(Max(a-2*L-1,0))*f,1,2*ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^b*2^(Min(L,a-1-L)-1)]);
                    end if;

                end if;


            // 6.5: l=2, ord_2(d_K) = 3
            elif Valuation(d_K,2) eq 3 then

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type V_2
                if (L ge a) and (a ge 3) then
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                for c in [2..Min(L-1,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^b*2^(Min(c,a-c)-2)]);
                end for;

                // Type VI_1
                if (L eq 1) and (a ge 2) then
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type VI_2
                if (a eq L+1) and (L ge 2) then 
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if; 

                // Type VI_3
                if (a ge L+2) and (L ge 2) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^b*2^(Min(L,a-L)-2)]);
                end if; 

                // Type VIII
                if L ge 1 then 

                    // Type VIII_1
                    if a eq L+1 then 
                        Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                    end if; 

                    // Type VIII_2
                    if a ge L+2 then 
                        Append(~points[1],[2^(Max(a-2*L-1,0))*f,1,ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^b*2]);
                        Append(~points[2],[2^(Max(a-2*L-1,0))*f,1,2*ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^b*(2^(Min(L,a-1-L)-1)-1)]);
                    end if;
                end if;
            end if;
        end if;


    // Case some prime dividing D is inert in K
    elif D_check eq false then 

        // 6.1: General Case 

        // Type I
        if (f_0^2*d_K eq -4) and (L eq 0) then
            Append(~points[2],[l^a*f,2,2*ClassNumber((l^(a)*f)^2*d_K),2^(b)]); 
        elif (f_0^2*d_K eq -3) and (L eq 0) then
            Append(~points[2],[l^a*f,3,2*ClassNumber((l^(a)*f)^2*d_K),2^(b)]); 
        else 
            Append(~points[2],[l^a*f,1,2*ClassNumber((l^(a)*f)^2*d_K),2^(b)]); 
        end if; 

        // Type II
        if a le L then
            Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^(b)]); 
        end if;

        if L eq 0 then 

            if (f_0^2*d_K eq -4) then 
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[2],[l^(a-1)*f,2,2*ClassNumber((l^(a-1)*f)^2*d_K),2^(b)]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,2,2*ClassNumber((l^(a-h)*f)^2*d_K),2^(b+1)]);
                    end for;
                end if;

            elif (f_0^2*d_K eq -3) then
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[2],[l^(a-1)*f,3,2*ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,3,2*ClassNumber((l^(a-h)*f)^2*d_K),2^(b+1)]);
                    end for;
                end if;

            else 
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[2],[l^(a-1)*f,1,2*ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,1,2*ClassNumber((l^(a-h)*f)^2*d_K),2^(b+1)]);
                    end for;
                end if;
            end if; 

        end if;

        // Type X
        if (L ge 1) and (a gt L) and (symbol_l_K eq 1) then
            Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^(b+1)]); 
        end if;

        // 6.2: l > 2
        if l gt 2 then 

            // Type V
            if (L ge 2) then 
                for c in [1..Min(a-1,L-1)] do 
                    Append(~points[2],[l^(Max(a-2*c,0))*f,1,2*ClassNumber((l^(Max(a-2*c,0))*f)^2*d_K),2^(b+1)*((l-1)/2)*l^(Min(c,a-c)-1)]);
                end for;
            end if;

            // Type VI
            if (a gt L+1) and (L ge 1) and (symbol_l_K eq -1) then 
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*(l^(Min(L,a-L)))]);
            end if; 

            if (a ge L+1) and (L ge 1) and (symbol_l_K eq 0) then 

                // Type VII
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*((l-1))*l^(Min(L,a-L)-1)]);

                // Type VIII
                Append(~points[2],[l^(Max(a-2*L-1,0))*f,1,2*ClassNumber((l^(Max(a-2*L-1,0))*f)^2*d_K),2^b*(l^(Min(L,a-L-1)))]);

            end if; 
             
            if (a ge L+1) and (L ge 1) and (symbol_l_K eq 1) then

                // Type IX
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*((l-2)*l^(Min(L,a-L)-1))]);

                // Type XI
                if (a ge L+2) then 
                    for h in [1..a-L-1] do 
                        Append(~points[2],[l^(Max(a-2*L-h,0))*f,1,2*ClassNumber((l^(Max(a-2*L-h,0))*f)^2*d_K),2^(b+1)*(l-1)*l^(Min(L,a-L-h)-1)]);
                    end for;
                end if;

            end if;

        elif l eq 2 then 

            // 6.3: l=2, unramified 
            if symbol_l_K ne 0 then 

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if;

                // Type V_2
                if (L ge a) and (a ge 3) then 
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                if (a ge L+1) and (L ge 3) then 
                    Append(~points[2],[2^(Max(a-2*L+2,0))*f,1,2*ClassNumber((2^(Max(a-2*L+2,0))*f)^2*d_K),2^(b+1)*2^(Min(a-L+1,L-1)-2)]);
                end if;

                // Type V_4
                for c in [2..Min(L-2,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^(b+1)*2^(Min(c,a-c)-2)]);
                end for; 

                // Type VI
                if (a ge L+1) and (L ge 1) and (symbol_l_K eq -1) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^(b+1)*2^(Min(L,a-L)-1)]);
                end if;

                // Type XI
                if (a ge L+2) and (L ge 1) and (symbol_l_K eq 1) then 
                    for h in [1..a-L-1] do 
                        Append(~points[2],[2^(Max(a-2*L-h,0))*f,1,2*ClassNumber((2^(Max(a-2*L-h,0))*f)^2*d_K),2^(b+1)*2^(Min(L,a-L-h)-1)]);
                    end for;
                end if;

            // 6.4: l=2, ord_2(d_K) = 2
            elif Valuation(d_K,2) eq 2 then

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type V_2
                if (L ge a) and (a ge 3) then
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                for c in [2..Min(L-1,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^(b+1)*2^(Min(c,a-c)-2)]);
                end for;

                // Type VI_1
                if (L eq 1) and (a ge 2) then
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type VI_2
                if (a eq L+1) and (L ge 2) then 
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if; 

                // Type VI_3
                if (a ge L+2) and (L ge 2) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^(b+1)*(2^(Min(L,a-L)-2))]);
                end if; 

                // Type VIII
                if L ge 1 then 

                    // Type VIII_1
                    if a eq L+1 then 
                        Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                    end if; 

                    // Type VIII_2
                    if a ge L+2 then 
                        Append(~points[2],[2^(Max(a-2*L-1,0))*f,1,2*ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^(b+1)*2^(Min(L,a-1-L)-1)]);
                    end if;

                end if;

            // 6.5: l=2, ord_2(d_K) = 3
            elif Valuation(d_K,2) eq 3 then

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type V_2
                if (L ge a) and (a ge 3) then
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                for c in [2..Min(L-1,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^(b+1)*2^(Min(c,a-c)-2)]);
                end for;

                // Type VI_1
                if (L eq 1) and (a ge 2) then
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type VI_2
                if (a eq L+1) and (L ge 2) then 
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if; 

                // Type VI_3
                if (a ge L+2) and (L ge 2) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^(b+1)*2^(Min(L,a-L)-2)]);
                end if; 

                // Type VIII
                if L ge 1 then 

                    // Type VIII_1
                    if a eq L+1 then 
                        Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                    end if; 

                    // Type VIII_2
                    if a ge L+2 then 
                        Append(~points[2],[2^(Max(a-2*L-1,0))*f,1,2*ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^(b+1)*(2^(Min(L,a-1-L)-1))]);
                    end if;
                end if;
            end if;
        end if;
    end if; 

    // sort both sequences of point information by conductor (hence also by degree)
    points := [* Sort(points[1],func<x,y | x[1]-y[1]>), Sort(points[2],func<x,y | x[1]-y[1]>) *];
    return points;

end function; 



// CM_points_XD0
// Input: quaternion discriminant D (even product of primes), CM conductor f, 
// fundamental discriminant d_K, positive integer N
// Ouput: A pair of sequences of sequences [conductor, ram, degree, number],
// with the first sequence giving the sequence of index 2 subfields of 
// ring class fields which arise as residue fields of f^2d_K-CM points on X^D_0(N) via 
    // the CM conductor, 
    // the ramification index w.r.t. X^D_0(N)-->X(1) (which is 1, 2, or 3), 
    // the degree over Q of the residue field, and 
    // the number of points with this residue field and ramification index. 
// The second sequence gives the same ordered information for ring class fields
// which arise as residue fields of such points.  

// Note: the elliptic-modular D=1 case of X^1_0(N) = X_0(N) is allowed!

CM_points_XD0 := function(D, f, d_K, N)

    N_Fact := Factorization(N); 
    r := #N_Fact;
    D_Fact := Factorization(D);

    // N = 1 case, X^D_0(N) = X^D(1)
    if N eq 1 then 

        // checking that D is a quaternion discriminant
        if #D_Fact mod 2 eq 1 then 
            return "D not a quaternion discriminant!";
        end if;

        for pair in D_Fact do 
            if pair[2] ne 1 then 
                return "D not a quaternion discriminant!";
            end if; 
        end for; 

        // checking that K splits the quaternion algebra and computing
        // b = number of primes dividing D which are inert in K
        b := 0; 
        for pair in D_Fact do 
            if KroneckerSymbol(d_K,pair[1]) eq 1 then 
                return "K does not split the quaternion algebra of discriminant D";
            elif KroneckerSymbol(d_K,pair[1]) eq -1 then 
                b := b+1; 
            end if;
        end for; 

        // D_check: true if all primes dividing D are ramified in K, false otherwise 
        D_check := true; 
        for pair in D_Fact do
            if (KroneckerSymbol(d_K,pair[1]) eq -1) then
                D_check := false;
                break;
            end if;
        end for; 

        // Case all primes dividing D ramified in K
        if D_check eq true then 
            return [*[[f,1,ClassNumber(f^2*d_K),2^b]], [] *];

        // Case some prime dividing D inert in K
        elif D_check eq false then 
            return [*[], [[f,1,2*ClassNumber(f^2*d_K),2^b]] *];
        end if; 

    // N > 1 case
    elif N gt 1 then 

        // factors for creating cartesian product of information on pts at prime power levels
        prime_level_factors := [];
        for i in [1..r] do 

            // output list from prime_power function
            prime_power_pts := CM_points_XD0_prime_power(D_Fact,f,d_K,N_Fact[i][1],N_Fact[i][2]);

            if Type(prime_power_pts) eq MonStgElt then
                return prime_power_pts; // returns relevant string if K doesn't split B_D or level N not coprime to D
            end if;

            // condensing information to single sequence of pts, each a list with four entries:
                // field type: "NR" for ring class field or "R" for index 2 subfield thereof
                // conductor: CM conductor of the corresponding 
                // ram: ramification index w.r.t map X^D_0(l^a)-->X^D(1)
                // number: number of pts with this res fld and ramification index 
            prime_power_pts_factor := []; 

            // appending rational ring class field residue field pts
            for pt in prime_power_pts[1] do 
                Append(~prime_power_pts_factor,[*"R",pt[1],pt[2],pt[4]*]);
            end for;

            // appending ring class field residue field pts
            for pt in prime_power_pts[2] do
                Append(~prime_power_pts_factor,[*"NR",pt[1],pt[2],pt[4]*]);
            end for; 

            Append(~prime_level_factors,prime_power_pts_factor); 

        end for; 

        // creating cartesian product of information on pts at prime power levels
        prime_level_product := CartesianProduct(prime_level_factors); 

        // initializing list of infromation on CM points on X_0(N) to output
        points := [*[],[]*];

        for pt_tuple in prime_level_product do 

            s := #[i : i in [1..r] | pt_tuple[i][1] eq "NR"];
            conductors := [(Integers() ! pt[2]) : pt in pt_tuple]; 
            cond_lcm := Lcm(conductors); 

            ram := 1;
            for i in [1..r] do
                if pt_tuple[i][3] ne 1 then
                    ram := pt_tuple[i][3];
                    break;
                end if; 
            end for;

            // product of numbers of points at each prime power level 
            count := 1;
            for i in [1..r] do
                count := count*pt_tuple[i][4];
            end for; 

            // Case: all residue fields index 2 subfields of ring class fields 
            if s eq 0 then 
                Append(~points[1],[cond_lcm,ram,ClassNumber(cond_lcm^2*d_K),count]);

            // Case: at least one residue field is a ring class field
            else 
                Append(~points[2],[cond_lcm,ram,2*ClassNumber(cond_lcm^2*d_K),2^(s-1)*count]);
            end if; 

        end for;

        // sort list of points by conductor (hence also by degree)
        points := [* Sort(points[1],func<x,y | x[1]-y[1]>), Sort(points[2],func<x,y | x[1]-y[1]>) *];
        return points;

    end if; 
end function; 




//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Primitive Residue Fields of CM Points on X^D_0(N)
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////


// Prim_CM_res_flds_XD0_prime_power
// Input: factorization of quaternion discriminant D (even product of primes), CM conductor f, fundamental discriminant d_K, 
// prime l, exponent a at least 1
// Ouput: A pair of sequences [conductor, degree], with the first sequence in the
// pair giving information on the index 2 subfield of a ring class field 
// (as described in work of Jordan and Gonzalez--Rotger) which arises as a primitive
// residue field of f^2d_K-CM points on X^D_0(l^a) (if one exists) via 
    // the CM conductor of the ring class field,  
    // the degree over Q of the residue field
// The second sequence gives the same ordered information for the ring class field
// arising as a primitive residue field of such points (if one exists).

Prim_CM_res_flds_XD0_prime_power := function(D_Fact, f, d_K, l, a)

    L := Valuation(f,l); // "level" of d in G_{K,l,f_0}
    f_0 := IntegerRing()!(f/l^L); // coprime to l part of conductor f

    // checking that D is a quaternion discriminant and l doesn't divide D
    if #D_Fact mod 2 eq 1 then 
        return "D not a quaternion discriminant!";
    end if;

    for pair in D_Fact do 
        if pair[2] gt 1 then 
            return "D not a quaternion discriminant!";
        end if; 

        if pair[1] eq l then 
            return "level not coprime to quaternion discriminant D";
        end if; 
    end for; 

    // checking that K splits the quaternion algebra and computing
    // b = number of primes dividing D which are inert in K
    b := 0; 
    for pair in D_Fact do 
        if KroneckerSymbol(d_K,pair[1]) eq 1 then 
            return "K does not split the quaternion algebra of discriminant D";
        elif KroneckerSymbol(d_K,pair[1]) eq -1 then 
            b := b+1; 
        end if;
    end for; 

    // initializing CM points list 
    points := [*[],[]*];

    // setting splitting behavior of l in K, to be used often
    symbol_l_K := KroneckerSymbol(d_K,l);

    // D_check: true if all primes dividing D are ramified in K, false otherwise 
    D_check := true; 
    for pair in D_Fact do
        if (KroneckerSymbol(d_K,pair[1]) eq -1) then
            D_check := false;
            break;
        end if;
    end for; 

    // Casework as in Section 6.6

    // Case all primes dividing D ramified in K
    if D_check eq true then 

        // Case 1.1 
        if (l eq 2) and (a eq 1) then

            // Case 1.1a.
            if (symbol_l_K ne -1) or ((symbol_l_K eq -1) and (L ge 1)) then
                points[1] := [f,ClassNumber(f^2*d_K)];

            // Case 1.1b.
            elif (symbol_l_K eq -1) and (L eq 0) then 
                points[1] := [2*f,ClassNumber((2*f)^2*d_K)];
            end if; 
        end if; 

        if (l^a gt 2) and (L eq 0) then 

            // Case 1.2 
            if symbol_l_K eq 1 then 
                points[1] := [l^a*f,ClassNumber((l^a*f)^2*d_K)]; 
                points[2] := [f,2*ClassNumber(f^2*d_K)];

            // Case 1.3
            elif symbol_l_K eq -1 then
                points[1] := [l^a*f,ClassNumber((l^a*f)^2*d_K)];

            // Case 1.4
            elif symbol_l_K eq 0 then 
                points[1] := [l^(a-1)*f,ClassNumber((l^(a-1)*f)^2*d_K)];
            end if;
        end if; 

        if (l gt 2) and (L ge 1) then 

            // Case 1.5
            if symbol_l_K eq 1 then
                if a le 2*L then 
                    points[1] := [f,ClassNumber((f)^2*d_K)];
                else 
                    points[1] := [l^(a-2*L)*f,ClassNumber((l^(a-2*L)*f)^2*d_K)];
                    points[2] := [f,2*ClassNumber((f)^2*d_K)];
                end if; 

            // Case 1.6
            elif symbol_l_K eq -1 then
                if a le 2*L then
                    points[1] := [f,ClassNumber((f)^2*d_K)];
                else 
                    points[1] := [l^(a-2*L)*f,ClassNumber((l^(a-2*L)*f)^2*d_K)];
                end if;

            // Case 1.7
            elif symbol_l_K eq 0 then
                if a le 2*L+1 then
                    points[1] := [f,ClassNumber((f)^2*d_K)];
                else 
                    points[1] := [l^(a-2*L-1)*f,ClassNumber((l^(a-2*L-1)*f)^2*d_K)];
                end if;
            end if;
        end if;

        if (l eq 2) and (a ge 2) and (L ge 1) then 

            // Case 1.8
            if symbol_l_K eq 1 then 

                // Case 1.8a
                if L eq 1 then 
                    points[1] := [2^a*f,ClassNumber((2^a*f)^2*d_K)];

                // Case 1.8b
                elif (a le 2*L-2) then 
                    points[1] := [f,ClassNumber((f)^2*d_K)];

                // Case 1.8c
                elif (a ge 2*L-1) then 
                    points[1] := [2^(a-2*L+2)*f,ClassNumber((2^(a-2*L+2)*f)^2*d_K)];
                    points[2] := [f,2*ClassNumber((f)^2*d_K)];
                end if; 

            // Case 1.9
            elif symbol_l_K eq -1 then 

                // Case 1.9a
                if L eq 1 then 
                    points[1] := [2^a*f,ClassNumber((2^a*f)^2*d_K)];
                    points[2] := [2^(a-2)*f,2*ClassNumber((2^(a-2)*f)^2*d_K)];

                // Case 1.9b
                elif (a le 2*L-2) then 
                    points[1] := [f,ClassNumber((f)^2*d_K)];

                // Case 1.9c
                elif (a ge 2*L-1) then 
                    points[1] := [2^(a-2*L+2)*f,ClassNumber((2^(a-2*L+2)*f)^2*d_K)];
                    points[2] := [2^(Max(a-2*L,0))*f,2*ClassNumber((2^(Max(2-2*L,0))*f)^2*d_K)];
                end if;

            elif symbol_l_K eq 0 then 

                val := Valuation(d_K,2);

                // Case 1.10
                if val eq 2 then 

                    // Case 1.10a
                    if a le 2*L then 
                        points[1] := [f,ClassNumber((f)^2*d_K)];

                    // Case 1.10b
                    else
                        points[1] := [2^(a-2*L)*f,ClassNumber((2^(a-2*L)*f)^2*d_K)];
                        points[2] := [2^(a-2*L-1)*f,2*ClassNumber((2^(a-2*L-1)*f)^2*d_K)];
                    end if; 

                // Case 1.11
                elif val eq 3 then 

                    // Case 1.11a
                    if a le 2*L+1 then 
                        points[1] := [f,ClassNumber((f)^2*d_K)];

                    // Case 1.11b
                    else
                        points[1] := [2^(a-2*L-1)*f,ClassNumber((2^(a-2*L-1)*f)^2*d_K)];
                    end if; 

                end if; 
            end if; 
        end if; 


    // Case some prime dividing D is inert in K
    elif D_check eq false then 

        // Case 1.1 
        if (l eq 2) and (a eq 1) then

            // Case 1.1a.
            if (symbol_l_K ne -1) or ((symbol_l_K eq -1) and (L ge 1)) then
                points[2] := [f,2*ClassNumber(f^2*d_K)];

            // Case 1.1b.
            elif (symbol_l_K eq -1) and (L eq 0) then 
                points[2] := [2*f,2*ClassNumber((2*f)^2*d_K)];
            end if; 
        end if; 

        if (l^a gt 2) and (L eq 0) then 

            // Case 1.2 
            if symbol_l_K eq 1 then 
                points[2] := [f,2*ClassNumber(f^2*d_K)];

            // Case 1.3
            elif symbol_l_K eq -1 then
                points[2] := [l^a*f,2*ClassNumber((l^a*f)^2*d_K)];

            // Case 1.4
            elif symbol_l_K eq 0 then 
                points[2] := [l^(a-1)*f,2*ClassNumber((l^(a-1)*f)^2*d_K)];
            end if;
        end if; 

        if (l gt 2) and (L ge 1) then 

            // Case 1.5
            if symbol_l_K eq 1 then
                    points[2] := [f,2*ClassNumber((f)^2*d_K)];

            // Case 1.6
            elif symbol_l_K eq -1 then
                if a le 2*L then
                    points[2] := [f,2*ClassNumber((f)^2*d_K)];
                else 
                    points[2] := [l^(a-2*L)*f,2*ClassNumber((l^(a-2*L)*f)^2*d_K)];
                end if;

            // Case 1.7
            elif symbol_l_K eq 0 then
                if a le 2*L+1 then
                    points[2] := [f,2*ClassNumber((f)^2*d_K)];
                else 
                    points[2] := [l^(a-2*L-1)*f,2*ClassNumber((l^(a-2*L-1)*f)^2*d_K)];
                end if;
            end if;
        end if;

        if (l eq 2) and (a ge 2) and (L ge 1) then 

            // Case 1.8
            if symbol_l_K eq 1 then 
                points[2] := [f,2*ClassNumber((f)^2*d_K)];

            // Case 1.9
            elif symbol_l_K eq -1 then 

                // Case 1.9a
                if L eq 1 then 
                    points[2] := [2^(a-2)*f,2*ClassNumber((2^(a-2)*f)^2*d_K)];

                // Case 1.9b
                elif (a le 2*L-2) then 
                    points[2] := [f,2*ClassNumber((f)^2*d_K)];

                // Case 1.9c
                elif (a ge 2*L-1) then 
                    points[2] := [2^(Max(a-2*L,0))*f,2*ClassNumber((2^(Max(2-2*L,0))*f)^2*d_K)];
                end if;

            elif symbol_l_K eq 0 then 

                val := Valuation(d_K,2);

                // Case 1.10
                if val eq 2 then 

                    // Case 1.10a
                    if a le 2*L then 
                        points[2] := [f,2*ClassNumber((f)^2*d_K)];

                    // Case 1.10b
                    else
                        points[2] := [2^(a-2*L-1)*f,2*ClassNumber((2^(a-2*L-1)*f)^2*d_K)];
                    end if; 

                // Case 1.11
                elif val eq 3 then 

                    // Case 1.11a
                    if a le 2*L+1 then 
                        points[2] := [f,2*ClassNumber((f)^2*d_K)];

                    // Case 1.11b
                    else
                        points[2] := [2^(a-2*L-1)*f,2*ClassNumber((2^(a-2*L-1)*f)^2*d_K)];
                    end if; 

                end if; 
            end if; 
        end if; 
    end if;

    return points; 

end function; 



// Prim_CM_res_flds_XD0
// Input: quaternion discriminant D (even product of primes), CM conductor f, 
// fundamental discriminant d_K, positive integer N
// Ouput: A pair of sequences [conductor, degree], with the first sequence in the
// pair giving information on the index 2 subfield of a ring class field 
// (as described in work of Jordan and Gonzalez--Rotger) which arises as a primitive
// residue field of f^2d_K-CM points on X^D_0(N) (if one exists) via 
    // the CM conductor of the ring class field,  
    // the degree over Q of the residue field
// The second sequence gives the same ordered information for the ring class field
// arising as a primitive residue field of such points (if one exists).

// Note: the elliptic-modular D=1 case of X^1_0(N) = Y_0(N) is allowed!

Prim_CM_res_flds_XD0 := function(D, f, d_K, N)

    N_Fact := Factorization(N); 
    r := #N_Fact;
    D_Fact := Factorization(D);

    // D_check: true if all primes dividing D are ramified in K, false otherwise 
    D_check := true; 
    for pair in D_Fact do
        if (KroneckerSymbol(d_K,pair[1]) eq -1) then
            D_check := false;
            break;
        end if;
    end for; 

    // N = 1 case, X^D_0(N) = X^D(1)
    if N eq 1 then 

        // checking that D is a quaternion discriminant
        if #D_Fact mod 2 eq 1 then 
            return "D not a quaternion discriminant!";
        end if;

        for pair in D_Fact do 
            if pair[2] ne 1 then 
                return "D not a quaternion discriminant!";
            end if; 
        end for; 

        // checking that K splits the quaternion algebra
        for pair in D_Fact do 
            if KroneckerSymbol(d_K,pair[1]) eq 1 then 
                return "K does not split the quaternion algebra of discriminant D";
            end if;
        end for; 

        // Case all primes dividing D ramified in K
        if D_check eq true then 
            return [*[f,ClassNumber(f^2*d_K)], [] *];

        // Case some prime dividing D is inert in K
        elif D_check eq false then 
            return [*[], [f,2*ClassNumber(f^2*d_K)] *];
        end if; 

    // N > 1 case
    elif N gt 1 then 

        // factors for creating cartesian product of information on pts at prime power levels
        prime_level_factors := [];
        for i in [1..r] do 

            // output list from prime_power function
            prime_power_flds := Prim_CM_res_flds_XD0_prime_power(D_Fact,f,d_K,N_Fact[i][1],N_Fact[i][2]);

            if Type(prime_power_flds) eq MonStgElt then
                if (prime_power_flds eq "D not a quaternion discriminant!") then 
                    return "D not a quaternion discriminant!";
                elif (prime_power_flds eq "level not coprime to quaternion discriminant D") then 
                    return "D not coprime to N";
                elif (prime_power_flds eq "K does not split the quaternion algebra of discriminant D") then 
                    return "K does not split the quaternion algebra of discriminant D";
                end if; 
            end if; 

            // append prim res flds for ith prime power level
            Append(~prime_level_factors,prime_power_flds); 

        end for; 

        // initializing list of infromation on primitive residue fields
        // of points on X^D_0(N) to output
        points := [*[],[]*];

        // have_fixed: to be true if there is a primitive residue field 
        // of points on X^_0(N) which is an index 2 subfield of a ring 
        // class field, based on info at prime power level

        // have_rcf: to be true if there is a primitive residue field 
        // of points on X^_0(N) which is a ring class field
        if D_check eq true then 

            // initialize have_fixed as true in this case
            have_fixed := true; 

            // check that at each prime power level we have a res fld
            // which is an index 2 subfield of a ring class field
            for i in [1..r] do
                if prime_level_factors[i][1] eq [] then 
                    have_fixed := false;
                    break;
                end if;
            end for; 

            // initialize have_rcf as false in this case
            have_rcf := false; 

            // check that at least one prime power level has a 
            // res fld which is a ring class field
            for i in [1..r] do
                if prime_level_factors[i][2] ne [] then
                    have_rcf := true; 
                    break;
                end if; 
            end for; 

        else 
            have_fixed := false;
            have_rcf := true;
        end if; 

        // index 2 subfield of ring class field primtiive res fld (if it exists)
        if have_fixed eq true then 
            B := 1;

            for i in [1..r] do
                B := IntegerRing()!(B*(prime_level_factors[i][1][1]/f));
            end for; 

            points[1] := [B*f,ClassNumber((B*f)^2*d_K)];

        end if; 

        // ring class field primitive residue field (if it exists)
        if D_check eq true then

            if have_rcf eq true then 
                C := 1;

                for i in [1..r] do 

                    if prime_level_factors[i][2] eq [] then
                        C := IntegerRing()!(C*(prime_level_factors[i][1][1]/f));
                    else 
                        C := IntegerRing()!(C*(prime_level_factors[i][2][1]/f));
                    end if;

                end for;

                points[2] := [C*f,2*ClassNumber((C*f)^2*d_K)];
            end if; 

        else 
            C := 1;

            for i in [1..r] do
                C := IntegerRing()!(C*(prime_level_factors[i][2][1]/f));
            end for; 

            points[2] := [C*f,2*ClassNumber((C*f)^2*d_K)];
        end if;

        return points; 

    end if;
end function; 




//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Least Degrees of CM Points on X^D_0(N)
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////


// d_OCM_XD0
// Input: quaternion discriminant D (even product of primes), CM conductor f, 
// fundamental discriminant d_K, positive integer N
// Ouput: The least degree over mathbb{Q} of an f^2*d_K-CM
// point on X^D_0(N). 

// Note: the elliptic-modular D=1 case of X^1_0(N) = Y_0(N) is allowed!

d_OCM_XD0 := function(D, f, d_K, N)
    
    prim_flds := Prim_CM_res_flds_XD0(D,f,d_K,N);

    if Type(prim_flds) eq MonStgElt then
        if (prim_flds eq "D not a quaternion discriminant!") then 
            return "D not a quaternion discriminant!";
        elif (prim_flds eq "D not coprime to N") then 
            return "D not coprime to N";
        elif (prim_flds eq "K does not split the quaternion algebra of discriminant D") then 
            return "K does not split the quaternion algebra of discriminant D";
        end if; 
    end if; 

    if prim_flds[2] eq [] then 
        return prim_flds[1][2];
    else
        // always have that d_2 <= d_1 when we have two primitive res flds,
        // using notation of section 7.3
        return prim_flds[2][2];
    end if; 
end function; 



// load list of all (not just maximal) orders of class number up to 100. The ith element 
// is the complete list of pairs [f,d_K] = [conductor, fundamental discrimint] for imaginary quadratic
// orders of class number i. Generated using list of maximal orders by M. Watkins. 

load 'cond_disc_list_allO.m';



// d_CM_XD0
// Input: quaternion discriminant D (even product of primes), positive integer N
// Output: If the least degree of a CM point on X^D_0(N) is realized by an order of class
// number at most 100, returns a sequences [f, d_K, h(O), d_{O,CM}(X^D_0(N))] of information 
// corresponding to an imaginary quadratic order O such that d_CM_XD0 = d_OCM_XD0, where:
    // f is the conductor of the order
    // d_K is the fundamental discriminant of the order
    // h(O) is the class number of the order
    // d_{O,CM}(X^D_0(N)) = d_{CM}(X^D_0(N)) is the least degree of an O-CM point on X^D_0(N)
// If the least degree is more than 100, returns "Cannot be computed, larger than 100"

// Note: the D=1 case of X^1_0(N) = X_0(N) is allowed!

d_CM_XD0 := function(D,N)
    
    // initializing list of minimizing order information
    Cond_Fundisc_h_deg := [];

    // attempting to initialize minimizing order info as info at first order d_K = - 3 with f=1
    // this will fail if K does not split D
    f := cond_disc_list_allO[1][1][1];
    d_K := cond_disc_list_allO[1][1][2];
    d_OCM := d_OCM_XD0(D, f, d_K, N);

    if Type(d_OCM) eq MonStgElt then // ensure K splits D 
        if (d_OCM eq "D not a quaternion discriminant!") then // one time check 
            return "D not a quaternion discriminant!"; 
        elif (d_OCM eq "D not coprime to N") then // one time check
            return "D not coprime to N";
        end if; 
            
    else 
        Cond_Fundisc_h_deg := [f, d_K, 1, d_OCM]; // update minimizing order info
    end if; 

    // looping over class number 1 orders to find smaller degrees
    for i in [1..#cond_disc_list_allO[1]] do 
        f := cond_disc_list_allO[1][i][1]; 
        d_K := cond_disc_list_allO[1][i][2]; 
        d_OCM := d_OCM_XD0(D, f, d_K, N);

        if Type(d_OCM) ne MonStgElt then // checks that K splits D 
            if (Cond_Fundisc_h_deg eq []) or (Cond_Fundisc_h_deg[4] gt d_OCM) then 
                Cond_Fundisc_h_deg := [f, d_K, 1, d_OCM]; // update minimizing order info
            end if;
        end if; 
    end for; 

    // If the current least degree found is at most 2 if D>1 and 1 otherwise, 
    // we know it is the least degree
    if (Cond_Fundisc_h_deg ne []) and ((Cond_Fundisc_h_deg[4] eq 1) or ((Cond_Fundisc_h_deg[4] eq 2) and (D gt 1))) then 
        // print "[f, d_K, h(O), d_CM(X^D_0(N))]: ";
        return Cond_Fundisc_h_deg; 
    
    else 
        if (Cond_Fundisc_h_deg ne []) then 
            h0 := Cond_Fundisc_h_deg[4]; // upper bound on class number of an order minimizing the degree
        else 
            h0 := 101; // larger upper bound than will stop the loop below
        end if;

        h := 2;
        while (h le h0) and (h le 100) do 
            for pair in cond_disc_list_allO[h] do
                f := pair[1];
                d_K := pair[2];
                d_OCM := d_OCM_XD0(D, f, d_K, N);

                if Type(d_OCM) ne MonStgElt then // checks that K splits D 
                    if (Cond_Fundisc_h_deg eq []) or (Cond_Fundisc_h_deg[4] gt d_OCM) then 
                        Cond_Fundisc_h_deg := [f, d_K, h, d_OCM]; // update minimizing order info 
                        h0 := d_OCM; // update upper bound on class number of a minimizing order
                    end if;
                end if; 
            end for;

            h := h+1;
        end while;
    end if; 

    
    if Cond_Fundisc_h_deg eq [] then 
        // checking that D is a quaternion discriminant and that D is coprime to N
        D_Fact := Factorization(D); 
        if #D_Fact mod 2 eq 1 then 
            return "D not a quaternion discriminant!";
        end if;

        for pair in D_Fact do 
            if pair[2] ne 1 then 
                return "D not a quaternion discriminant!";
            elif N mod pair[1] eq 0 then 
                return "D not coprime to N";
            end if; 
        end for; 

        // if the pair (D,N) is valid, being in this case means there are 
        // no CM points by an order O with h(O) <= 100
        return "No order of class number up to 100 splits D";

    elif h eq 101 then 
        print "upper bound given by: ", Cond_Fundisc_h_deg;
        return "Cannot be computed, larger than 100";
    else
        // being in this case means least degree is computed exactly 
        // print "[f, d_K, h(O), d_CM(X^D_0(N))]: ";
        return Cond_Fundisc_h_deg; 
    end if; 
end function; 



// Compare_dcm_info
// Input: two lists x, y
// Output: integer which is x[1]-y[1] if this quantity is non-zero, and is x[2]-y[2] otherwise,
// as comparision function for sorting dcm_list in next function
compare_dcm_info := function(x,y)
    c := x[1] - y[1];
    if c ne 0 then
        return c;
    else
        return x[2]-y[2];
    end if;
end function;



// list_d_CM_XD0 
// Input: positive integers low <= high
// Output: returns a sequence of sequences [D, N, f, d_K, d_{O,CM}(X^D_0(N))],
// one for each pair (D,N) with low <= D*N <= high where D>1 is a quaternion discriminant 
// and N is a positive integer relatively prime to D, of information 
// corresponding to an imaginary quadratic order O such that d_CM_XD0 = d_OCM_XD0, where:
    // f is the conductor of the order
    // d_K is the fundamental discriminant of the order
    // d_{O,CM}(X^D_0(N)) = d_{CM}(X^D_0(N)) is the least degree of an O-CM point on X^D_0(N)
// the output list is sorted lexicographically first by D and then by N

list_d_CM_XD0 := function(low,high)

    start_time := Cputime();
    dcm_list := [];

    // determine largest number of prime factors of D values to be considered
    primes_list := PrimesUpTo(Max(Floor(high/2),7)); // want at least four primes here
    size_primes_list := #primes_list;

    prod := 1;
    n_max := 0;
    while prod le high do 
        n_max := n_max+1;
        if 2*n_max le size_primes_list then
            prod := prod*primes_list[2*n_max-1]*primes_list[2*n_max];
        else 
            break;
        end if; 
    end while;

    for n in [1..n_max-1] do
        k := 2*n; // number of prime factors of D

        // get upper bound on largest prime factor of D to consider for 
        // d with k factors
        prod := 1;
        for i in [1..k-1] do
            prod := prod*primes_list[i];
        end for;

        prime_upper_bound := high/prod;

        // create set of primes at most prime_upper_bound
        small_primes_set := {};
        for i in [1..#primes_list] do
            if primes_list[i] le prime_upper_bound then
                Include(~small_primes_set,primes_list[i]);
            else
                break;
            end if;
        end for; 

        // create sequence of k-tuples of primes at most prime_upper_bound
        if k le #small_primes_set then
            k_primes := Subsets(small_primes_set,k);

            // loop through D values, represented by sets in k_primes
            for set in k_primes do

                D := 1;
                for p in set do
                    D := D*p;
                end for;

                if D le high then 

                    // loop through N values
                    for N in [Ceiling(low/D)..Max(Floor(high/D),1)] do

                        coprime_check := true;
                        for prime in set do
                            if N mod prime eq 0 then
                                coprime_check := false;
                                break;
                            end if;
                        end for;

                        if coprime_check eq true then 
                            dcm := d_CM_XD0(D,N);

                            if Type(dcm) eq MonStgElt then 
                                if (dcm eq "Cannot be computed, larger than 100") then 
                                    return "Cannot be computed, larger than 100 for D, N: ", D, ", ", N;
                                elif (dcm eq "No order of class number up to 100 splits D") then 
                                    return "No order of class number up to 100 splits D for D, N: ", D, ", ", N;
                                end if;
                            else 
                                Append(~dcm_list,[D,N,dcm[1],dcm[2],dcm[4]]);
                            end if; 
                        end if; 
                    end for;
                end if; 
            end for;
        end if;
    end for;

    end_time := Cputime();
    print "Done. Time taken", end_time - start_time;
    Sort(~dcm_list,compare_dcm_info);
    return dcm_list; 
end function;


// SetOutputFile("dcm_list_XD0_100k.m");
// print list_d_CM_XD0(1,10^4);
// UnsetOutputFile(); 



//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Back to Sporadic CM Points on X^D_0(N)
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////


// phi_from_fact: Given natural N, factorization of N (list of pairs (p,a)), computes phi(N) 

phi_from_fact := function(N,F)
    P := N;
    for i in [1..#F] do
        P := P*(1-1/(F[i][1]));
    end for;
    return P;
end function;



// psi_from_fact: Given natural N, factorization of N (list of pairs (p,a)), computes psi(N)

psi_from_fact := function(N,F)
    M := 1;
        for i in [1..#F] do
            M := M * (F[i][1]+1)*F[i][1]^(F[i][2]-1);
        end for;
    return M;
end function;



// epsilon1_from_fact: Given factorizations F_D and F_N of a rational quaternion discriminant D and
// a natural number N which is coprime to D, respectively, returns e_1(D,N)

epsilon1_from_facts := function(F_D,F_N)
    P := 1;

    if (#F_N gt 0) and (F_N[1][1] eq 2) then 
        if F_N[1][2] ge 2 then 
            return 0;
        end if;
    end if; 

    for i in [1..#F_D] do
        P := P*(1-KroneckerSymbol(-4,F_D[i][1]));
    end for;
    for i in [1..#F_N] do
        P := P*(1+KroneckerSymbol(-4,F_N[i][1]));
    end for;
    return P;

end function;



// epsilon3_from_fact: Given factorizations F_D and F_N of a rational quaternion discriminant D and
// a natural number N which is coprime to D, respectively, returns e_3(D,N)

epsilon3_from_facts := function(F_D,F_N)
    P := 1;

    if (#F_N gt 0) and (F_N[1][1] eq 3) then 
        if F_N[1][2] ge 2 then 
            return 0;
        end if;

    elif (#F_N gt 1) and (F_N[2][1] eq 3) then 
        if F_N[2][2] ge 2 then 
            return 0;
        end if;
    end if; 

    for i in [1..#F_D] do
        P := P*(1-KroneckerSymbol(-3,F_D[i][1]));
    end for;
    for i in [1..#F_N] do
        P := P*(1+KroneckerSymbol(-3,F_N[i][1]));
    end for;
    return P;

end function;



// no_least_Heegner_disc : list of pairs [D,N] for which there is no imaginary quadratic 
// discriminant of class number at most 100 satisfying the (D,N)-Heegner Hypothesis.
// We check these pairs via exact least degree computations.
no_least_Heegner_disc := [[101959, 210], [111397, 210], [141427, 210], [154583, 210], [164749, 210],
[165053, 330], [174629, 330], [190619, 210], [192907, 210], [194051, 210],
[199801, 330], [208351, 210], [218569, 210], [233519, 210], [240097, 210],
[272459, 210], [287419, 210], [296153, 210], [304513, 210], [307241, 210]];

    // for pair in no_least_Heegner_disc do
    //     dcm := d_CM_XD0(pair[1],pair[2]);
    //     if Type(dcm) eq MonStgElt then 
    //         if (dcm eq "Cannot be computed, larger than 100") then 
    //             print "Cannot be computed, larger than 100 for D, N: ", pair[1], ", ", pair[2];
    //         elif (dcm eq "No order of class number up to 100 splits D") then 
    //             print "No order of class number up to 100 splits D for D, N: ", pair[1], ", ", pair[2];
    //         end if;
    //     else 
    //         if (dcm[4] ge ( (7*EulerPhi(pair[1])*psi_from_fact(pair[2],Factorization(pair[2]))/1600) - 49*Sqrt(pair[1]*pair[2])/400)) then 
    //             print pair;
    //         end if; 
    //     end if;
    // end for;

// we find that all pairs in no_least_Heegner_disc satisfy the above check


// loading bads_list.m : list of pairs (D,N) for which X_0^D(N) is not found guaranteed to have a 
// sporadic CM point just based on the Frey-Faltings type check with the discriminant 
// of smallest absolute value satisfying the (D,N) Heeger hypothesis. This is created
// from code found in sporadic_checks.m. 
// load "bads_list.m";


// fail_dcm_check : list of all 682 triples [D,N,dcm(X_0^D(N))] for which
// dcm(X_0^D(N)) >= (21/400) ( phi(D)psi(N)/12 - e_1(D,N)/4 - e_3(D,N)/3 )
    // fail_dcm_check := [];

    // for pair in bads_list do
    //     dcm := d_CM_XD0(pair[1],pair[2]);
    //     if Type(dcm) eq MonStgElt then 
    //         if (dcm eq "Cannot be computed, larger than 100") then 
    //             print "Cannot be computed, larger than 100 for D, N: ", pair[1], ", ", 1;
    //         elif (dcm eq "No order of class number up to 100 splits D") then 
    //             print "No order of class number up to 100 splits D for D, N: ", pair[1], ", ", 1;
    //         end if;
    //     else 
    //         FD := Factorization(pair[1]);
    //         FN := Factorization(pair[2]);
    //         if (dcm[4] ge ( (21/400)*( (phi_from_fact(pair[1],FD)*psi_from_fact(pair[2],FN)/12) - epsilon1_from_facts(FD,FN)/4 - epsilon3_from_facts(FD,FN)/3))) then 
    //             Append(~fail_dcm_check,[pair[1],pair[2],dcm[4]]); 
    //         end if; 
    //     end if;
    // end for; 

    // SetOutputFile("fail_dcm_check.m");
    // print fail_dcm_check;
    // UnsetOutputFile(); 



// no_sporadics_XD0: list of pairs [D,N] for which we know that X_0^D(N) has no sporadic points,
// by virtue of having infinitely many degree 2 points

load "no_sporadics_XD0.m";
// load "fail_dcm_check.m";

// delta_eq2_D : list of D such that X_0^D(1) has infinitely many degree 2 points

delta_eq2_D := [6,10,14,15,21,22,26,33,34,35,38,39,46,51,55,57,58,62,65,69,74,77,82,
    86, 87,94,95,106,111,118,119,122,129,134,143,146,159,166,194,206, 
    210,215,314, 330,390,510,546];  

// initializing unknown_sporadics: list of all 391 triples [D,N,dcm(X_0^D(N))] consisting of
// pairs [D,N] not in no_sporadics_XD0 such that we are unsure whether X_0^D(N) has a sporadic 
// CM point based on our least degree check and checks based on complete knowledge of infinitude of
// degree 2 points on X_0^D(1) 

// unknown_sporadics := [];

// for triple in fail_dcm_check do
//     if not ([triple[1],triple[2]] in no_sporadics_XD0) then 
//         if (triple[3] gt 2) or (triple[1] in delta_eq2_D) then 
//             Append(~unknown_sporadics,triple);
//         end if;
//     end if;
// end for;

// SetOutputFile("unknown_sporadics.m");
// print unknown_sporadics;
// UnsetOutputFile(); 
    



//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Least Degrees of CM Points on X^D_1(N)
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////


// is_of_Type1 : given a pair (D,N), returns true if (D,N) is Type 1 and false otherwise. 
// (D,N) is Type 1 if D splits Q(\sqrt{-3}), 9 does not divide N, and no prime which is 2 (mod 3) 
// divides N. This is equivalent to
// d_{CM}(X_1(N)) being phi(N)/3, with a minimizing order O_K where K = Q(sqrt(-3))

is_of_Type1 := function(D,N)
    if N mod 9 eq 0 then
        return false;
    end if;

    N_Fact := Factorization(N);
    for pair in N_Fact do
        if KroneckerSymbol(-3, pair[1]) eq -1 then
            return false; 
        end if;
    end for;
 

    D_Fact := Factorization(D);
    for pair in D_Fact do
        if KroneckerSymbol(-3, pair[1]) eq 1 then
            return false; 
        end if;
    end for;

    return true; 

end function;



// is_of_Type2 : given a pair (D,N), returns true if (D,N) is Type 2 and false otherwise. 
// (D,N) is Type 2 if D splits Q(\sqrt{-1}), 4 does not divide N, and no prime which is 3 (mod 4) 
// divides N. This is equivalent to
// d_{CM}(X_1(N)) being phi(N)/2, with a minimizing order O_K where K = Q(sqrt(-4))

is_of_Type2 := function(D,N)
    if N mod 4 eq 0 then
        return false;
    end if;

    N_Fact := Factorization(N);
    for pair in N_Fact do
        if KroneckerSymbol(-4, pair[1]) eq -1 then
            return false; 
        end if;
    end for;
 

    D_Fact := Factorization(D);
    for pair in D_Fact do
        if KroneckerSymbol(-4, pair[1]) eq 1 then
            return false; 
        end if;
    end for;

    return true; 
    
end function;



// d_CM_XD1
// Input: quaternion discriminant D (even product of primes), positive integer N
// Output: If the least degree of a CM point on X^D_0(N) is realized by an order
// of class number at most 100, returns a sequences [f, d_K, h(O), d_{O,CM}(X^D_1(N))] 
// of information corresponding to an imaginary quadratic order O such that d_CM_XD1 = d_OCM_XD1, where:
    // f is the conductor of the order
    // d_K is the fundamental discriminant of the order
    // h(O) is the class number of the order
    // d_{O,CM}(X^D_1(N)) = d_{CM}(X^D_1(N)) is the least degree of an O-CM point on X^D_1(N)
// If the least degree is more than 100, returns "Cannot be computed, larger than 100"

// Note: the D=1 case of X^1_0(N) = X_0(N) is allowed!

d_CM_XD1 := function(D,N)

    dcm_XD0_info := d_CM_XD0(D,N);

    if (D eq 1) and (N in [1,2,3,4,6,7,9,11,14,19,27,43,67,163]) then // dcm(X_1(N)) = 1 cases
        return [* dcm_XD0_info[1], dcm_XD0_info[2], dcm_XD0_info[3], 1 *]; 

    elif N le 3 then 
        return [* dcm_XD0_info[1], dcm_XD0_info[2], dcm_XD0_info[3], dcm_XD0_info[4]*Max(EulerPhi(N)/2,1) *];

    elif is_of_Type1(D,N) then
        return [* 1, -3, 1, EulerPhi(N)/3 *];

    elif is_of_Type2(D,N) then
        return [* 1, -4, 1, EulerPhi(N)/2 *];

    else
        return [* dcm_XD0_info[1], dcm_XD0_info[2], dcm_XD0_info[3], dcm_XD0_info[4]*(EulerPhi(N)/2) *];
    
    end if;
end function; 



//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Sporadic CM Points on X^D_1(N)
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////


// no_sporadics_XD1: list of pairs [D,N] for which we know that X_1^D(N) has no sporadic CM points,
// by virtue of having \delta(X_0^D(N)) = 2 and 
// \delta(X_1^D(N)) \leq Max(2,phi(N)) \leq d_{CM}(X_1^D(N))

    // no_sporadics_XD1 := []; 

    // for pair in no_sporadics_XD0 do 
    //     if Max(2,EulerPhi(pair[2])) le d_CM_XD1(pair[1],pair[2])[4] then 
    //         Append(~no_sporadics_XD1, pair); 
    //     end if;
    // end for; 

    // SetOutputFile("no_sporadics_XD1.m");
    // print no_sporadics_XD1;
    // UnsetOutputFile(); 



