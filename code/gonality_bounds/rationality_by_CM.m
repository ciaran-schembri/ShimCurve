// The aim of this code is to produce info on rational CM points on quotients
// X_0(D;N)/<w_m> for D coprime to N and m || DN.

load "shimura_curve_CM_locus.m"; // CM points work from Saia22
class_num_1 := cond_disc_list_allO[1]; // class number 1 im quad orders
class_num_2 := cond_disc_list_allO[2]; // class number 2 im quad orders

// range one wishes to compute rational CM points info for
D_list := [D : D in [1..100] | IsSquarefree(D) and IsEven(#PrimeDivisors(D))];
N_list := [1..100];
DN_list := [[D,N] : D in D_list, N in N_list | GCD(D,N) eq 1];


// HallDivisors: lists hall divisors of given integer N
HallDivisors := function(N)
    return [d : d in Divisors(N) | GCD(d,Integers()!(N/d)) eq 1 and d ne 1];
end function;


// Given D coprime to N, outputs a list of all Hall Divisors m of DN such that there exists a
// rational CM point on the quotient X_0(D;N)/<w_m>
rational_CM_quotients := function(D,N)

    // computing list of quadratic CM points on X_0(D;N)

    quad_pts := [*[**],[**]*]; 
    for order in class_num_1 do
        pts := CM_points_XD0(D,order[1],order[2],N);

        if Type(pts) ne MonStgElt then 

            for pt in pts[1] do 
                if pt[3] eq 2 then 
                    Append(~quad_pts[1],[order[2],order[1],pt[1],pt[4]]);
                end if;
            end for;

            for pt in pts[2] do 
                if pt[3] eq 2 then 
                    Append(~quad_pts[2],[order[2],order[1],pt[1],pt[4]]);
                end if;
            end for;
        end if; 
    end for; 

    for order in class_num_2 do
        pts := CM_points_XD0(D,order[1],order[2],N);

        if Type(pts) ne MonStgElt then 

            for pt in pts[1] do 
                if pt[3] eq 2 then 
                    Append(~quad_pts[1],[order[2],order[1],pt[1],pt[4]]);
                end if;
            end for;
        end if; 
    end for; 

    HD := HallDivisors(D*N); 
    m_list := []; // initializing list of m with corresponding quotients having a rational CM point

    for m_index in [1..#HD] do

        m := HD[m_index];
        found_rat_pt := false; 

        for pt in quad_pts[1] do // GR06 Cor 5.14 (2)
            d_K := pt[1];
            f_R := pt[3];
            disc_R := f_R^2*d_K;
            m_r := GCD(IntegerRing()!m,IntegerRing()!(disc_R/GCD(N,f_R)));
            Q := m/m_r;

            D_R := 1;
            for pair in Factorization(D) do
                if ((f_R mod pair[1]) ne 0) and (KroneckerSymbol(disc_R,pair[1]) eq -1) then
                    D_R := D_R*pair[1];
                end if;
            end for;

            N_star_R := 1;
            for pair in Factorization(N) do 
                if (KroneckerSymbol(disc_R,pair[1]) eq 1) and ((f_R mod pair[1]) ne 0) then
                    N_star_R := N_star_R*pair[1];
                end if;
            end for; 

            // Now we use GRO6 Cor. 5.14 (2) to determine rationality of image points
            // note: d_R in {-12,-16,-27} give false info, as these aren't the correct
            // orders to attach in GR06's framework. We lose nothing by ignoring these orders,
            // as if we actually have fixed points of these orders we have fixed points of 
            // order -3 or -4.
            if (Q eq 1) and (not (D_R in [-12,-16,-27])) then 
                found_rat_pt := true;
                break;
            end if; 
        end for;

        if found_rat_pt eq true then
            Append(~m_list,m);
        
        else

            for pt in quad_pts[2] do // GR06 Cor 5.14 (1)
                d_K := pt[1];
                f_R := pt[3];
                disc_R := f_R^2*d_K;
                m_r := GCD(IntegerRing()!m,IntegerRing()!(disc_R/GCD(N,Integers()!f_R)));
                Q := m/m_r;

                D_R := 1;
                for pair in Factorization(D) do
                    if ((f_R mod pair[1]) ne 0) and (KroneckerSymbol(disc_R,pair[1]) eq -1) then
                        D_R := D_R*pair[1];
                    end if;
                end for;

                N_star_R := 1;
                for pair in Factorization(N) do 
                    if (KroneckerSymbol(Integers()!disc_R,Integers()!pair[1]) eq 1) and ((f_R mod pair[1]) ne 0) then
                        N_star_R := N_star_R*pair[1];
                    end if;
                end for; 

                // Now we use GRO6 Cor. 5.14 (1) to determine rationality of image points
                // note: d_R in {-12,-16,-27} give false info, as these aren't the correct
                // orders to attach in GR06's framework. We lose nothing by ignoring these orders,
                // as if we actually have fixed points of these orders we have fixed points of 
                // order -3 or -4.
                if (Q eq D_R*N_star_R) and (not (disc_R in [-12,-16,-27])) then
                    found_rat_pt := true;
                    break; 
                end if; 
            end for;

            if found_rat_pt eq true then
                Append(~m_list,m);
            end if;
        end if;
    end for;

    return m_list;

end function; 