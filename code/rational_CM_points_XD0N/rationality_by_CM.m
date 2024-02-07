// The aim of this code is to produce info on rational CM points on quotients
// X_0(D;N)/<w_m> for D coprime to N and m || DN.

load "shimura_curve_CM_locus.m"; // CM points work from Saia22
class_num_1 := cond_disc_list_allO[1]; // class number 1 im quad orders
class_num_2 := cond_disc_list_allO[2]; // class number 2 im quad orders



// HallDivisors: lists hall divisors of given integer N

HallDivisors := function(N)
    return [d : d in Divisors(N) | GCD(d,Integers()!(N/d)) eq 1 and d ne 1];
end function;



// quad_CM_X0DN : given D coprime to N, outputs a list of all quadratic CM points
// on X_0(D;N). The format of the output is a a sequence which consists of two sequences -- 
// the second is for points with residue field a corresponding ring class field, and the first is for points 
// with residue field a subfield of a ring class field cut out by an involution of a certain type. Each 
// of these two sequences has elements of the form [d_K,f,f',number] where [f,d_K] is the order
// of the CM point, f' is the conductor corresponding to the residue field, and number is the number
// of points with that same residue field (and ramification index w.r.t. the map
// to trivial level, which we don't track here)

quad_CM_X0DN := function(D,N)

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

    return quad_pts;
end function; 



// rational_CM_quotients: Given D coprime to N, outputs a list of all Hall Divisors m of 
// DN such that there exists a rational CM point on the quotient X_0(D;N)/<w_m>. We don't
// track the count or CM discriminants of such points, just existence. 
// (See the next function to track this information.)

rational_CM_quotients_X0DN := function(D,N)

    // computing list of quadratic CM points on X_0(D;N)
    quad_pts := quad_CM_X0DN(D,N); 

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



// rational_CM_points_XD0N: Given D coprime to N, outputs for each Hall Divisor m of DN a list 
// of counts of all rational CM point on the quotient X_0(D;N)/<w_m>
// Output format: A list [D,N,quotient_list], where quotient_list is a sequence of sequences of the
// form [m,rat_CM_pts] where rat_CM_pts is a sequence of sequences of the form 
// [d_K,number] indicating that the quotient X_0(D;N)/<w_m> has number rational d_K-CM points. 

rational_CM_points_X0DN := function(D,N)

    // computing list of quadratic CM points on X_0(D;N)

    quad_pts := quad_CM_X0DN(D,N); 

    HD := HallDivisors(D*N); 
    quotient_list := []; // initializing quotient_list

    for m_index in [1..#HD] do

        m := HD[m_index];
        rat_CM_pts := []; 

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
                Append(~rat_CM_pts,[d_K,pt[4]]); // tracking CM discriminant, number
            end if; 
        end for;


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
                Append(~rat_CM_pts,[d_K,pt[4]]); // tracking CM discriminant, number
            end if; 
        end for;

        Append(~quotient_list,[*m,rat_CM_pts*]);

    end for;

    return [* D,N,quotient_list *];

end function; 


// Testing

// range one wishes to compute rational CM points info for
    // D_list := [D : D in [6..100] | IsSquarefree(D) and IsEven(#PrimeDivisors(D))];
    // N_list := [1..100];
    // DN_list := [[D,N] : D in D_list, N in N_list | GCD(D,N) eq 1];

    // for pair in DN_list do
    //     D := pair[1];
    //     N := pair[2];
    //     // rational_CM_quotients_X0DN(D,N);
    //     rat_pts := rational_CM_points_X0DN(D,N); 
    //     for quotient in rat_pts[3] do
    //         if #quotient[2] gt 0 then 
    //             print D, N, quotient;
    //         end if; 
    //     end for;
    // end for; 




