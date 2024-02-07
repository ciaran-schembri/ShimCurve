// The aim of this code is to produce info on rational CM points on quotients
// X_0(D;N)/<w_m> for D coprime to N and m || DN.

load "shimura_curve_CM_locus.m"; // CM points work from Saia22
class_num_1 := cond_disc_list_allO[1]; // class number 1 im quad orders
class_num_2 := cond_disc_list_allO[2]; // class number 2 im quad orders

// range one wishes to compute rational CM points info for
D_list := [D : D in [1..100] | IsSquarefree(D) and IsEven(#PrimeDivisors(D))];
N_list := [1..100];
DN_list := [[D,N] : D in D_list, N in N_list | GCD(D,N) eq 1];



// for each pair in to_check, we list all of the quadratic CM points

to_check_quad_pts := [* *];
// format: an element of to_check_quad_pts is of form [* D, N, quad_pts *]
// where quad_pts is a sequence which consists of two sequences -- the second is for 
// points with residue field a ring class field, and the former for points with residue field
// a subfield of a ring class field cut out by an involution of a certain type. Each of these
// two sequences has elements of the form [d_K,f,f',number] where [f,d_K] is the order
// of the CM point, f' is the conductor corresponding to the residue field, and number is the number
// of points with that same residue field (and ramification index w.r.t. the map
// to trivial level, which we don't track here)

for pair in DN_list do 
    D := pair[1];
    N := pair[2];

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

    Append(~to_check_quad_pts, [* D, N, quad_pts *]); 
end for;


HallDivisors := function(N)
    return [d : d in Divisors(N) | GCD(d,Integers()!(N/d)) eq 1 and d ne 1];
end function;

// reminder : pt info lists in to_check_quad_pts are in order [d_K,f,f',number]
// where f is the CM cnductor for the point, and f' is for its residue field

// quad_image_info : list of information about the images of quadratic points in to_check_quad_pts
// on certain Atkin--Lehner quotients. In particular, using GR06 Corollary 5.14, we record for given
// D,N,m, and point list corresponding to [D,N] in to_check_quad_pts whether points of that residue
// field are fixed by w_m
// structure: sequence of sequences [* D, N, pts_info *] where pts_info, where pts_info
// is a sequence of sequences of the form [* m, pts_1, pts_2 *] where pts_i includes, for every quad_pts
// list corresponding to [D,N] in to_check_quad_pts, a sequence [d_K,f,f',B] where B is True if f^2d_K
// points in that list have rational image on X_0^D(N)/w_M and False otherwise. i=1 corresponds to points
// on X_0^D(N) with res fld an index 2 subfield of K(f'), while pts_2 corresponds to points with
// res fld K(f'). 

quad_image_info := [* *];

for i in [1..#to_check_quad_pts] do 

    D := to_check_quad_pts[i][1];
    N := to_check_quad_pts[i][2];
    pts_1 := to_check_quad_pts[i][3][1]; // quad CM pts on X_0^D(N) w/ res fld index 2 in K(f') as in GR06
    pts_2 := to_check_quad_pts[i][3][2]; // quad CM pts on X_0^D(N) w/ res fld K(f') 

    Append(~quad_image_info, [* D, N , [* *] *]);

    HD := HallDivisors(D*N);
    for m_index in [1..#HD] do

        m := HD[m_index];

        Append(~quad_image_info[i][3], [* m, [ ], [ ] *]);

        for pt in pts_1 do // GR06 Cor 5.14 (2)
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
                Append(~quad_image_info[i][3][m_index][2],[* d_K,pt[2],f_R,pt[4],"True" *]);
            else
                Append(~quad_image_info[i][3][m_index][2],[* d_K,pt[2],f_R,pt[4],"False" *]);
            end if; 
        end for;

        for pt in pts_2 do // GR06 Cor 5.14 (1)
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
                Append(~quad_image_info[i][3][m_index][3],[* d_K,pt[2],f_R,pt[4],"True" *]);
            else
                Append(~quad_image_info[i][3][m_index][3],[* d_K,pt[2],f_R,pt[4],"False" *]);
            end if; 
        end for;
    end for;
end for; 


// outputs list of elliptic quotients on which there is a rational CM point

rational_CM_pts_info := [* *];

for i in [1..#quad_image_info] do
    D := quad_image_info[i][1];
    N := quad_image_info[i][2];
    Append(~rational_CM_pts_info, [* D, N, [ ] *]);
    for m_index in [1..#quad_image_info[i][3]] do

        m := quad_image_info[i][3][m_index][1];

        found_rat := "False";

        for pt in quad_image_info[i][3][m_index][2] do
            if pt[5] eq "True" then
                found_rat := "True";
                break;
            end if;
        end for;

        if found_rat eq "False" then

            for pt in quad_image_info[i][3][m_index][3] do
                if pt[5] eq "True" then
                    found_rat := "True";
                    break;
                end if;
            end for;

        end if;

        if found_rat eq "True" then 
            Append(~rational_CM_pts_info[i][3], m);
        end if; 
    end for;
end for;

// output info to file
    // SetOutputFile("rational_CM_pts_info_1000.m");
    // print "quad_image_info := ", quad_image_info;
    // print "rational_CM_pts_info := ", rational_CM_pts_info;
    // UnsetOutputFile(); 

