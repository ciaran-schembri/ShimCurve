// The aim of this code is to compute gonality bounds for the Shimura curves X_0(D;N)

load "quot_genus.m"; 
load "rationality_by_CM.m";

// g <= 2
g_eq0 := [[6,1],[10,1],[22,1]];
g_eq1 := [[6,5],[6,7],[6,13],[10,3],[10,7],[14,1],[15,1],[21,1],[33,1],[34,1],[46,1]];

// geometrically hyperelliptic (Ogg83, GY17)
hyp_ell := [[6,11],[6,17],[6,19],[6,29],[6,31],[6,37],[10,11],[10,13],[10,19],[10,23],[14,3],[14,5],[15,2],[15,4],[21,2],[22,3],[22,5],[26,3],[35,1],
    [38,1],[39,1],[39,2],[51,1],[55,1],[57,1],[58,1],[62,1],[69,1],[74,1],[82,1],[86,1],[87,1],[93,1],[94,1],[95,1],[111,1],
    [119,1],[134,1],[146,1],[159,1],[194,1],[206,1]];

// hyperelliptic over Q (Ogg83, GY17)
hyp_ell_gonQ_eq2 := [[6,11],[6,19],[6,29],[6,31],[6,37],[10,11],[10,23],[14,5],[15,2],[22,3],[22,5],[35,1],
    [38,1],[39,1],[39,2],[51,1],[55,1],[58,1],[62,1],[69,1],[74,1],[86,1],[87,1],[94,1],[95,1],[111,1],
    [119,1],[134,1],[146,1],[159,1],[194,1],[206,1]];

// bielliptic and not hyperelliptic or of genus at most 1 (Rotger02 for N=1 and PS24 for N>1)
bielliptic := [[57,1],[65,1],[77,1],[82,1],[85,1],[106,1],[115,1],[118,1] ,[122,1],[129,1],[143,1],
[166,1],[178,1],[202,1],[210,1],[215,1],[314,1],[330,1],[390,1],[462,1],[510,1],[546,1],[6,17],[6,23],[6,41],[6,43],
[6,47],[6,71],[10,17],[10,29],[10,31],[14,13],[14,19],[15,7],[15,11],[15,13],[15,17],[21,5],[21,11],[22,7],[22,17],
[26,5],[33,2],[33,5],[33,7],[34,3],[35,2],[35,3],[38,3],[46,5],[6,25],[10,9],[15,8],[21,4],[39,4]];

// gonality_bound_list : given coprime D and N, returns a list 
// [D, N, gon_Q_low, gon_Q_high, gon_Qbar_low, gon_Qbar_high]
// where 
//      gon_Q_low is a lower bound for the Q-gonality of X_0(D;N)
//      gon_Q_high is an upper bound for the Q-gonality of X_0(D;N)
//      gon_Qbar_low is a lower bound for the Qbar-gonality of X_0(D;N)
//      gon_Qbar_high is an upper bound for the Qbar-gonality of X_0(D;N)

gonality_bound_list := function(D,N) 
    g := genus(D,N);
    Abramovich_bound := Ceiling((21/200)*(g-1)); // Abramovich 
    gon_Q_low := Abramovich_bound;  
    gon_Q_high := 2*g-2; // see, for example, Poonen 07 Appendix A
    gon_Qbar_low := Abramovich_bound;
    gon_Qbar_high := Floor((g+3)/2); // see, for example, Poonen 07 Appendix A

    if [D,N] in g_eq0 then 
        gon_Q_low := 2;
        gon_Q_high := 2;
        gon_Qbar_low := 1;
        gon_Qbar_high := 1;

    elif [D,N] in g_eq1 then 
        gon_Q_low := 2;
        gon_Q_high := 2;
        gon_Qbar_low := 2;
        gon_Qbar_high := 2;

    elif [D,N] in hyp_ell_gonQ_eq2 then 
        gon_Q_low := 2;
        gon_Q_high := 2;
        gon_Qbar_low := 2;
        gon_Qbar_high := 2;

    elif [D,N] in hyp_ell then 
        gon_Q_low := 4;
        gon_Q_high := 4;
        gon_Qbar_low := 2;
        gon_Qbar_high := 2;

    elif [D,N] in bielliptic then 
        gon_Q_low := 4;
        gon_Q_high := 4;
        gon_Qbar_low := 4;
        gon_Qbar_high := 4;

    elif gon_Q_high eq 4 then 
        gon_Q_low := 4;
        gon_Q_high := 4;
        gon_Qbar_low := 4;
        gon_Qbar_high := 4;

    elif gon_Q_high eq 4 then 
        gon_Qbar_low := 4;
        gon_Qbar_high := 4;

    else 
    
        if gon_Qbar_low lt 3 then 
            qon_Qbar_low := 3;
        end if;

        if gon_Q_low lt 4 then
            gon_Q_low := 4; 
        end if; 

    end if;

    if (gon_Q_low ne gon_Q_high) or (gon_Qbar_low ne gon_Qbar_high) then
        m_list := rational_CM_quotients(D,N);

        if #m_list gt 0 then 

            g_quot_min := Min([quot_genus(D,N,m) : m in m_list]);

            if g_quot_min ge 2 then
                gon_bound := 2*g_quot_min;
            else
                gon_bound := 2*(g_quot_min+1);
            end if;

            if gon_bound lt gon_Qbar_high then
                gon_Q_high := gon_bound;
                gon_Qbar_high := gon_bound;
            elif gon_bound lt gon_Q_high then 
                gon_Q_high := gon_bound; 
            end if;  

        end if;
    end if;

    // Shimura curves cannot have odd-degree points (no real points), so Q-gonalities must 
    // be even 
    gon_Q_low := Ceiling(gon_Q_low/2)*2;
    gon_Q_high := Floor(gon_Q_high/2)*2;

    return [D,N,gon_Q_low,gon_Q_high,gon_Qbar_low,gon_Qbar_high];
end function;



// Tests  

// // range one wishes to compute rational CM points info for
// D_list := [D : D in [6..100] | IsSquarefree(D) and IsEven(#PrimeDivisors(D))];
// N_list := [1..100];
// DN_list := [[D,N] : D in D_list, N in N_list | GCD(D,N) eq 1];

// for pair in DN_list do 
//     D := pair[1];
//     N := pair[2];
//     list := gonality_bound_list(D,N); 

//     if (list[3] eq list[4]) and (list[3] gt 4) then // Q-gonality computed
//         print "D, N: ", D, N;
//         print "gon_Q_eq", list[3]; 
//     end if;

//     if (list[5] eq list[6]) and (list[5] gt 4) then // Qbar-gonality computed
//         print "D, N: ", D, N;
//         print "gon_Qbar_eq", list[5]; 
//     end if;
// end for; 



// // range one wishes to compute rational CM points info for
// D_list := [D : D in [6..50] | IsSquarefree(D) and IsEven(#PrimeDivisors(D))];
// N_list := [1..50];
// DN_list := [[D,N] : D in D_list, N in N_list | GCD(D,N) eq 1];

// for pair in DN_list do 
//     D := pair[1];
//     N := pair[2];
//     gonality_bound_list(D,N);
// end for;


