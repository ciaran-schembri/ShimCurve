// Authors: Santiago Arango-Pineros, Tristan Phillips
// Date: 02/08/2024


// Signature tables

intrinsic SignatureTableX0DN(DBound::RngIntElt, NBound::RngIntElt) -> Any
    {Outputs signature table of the shimura curves X0(D;N) for D a quaternion discriminant and N coprime to D in the box D =< DBound and N <= NBound.}

    filename := Sprintf("~/Desktop/ShimCurve/data/signature-tables/SignatureTableX0DN_%o_%o.txt", DBound, NBound);
    Write(filename, Sprint("Discriminant ? Level ? Genus ? Elliptic Point Counts: <2,e_2>, <3,e_3>"));
    // we only want D square-free, with an even number of prime factors.
    for D in [D : D in [6..DBound] | MoebiusMu(D) eq 1] do
        // we want N that are coprime to D and square-free.
        for N in [N : N in [1..NBound] | GCD(D,N) eq 1] do
            Gamma := FuchsianGroup(QuaternionOrder(D,N) : VerifyEichler := false);
            e := EllipticInvariants(Gamma);
            g := Genus(Gamma);
            Write(filename, Sprintf("%o ? %o ? %o ? %o,%o ", D, N, g, e[1], e[2]));
        end for;
    end for;
    return Sprint("Signature table produced :)");
end intrinsic;