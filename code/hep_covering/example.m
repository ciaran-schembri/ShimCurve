QQ := Rationals();
B<i,j,ij> := QuaternionAlgebra<QQ|-3,5>;
O := MaximalOrder(B);
ZK := Integers(QuadraticField(-7));
nu := Embed(ZK,O);
G := FuchsianGroup(B);
z := FixedPoints(G!nu, UpperHalfPlane())[1];
D := UnitDisc(:Center:=z);
zeropt := D!0;
fd := FundamentalDomain(G,D);
_ := Group(G);  // add this line
import !"Geometry/GrpPSL2/GrpPSL2Shim/domain.m" : PrintDomain;
PrintDomain(ChangeUniverse(G`ShimFDSidepairsDomain,G), D);


AttachSpec("hep_utils.m");
Gamma := ArithmeticTriangleGroup(2,3,7);
FD := FundamentalDomain(Gamma);
