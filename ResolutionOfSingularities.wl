(* ::Package:: *)

BeginPackage["PlaneCurves`"]

PointM::usage="PointM[c,p] calculates the multiplicity of the point p in the curve c." 

SingularPoints::usage="SingularPoints[c] calculates the singular points of the affine plane curve defined by c."

SingularQ::usage"SingularQ[c] yields true if the curve c is singular."

Singular0Q::usage""

BlowUp::usage"BlowUp[c] gives the two charts of the blow up at the origin of the plane curve c."

ResolutionOfSingularities::usage"ResolutionOfSingularities[c] gives the charts of the resolution of singularities of the plane curve c obtained via a sequence of blow ups."
Bl0::usage=""

ShiftOrigin::usage""
(*-----------------------------------Function definitions------------------------------------------*)
Begin["Private`"]

PointM[poly_]:=Min[Map[Total,CoefficientRules[poly,Variables[poly]][[;;,1]]]]

PointM[poly_, point_]:=PointM[ShiftOrigin[poly,point]]

SingularPoints[poly_, cond_:0]:=Solve[Join[Table[D[poly,$v]==0,{$v,Variables[poly]}],{poly==0,cond==0}],Variables[poly][[;;]]]

ShiftOrigin[poly_, point_]:=ReplaceAll[poly,{Variables[poly][[1]]->Variables[poly][[1]]+(Replace[Variables[poly][[1]],point]),Variables[poly][[2]]->Variables[poly][[2]]+Replace[Variables[poly][[2]],point]}]

SingularQ[poly_, cond_:0]:=(Length[SingularPoints[poly, cond]]>0)
Singular0Q[poly_]:=(PointM[poly]>1)

Bl0[poly_]:=If[Singular0Q[poly],Flatten[Module[{u0=ToExpression["u0"],v0=ToExpression["v0"],u1=ToExpression["u1"],v1=ToExpression["v1"]},{Bl0[Expand[(poly/.{Sort[Variables[poly]][[2]]->u0*v0,Sort[Variables[poly]][[1]]->u0})/u0^PointM[poly]],{0},u0],Bl0[Expand[(poly/.{Sort[Variables[poly]][[1]]->v1*u1,Sort[Variables[poly]][[2]]->u1})/u1^PointM[poly]],{1},u1]}]],poly]
Bl0[poly_, tree_, Evar_]:=If[SingularQ[poly, Evar],Module[{var1=Sort[Variables[poly]][[1]],var2=Sort[Variables[poly]][[2]]},Flatten[Table[{Module[{u0=ToExpression["u"<>StringJoin[ToString/@Join[tree,{0}]]],v0=ToExpression["v"<>StringJoin[ToString/@Join[tree,{0}]]]},Bl0[Expand[(poly/.{var2->(u0*v0+(var2/.sing)),var1->u0+(var1/.sing)})/u0^PointM[poly,sing]],Join[tree,{0}],u0]],Module[{u1=ToExpression["u"<>StringJoin[ToString/@Join[tree,{1}]]],v1=ToExpression["v"<>StringJoin[ToString/@Join[tree,{1}]]]},Bl0[Expand[(poly/.{var1->(u1*v1+(var1/.sing)),var2->u1+(var2/.sing)})/u1^PointM[poly,sing]],Join[tree,{1}],u1]]},{sing,SingularPoints[poly,Evar]}],0]],poly]

BlowUp[poly_]:=If[Singular0Q[poly],Module[{v0=ToExpression["v0"],u1=ToExpression["u1"]},{Expand[ReplaceAll[poly,{Variables[poly][[2]]->Variables[poly][[1]]*v0}]/Variables[poly][[1]]^PointM[poly]],Expand[ReplaceAll[poly,{Variables[poly][[1]]->Variables[poly][[2]]*u1}]/Variables[poly][[2]]^PointM[poly]]}],{poly,Variables[poly]}]

ResolutionOfSingularities[poly_/;(Length[Variables[poly]]==2 && PolynomialQ[poly,Variables[poly]])]:=If[SingularQ[poly],Table[{Bl0[ShiftOrigin[poly,point]],point},{point,SingularPoints[poly]}],poly]

End[]

EndPackage[]


(*Bl0[poly_]:=If[Singular0Q[poly],Flatten[{Bl0[Expand[(poly/.{Sort[Variables[poly]][[2]]->u0*v0,Sort[Variables[poly]][[1]]->u0})/u0^PointM[poly]],{0},u0],Bl0[Expand[(poly/.{Sort[Variables[poly]][[1]]->v1*u1,Sort[Variables[poly]][[2]]->u1})/u1^PointM[poly]],{1},u1]}],poly]
Bl0[poly_, tree_, Evar_]:=If[SingularQ[poly, Evar],Module[{var1=Sort[Variables[poly]][[1]],var2=Sort[Variables[poly]][[2]]},Flatten[Table[{Module[{u0=ToExpression["u"<>StringJoin[ToString/@Join[tree,{0}]]],v0=ToExpression["v"<>StringJoin[ToString/@Join[tree,{0}]]]},Bl0[Expand[(poly/.{var2->(u0*v0+(var2/.sing)),var1->u0+(var1/.sing)})/u0^PointM[poly,sing]],Join[tree,{0}],u0]],Module[{u1=ToExpression["u"<>StringJoin[ToString/@Join[tree,{1}]]],v1=ToExpression["v"<>StringJoin[ToString/@Join[tree,{1}]]]},Bl0[Expand[(poly/.{var1->(u1*v1+(var1/.sing)),var2->u1+(var2/.sing)})/u1^PointM[poly,sing]],Join[tree,{1}],u1]]},{sing,SingularPoints[poly,Evar]}],0]],poly]
BlowUp[poly_]:=If[Singular0Q[poly],{Expand[(poly/.{Variables[poly][[2]]->Variables[poly][[1]]*v0})/Variables[poly][[1]]^PointM[poly]],Expand[(poly/.{Variables[poly][[1]]->Variables[poly][[2]]*u1})/Variables[poly][[2]]^PointM[poly]]},{poly,Variables[poly]}]
*)
