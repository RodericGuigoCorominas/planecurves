(* ::Package:: *)

BeginPackage["PlaneCurves`"]

PointM::usage="PointM[c,p] calculates the multiplicity of the point p in the curve c." 

SingularPoints::usage="SingularPoints[c] calculates the singular points of the affine plane curve defined by c."

SingularQ::usage"SingularQ[c] yields true if the curve c is singular."

Singular0Q::usage""

BlowUp::usage"BlowUp[c] gives the two charts of the blow up at the origin of the plane curve c."

ResolutionOfSingularities::usage"ResolutionOfSingularities[c] gives the charts of the resolution of singularities of the plane curve c obtained via a sequence of blow ups."
Bl0::usage=""

PolynomialDegree::usage"PolynomialDegree[p] returns the degree of the multivariate polynomial p."

Projectivize::usage"Projectivize[p,v] returns the homogeneization of the polynomial p with additional variable v."

DegreePart::usage"DegreePart[p,d] returns the sum of the terms of homogeneous degree d of p."

GeometricGenus::usage"GeometricGenus[c] returns the geometric genus of the curve c defined by an irreducible polynomial,
 if c has a worst ordinary singularities".

OrdinarySingularityQ::usage"OrdinarySingularityQ[c,p] returns True if the curve c has an odrinary singularity at the point p."

NewtonPolygon::usage"NewtonPolygon[p] returns the points corresponding to the Newton polygon of p."

ShiftOrigin::usage""
(*-----------------------------------Function definitions------------------------------------------*)
Begin["Private`"]

(*Polynomial properties*)
PolynomialDegree[poly_]:=Max[Total/@CoefficientRules[poly][[All,1]]]

Projectivize[poly_,zvar_]:=Expand[zvar^PolynomialDegree[poly]poly/.Thread[Variables[poly]->Variables[poly]/zvar]]

DegreePart[poly_,d_]:=FromCoefficientRules[Select[CoefficientRules[poly,Variables[poly]],Total@#[[1]]==d&],Variables[poly]]

(*Points on curves*)
PointM[poly_]:=Min[Map[Total,CoefficientRules[poly,Variables[poly]][[All,1]]]]

PointM[poly_, point_]:=PointM[ShiftOrigin[poly,point]]

SingularPoints[poly_, cond_:0]:=Solve[Join[Table[D[poly,$v]==0,{$v,Variables[poly]}],{poly==0,cond==0}],Variables[poly][[;;]]]

ShiftOrigin[poly_, point_]:=ReplaceAll[poly,Thread[Variables[poly]->Variables[poly]+ReplaceAll[Variables[poly],point]]]

OrdinarySingularityQ[poly_,point_]:=Module[{vars=Variables[poly],part=DegreePart[ShiftOrigin[poly,point],PointM[poly,point]]},If[Exponent[part,vars[[1]]]>Exponent[part,vars[[2]]],
Module[{pol=(part/.{vars[[2]]->1})},0==Length[Solve[{pol,D[pol,vars[[1]]]}=={0,0},vars[[1]]]]],
Module[{pol=(part/.{vars[[1]]->1})},0==Length[Solve[{pol,D[pol,vars[[2]]]}=={0,0},vars[[2]]]]]]]

(*Global properties*)
GeometricGenus[poly_]:=If[IrreduciblePolynomialQ[poly],If[SingularQ[poly],
Module[{sing=SingularPoints[poly]},If[And@@(OrdinarySingularityQ[poly,#]&/@sing),
Binomial[PolynomialDegree[poly]-1,2]-Sum[Binomial[m,2],{m,PointM[poly,#]&/@sing}]]],
Binomial[PolynomialDegree[poly]-1,2]]]

SingularQ[poly_, cond_:0]:=(Length[SingularPoints[poly, cond]]>0)
Singular0Q[poly_]:=(PointM[poly]>1)

NewtonPolygon[poly_]:=CoefficientRules[poly,Variables[poly]][[All,1]]

(*Blow-ups and resolutions*)
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
