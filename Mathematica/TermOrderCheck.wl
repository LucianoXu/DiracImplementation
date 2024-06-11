(* ::Package:: *)

(* ::Title:: *)
(*Termination Order Check*)


BeginPackage["TermOrderCheck`"];


ClosureCheck;
OrderCheck;
OrderCheckDerivative;
RuleOrderCheckDerivative;


Begin["Private`"];


ClosureCheck[term_, lb_, assum_] := With[
	{res=FullSimplify[term >= lb,assum]},
	If[res =!= True, 
		Throw[
			{
				"Closure Check Error:\n",
				Hold[term>lb],
				"\nSimplified Result:\n",
				res,
				"\nCalculated Term:\n",
				term
			}
		]
	]
];
ClosureCheck[___] := Throw["Invalid Arguments"];

OrderCheck[lhs_, rhs_, assum_] := With[
	{res=FullSimplify[lhs > rhs, assum]},
	If[res =!= True, 
		Throw[
			{
				"Order Check Error:\n",
				Hold[lhs>rhs],
				"\nSimplified Result:\n",
				res,
				"\nCalculated LHS:\n",
				lhs,
				"\nCalculated RHS:\n",
				rhs
			}
		]
	]
];
OrderCheck[___] := Throw["Invalid Arguments"];

OrderCheckDerivative[lhs_, rhs_, vars_, lb_]:=
	With[
	{
		init=(lhs-rhs)/.Thread[vars->Table[lb,Length[vars]]],
		derivatives=D[lhs-rhs,{vars}]
	},
	If[
		!(TrueQ[init>0] && AllTrue[FullSimplify[#>=0&/@derivatives,(#>=lb&&Element[#,Integers])&/@vars], TrueQ]),
		Throw[
			{
				"Order Check Derivatives Error:\n",
				"LHS:\n",
				lhs,
				"\nRHS:\n",
				rhs,
				"\nlower bound: ", lb,
				"\nInit: ", init,
				"\nDerivatives:\n",
				derivatives
			}
		]
	]
];
OrderCheckDerivative[___] := Throw["Invalid Arguments"];


RuleOrderCheckDerivative[P_, rule_, lb_] := Module[
	{vars, lhs, rhs},
	vars = Union[Cases[rule[[1]], p_Pattern :> p[[1]], Infinity]];
	lhs = rule[[1]]//.(p_Pattern :> p[[1]]);
	rhs = rule[[2]];
	OrderCheckDerivative[P[lhs], P[rhs], P[#]&/@vars, lb]
]
RuleOrderCheckDerivative[___] := Throw["Invalid Arguments"];


End[];


EndPackage[];
