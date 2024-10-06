(* ::Package:: *)

(* ::Title:: *)
(*Dirac Notation Kronecker-Delta Extension*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracDeltaExt`",{"DiracCore`"}];


DNDeltaExtRules;


Begin["Private`"];


DNDeltaExtRules = {};


(* Check whether the equality is satisfiable. *)
EqUSatQ[a_, b_]:=Length[
	Quiet[
		Solve[a==b, Union[Cases[a==b, _Symbol, Infinity]]]
	]
]===0;

(* DELTAUSAT *)
RuleDeltaUSat = DELTA[a_, b_]/;EqUSatQ[a, b] -> CPX[0];
AppendTo[DNDeltaExtRules, RuleDeltaUSat];


End[];


EndPackage[];
