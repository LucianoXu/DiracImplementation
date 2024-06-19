(* ::Package:: *)

(* ::Title:: *)
(*Dirac All*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracAll`", {"Unification`", "DiracCore`", "DiracDeltaExt`", "DiracSumExt`", "DiracProjExt`","DiracProjSumExt`"}];


DNRules;
DNNorm;
DNEqQ;


Begin["Private`"];


(* The order matters *)
DNRules = Join[DNSetRules, DNProjRules, DNCoreRules, DNDeltaExtRules, DNSumPushRules, DNSumExtRules, DNProjSumRules];


(* Type checking is integrated into normalization *)
DNNorm[term_] := With[
	{},
	TypeDeduce[term];
	FullSimplify[
		DNEntryExpand[term//.DNRules]//.DNRules
		(*//.DNEntryReduceRules//.DNRules*)
	]
]


DNEqQ[term1_,term2_]:=
	Catch[Unify[DNNorm[term1], DNNorm[term2], {}] =!= False];


End[];


EndPackage[];
