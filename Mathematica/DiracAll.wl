(* ::Package:: *)

(* ::Title:: *)
(*Dirac All*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracAll`", {"Unification`", "DiracCore`", "DiracDeltaExt`", "DiracSumExt`"}];


DNRules;
DNNorm;
DNEqQ;


Begin["Private`"];


(* The order matters *)
DNRules = Join[DNSetRules, DNCoreRules, DNDeltaExtRules, DNSumPushRules, DNSumExtRules];


DNNorm[term_]:=FullSimplify[DNEntryExpand[term//.DNRules]//.DNRules//.DNEntryReduceRules//.DNRules];


DNEqQ[term1_,term2_]:=
	Unify[DNNorm[term1], DNNorm[term2], {}] =!= False;


End[];


EndPackage[];
