(* ::Package:: *)

(* ::Title:: *)
(*Dirac All*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracAll`", {"DiracCore`", "DiracDeltaExt`", "DiracTpExt`", "DiracSumExt`"}];


DNRules;
DNNorm;
DNEqQ;


Begin["Private`"];


(* The order matters *)
DNRules = Join[DNSetRules, DNCoreRules, DNDeltaExtRules, DNTpExtRules, DNSumPushRules, DNSumExtRules];


DNNorm[term_]:=SumAlphaNorm[
		FullSimplify[Juxtapose[DNEntryExpand[term//.DNRules]//.DNRules//.DNEntryReduceRules//.DNRules]//.DNRules]
	];


DNEqQ[term1_,term2_]:=
	DNNorm[term1]===DNNorm[term2];


End[];


EndPackage[];
