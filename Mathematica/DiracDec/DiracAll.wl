(* ::Package:: *)

(* ::Title:: *)
(*Dirac All*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracAll`", 
	{
		"Unification`", "RewritingPlus`",
		"DiracCore`", 
		"DiracDeltaExt`", "DiracSumExt`", "DiracProjExt`","DiracProjSumExt`", "DiracUserLanguage`", "DiracBasisExpand`"
	}
];


DNRules;
DNNorm;
DNBasisExpandNorm;
DNEqQ;

DiracCBHook::usage="Define the callback hook that applies on the term at every step of rewriting.";
DNNormWithHook;


Begin["Private`"];


(* The order matters *)
DNRules = Join[DNSetRules, DNProjRules, DNCoreRules, DNDeltaExtRules, DNSumPushRules, DNSumExtRules, DNProjSumRules];
(* The Dispatch Optimization *)
DpDNBasisExpandRules = Dispatch[DNBasisExpandRules];


(* Type checking is integrated into normalization *)
DNNorm[term_, expandQ_, extraRules_] := With[
	{
		parsedTerm = DiracParse[term],
		DpDNRules = Dispatch[Join[extraRules, DNRules]]
	},
	TypeDeduce[parsedTerm];
	If[expandQ,
		FullSimplify[
			parsedTerm
			//InnermostReplaceAll[DpDNRules]
			//DNEntryExpand
			//InnermostReplaceAll[DpDNRules]
			(*//.DNEntryReduceRules//.DNRules*)
		],
		FullSimplify[
			parsedTerm
			//InnermostReplaceAll[DpDNRules]
		]
	]
];
DNNorm[term_] := DNNorm[term, True, {}];


DNBasisExpandNorm[term_, extraRules_] := With[
	{
		parsedTerm = DiracParse[term],
		DpDNRules = Dispatch[Join[extraRules, DNRules]]
	},
	TypeDeduce[parsedTerm];
	FullSimplify[
		parsedTerm
		//InnermostReplaceAll[DpDNRules]
		//DNEntryExpand
		//InnermostReplaceAll[DpDNRules]
		//InnermostReplaceAll[DpDNBasisExpandRules]
		//InnermostReplaceAll[DpDNRules]
		(*//.DNEntryReduceRules//.DNRules*)
	]
];
DNBasisExpandNorm[term_] := DNBasisExpandNorm[term, {}];


(* ::Text:: *)
(*This hook version is not updated to contain basis expand and extra rules.*)


DiracCBHook[term_] := term;
RewriteWithHook[term_]:= FixedPoint[ReplaceAll[DNRules][DiracCBHook[#]]&, term]; 
DNNormWithHook[term_] := With[
	{parsedTerm = DiracParse[term]},
	TypeDeduce[parsedTerm];
	FullSimplify[
		RewriteWithHook[DNEntryExpand[RewriteWithHook[parsedTerm]]]
	]
];


DNEqQ[term1_, term2_, expandQ_, extraRules_]:= Which[
	Catch[Unify[DNNorm[term1, expandQ, extraRules], DNNorm[term2, expandQ, extraRules], {}] =!= False],
	True,
	
	Catch[Unify[DNBasisExpandNorm[term1, extraRules], DNBasisExpandNorm[term2, extraRules], {}] =!= False],
	True,
	
	True,
	"MAYBE"];
	
DNEqQ[term1_, term2_] := DNEqQ[term1, term2, True, {}];


End[];


EndPackage[];


(* ::Chapter:: *)
(*TODO*)


(* ::Text:: *)
(*TODO: we should add alpha-equivalence to the equational theory of core language.*)
