(* ::Package:: *)

(* ::Title:: *)
(*Dirac Notation First-Second Extension*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracProjExt`",{"DiracCore`"}];


FST;
SND;
DNProjRules;


Begin["Private`"];


AppendTo[DiracSymbols, FST];
AppendTo[DiracSymbols, SND];


(* ::Section:: *)
(*Type Checking Rules*)


TypeDeduce[FST[s_]] := TypeChecking[FSTTyping[TypeDeduce[s]]];
TypeChecking[FSTTyping[sigma1_ ~ProdType~ sigma2_]] := sigma1;

TypeDeduce[SND[s_]] := TypeChecking[SNDTyping[TypeDeduce[s]]];
TypeChecking[SNDTyping[sigma1_ ~ProdType~ sigma2_]] := sigma2;


(* ::Section:: *)
(*Type Calculations*)


TProj1[ProdType[T1_, T2_]]:=T1;
TProj2[ProdType[T1_, T2_]]:=T2;

TCalc[FST[s_]]:=TProj1[TCalc[s]];
TCalc[SND[s_]]:=TProj2[TCalc[s]];


(* ::Section:: *)
(*Rewriting Rules*)


DNProjRules = {};


(* ::Subsection:: *)
(*Basis*)


RuleBasis1Proj = FST[PAIR[s_, t_]] -> s;
AppendTo[DNProjRules, RuleBasis1Proj];

RuleBasis2Proj = SND[PAIR[s_, t_]] -> t;
AppendTo[DNProjRules, RuleBasis2Proj];

RuleBasis3Proj = PAIR[FST[t_], SND[t_]] -> t;
AppendTo[DNProjRules, RuleBasis3Proj];


(* ::Subsection:: *)
(*Delta*)


RuleDelta2Proj = DELTA[s_, PAIR[t1_, t2_]] -> DELTA[FST[s], t1] ~MLTS~ DELTA[SND[s], t2];
AppendTo[DNProjRules, RuleDelta2Proj];

RuleDelta3Proj = DELTA[FST[s_], FST[t_]] ~MLTS~ DELTA[SND[s_], SND[t_]] -> DELTA[s, t];
AppendTo[DNProjRules, RuleDelta3Proj];


(* ::Subsection:: *)
(*Decompose*)


RuleScalar23Proj = (B1_ ~TSRB~ B2_) ~DOT~ KET[t_] -> (B1 ~DOT~ KET[FST[t]]) ~MLTS~ (B2 ~DOT~ KET[SND[t]]);
AppendTo[DNProjRules, RuleScalar23Proj];


RuleScalar24Proj = BRA[t_] ~DOT~ (K1_ ~TSRK~ K2_) -> (BRA[FST[t]] ~DOT~ K1) ~MLTS~ (BRA[SND[t]] ~DOT~ K2);
AppendTo[DNProjRules, RuleScalar24Proj];


RuleScalar27Proj = BRA[s_] ~DOT~ ((O1_ ~TSRO~ O2_) ~MLTK~ K0_) -> ((BRA[FST[s]] ~MLTB~ O1) ~TSRB~ (BRA[SND[s]] ~MLTB~ O2)) ~DOT~ K0;
AppendTo[DNProjRules, RuleScalar27Proj];


RuleMLTK11Proj = (O1_ ~TSRO~ O2_) ~MLTK~ KET[t_] -> (O1 ~MLTK~ KET[FST[t]]) ~TSRK~ (O2 ~MLTK~ KET[SND[t]]);
AppendTo[DNProjRules, RuleMLTK11Proj];


RuleMLTB11Proj = BRA[t_] ~MLTB~ (O1_ ~TSRO~ O2_) -> (BRA[FST[t]] ~MLTB~ O1) ~TSRB~ (BRA[SND[t]] ~MLTB~ O2);
AppendTo[DNProjRules, RuleMLTB11Proj];


End[];


EndPackage[];
