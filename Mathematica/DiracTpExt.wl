(* ::Package:: *)

(* ::Title:: *)
(*Dirac Transpose Extension*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracTpExt`", {"DiracCore`"}];


TPK;
TPB;
TPO;

DNTpExtRules;
Juxtapose;


Begin["Private`"];


DNTpExtRules = {};


(* ::Section:: *)
(*Notation*)


Format[TPK[B_]]:=\!\(\*SuperscriptBox[\(B\), 
SubscriptBox[\("\<T\>"\), \("\<K\>"\)]]\);
Format[TPB[K_]]:=\!\(\*SuperscriptBox[\(K\), 
SubscriptBox[\("\<T\>"\), \("\<B\>"\)]]\);
Format[TPO[O0_]]:=\!\(\*SuperscriptBox[\(O0\), 
SubscriptBox[\("\<T\>"\), \("\<O\>"\)]]\);


(* ::Section:: *)
(* Internal Symbol for Juxtaposition*)


JUX;
SetAttributes[JUX,{Orderless}];


(* ::Section:: *)
(*Rewriting Rules*)


(* ::Subsection:: *)
(*Trans-Ket*)


RuleTPK1 = TPK[ZEROB] -> ZEROK;
AppendTo[DNTpExtRules, RuleTPK1];

RuleTPK2 = TPK[BRA[s_]] -> KET[s];
AppendTo[DNTpExtRules, RuleTPK2];

RuleTPK3 = TPK[ADJK[K_]] -> ADJK[TPK[K]];
AppendTo[DNTpExtRules, RuleTPK3];

RuleTPK4 = TPK[TPK[K_]] -> K;
AppendTo[DNTpExtRules, RuleTPK4];

RuleTPK5 = TPK[S_ ~SCRB~ B_] -> S ~SCRK~ TPK[B];
AppendTo[DNTpExtRules, RuleTPK5];

RuleTPK6 = TPK[B1_ ~ADDB~ B2_] -> TPK[B1] ~ADDK~ TPK[B2];
AppendTo[DNTpExtRules, RuleTPK6];

RuleTPK7 = TPK[B0_ ~MLTB~ O0_] -> TPO[O0] ~MLTK~ TPK[B0];
AppendTo[DNTpExtRules, RuleTPK7];

RuleTPK8 = TPK[B1_ ~TSRB~ B2_] -> TPK[B1] ~TSRK~ TPK[B2];
AppendTo[DNTpExtRules, RuleTPK8];


(* ::Subsection:: *)
(*Trans-Bra*)


RuleTPB1 = TPB[ZEROK] -> ZEROB;
AppendTo[DNTpExtRules, RuleTPB1];

RuleTPB2 = TPB[KET[s_]] -> BRA[s];
AppendTo[DNTpExtRules, RuleTPB2];

RuleTPB3 = TPB[ADJB[B_]] -> ADJB[TPB[B]];
AppendTo[DNTpExtRules, RuleTPB3];

RuleTPB4 = TPB[TPB[B_]] -> B;
AppendTo[DNTpExtRules, RuleTPB4];

RuleTPB5 = TPB[S_ ~SCRK~ K_] -> S ~SCRB~ TPB[K];
AppendTo[DNTpExtRules, RuleTPB5];

RuleTPB6 = TPB[K1_ ~ADDK~ K2_] -> TPB[K1] ~ADDB~ TPB[K2];
AppendTo[DNTpExtRules, RuleTPB6];

RuleTPB7 = TPB[O0_ ~MLTK~ K0_] -> TPB[K0] ~MLTB~ TPO[O0];
AppendTo[DNTpExtRules, RuleTPB7];

RuleTPB8 = TPB[K1_ ~TSRK~ K2_] -> TPB[K1] ~TSRB~ TPB[K2];
AppendTo[DNTpExtRules, RuleTPB8];


(* ::Subsection:: *)
(*Trans-Opt*)


RuleTPO1 = TPO[ZEROO] -> ZEROO;
AppendTo[DNTpExtRules, RuleTPO1];

RuleTPO2 = TPO[ONEO] -> ONEO;
AppendTo[DNTpExtRules, RuleTPO2];

RuleTPO3 = TPO[K_ ~OUTER~ B_] -> TPK[B] ~OUTER~ TPB[K];
AppendTo[DNTpExtRules, RuleTPO3];

RuleTPO4 = TPO[ADJO[O0_]] -> ADJO[TPO[O0]];
AppendTo[DNTpExtRules, RuleTPO4];

RuleTPO5 = TPO[TPO[O0_]] -> O0;
AppendTo[DNTpExtRules, RuleTPO5];

RuleTPO6 = TPO[S0_ ~SCRO~ O0_] -> S0 ~SCRO~ TPO[O0];
AppendTo[DNTpExtRules, RuleTPO6];

RuleTPO7 = TPO[O1_ ~ADDO~ O2_] -> TPO[O1] ~ADDO~ TPO[O2];
AppendTo[DNTpExtRules, RuleTPO7];

RuleTPO8 = TPO[O1_ ~MLTO~ O2_] -> TPO[O2] ~MLTO~ TPO[O1];
AppendTo[DNTpExtRules, RuleTPO8];

RuleTPO9 = TPO[O1_ ~TSRO~ O2_] -> TPO[O1] ~TSRO~ TPO[O2];
AppendTo[DNTpExtRules, RuleTPO9];


(* Juxtaposition *)
Juxtapose[term_]:=term/.{B_~DOT~K_->JUX[B~DOT~K,TPB[K]~DOT~TPK[B]]};


End[];


EndPackage[];
