(* ::Package:: *)

(* ::Title:: *)
(*Dirac Notation Core Language*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracCore`"];


(* ::Section:: *)
(*Public Interface*)


DiracSymbols::usage="The symbols for Dirac notation";

DiracCtx::usage="Defin the rewriting rules to specify the context for DiracCtx";

(* The kind symbols *)
AtomKind;
ProdKind;
ScalarKind;
KetKind;
BraKind;
OpKind;

(* The type symbols *)
ProdType;
TProj1;
TProj2;
TProjK;
TProjB;
SType;
KType;
BType;
OType;
TCalc;

InDiracCtxQ::usage = "Check whether the term is in the Dirac notation context.";
TypeDeduce::usage = "Check the typing of the terms according to the DiracCtx.";
TypeChecking;
TypingRules;


(* The term symbols *)
PAIR;

CPX;
DELTA;
ADDS;
MLTS;
CONJS;
DOT;

ZEROK;
KET;
ADJK;
SCRK;
ADDK;
MLTK;
TSRK;

ZEROB;
BRA;
ADJB;
SCRB;
ADDB;
MLTB;
TSRB;

ZEROO;
ONEO;
OUTER;
ADJO;
SCRO;
ADDO;
MLTO;
TSRO;

DNCoreRules;


Begin["Private`"];


DiracSymbols={
ProdType, TProj1, TProj2, TProjK, TProjB, SType, KType, BType, OType, TCalc,
PAIR,
CPX, DELTA, ADDS, MLTS, CONJS, DOT,
ZEROK, KET, ADJK, SCRK, ADDK, MLTK, TSRK,
ZEROB, BRA, ADJB, SCRB, ADDB, MLTB, TSRB,
ZEROO, ONEO, OUTER, ADJO, SCRO, ADDO, MLTO, TSRO
};


(* ::Section:: *)
(*Notation*)


Format[DELTA[t1_, t2_]]:=Subscript["\[Delta]", t1,t2];
Format[A_ ~ADDS~ B_]:=Row[{"(", A, "\!\(\*SubscriptBox[\(+\), \(S\)]\)", B, ")"}];
Format[A_ ~MLTS~ B_]:=Row[{"(", A, "\!\(\*SubscriptBox[\(\[Times]\), \(S\)]\)", B, ")"}];
Format[CONJS[A_]]:=SuperStar[A];
Format[A_ ~DOT~ B_]:=Row[{"(", A, "\!\(\*SubscriptBox[\(\[CenterDot]\), \(S\)]\)", B, ")"}];

Format[ZEROK]:=\!\(\*SubscriptBox[\(0\), \("\<K\>"\)]\);
Format[KET[s_]]:=Ket[{s}];
Format[ADJK[B_]]:=\!\(\*SuperscriptBox[\(B\), 
SubscriptBox[\("\<\[Dagger]\>"\), \("\<K\>"\)]]\);
Format[S_ ~SCRK~ K_]:=Row[{"(", S, K, ")"}];
Format[K1_ ~ADDK~ K2_]:=Row[{"(", K1, "\!\(\*SubscriptBox[\(+\), \(K\)]\)", K2, ")"}];
Format[O0_ ~MLTK~ K_]:=Row[{"(", O0, "\!\(\*SubscriptBox[\(\[CenterDot]\), \(K\)]\)", K, ")"}];
Format[K1_ ~TSRK~ K2_]:=Row[{"(", K1, "\[CircleTimes]\!\(\*SubscriptBox[\(\\\ \), \(K\)]\)", K2, ")"}];

Format[ZEROB]:=\!\(\*SubscriptBox[\(0\), \("\<B\>"\)]\);
Format[BRA[s_]]:=Bra[{s}];
Format[ADJB[K_]]:=\!\(\*SuperscriptBox[\(K\), 
SubscriptBox[\("\<\[Dagger]\>"\), \("\<B\>"\)]]\);
Format[S_ ~SCRB~ B_]:=Row[{"(", S, B, ")"}];
Format[B1_ ~ADDB~ B2_]:=Row[{"(", B1, "\!\(\*SubscriptBox[\(+\), \(B\)]\)", B2, ")"}];
Format[B_ ~MLTB~ O0_]:=Row[{"(", B, "\!\(\*SubscriptBox[\(\[CenterDot]\), \(B\)]\)", O0, ")"}];
Format[B1_ ~TSRB~ B2_]:=Row[{"(", B1, "\[CircleTimes]\!\(\*SubscriptBox[\(\\\ \), \(B\)]\)", B2, ")"}];

Format[ZEROO]:=\!\(\*SubscriptBox[\(0\), \("\<O\>"\)]\);
Format[ONEO]:=\!\(\*SubscriptBox[\(1\), \("\<O\>"\)]\);
Format[K_ ~OUTER ~ B_]:=Row[{"(", K, "\[CircleTimes]\!\(\*SubscriptBox[\(\\\ \), \(P\)]\)", B, ")"}];
Format[ADJO[O0_]]:=\!\(\*SuperscriptBox[\(O0\), 
SubscriptBox[\("\<\[Dagger]\>"\), \("\<O\>"\)]]\);
Format[S_ ~SCRO~ O0_]:=Row[{"(", S, O0, ")"}];
Format[O1_ ~ADDO~ O2_]:=Row[{"(", O1, "\!\(\*SubscriptBox[\(+\), \(O\)]\)", O2, ")"}];
Format[O1_ ~MLTO~ O2_]:=Row[{"(", O1, "\!\(\*SubscriptBox[\(\[CenterDot]\), \(O\)]\)", O2, ")"}];
Format[O1_ ~TSRO~ O2_]:=Row[{"(", O1, "\[CircleTimes]\!\(\*SubscriptBox[\(\\\ \), \(O\)]\)", O2, ")"}];


(* ::Section:: *)
(*Setting Attributes*)


(* Avoid unnecessary computations *)
(*SetAttributes[CPX,HoldAll];*)
SetAttributes[DELTA, Orderless];
SetAttributes[{ADDS, MLTS, ADDK, ADDB, ADDO}, {Orderless, Flat, OneIdentity}];


(* ::Section:: *)
(*Context Operation*)


(*UniqueAndUpdate[T_]:=With[{nv=Unique[]}, AppendTo[DiracCtx,nv->T]; nv];*)


(* ::Section:: *)
(*Type Checking Rules*)


DiracCtx = {};

InDiracCtxQ[term_] := MatchQ[term, Alternatives@@First/@DiracCtx];

TypingRules = {};

TypeDeduce[v_?InDiracCtxQ]:=v/.DiracCtx;
TypeDeduce[e_]:=Throw[{"Type Checking Error: ", e, "Context: ", DiracCtx}];
TypeChecking[e_]:=Throw[{"Type Checking Error: ", e, "Context: ", DiracCtx}];

TypeDeduce[sigma1_ ~ProdType~ sigma2_] := TypeDeduce[sigma1] ~ProdKind~ TypeDeduce[sigma2];
TypeDeduce[SType] := ScalarKind;
TypeDeduce[KType[sigma_]] := KType[TypeDeduce[sigma]];
TypeDeduce[BType[sigma_]] := BType[TypeDeduce[sigma]];
TypeDeduce[OType[sigma_, tau_]] := OType[TypeDeduce[sigma], TypeDeduce[tau]];

(* Basis *)
TypeDeduce[PAIR[s_, t_]] := TypeDeduce[s] ~ProdType~ TypeDeduce[t];

(* Scalar *)
TypeDeduce[CPX[alpha_]] := SType;

TypeDeduce[DELTA[s_, t_]] := TypeChecking[DELTATyping[TypeDeduce[s], TypeDeduce[t]]];
TypeChecking[DELTATyping[T_, T_]] := SType;

TypeDeduce[ADDS[args__]] := TypeChecking[ADDSTyping@@TypeDeduce/@{args}];
TypeChecking[ADDSTyping[SType..]] := SType;

TypeDeduce[MLTS[args__]] := TypeChecking[MLTSTyping@@TypeDeduce/@{args}];
TypeChecking[MLTSTyping[SType..]] := SType;

TypeDeduce[CONJS[S_]] := TypeChecking[CONJSTyping[TypeDeduce[S]]];
TypeChecking[CONJSTyping[SType]] := SType;

TypeDeduce[B_ ~DOT~ K_] := TypeChecking[TypeDeduce[B] ~DOTTyping~ TypeDeduce[K]];
TypeChecking[BType[T_] ~DOTTyping~ KType[T_]] := SType;

(* Ket *)
TypeDeduce[ZEROK[sigma_]] := KType[sigma];

TypeDeduce[KET[s_]] := KType[TypeDeduce[s]];

TypeDeduce[ADJK[B_]] := TypeChecking[ADJKTyping[TypeDeduce[B]]];
TypeChecking[ADJKTyping[BType[sigma_]]] := KType[sigma];

TypeDeduce[S_ ~SCRK~ K_] := TypeChecking[TypeDeduce[S] ~SCRKTyping~ TypeDeduce[K]];
TypeChecking[SType ~SCRKTyping~ KType[sigma_]] := KType[sigma];

TypeDeduce[ADDK[args__]] := TypeChecking[ADDKTyping@@TypeDeduce/@{args}];
TypeChecking[ADDKTyping[(KType[sigma_])..]] := KType[sigma];

TypeDeduce[O0_ ~MLTK~ K_] := TypeChecking[TypeDeduce[O0] ~MLTKTyping~ TypeDeduce[K]];
TypeChecking[OType[sigma_, tau_] ~MLTKTyping~ KType[tau_]] := KType[sigma];

TypeDeduce[K1_ ~TSRK~ K2_] := TypeChecking[TypeDeduce[K1] ~TSRKTyping~ TypeDeduce[K2]];
TypeChecking[KType[sigma_] ~TSRKTyping~ KType[tau_]] := KType[sigma ~ProdType~ tau];

(* Bra *)
TypeDeduce[ZEROB[sigma_]] := BType[sigma];

TypeDeduce[BRA[s_]] := BType[TypeDeduce[s]];

TypeDeduce[ADJB[K_]] := TypeChecking[ADJBTyping[TypeDeduce[K]]];
TypeChecking[ADJBTyping[KType[sigma_]]] := BType[sigma];

TypeDeduce[S_ ~SCRB~ B_] := TypeChecking[TypeDeduce[S] ~SCRBTyping~ TypeDeduce[B]];
TypeChecking[SType ~SCRBTyping~ BType[sigma_]] := BType[sigma];

TypeDeduce[ADDB[args__]] := TypeChecking[ADDBTyping@@TypeDeduce/@{args}];
TypeChecking[ADDBTyping[(BType[sigma_])..]] := BType[sigma];

TypeDeduce[B_ ~MLTB~ O0_] := TypeChecking[TypeDeduce[B] ~MLTBTyping~ TypeDeduce[O0]];
TypeChecking[BType[sigma_] ~MLTBTyping~ OType[sigma_, tau_]] := BType[tau];

TypeDeduce[B1_ ~TSRB~ B2_] := TypeChecking[TypeDeduce[B1] ~TSRBTyping~ TypeDeduce[B2]];
TypeChecking[BType[sigma_] ~TSRBTyping~ BType[tau_]] := BType[sigma ~ProdType~ tau];

(* Operator *)

TypeDeduce[ZEROO[sigma_, tau_]] := OType[sigma, tau];

TypeDeduce[ONEO[sigma_]] := OType[sigma, sigma];

TypeDeduce[K_ ~OUTER~ B_] := TypeChecking[TypeDeduce[K] ~OUTERTyping~ TypeDeduce[B]];
TypeChecking[KType[sigma_] ~OUTERTyping~ BType[tau_]] := OType[sigma, tau];

TypeDeduce[ADJO[O0_]] := TypeChecking[ADJOTyping[TypeDeduce[O0]]];
TypeChecking[ADJOTyping[OType[sigma_, tau_]]] := OType[tau, sigma];

TypeDeduce[S_ ~SCRO~ O0_] := TypeChecking[TypeDeduce[S] ~SCROTyping~ TypeDeduce[O0]];
TypeChecking[SType ~SCROTyping~ OType[sigma_, tau_]] := OType[sigma, tau];

TypeDeduce[ADDO[args__]] := TypeChecking[ADDOTyping@@TypeDeduce/@{args}];
TypeChecking[ADDOTyping[(OType[sigma_, tau_])..]] := OType[sigma, tau];

TypeDeduce[O1_ ~MLTO~ O2_] := TypeChecking[TypeDeduce[O1] ~MLTOTyping~ TypeDeduce[O2]];
TypeChecking[OType[sigma_, tau_] ~MLTOTyping~ OType[tau_, rho_]] := OType[sigma, rho];

TypeDeduce[O1_ ~TSRO~ O2_] := TypeChecking[TypeDeduce[O1] ~TSROTyping~ TypeDeduce[O2]];
TypeChecking[OType[sigma1_, tau1_] ~TSROTyping~ OType[sigma2_, tau2_]] := OType[sigma1 ~ProdType~ sigma2, tau1 ~ProdType~ tau2];


(* ::Section:: *)
(*Type Calculations*)


TProjK[KType[T_]]:=T;
TProjB[BType[T_]]:=T;
TProjK[OType[T1_, T2_]]:=T1;
TProjB[OType[T1_, T2_]]:=T2;

TCalc[a_?InDiracCtxQ]:=a/.DiracCtx;
(*TCalc[a_/;MatchQ[a, DefinedPatterns]]:=With[{},Print[a];Print[DiracCtx];a/.DiracCtx];*)
TCalc[PAIR[s_, t_]]:=TCalc[s] ~ProdType~ TCalc[t];

TCalc[CPX[_]]:=SType;
TCalc[DELTA[_, _]]:=SType;
TCalc[_ ~ADDS~ _]:=SType;
TCalc[_ ~MLTS~ _]:=SType;
TCalc[CONJS[_]]:=SType;
TCalc[_ ~DOT~ _]:=SType;

TCalc[ZEROK[sigma_]]:=KType[sigma];
TCalc[KET[s_]]:=KType[TCalc[s]];
TCalc[ADJK[B_]]:=KType[TProjB[TCalc[B]]];
TCalc[_ ~SCRK~ K_]:=TCalc[K];
TCalc[K_ ~ADDK~ _]:=TCalc[K];
TCalc[O0_ ~MLTK~ _]:=KType[TProjK[TCalc[O0]]];
TCalc[K1_ ~TSRK~ K2_]:=KType[TProjK[TCalc[K1]] ~ProdType~ TProjK[TCalc[K2]]];

TCalc[ZEROB[sigma_]]:=BType[sigma];
TCalc[BRA[s_]]:=BType[TCalc[s]];
TCalc[ADJB[K_]]:=BType[TProjK[TCalc[K]]];
TCalc[_ ~SCRB~ B_]:=TCalc[B];
TCalc[B_ ~ADDB~ _]:=TCalc[B];
TCalc[_ ~MLTB~ O0_]:=BType[TProjB[TCalc[O0]]];
TCalc[B1_ ~TSRB~ B2_]:=BType[TProjB[TCalc[B1]] ~ProdType~ TProjB[TCalc[B2]]];

TCalc[ZEROO[sigma_, tau_]]:=OType[sigma, tau];
TCalc[ONEO[sigma_]]:=OType[sigma, sigma];
TCalc[K_ ~OUTER~ B_]:=OType[TProjK[TCalc[K]], TProjB[TCalc[B]]];
TCalc[ADJO[O0_]]:=OType[TProjB[TCalc[O0]], TProjK[TCalc[O0]]];
TCalc[_ ~SCRO~ O0_]:=TCalc[O0];
TCalc[O0_ ~ADDO~ _]:=TCalc[O0];
TCalc[O1_ ~MLTO~ O2_]:=OType[TProjK[TCalc[O1]], TProjB[TCalc[O2]]];
TCalc[O1_ ~TSRO~ O2_]:=OType[
	TProjK[TCalc[O1]] ~ProdType~ TProjK[TCalc[O2]], 
	TProjB[TCalc[O1]] ~ProdType~ TProjB[TCalc[O2]]
];




(* ::Section:: *)
(*Rewriting Rules*)


DNCoreRules={};


(* ::Subsection:: *)
(*Delta*)


RuleDelta1 = DELTA[s_, s_] -> CPX[1];
AppendTo[DNCoreRules, RuleDelta1];

RuleDelta2 = DELTA[PAIR[s1_, s2_], PAIR[t1_, t2_]] -> DELTA[s1, t1] ~MLTS~ DELTA[s2, t2];
AppendTo[DNCoreRules, RuleDelta2];


(* ::Subsection:: *)
(*Scalars*)


RuleScalar1 = CPX[0] ~ADDS~ a_ -> a;
AppendTo[DNCoreRules, RuleScalar1];


RuleScalar2 = CPX[a_] ~ADDS~ CPX[b_] -> CPX[a + b];
AppendTo[DNCoreRules, RuleScalar2];


RuleScalar3 = S0_ ~ADDS~ S0_ -> CPX[1 + 1] ~MLTS~ S0;
AppendTo[DNCoreRules, RuleScalar3];


RuleScalar4 = (CPX[a_] ~MLTS~ S0_) ~ADDS~ S0_ -> CPX[a + 1] ~MLTS~ S0;
AppendTo[DNCoreRules, RuleScalar4];


RuleScalar5 = (CPX[a_] ~MLTS~ S0_) ~ADDS~ (CPX[b_] ~MLTS~ S0_) -> CPX[a + b] ~MLTS~ S0;
AppendTo[DNCoreRules, RuleScalar5];


RuleScalar6 = CPX[0] ~MLTS~ a_ -> CPX[0];
AppendTo[DNCoreRules, RuleScalar6];


RuleScalar7 = CPX[1] ~MLTS~ a_ -> a;
AppendTo[DNCoreRules, RuleScalar7];


RuleScalar8 = CPX[a_] ~MLTS~ CPX[b_] -> CPX[a * b];
AppendTo[DNCoreRules, RuleScalar8];


RuleScalar9 = S1_ ~MLTS~ (S2_ ~ADDS~ S3_) -> (S1 ~MLTS~ S2) ~ADDS~ (S1 ~MLTS~ S3);
AppendTo[DNCoreRules, RuleScalar9];


RuleScalar10 = CONJS[CPX[a_]] -> CPX[Conjugate[a]];
AppendTo[DNCoreRules, RuleScalar10];


RuleScalar11 = CONJS[DELTA[s_, t_]] -> DELTA[s, t];
AppendTo[DNCoreRules, RuleScalar11];


RuleScalar12 = CONJS[S1_ ~ADDS~ S2_] -> CONJS[S1] ~ADDS~ CONJS[S2];
AppendTo[DNCoreRules, RuleScalar12];


RuleScalar13 = CONJS[S1_ ~MLTS~ S2_] -> CONJS[S1] ~MLTS~ CONJS[S2];
AppendTo[DNCoreRules, RuleScalar13];


RuleScalar14 = CONJS[CONJS[S0_]] -> S0;
AppendTo[DNCoreRules, RuleScalar14];


RuleScalar15 = CONJS[B0_ ~DOT~ K0_] -> ADJB[K0] ~DOT~ ADJK[B0];
AppendTo[DNCoreRules, RuleScalar15];


RuleScalar16 = ZEROB[sigma_] ~DOT~ K0_ -> CPX[0];
AppendTo[DNCoreRules, RuleScalar16];


RuleScalar17 = B0_ ~DOT~ ZEROK[sigma_] -> CPX[0];
AppendTo[DNCoreRules, RuleScalar17];


RuleScalar18 = (S0_ ~SCRB~ B0_) ~DOT~ K0_ -> S0 ~MLTS~ (B0 ~DOT~ K0);
AppendTo[DNCoreRules, RuleScalar18];


RuleScalar19 = B0_ ~DOT~ (S0_ ~SCRK~ K0_) -> S0 ~MLTS~ (B0 ~DOT~ K0);
AppendTo[DNCoreRules, RuleScalar19];


RuleScalar20 = (B1_ ~ADDB~ B2_) ~DOT~ K0_ -> (B1 ~DOT~ K0) ~ADDS~ (B2 ~DOT~ K0);
AppendTo[DNCoreRules, RuleScalar20];


RuleScalar21 = B0_ ~DOT~ (K1_ ~ADDK~ K2_) -> (B0 ~DOT~ K1) ~ADDS~ (B0 ~DOT~ K2);
AppendTo[DNCoreRules, RuleScalar21];


RuleScalar22 = BRA[s_] ~DOT~ KET[t_] -> DELTA[s, t];
AppendTo[DNCoreRules, RuleScalar22];


RuleScalar23 = (B1_ ~TSRB~ B2_) ~DOT~ KET[PAIR[s_, t_]] -> (B1 ~DOT~ KET[s]) ~MLTS~ (B2 ~DOT~ KET[t]);
AppendTo[DNCoreRules, RuleScalar23];


RuleScalar24 = BRA[PAIR[s_, t_]] ~DOT~ (K1_ ~TSRK~ K2_) -> (BRA[s] ~DOT~ K1) ~MLTS~ (BRA[t] ~DOT~ K2);
AppendTo[DNCoreRules, RuleScalar24];


RuleScalar25 = (B1_ ~TSRB~ B2_) ~DOT~ (K1_ ~TSRK~ K2_) -> (B1 ~DOT~ K1) ~MLTS~ (B2 ~DOT~ K2);
AppendTo[DNCoreRules, RuleScalar25];


RuleScalar26 = (B0_ ~MLTB~ O0_) ~DOT~ K0_ -> B0 ~DOT~ (O0 ~MLTK~ K0);
AppendTo[DNCoreRules, RuleScalar26];


RuleScalar27 = BRA[PAIR[s_, t_]] ~DOT~ ((O1_ ~TSRO~ O2_) ~MLTK~ K0_) -> ((BRA[s] ~MLTB~ O1) ~TSRB~ (BRA[t] ~MLTB~ O2)) ~DOT~ K0;
AppendTo[DNCoreRules, RuleScalar27];


RuleScalar28 = (B1_ ~TSRB~ B2_) ~DOT~ ((O1_ ~TSRO~ O2_) ~MLTK~ K0_) -> ((B1 ~MLTB~ O1) ~TSRB~ (B2 ~MLTB~ O2)) ~DOT~ K0;
AppendTo[DNCoreRules, RuleScalar28];


(* ::Subsection:: *)
(*Ket and Bra*)


(* ::Subsubsection:: *)
(*ADJK/ADJB*)


RuleADJK1 = ADJK[ZEROB[sigma_]] -> ZEROK[sigma];
AppendTo[DNCoreRules, RuleADJK1];


RuleADJK2 = ADJK[BRA[t_]] -> KET[t];
AppendTo[DNCoreRules, RuleADJK2];


RuleADJK3 = ADJK[ADJB[K0_]] -> K0;
AppendTo[DNCoreRules, RuleADJK3];


RuleADJK4 = ADJK[S0_ ~SCRB~ B0_] -> CONJS[S0] ~SCRK~ ADJK[B0];
AppendTo[DNCoreRules, RuleADJK4];


RuleADJK5 = ADJK[B1_ ~ADDB~ B2_] -> ADJK[B1] ~ADDK~ ADJK[B2];
AppendTo[DNCoreRules, RuleADJK5];


RuleADJK6 = ADJK[B0_ ~MLTB~ O0_] -> ADJO[O0] ~MLTK~ ADJK[B0];
AppendTo[DNCoreRules, RuleADJK6];


RuleADJK7 = ADJK[B1_ ~TSRB~ B2_] -> ADJK[B1] ~TSRK~ ADJK[B2];
AppendTo[DNCoreRules, RuleADJK7];


RuleADJB1 = ADJB[ZEROK[sigma_]] -> ZEROB[sigma];
AppendTo[DNCoreRules, RuleADJB1];


RuleADJB2 = ADJB[KET[t_]] -> BRA[t];
AppendTo[DNCoreRules, RuleADJB2];


RuleADJB3 = ADJB[ADJK[B0_]] -> B0;
AppendTo[DNCoreRules, RuleADJB3];


RuleADJB4 = ADJB[S0_ ~SCRK~ K0_] -> CONJS[S0] ~SCRB~ ADJB[K0];
AppendTo[DNCoreRules, RuleADJB4];


RuleADJB5 = ADJB[K1_ ~ADDK~ K2_] -> ADJB[K1] ~ADDB~ ADJB[K2];
AppendTo[DNCoreRules, RuleADJB5];


RuleADJB6 = ADJB[O0_ ~MLTK~ K0_] -> ADJB[K0] ~MLTB~ ADJO[O0];
AppendTo[DNCoreRules, RuleADJB6];


RuleADJB7 = ADJB[K1_ ~TSRK~ K2_] -> ADJB[K1] ~TSRB~ ADJB[K2];
AppendTo[DNCoreRules, RuleADJB7];


(* ::Subsubsection:: *)
(*SCRK/SCRB*)


RuleSCRK1 = CPX[0] ~SCRK~ K0_ :> ZEROK[TProjK[TCalc[K0]]];
AppendTo[DNCoreRules, RuleSCRK1];


RuleSCRK2 = CPX[1] ~SCRK~ K0_ -> K0;
AppendTo[DNCoreRules, RuleSCRK2];


RuleSCRK3 = S0_ ~SCRK~ ZEROK[sigma_] -> ZEROK[sigma];
AppendTo[DNCoreRules, RuleSCRK3];


RuleSCRK4 = S1_ ~SCRK~ (S2_ ~SCRK~ K0_) -> (S1 ~MLTS~ S2) ~SCRK~ K0;
AppendTo[DNCoreRules, RuleSCRK4];


RuleSCRK5 = S0_ ~SCRK~ (K1_ ~ADDK~ K2_) -> (S0 ~SCRK~ K1) ~ADDK~ (S0 ~SCRK~ K2);
AppendTo[DNCoreRules, RuleSCRK5];


RuleSCRB1 = CPX[0] ~SCRB~ B0_ -> ZEROB[TProjB[TCalc[B0]]];
AppendTo[DNCoreRules, RuleSCRB1];


RuleSCRB2 = CPX[1] ~SCRB~ B0_ -> B0;
AppendTo[DNCoreRules, RuleSCRB2];


RuleSCRB3 = S0_ ~SCRB~ ZEROB[sigma_] -> ZEROB[sigma];
AppendTo[DNCoreRules, RuleSCRB3];


RuleSCRB4 = S1_ ~SCRB~ (S2_ ~SCRB~ B0_) -> (S1 ~MLTS~ S2) ~SCRB~ B0;
AppendTo[DNCoreRules, RuleSCRB4];


RuleSCRB5 = S0_ ~SCRB~ (B1_ ~ADDB~ B2_) -> (S0 ~SCRB~ B1) ~ADDB~ (S0 ~SCRB~ B2);
AppendTo[DNCoreRules, RuleSCRB5];


(* ::Subsubsection:: *)
(*ADDK/ADDB*)


RuleADDK1 = K0_ ~ADDK~ ZEROK[sigma_] -> K0;
AppendTo[DNCoreRules, RuleADDK1];


RuleADDK2 = K0_ ~ADDK~ K0_ -> CPX[1 + 1] ~SCRK~ K0;
AppendTo[DNCoreRules, RuleADDK2];


RuleADDK3 = (S0_ ~SCRK~ K0_) ~ADDK~ K0_ -> (S0 ~ADDS~ CPX[1]) ~SCRK~ K0;
AppendTo[DNCoreRules, RuleADDK3];


RuleADDK4 = (S1_ ~SCRK~ K0_) ~ADDK~ (S2_ ~SCRK~ K0_) -> (S1 ~ADDS~ S2) ~SCRK~ K0;
AppendTo[DNCoreRules, RuleADDK4];


RuleADDB1 = B0_ ~ADDB~ ZEROB[sigma_] -> B0;
AppendTo[DNCoreRules, RuleADDB1];


RuleADDB2 = B0_ ~ADDB~ B0_ -> CPX[1 + 1] ~SCRB~ B0;
AppendTo[DNCoreRules, RuleADDB2];


RuleADDB3 = (S0_ ~SCRB~ B0_) ~ADDB~ B0_ -> (S0 ~ADDS~ CPX[1]) ~SCRB~ B0;
AppendTo[DNCoreRules, RuleADDB3];


RuleADDB4 = (S1_ ~SCRB~ B0_) ~ADDB~ (S2_ ~SCRB~ B0_) -> (S1 ~ADDS~ S2) ~SCRB~ B0;
AppendTo[DNCoreRules, RuleADDB4];


(* ::Subsubsection:: *)
(*MLTK/MLTB*)


RuleMLTK1 = ZEROO[sigma_,tau_] ~MLTK~ K0_ -> ZEROK[sigma];
AppendTo[DNCoreRules, RuleMLTK1];


RuleMLTK2 = O0_ ~MLTK~ ZEROK[sigma_] :> ZEROK[TProjK[TCalc[O0]]];
AppendTo[DNCoreRules, RuleMLTK2];


RuleMLTK3 = ONEO[sigma_] ~MLTK~ K0_ -> K0;
AppendTo[DNCoreRules, RuleMLTK3];


RuleMLTK4 = (S0_ ~SCRO~ O0_) ~MLTK~ K0_ -> S0 ~SCRK~ (O0 ~MLTK~ K0);
AppendTo[DNCoreRules, RuleMLTK4];


RuleMLTK5 = O0_ ~MLTK~ (S0_ ~SCRK~ K0_) -> S0 ~SCRK~ (O0 ~MLTK~ K0);
AppendTo[DNCoreRules, RuleMLTK5];


RuleMLTK6 = (O1_ ~ADDO~ O2_) ~MLTK~ K0_ -> (O1 ~MLTK~ K0) ~ADDK~ (O2 ~MLTK~ K0);
AppendTo[DNCoreRules, RuleMLTK6];


RuleMLTK7 = O0_ ~MLTK~ (K1_ ~ADDK~ K2_) -> (O0 ~MLTK~ K1) ~ADDK~ (O0 ~MLTK~ K2);
AppendTo[DNCoreRules, RuleMLTK7];


RuleMLTK8 = (K1_ ~OUTER~ B0_) ~MLTK~ K2_ -> (B0 ~DOT~ K2) ~SCRK~ K1;
AppendTo[DNCoreRules, RuleMLTK8];


RuleMLTK9 = (O1_ ~MLTO~ O2_) ~MLTK~ K0_ -> O1 ~MLTK~ (O2 ~MLTK~ K0);
AppendTo[DNCoreRules, RuleMLTK9];


RuleMLTK10 = (O1_ ~TSRO~ O2_) ~MLTK~ ((O1p_ ~TSRO~ O2p_) ~MLTK~ K0_) -> ((O1 ~MLTO~ O1p) ~TSRO~ (O2 ~MLTO~ O2p)) ~MLTK~ K0;
AppendTo[DNCoreRules, RuleMLTK10];


RuleMLTK11 = (O1_ ~TSRO~ O2_) ~MLTK~ KET[PAIR[s_, t_]] -> (O1 ~MLTK~ KET[s]) ~TSRK~ (O2 ~MLTK~ KET[t]);
AppendTo[DNCoreRules, RuleMLTK11];


RuleMLTK12 = (O1_ ~TSRO~ O2_) ~MLTK~ (K1_ ~TSRK~ K2_) -> (O1 ~MLTK~ K1) ~TSRK~ (O2 ~MLTK~ K2);
AppendTo[DNCoreRules, RuleMLTK12];


RuleMLTB1 = B0_ ~MLTB~ ZEROO[sigma_, tau_] -> ZEROB[tau];
AppendTo[DNCoreRules, RuleMLTB1];


RuleMLTB2 = ZEROB[sigma_] ~MLTB~ O0_ -> ZEROB[TProjB[TCalc[O0]]];
AppendTo[DNCoreRules, RuleMLTB2];


RuleMLTB3 = B0_ ~MLTB~ ONEO[sigma_] -> B0;
AppendTo[DNCoreRules, RuleMLTB3];


RuleMLTB4 = B0_ ~MLTB~ (S0_ ~SCRO~ O0_) -> S0 ~SCRB~ (B0 ~MLTB~ O0);
AppendTo[DNCoreRules, RuleMLTB4];


RuleMLTB5 = (S0_ ~SCRB~ B0_) ~MLTB~ O0_ -> S0 ~SCRB~ (B0 ~MLTB~ O0);
AppendTo[DNCoreRules, RuleMLTB5];


RuleMLTB6 = B0_ ~MLTB~ (O1_ ~ADDO~ O2_) -> (B0 ~MLTB~ O1) ~ADDB~ (B0 ~MLTB~ O2);
AppendTo[DNCoreRules, RuleMLTB6];


RuleMLTB7 = (B1_ ~ADDB~ B2_) ~MLTB~ O0_ -> (B1 ~MLTB~ O0) ~ADDB~ (B2 ~MLTB~ O0);
AppendTo[DNCoreRules, RuleMLTB7];


RuleMLTB8 = B1_ ~MLTB~ (K0_ ~OUTER~ B2_) -> (B1 ~DOT~ K0) ~SCRB~ B2;
AppendTo[DNCoreRules, RuleMLTB8];


RuleMLTB9 = B0_ ~MLTB~ (O1_ ~MLTO~ O2_) -> (B0 ~MLTB~ O1) ~MLTB~ O2;
AppendTo[DNCoreRules, RuleMLTB9];


RuleMLTB10 = (B0_ ~MLTB~ (O1p_ ~TSRO~ O2p_)) ~MLTB~ (O1_ ~TSRO~ O2_) -> B0 ~MLTB~ ((O1p ~MLTO~ O1) ~TSRO~ (O2p ~MLTO~ O2));
AppendTo[DNCoreRules, RuleMLTB10];


RuleMLTB11 = BRA[PAIR[s_, t_]] ~MLTB~ (O1_ ~TSRO~ O2_) -> (BRA[s] ~MLTB~ O1) ~TSRB~ (BRA[t] ~MLTB~ O2);
AppendTo[DNCoreRules, RuleMLTB11];


RuleMLTB12 = (B1_ ~TSRB~ B2_) ~MLTB~ (O1_ ~TSRO~ O2_) -> (B1 ~MLTB~ O1) ~TSRB~ (B2 ~MLTB~ O2);
AppendTo[DNCoreRules, RuleMLTB12];


(* ::Subsubsection:: *)
(*TSRK/TSRB*)


RuleTSRK1 = ZEROK[sigma_] ~TSRK~ K0_ :> ZEROK[sigma ~ProdType~ TProjK[TCalc[K0]]];
AppendTo[DNCoreRules, RuleTSRK1];


RuleTSRK2 = K0_ ~TSRK~ ZEROK[sigma_] -> ZEROK[TProjK[TCalc[K0]] ~ProdType~ sigma];
AppendTo[DNCoreRules, RuleTSRK2];


RuleTSRK3 = KET[s_] ~TSRK~ KET[t_] -> KET[PAIR[s, t]];
AppendTo[DNCoreRules, RuleTSRK3];


RuleTSRK4 = (S0_ ~SCRK~ K1_) ~TSRK~ K2_ -> S0 ~SCRK~ (K1 ~TSRK~ K2);
AppendTo[DNCoreRules, RuleTSRK4];


RuleTSRK5 = K1_ ~TSRK~ (S0_ ~SCRK~ K2_) -> S0 ~SCRK~ (K1 ~TSRK~ K2);
AppendTo[DNCoreRules, RuleTSRK5];


RuleTSRK6 = (K1_ ~ADDK~ K2_) ~TSRK~ K0_ -> (K1 ~TSRK~ K0) ~ADDK~ (K2 ~TSRK~ K0);
AppendTo[DNCoreRules, RuleTSRK6];


RuleTSRK7 = K0_ ~TSRK~ (K1_ ~ADDK~ K2_) -> (K0 ~TSRK~ K1) ~ADDK~ (K0 ~TSRK~ K2);
AppendTo[DNCoreRules, RuleTSRK7];


RuleTSRB1 = ZEROB[sigma_] ~TSRB~ B0_ -> ZEROB[sigma ~ProdType~ TProjB[TCalc[B0]]];
AppendTo[DNCoreRules, RuleTSRB1];


RuleTSRB2 = B0_ ~TSRB~ ZEROB[sigma_] -> ZEROB[TProjB[TCalc[B0]] ~ProdType~ sigma];
AppendTo[DNCoreRules, RuleTSRB2];


RuleTSRB3 = BRA[s_] ~TSRB~ BRA[t_] -> BRA[PAIR[s, t]];
AppendTo[DNCoreRules, RuleTSRB3];


RuleTSRB4 = (S0_ ~SCRB~ B1_) ~TSRB~ B2_ -> S0 ~SCRB~ (B1 ~TSRB~ B2);
AppendTo[DNCoreRules, RuleTSRB4];


RuleTSRB5 = B1_ ~TSRB~ (S0_ ~SCRB~ B2_) -> S0 ~SCRB~ (B1 ~TSRB~ B2);
AppendTo[DNCoreRules, RuleTSRB5];


RuleTSRB6 = (B1_ ~ADDB~ B2_) ~TSRB~ B0_ -> (B1 ~TSRB~ B0) ~ADDB~ (B2 ~TSRB~ B0);
AppendTo[DNCoreRules, RuleTSRB6];


RuleTSRB7 = B0_ ~TSRB~ (B1_ ~ADDB~ B2_) -> (B0 ~TSRB~ B1) ~ADDB~ (B0 ~TSRB~ B2);
AppendTo[DNCoreRules, RuleTSRB7];


(* ::Subsection:: *)
(*Operators*)


(* ::Subsubsection:: *)
(*Outer*)


RuleOUTER1 = ZEROK[sigma_] ~OUTER~ B0_ :> ZEROO[sigma, TProjB[TCalc[B0]]];
AppendTo[DNCoreRules, RuleOUTER1];


RuleOUTER2 = K0_ ~OUTER~ ZEROB[sigma_] -> ZEROO[TProjK[TCalc[K0]], sigma];
AppendTo[DNCoreRules, RuleOUTER2];


RuleOUTER3 = (S0_ ~SCRK~ K0_) ~OUTER~ B0_ -> S0 ~SCRO~ (K0 ~OUTER~ B0);
AppendTo[DNCoreRules, RuleOUTER3];


RuleOUTER4 = K0_ ~OUTER~ (S0_ ~SCRB~ B0_) -> S0 ~SCRO~ (K0 ~OUTER~ B0);
AppendTo[DNCoreRules, RuleOUTER4];


RuleOUTER5 = (K1_ ~ADDK~ K2_) ~OUTER~ B0_ -> (K1 ~OUTER~ B0) ~ADDO~ (K2 ~OUTER~ B0);
AppendTo[DNCoreRules, RuleOUTER5];


RuleOUTER6 = K0_ ~OUTER~ (B1_ ~ADDB~ B2_) -> (K0 ~OUTER~ B1) ~ADDO~ (K0 ~OUTER~ B2);
AppendTo[DNCoreRules, RuleOUTER6];


(* ::Subsubsection:: *)
(*ADJO*)


RuleADJO1 = ADJO[ZEROO[sigma_, tau_]] -> ZEROO[tau, sigma];
AppendTo[DNCoreRules, RuleADJO1];


RuleADJO2 = ADJO[ONEO[sigma_]] -> ONEO[sigma];
AppendTo[DNCoreRules, RuleADJO2];


RuleADJO3 = ADJO[K0_ ~OUTER~ B0_] -> ADJK[B0] ~OUTER~ ADJB[K0];
AppendTo[DNCoreRules, RuleADJO3];


RuleADJO4 = ADJO[ADJO[O0_]] -> O0;
AppendTo[DNCoreRules, RuleADJO4];


RuleADJO5 = ADJO[S0_ ~SCRO~ O0_] -> CONJS[S0] ~SCRO~ ADJO[O0];
AppendTo[DNCoreRules, RuleADJO5];


RuleADJO6 = ADJO[O1_ ~ADDO~ O2_] -> ADJO[O1] ~ADDO~ ADJO[O2];
AppendTo[DNCoreRules, RuleADJO6];


RuleADJO7 = ADJO[O1_ ~MLTO~ O2_] -> ADJO[O2] ~MLTO~ ADJO[O1];
AppendTo[DNCoreRules, RuleADJO7];


RuleADJO8 = ADJO[O1_ ~TSRO~ O2_] -> ADJO[O1] ~TSRO~ ADJO[O2];
AppendTo[DNCoreRules, RuleADJO8];


(* ::Subsubsection:: *)
(*SCRO*)


RuleSCRO1 = CPX[0] ~SCRO~ O0_ :> ZEROO[TProjK[TCalc[O0]], TProjB[TCalc[O0]]];
AppendTo[DNCoreRules, RuleSCRO1];


RuleSCRO2 = CPX[1] ~SCRO~ O0_ -> O0;
AppendTo[DNCoreRules, RuleSCRO2];


RuleSCRO3 = S0_ ~SCRO~ ZEROO[sigma_, tau_] -> ZEROO[sigma, tau];
AppendTo[DNCoreRules, RuleSCRO3];


RuleSCRO4 = S1_ ~SCRO~ (S2_ ~SCRO~ O0_) -> (S1 ~MLTS~ S2) ~SCRO~ O0;
AppendTo[DNCoreRules, RuleSCRO4];


RuleSCRO5 = S0_ ~SCRO~ (O1_ ~ADDO~ O2_) -> (S0 ~SCRO~ O1) ~ADDO~ (S0 ~SCRO~ O2);
AppendTo[DNCoreRules, RuleSCRO5];


(* ::Subsubsection:: *)
(*ADDO*)


RuleADDO1 = O0_ ~ADDO~ ZEROO[sigma_, tau_] -> O0;
AppendTo[DNCoreRules, RuleADDO1];


RuleADDO2 = O0_ ~ADDO~ O0_ -> CPX[1 + 1] ~SCRO~ O0;
AppendTo[DNCoreRules, RuleADDO2];


RuleADDO3 = (S0_ ~SCRO~ O0_) ~ADDO~ O0_ -> (S0 ~ADDS~ CPX[1]) ~SCRO~ O0;
AppendTo[DNCoreRules, RuleADDO3];


RuleADDO4 = (S1_ ~SCRO~ O0_) ~ADDO~ (S2_ ~SCRO~ O0_) -> (S1 ~ADDS~ S2) ~SCRO~ O0;
AppendTo[DNCoreRules, RuleADDO4];


(* ::Subsubsection:: *)
(*MLTO*)


RuleMLTO1 = ZEROO[sigma_, tau_] ~MLTO~ O0_ :> ZEROO[sigma, TProjB[TCalc[O0]]];
AppendTo[DNCoreRules, RuleMLTO1];


RuleMLTO2 = O0_ ~MLTO~ ZEROO[sigma_, tau_] :> ZEROO[TProjK[TCalc[O0]], tau];
AppendTo[DNCoreRules, RuleMLTO2];


RuleMLTO3 = ONEO[sigma_] ~MLTO~ O0_ -> O0;
AppendTo[DNCoreRules, RuleMLTO3];


RuleMLTO4 = O0_ ~MLTO~ ONEO[sigma_] -> O0;
AppendTo[DNCoreRules, RuleMLTO4];


RuleMLTO5 = (K0_ ~OUTER~ B0_) ~MLTO~ O0_ -> K0 ~OUTER~ (B0 ~MLTB~ O0);
AppendTo[DNCoreRules, RuleMLTO5];


RuleMLTO6 = O0_ ~MLTO~ (K0_ ~OUTER~ B0_) -> (O0 ~MLTK~ K0) ~OUTER~ B0;
AppendTo[DNCoreRules, RuleMLTO6];


RuleMLTO7 = (S0_ ~SCRO~ O1_) ~MLTO~ O2_ -> S0 ~SCRO~ (O1 ~MLTO~ O2);
AppendTo[DNCoreRules, RuleMLTO7];


RuleMLTO8 = O1_ ~MLTO~ (S0_ ~SCRO~ O2_) -> S0 ~SCRO~ (O1 ~MLTO~ O2);
AppendTo[DNCoreRules, RuleMLTO8];


RuleMLTO9 = (O1_ ~ADDO~ O2_) ~MLTO~ O0_ -> (O1 ~MLTO~ O0) ~ADDO~ (O2 ~MLTO~ O0);
AppendTo[DNCoreRules, RuleMLTO9];


RuleMLTO10 = O0_ ~MLTO~ (O1_ ~ADDO~ O2_) -> (O0 ~MLTO~ O1) ~ADDO~ (O0 ~MLTO~ O2);
AppendTo[DNCoreRules, RuleMLTO10];


RuleMLTO11 = (O1_ ~MLTO~ O2_) ~MLTO~ O0_ -> O1 ~MLTO~ (O2 ~MLTO~ O0);
AppendTo[DNCoreRules, RuleMLTO11];


RuleMLTO12 = (O1_ ~TSRO~ O2_) ~MLTO~ (O1p_ ~TSRO~ O2p_) -> (O1 ~MLTO~ O1p) ~TSRO~ (O2 ~MLTO~ O2p);
AppendTo[DNCoreRules, RuleMLTO12];


RuleMLTO13 = (O1_ ~TSRO~ O2_) ~MLTO~ ((O1p_ ~TSRO~ O2p_) ~MLTO~ O0_) -> ((O1 ~MLTO~ O1p) ~TSRO~ (O2 ~MLTO~ O2p)) ~MLTO~ O0;
AppendTo[DNCoreRules, RuleMLTO13];


(* ::Subsubsection:: *)
(*TSRO*)


RuleTSRO1 = ZEROO[sigma_, tau_] ~TSRO~ O0_ :> 
	ZEROO[sigma ~ProdType~ TProjK[TCalc[O0]], tau ~ProdType~ TProjB[TCalc[O0]]];
AppendTo[DNCoreRules, RuleTSRO1];


RuleTSRO2 = O0_ ~TSRO~ ZEROO[sigma_, tau_] :>
	ZEROO[TProjK[TCalc[O0]] ~ProdType~ sigma, TProjB[TCalc[O0]] ~ProdType~ tau];
AppendTo[DNCoreRules, RuleTSRO2];


RuleTSROONEO = ONEO[sigma_] ~TSRO~ ONEO[tau_] -> ONEO[sigma ~ProdType~ tau];
AppendTo[DNCoreRules, RuleTSROONEO];


RuleTSRO3 = (K1_ ~OUTER~ B1_) ~TSRO~ (K2_ ~OUTER~ B2_) -> (K1 ~TSRK~ K2) ~OUTER~ (B1 ~TSRB~ B2);
AppendTo[DNCoreRules, RuleTSRO3];


RuleTSRO4 = (S0_ ~SCRO~ O1_) ~TSRO~ O2_ -> S0 ~SCRO~ (O1 ~TSRO~ O2);
AppendTo[DNCoreRules, RuleTSRO4];


RuleTSRO5 = O1_ ~TSRO~ (S0_ ~SCRO~ O2_) -> S0 ~SCRO~ (O1 ~TSRO~ O2);
AppendTo[DNCoreRules, RuleTSRO5];


RuleTSRO6 = (O1_ ~ADDO~ O2_) ~TSRO~ O0_ -> (O1 ~TSRO~ O0) ~ADDO~ (O2 ~TSRO~ O0);
AppendTo[DNCoreRules, RuleTSRO6];


RuleTSRO7 = O0_ ~TSRO~ (O1_ ~ADDO~ O2_) -> (O0 ~TSRO~ O1) ~ADDO~ (O0 ~TSRO~ O2);
AppendTo[DNCoreRules, RuleTSRO7];


(* ::Subsection:: *)
(*Compute CPX*)


(*RuleCalcCPX = CPX[x_]/;Unevaluated[x]=!=Evaluate[x] :> CPX[Evaluate[x]];
AppendTo[DNCoreRules, RuleCalcCPX];*)


(* ::Section:: *)
(*The sorted DNCoreRules*)


DNCoreRules = {

	(* DELTA *)
	RuleScalar22,
	RuleDelta1, 
	RuleDelta2,
	
	(* ZERO/ONE *)
	RuleScalar1, 
	RuleScalar6, 
	RuleScalar7, 
	RuleScalar16,
	RuleScalar17,
	RuleSCRK1,
	RuleSCRK2,
	RuleSCRK3,
	RuleSCRB1,
	RuleSCRB2,
	RuleSCRB3,
	RuleADDK1,
	RuleADDB1,
	RuleMLTK1,
	RuleMLTK2,
	RuleMLTK3,
	RuleMLTB1,
	RuleMLTB2,
	RuleMLTB3,
	RuleTSRK1,
	RuleTSRK2,
	RuleTSRB1,
	RuleTSRB2,
	RuleOUTER1,
	RuleOUTER2,
	RuleSCRO1,
	RuleSCRO2,
	RuleSCRO3,
	RuleMLTO1,
	RuleMLTO2,
	RuleMLTO3,
	RuleMLTO4,
	RuleTSRO1,
	RuleTSRO2,
	RuleTSROONEO,
	
	(* ADJOINT *)
	RuleScalar10, 
	RuleScalar11, 
	RuleScalar12, 
	RuleScalar13, 
	RuleScalar14, 
	RuleScalar15,
	RuleADJK1,
	RuleADJK2,
	RuleADJK3,
	RuleADJK4,
	RuleADJK5,
	RuleADJK6,
	RuleADJK7,
	RuleADJB1,
	RuleADJB2,
	RuleADJB3,
	RuleADJB4,
	RuleADJB5,
	RuleADJB6,
	RuleADJB7,
	RuleADJO1,
	RuleADJO2,
	RuleADJO3,
	RuleADJO4,
	RuleADJO5,
	RuleADJO6,
	RuleADJO7,
	RuleADJO8,
	RuleADDO1,
	
	(* Main *)
	
	RuleScalar2, 
	RuleScalar3, 
	RuleScalar4, 
	RuleScalar5, 
	RuleScalar8, 
	RuleScalar18,
	RuleScalar19,
	RuleScalar23,
	RuleScalar24,
	RuleScalar25,
	RuleScalar26,
	RuleScalar27,
	RuleScalar28,
	
	
	RuleSCRK4,
	RuleSCRB4,
	

	RuleADDK2,
	RuleADDK3,
	RuleADDK4,
	RuleADDB2,
	RuleADDB3,
	RuleADDB4,
	
	RuleMLTK4,
	RuleMLTK5,
	RuleMLTK8,
	RuleMLTK9,
	RuleMLTK10,
	RuleMLTK11,
	RuleMLTK12,
	RuleMLTB4,
	RuleMLTB5,
	RuleMLTB8,
	RuleMLTB9,
	RuleMLTB10,
	RuleMLTB11,
	RuleMLTB12,
	
	RuleTSRK3,
	RuleTSRK4,
	RuleTSRK5,
	RuleTSRB3,
	RuleTSRB4,
	RuleTSRB5,
	
	RuleOUTER3,
	RuleOUTER4,
	
	RuleSCRO4,
	
	RuleADDO2,
	RuleADDO3,
	RuleADDO4,
	
	RuleMLTO5,
	RuleMLTO6,
	RuleMLTO7,
	RuleMLTO8,
	RuleMLTO11,
	RuleMLTO12,
	RuleMLTO13,
	
	RuleTSRO3,
	RuleTSRO4,
	RuleTSRO5,

	(* distribution *)
	RuleScalar9, 
	RuleScalar20,
	RuleScalar21,
	RuleSCRK5,
	RuleSCRB5,
	RuleMLTK6,
	RuleMLTK7,
	RuleMLTB6,
	RuleMLTB7,
	RuleTSRK6,
	RuleTSRK7,
	RuleTSRB6,
	RuleTSRB7,
	RuleOUTER5,
	RuleOUTER6,
	RuleSCRO5,
	RuleMLTO9,
	RuleMLTO10,
	RuleTSRO6,
	RuleTSRO7
};


End[];


EndPackage[];
