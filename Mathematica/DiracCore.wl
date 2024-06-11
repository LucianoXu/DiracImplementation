(* ::Package:: *)

(* ::Title:: *)
(*Dirac Notation Core Language*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracCore`", {"Typing`"}];


(* ::Section:: *)
(*Public Interface*)


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
TypeProj1;
TypeProj2;
TypeProjK;
TypeProjB;
SType;
KType;
BType;
OType;
TypeCalc;

InDiracCtxQ::usage = "Check whether the term is in the Dirac notation context.";
TypeDeduce::usage = "Check the typing of the terms according to the DiracCtx.";
TypeChecking;
TypingRules;


(* The term symbols *)
PAIR;
FST;
SND;

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


SetAttributes[DELTA, Orderless];
SetAttributes[{ADDS, MLTS, ADDK, ADDB, ADDO}, {Orderless, Flat, OneIdentity}];


(* ::Section:: *)
(*Type Checking Rules*)


DiracCtx = {};

InDiracCtxQ[term_] := MatchQ[term, Alternatives@@First/@DiracCtx];

TypingRules = {};

TypeDeduce[v_?InDiracCtxQ]:=v/.DiracCtx;
TypeDeduce[e_]:=Throw[{"Type Checking Error: ", e}];
TypeChecking[e_]:=Throw[{"Type Checking Error: ", e}];

TypeDeduce[sigma1_ ~ProdType~ sigma2_] := TypeDeduce[sigma1] ~ProdKind~ TypeDeduce[sigma2];
TypeDeduce[SType] := ScalarKind;
TypeDeduce[KType[sigma_]] := KType[TypeDeduce[sigma]];
TypeDeduce[BType[sigma_]] := BType[TypeDeduce[sigma]];
TypeDeduce[OType[sigma_, tau_]] := OType[TypeDeduce[sigma], TypeDeduce[tau]];

(* Basis *)
TypeDeduce[PAIR[s_, t_]] := TypeDeduce[s] ~ProdType~ TypeDeduce[t];

TypeDeduce[FST[s_]] := TypeChecking[FSTTyping[TypeDeduce[s]]];
TypeChecking[FSTTyping[sigma1_ ~ProdType~ sigma2_]] := sigma1;

TypeDeduce[SND[s_]] := TypeChecking[SNDTyping[TypeDeduce[s]]];
TypeChecking[SNDTyping[sigma1_ ~ProdType~ sigma2_]] := sigma2;

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


TypeProj1[ProdType[T1_, T2_]]:=T1;
TypeProj2[ProdType[T1_, T2_]]:=T2;
KType[TypeProjK[T_]]:=T;
TypeProjK[KType[T_]]:=T;
BType[TypeProjB[T_]]:=T;
TypeProjB[BType[T_]]:=T;
OType[TypeProjK[T_],TypeProjB[T_]]:=T;
TypeProjK[OType[T1_, T2_]]:=T1;
TypeProjB[OType[T1_, T2_]]:=T2;

TypeCalc[a_?InDiracCtxQ]:=a/.DiracCtx;
(*TypeCalc[a_/;MatchQ[a, DefinedPatterns]]:=With[{},Print[a];Print[DiracCtx];a/.DiracCtx];*)
TypeCalc[PAIR[s_, t_]]:=TypeCalc[s] ~ProdType~ TypeCalc[t];
TypeCalc[FST[s_]]:=TypeProj1[TypeCalc[s]];
TypeCalc[SND[s_]]:=TypeProj2[TypeCalc[s]];

TypeCalc[CPX[_]]:=SType;
TypeCalc[DELTA[_, _]]:=SType;
TypeCalc[_ ~ADDS~ _]:=SType;
TypeCalc[_ ~MLTS~ _]:=SType;
TypeCalc[CONJS[_]]:=SType;
TypeCalc[_ ~DOT~ _]:=SType;

TypeCalc[ZEROK[sigma_]]:=KType[sigma];
TypeCalc[KET[s_]]:=KType[TypeCalc[s]];
TypeCalc[ADJK[B_]]:=KType[TypeProjB[TypeCalc[B]]];
TypeCalc[_ ~SCRK~ K_]:=TypeCalc[K];
TypeCalc[K_ ~ADDK~ _]:=TypeCalc[K];
TypeCalc[O0_ ~MLTK~ _]:=KType[TypeProjK[TypeCalc[O0]]];
TypeCalc[K1_ ~TSRK~ K2_]:=KType[TypeProjK[TypeCalc[K1]] ~ProdType~ TypeProjK[TypeCalc[K2]]];

TypeCalc[ZEROB[sigma_]]:=BType[sigma];
TypeCalc[BRA[s_]]:=BType[TypeCalc[s]];
TypeCalc[ADJB[K_]]:=BType[TypeProjK[TypeCalc[K]]];
TypeCalc[_ ~SCRB~ B_]:=TypeCalc[B];
TypeCalc[B_ ~ADDB~ _]:=TypeCalc[B];
TypeCalc[_ ~MLTB~ O0_]:=BType[TypeProjB[TypeCalc[O0]]];
TypeCalc[B1_ ~TSRB~ B2_]:=BType[TypeProjB[TypeCalc[B1]] ~ProdType~ TypeProjB[TypeCalc[B2]]];

TypeCalc[ZEROO[sigma_, tau_]]:=OType[sigma, tau];
TypeCalc[ONEO[sigma_]]:=OType[sigma, sigma];
TypeCalc[K_ ~OUTER~ B_]:=OType[TypeProjK[TypeCalc[K]], TypeProjB[TypeCalc[B]]];
TypeCalc[ADJO[O0_]]:=OType[TypeProjB[TypeCalc[O0]], TypeProjK[TypeCalc[O0]]];
TypeCalc[_ ~SCRO~ O0_]:=TypeCalc[O0];
TypeCalc[O0_ ~ADDO~ _]:=TypeCalc[O0];
TypeCalc[O1_ ~MLTO~ O2_]:=OType[TypeProjK[TypeCalc[O1]], TypeProjB[TypeCalc[O2]]];
TypeCalc[O1_ ~TSRO~ O2_]:=OType[
	TypeProjK[TypeCalc[O1]] ~ProdType~ TypeProjK[TypeCalc[O2]], 
	TypeProjB[TypeCalc[O1]] ~ProdType~ TypeProjB[TypeCalc[O2]]
];




(* ::Section:: *)
(*Rewriting Rules*)


DNCoreRules={};


(* ::Subsection:: *)
(*Basis*)


RuleBasis1 = FST[PAIR[s_, t_]] -> s;
AppendTo[DNCoreRules, RuleBasis1];

RuleBasis2 = SND[PAIR[s_, t_]] -> t;
AppendTo[DNCoreRules, RuleBasis2];

RuleBasis3 = PAIR[FST[t_], SND[t_]] -> t;
AppendTo[DNCoreRules, RuleBasis3];


(* ::Subsection:: *)
(*Scalars*)


RuleDelta1 = DELTA[s_, s_] -> CPX[1];
AppendTo[DNCoreRules, RuleDelta1];

RuleDelta2 = DELTA[s_, PAIR[t1_, t2_]] -> DELTA[FST[s], t1] ~MLTS~ DELTA[SND[s], t2];
AppendTo[DNCoreRules, RuleDelta2];

RuleDelta3 = DELTA[FST[s_], FST[t_]] ~MLTS~ DELTA[SND[s_], SND[t_]] -> DELTA[s, t];
AppendTo[DNCoreRules, RuleDelta3];


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


RuleScalar16 = ZEROB[_] ~DOT~ K0_ -> CPX[0];
AppendTo[DNCoreRules, RuleScalar16];


RuleScalar17 = B0_ ~DOT~ ZEROK[_] -> CPX[0];
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


RuleScalar23 = (B1_ ~TSRB~ B2_) ~DOT~ KET[t_] -> (B1 ~DOT~ KET[FST[t]]) ~MLTS~ (B2 ~DOT~ KET[SND[t]]);
AppendTo[DNCoreRules, RuleScalar23];


RuleScalar24 = BRA[t_] ~DOT~ (K1_ ~TSRK~ K2_) -> (BRA[FST[t]] ~DOT~ K1) ~MLTS~ (BRA[SND[t]] ~DOT~ K2);
AppendTo[DNCoreRules, RuleScalar24];


RuleScalar25 = (B1_ ~TSRB~ B2_) ~DOT~ (K1_ ~TSRK~ K2_) -> (B1 ~DOT~ K1) ~MLTS~ (B2 ~DOT~ K2);
AppendTo[DNCoreRules, RuleScalar25];


RuleScalar26 = (B0_ ~MLTB~ O0_) ~DOT~ K0_ -> B0 ~DOT~ (O0 ~MLTK~ K0);
AppendTo[DNCoreRules, RuleScalar26];


RuleScalar27 = BRA[s_] ~DOT~ ((O1_ ~TSRO~ O2_) ~MLTK~ K0_) -> ((BRA[FST[s]] ~MLTB~ O1) ~TSRB~ (BRA[SND[s]] ~MLTB~ O2)) ~DOT~ K0;
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


RuleSCRK1 = CPX[0] ~SCRK~ K0_ :> ZEROK[TypeProjK[TypeCalc[K0]]];
AppendTo[DNCoreRules, RuleSCRK1];


RuleSCRK2 = CPX[1] ~SCRK~ K0_ -> K0;
AppendTo[DNCoreRules, RuleSCRK2];


RuleSCRK3 = S0_ ~SCRK~ ZEROK[sigma_] -> ZEROK[sigma];
AppendTo[DNCoreRules, RuleSCRK3];


RuleSCRK4 = S1_ ~SCRK~ (S2_ ~SCRK~ K0_) -> (S1 ~MLTS~ S2) ~SCRK~ K0;
AppendTo[DNCoreRules, RuleSCRK4];


RuleSCRK5 = S0_ ~SCRK~ (K1_ ~ADDK~ K2_) -> (S0 ~SCRK~ K1) ~ADDK~ (S0 ~SCRK~ K2);
AppendTo[DNCoreRules, RuleSCRK5];


RuleSCRB1 = CPX[0] ~SCRB~ B0_ -> ZEROB[TypeProjB[TypeCalc[B0]]];
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


RuleMLTK2 = O0_ ~MLTK~ ZEROK[sigma_] :> ZEROK[TypeProjK[TypeCalc[O0]]];
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


RuleMLTK11 = (O1_ ~TSRO~ O2_) ~MLTK~ KET[t_] -> (O1 ~MLTK~ KET[FST[t]]) ~TSRK~ (O2 ~MLTK~ KET[SND[t]]);
AppendTo[DNCoreRules, RuleMLTK11];


RuleMLTK12 = (O1_ ~TSRO~ O2_) ~MLTK~ (K1_ ~TSRK~ K2_) -> (O1 ~MLTK~ K1) ~TSRK~ (O2 ~MLTK~ K2);
AppendTo[DNCoreRules, RuleMLTK12];


RuleMLTB1 = B0_ ~MLTB~ ZEROO[sigma_, tau_] -> ZEROB[tau];
AppendTo[DNCoreRules, RuleMLTB1];


RuleMLTB2 = ZEROB[sigma_] ~MLTB~ O0_ -> ZEROB[TypeProjB[TypeCalc[O0]]];
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


RuleMLTB11 = BRA[t_] ~MLTB~ (O1_ ~TSRO~ O2_) -> (BRA[FST[t]] ~MLTB~ O1) ~TSRB~ (BRA[SND[t]] ~MLTB~ O2);
AppendTo[DNCoreRules, RuleMLTB11];


RuleMLTB12 = (B1_ ~TSRB~ B2_) ~MLTB~ (O1_ ~TSRO~ O2_) -> (B1 ~MLTB~ O1) ~TSRB~ (B2 ~MLTB~ O2);
AppendTo[DNCoreRules, RuleMLTB12];


(* ::Subsubsection:: *)
(*TSRK/TSRB*)


RuleTSRK1 = ZEROK[sigma_] ~TSRK~ K0_ :> ZEROK[sigma ~ProdType~ TypeProjK[TypeCalc[K0]]];
AppendTo[DNCoreRules, RuleTSRK1];


RuleTSRK2 = K0_ ~TSRK~ ZEROK[sigma_] -> ZEROK[TypeProjK[TypeCalc[K0]] ~ProdType~ sigma];
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


RuleTSRB1 = ZEROB[sigma_] ~TSRB~ B0_ -> ZEROB[sigma ~ProdType~ TypeProjB[TypeCalc[B0]]];
AppendTo[DNCoreRules, RuleTSRB1];


RuleTSRB2 = B0_ ~TSRB~ ZEROB[sigma_] -> ZEROB[TypeProjB[TypeCalc[B0]] ~ProdType~ sigma];
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


RuleOUTER1 = ZEROK[sigma_] ~OUTER~ B0_ :> ZEROO[sigma, TypeProjB[TypeCalc[B0]]];
AppendTo[DNCoreRules, RuleOUTER1];


RuleOUTER2 = K0_ ~OUTER~ ZEROB[sigma_] -> ZEROO[TypeProjK[TypeCalc[K0]], sigma];
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


RuleSCRO1 = CPX[0] ~SCRO~ O0_ :> ZEROO[TypeProjK[TypeCalc[O0]], TypeProjB[TypeCalc[O0]]];
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


RuleMLTO1 = ZEROO[sigma_, tau_] ~MLTO~ O0_ :> ZEROO[sigma, TypeProjB[TypeCalc[O0]]];
AppendTo[DNCoreRules, RuleMLTO1];


RuleMLTO2 = O0_ ~MLTO~ ZEROO[sigma_, tau_] :> ZEROO[TypeProjK[TypeCalc[O0]], tau];
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
	ZEROO[sigma ~ProdType~ TypeProjK[TypeCalc[O0]], tau ~ProdType~ TypeProjB[TypeCalc[O0]]];
AppendTo[DNCoreRules, RuleTSRO1];


RuleTSRO2 = O0_ ~TSRO~ ZEROO[sigma_, tau_] :>
	ZEROO[TypeProjK[TypeCalc[O0]] ~ProdType~ sigma, TypeProjB[TypeCalc[O0]] ~ProdType~ tau];
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


End[];


EndPackage[];
