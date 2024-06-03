(* ::Package:: *)

(* ::Title:: *)
(*Dirac Notation Core Language*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracCore`",{"TermOrderCheck`"}];


(* ::Section:: *)
(*Public Interface*)


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
(*Defining Orders*)


InCarrier[a_]:=Element[a, Integers]&&a>=2;

P[0]:=2;
P[1]:=2;
P[2]:=P[Unevaluated[1+1]];
P[t_+u_]:=1+P[t]+P[u];
P[t_ u_]:=P[t] P[u];
P[Conjugate[t_]]:=P[t]^2-1;

ClosureCheck[P[Unevaluated[0]], 2, None];
ClosureCheck[P[Unevaluated[1]], 2, None];
ClosureCheck[P[Unevaluated[t+u]], 2, InCarrier[P[t]]&&InCarrier[P[u]]];
ClosureCheck[P[Unevaluated[t u]], 2, InCarrier[P[t]]&&InCarrier[P[u]]];
ClosureCheck[P[Unevaluated[Conjugate[t]]], 2, InCarrier[P[t]]];

P[FST[u_]]:=Ceiling[Sqrt[P[u]]];
P[SND[u_]]:=Ceiling[Sqrt[P[u]]];
P[PAIR[s_,t_]]:=P[s]^2 P[t]^2;

(* These two inequalities are not passed in mathematica, but obviously true. *)
Catch[ClosureCheck[P[FST[u]], 2, InCarrier[P[u]]]];
Catch[ClosureCheck[P[SND[u]], 2, InCarrier[P[u]]]];
ClosureCheck[P[PAIR[s,t]], 2, InCarrier[P[s]]&&InCarrier[P[t]]];

P[CPX[a_]]:=1+P[a];
P[DELTA[s_,t_]]:=P[s] P[t]; (* this is fixed by the low-level rules *)
P[S1_~ADDS~S2_]:=(1+3(P[S1]+P[S2]));
P[S1_~MLTS~S2_]:=P[S1] P[S2];
P[CONJS[S_]]:=P[S]^2-1;
P[B_~DOT~K_]:=P[B]^3 P[K]^2;

ClosureCheck[P[CPX[a]], 2, InCarrier[P[a]]];
ClosureCheck[P[DELTA[s,t]], 2, InCarrier[P[s]]&&InCarrier[P[t]]];
ClosureCheck[P[S1~ADDS~S2], 2, InCarrier[P[S1]]&&InCarrier[P[S2]]];
ClosureCheck[P[S1~MLTS~S2], 2, InCarrier[P[S1]]&&InCarrier[P[S2]]];
ClosureCheck[P[CONJS[S]], 2, InCarrier[P[S]]];
ClosureCheck[P[B~DOT~K], 2, InCarrier[P[B]]&&InCarrier[P[K]]];

P[ZEROK]:=2;
P[KET[t_]]:=P[t];
P[ADJK[B_]]:=P[B]^2-1;
P[S_~SCRK~K_]:= 2 P[S] P[K];
P[K1_~ADDK~K2_]:=5+6(P[K1]+P[K2]);
P[O_~MLTK~K_]:=P[O]^3 P[K]^2;
P[K1_~TSRK~K2_]:=42 P[K1]^2 P[K2]^2;

ClosureCheck[P[ZEROK], 2, None];
ClosureCheck[P[KET[t]], 2, InCarrier[P[t]]];
ClosureCheck[P[ADJK[B]], 2, InCarrier[P[B]]];
ClosureCheck[P[S ~SCRK~ K], 2, InCarrier[P[S]]&&InCarrier[P[K]]];
ClosureCheck[P[K1 ~ADDK~ K2], 2, InCarrier[P[K1]]&&InCarrier[P[K2]]];
ClosureCheck[P[O0 ~MLTK~ K], 2, InCarrier[P[O0]]&&InCarrier[P[K]]];
ClosureCheck[P[K1 ~TSRK~ K2], 2, InCarrier[P[K1]]&&InCarrier[P[K2]]];

P[ZEROB]:=2;
P[BRA[t_]]:=P[t];
P[ADJB[K_]]:=P[K]^2-1;
P[S_~SCRB~B_]:= 2 P[S] P[B];
P[B1_~ADDB~B2_]:=5+6(P[B1]+P[B2]);
P[B_~MLTB~O_]:=P[B]^2 P[O]^3;
P[B1_~TSRB~B2_]:=42 P[B1]^2 P[B2]^2;

ClosureCheck[P[ZEROB], 2, None];
ClosureCheck[P[BRA[t]], 2, InCarrier[P[t]]];
ClosureCheck[P[ADJB[K]], 2, InCarrier[P[K]]];
ClosureCheck[P[S ~SCRB~ B], 2, InCarrier[P[S]]&&InCarrier[P[B]]];
ClosureCheck[P[B1 ~ADDB~ B2], 2, InCarrier[P[B1]]&&InCarrier[P[B2]]];
ClosureCheck[P[B ~MLTB~ O0], 2, InCarrier[P[B]]&&InCarrier[P[O0]]];
ClosureCheck[P[B1 ~TSRB~ B2], 2, InCarrier[P[B1]]&&InCarrier[P[B2]]];

P[ZEROO]:=2;
P[ONEO]:=2;
P[K_~OUTER~B_]:=P[K]^2 P[B]^2;
P[ADJO[O_]]:=P[O]^2-1;
P[S_~SCRO~O_]:=2 P[S] P[O];
P[O1_~ADDO~O2_]:=5+6(P[O1]+P[O2]);
P[O1_~MLTO~O2_]:=P[O1]^5 P[O2]^4;
P[O1_~TSRO~O2_]:=299792458 P[O1]^2 P[O2]^2;

ClosureCheck[P[ZEROO], 2, None];
ClosureCheck[P[ONEO], 2, None];
ClosureCheck[P[K ~OUTER~ B], 2, InCarrier[P[K]]&&InCarrier[P[B]]];
ClosureCheck[P[ADJO[O0]], 2, InCarrier[P[O0]]];
ClosureCheck[P[S ~SCRO~ O0], 2, InCarrier[P[S]]&&InCarrier[P[O0]]];
ClosureCheck[P[O1 ~ADDO~ O2], 2, InCarrier[P[O1]]&&InCarrier[P[O2]]];
ClosureCheck[P[O1 ~MLTO~ O2], 2, InCarrier[P[O1]]&&InCarrier[P[O2]]];
ClosureCheck[P[O1 ~TSRO~ O2], 2, InCarrier[P[O1]]&&InCarrier[P[O2]]];


(* ::Section::Closed:: *)
(*Order Check for Complex Scalar Avatar (implemented by MMA)*)


OrderCheck[P[Unevaluated[0+a]], P[Unevaluated[a]], InCarrier[P[a]]];
OrderCheck[P[Unevaluated[0 a]], P[Unevaluated[0]], InCarrier[P[a]]];
OrderCheck[P[Unevaluated[1 a]], P[Unevaluated[a]], InCarrier[P[a]]];
OrderCheck[P[Unevaluated[a (b + c)]], P[Unevaluated[a b + a c]], InCarrier[P[a]]&&InCarrier[P[b]]&&InCarrier[P[c]]];
OrderCheck[P[Unevaluated[Conjugate[0]]], P[Unevaluated[0]], None];
OrderCheck[P[Unevaluated[Conjugate[1]]], P[Unevaluated[1]], None];
OrderCheck[P[Unevaluated[Conjugate[a + b]]], P[Unevaluated[Conjugate[a] + Conjugate[b]]], InCarrier[P[a]]&&InCarrier[P[b]]];
OrderCheck[P[Unevaluated[Conjugate[a b]]], P[Unevaluated[Conjugate[a] Conjugate[b]]], InCarrier[P[a]]&&InCarrier[P[b]]];
OrderCheck[P[Unevaluated[Conjugate[Conjugate[a]]]], P[Unevaluated[a]], InCarrier[P[a]]];


(* ::Section:: *)
(*Rewriting Rules*)


DNCoreRules={};


(* ::Subsection:: *)
(*Basis*)


RuleBasis1 = FST[PAIR[s_, t_]] -> s;
AppendTo[DNCoreRules, RuleBasis1];
OrderCheck[P[FST[PAIR[s, t]]], P[s], InCarrier[P[s]]&&InCarrier[P[t]]];

RuleBasis2 = SND[PAIR[s_, t_]] -> t;
AppendTo[DNCoreRules, RuleBasis2];
OrderCheck[P[SND[PAIR[s, t]]], P[s], InCarrier[P[s]]&&InCarrier[P[t]]];

RuleBasis3 = PAIR[FST[t_], SND[t_]] -> t;
AppendTo[DNCoreRules, RuleBasis3];
OrderCheck[P[PAIR[FST[t],SND[t]]], P[t], InCarrier[P[t]]];


(* ::Subsection:: *)
(*Scalars*)


RuleDelta1 = DELTA[s_, s_] -> CPX[1];
AppendTo[DNCoreRules, RuleDelta1];
OrderCheck[P[DELTA[s,s]], P[CPX[1]], InCarrier[P[s]]];

RuleDelta2 = DELTA[s_, PAIR[t1_, t2_]] -> DELTA[FST[s], t1] ~MLTS~ DELTA[SND[s], t2];
AppendTo[DNCoreRules, RuleDelta2];

OrderCheckDerivative[
	P[DELTA[s, PAIR[t1, t2]]], 
	P[DELTA[FST[s], t1] ~MLTS~ DELTA[SND[s], t2]],
	{P[s], P[t1], P[t2]}, 2
];

RuleDelta3 = DELTA[FST[s_], FST[t_]] ~MLTS~ DELTA[SND[s_], SND[t_]] -> DELTA[s, t];
AppendTo[DNCoreRules, RuleDelta3];

OrderCheckDerivative[
	P[DELTA[FST[s], FST[t]]~MLTS~DELTA[SND[s], SND[t]]], 
	P[DELTA[s, t]], 
	{P[s], P[t]}, 2
];


RuleScalar1 = CPX[0] ~ADDS~ a_ -> a;
AppendTo[DNCoreRules, RuleScalar1];
OrderCheck[P[CPX[0] ~ADDS~ a], P[a], InCarrier[P[a]]];


RuleScalar2 = CPX[a_] ~ADDS~ CPX[b_] -> CPX[a + b];
AppendTo[DNCoreRules, RuleScalar2];
OrderCheck[P[CPX[a] ~ADDS~ CPX[b]], P[CPX[a+b]], InCarrier[P[a]]&&InCarrier[P[b]]];


RuleScalar3 = S0_ ~ADDS~ S0_ -> CPX[1 + 1] ~MLTS~ S0;
AppendTo[DNCoreRules, RuleScalar3];
OrderCheck[P[S0 ~ADDS~ S0], P[Unevaluated[CPX[Unevaluated[1 + 1]] ~MLTS~ S0]], InCarrier[P[S0]]];


RuleScalar4 = (CPX[a_] ~MLTS~ S0_) ~ADDS~ S0_ -> CPX[a + 1] ~MLTS~ S0;
AppendTo[DNCoreRules, RuleScalar4];
OrderCheck[P[(CPX[a]~MLTS~S0)~ADDS~S0], P[CPX[a+1]~MLTS~S0], InCarrier[P[a]]&&InCarrier[P[S0]]];


RuleScalar5 = (CPX[a_] ~MLTS~ S0_) ~ADDS~ (CPX[b_] ~MLTS~ S0_) -> CPX[a + b] ~MLTS~ S0;
AppendTo[DNCoreRules, RuleScalar5];
OrderCheck[P[(CPX[a]~MLTS~S0)~ADDS~(CPX[b] ~MLTS~ S0)], P[CPX[a+b]~MLTS~S0], InCarrier[P[a]]&&InCarrier[P[b]]&&InCarrier[P[S0]]];


RuleScalar6 = CPX[0] ~MLTS~ a_ -> CPX[0];
AppendTo[DNCoreRules, RuleScalar6];
OrderCheck[P[CPX[0] ~MLTS~ a], P[CPX[0]], InCarrier[P[a]]];


RuleScalar7 = CPX[1] ~MLTS~ a_ -> a;
AppendTo[DNCoreRules, RuleScalar7];
OrderCheck[P[CPX[1] ~MLTS~ a], P[a], InCarrier[P[a]]];


RuleScalar8 = CPX[a_] ~MLTS~ CPX[b_] -> CPX[a * b];
AppendTo[DNCoreRules, RuleScalar8];
OrderCheck[P[CPX[a] ~MLTS~ CPX[b]], P[CPX[a * b]], InCarrier[P[a]]&&InCarrier[P[b]]];


RuleScalar9 = S1_ ~MLTS~ (S2_ ~ADDS~ S3_) -> (S1 ~MLTS~ S2) ~ADDS~ (S1 ~MLTS~ S3);
AppendTo[DNCoreRules, RuleScalar9];
RuleOrderCheckDerivative[P, RuleScalar9, 2];


RuleScalar10 = CONJS[CPX[a_]] -> CPX[Conjugate[a]];
AppendTo[DNCoreRules, RuleScalar10];
OrderCheck[P[CONJS[CPX[a]]], P[CPX[Conjugate[a]]], InCarrier[P[a]]];


RuleScalar11 = CONJS[DELTA[s_, t_]] -> DELTA[s, t];
AppendTo[DNCoreRules, RuleScalar11];
OrderCheckDerivative[
	P[CONJS[DELTA[s, t]]],
	P[DELTA[s, t]],
	{P[s], P[t]}, 2
];


RuleScalar12 = CONJS[S1_ ~ADDS~ S2_] -> CONJS[S1] ~ADDS~ CONJS[S2];
AppendTo[DNCoreRules, RuleScalar12];
OrderCheck[P[CONJS[S1 ~ADDS~ S2]], P[CONJS[S1] ~ADDS~ CONJS[S2]], InCarrier[P[S1]]&&InCarrier[P[S2]]];


RuleScalar13 = CONJS[S1_ ~MLTS~ S2_] -> CONJS[S1] ~MLTS~ CONJS[S2];
AppendTo[DNCoreRules, RuleScalar13];
OrderCheck[P[CONJS[S1 ~MLTS~ S2]], P[CONJS[S1] ~MLTS~ CONJS[S2]], InCarrier[P[S1]]&&InCarrier[P[S2]]];


RuleScalar14 = CONJS[CONJS[S0_]] -> S0;
AppendTo[DNCoreRules, RuleScalar14];
OrderCheck[P[CONJS[CONJS[S0]]], P[S0], InCarrier[P[S0]]];


RuleScalar15 = CONJS[B0_ ~DOT~ K0_] -> ADJB[K0] ~DOT~ ADJK[B0];
AppendTo[DNCoreRules, RuleScalar15];
RuleOrderCheckDerivative[P, RuleScalar15, 2];


RuleScalar16 = ZEROB ~DOT~ K0_ -> CPX[0];
AppendTo[DNCoreRules, RuleScalar16];
OrderCheck[P[ZEROB ~DOT~ K0], P[CPX[0]], InCarrier[P[K0]]];


RuleScalar17 = B0_ ~DOT~ ZEROK -> CPX[0];
AppendTo[DNCoreRules, RuleScalar17];
OrderCheck[P[B0 ~DOT~ ZEROK], P[CPX[0]], InCarrier[P[B0]]];


RuleScalar18 = (S0_ ~SCRB~ B0_) ~DOT~ K0_ -> S0 ~MLTS~ (B0 ~DOT~ K0);
AppendTo[DNCoreRules, RuleScalar18];
OrderCheckDerivative[
	P[(S0 ~SCRB~ B0) ~DOT~ K0],
	P[S0 ~MLTS~ (B0 ~DOT~ K0)],
	{P[B0], P[S0], P[K0]}, 2
];


RuleScalar19 = B0_ ~DOT~ (S0_ ~SCRK~ K0_) -> S0 ~MLTS~ (B0 ~DOT~ K0);
AppendTo[DNCoreRules, RuleScalar19];
OrderCheckDerivative[
	P[B0 ~DOT~ (S0 ~SCRK~ K0)],
	P[S0 ~MLTS~ (B0 ~DOT~ K0)],
	{P[B0], P[S0], P[K0]}, 2
];


RuleScalar20 = (B1_ ~ADDB~ B2_) ~DOT~ K0_ -> (B1 ~DOT~ K0) ~ADDS~ (B2 ~DOT~ K0);
AppendTo[DNCoreRules, RuleScalar20];
OrderCheckDerivative[
	P[(B1 ~ADDB~ B2) ~DOT~ K0], 
	P[(B1 ~DOT~ K0) ~ADDS~ (B2 ~DOT~ K0)], 
	{P[B1], P[B2], P[K0]}, 2
];


RuleScalar21 = B0_ ~DOT~ (K1_ ~ADDK~ K2_) -> (B0 ~DOT~ K1) ~ADDS~ (B0 ~DOT~ K2);
AppendTo[DNCoreRules, RuleScalar21];
OrderCheckDerivative[
	P[B0 ~DOT~ (K1 ~ADDK~ K2)], 
	P[(B0 ~DOT~ K1) ~ADDS~ (B0 ~DOT~ K2)], 
	{P[B0], P[K1], P[K2]}, 2
];


RuleScalar22 = BRA[s_] ~DOT~ KET[t_] -> DELTA[s, t];
AppendTo[DNCoreRules, RuleScalar22];
OrderCheckDerivative[
	P[BRA[s]~DOT~KET[t]], 
	P[DELTA[s, t]], 
	{P[s], P[t]}, 2
];


RuleScalar23 = (B1_ ~TSRB~ B2_) ~DOT~ KET[t_] -> (B1 ~DOT~ KET[FST[t]]) ~MLTS~ (B2 ~DOT~ KET[SND[t]]);
AppendTo[DNCoreRules, RuleScalar23];
OrderCheckDerivative[
	P[(B1 ~TSRB~ B2) ~DOT~ KET[t]],
	P[(B1 ~DOT~ KET[FST[t]]) ~MLTS~ (B2 ~DOT~ KET[SND[t]])],
	{P[B1], P[B2], P[t]}, 2
];


RuleScalar24 = BRA[t_] ~DOT~ (K1_ ~TSRK~ K2_) -> (BRA[FST[t]] ~DOT~ K1) ~MLTS~ (BRA[SND[t]] ~DOT~ K2);
AppendTo[DNCoreRules, RuleScalar24];
OrderCheckDerivative[
	P[BRA[t] ~DOT~ (K1 ~TSRK~ K2)],
	P[(BRA[FST[t]] ~DOT~ K1) ~MLTS~ (BRA[SND[t]] ~DOT~ K2)],
	{P[t], P[K1], P[K2]}, 2
];


RuleScalar25 = (B1_ ~TSRB~ B2_) ~DOT~ (K1_ ~TSRK~ K2_) -> (B1 ~DOT~ K1) ~MLTS~ (B2 ~DOT~ K2);
AppendTo[DNCoreRules, RuleScalar25];


RuleScalar26 = (B0_ ~MLTB~ O0_) ~DOT~ K0_ -> B0 ~DOT~ (O0 ~MLTK~ K0);
AppendTo[DNCoreRules, RuleScalar26];
RuleOrderCheckDerivative[P, RuleScalar26, 2];


RuleScalar27 = BRA[s_] ~DOT~ ((O1_ ~TSRO~ O2_) ~MLTK~ K0_) -> ((BRA[FST[s]] ~MLTB~ O1) ~TSRB~ (BRA[SND[s]] ~MLTB~ O2)) ~DOT~ K0;
AppendTo[DNCoreRules, RuleScalar27];
OrderCheckDerivative[
	P[BRA[s] ~DOT~ ((O1 ~TSRO~ O2) ~MLTK~ K0)], 
	P[((BRA[FST[s]] ~MLTB~ O1) ~TSRB~ (BRA[SND[s]] ~MLTB~ O2)) ~DOT~ K0],
	{P[s], P[O1], P[O2], P[K0]}, 2
];


RuleScalar28 = (B1_ ~TSRB~ B2_) ~DOT~ ((O1_ ~TSRO~ O2_) ~MLTK~ K0_) -> ((B1 ~MLTB~ O1) ~TSRB~ (B2 ~MLTB~ O2)) ~DOT~ K0;
AppendTo[DNCoreRules, RuleScalar28];
RuleOrderCheckDerivative[P, RuleScalar28, 2];


(* ::Subsection:: *)
(*Ket and Bra*)


(* ::Subsubsection:: *)
(*ADJK/ADJB*)


RuleADJK1 = ADJK[ZEROB] -> ZEROK;
AppendTo[DNCoreRules, RuleADJK1];
OrderCheck[P[ADJK[ZEROB]], P[ZEROK], None];


RuleADJK2 = ADJK[BRA[t_]] -> KET[t];
AppendTo[DNCoreRules, RuleADJK2];
OrderCheck[P[ADJK[BRA[t]]], P[KET[t]], InCarrier[P[t]]];


RuleADJK3 = ADJK[ADJB[K0_]] -> K0;
AppendTo[DNCoreRules, RuleADJK3];
OrderCheck[P[ADJK[ADJB[K0]]], P[K0], InCarrier[P[K0]]];


RuleADJK4 = ADJK[S0_ ~SCRB~ B0_] -> CONJS[S0] ~SCRK~ ADJK[B0];
AppendTo[DNCoreRules, RuleADJK4];
OrderCheck[P[ADJK[S0 ~SCRB~ B0]], P[CONJS[S0] ~SCRK~ ADJK[B0]], InCarrier[P[S0]]&&InCarrier[P[B0]]];


RuleADJK5 = ADJK[B1_ ~ADDB~ B2_] -> ADJK[B1] ~ADDK~ ADJK[B2];
AppendTo[DNCoreRules, RuleADJK5];
OrderCheck[P[ADJK[B1 ~ADDB~ B2]], P[ADJK[B1] ~ADDK~ ADJK[B2]], InCarrier[P[B1]]&&InCarrier[P[B2]]];


RuleADJK6 = ADJK[B0_ ~MLTB~ O0_] -> ADJO[O0] ~MLTK~ ADJK[B0];
AppendTo[DNCoreRules, RuleADJK6];
OrderCheck[P[ADJK[B0 ~MLTB~ O0]], P[ADJO[O0] ~MLTK~ ADJK[B0]], InCarrier[P[B0]]&&InCarrier[P[O0]]];


RuleADJK7 = ADJK[B1_ ~TSRB~ B2_] -> ADJK[B1] ~TSRK~ ADJK[B2];
AppendTo[DNCoreRules, RuleADJK7];
OrderCheck[P[ADJK[B1 ~TSRB~ B2]], P[ADJK[B1] ~TSRK~ ADJK[B2]], InCarrier[P[B1]]&&InCarrier[P[B2]]];


RuleADJB1 = ADJB[ZEROK] -> ZEROB;
AppendTo[DNCoreRules, RuleADJB1];
OrderCheck[P[ADJB[ZEROK]], P[ZEROB], None];


RuleADJB2 = ADJB[KET[t_]] -> BRA[t];
AppendTo[DNCoreRules, RuleADJB2];
OrderCheck[P[ADJB[KET[t]]], P[BRA[t]], InCarrier[P[t]]];


RuleADJB3 = ADJB[ADJK[B0_]] -> B0;
AppendTo[DNCoreRules, RuleADJB3];
OrderCheck[P[ADJB[ADJK[B0]]], P[B0], InCarrier[P[B0]]];


RuleADJB4 = ADJB[S0_ ~SCRK~ K0_] -> CONJS[S0] ~SCRB~ ADJB[K0];
AppendTo[DNCoreRules, RuleADJB4];
OrderCheck[P[ADJB[S0 ~SCRK~ K0]], P[CONJS[S0] ~SCRB~ ADJB[K0]], InCarrier[P[S0]]&&InCarrier[P[K0]]];


RuleADJB5 = ADJB[K1_ ~ADDK~ K2_] -> ADJB[K1] ~ADDB~ ADJB[K2];
AppendTo[DNCoreRules, RuleADJB5];
OrderCheck[P[ADJB[K1 ~ADDK~ K2]], P[ADJB[K1] ~ADDB~ ADJB[K2]], InCarrier[P[K1]]&&InCarrier[P[K2]]];


RuleADJB6 = ADJB[O0_ ~MLTK~ K0_] -> ADJB[K0] ~MLTB~ ADJO[O0];
AppendTo[DNCoreRules, RuleADJB6];
OrderCheck[P[ADJB[O0 ~MLTK~ K0]], P[ADJB[K0] ~MLTB~ ADJO[O0]], InCarrier[P[K0]]&&InCarrier[P[O0]]];


RuleADJB7 = ADJB[K1_ ~TSRK~ K2_] -> ADJB[K1] ~TSRB~ ADJB[K2];
AppendTo[DNCoreRules, RuleADJB7];
OrderCheck[P[ADJB[K1 ~TSRK~ K2]], P[ADJB[K1] ~TSRB~ ADJB[K2]], InCarrier[P[K1]]&&InCarrier[P[K2]]];


(* ::Subsubsection:: *)
(*SCRK/SCRB*)


RuleSCRK1 = CPX[0] ~SCRK~ K0_ -> ZEROK;
AppendTo[DNCoreRules, RuleSCRK1];
OrderCheck[P[CPX[0]~SCRK~K0], P[ZEROK], InCarrier[P[K0]]];


RuleSCRK2 = CPX[1] ~SCRK~ K0_ -> K0;
AppendTo[DNCoreRules, RuleSCRK2];
OrderCheck[P[CPX[1]~SCRK~K0], P[K0], InCarrier[P[K0]]];


RuleSCRK3 = S0_ ~SCRK~ ZEROK -> ZEROK;
AppendTo[DNCoreRules, RuleSCRK3];
OrderCheck[P[S0 ~SCRK~ ZEROK], P[ZEROK], InCarrier[P[S0]]];


RuleSCRK4 = S1_ ~SCRK~ (S2_ ~SCRK~ K0_) -> (S1 ~MLTS~ S2) ~SCRK~ K0;
AppendTo[DNCoreRules, RuleSCRK4];
OrderCheck[P[S0 ~SCRK~ ZEROK], P[ZEROK], InCarrier[P[S0]]];


RuleSCRK5 = S0_ ~SCRK~ (K1_ ~ADDK~ K2_) -> (S0 ~SCRK~ K1) ~ADDK~ (S0 ~SCRK~ K2);
AppendTo[DNCoreRules, RuleSCRK5];
RuleOrderCheckDerivative[P, RuleSCRK5, 2];


RuleSCRB1 = CPX[0] ~SCRB~ B0_ -> ZEROB;
AppendTo[DNCoreRules, RuleSCRB1];
RuleOrderCheckDerivative[P, RuleSCRB1, 2];


RuleSCRB2 = CPX[1] ~SCRB~ B0_ -> B0;
AppendTo[DNCoreRules, RuleSCRB2];
RuleOrderCheckDerivative[P, RuleSCRB2, 2];

RuleSCRB3 = S0_ ~SCRB~ ZEROB -> ZEROB;
AppendTo[DNCoreRules, RuleSCRB3];
RuleOrderCheckDerivative[P, RuleSCRB3, 2];

RuleSCRB4 = S1_ ~SCRB~ (S2_ ~SCRB~ B0_) -> (S1 ~MLTS~ S2) ~SCRB~ B0;
AppendTo[DNCoreRules, RuleSCRB4];
RuleOrderCheckDerivative[P, RuleSCRB4, 2];

RuleSCRB5 = S0_ ~SCRB~ (B1_ ~ADDB~ B2_) -> (S0 ~SCRB~ B1) ~ADDB~ (S0 ~SCRB~ B2);
AppendTo[DNCoreRules, RuleSCRB5];
RuleOrderCheckDerivative[P, RuleSCRB5, 2];


(* ::Subsubsection:: *)
(*ADDK/ADDB*)


RuleADDK1 = K0_ ~ADDK~ ZEROK -> K0;
AppendTo[DNCoreRules, RuleADDK1];
RuleOrderCheckDerivative[P, RuleADDK1, 2];


RuleADDK2 = K0_ ~ADDK~ K0_ -> CPX[1 + 1] ~SCRK~ K0;
AppendTo[DNCoreRules, RuleADDK2];
RuleOrderCheckDerivative[P, RuleADDK2, 2];


RuleADDK3 = (S0_ ~SCRK~ K0_) ~ADDK~ K0_ -> (S0 ~ADDS~ CPX[1]) ~SCRK~ K0;
AppendTo[DNCoreRules, RuleADDK3];
RuleOrderCheckDerivative[P, RuleADDK3, 2];


RuleADDK4 = (S1_ ~SCRK~ K0_) ~ADDK~ (S2_ ~SCRK~ K0_) -> (S1 ~ADDS~ S2) ~SCRK~ K0;
AppendTo[DNCoreRules, RuleADDK4];
RuleOrderCheckDerivative[P, RuleADDK4, 2];


RuleADDB1 = B0_ ~ADDB~ ZEROB -> B0;
AppendTo[DNCoreRules, RuleADDB1];
RuleOrderCheckDerivative[P, RuleADDB1, 2];


RuleADDB2 = B0_ ~ADDB~ B0_ -> CPX[1 + 1] ~SCRB~ B0;
AppendTo[DNCoreRules, RuleADDB2];
RuleOrderCheckDerivative[P, RuleADDB2, 2];


RuleADDB3 = (S0_ ~SCRB~ B0_) ~ADDB~ B0_ -> (S0 ~ADDS~ CPX[1]) ~SCRB~ B0;
AppendTo[DNCoreRules, RuleADDB3];
RuleOrderCheckDerivative[P, RuleADDB3, 2];


RuleADDB4 = (S1_ ~SCRB~ B0_) ~ADDB~ (S2_ ~SCRB~ B0_) -> (S1 ~ADDS~ S2) ~SCRB~ B0;
AppendTo[DNCoreRules, RuleADDB4];
RuleOrderCheckDerivative[P, RuleADDB4, 2];


(* ::Subsubsection:: *)
(*MLTK/MLTB*)


RuleMLTK1 = ZEROO ~MLTK~ K0_ -> ZEROK;
AppendTo[DNCoreRules, RuleMLTK1];
RuleOrderCheckDerivative[P, RuleMLTK1, 2];


RuleMLTK2 = O0_ ~MLTK~ ZEROK -> ZEROK;
AppendTo[DNCoreRules, RuleMLTK2];
RuleOrderCheckDerivative[P, RuleMLTK2, 2];


RuleMLTK3 = ONEO ~MLTK~ K0_ -> K0;
AppendTo[DNCoreRules, RuleMLTK3];
RuleOrderCheckDerivative[P, RuleMLTK3, 2];


RuleMLTK4 = (S0_ ~SCRO~ O0_) ~MLTK~ K0_ -> S0 ~SCRK~ (O0 ~MLTK~ K0);
AppendTo[DNCoreRules, RuleMLTK4];
RuleOrderCheckDerivative[P, RuleMLTK4, 2];


RuleMLTK5 = O0_ ~MLTK~ (S0_ ~SCRK~ K0_) -> S0 ~SCRK~ (O0 ~MLTK~ K0);
AppendTo[DNCoreRules, RuleMLTK5];
RuleOrderCheckDerivative[P, RuleMLTK5, 2];


RuleMLTK6 = (O1_ ~ADDO~ O2_) ~MLTK~ K0_ -> (O1 ~MLTK~ K0) ~ADDK~ (O2 ~MLTK~ K0);
AppendTo[DNCoreRules, RuleMLTK6];
RuleOrderCheckDerivative[P, RuleMLTK6, 2];


RuleMLTK7 = O0_ ~MLTK~ (K1_ ~ADDK~ K2_) -> (O0 ~MLTK~ K1) ~ADDK~ (O0 ~MLTK~ K2);
AppendTo[DNCoreRules, RuleMLTK7];
RuleOrderCheckDerivative[P, RuleMLTK7, 2];


RuleMLTK8 = (K1_ ~OUTER~ B0_) ~MLTK~ K2_ -> (B0 ~DOT~ K2) ~SCRK~ K1;
AppendTo[DNCoreRules, RuleMLTK8];
RuleOrderCheckDerivative[P, RuleMLTK8, 2];


RuleMLTK9 = (O1_ ~MLTO~ O2_) ~MLTK~ K0_ -> O1 ~MLTK~ (O2 ~MLTK~ K0);
AppendTo[DNCoreRules, RuleMLTK9];
RuleOrderCheckDerivative[P, RuleMLTK9, 2];


RuleMLTK10 = (O1_ ~TSRO~ O2_) ~MLTK~ ((O1p_ ~TSRO~ O2p_) ~MLTK~ K0_) -> ((O1 ~MLTO~ O1p) ~TSRO~ (O2 ~MLTO~ O2p)) ~MLTK~ K0;
AppendTo[DNCoreRules, RuleMLTK10];
RuleOrderCheckDerivative[P, RuleMLTK10, 2];


RuleMLTK11 = (O1_ ~TSRO~ O2_) ~MLTK~ KET[t_] -> (O1 ~MLTK~ KET[FST[t]]) ~TSRK~ (O2 ~MLTK~ KET[SND[t]]);
AppendTo[DNCoreRules, RuleMLTK11];
RuleOrderCheckDerivative[P, RuleMLTK11, 2];


RuleMLTK12 = (O1_ ~TSRO~ O2_) ~MLTK~ (K1_ ~TSRK~ K2_) -> (O1 ~MLTK~ K1) ~TSRK~ (O2 ~MLTK~ K2);
AppendTo[DNCoreRules, RuleMLTK12];
RuleOrderCheckDerivative[P, RuleMLTK12, 2];


RuleMLTB1 = B0_ ~MLTB~ ZEROO -> ZEROB;
AppendTo[DNCoreRules, RuleMLTB1];
RuleOrderCheckDerivative[P, RuleMLTB1, 2];


RuleMLTB2 = ZEROB ~MLTB~ O0_ -> ZEROB;
AppendTo[DNCoreRules, RuleMLTB2];
RuleOrderCheckDerivative[P, RuleMLTB2, 2];


RuleMLTB3 = B0_ ~MLTB~ ONEO -> B0;
AppendTo[DNCoreRules, RuleMLTB3];
RuleOrderCheckDerivative[P, RuleMLTB3, 2];


RuleMLTB4 = B0_ ~MLTB~ (S0_ ~SCRO~ O0_) -> S0 ~SCRB~ (B0 ~MLTB~ O0);
AppendTo[DNCoreRules, RuleMLTB4];
RuleOrderCheckDerivative[P, RuleMLTB4, 2];


RuleMLTB5 = (S0_ ~SCRB~ B0_) ~MLTB~ O0_ -> S0 ~SCRB~ (B0 ~MLTB~ O0);
AppendTo[DNCoreRules, RuleMLTB5];
RuleOrderCheckDerivative[P, RuleMLTB5, 2];


RuleMLTB6 = B0_ ~MLTB~ (O1_ ~ADDO~ O2_) -> (B0 ~MLTB~ O1) ~ADDB~ (B0 ~MLTB~ O2);
AppendTo[DNCoreRules, RuleMLTB6];
RuleOrderCheckDerivative[P, RuleMLTB6, 2];


RuleMLTB7 = (B1_ ~ADDB~ B2_) ~MLTB~ O0_ -> (B1 ~MLTB~ O0) ~ADDB~ (B2 ~MLTB~ O0);
AppendTo[DNCoreRules, RuleMLTB7];
RuleOrderCheckDerivative[P, RuleMLTB7, 2];


RuleMLTB8 = B1_ ~MLTB~ (K0_ ~OUTER~ B2_) -> (B1 ~DOT~ K0) ~SCRB~ B2;
AppendTo[DNCoreRules, RuleMLTB8];
RuleOrderCheckDerivative[P, RuleMLTB8, 2];


RuleMLTB9 = B0_ ~MLTB~ (O1_ ~MLTO~ O2_) -> (B0 ~MLTB~ O1) ~MLTB~ O2;
AppendTo[DNCoreRules, RuleMLTB9];
RuleOrderCheckDerivative[P, RuleMLTB9, 2];


RuleMLTB10 = (B0_ ~MLTB~ (O1p_ ~TSRO~ O2p_)) ~MLTB~ (O1_ ~TSRO~ O2_) -> B0 ~MLTB~ ((O1p ~MLTO~ O1) ~TSRO~ (O2p ~MLTO~ O2));
AppendTo[DNCoreRules, RuleMLTB10];
RuleOrderCheckDerivative[P, RuleMLTB10, 2];


RuleMLTB11 = BRA[t_] ~MLTB~ (O1_ ~TSRO~ O2_) -> (BRA[FST[t]] ~MLTB~ O1) ~TSRB~ (BRA[SND[t]] ~MLTB~ O2);
AppendTo[DNCoreRules, RuleMLTB11];
RuleOrderCheckDerivative[P, RuleMLTB11, 2];


RuleMLTB12 = (B1_ ~TSRB~ B2_) ~MLTB~ (O1_ ~TSRO~ O2_) -> (B1 ~MLTB~ O1) ~TSRB~ (B2 ~MLTB~ O2);
AppendTo[DNCoreRules, RuleMLTB12];
RuleOrderCheckDerivative[P, RuleMLTB12, 2];


(* ::Subsubsection:: *)
(*TSRK/TSRB*)


RuleTSRK1 = ZEROK ~TSRK~ K0_ -> ZEROK;
AppendTo[DNCoreRules, RuleTSRK1];
RuleOrderCheckDerivative[P, RuleTSRK1, 2];


RuleTSRK2 = K0_ ~TSRK~ ZEROK -> ZEROK;
AppendTo[DNCoreRules, RuleTSRK2];
RuleOrderCheckDerivative[P, RuleTSRK2, 2];


RuleTSRK3 = KET[s_] ~TSRK~ KET[t_] -> KET[PAIR[s, t]];
AppendTo[DNCoreRules, RuleTSRK3];
RuleOrderCheckDerivative[P, RuleTSRK3, 2];


RuleTSRK4 = (S0_ ~SCRK~ K1_) ~TSRK~ K2_ -> S0 ~SCRK~ (K1 ~TSRK~ K2);
AppendTo[DNCoreRules, RuleTSRK4];
RuleOrderCheckDerivative[P, RuleTSRK4, 2];


RuleTSRK5 = K1_ ~TSRK~ (S0_ ~SCRK~ K2_) -> S0 ~SCRK~ (K1 ~TSRK~ K2);
AppendTo[DNCoreRules, RuleTSRK5];
RuleOrderCheckDerivative[P, RuleTSRK5, 2];


RuleTSRK6 = (K1_ ~ADDK~ K2_) ~TSRK~ K0_ -> (K1 ~TSRK~ K0) ~ADDK~ (K2 ~TSRK~ K0);
AppendTo[DNCoreRules, RuleTSRK6];
RuleOrderCheckDerivative[P, RuleTSRK6, 2];


RuleTSRK7 = K0_ ~TSRK~ (K1_ ~ADDK~ K2_) -> (K0 ~TSRK~ K1) ~ADDK~ (K0 ~TSRK~ K2);
AppendTo[DNCoreRules, RuleTSRK7];
RuleOrderCheckDerivative[P, RuleTSRK7, 2];


RuleTSRB1 = ZEROB ~TSRB~ B0_ -> ZEROB;
AppendTo[DNCoreRules, RuleTSRB1];
RuleOrderCheckDerivative[P, RuleTSRB1, 2];


RuleTSRB2 = B0_ ~TSRB~ ZEROB -> ZEROB;
AppendTo[DNCoreRules, RuleTSRB2];
RuleOrderCheckDerivative[P, RuleTSRB2, 2];


RuleTSRB3 = BRA[s_] ~TSRB~ BRA[t_] -> BRA[PAIR[s, t]];
AppendTo[DNCoreRules, RuleTSRB3];
RuleOrderCheckDerivative[P, RuleTSRB3, 2];


RuleTSRB4 = (S0_ ~SCRB~ B1_) ~TSRB~ B2_ -> S0 ~SCRB~ (B1 ~TSRB~ B2);
AppendTo[DNCoreRules, RuleTSRB4];
RuleOrderCheckDerivative[P, RuleTSRB4, 2];


RuleTSRB5 = B1_ ~TSRB~ (S0_ ~SCRB~ B2_) -> S0 ~SCRB~ (B1 ~TSRB~ B2);
AppendTo[DNCoreRules, RuleTSRB5];
RuleOrderCheckDerivative[P, RuleTSRB5, 2];


RuleTSRB6 = (B1_ ~ADDB~ B2_) ~TSRB~ B0_ -> (B1 ~TSRB~ B0) ~ADDB~ (B2 ~TSRB~ B0);
AppendTo[DNCoreRules, RuleTSRB6];
RuleOrderCheckDerivative[P, RuleTSRB6, 2];


RuleTSRB7 = B0_ ~TSRB~ (B1_ ~ADDB~ B2_) -> (B0 ~TSRB~ B1) ~ADDB~ (B0 ~TSRB~ B2);
AppendTo[DNCoreRules, RuleTSRB7];
RuleOrderCheckDerivative[P, RuleTSRB7, 2];


(* ::Subsection:: *)
(*Operators*)


(* ::Subsubsection:: *)
(*Outer*)


RuleOUTER1 = ZEROK ~OUTER~ B0_ -> ZEROO;
AppendTo[DNCoreRules, RuleOUTER1];
RuleOrderCheckDerivative[P, RuleOUTER1, 2];


RuleOUTER2 = K0_ ~OUTER~ ZEROB -> ZEROO;
AppendTo[DNCoreRules, RuleOUTER2];
RuleOrderCheckDerivative[P, RuleOUTER2, 2];


RuleOUTER3 = (S0_ ~SCRK~ K0_) ~OUTER~ B0_ -> S0 ~SCRO~ (K0 ~OUTER~ B0);
AppendTo[DNCoreRules, RuleOUTER3];
RuleOrderCheckDerivative[P, RuleOUTER3, 2];


RuleOUTER4 = K0_ ~OUTER~ (S0_ ~SCRB~ B0_) -> S0 ~SCRO~ (K0 ~OUTER~ B0);
AppendTo[DNCoreRules, RuleOUTER4];
RuleOrderCheckDerivative[P, RuleOUTER4, 2];


RuleOUTER5 = (K1_ ~ADDK~ K2_) ~OUTER~ B0_ -> (K1 ~OUTER~ B0) ~ADDO~ (K2 ~OUTER~ B0);
AppendTo[DNCoreRules, RuleOUTER5];
RuleOrderCheckDerivative[P, RuleOUTER5, 2];


RuleOUTER6 = K0_ ~OUTER~ (B1_ ~ADDB~ B2_) -> (K0 ~OUTER~ B1) ~ADDO~ (K0 ~OUTER~ B2);
AppendTo[DNCoreRules, RuleOUTER6];
RuleOrderCheckDerivative[P, RuleOUTER6, 2];


(* ::Subsubsection:: *)
(*ADJO*)


RuleADJO1 = ADJO[ZEROO] -> ZEROO;
AppendTo[DNCoreRules, RuleADJO1];
RuleOrderCheckDerivative[P, RuleADJO1, 2];


RuleADJO2 = ADJO[ONEO] -> ONEO;
AppendTo[DNCoreRules, RuleADJO2];
RuleOrderCheckDerivative[P, RuleADJO2, 2];


RuleADJO3 = ADJO[K0_ ~OUTER~ B0_] -> ADJK[B0] ~OUTER~ ADJB[K0];
AppendTo[DNCoreRules, RuleADJO3];
RuleOrderCheckDerivative[P, RuleADJO3, 2];


RuleADJO4 = ADJO[ADJO[O0_]] -> O0;
AppendTo[DNCoreRules, RuleADJO4];
RuleOrderCheckDerivative[P, RuleADJO4, 2];


RuleADJO5 = ADJO[S0_ ~SCRO~ O0_] -> CONJS[S0] ~SCRO~ ADJO[O0];
AppendTo[DNCoreRules, RuleADJO5];
RuleOrderCheckDerivative[P, RuleADJO5, 2];


RuleADJO6 = ADJO[O1_ ~ADDO~ O2_] -> ADJO[O1] ~ADDO~ ADJO[O2];
AppendTo[DNCoreRules, RuleADJO6];
RuleOrderCheckDerivative[P, RuleADJO6, 2];


RuleADJO7 = ADJO[O1_ ~MLTO~ O2_] -> ADJO[O2] ~MLTO~ ADJO[O1];
AppendTo[DNCoreRules, RuleADJO7];
RuleOrderCheckDerivative[P, RuleADJO7, 2];


RuleADJO8 = ADJO[O1_ ~TSRO~ O2_] -> ADJO[O1] ~TSRO~ ADJO[O2];
AppendTo[DNCoreRules, RuleADJO8];
RuleOrderCheckDerivative[P, RuleADJO8, 2];


(* ::Subsubsection:: *)
(*SCRO*)


RuleSCRO1 = CPX[0] ~SCRO~ O0_ -> ZEROO;
AppendTo[DNCoreRules, RuleSCRO1];
RuleOrderCheckDerivative[P, RuleSCRO1, 2];


RuleSCRO2 = CPX[1] ~SCRO~ O0_ -> O0;
AppendTo[DNCoreRules, RuleSCRO2];
RuleOrderCheckDerivative[P, RuleSCRO2, 2];


RuleSCRO3 = S0_ ~SCRO~ ZEROO -> ZEROO;
AppendTo[DNCoreRules, RuleSCRO3];
RuleOrderCheckDerivative[P, RuleSCRO3, 2];


RuleSCRO4 = S1_ ~SCRO~ (S2_ ~SCRO~ O0_) -> (S1 ~MLTS~ S2) ~SCRO~ O0;
AppendTo[DNCoreRules, RuleSCRO4];
RuleOrderCheckDerivative[P, RuleSCRO4, 2];


RuleSCRO5 = S0_ ~SCRO~ (O1_ ~ADDO~ O2_) -> (S0 ~SCRO~ O1) ~ADDO~ (S0 ~SCRO~ O2);
AppendTo[DNCoreRules, RuleSCRO5];
RuleOrderCheckDerivative[P, RuleSCRO5, 2];


(* ::Subsubsection:: *)
(*ADDO*)


RuleADDO1 = O0_ ~ADDO~ ZEROO -> O0;
AppendTo[DNCoreRules, RuleADDO1];
RuleOrderCheckDerivative[P, RuleADDO1, 2];


RuleADDO2 = O0_ ~ADDO~ O0_ -> CPX[1 + 1] ~SCRO~ O0;
AppendTo[DNCoreRules, RuleADDO2];
RuleOrderCheckDerivative[P, RuleADDO2, 2];


RuleADDO3 = (S0_ ~SCRO~ O0_) ~ADDO~ O0_ -> (S0 ~ADDS~ CPX[1]) ~SCRO~ O0;
AppendTo[DNCoreRules, RuleADDO3];
RuleOrderCheckDerivative[P, RuleADDO3, 2];


RuleADDO4 = (S1_ ~SCRO~ O0_) ~ADDO~ (S2_ ~SCRO~ O0_) -> (S1 ~ADDS~ S2) ~SCRO~ O0;
AppendTo[DNCoreRules, RuleADDO4];
RuleOrderCheckDerivative[P, RuleSCRO4, 2];


(* ::Subsubsection:: *)
(*MLTO*)


RuleMLTO1 = ZEROO ~MLTO~ O0_ -> ZEROO;
AppendTo[DNCoreRules, RuleMLTO1];
RuleOrderCheckDerivative[P, RuleMLTO1, 2];


RuleMLTO2 = O0_ ~MLTO~ ZEROO -> ZEROO;
AppendTo[DNCoreRules, RuleMLTO2];
RuleOrderCheckDerivative[P, RuleMLTO2, 2];


RuleMLTO3 = ONEO ~MLTO~ O0_ -> O0;
AppendTo[DNCoreRules, RuleMLTO3];
RuleOrderCheckDerivative[P, RuleMLTO3, 2];


RuleMLTO4 = O0_ ~MLTO~ ONEO -> O0;
AppendTo[DNCoreRules, RuleMLTO4];
RuleOrderCheckDerivative[P, RuleMLTO4, 2];


RuleMLTO5 = (K0_ ~OUTER~ B0_) ~MLTO~ O0_ -> K0 ~OUTER~ (B0 ~MLTB~ O0);
AppendTo[DNCoreRules, RuleMLTO5];
RuleOrderCheckDerivative[P, RuleMLTO5, 2];


RuleMLTO6 = O0_ ~MLTO~ (K0_ ~OUTER~ B0_) -> (O0 ~MLTK~ K0) ~OUTER~ B0;
AppendTo[DNCoreRules, RuleMLTO6];
RuleOrderCheckDerivative[P, RuleMLTO6, 2];


RuleMLTO7 = (S0_ ~SCRO~ O1_) ~MLTO~ O2_ -> S0 ~SCRO~ (O1 ~MLTO~ O2);
AppendTo[DNCoreRules, RuleMLTO7];
RuleOrderCheckDerivative[P, RuleMLTO7, 2];


RuleMLTO8 = O1_ ~MLTO~ (S0_ ~SCRO~ O2_) -> S0 ~SCRO~ (O1 ~MLTO~ O2);
AppendTo[DNCoreRules, RuleMLTO8];
RuleOrderCheckDerivative[P, RuleMLTO8, 2];


RuleMLTO9 = (O1_ ~ADDO~ O2_) ~MLTO~ O0_ -> (O1 ~MLTO~ O0) ~ADDO~ (O2 ~MLTO~ O0);
AppendTo[DNCoreRules, RuleMLTO9];
RuleOrderCheckDerivative[P, RuleMLTO9, 2];


RuleMLTO10 = O0_ ~MLTO~ (O1_ ~ADDO~ O2_) -> (O0 ~MLTO~ O1) ~ADDO~ (O0 ~MLTO~ O2);
AppendTo[DNCoreRules, RuleMLTO10];
RuleOrderCheckDerivative[P, RuleMLTO10, 2];


RuleMLTO11 = (O1_ ~MLTO~ O2_) ~MLTO~ O0_ -> O1 ~MLTO~ (O2 ~MLTO~ O0);
AppendTo[DNCoreRules, RuleMLTO11];
RuleOrderCheckDerivative[P, RuleMLTO11, 2];


RuleMLTO12 = (O1_ ~TSRO~ O2_) ~MLTO~ (O1p_ ~TSRO~ O2p_) -> (O1 ~MLTO~ O1p) ~TSRO~ (O2 ~MLTO~ O2p);
AppendTo[DNCoreRules, RuleMLTO12];
RuleOrderCheckDerivative[P, RuleMLTO12, 2];


RuleMLTO13 = (O1_ ~TSRO~ O2_) ~MLTO~ ((O1p_ ~TSRO~ O2p_) ~MLTO~ O0_) -> ((O1 ~MLTO~ O1p) ~TSRO~ (O2 ~MLTO~ O2p)) ~MLTO~ O0;
AppendTo[DNCoreRules, RuleMLTO13];
RuleOrderCheckDerivative[P, RuleMLTO13, 2];


(* ::Subsubsection:: *)
(*TSRO*)


RuleTSRO1 = ZEROO ~TSRO~ O0_ -> ZEROO;
AppendTo[DNCoreRules, RuleTSRO1];
RuleOrderCheckDerivative[P, RuleTSRO1, 2];


RuleTSRO2 = O0_ ~TSRO~ ZEROO -> ZEROO;
AppendTo[DNCoreRules, RuleTSRO2];
RuleOrderCheckDerivative[P, RuleTSRO2, 2];


RuleTSRO3 = (K1_ ~OUTER~ B1_) ~TSRO~ (K2_ ~OUTER~ B2_) -> (K1 ~TSRK~ K2) ~OUTER~ (B1 ~TSRB~ B2);
AppendTo[DNCoreRules, RuleTSRO3];
RuleOrderCheckDerivative[P, RuleTSRO3, 2];


RuleTSRO4 = (S0_ ~SCRO~ O1_) ~TSRO~ O2_ -> S0 ~SCRO~ (O1 ~TSRO~ O2);
AppendTo[DNCoreRules, RuleTSRO4];
RuleOrderCheckDerivative[P, RuleTSRO4, 2];


RuleTSRO5 = O1_ ~TSRO~ (S0_ ~SCRO~ O2_) -> S0 ~SCRO~ (O1 ~TSRO~ O2);
AppendTo[DNCoreRules, RuleTSRO5];
RuleOrderCheckDerivative[P, RuleTSRO5, 2];


RuleTSRO6 = (O1_ ~ADDO~ O2_) ~TSRO~ O0_ -> (O1 ~TSRO~ O0) ~ADDO~ (O2 ~TSRO~ O0);
AppendTo[DNCoreRules, RuleTSRO6];
RuleOrderCheckDerivative[P, RuleTSRO6, 2];


RuleTSRO7 = O0_ ~TSRO~ (O1_ ~ADDO~ O2_) -> (O0 ~TSRO~ O1) ~ADDO~ (O0 ~TSRO~ O2);
AppendTo[DNCoreRules, RuleTSRO7];
RuleOrderCheckDerivative[P, RuleTSRO7, 2];


End[];


EndPackage[];
