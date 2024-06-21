(* ::Package:: *)

(* ::Title:: *)
(*Dirac Sum Extension*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracSumExt`", {"Unification`", "DiracCore`"}];


SetType;
TypeProjSet;

USET;
SETPROD;

SUMS;
SUMK;
SUMB;
SUMO;

(* the symbol to gather different summation index for sum 
	SUMK[IDX[{i, M}, {j, N}], body]
*)
IDX;

DNSetRules;

DNSumExtRules;

SumAlphaNorm;

DNEntryExpand;

DNSumPushRules;

DNSumPullRules;

DNEntryReduceRules;


Begin["Private`"];


DNSumExtRules = {};


(* ::Section:: *)
(*Notation*)


(* ::Text:: *)
(*This format will influence the calculation, so we disable it.*)


(*
Format[SUMS[IDX[indices___], body_]]:=\!\(
\*SubscriptBox[\(\[Sum]\), \(indices\)]body\);
Format[SUMK[IDX[indices___], body_]]:=\!\(
\*SubscriptBox[\(\[Sum]\), \(indices\)]body\);
Format[SUMB[IDX[indices___], body_]]:=\!\(
\*SubscriptBox[\(\[Sum]\), \(indices\)]body\);
Format[SUMO[IDX[indices___], body_]]:=\!\(
\*SubscriptBox[\(\[Sum]\), \(indices\)]body\);
*)


(* ::Section:: *)
(*Type Checking*)


(* Get the new typing assumptions as an association*)
TypingAssumpt[IDX[indices___]]:=#[[1]]->TypeProjSet[TypeCalc[#[[2]]]]&/@{indices};


TypeDeduce[USET[sigma_]] := SetType[sigma];

TypeDeduce[S1_ ~SETPROD~ S2_] := TypeChecking[TypeDeduce[S1] ~SETPRODTyping~ TypeDeduce[S2]];
TypeChecking[SetType[sigma_] ~SETPRODTyping~ SetType[tau_]] := SetType[sigma ~ProdType~ tau];
TypeDeduce[SUMS[idx:IDX[indices__], body_]] := 
	TypeChecking[
		SUMSTyping[
			IDX@@({#[[1]],TypeDeduce[#[[2]]]}&/@{indices}), 
			Block[{DiracCtx=Join[DiracCtx, TypingAssumpt[idx]]}, TypeDeduce[body]]
		]
	];
TypeChecking[SUMSTyping[_, SType]] := SType;

TypeDeduce[SUMK[idx:IDX[indices__], body_]] := 
	TypeChecking[
		SUMKTyping[
			IDX@@({#[[1]],TypeDeduce[#[[2]]]}&/@{indices}), 
			Block[{DiracCtx=Join[DiracCtx, TypingAssumpt[idx]]}, TypeDeduce[body]]
		]
	];
TypeChecking[SUMKTyping[_, KType[sigma_]]] := KType[sigma];

TypeDeduce[SUMB[idx:IDX[indices__], body_]] := 
	TypeChecking[
		SUMBTyping[
			IDX@@({#[[1]],TypeDeduce[#[[2]]]}&/@{indices}), 
			Block[{DiracCtx=Join[DiracCtx, TypingAssumpt[idx]]}, TypeDeduce[body]]
		]
	];
TypeChecking[SUMBTyping[_, BType[sigma_]]] := BType[sigma];

TypeDeduce[SUMO[idx:IDX[indices__], body_]] := 
	TypeChecking[
		SUMOTyping[
			IDX@@({#[[1]],TypeDeduce[#[[2]]]}&/@{indices}), 
			Block[{DiracCtx=Join[DiracCtx, TypingAssumpt[idx]]}, TypeDeduce[body]]
		]
	];
TypeChecking[SUMOTyping[_, OType[sigma_, tau_]]] := OType[sigma, tau];


(* ::Section:: *)
(*Calculation about Sum Index*)


SUMS[IDX[], body_]:=body;
SUMS[IDX[ids1___], SUMS[IDX[ids2___], body_]]:=SUMS[IDX[ids1,ids2], body];
SUMS[i_, M_, body_]:=SUMS[IDX[{i, M}], body];

SUMK[IDX[], body_]:=body;
SUMK[IDX[ids1___], SUMK[IDX[ids2___], body_]]:=SUMK[IDX[ids1,ids2], body];
SUMK[i_, M_, body_]:=SUMK[IDX[{i, M}], body];

SUMB[IDX[], body_]:=body;
SUMB[IDX[ids1___], SUMB[IDX[ids2___], body_]]:=SUMB[IDX[ids1,ids2], body];
SUMB[i_, M_, body_]:=SUMB[IDX[{i, M}], body];

SUMO[IDX[], body_]:=body;
SUMO[IDX[ids1___], SUMO[IDX[ids2___], body_]]:=SUMO[IDX[ids1,ids2], body];
SUMO[i_, M_, body_]:=SUMO[IDX[{i, M}], body];

IndexOf[IDX[indices___]]:=First/@{indices};
UniqueRenaming[IDX[indices___]]:=#->Unique[]&/@(First/@{indices});


(* ::Section:: *)
(*Convert to alpha-equivalent normal form*)


(* get the list of all bind variables *)
BindVars[term_]:=Cases[term,IDX[bindvs___]->bindvs,{0,Infinity}]//Union//Map[First];

NewBindVars[bindvs_]:=Table[Symbol["idx"<>ToString[i]], {i, Length[bindvs]}];


(* ::Section:: *)
(*Set Attributes*)


SetAttributes[UNION, {Orderless, Flat, OneIdentity}];
SetAttributes[IDX, {Orderless}];


(* ::Section:: *)
(*Type Calculation*)


TypeCalc[USET[sigma_]]:=SetType[sigma];
TypeCalc[M1_ ~SETPROD~ M2_]:=SetType[TypeProjSet[TypeCalc[M1]] ~ProdType~ TypeProjSet[TypeCalc[M2]]];
TypeProjSet[SetType[sigma_]]:=sigma;

TypeCalc[SUMS[_, _]]:=SType;
(* Need testing *)
TypeCalc[t:(SUMK|SUMB|SUMO)[idx_, body_]]:=Block[{DiracCtx=Join[DiracCtx, TypingAssumpt[idx]]}, TypeCalc[body]];


(* ::Section:: *)
(*Operations*)


(*RenameSum[sum:(SUMS|SUMK|SUMB|SUMO)[i_, _, _]]:=sum/.{i:>Unique[]};*)
CompleteBasis[sigma_]:=With[{nv=Unique[]}, SUMO[nv, USET[sigma], KET[nv]~OUTER~BRA[nv]]];


(* ::Section:: *)
(*Rewriting Rules*)


(* ::Subsection:: *)
(*Set Simp*)


DNSetRules = {};

RuleSet4 = USET[sigma_] ~SETPROD~ USET[tau_] -> USET[sigma ~ProdType~ tau];
AppendTo[DNSetRules, RuleSet4];


(* ::Subsection:: *)
(*SUM*)


(* ::Subsubsection:: *)
(*SUM-CONST*)


RuleSumConst1 = SUMS[IDX[___], CPX[0]] -> CPX[0];
AppendTo[DNSumExtRules, RuleSumConst1];

RuleSumConst2 = SUMK[IDX[___], ZEROK[sigma_]] -> ZEROK[sigma];
AppendTo[DNSumExtRules, RuleSumConst2];

RuleSumConst3 = SUMB[IDX[___], ZEROB[sigma_]] -> ZEROB[sigma];
AppendTo[DNSumExtRules, RuleSumConst3];

RuleSumConst4 = SUMO[IDX[___], ZEROO[sigma_, tau_]] -> ZEROO[sigma, tau];
AppendTo[DNSumExtRules, RuleSumConst4];

RuleSumConstOne = ONEO[sigma_] -> CompleteBasis[sigma];
AppendTo[DNSumExtRules, RuleSumConstOne];


(* ::Subsubsection:: *)
(*SUM-ELIM*)


RuleSumElim5 = SUMS[IDX[{i_, USET[_]}, indices___], DELTA[i_, s_]]/;FreeQ[s, i] -> SUMS[IDX[indices], CPX[1]];
AppendTo[DNSumExtRules, RuleSumElim5];

RuleSumElim6 = SUMS[IDX[{i_, USET[_]}, indices___], DELTA[i_, s_] ~MLTS~ S_]/;FreeQ[s, i] :> SUMS[IDX[indices], S/.{i->s}];
AppendTo[DNSumExtRules, RuleSumElim6];

RuleSumElim7K = SUMK[IDX[{i_, USET[_]}, indices___], DELTA[i_, s_] ~SCRK~ A_]/;FreeQ[s, i] :> SUMK[IDX[indices], A/.{i->s}];
AppendTo[DNSumExtRules, RuleSumElim7K];
RuleSumElim7B = SUMB[IDX[{i_, USET[_]}, indices___], DELTA[i_, s_] ~SCRB~ A_]/;FreeQ[s, i] :> SUMB[IDX[indices], A/.{i->s}];
AppendTo[DNSumExtRules, RuleSumElim7B];
RuleSumElim7O = SUMO[IDX[{i_, USET[_]}, indices___], DELTA[i_, s_] ~SCRO~ A_]/;FreeQ[s, i] :> SUMO[IDX[indices], A/.{i->s}];
AppendTo[DNSumExtRules, RuleSumElim7O];

RuleSumElim8K = SUMK[IDX[{i_, USET[_]}, indices___], (DELTA[i_, s_] ~MLTS~ S_) ~SCRK~ A_]/;FreeQ[s, i] :> SUMK[IDX[indices], (S~SCRK~A)/.{i->s}];
AppendTo[DNSumExtRules, RuleSumElim8K];
RuleSumElim8B = SUMB[IDX[{i_, USET[_]}, indices___], (DELTA[i_, s_] ~MLTS~ S_) ~SCRB~ A_]/;FreeQ[s, i] :> SUMB[IDX[indices], (S~SCRB~A)/.{i->s}];
AppendTo[DNSumExtRules, RuleSumElim8B];
RuleSumElim8O = SUMO[IDX[{i_, USET[_]}, indices___], (DELTA[i_, s_] ~MLTS~ S_) ~SCRO~ A_]/;FreeQ[s, i] :> SUMO[IDX[indices], (S~SCRO~A)/.{i->s}];
AppendTo[DNSumExtRules, RuleSumElim8O];


RuleSumElim9 = SUMS[IDX[{i_, M_}, {j_, M_}, indices___], DELTA[i_, j_]] -> SUMS[IDX[{j, M}, indices], CPX[1]];
AppendTo[DNSumExtRules, RuleSumElim9];

RuleSumElim10 = SUMS[IDX[{i_, M_}, {j_, M_}, indices___], DELTA[i_, j_] ~MLTS~ S_] :> SUMS[IDX[{j, M}, indices], S/.{i->j}];
AppendTo[DNSumExtRules, RuleSumElim10];

RuleSumElim11K = SUMK[IDX[{i_, M_}, {j_, M_}, indices___], DELTA[i_, j_] ~SCRK~ A_] :> SUMK[IDX[{j, M}, indices], A/.{i->j}];
AppendTo[DNSumExtRules, RuleSumElim11K];
RuleSumElim11B = SUMB[IDX[{i_, M_}, {j_, M_}, indices___], DELTA[i_, j_] ~SCRB~ A_] :> SUMB[IDX[{j, M}, indices], A/.{i->j}];
AppendTo[DNSumExtRules, RuleSumElim11B];
RuleSumElim11O = SUMO[IDX[{i_, M_}, {j_, M_}, indices___], DELTA[i_, j_] ~SCRO~ A_] :> SUMO[IDX[{j, M}, indices], A/.{i->j}];
AppendTo[DNSumExtRules, RuleSumElim11O];

RuleSumElim12K = SUMK[IDX[{i_, M_}, {j_, M_}, indices___], (DELTA[i_, j_] ~MLTS~ S_) ~SCRK~ A_] :> SUMK[IDX[{j, M}, indices], (S~SCRK~A)/.{i->j}];
AppendTo[DNSumExtRules, RuleSumElim12K];
RuleSumElim12B = SUMB[IDX[{i_, M_}, {j_, M_}, indices___], (DELTA[i_, j_] ~MLTS~ S_) ~SCRB~ A_] :> SUMB[IDX[{j, M}, indices], (S~SCRB~A)/.{i->j}];
AppendTo[DNSumExtRules, RuleSumElim12B];
RuleSumElim12O = SUMO[IDX[{i_, M_}, {j_, M_}, indices___], (DELTA[i_, j_] ~MLTS~ S_) ~SCRO~ A_] :> SUMO[IDX[{j, M}, indices], (S~SCRO~A)/.{i->j}];
AppendTo[DNSumExtRules, RuleSumElim12O];


(* ::Subsubsection:: *)
(*SUM-DIST*)


RuleSumDist1 = CONJS[SUMS[idx_, S_]] -> SUMS[idx, CONJS[S]];
AppendTo[DNSumExtRules, RuleSumDist1];


RuleSumDist3K = ADJK[SUMB[idx_, B_]] -> SUMK[idx, ADJK[B]];
AppendTo[DNSumExtRules, RuleSumDist3K];
RuleSumDist3B = ADJB[SUMK[idx_, K_]] -> SUMB[idx, ADJB[K]];
AppendTo[DNSumExtRules, RuleSumDist3B];
RuleSumDist3O = ADJO[SUMO[idx_, O0_]] -> SUMO[idx, ADJO[O0]];
AppendTo[DNSumExtRules, RuleSumDist3O];


(* ::Subsubsection:: *)
(*SUM-PUSH*)


(* The rules to push in *)
DNSumPushRules = {};

RuleSumPush1 = SUMS[idx_, S_] ~MLTS~ X_ :> With[{nv=UniqueRenaming[idx]}, SUMS[idx/.nv, (S/.nv) ~MLTS~ X]];
AppendTo[DNSumPushRules, RuleSumPush1];

RuleSumPush5K = S_ ~SCRK~ SUMK[idx_, K_] :> With[{nv=UniqueRenaming[idx]}, SUMK[idx/.nv, S ~SCRK~ (K/.nv)]];
AppendTo[DNSumPushRules, RuleSumPush5K];
RuleSumPush5B = S_ ~SCRB~ SUMB[idx_, B_] :> With[{nv=UniqueRenaming[idx]}, SUMB[idx/.nv, S ~SCRB~ (B/.nv)]];
AppendTo[DNSumPushRules, RuleSumPush5B];
RuleSumPush5O = S_ ~SCRO~ SUMO[idx_, O0_] :> With[{nv=UniqueRenaming[idx]}, SUMO[idx/.nv, S ~SCRO~ (O0/.nv)]];
AppendTo[DNSumPushRules, RuleSumPush5O];

RuleSumPush6K = SUMS[idx_, S_] ~SCRK~ K_ :> With[{nv=UniqueRenaming[idx]}, SUMK[idx/.nv, (S/.nv) ~SCRK~ K]];
AppendTo[DNSumPushRules, RuleSumPush6K];
RuleSumPush6B = SUMS[idx_, S_] ~SCRB~ B_ :> With[{nv=UniqueRenaming[idx]}, SUMB[idx/.nv, (S/.nv) ~SCRB~ B]];
AppendTo[DNSumPushRules, RuleSumPush6B];
RuleSumPush6O = SUMS[idx_, S_] ~SCRO~ O0_ :> With[{nv=UniqueRenaming[idx]}, SUMO[idx/.nv, (S/.nv) ~SCRO~ O0]];
AppendTo[DNSumPushRules, RuleSumPush6O];

RuleSumPush7BK = B_ ~DOT~ SUMK[idx_, K_] :> With[{nv=UniqueRenaming[idx]}, SUMS[idx/.nv, B ~DOT~ (K/.nv)]];
AppendTo[DNSumPushRules, RuleSumPush7BK];
RuleSumPush7OK = O0_ ~MLTK~ SUMK[idx_, K_] :> With[{nv=UniqueRenaming[idx]}, SUMK[idx/.nv, O0 ~MLTK~ (K/.nv)]];
AppendTo[DNSumPushRules, RuleSumPush7OK];
RuleSumPush7BO = B_ ~MLTB~ SUMO[idx_, O0_] :> With[{nv=UniqueRenaming[idx]}, SUMB[idx/.nv, B ~MLTB~ (O0/.nv)]];
AppendTo[DNSumPushRules, RuleSumPush7BO];
RuleSumPush7OO = O1_ ~MLTO~ SUMO[idx_, O2_] :> With[{nv=UniqueRenaming[idx]}, SUMO[idx/.nv, O1 ~MLTO~ (O2/.nv)]];
AppendTo[DNSumPushRules, RuleSumPush7OO];

RuleSumPush8BK = SUMB[idx_, B_] ~DOT~ K_ :> With[{nv=UniqueRenaming[idx]}, SUMS[idx/.nv, (B/.nv) ~DOT~ K]];
AppendTo[DNSumPushRules, RuleSumPush8BK];
RuleSumPush8OK = SUMO[idx_, O0_] ~MLTK~ K_ :> With[{nv=UniqueRenaming[idx]}, SUMK[idx/.nv, (O0/.nv) ~MLTK~ K]];
AppendTo[DNSumPushRules, RuleSumPush8OK];
RuleSumPush8BO = SUMB[idx_, B_] ~MLTB~ O0_ :> With[{nv=UniqueRenaming[idx]}, SUMB[idx/.nv, (B/.nv) ~MLTB~ O0]];
AppendTo[DNSumPushRules, RuleSumPush8BO];
RuleSumPush8OO = SUMO[idx_, O1_] ~MLTO~ O2_ :> With[{nv=UniqueRenaming[idx]}, SUMO[idx/.nv, (O1/.nv) ~MLTO~ O2]];
AppendTo[DNSumPushRules, RuleSumPush8OO];

RuleSumPush9KB = K_ ~OUTER~ SUMB[idx_, B_] :> With[{nv=UniqueRenaming[idx]}, SUMO[idx/.nv, K ~OUTER~ (B/.nv)]];
AppendTo[DNSumPushRules, RuleSumPush9KB];
RuleSumPush9KK = K1_ ~TSRK~ SUMK[idx_, K2_] :> With[{nv=UniqueRenaming[idx]}, SUMK[idx/.nv, K1 ~TSRK~ (K2/.nv)]];
AppendTo[DNSumPushRules, RuleSumPush9KK];
RuleSumPush9BB = B1_ ~TSRB~ SUMB[idx_, B2_] :> With[{nv=UniqueRenaming[idx]}, SUMB[idx/.nv, B1 ~TSRB~ (B2/.nv)]];
AppendTo[DNSumPushRules, RuleSumPush9BB];
RuleSumPush9OO = O1_ ~TSRO~ SUMO[idx_, O2_] :> With[{nv=UniqueRenaming[idx]}, SUMO[idx/.nv, O1 ~TSRO~ (O2/.nv)]];
AppendTo[DNSumPushRules, RuleSumPush9OO];

RuleSumPush10KB = SUMK[idx_, K_] ~OUTER~ B_ :> With[{nv=UniqueRenaming[idx]}, SUMO[idx/.nv, (K/.nv) ~OUTER~ B]];
AppendTo[DNSumPushRules, RuleSumPush10KB];
RuleSumPush10KK = SUMK[idx_, K1_] ~TSRK~ K2_ :> With[{nv=UniqueRenaming[idx]}, SUMK[idx/.nv, (K1/.nv) ~TSRK~ K2]];
AppendTo[DNSumPushRules, RuleSumPush10KK];
RuleSumPush10BB = SUMB[idx_, B1_] ~TSRB~ B2_ :> With[{nv=UniqueRenaming[idx]}, SUMB[idx/.nv, (B1/.nv) ~TSRB~ B2]];
AppendTo[DNSumPushRules, RuleSumPush10BB];
RuleSumPush10OO = SUMO[idx_, O1_] ~TSRO~ O2_ :> With[{nv=UniqueRenaming[idx]}, SUMO[idx/.nv, (O1/.nv) ~TSRO~ O2]];
AppendTo[DNSumPushRules, RuleSumPush10OO];


(* ::Subsubsection::Closed:: *)
(*SUM-PULL*)


(* The rules to pull out *)
DNSumPullRules = {};

RuleSumPull1 = SUMS[IDX[{i_, M_}, indices___], S_ ~MLTS~ X_]/;FreeQ[X,i] -> SUMS[IDX[indices], SUMS[i, M, S] ~MLTS~ X];
AppendTo[DNSumPullRules, RuleSumPull1];

RuleSumPull1L = SUMS[IDX[{i_, M_}, indices___], (B_ ~DOT~ K_) ~MLTS~ X_]/;FreeQ[B,i] -> SUMS[IDX[indices], B ~DOT~ SUMK[i, M, X ~SCRK~ K]];
AppendTo[DNSumPullRules, RuleSumPull1L];

RuleSumPull1R = SUMS[IDX[{i_, M_}, indices___], (B_ ~DOT~ K_) ~MLTS~ X_]/;FreeQ[K,i] -> SUMS[IDX[indices], SUMB[i, M, X ~SCRB~ B] ~DOT~ K];
AppendTo[DNSumPullRules, RuleSumPull1R];

RuleSumPull5K = SUMK[IDX[{i_, M_}, indices___], S_ ~SCRK~ K_]/;FreeQ[S,i] -> SUMK[IDX[indices], S ~SCRK~ SUMK[i, M, K]];
AppendTo[DNSumPullRules, RuleSumPull5K];
RuleSumPull5B = SUMB[IDX[{i_, M_}, indices___], S_ ~SCRB~ B_]/;FreeQ[S,i] -> SUMB[IDX[indices], S ~SCRB~ SUMB[i, M, B]];
AppendTo[DNSumPullRules, RuleSumPull5B];
RuleSumPull5O = SUMO[IDX[{i_, M_}, indices___], S_ ~SCRO~ O0_]/;FreeQ[S,i] -> SUMO[IDX[indices], S ~SCRO~ SUMO[i, M, O0]];
AppendTo[DNSumPullRules, RuleSumPull5O];

RuleSumPull6K = SUMK[IDX[{i_, M_}, indices___], S_ ~SCRK~ K_]/;FreeQ[K,i] -> SUMK[IDX[indices], SUMS[i, M, S] ~SCRK~ K];
AppendTo[DNSumPullRules, RuleSumPull6K];
RuleSumPull6B = SUMB[IDX[{i_, M_}, indices___], S_ ~SCRB~ B_]/;FreeQ[B,i] -> SUMB[IDX[indices], SUMS[i, M, S] ~SCRB~ B];
AppendTo[DNSumPullRules, RuleSumPull6B];
RuleSumPull6O = SUMO[IDX[{i_, M_}, indices___], S_ ~SCRO~ O0_]/;FreeQ[O0,i] -> SUMO[IDX[indices], SUMS[i, M, S] ~SCRO~ O0];
AppendTo[DNSumPullRules, RuleSumPull6O];

RuleSumPull7BK = SUMS[IDX[{i_, M_}, indices___], B_ ~DOT~ K_]/;FreeQ[B,i] -> SUMS[IDX[indices], B ~DOT~ SUMK[i, M, K]];
AppendTo[DNSumPullRules, RuleSumPull7BK];
RuleSumPull7OK = SUMK[IDX[{i_, M_}, indices___], O0_ ~MLTK~ K_]/;FreeQ[O0,i] -> SUMK[IDX[indices], O0 ~MLTK~ SUMK[i, M, K]];
AppendTo[DNSumPullRules, RuleSumPull7OK];
RuleSumPull7BO = SUMB[IDX[{i_, M_}, indices___], B_ ~MLTB~ O0_]/;FreeQ[B,i] -> SUMB[IDX[indices], B ~MLTB~ SUMO[i, M, O0]];
AppendTo[DNSumPullRules, RuleSumPull7BO];
RuleSumPull7OO = SUMO[IDX[{i_, M_}, indices___], O1_ ~MLTO~ O2_]/;FreeQ[O1,i] -> SUMO[IDX[indices], O1 ~MLTO~ SUMO[i, M, O2]];
AppendTo[DNSumPullRules, RuleSumPull7OO];


RuleSumPull8BK = SUMS[IDX[{i_, M_}, indices___], B_ ~DOT~ K_]/;FreeQ[K,i] -> SUMS[IDX[indices], SUMB[i, M, B] ~DOT~ K];
AppendTo[DNSumPullRules, RuleSumPull8BK];
RuleSumPull8OK = SUMK[IDX[{i_, M_}, indices___], O0_ ~MLTK~ K_]/;FreeQ[K,i] -> SUMK[IDX[indices], SUMO[i, M, O0] ~MLTK~ K];
AppendTo[DNSumPullRules, RuleSumPull8OK];
RuleSumPull8BO = SUMB[IDX[{i_, M_}, indices___], B_ ~MLTB~ O0_]/;FreeQ[O0,i] -> SUMB[IDX[indices], SUMB[i, M, B] ~MLTB~ O0];
AppendTo[DNSumPullRules, RuleSumPull8BO];
RuleSumPull8OO = SUMO[IDX[{i_, M_}, indices___], O1_ ~MLTO~ O2_]/;FreeQ[O2,i] -> SUMO[IDX[indices], SUMO[i, M, O1] ~MLTO~ O2];
AppendTo[DNSumPullRules, RuleSumPull8OO];


RuleSumPull9KB = SUMO[IDX[{i_, M_}, indices___], K_ ~OUTER~ B_]/;FreeQ[K,i] -> SUMO[IDX[indices], K ~OUTER~ SUMB[i, M, B]];
AppendTo[DNSumPullRules, RuleSumPull9KB];
RuleSumPull9KK = SUMK[IDX[{i_, M_}, indices___], K1_ ~TSRK~ K2_]/;FreeQ[K1,i] -> SUMK[IDX[indices], K1 ~TSRK~ SUMK[i, M, K2]];
AppendTo[DNSumPullRules, RuleSumPull9KK];
RuleSumPull9BB = SUMB[IDX[{i_, M_}, indices___], B1_ ~TSRB~ B2_]/;FreeQ[B1,i] -> SUMB[IDX[indices], B1 ~TSRB~ SUMB[i, M, B2]];
AppendTo[DNSumPullRules, RuleSumPull9BB];
RuleSumPull9OO = SUMO[IDX[{i_, M_}, indices___], O1_ ~TSRO~ O2_]/;FreeQ[O1,i] -> SUMO[IDX[indices], O1 ~TSRO~ SUMO[i, M, O2]];
AppendTo[DNSumPullRules, RuleSumPull9OO];


RuleSumPull10KB = SUMO[IDX[{i_, M_}, indices___], K_ ~OUTER~ B_]/;FreeQ[B,i] -> SUMO[IDX[indices], SUMK[i, M, K] ~OUTER~ B];
AppendTo[DNSumPullRules, RuleSumPull10KB];
RuleSumPull10KK = SUMK[IDX[{i_, M_}, indices___], K1_ ~TSRK~ K2_]/;FreeQ[K2,i] -> SUMK[IDX[indices], SUMK[i, M, K1] ~TSRK~ K2];
AppendTo[DNSumPullRules, RuleSumPull10KK];
RuleSumPull10BB = SUMB[IDX[{i_, M_}, indices___], B1_ ~TSRB~ B2_]/;FreeQ[B2,i] -> SUMB[IDX[indices], SUMB[i, M, B1] ~TSRB~ B2];
AppendTo[DNSumPullRules, RuleSumPull10BB];
RuleSumPull10OO = SUMO[IDX[{i_, M_}, indices___], O1_ ~TSRO~ O2_]/;FreeQ[O2,i] -> SUMO[IDX[indices], SUMO[i, M, O1] ~TSRO~ O2];
AppendTo[DNSumPullRules, RuleSumPull10OO];


(* ::Subsubsection:: *)
(*SUM-ADD*)


(*RuleSumAdd1 = SUMS[IDX[{i_, M_}, indicesl___], S1_] ~ADDS~ SUMS[IDX[{j_, M_}, indicesr___], S2_] :>
	With[
		{newvar=Unique[]},
		SUMS[IDX[{newvar, M}], SUMS[IDX[indicesl], (S1 /.{i -> newvar})] ~ADDS~ SUMS[IDX[indicesr], (S2 /. {j -> newvar})]]
	];
AppendTo[DNSumExtRules, RuleSumAdd1];

RuleSumAdd2 = SUMK[IDX[{i_, M_}, indicesl___], K1_] ~ADDK~ SUMK[IDX[{j_, M_}, indicesr___], K2_] :>
	With[
		{newvar=Unique[]},
		SUMK[IDX[{newvar, M}], SUMK[IDX[indicesl], (K1 /.{i -> newvar})] ~ADDK~ SUMK[IDX[indicesr], (K2 /. {j -> newvar})]]
	];
AppendTo[DNSumExtRules, RuleSumAdd2];

RuleSumAdd3 = SUMB[IDX[{i_, M_}, indicesl___], B1_] ~ADDB~ SUMB[IDX[{j_, M_}, indicesr___], B2_] :>
	With[
		{newvar=Unique[]},
		SUMB[IDX[{newvar, M}], SUMB[IDX[indicesl], (B1 /.{i -> newvar})] ~ADDB~ SUMB[IDX[indicesr], (B2 /. {j -> newvar})]]
	];
AppendTo[DNSumExtRules, RuleSumAdd3];

RuleSumAdd4 = SUMO[IDX[{i_, M_}, indicesl___], O1_] ~ADDO~ SUMO[IDX[{j_, M_}, indicesr___], O2_] :>
	With[
		{newvar=Unique[]},
		SUMO[IDX[{newvar, M}], SUMO[IDX[indicesl], (O1 /.{i -> newvar})] ~ADDO~ SUMO[IDX[indicesr], (O2 /. {j -> newvar})]]
	];
AppendTo[DNSumExtRules, RuleSumAdd4];*)


(* ::Subsubsection:: *)
(*SUM-ADD*)


IdxUnifyQ[idx1_IDX, idx2_IDX]:=Sort[Last/@List@@idx1]===Sort[Last/@List@@idx2];

IdxUnify[idx1_IDX, idx2_IDX]:=
	With[
		{nvs=Table[Unique[],Length[idx1]]},
		{
			Thread[First/@Sort[List@@#1,#1[[2]]<#2[[2]]&]->#2]&[idx1, nvs],
			Thread[First/@Sort[List@@#1,#1[[2]]<#2[[2]]&]->#2]&[idx2, nvs]
		}
	];
	
IdxUnifySameTermQ[idx1_IDX, idx2_IDX, t1_, t2_]:=
	With[
		{nvs=Table[Unique[],Length[idx1]]},
		SameQ[
			t1/.(Thread[First/@Sort[List@@#1,#1[[2]]<#2[[2]]&]->#2]&[idx1, nvs]),
			t2/.(Thread[First/@Sort[List@@#1,#1[[2]]<#2[[2]]&]->#2]&[idx2, nvs])
		]
	];

RuleSumAdd1 = SUMS[idx_, S1_ ~ADDS~ S2_] -> SUMS[idx, S1] ~ADDS~ SUMS[idx, S2];
AppendTo[DNSumExtRules, RuleSumAdd1];

RuleSumAdd2 = SUMK[idx_, K1_ ~ADDK~ K2_] -> SUMK[idx, K1] ~ADDK~ SUMK[idx, K2];
AppendTo[DNSumExtRules, RuleSumAdd2];

RuleSumAdd3 = SUMB[idx_, B1_ ~ADDB~ B2_] -> SUMB[idx, B1] ~ADDB~ SUMB[idx, B2];
AppendTo[DNSumExtRules, RuleSumAdd3];

RuleSumAdd4 = SUMO[idx_, O1_ ~ADDO~ O2_] -> SUMO[idx, O1] ~ADDO~ SUMO[idx, O2];
AppendTo[DNSumExtRules, RuleSumAdd4];

RuleSumAddComp1 = SUMS[idx1_, CPX[alpha_] ~MLTS~ S1_] ~ADDS~ SUMS[idx2_, S2_] /; 
	IdxUnifyQ[idx1, idx2]&&IdxUnifySameTermQ[idx1, idx2, S1, S2] :>
	With[
		{renaming=IdxUnify[idx1, idx2]},
		SUMS[idx1/.renaming[[1]], (CPX[alpha+1]/.renaming[[1]]) ~ADDS~ (S2 /. renaming[[2]])]
	];
AppendTo[DNSumExtRules, RuleSumAddComp1];

RuleSumAddComp2 = SUMS[idx1_, CPX[alpha_] ~MLTS~ S1_] ~ADDS~ SUMS[idx2_, CPX[beta_] ~MLTS~ S2_] /; 
	IdxUnifyQ[idx1, idx2]&&IdxUnifySameTermQ[idx1, idx2, S1, S2] :>
	With[
		{renaming=IdxUnify[idx1, idx2]},
		SUMS[idx1/.renaming[[1]], (CPX[(alpha/.renaming[[1]])+(beta/.renaming[[2]])]) ~ADDS~ (S2 /. renaming[[2]])]
	];
AppendTo[DNSumExtRules, RuleSumAddComp2];

RuleSumAddComp3 = SUMK[idx1_, S_ ~SCRK~ K1_] ~ADDK~ SUMK[idx2_, K2_] /; 
	IdxUnifyQ[idx1, idx2]&&IdxUnifySameTermQ[idx1, idx2, K1, K2] :>
	With[
		{renaming=IdxUnify[idx1, idx2]},
		SUMK[idx1/.renaming[[1]], ((S/.renaming[[1]])~ADDS~CPX[1])~SCRK~(K2 /. renaming[[2]])]
	];
AppendTo[DNSumExtRules, RuleSumAddComp3];

RuleSumAddComp4 = SUMK[idx1_, S1_ ~SCRK~ K1_] ~ADDK~ SUMK[idx2_, S2_ ~SCRK~ K2_] /; 
	IdxUnifyQ[idx1, idx2]&&IdxUnifySameTermQ[idx1, idx2, K1, K2] :>
	With[
		{renaming=IdxUnify[idx1, idx2]},
		SUMK[idx1/.renaming[[1]], ((S1/.renaming[[1]])~ADDS~(S2/.renaming[[2]]))~SCRK~(K2 /. renaming[[2]])]
	];
AppendTo[DNSumExtRules, RuleSumAddComp4];

RuleSumAddComp5 = SUMB[idx1_, S_ ~SCRB~ B1_] ~ADDB~ SUMB[idx2_, B2_] /; 
	IdxUnifyQ[idx1, idx2]&&IdxUnifySameTermQ[idx1, idx2, B1, B2] :>
	With[
		{renaming=IdxUnify[idx1, idx2]},
		SUMB[idx1/.renaming[[1]], ((S/.renaming[[1]])~ADDS~CPX[1])~SCRB~(B2 /. renaming[[2]])]
	];
AppendTo[DNSumExtRules, RuleSumAddComp5];

RuleSumAddComp6 = SUMB[idx1_, S1_ ~SCRB~ B1_] ~ADDB~ SUMB[idx2_, S2_ ~SCRB~ B2_] /; 
	IdxUnifyQ[idx1, idx2]&&IdxUnifySameTermQ[idx1, idx2, B1, B2] :>
	With[
		{renaming=IdxUnify[idx1, idx2]},
		SUMB[idx1/.renaming[[1]], ((S1/.renaming[[1]])~ADDS~(S2/.renaming[[2]]))~SCRB~(B2 /. renaming[[2]])]
	];
AppendTo[DNSumExtRules, RuleSumAddComp6];

RuleSumAddComp7 = SUMO[idx1_, S_ ~SCRO~ O1_] ~ADDO~ SUMO[idx2_, O2_] /; 
	IdxUnifyQ[idx1, idx2]&&IdxUnifySameTermQ[idx1, idx2, O1, O2] :>
	With[
		{renaming=IdxUnify[idx1, idx2]},
		SUMO[idx1/.renaming[[1]], ((S/.renaming[[1]])~ADDS~CPX[1])~SCRO~(O2 /. renaming[[2]])]
	];
AppendTo[DNSumExtRules, RuleSumAddComp7];

RuleSumAddComp8 = SUMO[idx1_, S1_ ~SCRO~ O1_] ~ADDO~ SUMO[idx2_, S2_ ~SCRO~ O2_] /; 
	IdxUnifyQ[idx1, idx2]&&IdxUnifySameTermQ[idx1, idx2, O1, O2] :>
	With[
		{renaming=IdxUnify[idx1, idx2]},
		SUMO[idx1/.renaming[[1]], ((S1/.renaming[[1]])~ADDS~(S2/.renaming[[2]]))~SCRO~(O2 /. renaming[[2]])]
	];
AppendTo[DNSumExtRules, RuleSumAddComp8];


(* ::Subsubsection:: *)
(*EntryExpand*)


EntryExpandS[S_?AtomQ]:=S;
EntryExpandS[S:CPX[_]|DELTA[_,_]]:=S;
EntryExpandS[S1_ ~ADDS~ S2_]:=EntryExpandS[S1] ~ADDS~ EntryExpandS[S2];
EntryExpandS[S1_ ~MLTS~ S2_]:=EntryExpandS[S1] ~MLTS~ EntryExpandS[S2];
EntryExpandS[CONJS[S_]]:=CONJS[EntryExpandS[S]];
EntryExpandS[B_ ~DOT~ K_]:=EntryExpandB[B] ~DOT~ EntryExpandK[K];
EntryExpandS[SUMS[idx_, S_]]:=SUMS[idx, EntryExpandS[S]];
EntryExpandS[S_]:=S;

EntryExpandK[K:ZEROK[_]|KET[_]]:=K;
EntryExpandK[ADJK[B_]]:=ADJK[EntryExpandB[B]];
EntryExpandK[S_ ~SCRK~ K_]:=EntryExpandS[S] ~SCRK~ EntryExpandK[K];
EntryExpandK[K1_ ~ADDK~ K2_]:=EntryExpandK[K1] ~ADDK~ EntryExpandK[K2];
EntryExpandK[O0_ ~MLTK~ K_]:=EntryExpandO[O0] ~MLTK~ EntryExpandK[K];
EntryExpandK[K1_ ~TSRK~ K2_]:=EntryExpandK[K1] ~TSRK~ EntryExpandK[K2];
EntryExpandK[SUMK[idx_, K_]]:=SUMK[idx, EntryExpandK[K]];
EntryExpandK[K_]:=With[{nv=Unique[]}, SUMK[nv, USET[TypeProjK[TypeCalc[K]]], (BRA[nv]~DOT~K)~SCRK~KET[nv]]];

EntryExpandB[B:ZEROB[_]|BRA[_]]:=B;
EntryExpandB[ADJB[K_]]:=ADJB[EntryExpandK[K]];
EntryExpandB[S_ ~SCRB~ B_]:=EntryExpandS[S] ~SCRB~ EntryExpandB[B];
EntryExpandB[B1_ ~ADDB~ B2_]:=EntryExpandB[B1] ~ADDB~ EntryExpandB[B2];
EntryExpandB[B_ ~MLTB~ O0_]:=EntryExpandB[B] ~MLTB~ EntryExpandO[O0];
EntryExpandB[B1_ ~TSRB~ B2_]:=EntryExpandB[B1] ~TSRB~ EntryExpandB[B2];
EntryExpandB[SUMB[idx_, B_]]:=SUMB[idx, EntryExpandB[B]];
EntryExpandB[B_]:=With[{nv=Unique[]}, SUMB[nv, USET[TypeProjB[TypeCalc[B]]], (B~DOT~KET[nv])~SCRB~BRA[nv]]];

EntryExpandO[O0:ZEROO[_, _]|ONEO[_]]:=O0;
EntryExpandO[K_ ~OUTER~ B_]:=EntryExpandK[K] ~OUTER~ EntryExpandB[B];
EntryExpandO[ADJO[O0_]]:=ADJO[EntryExpandO[O0]];
EntryExpandO[S_ ~SCRO~ O0_]:=EntryExpandS[S] ~SCRO~ EntryExpandO[O0];
EntryExpandO[O1_ ~ADDO~ O2_]:=EntryExpandO[O1] ~ADDO~ EntryExpandO[O2];
EntryExpandO[O1_ ~TSRO~ O2_]:=EntryExpandO[O1] ~TSRO~ EntryExpandO[O2];
EntryExpandO[O1_ ~MLTO~ O2_]:=EntryExpandO[O1] ~MLTO~ EntryExpandO[O2];
EntryExpandO[SUMO[idx_, O_]]:=SUMO[idx, EntryExpandO[O]];
EntryExpandO[O0_]:=With[{i=Unique[], j=Unique[]}, SUMO[
	IDX[{i, USET[TypeProjK[TypeCalc[O0]]]}, {j, USET[TypeProjB[TypeCalc[O0]]]}], 
	(BRA[i]~DOT~(O0~MLTK~KET[j]))~SCRO~(KET[i]~OUTER~BRA[j])
]];

(* Unify the interface. *)
DNEntryExpand[S1_ ~ADDS~ S2_]:=EntryExpandS[S1] ~ADDS~ EntryExpandS[S2];
DNEntryExpand[S1_ ~MLTS~ S2_]:=EntryExpandS[S1] ~MLTS~ EntryExpandS[S2];
DNEntryExpand[CONJS[S_]]:=CONJS[EntryExpandS[S]];
DNEntryExpand[B_ ~DOT~ K_]:=EntryExpandB[B] ~DOT~ EntryExpandK[K];
DNEntryExpand[SUMS[idx_, S_]]:=SUMS[idx, EntryExpandS[S]];

DNEntryExpand[ADJK[B_]]:=ADJK[EntryExpandB[B]];
DNEntryExpand[S_ ~SCRK~ K_]:=EntryExpandS[S] ~SCRK~ EntryExpandK[K];
DNEntryExpand[K1_ ~ADDK~ K2_]:=EntryExpandK[K1] ~ADDK~ EntryExpandK[K2];
DNEntryExpand[O0_ ~MLTK~ K_]:=EntryExpandO[O0] ~MLTK~ EntryExpandK[K];
DNEntryExpand[K1_ ~TSRK~ K2_]:=EntryExpandK[K1] ~TSRK~ EntryExpandK[K2];
DNEntryExpand[SUMK[idx_, K_]]:=SUMK[idx, EntryExpandK[K]];

DNEntryExpand[ADJB[K_]]:=ADJB[EntryExpandK[K]];
DNEntryExpand[S_ ~SCRB~ B_]:=EntryExpandS[S] ~SCRB~ EntryExpandB[B];
DNEntryExpand[B1_ ~ADDB~ B2_]:=EntryExpandB[B1] ~ADDB~ EntryExpandB[B2];
DNEntryExpand[B_ ~MLTB~ O0_]:=EntryExpandB[B] ~MLTB~ EntryExpandO[O0];
DNEntryExpand[B1_ ~TSRB~ B2_]:=EntryExpandB[B1] ~TSRB~ EntryExpandB[B2];
DNEntryExpand[SUMB[idx_, B_]]:=SUMB[idx, EntryExpandB[B]];

DNEntryExpand[K_ ~OUTER~ B_]:=EntryExpandK[K] ~OUTER~ EntryExpandB[B];
DNEntryExpand[ADJO[O0_]]:=ADJO[EntryExpandO[O0]];
DNEntryExpand[S_ ~SCRO~ O0_]:=EntryExpandS[S] ~SCRO~ EntryExpandO[O0];
DNEntryExpand[O1_ ~ADDO~ O2_]:=EntryExpandO[O1] ~ADDO~ EntryExpandO[O2];
DNEntryExpand[O1_ ~TSRO~ O2_]:=EntryExpandO[O1] ~TSRO~ EntryExpandO[O2];
DNEntryExpand[O1_ ~MLTO~ O2_]:=EntryExpandO[O1] ~MLTO~ EntryExpandO[O2];
DNEntryExpand[SUMO[idx_, O_]]:=SUMO[idx, EntryExpandO[O]];

(* the following three rules expand variables according to the context *)

DNEntryExpand[X_/;InDiracCtxQ[X]&&MatchQ[TypeCalc[X], KType[_]]]:=EntryExpandK[X];
DNEntryExpand[X_/;InDiracCtxQ[X]&&MatchQ[TypeCalc[X], BType[_]]]:=EntryExpandB[X];
DNEntryExpand[X_/;InDiracCtxQ[X]&&MatchQ[TypeCalc[X], OType[_,_]]]:=EntryExpandO[X];

DNEntryExpand[X_]:=X;



(* ::Subsubsection:: *)
(*EntryReduce*)


DNEntryReduceRules = {};
RuleEntryReduce1 = SUMK[IDX[{i_, USET[_]}, indices___], (BRA[i_]~DOT~K_)~SCRK~KET[i_]] -> SUMK[IDX[indices], K];
AppendTo[DNEntryReduceRules, RuleEntryReduce1];

RuleEntryReduce2 = SUMB[IDX[{i_, USET[_]}, indices___], (B_~DOT~KET[i_])~SCRB~BRA[i_]] -> SUMB[IDX[indices], B];
AppendTo[DNEntryReduceRules, RuleEntryReduce2];

RuleEntryReduce3 = SUMO[IDX[{i1_, USET[_]}, {i2_, USET[_]}, indices___], (BRA[i1_]~DOT~(A_~MLTK~KET[i2_]))~SCRO~(KET[i1_]~OUTER~BRA[i2_])] -> SUMO[IDX[indices], A];
AppendTo[DNEntryReduceRules, RuleEntryReduce3];


(* ::Subsection:: *)
(*Unification Preprocessing*)


(* ::Text:: *)
(*alpha-conversion is dealt in this unification.*)


UnifyPreproc[s1:(sop:SUMS|SUMK|SUMB|SUMO)[idx1_, body1_], s2:(sop:SUMS|SUMK|SUMB|SUMO)[idx2_, body2_]] := 
	Module[
		{
			bindvs1=BindVars[s1], 
			bindvs2=BindVars[s2],
			newbdvs1, newbdvs2
		}, 
		newbdvs1=Table[Unique[], Length[bindvs1]]; newbdvs2=Table[Unique[], Length[bindvs2]];
		{s1/.Thread[bindvs1 -> newbdvs1], s2/.Thread[bindvs2 -> newbdvs2], Join[newbdvs1, newbdvs2]}
	];


End[];


EndPackage[];
