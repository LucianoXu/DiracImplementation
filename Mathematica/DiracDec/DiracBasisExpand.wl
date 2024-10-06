(* ::Package:: *)

(* ::Title:: *)
(*DiracBasisExpand*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracBasisExpand`", {"DiracCore`", "DiracSumExt`"}];


DNBasisExpandRules;


Begin["Private`"];


DNBasisExpandRules = {};


RuleBasisExpand1 = USET[s_List]->s;
AppendTo[DNBasisExpandRules, RuleBasisExpand1];


RuleBasisExpand2 = SUMS[IDX[{i_, s_List}, indices___], body_] :> SUMS[IDX[indices], ADDS@@((body/.{i->#})&/@s)];
AppendTo[DNBasisExpandRules, RuleBasisExpand2];


RuleBasisExpand3 = SUMK[IDX[{i_, s_List}, indices___], body_] :> SUMK[IDX[indices], ADDK@@((body/.{i->#})&/@s)];
AppendTo[DNBasisExpandRules, RuleBasisExpand3];


RuleBasisExpand4 = SUMB[IDX[{i_, s_List}, indices___], body_] :> SUMB[IDX[indices], ADDB@@((body/.{i->#})&/@s)];
AppendTo[DNBasisExpandRules, RuleBasisExpand4];


RuleBasisExpand5 = SUMO[IDX[{i_, s_List}, indices___], body_] :> SUMO[IDX[indices], ADDO@@((body/.{i->#})&/@s)];
AppendTo[DNBasisExpandRules, RuleBasisExpand5];


End[];


EndPackage[];
