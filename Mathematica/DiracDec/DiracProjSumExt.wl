(* ::Package:: *)

(* ::Title:: *)
(*Dirac Notation Projection Sum Extension*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracProjSumExt`",{"DiracCore`","DiracProjExt`","DiracSumExt`"}];


DNProjSumRules;


Begin["Private`"];


DNProjSumRules = {};


(* ::Subsubsection:: *)
(*Index Split*)


RuleIndexSplit1 = (sum:SUMS|SUMK|SUMB|SUMO)[IDX[{i_, USET[sigma_ ~ProdType~ tau_]}, indices___], body_]/;
	!FreeQ[body, FST[i]|SND[i]] :> 
	With[{nv1=Unique[], nv2=Unique[]}, sum[IDX[{nv1, USET[sigma]}, {nv2, USET[tau]}, indices], body//.{FST[i]->nv1, SND[i]->nv2, i->PAIR[nv1,nv2]}]];
AppendTo[DNProjSumRules, RuleIndexSplit1];

RuleIndexSplit2 = (sum:SUMS|SUMK|SUMB|SUMO)[IDX[{i_, M1_ ~SETPROD~ M2_}, indices___], body_]/;
	!FreeQ[body, FST[i]|SND[i]] :> 
	With[{nv1=Unique[], nv2=Unique[]}, sum[IDX[{nv1, M1}, {nv2, M2}, indices], body//.{FST[i]->nv1, SND[i]->nv2, i->PAIR[nv1,nv2]}]];
AppendTo[DNProjSumRules, RuleIndexSplit2];


RuleIndexSplit3 = (sum:SUMS|SUMK|SUMB|SUMO)[IDX[{i_, M1_}, {j_, M2_}, indices___], body_]/;
	And[
		Length[Position[body, PAIR[i,j]]]===Length[Position[body, i]], 
		Length[Position[body, PAIR[i,j]]]===Length[Position[body, j]]
	] :> 
	With[{nv=Unique[]}, sum[IDX[{nv, M1 ~SETPROD~ M2}, indices], body//.(PAIR[i,j]->nv)]];
AppendTo[DNProjSumRules, RuleIndexSplit3];


End[];


EndPackage[];
