(* ::Package:: *)

(* ::Title:: *)
(*Confluence*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["Confluence`","Unification`"];


Joinable;
Confluence;


Begin["Private`"];


JoinableQ[term1_, term2_, rules_]:=(term1//.rules)===(term2//.rules);


RuleProc[rule_]:=Module[
	{lhs=rule[[1]]/.(p_Pattern:>p[[1]]), rhs=rule[[2]], vars,newvars,renaming},
	
	vars=Union[Cases[rule[[1]],p_Pattern:>p[[1]],{0,Infinity}]];
	newvars=Table[Unique[],Length[vars]];
	renaming=Thread[vars->newvars];
	{lhs/.renaming, rhs/.renaming, newvars}
];


Subterms[term_]:={#,term[[Sequence@@#]]}&/@Position[term,p_/;!AtomQ[p]];


CriticalPair[rule1_, rule2_, ruleset_]:=Module[
	{
		procrule1=RuleProc[rule1],procrule2=RuleProc[rule2],vars,
		subterms1,unifyres, cps,cpsrewrite
	},
	
	vars=Join[procrule1[[3]],procrule2[[3]]];
	subterms1=Subterms[procrule1[[1]]];
	unifyres=Select[
		{#[[1]],Unify[procrule2[[1]],#[[2]],vars]}&/@subterms1,
		#[[2]]=!=False&
	];
	(* Construct Critical Pairs *)
	cps=<|
		"root"->procrule1[[1]]/.(#[[2]]),
		"CP"->{ReplaceAt[procrule1[[1]]/.(#[[2]]),rule2,#[[1]]], procrule1[[2]]/.(#[[2]])}
		|>&/@unifyres;
	cpsrewrite=Select[<|
		"root"->#["root"],
		"CP"->#["CP"],
		"RewriteRes"->{#["CP"][[1]]//.ruleset,#["CP"][[2]]//.ruleset},
		"Rules"->{rule1, rule2}
		|>&/@cps,FullSimplify[#["RewriteRes"][[1]]==#["RewriteRes"][[2]]]=!=True&];
	{cps,cpsrewrite}
];


Confluence[ruleset_]:=Module[
	{rulepairs=Tuples[ruleset,2],allcps={},unjoinablecps={},i,progress=0,total,pairRes},
	
	total=Length[rulepairs];
	CreateDialog[Column[{"Processing...",Dynamic[ProgressIndicator[progress,{0,total}]],Dynamic[progress]}]];
	For[i=1,i<=total,i++,
		pairRes=CriticalPair[rulepairs[[i]][[1]],rulepairs[[i]][[2]],ruleset];
		allcps=Join[allcps,pairRes[[1]]];
		unjoinablecps=Join[unjoinablecps,pairRes[[2]]];
		progress=i;
	];
	{allcps,unjoinablecps}
];


End[];


EndPackage[];
