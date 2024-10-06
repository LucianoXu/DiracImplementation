(* ::Package:: *)

(* ::Title:: *)
(*RewritingPlus*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["RewritingPlus`"];


InnermostReplaceAll::usage="Innermost rewriting";
RuleFirstReplaceAll::usage="Rule First Rewriting (input should be rule set)";


Begin["Private`"];


(* ::Subsection:: *)
(*Innermost Rewriting*)


InnermostReplaceAll[rules_][expr_]:=
	FixedPoint[
		(*-------------------------------*)
		Function[
			input,
			FixedPoint[
				ReplaceAll[rules],
				If[AtomQ[input],
					input,
					(InnermostReplaceAll[rules][input[[0]]])@@(Map[InnermostReplaceAll[rules],input])
				]
			]
		],
		(*-------------------------------*)
		expr
];

InnermostReplaceAll[expr_, rules_] := InnermostReplaceAll[rules][expr];


(* ::Subsection:: *)
(*Rulefirst Rewriting*)


RuleFirstReplaceAll[rules_][expr_]:=
	FixedPoint[
		Function[
			input,
			Fold[#1//.#2&, input, rules]
		],
		expr
];

RuleFirstReplaceAll[expr_, rules_] := InnermostReplaceAll[rules][expr];


End[];


EndPackage[];
