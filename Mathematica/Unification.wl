(* ::Package:: *)

(* ::Title:: *)
(*Unification*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["Unification`"];


UnifyPreproc::usage = "The preprocessing function for unification of expressions. Should return: {newlhs, newrhs, newvars}.";

Unify::usage = "Unify[term1_, term2_, vars_]
Return: False if not unifiable, one substitution if unifiable.
Supports Orderless unification (by branching and backtracking). ";


Begin["Private`"];


(*Helper function to check if a variable occurs in a term*)
OccursInQ[x_,expr_]:=MemberQ[Variables[expr],x];

PermutePairs[list1_, list2_] := With[
	{perm2 = Permutations[list2]},
	Transpose/@Table[{list1, permls}, {permls, perm2}]
];

UnifyStep[substitutions_, equations_, vars_] := Module[
		{
			subst=substitutions,
			eqs=equations,
			lhs, rhs,
			procEq,
			perm, i,
			branchRes
		},
(*		Print["New Branch: ", substitutions, equations];
		Print["Vars: ", vars];*)
		While[Length[eqs]>0,
			lhs=eqs[[1]][[1]];
			rhs=eqs[[1]][[2]];
			Which[
				lhs===rhs,
				eqs = Rest[eqs]; Continue[],
				
				MemberQ[vars, lhs],
				If[
					OccursInQ[lhs, rhs],
					Return[False],
					AppendTo[subst, lhs->rhs]; eqs=Rest[eqs]/.{lhs->rhs}; Continue[]
				],
				
				MemberQ[vars, rhs],
				If[
					OccursInQ[rhs, lhs],
					Return[False],
					AppendTo[subst, rhs->lhs]; eqs=Rest[eqs]/.{rhs->lhs}; Continue[]
				],
				
				MatchQ[lhs, _[___]]&&MatchQ[rhs, _[___]],
				If[
					Head[lhs]=!=Head[rhs]||Length[lhs]=!=Length[rhs],
					Return[False],
					procEq = UnifyPreproc[lhs, rhs];
					If[
						MemberQ[Attributes[Evaluate[Head[procEq[[1]]]]], Orderless],
						
						perm = PermutePairs[List@@(procEq[[1]]), List@@(procEq[[2]])];
						For[i=1, i<=Length[perm], i++,
							(* Use recursion to search in different branches *)
							branchRes = UnifyStep[subst, Join[perm[[i]], Rest[eqs]], Join[vars, procEq[[3]]]];
							If[branchRes=!=False, Return[branchRes]];
						];
						Return[False],
						
						If[Length[procEq[[3]]]>0,
							Return[
								UnifyStep[
									subst, 
									Join[Transpose[{List@@(procEq[[1]]), List@@(procEq[[2]])}], Rest[eqs]], 
									Join[vars, procEq[[3]]]
								]
							],
								
							eqs = Join[Transpose[{List@@(procEq[[1]]), List@@(procEq[[2]])}], Rest[eqs]]; Continue[]
						]
					]
				],
				
				True,
				Return[False]
			]
		];
		
		Return[subst]
	];
	

(* default behaviour *)
UnifyPreproc[term1_, term2_] := {term1, term2, {}};


(*
	Main unification function
	Return: False if not unifiable, one substitution if unifiable.
*)
Unprotect[Unify];

Unify[term1_, term2_, vars_]:=UnifyStep[{}, {{term1, term2}}, vars];
Unify[term1_, term2_]:=UnifyStep[{}, {{term1, term2}}, {}];
Unify[___]:=Throw["Invalid Arguments for Unify."];

SetAttributes[Unify, Protected];


End[];


EndPackage[];
