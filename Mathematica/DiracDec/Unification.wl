(* ::Package:: *)

u


(* ::Title:: *)
(*Unification*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["Unification`"];


UnifyPreproc::usage = "The preprocessing function for unification of expressions. Should return: {newlhs, newrhs, newvars}.";

Unify::usage = "Unify[term1_, term2_, vars_] Return: False if not unifiable, one substitution if unifiable. Supports Orderless unification (by branching and backtracking). 
	The vars should be in forms of {{vars1...}, {vars2...}, ...}, indicating that variables in the same set cannot be assigned to each other.";


Begin["Private`"];


(*Helper function to check if a variable occurs in a term*)
OccursInQ[x_,expr_]:=MemberQ[Variables[expr],x];

(* eqtheory: a list of rewriting rules representing the avaiable equational theory to use *)
UnifyStep[substitutions_, equations_, vars_, eqtheory_] := Module[
		{
			subst=substitutions,
			varnames = Union@@vars,
			eqs=equations,
			lhs, rhs,
			procEq,
			perm, i,
			branchRes
		},
		(* >>>>>>>>>>>>>>>>>>>>>>>>> *)
		(* for debug output purpose *)
		(*Print["New Branch Substitution ", substitutions];
		Print["Vars: ", vars];*)
		(* <<<<<<<<<<<<<<<<<<<<<<<< *)
		While[Length[eqs]>0,
			(*Print["    Equation: ", eqs];*)
			lhs=eqs[[1]][[1]]//.eqtheory;
			rhs=eqs[[1]][[2]]//.eqtheory;
			Which[
				lhs===rhs || TrueQ[FullSimplify[lhs==rhs]],
				eqs = Rest[eqs]; Continue[],
				
				(* check equivalence of numbers *)
				(* This check don't work *)
				(*
				MemberQ[{Complex,Real,Rational,Integer}, Head[lhs]]
				&& Head[rhs]===Head[lhs]
				&& TrueQ[FullSimplify[lhs==rhs]],
				eqs = Rest[eqs]; Continue[],
				*)
				
				MemberQ[varnames, lhs],
				If[
					OccursInQ[lhs, rhs]||(AtomQ[rhs]&&AnyTrue[vars, Length[Intersection[{lhs, rhs},#]]==2&]),
					Return[False],
					subst=Join[subst/.lhs->rhs, {lhs->rhs}]; eqs=Rest[eqs]/.{lhs->rhs}; Continue[]
				],
				
				MemberQ[varnames, rhs],
				If[
					OccursInQ[rhs, lhs]||(AtomQ[lhs]&&AnyTrue[vars, Length[Intersection[{lhs, rhs},#]]==2&]),
					Return[False],
					subst=Join[subst/.rhs->lhs, {rhs->lhs}]; eqs=Rest[eqs]/.{rhs->lhs}; Continue[]
				],
				
				MatchQ[lhs, _[___]]&&MatchQ[rhs, _[___]],
				If[
					Head[lhs]=!=Head[rhs]||Length[lhs]=!=Length[rhs]||Length[lhs]===0,
					Return[False],
					procEq = UnifyPreproc[lhs, rhs];
					If[
						MemberQ[Attributes[Evaluate[Head[procEq[[1]]]]], Orderless],
						
						(* Match the first of procEq[[1]] with different elements in procEq[[2]] *)
						For[i=1, i<=Length[procEq[[2]]], i++,
							(* Use recursion to search in different branches *)
							branchRes = UnifyStep[
								subst, 
								Join[{{procEq[[1]][[1]], procEq[[2]][[i]]}, {Rest[procEq[[1]]], Drop[procEq[[2]],{i}]}}, Rest[eqs]], 
								Union[vars, procEq[[3]]],
								eqtheory
							];
							If[branchRes=!=False, Return[branchRes]];
						];
						(*Print["Branch Searching Failed"];*)
						Return[False],
						
						If[Length[procEq[[3]]]>0,
							Return[
								UnifyStep[
									subst, 
									Join[Transpose[{List@@(procEq[[1]]), List@@(procEq[[2]])}], Rest[eqs]], 
									Union[vars, procEq[[3]]],
									eqtheory
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

VarsOf[term1_, term2_]:=Union[Cases[term1,_Symbol,{0,Infinity}],Cases[term2,_Symbol,{0,Infinity}]];

Unify[term1_, term2_, vars_, eqtheory_]:=UnifyStep[{}, {{term1, term2}}, vars, eqtheory];
Unify[term1_, term2_, vars_]:=UnifyStep[{}, {{term1, term2}}, vars, {}];
Unify[term1_, term2_]:=UnifyStep[{}, {{term1, term2}}, VarsOf[term1, term2], {}];
Unify[___]:=Throw["Invalid Arguments for Unify."];

SetAttributes[Unify, Protected];


End[];


EndPackage[];
