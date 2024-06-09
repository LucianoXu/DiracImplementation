(* ::Package:: *)

(* ::Title:: *)
(*Typing*)


(* The infrastructure for typing. *)
BeginPackage["Typing`", {"Notation`"}];


Typing::usage = "The symbol for typing. Typing[x, T] means the term x has type T.";
GetType::usage = "GetType will return the type of a typing object.";
TypingRuleCompile::usage = "Compile a typing assigning represented by a list, into a compiled package of typing rules.";
ConcatCompiled::usage = "Concatenate two compiled typing rule packages.";
TypeCheck::usage = "TypeCheck[t,assign] checks the typing according to the given typing assignings.";

RemoveType::usage = "RemoveType[t] will remove all typing hints in the term t.";
RemoveInnerType::usage = "RemoveInnerType[t] will remove all typing hints other than the head typing. Intended for printing the final result.";


Begin["Notate`"];

LeftTriangle=Typing;
Notation[
	ParsedBoxWrapper[RowBox[{"a_", "\[LeftTriangle]", "b_"}]] 
	\[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"Typing", "[", "a_", ",", "b_", "]"}]]
];

End[];


Begin["Private`"];
(* Simplify nested typing *)
Typing[Typing[t_,T_],T_]:=Typing[t,T];

GetType[Typing[x_,T_]]:=T;

(* 
about type checking:
A type checking rule is a key value pair

	<pattern> -> T

It means that the term matching the pattern on the left should be annoted with type T.
*)

TypingAssign2TypingRule[assign_List]:=
	With[{body=Unique[]},Map[
		If[Head[#]===RuleDelayed,
			(body:#[[1]]):>body\[LeftTriangle]#[[2]],
			(body:#[[1]])->body\[LeftTriangle]#[[2]]
		]&,
		assign]
	];

FinilizeWrapping[rule_]:=
	If[Head[rule]===RuleDelayed,
		(h:Except[Typing|LeftTriangle])[l___,rule[[1]], r___] :> h[l,rule[[2]],r],
		(h:Except[Typing|LeftTriangle])[l___,rule[[1]], r___] -> h[l,rule[[2]],r]
	]

(* 
	This Type Checking will apply the FinilizedTypingRules repeatedly, fill in the typings, and try to add the typing hint to the root. 
	This method can be time consuming in repeated invoking, because it recompiles the rules everytime.
*)

(* an empty compiled typing rule package *)
EmptyCompiled=<|TypingRule->{}, SubtermTyping->{}|>;

TypingRuleCompile[assign_List]:=
	Module[
		{TypingAssigns=TypingAssign2TypingRule[assign]},
		<|TypingRule->TypingAssigns, SubtermTyping->FinilizeWrapping/@TypingAssigns|>
	];
	
ConcatCompiled[comp1_,comp2_]:=<|TypingRule->comp1[TypingRule]\[Union]comp2[TypingRule], SubtermTyping->comp1[SubtermTyping]\[Union]comp2[SubtermTyping]|>;

(* the method for type rewriting *)

Options[TypeCheck] = {Compiled -> EmptyCompiled};
TypeCheck[t_, assign_List:{}, OptionsPattern[]]:=
	With[
		{finalCompiled=ConcatCompiled[TypingRuleCompile[assign],OptionValue[Compiled]]},
		Replace[t//.finalCompiled[SubtermTyping], finalCompiled[TypingRule]]
	];

RemoveType[t_,levelspec_:{0,Infinity}]:=FixedPoint[Replace[#,x_\[LeftTriangle]T_->x,levelspec]&,t];

RemoveInnerType[t_Typing]:=RemoveType[t[[1]]]\[LeftTriangle]t[[2]];

End[];


EndPackage[];
