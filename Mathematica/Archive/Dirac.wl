(* ::Package:: *)

(* ::Title:: *)
(*Dirac Notations*)


ClearAll["Dirac`*"];

AppendTo[$Path,NotebookDirectory[]];
BeginPackage["Dirac`",{"Notation`","Typing`"}];

Off[RuleDelayed::rhs];


(* ::Chapter:: *)
(*Dirac Notation: Core Language*)


(* ::Section:: *)
(*Public Interface*)


(* Typing symbols for Dirac notations *)
SType;
\[ScriptCapitalS];

KType;
\[ScriptCapitalK];

BType;
\[ScriptCapitalB];

OType;
\[ScriptCapitalO];

(* Typing symbol for product type of Hilbert spaces *)
Prod;

Pair;
Fst;
Snd;

Delta;

(* We directly use Plus and Times in Mathematica to serve our purpose. *)
Plus;
Times;

Zero::usage = "The zero notation for scalar, ket, bra or operator";
OneO;

(* We borrow symbol C from Wolfram Language to act as the symbol of Complex Numbers *)
C;

(* Ket and Bra is already introduced in Mathematica with formating purpose only. 
NOTE: to make use of the notation |x> and <y| for Ket and Bra, we design the rules to be 
Ket[{x\[LeftTriangle]T}] : KType[T], and similarly for bra.
*)
Ket;
Bra;

(* We use ConjugateTranspose for conjugate transpose *)
Conjugate;
ConjugateTranspose;

(* CenterDot is already introduced in Mathematica. *)
Dot;

(* CircleTimes for tensor product 
	We don't use TensorProduct predefined in MMA, because it is associative, while that in our language should not be.
*)
CircleTimes;


TypingAssigns::usage = "The typing rules for Dirac notation.";

DiracTypeCheck::usage = "Check and infer the typing of the term.";

RewritingRules::usage = "The rewriting rules for Dirac notation";

DiracNorm::usage = "Type check and normalize the term.";


Begin["Core`"];


(* ::Section::Closed:: *)
(*Notations*)


Begin["Notate`"];

\[ScriptCapitalS]=SType;
Notation[
	ParsedBoxWrapper[RowBox[{"\[ScriptCapitalS]"}]] 
	\[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"SType"}]]
];

\[ScriptCapitalK]=KType;
Notation[
	ParsedBoxWrapper[SubscriptBox["\[ScriptCapitalK]","T_"]] 
	\[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"KType","[","T_","]"}]]
];

\[ScriptCapitalB]=BType;
Notation[
	ParsedBoxWrapper[SubscriptBox["\[ScriptCapitalB]","T_"]] 
	\[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"BType","[","T_","]"}]]
];

\[ScriptCapitalO]=OType;
Notation[
	ParsedBoxWrapper[SubscriptBox["\[ScriptCapitalO]",RowBox[{"T1_",",","T2_"}]]] 
	\[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"OType","[","T1_",",","T2_","]"}]]
];

Notation[
	ParsedBoxWrapper[RowBox[{"(","t1_",",","t2_",")"}]]
	\[DoubleLongLeftArrow] ParsedBoxWrapper[RowBox[{"Pair","[","t1_",",","t2_","]"}]]
]

Notation[
	ParsedBoxWrapper[SubscriptBox["\[Delta]",RowBox[{"t1_",",","t2_"}]]] 
	\[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"Delta","[","t1_",",","t2_","]"}]]
];

Diamond=Prod;
Notation[
	ParsedBoxWrapper[RowBox[{"a_", "\[Diamond]", "b_"}]] 
	\[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"Prod", "[", "a_", ",", "b_", "]"}]]
];

Notation[
	ParsedBoxWrapper[RowBox[{"(", "a_", "\[Diamond]", "b_", ")"}]] 
	\[DoubleLongLeftArrow] ParsedBoxWrapper[RowBox[{"Prod", "[", "a_", ",", "b_", "]"}]]
];

Notation[
	ParsedBoxWrapper[RowBox[{"(","t_","\[LeftTriangle]","T_",")", "\[ConjugateTranspose]"}]]
	\[DoubleLongLeftArrow] ParsedBoxWrapper[RowBox[{"ConjugateTranspose", "[", "Typing", "[", "t_", ",", "T_", "]","]"}]] 
];

End[];


(* ::Section:: *)
(*Typing of Dirac Notations*)


Begin["Typings`"];

(* 
These two assignments enables infix notations used in this package.
The problem is that the notation defined above cannot be directly used in the package itself.*)


(* about matching types *)
DiracTypePatt=\[ScriptCapitalS]|\[ScriptCapitalK][_]|\[ScriptCapitalB][_]|\[ScriptCapitalO][_,_];
DiracKBOTypePatt=\[ScriptCapitalK][_]|\[ScriptCapitalB][_]|\[ScriptCapitalO][_,_];

DualType[\[ScriptCapitalS]]:=\[ScriptCapitalS];
DualType[\[ScriptCapitalK][T_]]:=\[ScriptCapitalB][T];
DualType[\[ScriptCapitalB][T_]]:=\[ScriptCapitalK][T];
DualType[\[ScriptCapitalO][T1_,T2_]]:=\[ScriptCapitalO][T2,T1];
DualType[DualType[T_]]:=T;

(* checking of dual types *)
TypeDualQ[T1_,T2_]:=T1===DualType[T2];


(* calculate the result type of dot *)
DotType[\[ScriptCapitalB][T_],\[ScriptCapitalK][T_]]:=\[ScriptCapitalS];
DotType[\[ScriptCapitalO][T1_,T2_],\[ScriptCapitalK][T2_]]:=\[ScriptCapitalK][T1];
DotType[\[ScriptCapitalB][T1_],\[ScriptCapitalO][T1_,T2_]]:=\[ScriptCapitalB][T2];
DotType[\[ScriptCapitalO][T1_,T2_],\[ScriptCapitalO][T2_,T3_]]:=\[ScriptCapitalO][T1,T3];


(* checking of matching dot types *)
DotTypeMatchQ[T1_,T2_]:=
	MatchQ[{T1,T2},{\[ScriptCapitalB][_],\[ScriptCapitalK][_]}]||
	MatchQ[{T1,T2},{\[ScriptCapitalO][_,_],\[ScriptCapitalK][_]}]||
	MatchQ[{T1,T2},{\[ScriptCapitalB][_],\[ScriptCapitalO][_,_]}]||
	MatchQ[{T1,T2},{\[ScriptCapitalO][_,_],\[ScriptCapitalO][_,_]}];

(* checking of matching dot types *)
DotTypeMatchQ[T1_,T2_,Res_]:=DotTypeMatchQ[T1,T2]&&Res===DotType[T1,T2];

(* calculate the result type of tensor (all 16 combinations of {S, K, B, O}^2 are allowed) *)
TensorType[\[ScriptCapitalS],\[ScriptCapitalS]]:=\[ScriptCapitalS];
TensorType[\[ScriptCapitalS],\[ScriptCapitalK][T_]]:=\[ScriptCapitalK][T];
TensorType[\[ScriptCapitalK][T_],\[ScriptCapitalS]]:=\[ScriptCapitalK][T];
TensorType[\[ScriptCapitalS],\[ScriptCapitalB][T_]]:=\[ScriptCapitalB][T];
TensorType[\[ScriptCapitalB][T_],\[ScriptCapitalS]]:=\[ScriptCapitalB][T];
TensorType[\[ScriptCapitalS],\[ScriptCapitalO][T1_,T2_]]:=\[ScriptCapitalO][T1,T2];
TensorType[\[ScriptCapitalO][T1_,T2_],\[ScriptCapitalS]]:=\[ScriptCapitalO][T1,T2];
TensorType[\[ScriptCapitalB][T1_],\[ScriptCapitalK][T2_]]:=\[ScriptCapitalO][T2,T1];
TensorType[\[ScriptCapitalK][T1_],\[ScriptCapitalB][T2_]]:=\[ScriptCapitalO][T1,T2];
TensorType[\[ScriptCapitalK][T1_],\[ScriptCapitalK][T2_]]:=\[ScriptCapitalK][T1\[Diamond]T2];
TensorType[\[ScriptCapitalB][T1_],\[ScriptCapitalB][T2_]]:=\[ScriptCapitalB][T1\[Diamond]T2];
TensorType[\[ScriptCapitalO][T1_,T2_],\[ScriptCapitalO][R1_,R2_]]:=\[ScriptCapitalO][T1\[Diamond]R1,T2\[Diamond]R2];
TensorType[\[ScriptCapitalO][T1_,T2_],\[ScriptCapitalK][R_]]:=\[ScriptCapitalO][T1\[Diamond]R,T2];
TensorType[\[ScriptCapitalK][R_],\[ScriptCapitalO][T1_,T2_]]:=\[ScriptCapitalO][R\[Diamond]T1,T2];
TensorType[\[ScriptCapitalO][T1_,T2_],\[ScriptCapitalB][R_]]:=\[ScriptCapitalO][T1,T2\[Diamond]R];
TensorType[\[ScriptCapitalB][R_],\[ScriptCapitalO][T1_,T2_]]:=\[ScriptCapitalO][T1,R\[Diamond]T2];

TensorTypeMatchQ[T1_,T2_]:=MatchQ[T1,DiracTypePatt]&&MatchQ[T2,DiracTypePatt];

TensorTypeMatchQ[T1_,T2_,Res_]:=TensorTypeMatchQ[T1,T2]&&Res===TensorType[T1,T2];


(* The type of tensor product that will produce a product type in bra *)
DoubleBraTensorType[\[ScriptCapitalB][T1_],\[ScriptCapitalB][T2_]]:=\[ScriptCapitalB][T1\[Diamond]T2];
DoubleBraTensorType[\[ScriptCapitalO][T1_,T2_],\[ScriptCapitalB][R_]]:=\[ScriptCapitalO][T1,T2\[Diamond]R];
DoubleBraTensorType[\[ScriptCapitalB][R_],\[ScriptCapitalO][T1_,T2_]]:=\[ScriptCapitalO][T1,R\[Diamond]T2];
DoubleBraTensorType[\[ScriptCapitalO][T1_,T2_],\[ScriptCapitalO][R1_,R2_]]:=\[ScriptCapitalO][T1\[Diamond]R1,T2\[Diamond]R2];

DoubleBraTensorTypeMatchQ[X_,Y_]:=
	MatchQ[{X,Y},{\[ScriptCapitalB][_],\[ScriptCapitalB][_]}]||
	MatchQ[{X,Y},{\[ScriptCapitalO][_,_],\[ScriptCapitalB][_]}]||
	MatchQ[{X,Y},{\[ScriptCapitalB][_],\[ScriptCapitalO][_,_]}]||
	MatchQ[{X,Y},{\[ScriptCapitalO][_,_],\[ScriptCapitalO][_,_]}];
	
DoubleBraTensorTypeMatchQ[T1_,T2_,Res_]:=DoubleBraTensorTypeMatchQ[T1,T2]&&Res===DoubleBraTensorType[T1,T2];


(* The type of tensor product that will produce a product type in ket *)
DoubleKetTensorType[\[ScriptCapitalK][T1_],\[ScriptCapitalK][T2_]]:=\[ScriptCapitalK][T1\[Diamond]T2];
DoubleKetTensorType[\[ScriptCapitalO][T1_,T2_],\[ScriptCapitalK][R_]]:=\[ScriptCapitalO][T1\[Diamond]R,T2];
DoubleKetTensorType[\[ScriptCapitalK][R_],\[ScriptCapitalO][T1_,T2_]]:=\[ScriptCapitalO][R\[Diamond]T1,T2];
DoubleKetTensorType[\[ScriptCapitalO][T1_,T2_],\[ScriptCapitalO][R1_,R2_]]:=\[ScriptCapitalO][T1\[Diamond]R1,T2\[Diamond]R2];

DoubleKetTensorTypeMatchQ[X_,Y_]:=
	MatchQ[{X,Y},{\[ScriptCapitalK][_],\[ScriptCapitalK][_]}]||
	MatchQ[{X,Y},{\[ScriptCapitalO][_,_],\[ScriptCapitalK][_]}]||
	MatchQ[{X,Y},{\[ScriptCapitalK][_],\[ScriptCapitalO][_,_]}]||
	MatchQ[{X,Y},{\[ScriptCapitalO][_,_],\[ScriptCapitalO][_,_]}];
	
DoubleKetTensorTypeMatchQ[T1_,T2_,Res_]:=DoubleKetTensorTypeMatchQ[T1,T2]&&Res===DoubleKetTensorType[T1,T2];


(* a context is a List of typings *)

TypingAssigns = {};

TypingPair = Pair[(t1_\[LeftTriangle]T1_),(t2_\[LeftTriangle]T2_)] -> T1\[Diamond]T2;
AppendTo[TypingAssigns, Hold[TypingPair]];

TypingFst = Fst[t_\[LeftTriangle](T1_\[Diamond]T2_)] -> T1;
AppendTo[TypingAssigns, Hold[TypingFst]];

TypingSnd = Snd[t_\[LeftTriangle](T1_\[Diamond]T2_)] -> T2;
AppendTo[TypingAssigns, Hold[TypingSnd]];

TypingC = C[t_] -> \[ScriptCapitalS];
AppendTo[TypingAssigns, Hold[TypingC]];

TypingDelta = Delta[t1_\[LeftTriangle]T_, t2_\[LeftTriangle]T_] -> \[ScriptCapitalS];
AppendTo[TypingAssigns, Hold[TypingDelta]];

TypingZero = Zero[T:DiracTypePatt] -> T;
AppendTo[TypingAssigns, Hold[TypingZero]];

TypingOneO = OneO[T_] -> \[ScriptCapitalO][T,T];
AppendTo[TypingAssigns, Hold[TypingOneO]];

TypingKet = Ket[{t_\[LeftTriangle]T_}] -> \[ScriptCapitalK][T];
AppendTo[TypingAssigns, Hold[TypingKet]];

TypingBra = Bra[{t_\[LeftTriangle]T_}] -> \[ScriptCapitalB][T];
AppendTo[TypingAssigns, Hold[TypingBra]];

TypingAdj = ((t_)\[LeftTriangle]T:DiracTypePatt)\[ConjugateTranspose] -> DualType[T];
AppendTo[TypingAssigns, Hold[TypingAdj]];

(* This rule makes use of the Flat attribute of Dot symbol *)
TypingDOT = Verbatim[Dot][args:(_\[LeftTriangle]DiracKBOTypePatt)..]/;
	MatchQ[Fold[DotType,#[[2]]&/@{args}],DiracTypePatt]:>Fold[DotType,#[[2]]&/@{args}];
AppendTo[TypingAssigns, Hold[TypingDOT]];

TypingTSR = (a_\[LeftTriangle]T1_)\[CircleTimes](b_\[LeftTriangle]T2_)/;TensorTypeMatchQ[T1,T2] -> TensorType[T1,T2];
AppendTo[TypingAssigns, Hold[TypingTSR]];

TypingMLT = (argsl:((_\[LeftTriangle]\[ScriptCapitalS])|(s_?NumericQ))...)(arg:(_\[LeftTriangle]T:DiracTypePatt)..)(argsr:((_\[LeftTriangle]\[ScriptCapitalS])|(s_/;NumericQ[s]))...) -> T;
AppendTo[TypingAssigns, Hold[TypingMLT]];

TypingADD = (argsl:(_\[LeftTriangle]T:DiracTypePatt)..)+(argsr:(_\[LeftTriangle]T_)) -> T;
AppendTo[TypingAssigns, Hold[TypingADD]];

TypingADDPatt = (argsl:(_\[LeftTriangle]T_)..)+(argsr:(_\[LeftTriangle]T_))+Verbatim[Pattern][name_,patt_] -> T;
AppendTo[TypingAssigns, Hold[TypingADDPatt]];

(* we need this rule because we have a a -> a^2 *)
TypingPow = (_\[LeftTriangle]T:\[ScriptCapitalS]|\[ScriptCapitalO][R_,R_])^(n_) -> T;
AppendTo[TypingAssigns, Hold[TypingPow]];



(* Speical Flattening Rules for AC symbols *)
Typing[(l:(_\[LeftTriangle]T_)...)+Typing[t:Verbatim[Plus][___],T_]+(r:(_\[LeftTriangle]T_)...),T_]:=Typing[l+t+r,T];
Typing[(l:(_\[LeftTriangle]\[ScriptCapitalS])...)Typing[t:Verbatim[Times][___],T_](r:(_\[LeftTriangle]\[ScriptCapitalS])...),T_]:=Typing[l t r,T];
Typing[(l:(_\[LeftTriangle]DiracTypePatt)...) . Typing[t:Verbatim[Dot][___],T_] . (r:(_\[LeftTriangle]DiracTypePatt)...),R_]:=Typing[l . t . r,R]/;
	Fold[DotType,Join[#[[2]]&/@{l},{T},#[[2]]&/@{r}]]===R;


(*
(* Special rules to deal with patterns when constructing types in meta-language. *)
TypingADDPatt = Add[args:(_\[LeftTriangle]T_)...,Verbatim[___]] :> Add[args, ___]\[LeftTriangle]T;
AppendTo[TypingAssigns, Hold[TypingADDPatt]];*)

(* This method will transform unterminating typing rules into terminating ones. 
The result rule will only rewrite the term when there is a parent symbol other than Typing. *)


DiracTypingCompiled = TypingRuleCompile[ReleaseHold[TypingAssigns]];

(* remove Typing in C symbols *)
RemoveCTyping[term_]:=term//.{C[t_]:>C[RemoveType[t]]};

DiracTypeCheck[t_,assign_List:{}]:=TypeCheck[t,assign,Compiled->DiracTypingCompiled]//RemoveCTyping;


End[];


(* ::Section:: *)
(*Rewriting Rules*)


Begin["Rewriting`"];


SetAttributes[Delta, Orderless];


RewritingRules = {};

(* compile the rewriting rule to add typing decorations *)	
CompiledRewritingRule[rule_,LHSassign_List,RHSassign_List]:=
	DiracTypeCheck[rule[[1]],LHSassign]->DiracTypeCheck[rule[[2]],RHSassign];


(* ::Subsection:: *)
(*Dealing With Plus/Times/Pow*)


(* POWTYPE *)
AppendTo[
	RewritingRules,
	Lookup[TypingRuleCompile[{Typings`TypingPow}],Private`SubtermTyping][[1]]
];

(* MLTTYPE *)
AppendTo[
	RewritingRules,
	Lookup[TypingRuleCompile[{Typings`TypingMLT}],Private`SubtermTyping][[1]]
];

(* POW-REDUCE *)
AppendTo[
	RewritingRules,
	((C[a_]\[LeftTriangle]\[ScriptCapitalS])^(n_))\[LeftTriangle]\[ScriptCapitalS] -> C[a^n]\[LeftTriangle]\[ScriptCapitalS]
];


(* ::Subsection:: *)
(*BASIS*)


(* BASIS1 *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		Fst[Pair[e1_,e2_]]->e1,
		{Verbatim[e1_]->T1_,Verbatim[e2_]->T2_},
		{e1->T1}
	]
];


(* BASIS2 *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		Snd[Pair[e1_,e2_]]->e2,
		{Verbatim[e1_]->T1_,Verbatim[e2_]->T2_},
		{e2->T2}
	]
];


(* BASIS3 *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		Pair[Fst[e_], Snd[e_]]->e,
		{Verbatim[e_]->(T1_\[Diamond]T2_)},
		{e->T1\[Diamond]T2}
	]
];


(* ::Subsection:: *)
(*DELTA*)


(* DELTA1 *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		Delta[u_,Pair[s_,t_]]->Delta[Fst[u],s]Delta[Snd[u],t],
		{Verbatim[u_]->(P_\[Diamond]Q_),Verbatim[s_]->P_,Verbatim[t_]->Q_},
		{u->P\[Diamond]Q,s->P,t->Q}
	]
];


(* DELTA2 *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		Delta[Fst[u_],Fst[v_]]Delta[Snd[u_],Snd[v_]]->Delta[u,v],
		{Verbatim[u_]->(P_\[Diamond]Q_),Verbatim[v_]->(P_\[Diamond]Q_)},
		{u->P\[Diamond]Q,v->P\[Diamond]Q}
	]
];


(* ::Subsection:: *)
(*ADD*)


(* ADD0 *)
AppendTo[
	RewritingRules,
	((Zero[T:Typings`DiracTypePatt]\[LeftTriangle]T_)+x_+(arg:(_\[LeftTriangle]T_)...))\[LeftTriangle]T_->(x+arg)\[LeftTriangle]T
];


(* ADDCADD *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		C[a_]+C[b_]->C[a+b],
		{},
		{}
	]
];


(* ADDFAC0 *)
(* This rule connects the mathematica rule a + a -> 2 a *)
AppendTo[
	RewritingRules,
	((c_?NumericQ)(x_\[LeftTriangle]T_))\[LeftTriangle]T_->((C[c]\[LeftTriangle]\[ScriptCapitalS])(x\[LeftTriangle]T))\[LeftTriangle]T
];


(* ADDFAC1S *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		C[a_](x_)+(x_)+(arg:(_\[LeftTriangle]\[ScriptCapitalS])...)->(C[a+1]x + arg)\[LeftTriangle]\[ScriptCapitalS],
		{Verbatim[x_]->\[ScriptCapitalS]},
		{x->\[ScriptCapitalS]}
	]
];


(* ADDFAC1K *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		(c_)(x_)+(x_)+(arg:(_\[LeftTriangle]\[ScriptCapitalK][T_])...)->((c+C[1])x + arg)\[LeftTriangle]\[ScriptCapitalK][T],
		{Verbatim[c_]->\[ScriptCapitalS],Verbatim[x_]->\[ScriptCapitalK][T_]},
		{c->\[ScriptCapitalS],x->\[ScriptCapitalK][T]}
	]
];


(* ADDFAC1B *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		(c_)(x_)+(x_)+(arg:(_\[LeftTriangle]\[ScriptCapitalB][T_])...)->((c+C[1])x + arg)\[LeftTriangle]\[ScriptCapitalB][T],
		{Verbatim[c_]->\[ScriptCapitalS],Verbatim[x_]->\[ScriptCapitalB][T_]},
		{c->\[ScriptCapitalS],x->\[ScriptCapitalB][T]}
	]
];


(* ADDFAC1O *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		(c_)(x_)+(x_)+(arg:(_\[LeftTriangle]\[ScriptCapitalO][T1_,T2_])...)->((c+C[1])x + arg)\[LeftTriangle]\[ScriptCapitalO][T1,T2],
		{Verbatim[c_]->\[ScriptCapitalS],Verbatim[x_]->\[ScriptCapitalO][T1_,T2_]},
		{c->\[ScriptCapitalS],x->\[ScriptCapitalO][T1,T2]}
	]
];


(* ADDFAC2S *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		C[a_](x_)+C[b_](x_)+(arg:(_\[LeftTriangle]\[ScriptCapitalS])...)->(C[a+b]x + arg)\[LeftTriangle]\[ScriptCapitalS],
		{Verbatim[x_]->\[ScriptCapitalS]},
		{x->\[ScriptCapitalS]}
	]
];


(* ADDFAC2K *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		(c1_)(x_)+(c2_)(x_)+(arg:(_\[LeftTriangle]\[ScriptCapitalK][T_])...)->((c1+c2)x + arg)\[LeftTriangle]\[ScriptCapitalK][T],
		{Verbatim[c1_]->\[ScriptCapitalS],Verbatim[c2_]->\[ScriptCapitalS],Verbatim[x_]->\[ScriptCapitalK][T_]},
		{c1->\[ScriptCapitalS],c2->\[ScriptCapitalS],x->\[ScriptCapitalK][T]}
	]
];


(* ADDFAC2B *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		(c1_)(x_)+(c2_)(x_)+(arg:(_\[LeftTriangle]\[ScriptCapitalB][T_])...)->((c1+c2)x + arg)\[LeftTriangle]\[ScriptCapitalB][T],
		{Verbatim[c1_]->\[ScriptCapitalS],Verbatim[c2_]->\[ScriptCapitalS],Verbatim[x_]->\[ScriptCapitalB][T_]},
		{c1->\[ScriptCapitalS],c2->\[ScriptCapitalS],x->\[ScriptCapitalB][T]}
	]
];


(* ADDFAC2O *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		(c1_)(x_)+(c2_)(x_)+(arg:(_\[LeftTriangle]\[ScriptCapitalO][T1_,T2_])...)->((c1+c2)x + arg)\[LeftTriangle]\[ScriptCapitalO][T1,T2],
		{Verbatim[c1_]->\[ScriptCapitalS],Verbatim[c2_]->\[ScriptCapitalS],Verbatim[x_]->\[ScriptCapitalO][T1_,T2_]},
		{c1->\[ScriptCapitalS],c2->\[ScriptCapitalS],x->\[ScriptCapitalO][T1,T2]}
	]
];


(* ::Subsection:: *)
(*SCL*)


(* SCL0 *)
AppendTo[
	RewritingRules,
	C[0]\[LeftTriangle]\[ScriptCapitalS]->Zero[\[ScriptCapitalS]]\[LeftTriangle]\[ScriptCapitalS]
];


(* ::Subsection:: *)
(*MLT*)


(* MLT0 *)
AppendTo[
	RewritingRules,
	(Zero[T:Typings`DiracTypePatt]\[LeftTriangle]T_)((_\[LeftTriangle]Typings`DiracTypePatt)...)\[LeftTriangle]R_->Zero[R]\[LeftTriangle]R
];


(* MLT1 *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		(C[1](x_\[LeftTriangle](T:Typings`DiracTypePatt))(arg:(_\[LeftTriangle]\[ScriptCapitalS])...))\[LeftTriangle]T_->((x\[LeftTriangle]T) arg)\[LeftTriangle]T,
		{},
		{}
	]
];


(* MLTAB *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		(C[a_]\[LeftTriangle]\[ScriptCapitalS])(C[b_]\[LeftTriangle]\[ScriptCapitalS])(arg:(_\[LeftTriangle]Typings`DiracTypePatt)...)\[LeftTriangle]T_->Times[C[a b]\[LeftTriangle]\[ScriptCapitalS],arg]\[LeftTriangle]T,
		{},
		{}
	]
];


(* MLTDIST *)
AppendTo[
	RewritingRules,
	((a_\[LeftTriangle]\[ScriptCapitalS])(Verbatim[Plus][args:(_\[LeftTriangle](T:Typings`DiracTypePatt))..]\[LeftTriangle]T_))\[LeftTriangle]T_:>
	Plus@@((((a\[LeftTriangle]\[ScriptCapitalS])#)\[LeftTriangle]T)&/@{args})\[LeftTriangle]T
];


(* ::Subsection:: *)
(*ADJ*)


(* ADJC *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		(C[x_])\[ConjugateTranspose]->C[Conjugate[x]],
		{},
		{}
	]
];


(* ADJZERO *)
AppendTo[
	RewritingRules,
	(Zero[T_:Typings`DiracTypePatt]\[LeftTriangle]T_)\[ConjugateTranspose]\[LeftTriangle]R_:>Zero[R]\[LeftTriangle]R/;Typings`TypeDualQ[T,R]
];


(* ADJONEO *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		(OneO[T_])\[ConjugateTranspose]->OneO[T],
		{},
		{}
	]
];


(* ADJDELTA *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		(Delta[a_,b_])\[ConjugateTranspose]->Delta[a,b],
		{Verbatim[a_]->T_,Verbatim[b_]->T_},
		{a->T,b->T}
	]
];


(* ADJKET *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		Ket[{a_}]\[ConjugateTranspose] -> Bra[{a}],
		{Verbatim[a_]->T_},
		{a->T}
	]
];


(* ADJBRA *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		Bra[{a_}]\[ConjugateTranspose] -> Ket[{a}],
		{Verbatim[a_]->T_},
		{a->T}
	]
];


(* ADJADD *)
AppendTo[
	RewritingRules,
	(Verbatim[Plus][args:(_\[LeftTriangle]T_:DiracTypePatt)..]\[LeftTriangle]T_)\[ConjugateTranspose]\[LeftTriangle]R_:>
		Plus@@(((#)\[ConjugateTranspose]\[LeftTriangle]R)&/@{args})\[LeftTriangle]R/;Typings`TypeDualQ[T,R]
];


(* ADJMLT *)
AppendTo[
	RewritingRules,
	(((x:(_\[LeftTriangle]T_:DiracTypePatt))(args:(_\[LeftTriangle]\[ScriptCapitalS])..))\[LeftTriangle]T_)\[ConjugateTranspose]\[LeftTriangle]R_/;Typings`TypeDualQ[T,R]:>
		Times@@(Join[((#)\[ConjugateTranspose]\[LeftTriangle]\[ScriptCapitalS])&/@{args},{(x\[LeftTriangle]T)\[ConjugateTranspose]\[LeftTriangle]R}])\[LeftTriangle]R
];


(* ADJADJ *)
AppendTo[
	RewritingRules,
	((x_\[LeftTriangle]T:Typings`DiracTypePatt)\[ConjugateTranspose]\[LeftTriangle]R_)\[ConjugateTranspose]\[LeftTriangle]T_/;Typings`TypeDualQ[T,R]->x\[LeftTriangle]T
];


(* ADJDOT *)
AppendTo[
	RewritingRules,
	
	((x_\[LeftTriangle]T1_) . (y_\[LeftTriangle]T2_)\[LeftTriangle]R_)\[ConjugateTranspose]\[LeftTriangle]L_
	/;Typings`DotTypeMatchQ[T1,T2,R]&&Typings`TypeDualQ[R,L]
	->
	((y\[LeftTriangle]T2)\[ConjugateTranspose]\[LeftTriangle]Typings`DualType[T2]) . ((x\[LeftTriangle]T1)\[ConjugateTranspose]\[LeftTriangle]Typings`DualType[T1])\[LeftTriangle]L

];


(* ADJTSR *)
AppendTo[
	RewritingRules,
	((x_\[LeftTriangle]T1_)\[CircleTimes](y_\[LeftTriangle]T2_)\[LeftTriangle]R_)\[ConjugateTranspose]\[LeftTriangle]L_/;Typings`TensorTypeMatchQ[T1,T2,R]&&Typings`TypeDualQ[R,L]->
		((x\[LeftTriangle]T1)\[ConjugateTranspose]\[LeftTriangle]Typings`DualType[T1])\[CircleTimes]((y\[LeftTriangle]T2)\[ConjugateTranspose]\[LeftTriangle]Typings`DualType[T2])\[LeftTriangle]L
];


(* ::Subsection:: *)
(*DOT*)


(* ::Text:: *)
(*Dot rewriting rules are not compiled to have the Typing symbol at the root, because the typing of Dot is flattened and we want to match subsequences during rewriting.*)


(* ::Subsubsection:: *)
(*DOTZERO*)


(* DOTZERO1 *)
AppendTo[
	RewritingRules,
	(Zero[T1_]\[LeftTriangle]T1_) . (y_\[LeftTriangle]T2_)/;Typings`DotTypeMatchQ[T1,T2] -> With[{resT=Typings`DotType[T1,T2]},Zero[resT]\[LeftTriangle]resT]
];

(* DOTZERO2 *)
AppendTo[
	RewritingRules,
	(x_\[LeftTriangle]T1_) . (Zero[T2_]\[LeftTriangle]T2_)/;Typings`DotTypeMatchQ[T1,T2] -> With[{resT=Typings`DotType[T1,T2]},Zero[resT]\[LeftTriangle]resT]
];


(* ::Subsubsection:: *)
(*DOTONEO*)


(* DOTONEO1 *)
AppendTo[
	RewritingRules,
	(OneO[T1_]\[LeftTriangle]\[ScriptCapitalO][T1_,T1_]) . (y_\[LeftTriangle]T2_)/;Typings`DotTypeMatchQ[\[ScriptCapitalO][T1,T1],T2] -> y\[LeftTriangle]T2
];

(* DOTONEO2 *)
AppendTo[
	RewritingRules,
	(x_\[LeftTriangle]T1_) . (OneO[T2_]\[LeftTriangle]\[ScriptCapitalO][T2_,T2_])/;Typings`DotTypeMatchQ[T1,\[ScriptCapitalO][T2,T2]] -> x\[LeftTriangle]T1
];


(* ::Subsubsection:: *)
(*DOTSCL*)


(* DOTSCL1 *)
AppendTo[
	RewritingRules,
	((args:(_\[LeftTriangle]\[ScriptCapitalS])..)(x:(_\[LeftTriangle]T1_))\[LeftTriangle]T1_) . (y:(_\[LeftTriangle]T2_))/;Typings`DotTypeMatchQ[T1,T2] :>
		With[{resT=Typings`DotType[T1,T2]},Times[args]((x\[LeftTriangle]T1) . (y\[LeftTriangle]T2)\[LeftTriangle]resT)\[LeftTriangle]resT]
];

(* DOTSCL2 *)
AppendTo[
	RewritingRules,
	(x:(_\[LeftTriangle]T1_)) . ((args:(_\[LeftTriangle]\[ScriptCapitalS])..)(y:(_\[LeftTriangle]T2_))\[LeftTriangle]T2_)/;Typings`DotTypeMatchQ[T1,T2] :>
		With[{resT=Typings`DotType[T1,T2]},Times[args]((x\[LeftTriangle]T1) . (y\[LeftTriangle]T2)\[LeftTriangle]resT)\[LeftTriangle]resT]
];


(* ::Subsubsection:: *)
(*DOTDIST*)


(* DOTDIST1 *)
AppendTo[
	RewritingRules,
	(Verbatim[Plus][args:(_\[LeftTriangle]T1_)..]\[LeftTriangle]T1_) . (y:(_\[LeftTriangle]T2_))/;Typings`DotTypeMatchQ[T1,T2] :>
		With[{resT=Typings`DotType[T1,T2]},Plus@@(((# . (y\[LeftTriangle]T2))\[LeftTriangle]resT)&/@{args})\[LeftTriangle]resT]
];

(* DOTDIST2 *)
AppendTo[
	RewritingRules,
	(x:(_\[LeftTriangle]T1_)) . (Verbatim[Plus][args:(_\[LeftTriangle]T2_)..]\[LeftTriangle]T2_)/;Typings`DotTypeMatchQ[T1,T2] :>
		With[{resT=Typings`DotType[T1,T2]},Plus@@((((x\[LeftTriangle]T1) . #)\[LeftTriangle]resT)&/@{args})\[LeftTriangle]resT]
];


(* ::Subsubsection:: *)
(*DOTBRAKET*)


(* DOTBRAKET *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		Bra[{s_}] . Ket[{t_}] -> Delta[s,t],
		{Verbatim[s_]->T_,Verbatim[t_]->T_},
		{s->T,t->T}
	]
];


(* ::Subsubsection:: *)
(*DOTRECOMB*)


(* DOTRECOMBKET *)
DOTRECOMBKET=
		((X1_\[LeftTriangle]T1_)\[CircleTimes](X2_\[LeftTriangle]T2_)\[LeftTriangle]T12_) . (Ket[{s_\[LeftTriangle]((R1_)\[Diamond](R2_))}]\[LeftTriangle]\[ScriptCapitalK][(R1_)\[Diamond](R2_)])/;
		Typings`DoubleBraTensorTypeMatchQ[T1,T2,T12]&&Typings`DotTypeMatchQ[T12,\[ScriptCapitalK][R1\[Diamond]R2]]->
		With[
			{resT1=Typings`DotType[T1,\[ScriptCapitalK][R1]],resT2=Typings`DotType[T2,\[ScriptCapitalK][R2]]},
			((X1\[LeftTriangle]T1) . (Ket[{Fst[s\[LeftTriangle](R1\[Diamond]R2)]\[LeftTriangle]R1}]\[LeftTriangle]\[ScriptCapitalK][R1])\[LeftTriangle]resT1)\[CircleTimes]((X2\[LeftTriangle]T2) . (Ket[{Snd[s\[LeftTriangle](R1\[Diamond]R2)]\[LeftTriangle]R2}]\[LeftTriangle]\[ScriptCapitalK][R2])\[LeftTriangle]resT2)\[LeftTriangle]Typings`TensorType[resT1,resT2]
			];
AppendTo[
	RewritingRules,
	DOTRECOMBKET
];


(* DOTRECOMBBRA *)
DOTRECOMBBRA=
		(Bra[{s_\[LeftTriangle]((R1_)\[Diamond](R2_))}]\[LeftTriangle]\[ScriptCapitalB][(R1_)\[Diamond](R2_)]) . ((X1_\[LeftTriangle]T1_)\[CircleTimes](X2_\[LeftTriangle]T2_)\[LeftTriangle]T12_)/;
		Typings`DoubleKetTensorTypeMatchQ[T1,T2,T12]&&Typings`DotTypeMatchQ[\[ScriptCapitalB][R1\[Diamond]R2],T12]->
		With[
			{resT1=Typings`DotType[\[ScriptCapitalB][R1],T1],resT2=Typings`DotType[\[ScriptCapitalB][R2],T2]},
			((Bra[{Fst[s\[LeftTriangle](R1\[Diamond]R2)]\[LeftTriangle]R1}]\[LeftTriangle]\[ScriptCapitalB][R1]) . (X1\[LeftTriangle]T1)\[LeftTriangle]resT1)\[CircleTimes]((Bra[{Snd[s\[LeftTriangle](R1\[Diamond]R2)]\[LeftTriangle]R2}]\[LeftTriangle]\[ScriptCapitalB][R2]) . (X2\[LeftTriangle]T2)\[LeftTriangle]resT2)\[LeftTriangle]Typings`TensorType[resT1,resT2]
			];		
AppendTo[
	RewritingRules,
	DOTRECOMBBRA
];


(* DOTRECOMBBK*)
DOTRECOMBBK=
		((X1_\[LeftTriangle]T1_)\[CircleTimes](X2_\[LeftTriangle]T2_)\[LeftTriangle]T12_) . ((Y1_\[LeftTriangle]R1_)\[CircleTimes](Y2_\[LeftTriangle]R2_)\[LeftTriangle]R12_)/;
		Typings`DoubleBraTensorTypeMatchQ[T1,T2,T12]&&
		Typings`DoubleKetTensorTypeMatchQ[R1,R2,R12]&&
		Typings`DotTypeMatchQ[T12,R12]->
		With[
			{resT1=Typings`DotType[T1,R1],resT2=Typings`DotType[T2,R2]},
			((X1\[LeftTriangle]T1) . (Y1\[LeftTriangle]R1)\[LeftTriangle]resT1)\[CircleTimes]((X2\[LeftTriangle]T2) . (Y2\[LeftTriangle]R2)\[LeftTriangle]resT2)\[LeftTriangle]Typings`TensorType[resT1,resT2]
			];

AppendTo[
	RewritingRules,
	DOTRECOMBBK
];


(* DOTRECOMBSINGLEK1 *)
DOTRECOMBSINGLEK1=
		(B_\[LeftTriangle]TB:(\[ScriptCapitalB][R_]|\[ScriptCapitalO][_,R_])) . ((X1_\[LeftTriangle]T1:(\[ScriptCapitalK][R_]|\[ScriptCapitalO][R_,_]))\[CircleTimes](X2_\[LeftTriangle]T2:\[ScriptCapitalB][_])\[LeftTriangle]T12_)/;
		Typings`TensorTypeMatchQ[T1,T2,T12]->
		With[
			{resT1=Typings`DotType[TB,T1]},
			((B\[LeftTriangle]TB) . (X1\[LeftTriangle]T1)\[LeftTriangle]resT1)\[CircleTimes](X2\[LeftTriangle]T2)\[LeftTriangle]Typings`TensorType[resT1,T2]
			];		
AppendTo[
	RewritingRules,
	DOTRECOMBSINGLEK1
];


(* DOTRECOMBSINGLEK2 *)
DOTRECOMBSINGLEK2=
		(B_\[LeftTriangle]TB:(\[ScriptCapitalB][R_]|\[ScriptCapitalO][_,R_])) . ((X1_\[LeftTriangle]T1:\[ScriptCapitalB][_])\[CircleTimes](X2_\[LeftTriangle]T2:(\[ScriptCapitalK][R_]|\[ScriptCapitalO][R_,_]))\[LeftTriangle]T12_)/;
		Typings`TensorTypeMatchQ[T1,T2,T12]->
		With[
			{resT2=Typings`DotType[TB,T2]},
			(X1\[LeftTriangle]T1)\[CircleTimes]((B\[LeftTriangle]TB) . (X2\[LeftTriangle]T2)\[LeftTriangle]resT2)\[LeftTriangle]Typings`TensorType[T1,resT2]
			];		
AppendTo[
	RewritingRules,
	DOTRECOMBSINGLEK2
];


(* DOTRECOMBSINGLEB1 *)
DOTRECOMBSINGLEB1=
		((X1_\[LeftTriangle]T1:(\[ScriptCapitalB][R_]|\[ScriptCapitalO][_,R_]))\[CircleTimes](X2_\[LeftTriangle]T2:\[ScriptCapitalK][_])\[LeftTriangle]T12_) . (K_\[LeftTriangle]TK:(\[ScriptCapitalK][R_]|\[ScriptCapitalO][R_,_]))/;
		Typings`TensorTypeMatchQ[T1,T2,T12]->
		With[
			{resT1=Typings`DotType[T1,TK]},
			((X1\[LeftTriangle]T1) . (K\[LeftTriangle]TK)\[LeftTriangle]resT1)\[CircleTimes](X2\[LeftTriangle]T2)\[LeftTriangle]Typings`TensorType[resT1,T2]
			];		
AppendTo[
	RewritingRules,
	DOTRECOMBSINGLEB1
];


(* DOTRECOMBSINGLEB2 *)
DOTRECOMBSINGLEB2=
		((X1_\[LeftTriangle]T1:\[ScriptCapitalK][_])\[CircleTimes](X2_\[LeftTriangle]T2:(\[ScriptCapitalB][R_]|\[ScriptCapitalO][_,R_]))\[LeftTriangle]T12_) . (K_\[LeftTriangle]TK:(\[ScriptCapitalK][R_]|\[ScriptCapitalO][R_,_]))/;
		Typings`TensorTypeMatchQ[T1,T2,T12]->
		With[
			{resT2=Typings`DotType[T2,TK]},
			(X1\[LeftTriangle]T1)\[CircleTimes]((X2\[LeftTriangle]T2) . (K\[LeftTriangle]TK)\[LeftTriangle]resT2)\[LeftTriangle]Typings`TensorType[T1,resT2]
			];		
AppendTo[
	RewritingRules,
	DOTRECOMBSINGLEB2
];


(* ::Subsubsection:: *)
(*DOTSORT*)


(* DOTSORT rules are already incorporated in Dot symbol. *)


(* ::Subsection:: *)
(*TSR*)


(* ::Text:: *)
(*I found it's very hard to simplify the expressions containing special tensor products like O\[CircleTimes]K. A sophisticated sorting algorithm is necessary.*)


(* ::Subsubsection:: *)
(*TSRZERO*)


(* TSRZERO1 *)
AppendTo[
	RewritingRules,
	(Zero[T1_]\[LeftTriangle]T1_)\[CircleTimes](y_\[LeftTriangle]T2_)\[LeftTriangle]R_/;Typings`TensorTypeMatchQ[T1,T2,R] -> Zero[R]\[LeftTriangle]R
];

(* TSRZERO2 *)
AppendTo[
	RewritingRules,
	(x_\[LeftTriangle]T1_)\[CircleTimes](Zero[T2_]\[LeftTriangle]T2_)\[LeftTriangle]R_/;Typings`TensorTypeMatchQ[T1,T2,R] -> Zero[R]\[LeftTriangle]R
];


(* ::Subsubsection:: *)
(*TSRKET/TSRBRA*)


(* TSRKET *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		Ket[{s_}]\[CircleTimes]Ket[{t_}] -> Ket[{Pair[s,t]}],
		{Verbatim[s_]->T1_,Verbatim[t_]->T2_},
		{s->T1,t->T2}
	]
];


(* TSRBRA *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		Bra[{s_}]\[CircleTimes]Bra[{t_}] -> Bra[{Pair[s,t]}],
		{Verbatim[s_]->T1_,Verbatim[t_]->T2_},
		{s->T1,t->T2}
	]
];


(* TSRSCL1 *)
AppendTo[
	RewritingRules,
	(s:(_\[LeftTriangle]\[ScriptCapitalS]))\[CircleTimes](x:(_\[LeftTriangle]T:Typings`DiracTypePatt))\[LeftTriangle]T_-> (s x)\[LeftTriangle]T
];

(* TSRSCL2 *)
AppendTo[
	RewritingRules,
	(x:(_\[LeftTriangle]T:Typings`DiracTypePatt))\[CircleTimes](s:(_\[LeftTriangle]\[ScriptCapitalS]))\[LeftTriangle]T_-> (s x)\[LeftTriangle]T
];


(* TSRSWAP *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		b_\[CircleTimes]k_->k\[CircleTimes]b,
		{Verbatim[k_]->\[ScriptCapitalK][T1_],Verbatim[b_]->\[ScriptCapitalB][T2_]},
		{k->\[ScriptCapitalK][T1],b->\[ScriptCapitalB][T2]}
	]
];


(* TSRRECOMB *)
AppendTo[
	RewritingRules,
	CompiledRewritingRule[
		(k1_\[CircleTimes]b1_)\[CircleTimes](k2_\[CircleTimes]b2_)->(k1\[CircleTimes]k2)\[CircleTimes](b1\[CircleTimes]b2),
		{Verbatim[k1_]->\[ScriptCapitalK][T1_],Verbatim[k2_]->\[ScriptCapitalK][T2_],Verbatim[b1_]->\[ScriptCapitalB][R1_],Verbatim[b2_]->\[ScriptCapitalB][R2_]},
		{k1->\[ScriptCapitalK][T1],k2->\[ScriptCapitalK][T2],b1->\[ScriptCapitalB][R1],b2->\[ScriptCapitalB][R2]}
	]
];


(* TSRMLT1 *)
AppendTo[
	RewritingRules,
	((args:(_\[LeftTriangle]\[ScriptCapitalS])..)(x:(_\[LeftTriangle]T1_))\[LeftTriangle]T1_)\[CircleTimes](y:(_\[LeftTriangle]T2_))\[LeftTriangle]R_/;Typings`TensorTypeMatchQ[T1,T2,R] :>
		Times[args]((x\[LeftTriangle]T1)\[CircleTimes](y\[LeftTriangle]T2)\[LeftTriangle]R)\[LeftTriangle]R
];



(* TSRMLT2 *)
AppendTo[
	RewritingRules,
	(x:(_\[LeftTriangle]T1_))\[CircleTimes]((args:(_\[LeftTriangle]\[ScriptCapitalS])..)(y:(_\[LeftTriangle]T2_))\[LeftTriangle]T2_)\[LeftTriangle]R_/;Typings`TensorTypeMatchQ[T1,T2,R] :>
		Times[args]((x\[LeftTriangle]T1)\[CircleTimes](y\[LeftTriangle]T2)\[LeftTriangle]R)\[LeftTriangle]R
];



(* TSRDIST1 *)
AppendTo[
	RewritingRules,
	(Verbatim[Plus][args:(_\[LeftTriangle]T1_)..]\[LeftTriangle]T1_)\[CircleTimes](y:(_\[LeftTriangle]T2_))\[LeftTriangle]R_/;Typings`TensorTypeMatchQ[T1,T2,R] :>
		Plus@@(((# \[CircleTimes] (y\[LeftTriangle]T2))\[LeftTriangle]R)&/@{args})\[LeftTriangle]R
];

(* TSRDIST1 *)
AppendTo[
	RewritingRules,
	(x:(_\[LeftTriangle]T1_))\[CircleTimes](Verbatim[Plus][args:(_\[LeftTriangle]T2_)..]\[LeftTriangle]T2_)\[LeftTriangle]R_/;Typings`TensorTypeMatchQ[T1,T2,R] :>
		Plus@@((((x\[LeftTriangle]T1) \[CircleTimes] #)\[LeftTriangle]R)&/@{args})\[LeftTriangle]R
];


(* ::Subsection:: *)
(*Rewriting Methods*)


(* the method to invoke rewriting *)
RewritingRulesWithTyping = RewritingRules;

DiracNorm[term_,assign_List:{}]:=
	With[{res=DiracTypeCheck[term,assign]//.RewritingRulesWithTyping}, 
		If[Head[res]=!=Typing,Throw["Not well typed term: ",res]];
		res];

End[];


End[];


(* ::Chapter:: *)
(*Dirac Notation: Extended Language*)


(* ::Section:: *)
(*Public Interface*)


(* Transpose: use the Transpose symbol provided by MMA. *)
Transpose;
(* Big Operator *)
DSum::usage = "The summation for Dirac notations.";


BindVars::usage:="Get all the bind variable names (in DSum) of the typed checked term.";
DSumRename::usage:="Rename the bind variabel with fresh ones.";

DiracExtTypeCheck::usage = "Type checking the Dirac notation (extended language).";

DiracExtNorm::usage = "Normalize the Dirac notation (in extended lanugage).";
DiracExtNormDebug::usage = "[DEBUG] Normalize the Dirac notation (in extended lanugage).";

DSumExpand::usage = "The function to expand the Dirac summation when index type is a list.";

DiracEqQ::usage = "Test whether two Dirac notations are equivalent";

EntryReduce::usage="Reduce the entry expansion expressions.";


Begin["Ext`"];


(* the special symbol for orderless bind variable list *)
BINDV;


(* ::Section:: *)
(*Notations*)


Notation[
	ParsedBoxWrapper[RowBox[{UnderscriptBox["\[Sum]", "i__"], "body_"}]] 
	\[DoubleLongLeftArrow] ParsedBoxWrapper[RowBox[{"DSum", "[", "Ext`BINDV", "[", "i__", "]", ",", "body_", "]"}]] 
];

Notation[
	ParsedBoxWrapper[RowBox[{"(","t_","\[LeftTriangle]","T_",")", "\[Transpose]"}]]
	\[DoubleLongLeftArrow] ParsedBoxWrapper[RowBox[{"Transpose", "[", "Typing", "[", "t_", ",", "T_", "]","]"}]] 
];


(* ::Section:: *)
(*Syntactic Operations*)


(* term should be checked already *)
BindVars[term_]:=Cases[term,DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)..],_\[LeftTriangle]T_]\[LeftTriangle]T_->bindvs,{0,Infinity}]//Union//Map[First]


DSumRename[term_]:=term/.(#->Unique[]&/@BindVars[term]);


(* ::Section:: *)
(*Typing of Dirac Notations*)


Begin["Typings`"];

ExtTypingAssigns = TypingAssigns;

TypingTrans = ((t_)\[LeftTriangle]T:DiracTypePatt)\[Transpose] -> DualType[T];
AppendTo[ExtTypingAssigns, Hold[TypingTrans]];

BindVWellTypedQ[bindv_,bindvT_,body_]:=AllTrue[Cases[body, bindv\[LeftTriangle]_,{0,Infinity}],MatchQ[#,bindv\[LeftTriangle]bindvT]&];
TypingDSum = 
	DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)..],body:(_\[LeftTriangle]T_)]/;
	AllTrue[{bindvs},BindVWellTypedQ[#[[1]],#[[2]],body]&]->T;
	
AppendTo[ExtTypingAssigns, Hold[TypingDSum]];


DiracExtTypingCompiled = TypingRuleCompile[ReleaseHold[ExtTypingAssigns]];
DiracExtTypeCheck[t_,assign_List:{}]:=TypeCheck[t,assign,Compiled->DiracExtTypingCompiled]//RemoveCTyping;
End[];


(* ::Section:: *)
(*Rewriting Rules*)


Begin["Rewriting`"];


ExtRewritingRules = RewritingRules;

(* compile the rewriting rule to add typing decorations *)	
CompiledRewritingRule[rule_,LHSassign_List,RHSassign_List]:=
	DiracExtTypeCheck[rule[[1]],LHSassign]->DiracExtTypeCheck[rule[[2]],RHSassign];


(* ::Subsection:: *)
(*Some Syntax Sugar*)


(* enable list of variables *)
DSum[bv:(_\[LeftTriangle]_),body_]:=DSum[Ext`BINDV[bv],body];
DSum[{bv:(_\[LeftTriangle]_)..},body_]:=DSum[Ext`BINDV[bv],body];
(* this is for equivalence of swaping of sum indices *)
DSum[Ext`BINDV[bindvsA:(_\[LeftTriangle]_)..],DSum[Ext`BINDV[bindvsB:(_\[LeftTriangle]_)..],body_]]:=DSum[Ext`BINDV[bindvsA,bindvsB],body];
DSum[Ext`BINDV[],body_]:=body;

SetAttributes[Ext`BINDV,Orderless];


(* ::Subsection:: *)
(*Delta Decision*)


(* DELTASAME *)
AppendTo[
	ExtRewritingRules,
	Delta[x_\[LeftTriangle]T_,y_\[LeftTriangle]T_]\[LeftTriangle]\[ScriptCapitalS]/;FullSimplify[RemoveType[x==y]]->C[1]\[LeftTriangle]\[ScriptCapitalS]
];


(* Check whether the equality is satisfiable. *)
EqUSatQ[a_,b_]:=Length[
	Quiet[
		Solve[RemoveType[a==b],Union[Cases[a==b,_Symbol,Infinity]]]
	]
]===0;

(* DELTAUSAT *)
AppendTo[
	ExtRewritingRules,
	Delta[a_\[LeftTriangle]T_,b_\[LeftTriangle]T_]\[LeftTriangle]\[ScriptCapitalS]/;EqUSatQ[a,b]->C[0]\[LeftTriangle]\[ScriptCapitalS]
];


(* ::Subsection:: *)
(*TRANS*)


(* TRANS0 *)
AppendTo[
	ExtRewritingRules,
	CompiledRewritingRule[
		(C[x_])\[Transpose]->C[x],
		{},
		{}
	]
];


(* TRANSZERO *)
AppendTo[
	ExtRewritingRules,
	(Zero[T_:Typings`DiracTypePatt]\[LeftTriangle]T_)\[Transpose]\[LeftTriangle]R_:>Zero[R]\[LeftTriangle]R/;Typings`TypeDualQ[T,R]
];


(* TRANSONEO *)
AppendTo[
	ExtRewritingRules,
	CompiledRewritingRule[
		(OneO[T_])\[Transpose]->OneO[T],
		{},
		{}
	]
];


(* TRANSDELTA *)
AppendTo[
	ExtRewritingRules,
	CompiledRewritingRule[
		(Delta[a_,b_])\[Transpose]->Delta[a,b],
		{Verbatim[a_]->T_,Verbatim[b_]->T_},
		{a->T,b->T}
	]
];


(* TRANSKET *)
AppendTo[
	ExtRewritingRules,
	CompiledRewritingRule[
		Ket[{a_}]\[Transpose] -> Bra[{a}],
		{Verbatim[a_]->T_},
		{a->T}
	]
];


(* TRANSBRA *)
AppendTo[
	ExtRewritingRules,
	CompiledRewritingRule[
		Bra[{a_}]\[Transpose] -> Ket[{a}],
		{Verbatim[a_]->T_},
		{a->T}
	]
];


(* TRANSADD *)
AppendTo[
	ExtRewritingRules,
	(Verbatim[Plus][args:(_\[LeftTriangle]T_:DiracTypePatt)..]\[LeftTriangle]T_)\[Transpose]\[LeftTriangle]R_:>
		Plus@@(((#)\[Transpose]\[LeftTriangle]R)&/@{args})\[LeftTriangle]R/;Typings`TypeDualQ[T,R]
];


(* TRANSMLT *)
AppendTo[
	ExtRewritingRules,
	(((x:(_\[LeftTriangle]T_:DiracTypePatt))(args:(_\[LeftTriangle]\[ScriptCapitalS])..))\[LeftTriangle]T_)\[Transpose]\[LeftTriangle]R_/;Typings`TypeDualQ[T,R]:>
		Times@@(Join[((#)\[Transpose]\[LeftTriangle]\[ScriptCapitalS])&/@{args},{(x\[LeftTriangle]T)\[ConjugateTranspose]\[LeftTriangle]R}])\[LeftTriangle]R
];


(* TRANSTRANS *)
AppendTo[
	ExtRewritingRules,
	((x_\[LeftTriangle]T:Typings`DiracTypePatt)\[Transpose]\[LeftTriangle]R_)\[Transpose]\[LeftTriangle]T_/;Typings`TypeDualQ[T,R]->x\[LeftTriangle]T
];


(* TRANSDOT *)
AppendTo[
	ExtRewritingRules,
	((x_\[LeftTriangle]T1_) . (y_\[LeftTriangle]T2_)\[LeftTriangle]R_)\[Transpose]\[LeftTriangle]L_/;Typings`DotTypeMatchQ[T1,T2,R]&&Typings`TypeDualQ[R,L]->
		((y\[LeftTriangle]T2)\[Transpose]\[LeftTriangle]Typings`DualType[T2]) . ((x\[LeftTriangle]T1)\[Transpose]\[LeftTriangle]Typings`DualType[T1])\[LeftTriangle]L
];


(* TRANSTSR *)
AppendTo[
	ExtRewritingRules,
	((x_\[LeftTriangle]T1_)\[CircleTimes](y_\[LeftTriangle]T2_)\[LeftTriangle]R_)\[Transpose]\[LeftTriangle]L_/;Typings`TensorTypeMatchQ[T1,T2,R]&&Typings`TypeDualQ[R,L]->
		((x\[LeftTriangle]T1)\[Transpose]\[LeftTriangle]Typings`DualType[T1])\[CircleTimes]((y\[LeftTriangle]T2)\[Transpose]\[LeftTriangle]Typings`DualType[T2])\[LeftTriangle]L
];


(* ::Subsection:: *)
(*SUM-ELIM*)


(* SUMELIM0 *)
AppendTo[
	ExtRewritingRules,
	DSum[Ext`BINDV[_],Zero[T_]\[LeftTriangle]T_]\[LeftTriangle]T_->Zero[T]\[LeftTriangle]T
];


(* SUMELIMDELTA1 *)
AppendTo[
	ExtRewritingRules,
	DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)...,i_\[LeftTriangle]T_],Delta[i_\[LeftTriangle]T_,j_\[LeftTriangle]T_]\[LeftTriangle]\[ScriptCapitalS]]\[LeftTriangle]\[ScriptCapitalS]
	/;FreeQ[j,i]
	->DSum[Ext`BINDV[bindvs],C[1]\[LeftTriangle]\[ScriptCapitalS]]\[LeftTriangle]\[ScriptCapitalS]
];


(* SUMELIMDELTA2 *)
AppendTo[
	ExtRewritingRules,
	DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)...,i_\[LeftTriangle]T_],
		(eles:(_\[LeftTriangle]Typings`DiracTypePatt)..)(Delta[i_\[LeftTriangle]T_,j_\[LeftTriangle]T_]\[LeftTriangle]\[ScriptCapitalS])\[LeftTriangle]AT_
	]\[LeftTriangle]AT_
	/;FreeQ[j,i]
	:>DSum[Ext`BINDV[bindvs],(Times[eles]//.{i->j})\[LeftTriangle]AT]\[LeftTriangle]AT
];


(* ::Subsection:: *)
(*SUM-DIST*)


(* SUMPULL0 *)
AppendTo[
	ExtRewritingRules,
	DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)...,i_\[LeftTriangle]T_],
	(eles:(_\[LeftTriangle]Typings`DiracTypePatt)..)(A_\[LeftTriangle]\[ScriptCapitalS])\[LeftTriangle]RT_]\[LeftTriangle]RT_
	/;FreeQ[A,i]
	:>DSum[Ext`BINDV[bindvs],(DSum[i\[LeftTriangle]T,Times[eles]\[LeftTriangle]RT]\[LeftTriangle]RT)(A\[LeftTriangle]\[ScriptCapitalS])\[LeftTriangle]RT]\[LeftTriangle]RT
];

AppendTo[
	ExtRewritingRules,
	DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)...,i_\[LeftTriangle]T_],
	(eles:(_\[LeftTriangle]\[ScriptCapitalS])..)(A_\[LeftTriangle]RT:Typings`DiracTypePatt)\[LeftTriangle]RT_]\[LeftTriangle]RT_
	/;FreeQ[A,i]
	:>DSum[Ext`BINDV[bindvs],(DSum[i\[LeftTriangle]T,Times[eles]\[LeftTriangle]\[ScriptCapitalS]]\[LeftTriangle]\[ScriptCapitalS])(A\[LeftTriangle]RT)\[LeftTriangle]RT]\[LeftTriangle]RT
];


(* SUMPUSHADJ *)
AppendTo[
	ExtRewritingRules,
	(DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)..],
	t_\[LeftTriangle]RT:Typings`DiracTypePatt]\[LeftTriangle]RT_)\[ConjugateTranspose]\[LeftTriangle]RTT_
	/;Typings`TypeDualQ[RT,RTT]
	:>DSum[Ext`BINDV[bindvs],(t\[LeftTriangle]RT)\[ConjugateTranspose]\[LeftTriangle]RTT]\[LeftTriangle]RTT
];


(* SUMPUSHTRANS *)
AppendTo[
	ExtRewritingRules,
	(DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)..],
	t_\[LeftTriangle]RT:Typings`DiracTypePatt]\[LeftTriangle]RT_)\[Transpose]\[LeftTriangle]RTT_
	/;Typings`TypeDualQ[RT,RTT]
	:>DSum[Ext`BINDV[bindvs],(t\[LeftTriangle]RT)\[Transpose]\[LeftTriangle]RTT]\[LeftTriangle]RTT
];


(* SUMPULLDOTL *)
AppendTo[
	ExtRewritingRules,
	DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)...,i_\[LeftTriangle]T_],
	(A_\[LeftTriangle]AT:Typings`DiracTypePatt) . (B_\[LeftTriangle]BT:Typings`DiracTypePatt)\[LeftTriangle]ABT_]\[LeftTriangle]ABT_
	/;Typings`DotTypeMatchQ[AT,BT,ABT]&&FreeQ[A,i]
	:>DSum[Ext`BINDV[bindvs],(A\[LeftTriangle]AT) . (DSum[i\[LeftTriangle]T,B\[LeftTriangle]BT]\[LeftTriangle]BT)\[LeftTriangle]ABT]\[LeftTriangle]ABT
];


(* SUMPULLDOTR *)
AppendTo[
	ExtRewritingRules,
	DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)...,i_\[LeftTriangle]T_],
	(A_\[LeftTriangle]AT:Typings`DiracTypePatt) . (B_\[LeftTriangle]BT:Typings`DiracTypePatt)\[LeftTriangle]ABT_]\[LeftTriangle]ABT_
	/;Typings`DotTypeMatchQ[AT,BT,ABT]&&FreeQ[B,i]
	:>DSum[Ext`BINDV[bindvs],(DSum[i\[LeftTriangle]T,A\[LeftTriangle]AT]\[LeftTriangle]AT) . (B\[LeftTriangle]BT)\[LeftTriangle]ABT]\[LeftTriangle]ABT
];


(* SUMPULLTSRL *)
AppendTo[
	ExtRewritingRules,
	DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)...,i_\[LeftTriangle]T_],
	(A_\[LeftTriangle]AT:Typings`DiracTypePatt)\[CircleTimes](B_\[LeftTriangle]BT:Typings`DiracTypePatt)\[LeftTriangle]ABT_]\[LeftTriangle]ABT_
	/;Typings`TensorTypeMatchQ[AT,BT,ABT]&&FreeQ[A,i]
	:>DSum[Ext`BINDV[bindvs],(A\[LeftTriangle]AT)\[CircleTimes](DSum[i\[LeftTriangle]T,B\[LeftTriangle]BT]\[LeftTriangle]BT)\[LeftTriangle]ABT]\[LeftTriangle]ABT
];


(* SUMPULLTSRR *)
AppendTo[
	ExtRewritingRules,
	DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)...,i_\[LeftTriangle]T_],
	(A_\[LeftTriangle]AT:Typings`DiracTypePatt)\[CircleTimes](B_\[LeftTriangle]BT:Typings`DiracTypePatt)\[LeftTriangle]ABT_]\[LeftTriangle]ABT_
	/;Typings`TensorTypeMatchQ[AT,BT,ABT]&&FreeQ[B,i]
	:>DSum[Ext`BINDV[bindvs],(DSum[i\[LeftTriangle]T,A\[LeftTriangle]AT]\[LeftTriangle]AT)\[CircleTimes](B\[LeftTriangle]BT)\[LeftTriangle]ABT]\[LeftTriangle]ABT
];


(* SUMPULLSINGLE *)
AppendTo[
	ExtRewritingRules,
	DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)...,i_\[LeftTriangle]T_],
	A_\[LeftTriangle]AT:Typings`DiracTypePatt]\[LeftTriangle]AT_
	/;FreeQ[A,i]&&A=!=C[1]
	:>DSum[Ext`BINDV[bindvs],(DSum[i\[LeftTriangle]T,C[1]\[LeftTriangle]\[ScriptCapitalS]]\[LeftTriangle]\[ScriptCapitalS])(A\[LeftTriangle]AT)\[LeftTriangle]AT]\[LeftTriangle]AT
];


(* ::Subsection:: *)
(*SUM-COMP*)


(* SUMCOMPDOTL *)
AppendTo[
	ExtRewritingRules,
	(A_\[LeftTriangle]AT_) . (DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)..],B_\[LeftTriangle]BT_]\[LeftTriangle]BT_)\[LeftTriangle]ABT_
	/;DiracExtNorm[DSumRename[(A\[LeftTriangle]AT)] . (B\[LeftTriangle]BT)\[LeftTriangle]ABT]=!=(A\[LeftTriangle]AT) . (B\[LeftTriangle]BT)\[LeftTriangle]ABT
	:>DSum[Ext`BINDV[bindvs],DiracExtNorm[DSumRename[(A\[LeftTriangle]AT)] . (B\[LeftTriangle]BT)\[LeftTriangle]ABT]]\[LeftTriangle]ABT
];


(* SUMCOMPDOTR *)
AppendTo[
	ExtRewritingRules,
	(DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)..],A_\[LeftTriangle]AT_]\[LeftTriangle]AT_) . (B_\[LeftTriangle]BT_)\[LeftTriangle]ABT_
	/;DiracExtNorm[(A\[LeftTriangle]AT) . DSumRename[(B\[LeftTriangle]BT)]\[LeftTriangle]ABT]=!=(A\[LeftTriangle]AT) . (B\[LeftTriangle]BT)\[LeftTriangle]ABT
	:>DSum[Ext`BINDV[bindvs],DiracExtNorm[(A\[LeftTriangle]AT) . DSumRename[(B\[LeftTriangle]BT)]\[LeftTriangle]ABT]]\[LeftTriangle]ABT
];


(* SUMCOMPTSRL *)
AppendTo[
	ExtRewritingRules,
	(A_\[LeftTriangle]AT_)\[CircleTimes](DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)..],B_\[LeftTriangle]BT_]\[LeftTriangle]BT_)\[LeftTriangle]ABT_
	/;DiracExtNorm[Ext`DSumRename[(A\[LeftTriangle]AT)]\[CircleTimes](B\[LeftTriangle]BT)\[LeftTriangle]ABT]=!=(A\[LeftTriangle]AT)\[CircleTimes](B\[LeftTriangle]BT)\[LeftTriangle]ABT
	:>DSum[Ext`BINDV[bindvs],DiracExtNorm[DSumRename[(A\[LeftTriangle]AT)]\[CircleTimes](B\[LeftTriangle]BT)\[LeftTriangle]ABT]]\[LeftTriangle]ABT
];


(* SUMCOMPTSRR *)
AppendTo[
	ExtRewritingRules,
	(DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)..],A_\[LeftTriangle]AT_]\[LeftTriangle]AT_)\[CircleTimes](B_\[LeftTriangle]BT_)\[LeftTriangle]ABT_
	/;DiracExtNorm[(A\[LeftTriangle]AT)\[CircleTimes]DSumRename[(B\[LeftTriangle]BT)]\[LeftTriangle]ABT]=!=(A\[LeftTriangle]AT)\[CircleTimes](B\[LeftTriangle]BT)\[LeftTriangle]ABT
	:>DSum[Ext`BINDV[bindvs],DiracExtNorm[(A\[LeftTriangle]AT)\[CircleTimes]DSumRename[(B\[LeftTriangle]BT)]\[LeftTriangle]ABT]]\[LeftTriangle]ABT
];


(* ::Subsection:: *)
(*Rewriting Methods*)


ExtRewritingRulesWithTyping = ExtRewritingRules;

(* the method to invoke rewriting *)
DiracExtNorm[term_,assign_List:{}]:=
	With[{res=DiracExtTypeCheck[term,assign]//.ExtRewritingRulesWithTyping}, 
		If[Head[res]=!=Typing,Throw["Not well typed term: ",res]];
		res];


DiracExtNormDebug[term_,assign_List:{}]:=
	Module[{temp=DiracExtTypeCheck[term,assign],res}, 
		res=FixedPoint[
			(
				Print["[Debug]:"];
				Print[#//RemoveType];
				#/.ExtRewritingRulesWithTyping
			)&,
			temp
		];
		If[Head[res]=!=Typing,Throw["Not well typed term: ",res]];
		res];


(* ::Subsection:: *)
(*Sum Expand*)


(* The function to expand the summation 
	The argument should be a well-typed term.
*)
ExpandRule=DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)...,i_\[LeftTriangle]{vals__}],body_]\[LeftTriangle]T_:>DSum[Ext`BINDV[bindvs],Fold[#1+(body//.{i->#2})&,Zero[T],{vals}]]\[LeftTriangle]T;
DSumExpand[wtTerm_Typing]:=DiracExtNorm[wtTerm//.ExpandRule];


End[];


(* ::Section:: *)
(*Transform Commands*)


EntryReduce[term_]:=term//.{
	DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)...,i_\[LeftTriangle]T_],
	(((Bra[{i_\[LeftTriangle]T_}]\[LeftTriangle]\[ScriptCapitalB][T_]) . (K_\[LeftTriangle]\[ScriptCapitalK][T_]))\[LeftTriangle]\[ScriptCapitalS])(Ket[{i_\[LeftTriangle]T_}]\[LeftTriangle]\[ScriptCapitalK][T_])\[LeftTriangle]\[ScriptCapitalK][T_]]\[LeftTriangle]\[ScriptCapitalK][T_]
	->DSum[Ext`BINDV[bindvs],K\[LeftTriangle]\[ScriptCapitalK][T]],
	
	DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)...,i_\[LeftTriangle]T_],
	(((B_\[LeftTriangle]\[ScriptCapitalB][T_]) . (Ket[{i_\[LeftTriangle]T_}]\[LeftTriangle]\[ScriptCapitalK][T_]))\[LeftTriangle]\[ScriptCapitalS])(Bra[{i_\[LeftTriangle]T_}]\[LeftTriangle]\[ScriptCapitalB][T_])\[LeftTriangle]\[ScriptCapitalB][T_]]\[LeftTriangle]\[ScriptCapitalB][T_]
	->DSum[Ext`BINDV[bindvs],B\[LeftTriangle]\[ScriptCapitalB][T]],
	
	DSum[Ext`BINDV[bindvs:(_\[LeftTriangle]_)...,i_\[LeftTriangle]T_,j_\[LeftTriangle]R_],
	(((Bra[{i_\[LeftTriangle]T_}]\[LeftTriangle]\[ScriptCapitalB][T_]) . (o_\[LeftTriangle]\[ScriptCapitalO][T_,R_]) . (Ket[{j_\[LeftTriangle]R_}]\[LeftTriangle]\[ScriptCapitalK][R_]))\[LeftTriangle]\[ScriptCapitalS])((Ket[{i_\[LeftTriangle]T_}]\[LeftTriangle]\[ScriptCapitalK][T_])\[CircleTimes](Bra[{j_\[LeftTriangle]R_}]\[LeftTriangle]\[ScriptCapitalB][R_])\[LeftTriangle]\[ScriptCapitalO][T_,R_])\[LeftTriangle]\[ScriptCapitalO][T_,R_]]\[LeftTriangle]\[ScriptCapitalO][T_,R_]
	->DSum[Ext`BINDV[bindvs],o\[LeftTriangle]\[ScriptCapitalO][T,R]]
};


EntryExpand[term_]:=term//.{
	
};


(* ::Section:: *)
(*The Equivalence Test Function*)


Begin["EqTest`"];


(* ::Subsection:: *)
(*The JUXTAPOSE symbol for B.K==K\[Transpose].B\[Transpose]*)


JUX;
SetAttributes[JUX,Orderless];

(* term should be checked already *)
Juxtapose[term_]:=term/.{(B:(_\[LeftTriangle]\[ScriptCapitalB][_])) . (K:(_\[LeftTriangle]\[ScriptCapitalK][_]))\[LeftTriangle]\[ScriptCapitalS]->JUX[B . K\[LeftTriangle]\[ScriptCapitalS],K\[Transpose] . B\[Transpose]\[LeftTriangle]\[ScriptCapitalS]]\[LeftTriangle]\[ScriptCapitalS]};


(* ::Subsection:: *)
(*Alpha-Conversion for Sum*)


(* 
This function transforms a term with DSum into the form that incorporates alpha equivalence.
newvars is the list of new variables for the transformation.
This method functions correctly because ReplaceAll scans in the top-down manner. *)
DSumEqNorm[term_,newvars_List]:=term/.
	dsum:DSum[Ext`BINDV[(_\[LeftTriangle]_)..],body_]\[LeftTriangle]_:>With[
		{bindvs=BindVars[dsum]},
		(* sort the bind variable according to their first appearance in the body*)
		dsum/.Thread[Keys[Sort[Association[#->First[Position[body,#],{0}]&/@bindvs]]]->Take[newvars,Length[bindvs]]]
	];


(* ::Subsection:: *)
(*Checking Function*)


DiracEqQ[termA_,termB_]:=
	Module[{normA=DiracExtNorm[termA],normB=DiracExtNorm[termB],newvars},
		normA=Juxtapose[normA]//DiracExtNorm;
		normB=Juxtapose[normB]//DiracExtNorm;
		newvars=Unique[BindVars[normA]\[Union]BindVars[normB]];
		normA=DSumEqNorm[normA,newvars]//DiracExtNorm;
		normB=DSumEqNorm[normB,newvars]//DiracExtNorm;
		
		(*Print[normA];
		Print[normB];*)
		
		normA===normB
		];
End[];


End[];


EndPackage[];
