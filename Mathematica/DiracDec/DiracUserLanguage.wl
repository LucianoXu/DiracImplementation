(* ::Package:: *)

(* ::Title:: *)
(*Dirac User Language*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracUserLanguage`", {"DiracCore`", "DiracDeltaExt`", "DiracSumExt`", "DiracProjExt`","DiracProjSumExt`"}];


DiracParse::usage="The parser from user language to internal language";


Begin["Private`"];


DiracParse[e_]:=e;
(* iterate through Dirac subterms *)
DiracParse[CPX[e_]]:=CPX[e];
DiracParse[f_[args___]]/;MemberQ[DiracSymbols, f]:=f@@(DiracParse[#]&/@{args});

DiracParseBuild[e_]:=Throw["Parsing Failed: ",e];


(* ::Text:: *)
(*We need the TypeCalc definition on user language to allow the application of user language in definitions TPO.*)


TCalc[Ket[{s_}]]:=KType[TCalc[s]];
DiracParse[Ket[{s_}]]:=KET[s];
TCalc[Bra[{s_}]]:=BType[TCalc[s]];
DiracParse[Bra[{s_}]]:=BRA[s];


TCalc[Verbatim[Plus][D1_, Ds___]]:=TCalc[D1];
DiracParse[Verbatim[Plus][D1_, D2_]]:=
	With[{D1Res=DiracParse[D1], D2Res=DiracParse[D2]},
		DiracParseBuild[Hold[D1Res+D2Res]]
	];
DiracParse[Verbatim[Plus][D1_, Ds__]]:=
	With[{D1Res=DiracParse[D1]},
		DiracParseBuild[Hold[D1Res + DiracParse[Unevaluated[Plus[Ds]]]]]
	];
DiracParseBuild[Hold[D1_ + D2_]]/;
	MatchQ[TCalc[D1],SType]&&MatchQ[TCalc[D2], SType] := D1 ~ADDS~ D2;
DiracParseBuild[Hold[D1_ + D2_]]/;
	MatchQ[TCalc[D1],KType[_]]&&MatchQ[TCalc[D2], KType[_]] := D1 ~ADDK~ D2;
DiracParseBuild[Hold[D1_ + D2_]]/;
	MatchQ[TCalc[D1],BType[_]]&&MatchQ[TCalc[D2], BType[_]] := D1 ~ADDB~ D2;
DiracParseBuild[Hold[D1_ + D2_]]/;
	MatchQ[TCalc[D1],OType[_, _]]&&MatchQ[TCalc[D2], OType[_, _]] := D1 ~ADDO~ D2;


TCalc[Verbatim[Times][D1_]]:=TCalc[D1];
TCalc[Verbatim[Times][D1_, Ds__]]:=
	With[{T1=TCalc[D1], T2=TCalc[Unevaluated[Times[Ds]]]},
		Which[
			MatchQ[T1, SType]&&MatchQ[T2, SType],
				SType,
			MatchQ[T1, SType]&&MatchQ[T2, KType[_]],
				T2,
			MatchQ[T1, SType]&&MatchQ[T2, BType[_]],
				T2,
			MatchQ[T1, SType]&&MatchQ[T2, OType[_, _]],
				T2,
			MatchQ[T2, SType]&&MatchQ[T1, KType[_]],
				T1,
			MatchQ[T2, SType]&&MatchQ[T1, BType[_]],
				T1,
			MatchQ[T2, SType]&&MatchQ[T1, OType[_, _]],
				T1,
			True,
				Throw[{"Type Calc Error:", T1, "Times", T2}]
		]
	];
DiracParse[Verbatim[Times][D1_, D2_]]:=
	With[{D1Res=DiracParse[D1], D2Res=DiracParse[D2]},
		DiracParseBuild[Hold[D1Res D2Res]]	
	];
DiracParse[Verbatim[Times][D1_, Ds__]]:=
	With[{D1Res=DiracParse[D1]},
		DiracParseBuild[Hold[D1Res DiracParse[Unevaluated[Times[Ds]]]]]
	];
DiracParseBuild[Hold[D1_ D2_]]/;
	MatchQ[TCalc[D1],SType]&&MatchQ[TCalc[D2], SType]:= D1 ~MLTS~ D2;
	
DiracParseBuild[Hold[D1_ D2_]]/;
	MatchQ[TCalc[D1],SType]&&MatchQ[TCalc[D2], KType[_]]:= D1 ~SCRK~ D2;
DiracParseBuild[Hold[D1_ D2_]]/;
	MatchQ[TCalc[D1],SType]&&MatchQ[TCalc[D2], BType[_]]:= D1 ~SCRB~ D2;
DiracParseBuild[Hold[D1_ D2_]]/;
	MatchQ[TCalc[D1],SType]&&MatchQ[TCalc[D2], OType[_, _]]:= D1 ~SCRO~ D2;
	
DiracParseBuild[Hold[D1_ D2_]]/;
	MatchQ[TCalc[D2],SType]&&MatchQ[TCalc[D1], KType[_]]:= D2 ~SCRK~ D1;
DiracParseBuild[Hold[D1_ D2_]]/;
	MatchQ[TCalc[D2],SType]&&MatchQ[TCalc[D1], BType[_]]:= D2 ~SCRB~ D1;
DiracParseBuild[Hold[D1_ D2_]]/;
	MatchQ[TCalc[D2],SType]&&MatchQ[TCalc[D1], OType[_, _]]:= D2 ~SCRO~ D1;


TCalc[SmallCircle[D1_]]:=TCalc[D1];
TCalc[D1_ \[SmallCircle] Ds__]:=
	With[{T1=TCalc[D1], T2=TCalc[Unevaluated[SmallCircle[Ds]]]},
		Which[
			MatchQ[T1, SType]&&MatchQ[T2, SType],
				SType,
			MatchQ[T1, SType]&&MatchQ[T2, KType[_]],
				T2,
			MatchQ[T1, SType]&&MatchQ[T2, BType[_]],
				T2,
			MatchQ[T1, SType]&&MatchQ[T2, OType[_, _]],
				T2,
			MatchQ[T1, KType[_]&&MatchQ[T2, SType]],
				T1,
			MatchQ[T1, KType[_]&&MatchQ[T2, KType[_]]],
				KType[TProjK[T1]~ProdType~TProjK[T2]],
			MatchQ[T1, KType[_]&&MatchQ[T2, BType[_]]],
				OType[TProjK[T1], TProjB[T2]],
			MatchQ[T1, BType[_]&&MatchQ[T2, SType]],
				T1,
			MatchQ[T1, BType[_]&&MatchQ[T2, KType[_]]],
				SType,
			MatchQ[T1, BType[_]&&MatchQ[T2, BType[_]]],
				BType[TProjB[T1]~ProdType~TProjB[T2]],
			MatchQ[T1, BType[_]&&MatchQ[T2, OType[_, _]]],
				BType[TProjB[T2]],
			MatchQ[T1, OType[_, _]&&MatchQ[T2, SType]],
				T1,
			MatchQ[T1, OType[_, _]&&MatchQ[T2, KType[_]]],
				KType[TProjK[T1]],
			MatchQ[T1, OType[_, _]&&MatchQ[T2, OType[_, _]]],
				OType[TProjK[T1], TProjB[T2]],
			True,
				Throw[{"Type Calc Error: ", T1, "\[SmallCircle]", T2}]
		]
	];
DiracParse[D1_ \[SmallCircle] D2_]:=
	With[{D1Res=DiracParse[D1], D2Res=DiracParse[D2]},
		DiracParseBuild[Hold[D1Res \[SmallCircle] D2Res]]
	];
DiracParse[D1_ \[SmallCircle] Ds__]:=
	With[{D1Res=DiracParse[D1]},
		DiracParseBuild[Hold[D1Res \[SmallCircle] DiracParse[SmallCircle[Ds]]]]
	];
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TCalc[D1],SType]&&MatchQ[TCalc[D2], SType]:= D1 ~MLTS~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TCalc[D1],SType]&&MatchQ[TCalc[D2], KType[_]]:= D1 ~SCRK~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TCalc[D1],SType]&&MatchQ[TCalc[D2], BType[_]]:= D1 ~SCRB~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TCalc[D1],SType]&&MatchQ[TCalc[D2], OType[_, _]]:= D1 ~SCRO~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TCalc[D1],KType[_]]&&MatchQ[TCalc[D2], SType]:= D2 ~SCRK~ D1;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TCalc[D1],KType[_]]&&MatchQ[TCalc[D2], KType[_]]:= D1 ~TSRK~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TCalc[D1],KType[_]]&&MatchQ[TCalc[D2], BType[_]]:= D1 ~OUTER~ D2;
(*
	DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]
	(* K \[SmallCircle] O Not Valid *)
*)
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TCalc[D1],BType[_]]&&MatchQ[TCalc[D2], SType]:= D2 ~SCRB~ D1;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TCalc[D1],BType[_]]&&MatchQ[TCalc[D2], KType[_]]:= D1 ~DOT~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TCalc[D1],BType[_]]&&MatchQ[TCalc[D2], BType[_]]:= D1 ~TSRB~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TCalc[D1],BType[_]]&&MatchQ[TCalc[D2], OType[_, _]]:= D1 ~MLTB~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TCalc[D1],OType[_, _]]&&MatchQ[TCalc[D2], SType]:= D2 ~TSRO~ D1;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TCalc[D1],OType[_, _]]&&MatchQ[TCalc[D2], KType[_]]:= D1 ~MLTK~ D2;
(*
	DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]
	(* O \[SmallCircle] B Not Valid *)
*)
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TCalc[D1],OType[_, _]]&&MatchQ[TCalc[D2], OType[_, _]]:= D1 ~MLTO~ D2;



TCalc[CircleTimes[D1_]]:=TCalc[D1];
TCalc[D1_ \[CircleTimes] Ds__]:=
	With[{T1=TCalc[D1], T2=TCalc[Unevaluated[CircleTimes[Ds]]]},
		Which[
			MatchQ[T1, KType[_]&&MatchQ[T2, KType[_]]],
				KType[TProjK[T1]~ProdType~TProjK[T2]],
			MatchQ[T1, BType[_]&&MatchQ[T2, BType[_]]],
				BType[TProjB[T1]~ProdType~TProjB[T2]],
			MatchQ[T1, OType[_, _]&&MatchQ[T2, OType[_, _]]],
				OType[TProjK[T1]~ProdType~TProjK[T2], TProjB[T1]~ProdType~TProjB[T2]],
			True,
				Throw["Type Calc Error: \[CircleTimes]"]
		]
	];
	
DiracParse[D1_ \[CircleTimes] D2_]:=
	With[{D1Res=DiracParse[D1], D2Res=DiracParse[D2]},
		DiracParseBuild[Hold[D1Res \[CircleTimes] D2Res]]	
	];
DiracParse[D1_ \[CircleTimes] Ds__]:=
	With[{D1Res=DiracParse[D1]},
		DiracParseBuild[Hold[D1Res \[SmallCircle] DiracParse[CircleTimes[Ds]]]]
	];
DiracParseBuild[Hold[D1_ \[CircleTimes] D2_]]/;
	MatchQ[TCalc[D1],KType[_]]&&MatchQ[TCalc[D2], KType[_]] := D1 ~TSRK~ D2;
DiracParseBuild[Hold[D1_ \[CircleTimes] D2_]]/;
	MatchQ[TCalc[D1],BType[_]]&&MatchQ[TCalc[D2], BType[_]] := D1 ~TSRB~ D2;
DiracParseBuild[Hold[D1_ \[CircleTimes] D2_]]/;
	MatchQ[TCalc[D1],KType[_]]&&MatchQ[TCalc[D2], BType[_]] := D1 ~OUTER~ D2;
DiracParseBuild[Hold[D1_ \[CircleTimes] D2_]]/;
	MatchQ[TCalc[D1],OType[_, _]]&&MatchQ[TCalc[D2], OType[_, _]] := D1 ~TSRO~ D2;


TCalc[SuperDagger[D_]]:=
	With[{T=TCalc[D]},
		Which[
			MatchQ[T, SType],
				SType,
			MatchQ[T, KType[_]],
				BType[TProjK[T]],
			MatchQ[T, BType[_]],
				KType[TProjB[T]],
			MatchQ[T, OType[_, _]],
				OType[TProjB[T], TProjK[T]],
			True,
				Throw["Type Calc Error: \[Dagger]"]
		]
	];
DiracParse[SuperDagger[D_]]:=With[{DRes=DiracParse[D]}, DiracParseBuild[Hold[SuperDagger[DRes]]]];
DiracParseBuild[Hold[SuperDagger[D_]]]/;
	MatchQ[TCalc[D], SType] := CONJS[D];
DiracParseBuild[Hold[SuperDagger[D_]]]/;
	MatchQ[TCalc[D], KType[_]] := ADJB[D];
DiracParseBuild[Hold[SuperDagger[D_]]]/;
	MatchQ[TCalc[D], BType[_]] := ADJK[D];
DiracParseBuild[Hold[SuperDagger[D_]]]/;
	MatchQ[TCalc[D], OType[_,_]] := ADJO[D];


TCalc[Sum[body_, {i_, M_}]]:=Block[{DiracCtx=Join[DiracCtx, DiracIdxCtx[IDX[{i, M}]]]}, TCalc[body]];
TCalc[Sum[body_, idx_]]:=Block[{DiracCtx=Join[DiracCtx, DiracIdxCtx[idx]]}, TCalc[body]];

(* Create new variables automatically when parsing Sum *)
DiracParse[Sum[body_, idx_IDX]]:=
	With[{nvs=Table[Unique[], Length[idx]]},
		With[
		{
			bodyRes=DiracParse[body/.Thread[First/@(List@@idx)->nvs]], 
			idxRes=DiracParse[IDX@@(Table[{nvs[[i]],idx[[i,2]]},{i,Length[idx]}])]
		}, 
		DiracParseBuild[Hold[Sum[bodyRes, idxRes]]]
		]
	];
DiracParse[Sum[body_, {i_, M_}]]:=
	With[{nv=Unique[]},
		With[
		{
			bodyRes=DiracParse[body/.i->nv], 
			MRes=DiracParse[M]
		}, 
		DiracParseBuild[Hold[Sum[bodyRes, IDX[{nv, MRes}]]]]
		]
	];
DiracParseBuild[Hold[Sum[body_, idx_]]]/;
	MatchQ[Block[{DiracCtx=Join[DiracCtx, DiracIdxCtx[idx]]}, TCalc[body]], SType] := SUMS[idx, body];
DiracParseBuild[Hold[Sum[body_, idx_]]]/;
	MatchQ[Block[{DiracCtx=Join[DiracCtx, DiracIdxCtx[idx]]}, TCalc[body]], KType[_]] := SUMK[idx, body];
DiracParseBuild[Hold[Sum[body_, idx_]]]/;
	MatchQ[Block[{DiracCtx=Join[DiracCtx, DiracIdxCtx[idx]]}, TCalc[body]], BType[_]] := SUMB[idx, body];
DiracParseBuild[Hold[Sum[body_, idx_]]]/;
	MatchQ[Block[{DiracCtx=Join[DiracCtx, DiracIdxCtx[idx]]}, TCalc[body]], OType[_,_]] := SUMO[idx, body];


End[];


EndPackage[];
