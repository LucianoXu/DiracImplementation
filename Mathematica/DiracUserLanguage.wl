(* ::Package:: *)

(* ::Title:: *)
(*Dirac User Language*)


AppendTo[$Path, NotebookDirectory[]];
BeginPackage["DiracUserLanguage`", {"DiracCore`", "DiracDeltaExt`", "DiracSumExt`", "DiracProjExt`","DiracProjSumExt`"}];


DiracParse::usage="The parser from user language to internal language";


Begin["Private`"];


DiracParse[e_]:=e;
(* iterate through all subterms *)
DiracParse[f_[args___]]:=f@@(DiracParse[#]&/@{args});
DiracParse[CPX[e_]]:=CPX[e];
DiracParseBuild[e_]:=Throw["Parsing Failed: ",e];


DiracParse[Ket[{s_}]]:=KET[s];
DiracParse[Bra[{s_}]]:=BRA[s];


DiracParse[Verbatim[Plus][D1_, D2_]]:=
	With[{D1Res=DiracParse[D1], D2Res=DiracParse[D2]},
		DiracParseBuild[Hold[D1Res+D2Res]]
	];
DiracParse[Verbatim[Plus][D1_, Ds__]]:=
	With[{D1Res=DiracParse[D1]},
		DiracParseBuild[Hold[D1Res + DiracParse[Unevaluated[Plus[Ds]]]]]
	];
DiracParseBuild[Hold[D1_ + D2_]]/;
	MatchQ[TypeCalc[D1],SType]&&MatchQ[TypeCalc[D2], SType] := D1 ~ADDS~ D2;
DiracParseBuild[Hold[D1_ + D2_]]/;
	MatchQ[TypeCalc[D1],KType[_]]&&MatchQ[TypeCalc[D2], KType[_]] := D1 ~ADDK~ D2;
DiracParseBuild[Hold[D1_ + D2_]]/;
	MatchQ[TypeCalc[D1],BType[_]]&&MatchQ[TypeCalc[D2], BType[_]] := D1 ~ADDB~ D2;
DiracParseBuild[Hold[D1_ + D2_]]/;
	MatchQ[TypeCalc[D1],OType[_, _]]&&MatchQ[TypeCalc[D2], OType[_, _]] := D1 ~ADDO~ D2;


DiracParse[Verbatim[Times][D1_ D2_]]:=
	With[{D1Res=DiracParse[D1], D2Res=DiracParse[D2]},
		DiracParseBuild[Hold[D1Res D2Res]]	
	];
DiracParse[Verbatim[Times][D1_, Ds__]]:=
	With[{D1Res=DiracParse[D1]},
		DiracParseBuild[Hold[D1Res + DiracParse[Unevaluated[Times[Ds]]]]]
	];
DiracParseBuild[Hold[D1_ D2_]]/;
	MatchQ[TypeCalc[D1],SType]&&MatchQ[TypeCalc[D2], SType]:= D1 ~MLTS~ D2;
DiracParseBuild[Hold[D1_ D2_]]/;
	MatchQ[TypeCalc[D1],SType]&&MatchQ[TypeCalc[D2], KType[_]]:= D1 ~SCRK~ D2;
DiracParseBuild[Hold[D1_ D2_]]/;
	MatchQ[TypeCalc[D1],SType]&&MatchQ[TypeCalc[D2], BType[_]]:= D1 ~SCRB~ D2;
DiracParseBuild[Hold[D1_ D2_]]/;
	MatchQ[TypeCalc[D1],SType]&&MatchQ[TypeCalc[D2], OType[_, _]]:= D1 ~SCRO~ D2;


DiracParse[D1_ \[SmallCircle] D2_]:=
	With[{D1Res=DiracParse[D1], D2Res=DiracParse[D2]},
		DiracParseBuild[Hold[D1Res \[SmallCircle] D2Res]]
	];
DiracParse[D1_ \[SmallCircle] Ds__]:=
	With[{D1Res=DiracParse[D1]},
		DiracParseBuild[Hold[D1Res \[SmallCircle] DiracParse[SmallCircle[Ds]]]]
	];
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TypeCalc[D1],SType]&&MatchQ[TypeCalc[D2], SType]:= D1 ~MLTS~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TypeCalc[D1],SType]&&MatchQ[TypeCalc[D2], KType[_]]:= D1 ~SCRK~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TypeCalc[D1],SType]&&MatchQ[TypeCalc[D2], BType[_]]:= D1 ~SCRB~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TypeCalc[D1],SType]&&MatchQ[TypeCalc[D2], OType[_, _]]:= D1 ~SCRO~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TypeCalc[D1],KType[_]]&&MatchQ[TypeCalc[D2], SType]:= D2 ~SCRK~ D1;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TypeCalc[D1],KType[_]]&&MatchQ[TypeCalc[D2], KType[_]]:= D1 ~TSRK~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TypeCalc[D1],KType[_]]&&MatchQ[TypeCalc[D2], BType[_]]:= D1 ~OUTER~ D2;
(*
	DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]
	(* K \[SmallCircle] O Not Valid *)
*)
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TypeCalc[D1],BType[_]]&&MatchQ[TypeCalc[D2], SType]:= D2 ~SCRB~ D1;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TypeCalc[D1],BType[_]]&&MatchQ[TypeCalc[D2], KType[_]]:= D1 ~DOT~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TypeCalc[D1],BType[_]]&&MatchQ[TypeCalc[D2], BType[_]]:= D1 ~TSRB~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TypeCalc[D1],BType[_]]&&MatchQ[TypeCalc[D2], OType[_, _]]:= D1 ~MLTB~ D2;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TypeCalc[D1],OType[_, _]]&&MatchQ[TypeCalc[D2], SType]:= D2 ~TSRO~ D1;
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TypeCalc[D1],OType[_, _]]&&MatchQ[TypeCalc[D2], KType[_]]:= D1 ~MLTK~ D2;
(*
	DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]
	(* O \[SmallCircle] B Not Valid *)
*)
DiracParseBuild[Hold[D1_ \[SmallCircle] D2_]]/;
	MatchQ[TypeCalc[D1],OType[_, _]]&&MatchQ[TypeCalc[D2], OType[_, _]]:= D1 ~MLTO~ D2;



DiracParse[D1_ \[CircleTimes] D2_]:=
	With[{D1Res=DiracParse[D1], D2Res=DiracParse[D2]},
		DiracParseBuild[Hold[D1Res \[CircleTimes] D2Res]]	
	];
DiracParse[D1_ \[CircleTimes] Ds__]:=
	With[{D1Res=DiracParse[D1]},
		DiracParseBuild[Hold[D1Res \[SmallCircle] DiracParse[CircleTimes[Ds]]]]
	];
DiracParseBuild[Hold[D1_ \[CircleTimes] D2_]]/;
	MatchQ[TypeCalc[D1],KType[_]]&&MatchQ[TypeCalc[D2], KType[_]] := D1 ~TSRK~ D2;
DiracParseBuild[Hold[D1_ \[CircleTimes] D2_]]/;
	MatchQ[TypeCalc[D1],BType[_]]&&MatchQ[TypeCalc[D2], BType[_]] := D1 ~TSRB~ D2;
DiracParseBuild[Hold[D1_ \[CircleTimes] D2_]]/;
	MatchQ[TypeCalc[D1],KType[_]]&&MatchQ[TypeCalc[D2], BType[_]] := D1 ~OUTER~ D2;
DiracParseBuild[Hold[D1_ \[CircleTimes] D2_]]/;
	MatchQ[TypeCalc[D1],OType[_, _]]&&MatchQ[TypeCalc[D2], OType[_, _]] := D1 ~TSRO~ D2;


DiracParse[SuperDagger[D_]]:=With[{DRes=DiracParse[D]}, DiracParseBuild[Hold[SuperDagger[DRes]]]];
DiracParseBuild[Hold[SuperDagger[D_]]]/;
	MatchQ[TypeCalc[D], SType] := CONJS[D];
DiracParseBuild[Hold[SuperDagger[D_]]]/;
	MatchQ[TypeCalc[D], KType[_]] := ADJB[D];
DiracParseBuild[Hold[SuperDagger[D_]]]/;
	MatchQ[TypeCalc[D], BType[_]] := ADJK[D];
DiracParseBuild[Hold[SuperDagger[D_]]]/;
	MatchQ[TypeCalc[D], OType[_,_]] := ADJO[D];


DiracParse[Sum[body_, idx_]]:=With[
	{bodyRes=DiracParse[body], idxRes=DiracParse[idx]}, 
	DiracParseBuild[Hold[Sum[bodyRes, idxRes]]]
	];
DiracParseBuild[Hold[Sum[body_, idx_]]]/;
	MatchQ[TypeCalc[SUMS[idx, body]], SType] := SUMS[idx, body];
DiracParseBuild[Hold[Sum[body_, idx_]]]/;
	MatchQ[TypeCalc[SUMK[idx, body]], KType[_]] := SUMK[idx, body];
DiracParseBuild[Hold[Sum[body_, idx_]]]/;
	MatchQ[TypeCalc[SUMB[idx, body]], BType[_]] := SUMB[idx, body];
DiracParseBuild[Hold[Sum[body_, idx_]]]/;
	MatchQ[TypeCalc[SUMO[idx, body]], OType[_,_]] := SUMO[idx, body];


End[];


EndPackage[];
