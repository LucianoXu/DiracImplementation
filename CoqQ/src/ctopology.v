From mathcomp Require Import all_ssreflect all_algebra.
From quantum.external Require Import forms.
From mathcomp.classical Require Import boolp cardinality mathcomp_extra
  classical_sets functions.
From mathcomp.analysis Require Import ereal reals signed topology 
  prodnormedzmodule normedtype sequences.
From mathcomp.real_closed Require Import complex.
Require Import mcextra mcaextra notation mxpred extnum cpo.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order Order.Theory GRing.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Import VNorm.Exports VOrder.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(* specify extnum theory for R[i]                                             *)
(*         topology/theory of R[i] and 'M[R[i]]                               *)
(* finNormedModType : normedModType & vectType R[i]                           *)
(* vorderFinNormedModType : finNormedModType & vorder                         *)
(* convergence w.r.t. lowner order of matrices                                *)
(* denmx forms CPO                                                            *)
(******************************************************************************)

Module CTopology.

Section C_extNumType.
Import Num.Def Num.Theory.
Variable (R : realType).
Notation C := R[i].

Canonical C_pointedType := 
  Eval hnf in [pointedType of C for [numFieldType of C]].
Canonical C_filteredType := 
  Eval hnf in [filteredType C of C for [filteredType C of [numFieldType of C]]].
Canonical C_topologicalType := 
  Eval hnf in [topologicalType of C for [topologicalType of [numFieldType of C]]].
Canonical C_uniformType := 
  Eval hnf in [uniformType of C for [uniformType of [numFieldType of C]]].
Canonical C_pseudoMetricType := 
  Eval hnf in [pseudoMetricType [numFieldType of C] of C for 
    [pseudoMetricType [numFieldType of C] of [numFieldType of C]]].
Canonical C_pseudoMetricNormedZmodType := 
  Eval hnf in [pseudoMetricNormedZmodType C of C for 
    [pseudoMetricNormedZmodType C of [numFieldType of C]]].
Canonical C_normedModType := 
  Eval hnf in [normedModType C of C for [normedModType C of [numFieldType of C]]].

Let r2cC := [rmorphism of real_complex R] : {rmorphism R -> C}.
Let c2rC := (@complex.Re R).

Lemma continuous_c2rC : continuous c2rC.
Proof.
move=> x s/= /nbhs_ballP [/=e egt0 Pb]; apply/nbhs_ballP.
have Pe: (e%:C) > 0 by rewrite ltc0R.
exists e%:C =>//=; move=> y /= Pxy; apply Pb; move: Pxy.
by rewrite -!ball_normE /ball_/=/c2rC -raddfB/= -ltcR; apply/le_lt_trans/normc_ge_Re.
Qed.

Lemma c2rC_linear (a : R) (b c : C) : 
  c2rC ((r2cC a) * b + c) = a * (c2rC b) + c2rC c.
Proof. 
by rewrite/r2cC/c2rC/= raddfD/=; f_equal; case: b=>br bi=>/=; rewrite mul0r subr0.
Qed.

Let mx2c (m : 'rV[R]_2) := (m 0 0 +i* m 0 1)%C.
Let mx2c_norm (m : 'rV[R]_2) := complex.Re `|mx2c m|.

Lemma mx2c_is_additive : additive mx2c.
Proof. by move=>m n; rewrite/mx2c !mxE; simpc. Qed.
Local Canonical mx2c_additive := Additive mx2c_is_additive.

Lemma mx2c_continuous : continuous mx2c.
Proof.
move=> x s/= /nbhs_ballP [/=[e1 e2] /andP[/eqP e2eq0 e1gt0] Pb]; 
apply/nbhs_ballP; exists (e1/(Num.sqrt 2))=>//=; first by rewrite divr_gt0//.
move=>y/=; rewrite{1}/ball/=/mx_ball=>P; apply Pb.
move: (P 0 0) (P 0 1); rewrite -!ball_normE/ball_ /= e2eq0 /mx2c; simpc.
rewrite -![`| _ | < _ / _](ltr_pXn2r (_ : (0 < 2)%N)) ?real_normK ?num_real// 
  ?nnegrE// ?divr_ge0// ?ltW//= => P1 P2.
rewrite -[e1]gtr0_norm// -sqrtr_sqr ltr_sqrt ?exprn_gt0//.
by apply: (lt_le_trans (ltrD P1 P2)); rewrite expr_div_n sqr_sqrtr// -splitr.
Qed.

Local Program Canonical mx2c_vnorm := @Vnorm _ _ mx2c_norm _ _ _.
Next Obligation.
move=>x y; move: (ler_normD (mx2c x) (mx2c y)).
by rewrite lecE/mx2c_norm !raddfD/==>/andP[].
Qed.
Next Obligation.
move=>x/ComplexField.Normc.eq0_normc/eqP; rewrite eq_complex/==>/andP[/eqP P1/eqP P2].
apply/matrixP=>i j; rewrite ord1 mxE; case: j=>m; case: m=>//=[Pi|n]; last case: n=>//Pi.
rewrite -P1. 2: rewrite -P2. all: by f_equal; apply/val_inj.
Qed.
Next Obligation.
by move=>a x; rewrite/mx2c_norm/= !mxE !exprMn -mulrDr sqrtrM ?sqr_ge0// sqrtr_sqr.
Qed.

Lemma C_bounded_compact (a : C): compact [set x : C | `|x| <= a].
Proof.
case E: (a \is Num.real).
rewrite (_ : mkset _ = mx2c @` [set x : 'rV[R]_2 | mx2c_vnorm x <= complex.Re a]).
apply: continuous_compact.
apply: continuous_subspaceT=>x/= ?; apply: mx2c_continuous.
apply: compact_mnorm_le.
rewrite predeqE=>[[x1 x2]]/=; split=>[Px|[y Py1 Py2]].
exists (\row_j ((j == 0)%:R * x1 + (j == 1)%:R * x2)).
1,2: by rewrite/mx2c/mx2c_norm/=!mxE/= !mul0r !mul1r addr0 add0r// -lecR RRe_real.
by rewrite -Py2 lecE Py1 andbT/= -eqcR/=; apply/eqP/RIm_real.
rewrite (_ : mkset _ = set0).
apply: compact0.
rewrite predeqE=>x/=; split=>// P; move: E; 
by rewrite Num.Theory.realE (le_trans (Num.Theory.normr_ge0 x) P).
Qed.

Program Definition C_extNumMixin := ExtNumMixin _ _ _ 
  continuous_c2rC c2rC_linear C_bounded_compact.
Next Obligation. exact: lecR. Qed.
Next Obligation. by []. Qed.
Next Obligation. exact: RRe_real. Qed.

Canonical C_extNumType := ExtNumType R C C_extNumMixin.

Lemma C_complete (F : set (set C)) : ProperFilter F -> cauchy F -> cvg F.
Proof. exact: extNum_complete. Qed.

Canonical C_completeType := CompleteType C (@C_complete).
Canonical C_CompleteNormedModule := [completeNormedModType C of C].

End C_extNumType.
End CTopology.
Export CTopology.

Section C_sequence.
Variable (R: realType).
Local Notation C := R[i].
Implicit Type (f g: nat -> C) (n: nat) (s a b : C).

Lemma Chausdorff : hausdorff_space [topologicalType of C]. Proof. exact: ethausdorff. Qed.

Lemma ccvg_limE f a : f --> a <-> lim f = a /\ cvg f.
Proof. exact: (cvg_limE f a Chausdorff). Qed.

Lemma ccvg_cst a : (fun n:nat=>a) --> a. Proof. exact: cvg_cst. Qed.
Lemma is_ccvg_cst a : cvg (fun n:nat=>a). Proof. exact: is_cvg_cst. Qed.
Lemma clim_cst a : lim (fun n:nat=>a) = a. Proof. exact: lim_cst. Qed.
Lemma ccvgN f a : f --> a -> (- f) --> - a. Proof. exact: cvgN. Qed.
Lemma is_ccvgN f : cvg f -> cvg (- f). Proof. exact: is_cvgN. Qed.
Lemma is_ccvgNE f : cvg (- f) = cvg f. Proof. exact: is_cvgNE. Qed.
Lemma ccvgMn f n a : f --> a -> ((@GRing.natmul _)^~n \o f) --> a *+ n. Proof. exact: cvgMn. Qed.
Lemma is_ccvgMn f n : cvg f -> cvg ((@GRing.natmul _)^~n \o f). Proof. exact: is_cvgMn. Qed.
Lemma ccvgD f g a b : f --> a -> g --> b -> (f + g) --> a + b. Proof. exact: cvgD. Qed.
Lemma is_ccvgD f g : cvg f -> cvg g -> cvg (f + g). Proof. exact: is_cvgD. Qed.
Lemma ccvgB f g a b : f --> a -> g --> b -> (f - g) --> a - b. Proof. exact: cvgB. Qed.
Lemma is_ccvgB f g : cvg f -> cvg g -> cvg (f - g). Proof. exact: is_cvgB. Qed.
Lemma is_ccvgDlE f g : cvg g -> cvg (f + g) = cvg f. Proof. exact: is_cvgDlE. Qed.
Lemma is_ccvgDrE f g : cvg f -> cvg (f + g) = cvg g. Proof. exact: is_cvgDrE. Qed.
Lemma ccvgM f g a b : f --> a -> g --> b -> (f * g) --> a * b. Proof. exact: cvgZ. Qed.
Lemma is_ccvgM f g : cvg f -> cvg g -> cvg (f * g). Proof. exact: is_cvgZ. Qed.
Lemma ccvgMl f a b (g := fun=>b): f --> a -> f * g --> a * b. Proof. exact: cvgZl. Qed.
Lemma ccvgMr g a b (f := fun=>a): g --> b -> f * g --> a * b. Proof. exact: cvgZr. Qed.
Lemma is_ccvgMr g a (f := fun=> a) : cvg g -> cvg (f * g). Proof. exact: is_cvgZr. Qed.
Lemma is_ccvgMrE g a (f := fun=> a) : a != 0 -> cvg (f * g) = cvg g. Proof. exact: is_cvgZrE. Qed.
Lemma is_ccvgMl f a (g := fun=> a) : cvg f -> cvg (f * g). Proof. exact: is_cvgMl. Qed.
Lemma is_ccvgMlE f a (g := fun=> a) : a != 0 -> cvg (f * g) = cvg f. Proof. exact: is_cvgMlE. Qed.
Lemma ccvg_norm f a : f --> a -> (Num.norm \o f) --> `|a|. Proof. exact: cvg_norm. Qed.
Lemma is_ccvg_norm f : cvg f -> cvg (Num.norm \o f). Proof. exact: is_cvg_norm. Qed.
Lemma climN f : cvg f -> lim (- f) = - lim f. Proof. exact: limN. Qed.
Lemma climD f g : cvg f -> cvg g -> lim (f + g) = lim f + lim g. Proof. exact: limD. Qed.
Lemma climB f g : cvg f -> cvg g -> lim (f - g) = lim f - lim g. Proof. exact: limB. Qed.
Lemma climM f g : cvg f -> cvg g -> lim (f * g) = lim f * lim g. Proof. exact: limM. Qed.
Lemma clim_norm f : cvg f -> lim (Num.norm \o f) = `|lim f|. Proof. exact: lim_norm. Qed.
Lemma climV f : lim f != 0 -> lim ((fun x => (f x)^-1)) = (lim f)^-1. Proof. exact: limV. Qed.

Lemma ccvg_map f a (V : completeType) (h : C -> V) :
  continuous h -> f --> a -> (h \o f) --> h a.
Proof. exact: etcvg_map. Qed. 

Lemma ccvg_mapV (V : completeType) (h : V -> C) (h' : nat -> V) (a : V) :
  continuous h -> h' --> a -> (h \o h') --> h a.
Proof. exact: etcvg_mapV. Qed. 

Lemma is_ccvg_map f (V : completeType) (h : C -> V) :
  continuous h -> cvg f -> cvg (h \o f).
Proof. exact: is_etcvg_map. Qed.

Lemma is_ccvg_mapV (V : completeType) (h : V -> C) (h' : nat -> V) :
  continuous h -> cvg h' -> cvg (h \o h').
Proof. exact: is_etcvg_mapV. Qed.

Lemma clim_map f a (V : completeType) (h : C -> V) :
  hausdorff_space V -> continuous h -> cvg f -> lim (h \o f) = h (lim f).
Proof. by move=>hV ch; move/(ccvg_map ch)/cvg_lim=>/(_ hV). Qed.

Lemma clim_mapV (V : completeType) (h : V -> C) (h' : nat -> V) :
  continuous h -> cvg h' -> lim (h \o h') = h (lim h').
Proof. by move=>ch; move/(ccvg_mapV ch)/cvg_lim=>/(_ Chausdorff). Qed.

Lemma ccvg_limP f a :
  f --> a <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> `|f n - a| < e.
Proof. exact: cvg_limP. Qed.

Lemma ccvg_subseqP f a : 
  f --> a <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N) -> (f \o h) --> a).
Proof. exact: cvg_subseqP. Qed.

Lemma ccvg_subseqPN f a :
  ~ (f --> a) <-> exists e (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ 0 < e /\ (forall n, `|(f \o h) n - a| >= e).
Proof. exact: cvg_subseqPN. Qed.

Definition ccauchy_seq f := forall e, 0 < e -> exists N, forall i j, 
  (N <= i)%N -> (N <= j)%N -> `| f i - f j | < e.

Lemma ccauchy_seqP f : ccauchy_seq f <-> cvg f.
Proof. exact: cauchy_seqP. Qed.

Definition ccvg_seq f a := 
  forall e, 0 < e -> exists N : nat, 
    forall i, (N <= i)%N -> `| a - f i | < e.

Lemma ccvg_seqP f a : ccvg_seq f a <-> f --> a.
Proof. exact: cvg_seqP. Qed.

Lemma re_continuous : continuous (@Re R).
Proof. 
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists e%:C =>//=. by rewrite ltcR.
move=> y /= Pxy. apply (Pb (Re y)). move: Pxy.
rewrite -ball_normE/= /ball/= -raddfB/= -ltcR.
apply: (le_lt_trans (normc_ge_Re _)).
Qed.

Lemma im_continuous : continuous (@Im R).
Proof. 
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists e%:C =>//=. by rewrite ltcR.
move=> y /= Pxy. apply (Pb (Im y)). move: Pxy.
rewrite -ball_normE/= /ball/= -raddfB/= -ltcR.
apply: (le_lt_trans (normc_ge_Im _)).
Qed.

Lemma rc_continuous : continuous (@real_complex R).
Proof. 
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists (Re e) =>//=. by apply real_gt0.
move=> y /= Pxy. apply (Pb y%:C). move: Pxy.
by rewrite -ball_normE/= /ball/= -raddfB/= -ltcR cgt0_real// normc_real.
Qed.

Lemma ic_continuous : continuous (@im_complex R).
Proof. 
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists (Re e) =>//=. by apply real_gt0.
move=> y /= Pxy. apply (Pb y%:Ci). move: Pxy.
rewrite -ball_normE/= /ball/= -(@raddfB _ _ (im_complex_additive R))/=.
by rewrite normc_im -ltcR cgt0_real// normc_real.
Qed.

Lemma conjC_continuous (K : numClosedFieldType) : continuous (@Num.Theory.conjC K).
Proof.
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists (e) =>//=.
move=> y /= Pxy. apply (Pb (@Num.Theory.conjC K y)). move: Pxy.
by rewrite /ball/= -rmorphB Num.Theory.norm_conjC.
Qed.
Lemma ccvg_conj f a : f --> a -> (Num.Theory.conjC \o f) --> (Num.Theory.conjC a).
Proof. by apply: continuous_cvg; apply conjC_continuous. Qed.
Lemma is_ccvg_conj f : cvg f -> cvg (Num.Theory.conjC \o f).
Proof. by move=> /ccvg_conj /cvgP. Qed.
Lemma is_ccvg_conjE f : cvg (Num.Theory.conjC \o f) = cvg f.
Proof. 
rewrite propeqE; split.
have P1: f = (Num.Theory.conjC \o (Num.Theory.conjC \o f))
by apply/funext=>x/=; rewrite Num.Theory.conjCK.
rewrite [in X in _ -> X]P1. all: apply is_ccvg_conj.
Qed.
Lemma clim_conj f : cvg f -> lim (Num.Theory.conjC \o f) = Num.Theory.conjC (lim f).
Proof. by move=> ?; apply: cvg_lim; [apply: Chausdorff | apply: ccvg_conj]. Qed.

End C_sequence.

Section C_monotone.
Variable (R : realType).
Local Notation C := R[i].

Lemma clim_split (u_ : C ^nat) :
  cvg u_ -> lim u_ = (lim ((@Re _) \o u_))%:C + (lim ((@Im _) \o u_))%:Ci.
Proof.
move=>Pcvg; move: Pcvg {+}Pcvg.
move=>/(ccvg_map (@re_continuous R))/(cvg_lim (@Rhausdorff _))->.
move=>/(ccvg_map (@im_continuous R))/(cvg_lim (@Rhausdorff _))->.
by rewrite complex_split.
Qed.

Lemma cnondecreasing_is_cvgn (u_ : C ^nat) (M : C) :
       nondecreasing_seq u_ -> (forall n : nat, u_ n <= M) -> cvg u_.
Proof. exact: etnondecreasing_is_cvgn. Qed.

Lemma cnondecreasing_cvg (u_ : C ^nat) (M : C) :
       nondecreasing_seq u_ -> (forall n : nat, u_ n <= M) -> 
        u_ --> (lim ((@Re _) \o u_))%:C + (Im M)%:Ci.
Proof.
move=>P1 P2. move: (cnondecreasing_is_cvgn P1 P2)=>P3.
rewrite ccvg_limE; split=>//. rewrite clim_split//.
do 2 f_equal. suff ->: (Im (R:=R) \o u_) = (fun=>Im M) by apply: lim_cst.
by apply/funext=>i; move: (P2 i); rewrite/= lecE=>/andP[/eqP->].
Qed.

Lemma cnonincreasing_is_cvg (u_ : C ^nat) (M : C) :
       nonincreasing_seq u_ -> (forall n : nat, M <= u_ n) -> cvg u_.
Proof. exact: etnonincreasing_is_cvg. Qed.

Lemma cnonincreasing_cvg (u_ : C ^nat) (M : C) :
       nonincreasing_seq u_ -> (forall n : nat, M <= u_ n) -> 
        u_ --> (lim ((@Re _) \o u_))%:C + (Im M)%:Ci.
Proof.
move=>P1 P2. move: (cnonincreasing_is_cvg P1 P2)=>P3.
rewrite ccvg_limE; split=>//. rewrite clim_split//.
do 2 f_equal. suff ->: (Im (R:=R) \o u_) = (fun=>Im M) by apply: lim_cst.
by apply/funext=>i; move: (P2 i); rewrite/= lecE=>/andP[/eqP->].
Qed.

Lemma cnondecreasing_cvgn_le (u_ : C ^nat) :
       nondecreasing_seq u_ -> cvg u_ -> (forall n : nat, u_ n <= lim u_).
Proof. exact: etnondecreasing_cvgn_le. Qed.

Lemma cnonincreasing_cvg_ge (u_ : C ^nat) : 
  nonincreasing_seq u_ -> cvg u_ -> (forall n, lim u_ <= u_ n).
Proof. exact: etnonincreasing_cvg_ge. Qed.

Lemma cclosed_ge (y:C) : closed [set x : C | y <= x].
Proof. exact: etclosed_ge. Qed.

Lemma cclosed_le (y : C) : closed [set x : C | x <= y].
Proof. exact: etclosed_le. Qed.

Lemma cclosed_eq (y : C) : closed [set x : C | x = y].
Proof. exact: etclosed_eq. Qed.

Lemma clim_ge_near (x : C) (u : C ^nat) : 
  cvg u -> (\forall n \near \oo, x <= u n) -> x <= lim u.
Proof. exact: etlim_ge_near. Qed.

Lemma clim_le_near (x : C) (u : C ^nat) : 
  cvg u -> (\forall n \near \oo, x >= u n) -> x >= lim u.
Proof. exact: etlim_le_near. Qed.

Lemma lt_clim (u : C ^nat) (x : C) : nondecreasing_seq u -> cvg u -> x < lim u ->
  \forall n \near \oo, x <= u n.
Proof. exact: lt_etlim. Qed.

Lemma gt_clim (u : C ^nat) (x : C) : nonincreasing_seq u -> cvg u -> x > lim u ->
  \forall n \near \oo, x >= u n.
Proof. exact: gt_etlim. Qed.

Lemma ler_clim_near (u_ v_ : C ^nat) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, u_ n <= v_ n) -> lim u_ <= lim v_.
Proof. exact: ler_etlim_near. Qed.

Lemma clim_ge (x : C) (u : C ^nat) : cvg u -> (forall n, x <= u n) -> x <= lim u.
Proof. exact: etlim_ge. Qed.

Lemma clim_le (x : C) (u : C ^nat) : cvg u -> (forall n, u n <= x) -> lim u <= x.
Proof. exact: etlim_le. Qed.

Lemma ler_clim (u_ v_ : C^nat) : cvg u_ -> cvg v_ ->
  (forall n, u_ n <= v_ n) -> lim u_ <= lim v_.
Proof. exact: ler_etlim. Qed.

Lemma clim_eq_near (f g : C^nat) :
  cvg f -> (\forall n \near \oo, f n = g n) -> lim f = lim g.
Proof.
move=>/ccvg_limP cf [N _ Pn].
suff: g --> lim f by move/(cvg_lim (@Chausdorff _)).
apply/ccvg_limP=>e egt0.
move: (cf _ egt0)=>[M Pm].
exists (maxn N M)=>n Pnm.
rewrite -(Pn n)/=. apply: Pm. apply: (leq_trans _ Pnm). apply/leq_maxr.
apply: (leq_trans _ Pnm). apply/leq_maxl.
Qed.

End C_monotone.

Section C_sup.
Variable (R : realType).
Local Notation C := R[i].

Definition csup : set C -> C := nosimpl (@etsup R (C_extNumType R)).
Definition cinf : set C -> C := nosimpl (@etinf R (C_extNumType R)).

Lemma csup_adherent (E : set C) (eps : C) : 0 < eps ->
  has_sup E -> exists2 e : C, E e & (csup E - eps) < e.
Proof. exact: etsup_adherent. Qed. 

Lemma csup_upper_bound E : has_sup E -> ubound E (csup E).
Proof. exact: etsup_upper_bound. Qed.

Lemma csup_least_ubound E : has_sup E -> lbound (ubound E) (csup E).
Proof. exact: etsup_least_ubound. Qed.

End C_sup.

Section CmxCvg.
Variable (R: realType) (m n : nat).
Local Notation C := R[i].
Local Notation M := 'M[C]_(m,n).
Implicit Type (f g: nat -> M) (r: nat) (a b : M) (s : nat -> C) (k: C).

Lemma cmxhausdorff p q : hausdorff_space [topologicalType of 'M[C]_(p,q)].
Proof. exact: mxhausdorff. Qed.

Lemma cmxcvg_limE f a : f --> a <-> lim f = a /\ cvg f. Proof. exact: mxcvg_limE. Qed.
Lemma cmxcvg_lim f a : f --> a -> lim f = a. Proof. by move=>/cmxcvg_limE[]. Qed.
Lemma cmxcvg_cst a : (fun n:nat=>a) --> a. Proof. exact: cvg_cst. Qed.
Lemma is_cmxcvg_cst a : cvg (fun n:nat=>a). Proof. exact: is_mxcvg_cst. Qed.
Lemma cmxlim_cst a : lim (fun n:nat=>a) = a. Proof. exact: mxlim_cst. Qed.
Lemma cmxcvgN f a : f --> a -> (- f) --> - a. Proof. exact: mxcvgN. Qed.
Lemma is_cmxcvgN f : cvg f -> cvg (- f). Proof. by move=> /cmxcvgN /cvgP. Qed.
Lemma is_cmxcvgNE f : cvg (- f) = cvg f.
Proof. by rewrite propeqE; split=> /cmxcvgN; rewrite ?opprK => /cvgP. Qed.
Lemma cmxcvgMn f r a : f --> a -> ((@GRing.natmul _)^~r \o f) --> a *+ r.
Proof. exact: mxcvgMn. Qed.
Lemma is_cmxcvgMn f r : cvg f -> cvg ((@GRing.natmul _)^~r \o f).
Proof. by move=> /(@cmxcvgMn _ r) /cvgP. Qed.
Lemma cmxcvgD f g a b : f --> a -> g --> b -> (f + g) --> a + b.
Proof. exact: mxcvgD. Qed.
Lemma is_cmxcvgD f g : cvg f -> cvg g -> cvg (f + g).
Proof. by have := cvgP _ (cmxcvgD _ _); apply. Qed.
Lemma cmxcvgB f g a b : f --> a -> g --> b -> (f - g) --> a - b.
Proof. exact: mxcvgB. Qed.
Lemma is_cmxcvgB f g : cvg f -> cvg g -> cvg (f - g).
Proof. by have := cvgP _ (cmxcvgB _ _); apply. Qed.
Lemma is_cmxcvgDlE f g : cvg g -> cvg (f + g) = cvg f.
Proof.
move=> g_cvg; rewrite propeqE; split; last by move=> /is_cmxcvgD; apply.
by move=> /is_cmxcvgB /(_ g_cvg); rewrite addrK.
Qed.
Lemma is_cmxcvgDrE f g : cvg f -> cvg (f + g) = cvg g.
Proof. by rewrite addrC; apply: is_cmxcvgDlE. Qed.
Lemma cmxcvgZ s f k a : s --> k -> f --> a -> (fun x => s x *: f x) --> k *: a.
Proof. exact: mxcvgZ. Qed.
Lemma is_cmxcvgZ s f : cvg s -> cvg f -> cvg (fun x => s x *: f x).
Proof. by have := cvgP _ (cmxcvgZ _ _); apply. Qed.
Lemma cmxcvgZl s k a : s --> k -> (fun x => s x *: a) --> k *: a.
Proof. by move=> ?; apply: cmxcvgZ => //; exact: cmxcvg_cst. Qed.
Lemma is_cmxcvgZl s a : cvg s -> cvg (fun x => s x *: a).
Proof. by have := cvgP _ (cmxcvgZl  _); apply. Qed.
Lemma is_cmxcvgZlE s a : a != 0 -> cvg (fun x => s x *: a) = cvg s.
Proof. exact: is_mxcvgZlE. Qed.
Lemma cmxcvgZr k f a : f --> a -> k \*: f --> k *: a.
Proof. apply: cmxcvgZ => //; exact: ccvg_cst. Qed.
Lemma is_cmxcvgZr k f : cvg f -> cvg (k *: f ).
Proof. by have := cvgP _ (cmxcvgZr  _); apply. Qed.
Lemma is_cmxcvgZrE k f : k != 0 -> cvg (k *: f) = cvg f.
Proof.
move=> k_neq0; rewrite propeqE; split=>[/(@cmxcvgZr k^-1)|/(@cmxcvgZr k)/cvgP//].
by under [_ \*: _]funext => x /= do rewrite scalerK//; apply: cvgP.
Qed.

Lemma cmxlimN f : cvg f -> lim (- f) = - lim f.
Proof. by move=>?; apply/cmxcvg_lim/cmxcvgN. Qed.  
Lemma cmxlimD f g : cvg f -> cvg g -> lim (f + g) = lim f + lim g.
Proof. by move=>Pf Pg; apply/cmxcvg_lim/cmxcvgD; [apply Pf|apply Pg]. Qed.
Lemma cmxlimB f g : cvg f -> cvg g -> lim (f - g) = lim f - lim g.
Proof. move=> Pf Pg; apply/cmxcvg_lim/cmxcvgB; [apply Pf|apply Pg]. Qed.
Lemma cmxlimZ s f : cvg s -> cvg f -> lim (fun x => s x *: f x) = lim s *: lim f.
Proof. move=> Ps Pf; apply/cmxcvg_lim/cmxcvgZ;[apply Ps|apply Pf]. Qed.
Lemma cmxlimZl s a : cvg s -> lim (fun x => s x *: a) = lim s *: a.
Proof. by move=> ?; apply/cmxcvg_lim/cmxcvgZl. Qed.
Lemma cmxlimZr k f : cvg f -> lim (k *: f) = k *: lim f.
Proof. by move=> ?; apply/cmxcvg_lim/mxcvgZr. Qed.

(* since only nontrivial matrix are canonical to normZmodType *)
Lemma cmxcvg_norm (h : nat->'M[C]_(m.+1,n.+1)) (x : 'M[C]_(m.+1,n.+1)) : 
  h --> x -> (Num.norm \o h) --> `|x|.
Proof. exact: cvg_norm. Qed.
Lemma is_cmxcvg_norm (h : nat->'M[C]_(m.+1,n.+1)) : 
  cvg h -> cvg (Num.norm \o h).
Proof. exact: is_cvg_norm. Qed.
Lemma cmxlim_norm (h : nat->'M[C]_(m.+1,n.+1)) : 
  cvg h -> lim (Num.norm \o h) = `|lim h|.
Proof. exact: lim_norm. Qed.

Lemma cmxcvg_map f a (V : completeType) (h : M -> V) :
  continuous h -> f --> a -> (h \o f) --> h a.
Proof. exact: mxcvg_map. Qed.
Lemma cmxcvg_mapV (V : completeType) (h : V -> M) (h' : nat -> V) (a : V) :
  continuous h -> h' --> a -> (h \o h') --> h a.
Proof. exact: mxcvg_mapV. Qed.
Lemma is_cmxcvg_map f (V : completeType) (h : M -> V) :
  continuous h -> cvg f -> cvg (h \o f).
Proof. exact: is_mxcvg_map. Qed.
Lemma is_cmxcvg_mapV (V : completeType) (h : V -> M) (h' : nat -> V) :
  continuous h -> cvg h' -> cvg (h \o h').
Proof. exact: is_mxcvg_mapV. Qed.
Lemma cmxlim_map f a (V : completeType) (h : M -> V) :
  hausdorff_space V -> continuous h -> cvg f -> lim (h \o f) = h (lim f).
Proof. exact: mxlim_map. Qed.
Lemma cmxlim_mapV (V : completeType) (h : V -> M) (h' : nat -> V) :
  continuous h -> cvg h' -> lim (h \o h') = h (lim h').
Proof. exact: mxlim_mapV. Qed.

Lemma cmxcvg_limP p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) :
  h --> x <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> mx_norm (h n - x) < e.
Proof. exact: mxcvg_limP. Qed.
Lemma cmxcvg_subseqP p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) : 
  h --> x <-> (forall (h': nat -> nat), (forall n, (h' n.+1 > h' n)%N) -> (h \o h') --> x).
Proof. exact: mxcvg_subseqP. Qed.
Lemma cmxcvg_subseqPN p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) :
  ~ (h --> x) <-> exists e (h': nat -> nat), 
    (forall n, (h' n.+1 > h' n)%N) /\ 0 < e /\ (forall n, mx_norm ((h \o h') n - x) >= e).
Proof. exact: mxcvg_subseqPN. Qed.

Lemma cmxnatmul_continuous p : continuous (fun x : M => x *+ p).
Proof. exact: mxnatmul_continuous. Qed.
Lemma cmxscale_continuous : continuous (fun z : C * M => z.1 *: z.2).
Proof. exact: mxscale_continuous. Qed.
Lemma cmxscaler_continuous k : continuous (fun x : M => k *: x).
Proof. exact: mxscaler_continuous. Qed.
Lemma cmxscalel_continuous (x : M) : continuous (fun k : C => k *: x).
Proof. exact: mxscalel_continuous. Qed.
Lemma cmxopp_continuous : continuous (fun x : M => -x).
Proof. exact: mxopp_continuous. Qed.
Lemma cmxadd_continuous : continuous (fun z : M * M => z.1 + z.2).
Proof. exact: mxadd_continuous. Qed.
Lemma cmxaddr_continuous a : continuous (fun z : M => a + z).
Proof. exact: mxaddr_continuous. Qed.
Lemma cmxaddl_continuous a : continuous (fun z : M => z + a).
Proof. exact: mxaddl_continuous. Qed.

Definition cmxcauchy_seq f := 
  forall e, 0 < e -> exists N, forall i j, 
  (N <= i)%N -> (N <= j)%N -> mx_norm (f i - f j) < e.

Definition cmxcvg_seq f a := 
  forall e, 0 < e -> exists N : nat, 
    forall i, (N <= i)%N -> mx_norm (a - f i) < e.

Lemma cmxcauchy_seqP f : cmxcauchy_seq f <-> cvg f.
Proof. exact: mxcauchy_seqP. Qed.
Lemma cmxcvg_seqP f a : cmxcvg_seq f a <-> f --> a.
Proof. exact: mxcvg_seqP. Qed.

End CmxCvg.

Section CmxLinearContinuous.
Variable (R: realType).
Local Notation C := R[i].

Lemma cmxlinear_continuous m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q)) :
  linear f -> continuous f.
Proof. exact: mxlinear_continuous. Qed.

Lemma cmxcvg_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) : 
  linear f -> u --> a -> (fun x=> f (u x)) --> (f a).
Proof. exact: mxcvg_lfun. Qed.

Lemma is_cmxcvg_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
(u : nat -> 'M[C]_(m,n))  : linear f -> cvg u -> cvg (f \o u).
Proof. by move=>P1; have := cvgP _ (cmxcvg_lfun P1 _); apply. Qed.

Lemma cmxlim_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (u : nat -> 'M[C]_(m,n)) : 
  linear f -> cvg u -> lim (f \o u) = f (lim u).
Proof. by move=>P1 ?; apply/cmxcvg_lim/cmxcvg_lfun. Qed.

Lemma cmxclosed_comp m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
(A : set 'M[C]_(p,q)) :
  linear f -> closed A -> closed (f @^-1` A).
Proof. exact: mxclosed_comp. Qed.

Lemma cmxopen_comp m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (A : set 'M[C]_(p,q)) :
  linear f -> open A -> open (f @^-1` A).
Proof. exact: mxopen_comp. Qed.

Lemma cmxscalar_continuous m n (f : 'M[C]_(m,n) -> C) :
  scalar f -> continuous f.
Proof. exact: mxscalar_continuous. Qed.

Lemma cmxcvg_sfun m n (f : 'M[C]_(m,n) -> C)
  (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) : 
  scalar f -> u --> a -> (fun x=> f (u x)) --> (f a).
Proof. exact: mxcvg_sfun. Qed.

Lemma is_cmxcvg_sfun m n (f : 'M[C]_(m,n) -> C) (u : nat -> 'M[C]_(m,n)) : 
  scalar f -> cvg u -> cvg (f \o u).
Proof. by move=>P1; have := cvgP _ (cmxcvg_sfun P1 _); apply. Qed.

Lemma cmxlim_sfun m n (f : 'M[C]_(m,n) -> C) (u : nat -> 'M[C]_(m,n)) : 
  scalar f -> cvg u -> lim (f \o u) = f (lim u).
Proof. by move=>P1 ?; apply: cvg_lim=>//; apply: cmxcvg_sfun. Qed.

Lemma cmxcclosed_comp m n (f : 'M[C]_(m,n) -> C) (A : set C) :
  scalar f -> closed A -> closed (f @^-1` A).
Proof. exact: mxcclosed_comp. Qed.

Lemma cmxcopen_comp m n (f : 'M[C]_(m,n) -> C) (A : set C) :
  scalar f -> open A -> open (f @^-1` A).
Proof. exact: mxcopen_comp. Qed.

End CmxLinearContinuous.

Section CmxNormExtNumEqual.
Variable (R: realType) (m n : nat).
Local Notation C := R[i].
Local Notation M := 'M[C]_(m,n).
Implicit Type (mnorm : vnorm [lmodType C of M]).

Lemma cmxlim_mnorm mnorm (f : M ^nat) : 
  cvg f -> lim (mnorm \o f) = mnorm (lim f).
Proof. exact: mxlim_mnorm. Qed.

Lemma mnorm_lbounded mnorm : exists2 c : C, 
  0 < c & forall x,  c * mx_norm x <= mnorm x.
Proof. exact: mnorm_lbounded. Qed.

Lemma compact_mnorm_le mnorm (y : C) : compact [set x : M | mnorm x <= y].
Proof. exact: compact_mnorm_le. Qed.

Lemma compact_mnorm_sphere mnorm (y : C) : compact [set x : M | mnorm x = y].
Proof. exact: compact_mnorm_sphere. Qed.

Lemma cmx_Bolzano_Weierstrass (f : nat -> 'M[C]_(m,n)) (M : C) :
  (forall n, mx_norm (f n) <= M) -> exists (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ cvg (f \o h).
Proof. exact: Bolzano_Weierstrass. Qed.

(* bounded seq: cvg <-> any cvg subseq to a *)
Lemma cmxcvg_subseqP_cvg (f : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) (M : C): 
  (forall n, mx_norm (f n) <= M) ->
  f --> a <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N) 
    -> cvg (f \o h) -> lim (f \o h) = a).
Proof. exact: mxcvg_subseqP_cvg. Qed.

Lemma mnorm_bounded mnorm1 mnorm2 :
  exists2 c : C, 0 < c & forall x : M, mnorm1 x <= c * mnorm2 x.
Proof. exact: mnorm_bounded. Qed.

Lemma cmxcauchy_seqv_eq mnorm1 mnorm2 (f : nat -> M) :
  cauchy_seqv mnorm1 f -> cauchy_seqv mnorm2 f.
Proof. exact: mxcauchy_seqv_eq. Qed.

Lemma cmxcauchy_seqvE mnorm1 mnorm2 (f : nat -> M) :
  cauchy_seqv mnorm1 f <-> cauchy_seqv mnorm2 f.
Proof. exact: mxcauchy_seqvE. Qed.

Lemma cmxcauchy_seqE mnorm (f : nat -> M) :
  cauchy_seqv mnorm f <-> mxcauchy_seq f.
Proof. exact: mxcauchy_seqE. Qed.

Lemma cmxcauchy_seqvP mnorm (f : nat -> M) :
  cauchy_seqv mnorm f <-> cvg f.
Proof. exact: mxcauchy_seqvP. Qed.

End CmxNormExtNumEqual.

(* FinNormedModType *)
(* VOrderFinNormedModType *)
Module FinNormedModule.

Section ClassDef.
Variable R : realType.

Record class_of (T : Type) := Class {
  base : NormedModule.class_of [numFieldType of R[i]] T ;
  mixin : Vector.mixin_of (GRing.Lmodule.Pack _ base);
}.
Local Coercion base : class_of >-> NormedModule.class_of.
Definition base2 T (cT : class_of T) := @Vector.Class _ _ (@base T cT) (@mixin T cT).
Local Coercion base2 : class_of >-> Vector.class_of.

Structure type (phR : phant R[i]) := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R[i]) (T : Type) (cT : type phR).
Definition class := let: Pack _ c  as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT (b : NormedModule.class_of _ T) & phant_id (@NormedModule.class _ (Phant R[i]) bT) b =>
  fun mT m & phant_id (@Vector.class _ (Phant R[i]) mT) (@Vector.Class _ T b m) =>
    @Pack phR T (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack _ phR cT xclass.
Definition lmodType := @GRing.Lmodule.Pack _ phR cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack _ cT xclass.
Definition pseudoMetricNormedZmodType :=
  @PseudoMetricNormedZmodule.Pack _ phR cT xclass.
Definition normedModType := @NormedModule.Pack _ phR cT xclass.
Definition vectType := @Vector.Pack _ phR cT xclass.
Definition normedMod_zmodType := @GRing.Zmodule.Pack normedModType xclass.
Definition normedMod_lmodType := @GRing.Lmodule.Pack _ phR normedModType xclass.
Definition normedMod_vectType := @Vector.Pack _ phR normedModType xclass.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> NormedModule.class_of.
Coercion base2 : class_of >-> Vector.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion pseudoMetricNormedZmodType : type >-> PseudoMetricNormedZmodule.type.
Canonical pseudoMetricNormedZmodType.
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Coercion normedModType : type >-> NormedModule.type.
Canonical normedModType.
Coercion vectType : type >-> Vector.type.
Canonical vectType.
Canonical normedMod_zmodType.
Canonical normedMod_lmodType.
Canonical normedMod_vectType.
Notation finNormedModType R := (type (Phant R)).
Notation FinNormedModType R T := (@pack _ (Phant R) T _ _ id _ _ id).
Notation "[ 'finNormedModType' R 'of' T 'for' cT ]" :=  (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'finNormedModType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'finNormedModType' R 'of' T ]" :=  (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'finNormedModType'  R  'of'  T ]") : form_scope.
End Exports.

End FinNormedModule.

Export FinNormedModule.Exports.

Module VOrderFinNormedModule.

Section ClassDef.

Record mixin_of (R : realType) (V : finNormedModType R[i])
  (Rorder : POrder.mixin_of (Equality.class V))
  (le_op := POrder.le Rorder)
  := Mixin {
  _ : closed [set x : V | (le_op 0 x)] ;
}.

Variable R : realType.

Record class_of (T : Type) := Class {
  base : FinNormedModule.class_of R T;
  order_mixin : POrder.mixin_of (Equality.class (FinNormedModule.Pack _ base));
  vorder_mixin : VOrder.mixin_of order_mixin;
  mixin : mixin_of order_mixin;
}.
Local Coercion base : class_of >-> FinNormedModule.class_of.
Definition vorder_base T (cT : class_of T) :=
  @VOrder.Class _ _ (@base T cT) (order_mixin cT) (vorder_mixin cT).
Local Coercion vorder_base : class_of >-> VOrder.class_of.

Structure type (phR : phant R[i]) := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R[i]) (T : Type) (cT : type phR).
Definition class := let: Pack _ c  as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack (b0 : FinNormedModule.class_of R T)
           (om0 : POrder.mixin_of (Equality.class (FinNormedModule.Pack (Phant R[i]) b0)))
           (m0 : @mixin_of R (@FinNormedModule.Pack R (Phant R[i]) T b0) om0) :=
  fun bT (b : FinNormedModule.class_of R T)
      & phant_id (@FinNormedModule.class R (Phant R[i]) bT) b =>
  fun om & phant_id om0 om =>
  fun vmT vm & phant_id (@VOrder.class _ (Phant R[i]) vmT) (@VOrder.Class _ T b om vm) =>
  fun m & phant_id m0 m =>
  @Pack phR T (@Class T b om vm m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack _ phR cT xclass.
Definition lmodType := @GRing.Lmodule.Pack _ phR cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack _ cT xclass.
Definition pseudoMetricNormedZmodType :=
  @PseudoMetricNormedZmodule.Pack _ phR cT xclass.
Definition normedModType := @NormedModule.Pack _ phR cT xclass.
Definition finNormedModType := @FinNormedModule.Pack _ phR cT xclass.
Definition vectType := @Vector.Pack _ phR cT xclass.
Definition porderType := @POrder.Pack vorder_display cT xclass.
Definition vorderType := @VOrder.Pack _ phR cT xclass.
Definition finNormedMod_zmodType := @GRing.Zmodule.Pack finNormedModType xclass.
Definition finNormedMod_lmodType := @GRing.Lmodule.Pack _ phR finNormedModType xclass.
Definition finNormedMod_vectType := @Vector.Pack _ phR finNormedModType xclass.
Definition finNormedMod_porderType := @POrder.Pack vorder_display finNormedModType xclass.
Definition finNormedMod_vorderType := @VOrder.Pack _ phR finNormedModType xclass.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> FinNormedModule.class_of.
Coercion vorder_base : class_of >-> VOrder.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion pseudoMetricNormedZmodType : type >-> PseudoMetricNormedZmodule.type.
Canonical pseudoMetricNormedZmodType.
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Coercion normedModType : type >-> NormedModule.type.
Canonical normedModType.
Coercion finNormedModType : type >-> FinNormedModule.type.
Canonical finNormedModType.
Coercion vectType : type >-> Vector.type.
Canonical vectType.
Coercion porderType : type >-> POrder.type.
Canonical porderType.
Coercion vorderType : type >-> VOrder.type.
Canonical vorderType.
Canonical finNormedMod_zmodType.
Canonical finNormedMod_lmodType.
Canonical finNormedMod_vectType.
Canonical finNormedMod_porderType.
Canonical finNormedMod_vorderType.
Notation vorderFinNormedModType R := (type (Phant R)).
Notation VOrderFinNormedModType R T m := 
  (@pack _ (Phant R) T _ _ m _ _ id _ id _ _ id _ id).
Notation VOrderFinNormedModMixin := Mixin.
Notation "[ 'vorderFinNormedModType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'vorderFinNormedModType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'vorderFinNormedModType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'vorderFinNormedModType'  R  'of'  T ]") : form_scope.
End Exports.

End VOrderFinNormedModule.

Export VOrderFinNormedModule.Exports.


Section C_vorderFinNormedModType.
Variable (R : realType).
Local Notation C := R[i].

Canonical C_regular_finNormedModType := Eval hnf in (FinNormedModType C C^o).
Canonical C_finNormedModType :=
  Eval hnf in [finNormedModType C of C for [finNormedModType C of C^o]].

Program Canonical C_vorderMixin := @VOrderMixin _ _ 
  (Order.POrder.class [porderType of [lmodType C of C^o]]) _ _.
Next Obligation.
move=>z x y Pxy; suff: x + z <= y + z by [].
by rewrite Num.Theory.lerD2r.
Qed.
Next Obligation.
move=>e x y egt0 Pxy; suff: e * x <= e * y by [].
by rewrite Num.Theory.ler_pM2l.
Qed.

Canonical C_vorderType := 
  Eval hnf in [vorderType C of C for (VOrderType C C^o C_vorderMixin)].

Lemma levcE (x y : C) : ((x : [vorderType C of C]) ⊑ y) = (x <= y).
Proof. by []. Qed.
Lemma ltvcE (x y : C) : ((x : [vorderType C of C]) ⊏ y) = (x < y).
Proof. by []. Qed.

Definition C_vorderFinNormedModMixin := VOrderFinNormedModMixin (@cclosed_ge _ 0).
Canonical C_vorderFinNormedModType := VOrderFinNormedModType C C C_vorderFinNormedModMixin.

End C_vorderFinNormedModType.

Section FinNormedModTypeComplete.
Context {R : realType} {V : finNormedModType R[i]}.
Local Notation C := R[i].
Import Vector.InternalTheory Num.Def Num.Theory numFieldNormedType.Exports.

Lemma bounded_normr_mxnorm m n (f: V -> 'M[C]_(m,n)) (lf: linear f) (bf: bijective f) :
  (exists c, c > 0 /\ forall x : V, `|x| <= c * mx_norm (f x))
  /\ (exists c, c > 0 /\ forall x : V, mx_norm (f x) <= c * `|x|).
Proof.
move: bf=>[g fK gK]; move: (can2_linearP lf fK gK)=>lg.
pose mn x := `|g x|.
have meq0 : forall x, mn x = 0 -> x = 0.
  by move=>x/normr0_eq0; rewrite -{2}(gK x)/==>->; rewrite (linearlfE lf) linear0.
have mtrg : forall x y, mn (x + y) <= mn x + mn y.
  by move=>x y; rewrite /mn (linearlfE lg) linearD ler_normD.
have mZ : forall (a: C) (x : 'M_(m,n)), mn (a *: x) = `|a| * mn x.
  by move=>a x; rewrite /mn (linearlfE lg) linearZ normrZ.
pose mvn := Vnorm mtrg meq0 mZ.
have x2m : forall x, `|x| = mn (f x) by move=>x; rewrite /mn fK.
split. move: (mnorm_bounded mvn (@mx_norm_vnorm _ _ _))=>[c /= cgt0 Pml].
2: move: (mnorm_bounded (@mx_norm_vnorm _ _ _) mvn)=>[c /= cgt0 Pml].
all: exists c; split=>// x; by rewrite x2m.
Qed.

Lemma bounded_mxnorm_normr (m n: nat) (g: 'M[C]_(m,n) -> V) (lg: linear g) (bg: bijective g) :
  (exists c, c > 0 /\ forall x : 'M[C]_(m,n), mx_norm x <= c * `|g x|)
  /\ (exists c, c > 0 /\ forall x : 'M[C]_(m,n), `|g x| <= c * mx_norm x).
Proof.
move: bg=>[f gK fK]. move: (bounded_normr_mxnorm (can2_linearP lg gK fK) 
  (can2_bij gK fK))=>[[c1 [c1gt0 Pc1]] [c2 [c2gt0 Pc2]]].
split. exists c2; split=>// x; by rewrite -{1}(gK x).
exists c1; split=>// x; by rewrite -{2}(gK x).
Qed.

Lemma bijective_to_mx_continuous (m n: nat) (f: V -> 'M[C]_(m,n)) 
  (lf: linear f) (bf: bijective f) : continuous f.
Proof.
case: m f lf bf=>[f _ _|]; last case: n=>[m f _ _|m n f lf bf].
1,2: by rewrite mx_dim0=>x; apply: cst_continuous.
rewrite (linearlfE lf) -linear_bounded_continuous -bounded_funP=>r/=.
move: (bounded_normr_mxnorm lf bf)=>[_ [c2 [c2gt0 Pc2]]].
exists (c2 * r)=>x. rewrite -(ler_pM2l c2gt0) {2}/normr/=.
apply (le_trans (Pc2 _)).
Qed.

Lemma bijective_of_mx_continuous (m n: nat) (g: 'M[C]_(m,n) -> V) 
  (lg: linear g) (bg: bijective g) : continuous g.
Proof.
case: m g lg bg=>[g _ _|]; last case: n=>[m g _ _|m n g lg bg].
1,2: by apply: cst_continuous_eq; exists (g 0); apply/funext=>i; rewrite mx_dim0.
rewrite (linearlfE lg) -linear_bounded_continuous -bounded_funP=>r/=.
move: (bounded_mxnorm_normr lg bg)=>[_ [c2 [c2gt0 Pc2]]].
exists (c2 * r)=>x. rewrite -(ler_pM2l c2gt0) {1}/normr/=.
apply (le_trans (Pc2 _)).
Qed.

Lemma bijective_to_mx_cvgE (m n: nat) (f: V -> 'M[C]_(m,n)) (u : nat -> V) 
  (a : V) (lf: linear f) (bf: bijective f) :
  u --> a = ((f \o u)%FUN --> f a).
Proof.
rewrite propeqE; split; last move: {+}bf=>[g fK gK].
by apply: continuous_cvg; apply/(bijective_to_mx_continuous lf bf).
have P: u = (g \o (f \o u))%FUN by apply/funext=>i/=; rewrite fK.
have P1: a = g (f a) by rewrite fK. 
rewrite [in X in _ -> X]P [in X in _ -> X]P1; apply: continuous_cvg. 
apply (bijective_of_mx_continuous (can2_linearP lf fK gK) (can2_bij fK gK)).
Qed.

Lemma bijective_of_mx_cvgE (m n: nat) (f: 'M[C]_(m,n) -> V) 
  (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) (lf: linear f) (bf: bijective f) :
  u --> a = ((f \o u)%FUN --> f a).
Proof.
rewrite propeqE; split; last move: {+}bf=>[g fK gK].
by apply: continuous_cvg; apply/(bijective_of_mx_continuous lf bf).
have P: u = (g \o (f \o u))%FUN by apply/funext=>i/=; rewrite fK.
have P1: a = g (f a) by rewrite fK. 
rewrite [in X in _ -> X]P [in X in _ -> X]P1; apply: continuous_cvg. 
apply (bijective_to_mx_continuous (can2_linearP lf fK gK) (can2_bij fK gK)).
Qed.

Lemma bijective_to_mx_is_cvgE (m n: nat) (f: V -> 'M[C]_(m,n)) (u : nat -> V)
  (lf: linear f) (bf: bijective f) : cvg u = cvg (f \o u)%FUN.
Proof.
rewrite propeqE; split; move=>/cvg_ex[a Pa]; apply/cvg_ex.
exists (f a); by rewrite -bijective_to_mx_cvgE.
move: {+}bf=>[g fK gK]; exists (g a); move: Pa.
have P1: a = f (g a) by [].
by rewrite [in X in X -> _]P1 -bijective_to_mx_cvgE.
Qed.

Lemma bijective_of_mx_is_cvgE (m n: nat) (f: 'M[C]_(m,n) -> V) 
  (u : nat -> 'M[C]_(m,n)) (lf: linear f) (bf: bijective f) :
  cvg u = cvg (f \o u)%FUN.
Proof.
rewrite propeqE; split; move/cvg_ex=>[a Pa]; apply/cvg_ex.
exists (f a); by rewrite -bijective_of_mx_cvgE.
move: {+}bf=>[g fK gK]; exists (g a); move: Pa.
have P1: a = f (g a) by []. 
by rewrite [in X in X -> _]P1 -bijective_of_mx_cvgE.
Qed.

Lemma bijective_to_mx_limE (m n: nat) (f: V -> 'M[C]_(m,n)) (u : nat -> V)
  (lf: linear f) (bf: bijective f) :
  cvg u -> lim (f \o u)%FUN = f (lim u).
Proof.
move=>?; apply: cvg_lim; first by apply: mxhausdorff.
by rewrite -bijective_to_mx_cvgE.
Qed.

Lemma bijective_of_mx_limE (m n: nat) (f: 'M[C]_(m,n) -> V) 
  (u : nat -> 'M[C]_(m,n)) (lf: linear f) (bf: bijective f) :
  cvg u -> lim (f \o u)%FUN = f (lim u).
Proof.
move=> ?; apply: cvg_lim; first by apply: norm_hausdorff.
by rewrite -bijective_of_mx_cvgE.
Qed.

Local Notation MV := 'rV[C]_(Vector.dim V).

Lemma v2r_continuous : continuous (@v2r _ V).
Proof. apply: (bijective_to_mx_continuous _ v2r_bij); exact: linearP. Qed.

Lemma r2v_continuous : continuous (@r2v _ V).
Proof. apply: (bijective_of_mx_continuous _ r2v_bij); exact: linearP. Qed.

Lemma v2r_cvgE (u : nat -> V) (a : V): u --> a = ((v2r \o u)%FUN --> v2r a).
Proof. apply: (bijective_to_mx_cvgE _ _ _ v2r_bij); exact: linearP. Qed.

Lemma r2v_cvgE (u : nat -> MV) (a : MV) : u --> a = ((r2v \o u)%FUN --> r2v a).
Proof. apply: (bijective_of_mx_cvgE _ _ _ r2v_bij); exact: linearP. Qed.

Lemma v2r_is_cvgE (u : nat -> V) : cvg u = cvg (v2r \o u)%FUN.
Proof. apply: (bijective_to_mx_is_cvgE _ _ v2r_bij); exact: linearP. Qed.

Lemma r2v_is_cvgE (u : nat -> MV) : cvg u = cvg (r2v \o u)%FUN.
Proof. apply: (bijective_of_mx_is_cvgE _ _ r2v_bij). exact: linearP. Qed.

Lemma v2r_limE (u : nat -> V) : cvg u -> lim (v2r \o u)%FUN = v2r (lim u).
Proof. apply: (bijective_to_mx_limE _ v2r_bij); exact: linearP. Qed.

Lemma r2v_limE (u : nat -> MV) : cvg u -> lim (r2v \o u)%FUN = r2v (lim u).
Proof. apply: (bijective_of_mx_limE _ r2v_bij); exact: linearP. Qed.

Canonical finNormedMod_vnorm := Vnorm (@ler_normD _ V) (@normr0_eq0 _ V) (@normrZ _ V).

(* vnorm V transform to vnorm of matrix *)
Program Definition v2r_vnorm (f : vnorm V) := @VNorm.Vnorm _ _ (fun x=>f (r2v x)) _ _ _.
Next Obligation. 
by move=>f x y /=; rewrite linearD/= lev_normD.
Qed.
Next Obligation.
by move=>f x /= /normv0_eq0; rewrite -{2}(r2vK x)=>->; rewrite linear0.
Qed.
Next Obligation.
by move=>f a x/=; rewrite !linearZ/= normvZ.
Qed.

Program Definition r2v_vnorm (f : vnorm _) := @VNorm.Vnorm _ V (fun x=>f (v2r x)) _ _ _.
Next Obligation.
by move=>f x y /=; rewrite linearD/= lev_normD.
Qed.
Next Obligation.
by move=>f x /= /normv0_eq0; rewrite -{2}(v2rK x)=>->; rewrite linear0.
Qed.
Next Obligation.
by move=>f a x/=; rewrite !linearZ/= normvZ.
Qed.

Lemma r2vK_vnorm (f : vnorm _) x : v2r_vnorm (r2v_vnorm f) x = f x.
Proof. by rewrite /= r2vK. Qed.
Lemma v2rK_vnorm (f : vnorm V) x : r2v_vnorm (v2r_vnorm f) x = f x.
Proof. by rewrite /= v2rK. Qed.
Lemma r2v_vnormE (f : vnorm _) x : f x = r2v_vnorm f (r2v x).
Proof. by rewrite /= r2vK. Qed.
Lemma v2r_vnormE (f : vnorm V) x : f x = v2r_vnorm f (v2r x).
Proof. by rewrite /= v2rK. Qed.

Lemma compact_norm_le (e : C) : compact [set x : V | `|x| <= e].
Proof.
rewrite (_ : mkset _ = r2v @` [set x | v2r_vnorm finNormedMod_vnorm x <= e]).
apply: continuous_compact; last by apply: compact_mnorm_le.
apply: continuous_subspaceT=>x ?; apply: r2v_continuous.
rewrite predeqE=>/=x; split=>[Px|[y Py1 <-//]].
by exists (v2r x); rewrite/= v2rK.
Qed.

Lemma V_complete (F : set (set V)) :
  ProperFilter F -> cauchy F -> cvg F.
Proof. by apply: bounded_compact_complete; apply: compact_norm_le. Qed.

End FinNormedModTypeComplete.

Arguments bijective_to_mx_cvgE [R V m n f u a].
Arguments bijective_of_mx_cvgE [R V m n f u a].
Arguments bijective_to_mx_is_cvgE [R V m n f u].
Arguments bijective_of_mx_is_cvgE [R V m n f u].
Arguments bijective_to_mx_limE [R V m n f u].
Arguments bijective_of_mx_limE [R V m n f u].

Canonical finNormedMod_completeType (R : realType) (V : finNormedModType R[i]) 
  := CompleteType V (@V_complete _ V).
Canonical finNormedMod_CompleteNormedModule (R : realType) (V : finNormedModType R[i]) 
  := Eval hnf in [completeNormedModType R[i] of V].
Canonical vorderFinNormedMod_completeType (R : realType)
  (V : vorderFinNormedModType R[i]) := CompleteType V (@V_complete _ V).
Canonical vorderFinNormedMod_CompleteNormedModule (R : realType) 
  (V : vorderFinNormedModType R[i]) := 
  Eval hnf in [completeNormedModType R[i] of V].

Section FinNormedModTheory.
Context {R : realType} {V : finNormedModType R[i]}.
Local Notation C := R[i].
Import Num.Def Num.Theory Vector.InternalTheory.
Implicit Type (f g: nat -> V) (n: nat) (s a b : V).

Lemma Vhausdorff : hausdorff_space V.
Proof. exact: norm_hausdorff. Qed.

Lemma vcvg_limE f a : f --> a <-> lim f = a /\ cvg f.
Proof. exact: (cvg_limE f a Vhausdorff). Qed.

Lemma vcvg_map f a (U : completeType) (h : V -> U) :
  continuous h -> f --> a -> (h \o f) --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ [filter of f] a h).
by apply ch. by apply cvgf.
Qed.

Lemma vcvg_mapV (U : completeType) (h : U -> V) (h' : nat -> U) (a : U) :
  continuous h -> h' --> a -> (h \o h') --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ [filter of h'] a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_vcvg_map f (U : completeType) (h : V -> U) :
  continuous h -> cvg f -> cvg (h \o f).
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (vcvg_map P1 Pa).
Qed.

Lemma is_vcvg_mapV (U : completeType) (h : U -> V) (h' : nat -> U) :
  continuous h -> cvg h' -> cvg (h \o h').
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (vcvg_mapV P1 Pa).
Qed.

Lemma vlim_map f a (U : completeType) (h : V -> U) :
  hausdorff_space U -> continuous h -> cvg f -> lim (h \o f) = h (lim f).
Proof. by move=>hV ch; move/(vcvg_map ch)/cvg_lim=>/(_ hV). Qed.

Lemma vlim_mapV (U : completeType) (h : U -> V) (h' : nat -> U) :
  continuous h -> cvg h' -> lim (h \o h') = h (lim h').
Proof. by move=>ch; move/(vcvg_mapV ch)/cvg_lim=>/(_ Vhausdorff). Qed.

Lemma vcvg_limP f a :
  f --> a <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> `|f n - a| < e.
Proof. exact: cvg_limP. Qed.

Lemma vcvg_subseqP f a : 
  f --> a <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N) -> (f \o h) --> a).
Proof. exact: cvg_subseqP. Qed.

Lemma vcvg_subseqPN f a :
  ~ (f --> a) <-> exists e (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ 0 < e /\ (forall n, `|(f \o h) n - a| >= e).
Proof. exact: cvg_subseqPN. Qed.

(* equivalence of vnorm of V *)
(* linear continuous *)
Lemma normv_bounded (f g : vnorm V):
  exists2 c : C, 0 < c & forall x, f x <= c * g x.
Proof.
move: (mnorm_bounded (v2r_vnorm f) (v2r_vnorm g))=>[c cgt0 Pc].
exists c=>// x; by rewrite !v2r_vnormE.
Qed.

Lemma normv_ubounded (f : vnorm V) : 
  exists2 c, 0 < c & forall x, f x <= c * `| x |.
Proof. exact: normv_bounded. Qed.

Lemma normv_lbounded (f : vnorm V) : 
  exists2 c, 0 < c & forall x, c * `| x | <= f x.
Proof.
move: (normv_bounded finNormedMod_vnorm f)=>[c cgt0 Pc].
by exists (c^-1)=>[|x]; rewrite ?ler_pdivrMl// ?Pc// invr_gt0.
Qed.

Lemma cauchy_seqv_defaultE f :
  cauchy_seqv finNormedMod_vnorm f <-> cauchy_seq f.
Proof. by []. Qed.

Lemma cauchy_seqv_eq (nv1 nv2 : vnorm V) f :
  cauchy_seqv nv1 f <-> cauchy_seqv nv2 f.
split.
move: (normv_bounded nv2 nv1). 2: move: (normv_bounded nv1 nv2).
all: move=> [c Pc le_mn] P e Pe.
all: have Pec: 0 < (e / c) by apply divr_gt0.
all: move: (P (e/c) Pec )=>[N PN]; exists N=>s t Ps Pt.
all: apply: (le_lt_trans (le_mn (f s - f t))).
all: by rewrite -ltr_pdivlMl// mulrC PN.
Qed.

Lemma cauchy_seqv_cvg (nv : vnorm V) f :
  cauchy_seqv nv f <-> cvg f.
Proof.
rewrite (@cauchy_seqv_eq _ finNormedMod_vnorm).
exact: cauchy_seqP.
Qed.

Lemma normv_continuous (nv : vnorm V) : continuous nv.
Proof.
suff <-: (v2r_vnorm nv) \o v2r = nv.
apply: continuous_comp_simp. apply: v2r_continuous.
apply: continuous_mnorm.
by apply/funext=>x /=; rewrite v2rK.
Qed.

Context {T : Type} (F : set (set T)) {FF : ProperFilter F}.
Variable (nv : vnorm V).
Implicit Type (h : T -> V) (v : V).

Lemma cvg_normv h v : h @ F --> v -> nv (h x) @[x --> F] --> nv v.
Proof. by apply: continuous_cvg; apply: normv_continuous. Qed.

Lemma is_cvg_normv h : cvg (h @ F) -> cvg ((nv \o h : T -> C) @ F).
Proof. by have := cvgP _ (cvg_normv _); apply. Qed.

Lemma lim_normv h : cvg (h @ F) -> lim ((fun x => nv (h x)) @ F) = nv (lim (h @ F)).
Proof. by move=> ?; apply: cvg_lim => //; apply: cvg_normv. Qed.

End FinNormedModTheory.

Section LinearContinuous.
Context {R : realType}.
Variable (T : Type) (F : set (set T)).
Implicit Type (FF : Filter F) (PF: ProperFilter F).
Local Notation C := R[i].
Import Vector.InternalTheory.
Implicit Type (U V W: finNormedModType C).

Lemma linear_continuous {U V} (f : {linear U -> V}) :
  continuous f.
Proof.
pose g x := v2r (f (r2v x)); suff <-: r2v \o g \o v2r = f.
apply: continuous_comp_simp; first by apply: v2r_continuous.
apply: continuous_comp_simp; last by apply: r2v_continuous.
by apply/cmxlinear_continuous=>a x y; rewrite /g !linearP.
by apply/funext=>x; rewrite /g/= !v2rK.
Qed.

Lemma linear_continuousP {U V} (f : U -> V) :
  linear f -> continuous f.
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_continuous. Qed.

Lemma linear_cvg {FF} {U V} (f : {linear U -> V}) (u : T -> U) (a : U) :
  u @ F --> a -> f \o u @ F --> f a.
Proof. move=>cu. apply: continuous_cvg=>//. apply: linear_continuous. Qed.

Lemma linear_cvgP {FF} {U V} (f : U -> V) (u : T -> U) (a : U) :
  linear f -> u @ F --> a -> f \o u @ F --> f a.
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_cvg. Qed.

Lemma linear_is_cvg {FF} {U V} (f : {linear U -> V}) (u : T -> U) :
  cvg (u @ F) -> cvg (f \o u @ F).
Proof. move/cvg_ex=>[a Pa]; apply/cvg_ex; exists (f a); by apply: linear_cvg. Qed.

Lemma linear_is_cvgP {FF} {U V} (f : U -> V) (u : T -> U) :
  linear f -> cvg (u @ F) -> cvg (f \o u @ F).
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_is_cvg. Qed.

Lemma linear_lim {PF} {U V} (f : {linear U -> V}) (u : T -> U) :
  cvg (u @ F) -> lim (f \o u @ F) = f (lim (u @ F)).
Proof. by move=>cu; apply: cvg_lim; [apply: Vhausdorff | apply: linear_cvg]. Qed.

Lemma linear_limP {PF} {U V} (f : U -> V) (u : T -> U) :
  linear f -> cvg (u @ F) -> lim (f \o u @ F) = f (lim (u @ F)).
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_lim. Qed.

Lemma linearl_continuous {U V W} (f : {bilinear U -> V -> W}) (x : V):
  continuous (f^~ x).
Proof. have <-: applyr f x = f^~x by apply/funext/applyrE. apply: linear_continuous. Qed. 

Lemma linearl_cvg {FF} {U V W} (f : {bilinear U -> V -> W}) (x : V)
 (u : T -> U) (a : U) :
  u @ F --> a -> (f^~x) \o u @ F --> f a x.
Proof. have <-: applyr f x = f^~x by apply/funext/applyrE. apply: linear_cvg. Qed.

Lemma linearl_is_cvg {FF} {U V W} (f : {bilinear U -> V -> W}) (x : V) (u : T -> U) :
  cvg (u @ F) -> cvg (f^~x \o u @ F).
Proof. have <-: applyr f x = f^~x by apply/funext/applyrE. apply: linear_is_cvg. Qed.

Lemma linearl_lim {PF} {U V W} (f : {bilinear U -> V -> W}) (x : V) (u : T -> U) :
  cvg (u @ F) -> lim (f^~x \o u @ F) = f (lim (u @ F)) x.
Proof. have <-: applyr f x = f^~x by apply/funext/applyrE. apply: linear_lim. Qed.

Lemma linearr_continuous {U V W} (f : {bilinear U -> V -> W}) (x : U):
  continuous (f x).
Proof. exact: linear_continuous. Qed. 

Lemma linearr_cvg {FF} {U V W} (f : {bilinear U -> V -> W}) (x : U)
  (u : T -> V) (a : V):
  u @ F --> a -> (f x) \o u @ F --> f x a.
Proof. exact: linear_cvg. Qed.

Lemma linearr_is_cvg {FF} {U V W} (f : {bilinear U -> V -> W}) (x : U) (u : T -> V) :
  cvg (u @ F) -> cvg (f x \o u @ F).
Proof. exact: linear_is_cvg. Qed.

Lemma linearr_lim {PF} {U V W} (f : {bilinear U -> V -> W}) (x : U) (u : T -> V) :
  cvg (u @ F) -> lim (f x \o u @ F) = f x (lim (u @ F)).
Proof. exact: linear_lim. Qed.

Lemma linear_to_mx_continuous {U} m n (f : {linear U -> 'M[C]_(m,n)}) :
  continuous f.
Proof.
pose g x := (f (r2v x)); suff <-: g \o v2r = f.
apply: continuous_comp_simp; first by apply: v2r_continuous.
by apply/cmxlinear_continuous=>a x y; rewrite /g !linearP.
by apply/funext=>x; rewrite /g/= !v2rK.
Qed.

Lemma linear_to_mx_continuousP {U} m n (f : U -> 'M[C]_(m,n)) :
  linear f -> continuous f.
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_to_mx_continuous. Qed.

Lemma linear_of_mx_continuous {U} m n (f : {linear 'M[C]_(m,n) -> U}) :
  continuous f.
Proof.
pose g x := v2r (f x); suff <-: r2v \o g = f.
apply: continuous_comp_simp; last by apply: r2v_continuous.
by apply/cmxlinear_continuous=>a x y; rewrite /g !linearP.
by apply/funext=>x; rewrite /g/= !v2rK.
Qed.

Lemma linear_of_mx_continuousP {U} m n (f : 'M[C]_(m,n) -> U) :
  linear f -> continuous f.
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_of_mx_continuous. Qed.

Lemma closed_linearP {U V} (f : U -> V) (A : set V) :
  linear f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply linear_continuousP. Qed.

Lemma open_linearP {U V} (f : U -> V) (A : set V) :
  linear f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply linear_continuousP. Qed.

Lemma closed_linear {U V} (f : {linear U -> V}) (A : set V) : 
  closed A -> closed (f @^-1` A).
Proof. apply closed_linearP; exact: linearP. Qed. 

Lemma open_linear {U V} (f : {linear U -> V}) (A : set V) : 
  open A -> open (f @^-1` A).
Proof. apply open_linearP; exact: linearP. Qed. 

Lemma closed_to_mx_linearP {U} m n (f : U -> 'M[C]_(m,n)) (A : set 'M[C]_(m,n)):
  linear f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply linear_to_mx_continuousP. Qed.

Lemma closed_to_mx_linear {U} m n (f : {linear U -> 'M[C]_(m,n)}) (A : set 'M[C]_(m,n)):
  closed A -> closed (f @^-1` A).
Proof. apply closed_to_mx_linearP; exact: linearP. Qed.

Lemma open_to_mx_linearP {U} m n (f : U -> 'M[C]_(m,n)) (A : set 'M[C]_(m,n)):
  linear f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply linear_to_mx_continuousP. Qed.

Lemma open_to_mx_linear {U} m n (f : {linear U -> 'M[C]_(m,n)}) (A : set 'M[C]_(m,n)):
  open A -> open (f @^-1` A).
Proof. apply open_to_mx_linearP; exact: linearP. Qed.

Lemma closed_of_mx_linearP {U} m n (f : 'M[C]_(m,n) -> U) (A : set U):
  linear f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply linear_of_mx_continuousP. Qed.

Lemma closed_of_mx_linear {U} m n (f : {linear 'M[C]_(m,n) -> U}) (A : set U):
  closed A -> closed (f @^-1` A).
Proof. apply closed_of_mx_linearP; exact: linearP. Qed.

Lemma open_of_mx_linearP {U} m n (f : 'M[C]_(m,n) -> U) (A : set U):
  linear f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply linear_of_mx_continuousP. Qed.

Lemma open_of_mx_linear {U} m n (f : {linear 'M[C]_(m,n) -> U}) (A : set U):
  open A -> open (f @^-1` A).
Proof. apply open_of_mx_linearP; exact: linearP. Qed.

End LinearContinuous.

Section VOrderFinNormedModTheory.
Context {R : realType} {V : vorderFinNormedModType R[i]}.
Local Notation C := R[i].
Local Notation M := 'rV[C]_(Vector.dim V).
Import Vector.InternalTheory.

Lemma closed_gev0: closed [set x : V | (0 : V) ⊑ x].
Proof. by case: V=>?[???[?]]. Qed.

Definition v2r_vorderle (x y : M) := r2v x ⊑ r2v y.
Definition v2r_vorderlt (x y : M) := r2v x ⊏ r2v y.

Lemma v2r_vorderlt_def (x y : M): v2r_vorderlt x y = (y != x) && (v2r_vorderle x y).
Proof. by rewrite /v2r_vorderlt lt_def (can_eq r2vK). Qed.

Lemma v2r_vorderle_anti : antisymmetric v2r_vorderle.
Proof. by move=>x y; rewrite /v2r_vorderle=>/le_anti/r2v_inj. Qed.

Lemma v2r_vorderle_refl : reflexive v2r_vorderle.
Proof. by move=>x; exact: le_refl. Qed.

Lemma v2r_vorderle_trans : transitive v2r_vorderle.
Proof. by move=>x y z; exact: le_trans. Qed. 

Definition v2r_vorderle_porderMixin := LePOrderMixin 
  v2r_vorderlt_def v2r_vorderle_refl v2r_vorderle_anti v2r_vorderle_trans.
Definition v2r_vorderle_porderType := 
  POrderType vorder_display M v2r_vorderle_porderMixin.
Local Canonical v2r_vorderle_porderType.

Lemma v2r_lemx_add2r : forall (z x y : M), x ⊑ y -> x + z ⊑ y + z.
Proof. by move=>z x y; rewrite /Order.le/= /v2r_vorderle !linearD/= levD2r. Qed.

Lemma v2r_lemx_pscale2lP : forall (e : C) (x y : M), 0 < e -> x ⊑ y -> e *: x ⊑ e *: y.
Proof. 
by move=>e x y egt0; rewrite /Order.le/= 
  /v2r_vorderle !linearZ/=; apply lev_pscale2lP.
Qed.

Lemma v2r_closed_gemx0: closed [set x : M | (0 : M) ⊑ x].
Proof.
rewrite (_ : mkset _ = r2v @^-1` [set x : V | (0 : V) ⊑ x]).
apply: closed_comp=>[? _|]; [apply: r2v_continuous | apply: closed_gev0].
by rewrite predeqE {1}/Order.le/= /v2r_vorderle linear0.
Qed.

Definition v2r_mxcporder := MxCPorder
  v2r_lemx_add2r v2r_lemx_pscale2lP v2r_closed_gemx0.

Lemma nondecreasing_oppv (u_ : V ^nat) :
  nondecreasing_seq (- u_) = nonincreasing_seq u_.
Proof. by rewrite propeqE; split => du x y /du; rewrite levN2. Qed.

Lemma nonincreasing_oppv (u_ : V ^nat) :
  nonincreasing_seq (- u_) = nondecreasing_seq u_.
Proof. by rewrite propeqE; split => du x y /du; rewrite levN2. Qed.

Lemma decreasing_oppv (u_ : V ^nat) :
  decreasing_seq (- u_) = increasing_seq u_.
Proof. by rewrite propeqE; split => du x y; rewrite -du levN2. Qed.

Lemma increasing_oppv (u_ : V ^nat) :
  increasing_seq (- u_) = decreasing_seq u_.
Proof. by rewrite propeqE; split => du x y; rewrite -du levN2. Qed.

Lemma lbounded_by_opp (b : V) (u : V ^nat) :
  lbounded_by (-b) (- u) = ubounded_by b u.
Proof. 
by rewrite propeqE; split => bu i; move: (bu i); 
  rewrite {2}/GRing.opp/= levN2.
Qed.

Lemma ubounded_by_opp (b : V) (u : V ^nat) :
  ubounded_by (-b) (- u) = lbounded_by b u.
Proof. 
by rewrite propeqE; split => bu i; move: (bu i); 
  rewrite {2}/GRing.opp/= levN2.
Qed.

Lemma open_ngev0 : open [set x : V | ~ (0 : V) ⊑ x].
Proof. rewrite openC; apply closed_gev0. Qed.

Lemma open_ngev y :  open [set x : V | ~ y ⊑ x].
Proof.
rewrite (_ : mkset _ = [set t | [set x | ~ (0 : V) ⊑ x] (- y + t)]).
by move: (@addr_continuous _ _ (-y))=>/continuousP/=/(_ _ open_ngev0).
by apply/funext=>x; rewrite /= addrC subv_ge0.
Qed.

Lemma open_nlev0 : open [set x : V | ~ x ⊑ (0 : V)].
Proof.
rewrite (_ : mkset _ = [set t | [set x | ~ (0 : V) ⊑ x] (- t)]).
by move: (@opp_continuous _ V)=>/continuousP/=/(_ _ open_ngev0).
by apply/funext=>x; rewrite /= -{2}oppr0 levN2. 
Qed.

Lemma open_nlev y :  open [set x : V | ~ x ⊑ y].
Proof.
rewrite (_ : mkset _ = [set t | [set x : V | ~ - y ⊑ x] (- t)]).
by move: (@opp_continuous _ V)=>/continuousP/=/(_ _ (open_ngev (-y))).
by apply/funext=>x; rewrite /= levN2.
Qed.

Lemma closed_gev x : closed [set y : V | x ⊑ y ].
Proof. 
set A := ~` [set y : V | ~ (x ⊑ y)].
have ->: (fun x0 : V => is_true (x ⊑ x0)) = A.
by rewrite predeqE /A => y/=; rewrite notK.
rewrite closedC. apply/open_ngev. 
Qed.

Lemma closed_lev x : closed [set y : V | y ⊑ x ].
Proof. 
set A := ~` [set y : V | ~ (y ⊑ x)].
have ->: (fun x0 : V => is_true (x0 ⊑ x)) = A.
by rewrite predeqE /A => y/=; rewrite notK.
rewrite closedC. apply/open_nlev. 
Qed.

Lemma closed_eqv x : closed [set y : V | y = x].
Proof. exact: closed_eq. Qed.
(* rewrite (_ : mkset _ = [set y : V | x ⊑ y ] `&` [set y : V | y ⊑ x ]).
apply: closedI; [apply: closed_gev | apply: closed_lev].
by rewrite predeqE=>v/=; split=>[->//|/andP/le_anti->].
Qed. *)


Lemma lim_gev_nearF {T : Type} {F : set (set T)} {FF : ProperFilter F} 
  (x : V) (u : T -> V) :
    cvg (u @ F) -> (\forall n \near F, x ⊑ u n) -> x ⊑ lim (u @ F).
Proof. by move=> /[swap] /(closed_cvg (fun y => x ⊑ y))P; apply/P/closed_gev. Qed.

Lemma lim_gev_near (x : V) (u : V ^nat) : 
  cvg u -> (\forall n \near \oo, x ⊑ u n) -> x ⊑ lim u.
Proof. exact: lim_gev_nearF. Qed.

Lemma lim_lev_nearF {T : Type} {F : set (set T)} {FF : ProperFilter F} 
  (x : V) (u : T -> V) :
    cvg (u @ F) -> (\forall n \near F, u n ⊑ x) -> lim (u @ F) ⊑ x.
Proof. by move=> /[swap] /(closed_cvg (fun y : V => y ⊑ x))P; apply/P/closed_lev. Qed.

Lemma lim_lev_near (x : V) (u : V ^nat) : 
  cvg u -> (\forall n \near \oo, u n ⊑ x) -> lim u ⊑ x.
Proof. exact: lim_lev_nearF. Qed.

Lemma lev_lim_nearF {T : Type} {F : set (set T)} {FF : ProperFilter F} 
  (u v : T -> V) :
    cvg (u @ F) -> cvg (v @ F) -> 
      (\forall n \near F, u n ⊑ v n) -> lim (u @ F) ⊑ lim (v @ F).
Proof.
move=> uv cu cv; rewrite -(subv_ge0) -limB//.
apply: lim_gev_nearF=>//. apply: is_cvgB=>//.
by apply: filterS cv => k; rewrite (subv_ge0).
Qed.

Lemma lev_lim_near (u_ v_ : V ^nat) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, u_ n ⊑ v_ n) -> lim u_ ⊑ lim v_.
Proof. exact: lev_lim_nearF. Qed.

Lemma lim_eqv_nearF {T : Type} {F : set (set T)} {FF : ProperFilter F} 
  (u v : T -> V) : 
    cvg (u @ F) -> cvg (v @ F) ->
      (\forall n \near F, u n = v n) -> 
        lim (u @ F) = lim (v @ F).
Proof.
move=>cu cv uv. apply/le_anti/andP; split; apply/lev_lim_nearF=>//;
near=>J; suff ->: u J = v J by []; near: J; apply uv.
Unshelve. all: end_near.
Qed.

Lemma lim_eqv_near (u_ v_ : V ^nat) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, u_ n = v_ n) -> lim u_ = lim v_.
Proof. exact: lim_eqv_nearF. Qed.

Lemma lim_gevF {T : Type} {F : set (set T)} {FF : ProperFilter F} 
  (x : V) (u : T -> V) :
    cvg (u @ F) -> lbounded_by x u -> x ⊑ lim (u @ F).
Proof. by move=>P1 P2; apply: (lim_gev_nearF P1); apply: nearW. Qed.

Lemma lim_gev (x : V) (u : V ^nat) : cvg u -> lbounded_by x u -> x ⊑ lim u.
Proof. exact: lim_gevF. Qed.

Lemma lim_levF {T : Type} {F : set (set T)} {FF : ProperFilter F} 
  (x : V) (u : T -> V) :
    cvg (u @ F) -> ubounded_by x u -> lim (u @ F) ⊑ x.
Proof. by move=>P1 P2; apply: (lim_lev_nearF P1); apply: nearW. Qed.  

Lemma lim_lev (x : V) (u : V ^nat) : cvg u -> ubounded_by x u -> lim u ⊑ x.
Proof. exact: lim_levF. Qed.

Lemma lev_limF {T : Type} {F : set (set T)} {FF : ProperFilter F} 
  (u v : T -> V) :
    cvg (u @ F) -> cvg (v @ F) -> 
      (forall n, u n ⊑ v n) -> lim (u @ F) ⊑ lim (v @ F).
Proof. by move=>P1 P2 P3; apply: (lev_lim_nearF P1 P2); apply: nearW. Qed.

Lemma lev_lim (u v : V^nat) : cvg u -> cvg v ->
  (forall n, u n ⊑ v n) -> lim u ⊑ lim v.
Proof. exact: lev_limF. Qed.

Lemma nondecreasing_cvg_lev (u : V ^nat) :
       nondecreasing_seq u -> cvg u -> ubounded_by (lim u) u.
Proof.
move=>Ph Pc i; apply: lim_gev_near=>//; exists i=>// j; apply Ph.
Qed.

Lemma nonincreasing_cvg_gev (u : V ^nat) : 
  nonincreasing_seq u -> cvg u -> lbounded_by (lim u) u.
Proof.
move=>Ph Pc i; apply: lim_lev_near=>//; exists i=>// j; apply Ph.
Qed.

Lemma vnondecreasing_is_cvgn (f : nat -> V) (b : V) :
  nondecreasing_seq f -> ubounded_by b f -> cvg f.
Proof.
move=>P1 P2. pose g := (v2r \o f).
have P3: nondecreasing_seq g by move=>n m /P1; rewrite {2}/Order.le/= /v2r_vorderle !v2rK.
have P4: ubounded_by (v2r b) g by move=>i; rewrite /Order.le/= /v2r_vorderle !v2rK.
move: (mxnondecreasing_is_cvgn v2r_mxcporder P3 P4).
have <-: r2v \o g = f by apply/funext=>x/=; rewrite v2rK.
move=> /cvg_ex[l fxl]; apply/cvg_ex; exists (r2v l).
by apply: continuous_cvg => //; apply: r2v_continuous.
Qed.

Lemma vnonincreasing_is_cvg (f : nat -> V) (b : V) :
    nonincreasing_seq f -> lbounded_by b f -> cvg f.
Proof.
rewrite -(nondecreasing_oppv) -(ubounded_by_opp) -is_cvgNE.
exact: vnondecreasing_is_cvgn.
Qed.

End VOrderFinNormedModTheory.

(* Using Carathéodory to show that, *)
(* exists c, forall x, c * \sum_i `|xi| <= `|\sum_i xi| *)
(* Proof sketch : n dim space *)
(* 1. compact SB := [set x : V | 0 ⊑ x /\ `|x| = 1] *)
(* 2. compact SC := [set x : 'rV_n+1 | forall i, 0 <= xi & \sum_i xi = 1] *)
(* 3. pose TT := fun i : option 'I_n.+1 =>  match i with 
                                            | None => 'rV_n+1 
                                            | Some _ => V end  *)
(* 4. pose TA : forall i, set (TT i) := fun i => match i with
                                            | None => SC 
                                            | Some_ => SB end *)
(* 5. note conv(SB) = [set x | exists f : TT, (forall i, TA i (f i)) /\
      \sum_i f None 0 i *: f Some i = x] *)
(*  according to Carathéodory: x \in conv(SB) <-> 
      x = \sum_(i < n+1) ai xi, \sum ai = 1 & xi \in SB *)
(* 6. conv(SB) is compact by tychonoff theorem *)
(* 7. compact SA := [set r : C | exists x, x \in conv(SB) & `|x| = r] *)
(* 8. exists c > 0, SA c /\ forall r, SA r -> c <= r *)
(* 9. forall 0 ⊑ xi, `|\sum_i xi| >= c * \sum_i `|xi| *)

Section test.
Context {R : realType} {V : vorderFinNormedModType R[i]}.
Local Notation C := R[i].

Import Num.Def Num.Theory.

Lemma compact_ge0_norm1 : compact [set x : V | (0 : V) ⊑ x /\ `|x| = 1].
Proof.
apply: (subclosed_compact _ (compact_norm_le (V := V) (e := 1)))=>[|?/=[] _ ->//].
rewrite (_ : mkset _ = [set x : V | (0 : V) ⊑ x] `&` (fun x=>`|x|) @^-1` [set x : C | x = 1]).
apply: closedI. apply: closed_gev0.
apply: closed_comp=>[? _ |]; [apply: norm_continuous | apply: cclosed_eq].
by apply/funext=>x /=.
Qed.

(*Lemma tychonoff (I : eqType) (T : I -> topologicalType)
  (A : forall i, set (T i)) :*)
(*T : *)
Let TT (i : option bool) :=
  match i with
  | None => [topologicalType of C]
  | Some _ => [topologicalType of V]
  end.
Let TA (i : option bool) : set (TT i) :=
  match i with
  | None => [set x : C | 0 <= x <= 1]
  | Some _ => [set x : V | (0 : V) ⊑ x /\ `|x| = 1]
  end.
Let SV := [set x : V | exists a y z, 0 <= a <= 1 /\ 
((0 : V) ⊑ y /\ `|y| = 1) /\ ((0 : V) ⊑ z /\ `|z| = 1) /\ a *: y + (1-a) *: z = x].
Let SA := [set x : C | exists a y z, 0 <= a <= 1 /\ 
((0 : V) ⊑ y /\ `|y| = 1) /\ ((0 : V) ⊑ z /\ `|z| = 1) /\ `|a *: y + (1-a) *: z| = x].
Let SA_SV : SA = (fun x => `|x|) @` SV.
Proof.
apply/funext=>x/=; rewrite propeqE; split.
move=>[a[y[z[Pa[Py[Pz P]]]]]]; exists (a *: y + (1 - a) *: z)=>//;
exists a; exists y; exists z; do !split=>//.
move=>[w[a[y[z [Pa [Py [Pz <-]]]]]]] <-; exists a; exists y; exists z.
do !split=>//.
Qed.

Lemma compact_citv (a b : C) : compact [set x : C | a <= x <= b].
Proof.
apply: (subclosed_compact _ (C_bounded_compact (a := `|b - a| + `|a|))).
rewrite (_ : mkset _ = [set x : C | a <= x] `&` [set x : C | x <= b]).
apply: closedI. apply: cclosed_ge. apply: cclosed_le.
by apply/funext=>x/=; rewrite propeqE; split=>[/andP//|[]->->].
move=>x/=/andP[]; rewrite -[a <= x]subr_ge0 -[x <= b](lerD2r (-a))=>P1 P2.
rewrite -lerBlDr; apply/(le_trans (lerB_dist _ _)).
by rewrite !ger0_norm//; apply: (le_trans P1).
Qed.

Let compact_SV : compact SV.
Proof.
rewrite /SV (_ : mkset _ = (fun x => x None *: x (Some true) + (1 - x None) *: x (Some false)) @` [set f : product_topologicalType _ | 
  (forall i : option bool, @TA i (f i))]); last first.
apply/funext=>x/=; rewrite propeqE; split.
move=>[a[y[z[Pa[Py[Pz P]]]]]]; exists ((fun i : option bool => match i with 
  | None => a | Some true => y | Some false => z end) : forall i, TT i)=>//.
by case=>//=; case.
move=>[t Pt1 Pt2]; exists (t None); exists (t (Some true)); exists (t (Some false)).
split; first by apply: (Pt1 None). split; last split=>//; apply: (Pt1 (Some _)).

apply: continuous_compact; last first.
apply: tychonoff; case=>/=. move=>_; apply: compact_ge0_norm1. apply: compact_citv.
move=>x; apply: cvgD; apply: cvgZ.
3: apply: cvgB; first by apply: cvg_cst.
all: move: x; apply: continuous_subspaceT.
1,3: apply: (@proj_continuous _ TT None).
apply: (@proj_continuous _ TT (Some true)).
apply: (@proj_continuous _ TT (Some false)).
Qed.

Let compact_SA : compact SA.
Proof.
rewrite SA_SV; apply: (continuous_compact _ compact_SV).
apply/continuous_subspaceT/norm_continuous.
Qed.

Let not_SA0 : ~ SA 0.
Proof.
move=>[a[y[z[/andP[Pa1 Pa2][[y_ge0 +][[z_ge0 +]]]]]]]/eqP; rewrite normrE addv_ss_eq0.
rewrite !scaler_eq0 -[y == 0]normr_eq0 -[z == 0]normr_eq0=>->->.
by rewrite !oner_eq0 !orbF=>/andP[]/eqP->; rewrite subr0 oner_eq0.
by apply/orP; left; rewrite !scalev_ge0// subr_ge0.
Qed.

Let SA_ge0 (x : C) : SA x -> x > 0.
Proof.
rewrite lt_def=>P1; apply/andP; split.
by apply/negP=>/eqP Px; apply: not_SA0; rewrite -Px.
by move: P1=>[?[?[?[?[?[?]]]]]]<-.
Qed.

Lemma lev_add_norm_lbound : { c : C | 0 < c <= 1 /\ (forall X Y, 
  ((0 : V) ⊑ X) && ((0 : V) ⊑ Y) -> c * (`|X| + `|Y|) <= `|X + Y|)}.
Proof.
move: (pselect (exists x : V, (0 : V) ⊏ x))=>[]; last first.
move=>/forallNP P1; exists 1; split=>[|X Y /andP[]].
by apply/andP; split.
by rewrite le_eqVlt =>/orP[|/P1//]/eqP<-; rewrite normr0 !add0r mul1r.
move=>/cid[x x_gt0].
have Px0 : forall (x : V), (0 : V) ⊏ x -> `|x| > 0.
  by move=>y; rewrite !lt_def normr_eq0=>/andP[]->//=.
have Px: forall (x : V), (0 : V) ⊏ x -> `|1/`|x| *: x| = 1.
  by move=>y /Px0 Py; rewrite normrZ normrM normr1 mul1r 
  gtr0_norm ?invr_gt0// mulVf// lt0r_neq0.
have Ps1: SA 1.
  exists 0; exists (1/`|x| *: x); exists (1/`|x| *: x); do ! split.
  by apply/andP; split. 1,3: by rewrite scalev_ge0// ltW. 1,2: by apply: Px.
  by rewrite scale0r add0r subr0 scale1r Px.
have /cid2[c Pc1 Pc2]: exists2 x : C, SA x & forall y : C, SA y -> x <= y.
  by apply: extNum_compact_min=>[i/SA_ge0/=/gtr0_real//||]; [apply: compact_SA | exists 1].
have cle1 : c <= 1 by apply: Pc2.
exists c; split=>[|X Y]; first by apply/andP; split=>//; apply: SA_ge0.
rewrite 2 !le_eqVlt=>/andP[]/orP[/eqP<- _|X_gt0/orP[/eqP<-|Y_gt0]].
1,2: rewrite !normr0 ?(add0r, addr0) ler_piMl//.
pose a : R[i] := `|X| / (`|X| + `|Y|).
pose Z := a *: (1 / `|X| *: X) + (1-a) *: (1 / `|Y| *: Y).
have PZ: SV Z.
exists a; exists (1 / `|X| *: X); exists (1 / `|Y| *: Y); do ! split.
  by apply/andP; split; rewrite /a ?divr_ge0// ler_pdivrMr 
    ?mul1r ?lerDl// addr_gt0// Px0.
  1,3: by rewrite scalev_ge0// ltW.
  1,2: by apply: Px.
have: SA `|Z| by rewrite SA_SV/=; exists Z.
move=>/Pc2; rewrite/Z !scalerA.
have ->: a * (1 / `|X|) = 1 / (`|X| + `|Y|).
  by rewrite/a mulrC mulrA mulfVK// lt0r_neq0// Px0.
have ->: (1 - a) * (1 / `|Y|) = 1 / (`|X| + `|Y|).
  rewrite -{1}(mulfV (x := `|X| + `|Y|)) ?lt0r_neq0// ?addr_gt0// ?Px0//.
  by rewrite /a -mulrBl addrC addKr mulrC mulrA mulfVK// lt0r_neq0// Px0.
by rewrite -scalerDr normrZ ger0_norm ?divr_ge0// 
  mulrC mulrA mulr1 ler_pdivlMr// addr_gt0// Px0.
Qed.

(* Lemma test7 (x y : V) : `|x| = 1 -> `|y| <= 1 -> exists a z, 
  0 <= a <= 1 /\ `|z| = 1 /\ a *: x + (1-a) *: z = y.
Admitted.

Lemma test6 : { c : C | c > 0 /\ 
  (forall X Y, ((0 : V) ⊑ X) && (X ⊑ Y) -> c * `|X| <= `|Y|)}.
move: (pselect (exists x : V, (0 : V) ⊏ x))=>[]; last first.
move=>/forallNP P1; exists 1; split=>// X Y.
by move=>/andP[] xge0 /(le_trans xge0); move: xge0; rewrite !le_eqVlt
  =>/orP[|/P1//]/eqP<-/orP[|/P1//]/eqP<-; rewrite !normr0 mulr0 eqxx.
move=>/cid[x xgt0].
have Px: `|1/`|x| *: x| = 1.
  rewrite normrZ normrM normr1 mul1r ger0_norm ?invr_ge0// mulVf//.
  by move: xgt0; rewrite lt_def normr_eq0=>/andP[].
have Ps1: SA 1.
  exists 0; exists (1/`|x| *: x); exists (1/`|x| *: x); do ! split=>//.
  by apply/andP; split. 1,2: by rewrite scalev_ge0// ltW.
  by rewrite scale0r add0r subr0 scale1r.
have /cid2[c Pc1 Pc2]: exists2 x : C, SA x & forall y : C, SA y -> x <= y.
by apply: extNum_compact_min=>[i/test5/=/gtr0_real//||]; [apply: test3 | exists 1].
have cle1 : c <= 1 by apply: Pc2.
exists c; split=>[|X Y]. by apply: test5.
case E: (X == 0); first by move: E=>/eqP->; rewrite normr0 mulr0. *)


End test.

Section CmxLownerOrder.
Import MxLownerOrder Num.Def Num.Theory.
Variable (R : realType).
Local Notation C := R[i].

Lemma form_nng_neq0 n x : reflect (exists u: 'cV[C]_n, 
  (0 < \tr (u^*t *m u)) && (\tr (u^*t *m x *m u) \isn't Num.nneg))
  (~~ ((0 : 'M[C]_n) ⊑ x)).
Proof.
apply (iffP negP). apply contra_notP.
rewrite -forallNP=>P1. rewrite le_lownerE subr0. apply/psdmx_dot=>u.
move: (P1 u). move/negP. rewrite mxtrace_mulC negb_and=>/orP[|].
rewrite lt_def form_tr_ge0 negb_and/= orbF negbK=>/eqP/form_tr_eq0->.
by rewrite !mulmx0 linear0 nnegrE.
by rewrite negbK.
apply contraPnot. rewrite -forallNP le_lownerE subr0=>/psdmx_dot=>P1 u.
by apply/negP; rewrite negb_and negbK P1 orbT.
Qed.

Lemma Cnng_open (t : C) : t \isn't Num.nneg -> 
  exists2 e, 0 < e & forall s, `|s - t| < e -> s \isn't Num.nneg.
Proof.
rewrite nnegrE lecE/= negb_and -real_ltNge ?real0// ?num_real// =>/orP[P1|P1].
exists (`|complex.Im t|)%:C=>[|s]; first by rewrite ltcR normr_gt0.
2: exists (`|complex.Re t|)%:C=>[|s]; first by move: P1; rewrite ltcR !lt_def 
  normr_ge0 normr_eq0 eq_sym=>/andP[->].
all: rewrite nnegrE lecE negb_and/= -normr_gt0=>P2.
move: (le_lt_trans (normc_ge_Im _) P2). 2: move: (le_lt_trans (normc_ge_Re _) P2).
all: rewrite ltcR raddfB/= -normrN opprB =>P3.
move: (le_lt_trans (lerB_dist _ _) P3).
by rewrite ltrBlDl -ltrBlDr addrN=>->.
move/ltr_distlCDr: P3. 
by rewrite ltr0_norm// addrN -real_ltNge ?real0// ?num_real// orbC=>->.
Qed.

Lemma psdmx_closed n : (closed [set x : 'M[C]_n | (0 : 'M[C]_n) ⊑ x])%classic.
Proof.
case: n=>[x/= _|n]; first by rewrite !mx_dim0. 
rewrite (_ : mkset _ = ~` [set x | ~ (0 : 'M[C]_n.+1) ⊑ x]); last first.
by rewrite predeqE=>x /=; rewrite notK.
rewrite closedC. move=> x /= /negP /form_nng_neq0 [u /andP[P1 /Cnng_open [e egt0 Pe]]].
move: (@mnorm_bounded R n.+1 n.+1 (trnorm_vnorm _ _ _) mx_norm_vnorm)=>[c cgt0 Pc].
rewrite nbhs_ballP. 
exists (e/c/(\tr (u^*t *m u)))=>/=[|y/=]; first by do 2 apply divr_gt0=>//.
rewrite -ball_normE/= mulrAC ltr_pdivlMr// =>Pb; apply/negP/form_nng_neq0.
exists u; apply/andP; split=>//; apply Pe.
rewrite /ball/= -linearB/= -mulmxBl -mulmxBr.
apply: (le_lt_trans (trnorm_inner _ _)).
rewrite mulrC -lter_pdivlMl// mulrC. apply: (le_lt_trans _ Pb).
by move: (Pc (y - x))=>/=; rewrite mulrC -normrN opprB.
Qed.

Lemma trnorm_add_eq n (x y : 'M[C]_n) : (0 : 'M[C]_n) ⊑ x -> (0 : 'M[C]_n) ⊑ y 
  -> trnorm x  + trnorm y = trnorm (x + y).
Proof.
rewrite !le_lownerE !subr0=>P1 P2. move: (psdmx_add P1 P2).
move: P1 P2=>/psdmx_trnorm->/psdmx_trnorm->/psdmx_trnorm->.
by rewrite linearD.
Qed.

Program Definition lowner_mxcporder n := MxCPorder _ _ (@psdmx_closed n).
Next Obligation. exact: lemx_add2rP. Qed.
Next Obligation. exact: lemx_pscale2lP. Qed.

(* restate the cmxcvg of lowner order and trnorm *)
Lemma mxcvg_trnorm m n (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) : 
  u --> a -> ((@trnorm _ _ _) \o u) --> \tr| a |.
Proof. exact: mxcvg_mnorm. Qed.

Lemma is_mxcvg_trnorm m n (u : nat -> 'M[C]_(m,n)) : 
  cvg u -> cvg ((@trnorm _ _ _) \o u).
Proof. exact: is_mxcvg_mnorm. Qed.

Lemma mxlim_trnorm m n (u : nat -> 'M[C]_(m,n)) : 
  cvg u -> lim ((@trnorm _ _ _) \o u) = \tr| lim u |.
Proof. exact: cmxlim_mnorm. Qed.

Lemma mxnondecreasing_is_cvgn n (f : nat -> 'M[C]_n) (b : 'M[C]_n) :
  nondecreasing_seq f -> ubounded_by b f -> cvg f.
Proof. exact: (mxnondecreasing_is_cvgn (lowner_mxcporder n)). Qed.

Lemma mxnonincreasing_is_cvg n (f : nat -> 'M[C]_n) (b : 'M[C]_n) :
  nonincreasing_seq f -> lbounded_by b f -> cvg f.
Proof. exact: (mxnonincreasing_is_cvg (lowner_mxcporder n)). Qed.

Lemma closed_gemx n (x : 'M[C]_n) : closed [set y : 'M[C]_n | x ⊑ y ].
Proof. exact: (mxclosed_ge (lowner_mxcporder n)). Qed.

Lemma closed_lemx n (x : 'M[C]_n) : closed [set y : 'M[C]_n | y ⊑ x ].
Proof. exact: (mxclosed_le (lowner_mxcporder n)). Qed.

Lemma lim_gemx_near n (x : 'M[C]_n) (u : nat -> 'M[C]_n) : 
  cvg u -> (\forall n \near \oo, x ⊑ u n) -> x ⊑ lim u.
Proof. exact: (mxlim_ge_near (lowner_mxcporder n)). Qed.

Lemma lim_lemx_near n (x : 'M[C]_n) (u : nat -> 'M[C]_n) : 
  cvg u -> (\forall n \near \oo, u n ⊑ x) -> lim u ⊑ x.
Proof. exact: (mxlim_le_near (lowner_mxcporder n)). Qed.

Lemma lemx_lim_near n (u_ v_ : nat -> 'M[C]_n) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, u_ n ⊑ v_ n) -> lim u_ ⊑ lim v_.
Proof. exact: (ler_mxlim_near (lowner_mxcporder n)). Qed.

Lemma lim_gemx n (x : 'M[C]_n) (u : nat -> 'M[C]_n) : 
  cvg u -> lbounded_by x u -> x ⊑ lim u.
Proof. exact: (mxlim_ge (lowner_mxcporder n)). Qed.

Lemma lim_lemx n (x : 'M[C]_n) (u : nat -> 'M[C]_n) : 
  cvg u -> ubounded_by x u -> lim u ⊑ x.
Proof. exact: (mxlim_le (lowner_mxcporder n)). Qed.

Lemma lemx_lim n (u v : nat -> 'M[C]_n) : cvg u -> cvg v ->
  (forall n, u n ⊑ v n) -> lim u ⊑ lim v.
Proof. exact: (ler_mxlim (lowner_mxcporder n)). Qed.

Lemma mxnondecreasing_cvgn_le n (u : nat -> 'M[C]_n) :
  nondecreasing_seq u -> cvg u -> ubounded_by (lim u) u.
Proof. exact: (mxnondecreasing_cvgn_le (lowner_mxcporder n)). Qed.

Lemma mxnonincreasing_cvg_ge n (u : nat -> 'M[C]_n) : 
  nonincreasing_seq u -> cvg u -> lbounded_by (lim u) u.
Proof. exact: (mxnonincreasing_cvg_ge (lowner_mxcporder n)). Qed.

Lemma trace_continuous n : continuous (@mxtrace _ n : 'M[C]_n -> C).
Proof. by apply/cmxscalar_continuous/linearP. Qed.

Lemma closed_letr n (x : C) : closed [set y : 'M[C]_n | \tr y <= x].
Proof. 
rewrite (_ : mkset _ = mxtrace @^-1` [set y | y <= x])%classic.
apply: cmxcclosed_comp. exact: linearP. apply/cclosed_le. by apply/funext=>y.
Qed.

Lemma closed_getr n (x : C) : closed [set y : 'M[C]_n | x <= \tr y].
Proof. 
rewrite (_ : mkset _ = mxtrace @^-1` [set y | x <= y])%classic.
apply: cmxcclosed_comp. exact: linearP. apply/cclosed_ge. by apply/funext=>y.
Qed.

Lemma closed_eqtr n (x : C) : closed [set y : 'M[C]_n | \tr y = x].
Proof. 
rewrite (_ : mkset _ = mxtrace @^-1` [set y | y = x])%classic.
apply: cmxcclosed_comp. exact: linearP. apply/cclosed_eq. by apply/funext=>y.
Qed.

Lemma mxcvg_trace n (u : nat -> 'M[C]_n) (a : 'M[C]_n) : 
  u --> a -> ((@mxtrace _ n) \o u) --> \tr a.
Proof. by apply/cmxcvg_sfun/linearP. Qed.

Lemma is_mxcvg_trace n (u : nat -> 'M[C]_n) : cvg u -> cvg ((@mxtrace _ n) \o u).
Proof. by apply/is_cmxcvg_sfun/linearP. Qed.

Lemma mxlim_trace n (u : nat -> 'M[C]_n) : 
  cvg u -> lim ((@mxtrace _ n) \o u) = \tr (lim u).
Proof. by apply/cmxlim_sfun/linearP. Qed.

Lemma closed_denmx n : closed [set x : 'M[C]_n | x \is denmx].
Proof.
rewrite (_ : mkset _ = [set x | (0:'M[C]_n) ⊑ x] `&` [set x | \tr x <= 1]).
apply: closedI. apply: closed_gemx. apply: closed_letr.
by rewrite predeqE=>x/=; split; rewrite le_lownerE subr0=>/denmxP.
Qed.

Lemma closed_obsmx n : closed [set x : 'M[C]_n | x \is obsmx].
Proof.
rewrite (_ : mkset _ = [set x | (0:'M[C]_n) ⊑ x] `&` [set x | x ⊑ 1%:M]).
apply: closedI. apply: closed_gemx. apply: closed_lemx.
rewrite predeqE=>x/=; split.
by rewrite [in X in X -> _]obsmx_psd_eq !le_lownerE subr0=>/andP.
by rewrite [in X in _ -> X]obsmx_psd_eq !le_lownerE subr0=>[[]]->->.
Qed.

End CmxLownerOrder.

Section DenmxCPO.
Import MxLownerOrder Num.Theory.
Variable (R: realType) (n : nat).
Local Notation C := R[i].
Local Notation M := 'M[C]_n.
Local Notation D := 'MDen[C]_n.

Local Open Scope complex_scope.

Definition D2M (x : D) := x : M.

Lemma denmx0 : (0 : 'M[C]_n) \is denmx.
Proof. by apply/denmxP; split; [apply psdmx0 | rewrite linear0 lter01]. Qed.

Definition Denmx0 := ((DenMx denmx0) : D).

Definition Dlub (u : nat -> D) :=
  match lim (D2M \o u) \is denmx =P true with
  | ReflectT isden => (DenMx isden : D)
  | _ => Denmx0
  end.

Let chainD (u : nat -> D) : chain u -> nondecreasing_seq (D2M \o u).
Proof. by move=>/chain_homo P i j Pij; move: (P _ _ Pij); rewrite leEsub. Qed.

Let Dge0 : forall (x : D), Denmx0 ⊑ x.
Proof. by move=>x/=; case: x=>m Pm; rewrite leEsub/= le_lownerE subr0; apply/denmx_psd. Qed.

Let chainD_lb (u : nat -> D) : forall i, (0:M) ⊑ (D2M \o u) i.
Proof. by move=>i/=; case: (u i)=>m Pm; rewrite/= le_lownerE subr0; apply/denmx_psd. Qed.

Let chainD_ub (u : nat -> D) : forall i, (D2M \o u) i ⊑ 1%:M.
Proof.
move=>i/=; case: (u i)=>m Pm; rewrite/= le_lownerE.
by move: Pm=>/denmx_obs; rewrite obsmx_psd_eq=>/andP[_].
Qed.

Lemma lim_denmx (u : nat -> D) : 
  cvg (D2M \o u) -> [set x | x \is denmx] (lim (D2M \o u)).
Proof.
move=>P; apply: (@closed_cvg _ _ _ eventually_filter (D2M \o u) _ _ _ _)=>//.
apply closed_denmx. by apply: nearW=>x/=; case: (u x).
Qed.

Lemma Dlub_lub : forall c : nat -> D, chain c -> (forall i, c i ⊑ Dlub c) 
  /\ (forall x, (forall i, c i ⊑ x) -> Dlub c ⊑ x).
Proof.
move=>c Pc. move: (chainD Pc) (chainD_ub c)=>P1 P2.
move: (mxnondecreasing_is_cvgn P1 P2)=>P3.
move: (mxnondecreasing_cvgn_le P1 P3)=>P4.
rewrite /Dlub; case: eqP=>P5; last by exfalso; apply P5; apply lim_denmx.
split. by move=>i; rewrite leEsub/= P4.
by move=>x Px; rewrite leEsub/=; apply: lim_lemx.
Qed.

Lemma Dlub_ub : forall c : nat -> D, chain c -> (forall i, c i ⊑ Dlub c).
Proof. by move=>c /Dlub_lub=>[[P1]]. Qed.

Lemma Dlub_least : 
  forall c : nat -> D, chain c -> forall x, (forall i, c i ⊑ x) -> Dlub c ⊑ x.
Proof. by move=>c /Dlub_lub=>[[_ ]]. Qed.

Import CpoMixin.Exports.
Definition denmx_cpoMixin := CpoMixin Dge0 Dlub_ub Dlub_least.
Canonical denmx_cpoType := CpoType D denmx_cpoMixin.

End DenmxCPO.
