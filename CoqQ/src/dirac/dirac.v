(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra complex finmap.
From quantum.external Require Import forms spectral.
From mathcomp.classical Require Import boolp.
From mathcomp.analysis Require Import reals.
From mathcomp.real_closed Require Import complex.

Require Import mcextra mcaextra notation prodvect hermitian tensor.
Require Import mxpred extnum ctopology quantum.
From quantum.dirac Require Import setdec hstensor.

(************************************************************************)
(* This file provides an implementation of labelled Dirac notation      *)
(* It is defined as a non-dependent variant type 'D of dffun.           *)
(* 'D has linear algebraic structure (with + and scalar *:)             *)
(* implementation detail:                                               *)
(*   'D[H] := forall i : {set L} * {set L}, 'F[H]_(i.1, i.2)            *)
(*   for any (e : 'D) and (S,T : {set L}),                              *)
(*          e S T return the linear function 'F[H]_(S,T)                *)
(*   for any S T (f :'F[H]_(S,T)), '[ f ] return a 'D                   *)
(*   operations on 'D :                                                 *)
(*          construct : ket '|>, bra '<|, lin '[ ], dnum %:D            *)
(*                      d2v      d2dv     d2f    d2c                    *)
(*          unary: adjoint ^A, conjugate ^C, transpose ^T               *)
(*          binary: comp \o, tensor \⊗, general comp \·                   *)
(*   operation consistent : e.g., '[ f \⊗ g ] = '[ f ] \⊗ '[ g ]       *)
(*   big op :                                                           *)
(*          \mul : for comp    \o;  Monoid: Law, MulLaw, AddLaw          *)
(*          \ten_s : for tensor \⊗;  Monoid: Law, MulLaw, ComLaw AddLaw *)
(*          \dot  : for dot     \·;  Monoid: MulLaw, AddLaw              *)
(*   trace domain/codomain :                                            *)
(*          structure : 'D_(S,T) : e = '[ f ] for some f : 'F[H]_(S,T)  *)
(*          structure : 'D_S  : e = '[ f ] for some f : 'F[H]_S         *)
(*          structure : 'Ket_S  : e = '|v> for some v : 'H[H]_S         *)
(*          structure : {bar S}  : e = '<v| for some v : 'H[H]_S        *)
(*      canonical structure of each operations on 'D                    *)
(*          check [sqr of e | S] : find if e is canonical to 'D_S       *)
(*   vorder : e1 ⊑ e2 iff forall S T, 0 ⊑ (e2-e1) S S                  *)
(*                        & (e2-e1) S T = 0 if (S != T)                 *)
(*   order theory for tensor product                                    *)
(************************************************************************)

(* -------------------------------------------------------------------- *)
Import Order.TTheory GRing.Theory Num.Theory Num.Def.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Local Open Scope set_scope.
Local Open Scope efnd_scope.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.

(* -------------------------------------------------------------------- *)
Import Vector.InternalTheory.

Declare Scope dirac_scope.

Section Dirac.
Section Defn.
Context {L : finType} (H : L -> chsType).

Variant dirac := Dirac of {dffun forall d : {set L} * {set L}, 'F[H]_(d.1,d.2)}.

Definition dirac_val u := let: Dirac t := u in t.

Canonical dirac_subType := Eval hnf in [newType for dirac_val].

Fact dirac_key : unit. Proof. by []. Qed.
Definition dirac_of_fun_def (F : forall (i j : {set L}), 'F[H]_(i,j)) 
  := Dirac [ffun i => F i.1 i.2].
Definition dirac_of_fun k := locked_with k dirac_of_fun_def.
Canonical dirac_unlockable k := [unlockable fun dirac_of_fun k].

Definition fun_of_dirac u (i : {set L}) (j : {set L}) : 'F_(i,j) := dirac_val u (i,j).
Coercion fun_of_dirac : dirac >-> Funclass.

Lemma diracE k F i j : dirac_of_fun k F i j = F i j.
Proof. by rewrite unlock /fun_of_dirac /= ffunE. Qed.

Lemma diracP (u v : dirac) : (forall i j, u i j = v i j) <-> u = v.
Proof.
rewrite /fun_of_dirac; split=> [/= eq_uv | -> //].
by apply/val_inj/ffunP=> [[i j]]; apply: eq_uv.
Qed.

Lemma eq_dirac k u v : (forall i j, u i j = v i j) ->
  dirac_of_fun k u = dirac_of_fun k v.
Proof. by move=> eq_uv; apply/diracP => i j; rewrite !diracE eq_uv. Qed.

End Defn.

Definition dirac_eqMixin {I : finType} (E : I -> chsType) :=
  Eval hnf in [eqMixin of dirac E by <:].
Canonical dirac_eqType {I : finType} (E : I -> chsType) :=
  Eval hnf in EqType (dirac E) (dirac_eqMixin E).
Definition dirac_choiceMixin {I : finType} (E : I -> chsType) :=
  [choiceMixin of dirac E by <:].
Canonical dirac_choiceType {I : finType} (E : I -> chsType) :=
  Eval hnf in ChoiceType (dirac E) (dirac_choiceMixin E).

End Dirac.

Delimit Scope dirac_scope with D.
Bind Scope dirac_scope with dirac.
Local Open Scope dirac_scope.
Notation "''D[' H ]" := (@dirac _ H) (only parsing) : type_scope.
Notation "''D'" := (@dirac _ _) : type_scope.
Notation "\dirac_ ( i , j ) E" := (dirac_of_fun dirac_key (fun i j => E%VF)) : dirac_scope.

Section DiracSet.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T : {set L}).

Definition dset S T (f : 'F_(S,T)) : 'D :=
  \dirac_(i,j)
    match S =P i , T =P j return 'F[H]_(i,j) with
    | ReflectT eqi, ReflectT eqj => castlf (eqi, eqj) f
    | _, _ => 0
    end.

Lemma dsetii S T (f : 'F_(S,T)) :
  dset f S T = f.
Proof. by rewrite diracE; (do 2 case: eqP=>//?); rewrite castlf_id. Qed.

Lemma dset_eq0l S T S' T' (f : 'F_(S,T)) :
  S' != S -> dset f S' T' = 0.
Proof. by rewrite eq_sym diracE; case: eqP. Qed.

Lemma dset_eq0r S T S' T' (f : 'F_(S,T)) :
  T' != T -> dset f S' T' = 0.
Proof. by rewrite eq_sym diracE; do 2 case: eqP=>//. Qed.

Lemma dset_eq0p S T S' T' (f : 'F_(S,T)) :
  (S',T') != (S,T) -> dset f S' T' = 0.
Proof.
rewrite xpair_eqE negb_and=>/orP[P|P].
by rewrite dset_eq0l. by rewrite dset_eq0r.
Qed.

Lemma dset_inj S T : injective (@dset S T).
Proof. by move=>f g /diracP=>/(_ S T); rewrite !dsetii. Qed.

Lemma dset_cast S T S' T' (eqST: (S = S') * (T = T')) (f: 'F_(S,T)) :
  dset (castlf eqST f) = dset f.
Proof.
by case: eqST => eqS eqT; case: S' / eqS; case: T' / eqT; rewrite castlf_id.
Qed. 

End DiracSet.

(* Dirac : ringType with + and tensor (!!not com)*)
(* Dirac : vectType, so we can talk about its completeness, but not used now *)
Section DiracAlgebra.
Context {L : finType} (H : L -> chsType).
Implicit Types u v w : 'D[H].

Definition dirac_zero     := \dirac_(i , j) (0 : 'F[H]_(i,j)).
Definition dirac_add  u v := \dirac_(i , j) (u i j + v i j).
Definition dirac_opp  u   := \dirac_(i , j) - u i j.
Definition dirac_scale (c : C) u := \dirac_(i , j) (c *: u i j).

Program Canonical dirac_zmodType := Eval hnf in ZmodType 'D[H]
  (@GRing.Zmodule.Mixin _ dirac_zero dirac_opp dirac_add _ _ _ _).
Next Obligation.
by move=> f g h; apply/diracP=> i j; rewrite !diracE addrA.
Qed.
Next Obligation.
by move=> f g; apply/diracP=> i j; rewrite !diracE addrC.
Qed.
Next Obligation.
by move=> f; apply/diracP=> i j; rewrite !diracE add0r.
Qed.
Next Obligation.
by move=> f; apply/diracP=> i j; rewrite !diracE addNr.
Qed.

Lemma dirac_sumE T (r : seq T) (P : pred T) (F : T -> 'D) i j :
  (\sum_(x <- r | P x) F x) i j = \sum_(x <- r | P x) F x i j.
Proof. by elim/big_rec2: _ => /= [|x _ s Px <-]; rewrite diracE. Qed.

Program Canonical dirac_lmodType := Eval hnf in LmodType C 'D[H]
  (@LmodMixin _ _ dirac_scale _ _ _ _).
Next Obligation.
by move=> /= c d x; apply/diracP=> i j; rewrite !diracE scalerA.
Qed.
Next Obligation.
by move=> /= x; apply/diracP=> i j; rewrite !diracE scale1r.
Qed.
Next Obligation.
by move=> /= c u v; apply/diracP=> i j; rewrite !diracE scalerDr.
Qed.
Next Obligation.
by move=> /= u c d; apply/diracP=> i j; rewrite !diracE scalerDl.
Qed.

Lemma dirac_valZ c f i : dirac_val (c *: f) i = c *: dirac_val f i.
Proof. by rewrite {1}/GRing.scale/=/dirac_scale unlock/= ffunE; case: i. Qed.
Lemma dirac_valD f g i : dirac_val (f + g) i = dirac_val f i + dirac_val g i.
Proof. by rewrite {1}/GRing.add/=/dirac_add unlock/= ffunE; case: i. Qed.
Lemma dirac_valN f i : dirac_val (- f) i = - dirac_val f i.
Proof. by rewrite {1}/GRing.opp/=/dirac_opp unlock/= ffunE; case: i. Qed.
Lemma dirac_val0 i : dirac_val 0 i = 0.
Proof. by rewrite{1}/GRing.zero/=/dirac_zero/=unlock/= ffunE. Qed.

Let D := (\sum_i Vector.dim [vectType C of 'F[H]_(i.1,i.2)])%N.
Lemma dirac_vect_iso : Vector.axiom D 'D.
Proof.
pose Z := {i : {set L} * {set L} & 'I_(Vector.dim [vectType C of 'F[H]_(i.1,i.2)])}.
pose S (i : {set L} * {set L}) (x : 'I_(Vector.dim [vectType C of 'F[H]_(i.1,i.2)])) : Z := Tagged _ x.
suff: Vector.axiom #|{: Z}| 'D.
- apply: vect_axiom_eqdim; rewrite /D card_tagged.
  rewrite sumnE big_map big_enum /=.
  by apply: eq_bigr=> i _; rewrite card_ord.
pose fr (f : 'D) := \row_(i < #|{: Z}|)
  v2r (dirac_val f (tag (enum_val i))) 0 (tagged (enum_val i)).
exists fr=> /= [c f g|].
- by apply/rowP=> i; rewrite !mxE dirac_valD dirac_valZ linearP/= !mxE.
pose gr (i : {set L} * {set L}) (x : 'rV[C]_#|{: Z}|) :=
  r2v (\row_(j < Vector.dim [vectType C of 'F[H]_(i.1,i.2)]) x 0 (enum_rank (S _ j))).
exists (fun x => Dirac [ffun i => gr i x]) => [g|r].
- apply/val_inj=>/=; apply/ffunP=>i; rewrite ffunE /fr /gr.
  set r := (X in r2v X); suff ->: r = v2r (dirac_val g i) by rewrite v2rK.
  by apply/rowP=> k; rewrite !mxE enum_rankK /=.
- apply/rowP=> j; rewrite !mxE /= ffunE /gr r2vK mxE; congr (_ _ _).
  by apply/(canLR enum_valK)/esym/eqP; rewrite eq_Tagged.
Qed.
Definition dirac_vectMixin := VectMixin dirac_vect_iso.
Canonical dirac_vectType := VectType C 'D[H] dirac_vectMixin.

Lemma dset_is_linear S T : linear (@dset _ H S T).
Proof.
move=>a x y; apply/diracP=>i j; rewrite !diracE.
case: eqP=>p1; first case: eqP=>p2;
by rewrite ?linearP// scaler0 addr0.
Qed.
Definition dset_additive S T := Additive (@dset_is_linear S T).
Definition dset_linear S T := Linear (@dset_is_linear S T).
Local Canonical dset_linear.

Lemma dset_dec (f : 'D) : \sum_i dset (f i.1 i.2) = f.
Proof.
by apply/diracP=>i j; rewrite dirac_sumE (bigD1 (i,j))// big1/=
  =>[[k1 k2]/= nk|]; rewrite ?addr0 ?dsetii// dset_eq0p// eq_sym.
Qed.

(* We define the basic constructors *)
(* dlin dket dbra dnum dconj dtr dadj dmul ddot dten *)
(* we prevent any possible unfolding of them *)
Definition dlin_fun_def S T (f: 'F_(S,T)) : 'D[H] := dset f.
Definition dket_fun_def S (v : 'H_S) : 'D[H] := dset (v2f v).
Definition dbra_fun_def S (v : 'H_S) : 'D[H] := dset (v2df v).
Definition dnum_fun_def (c : C) : 'D[H] := dset (s2sf c).
Definition dconj_fun_def (e : 'D) : 'D[H] := \dirac_(i,j) (e i j)^C.
Definition dtr_fun_def   (e : 'D) : 'D[H] := \dirac_(i,j) (e j i)^T.
Definition dadj_fun_def  (e : 'D) : 'D[H] := \dirac_(i,j) (e j i)^A.
Definition dmul_fun_def (e1 e2 : 'D) : 'D[H] :=
  \dirac_(i , j) \sum_(k : {set L}) (e1 k j \o e2 i k : 'F[H]_(i,j)).
Definition ddot_fun_def (e1 e2 : 'D) : 'D[H] := 
  \sum_d11 \sum_d12 \sum_d21 \sum_d22 dset (e1 d11 d12 \· e2 d21 d22).
Definition dten_fun_def (e1 e2 : 'D) : 'D[H] := 
  \sum_d11 \sum_d12 \sum_d21 \sum_d22 dset (e1 d11 d12 \⊗ e2 d21 d22).
Definition dlin_fun := nosimpl dlin_fun_def.
Definition dket_fun := nosimpl dket_fun_def.
Definition dbra_fun := nosimpl dbra_fun_def.
Definition dnum_fun := nosimpl dnum_fun_def.
Definition dconj_fun := nosimpl dconj_fun_def.
Definition dtr_fun := nosimpl dtr_fun_def.
Definition dadj_fun := nosimpl dadj_fun_def.
Definition dmul_fun := nosimpl dmul_fun_def.
Definition ddot_fun := nosimpl ddot_fun_def.
Definition dten_fun := nosimpl dten_fun_def.
Definition dlin := locked_with fold_key dlin_fun.
Definition dket := locked_with fold_key dket_fun.
Definition dbra := locked_with fold_key dbra_fun.
Definition dnum := locked_with fold_key dnum_fun.
Definition dconj := locked_with fold_key dconj_fun.
Definition dtr := locked_with fold_key dtr_fun.
Definition dadj := locked_with fold_key dadj_fun.
Definition dmul := locked_with fold_key dmul_fun.
Definition ddot := locked_with fold_key ddot_fun.
Definition dten := locked_with fold_key dten_fun.
Lemma dlin_unfold : dlin = (fun S T (f: 'F_(S,T)) => dset f).
Proof. by rewrite [LHS](unlock [unlockable of _]). Qed.
Lemma dket_unfold : dket = (fun S (v : 'H_S) => dset (v2f v)).
Proof. by rewrite [LHS](unlock [unlockable of _]). Qed.
Lemma dbra_unfold : dbra = (fun S (v : 'H_S) => dset (v2df v)).
Proof. by rewrite [LHS](unlock [unlockable of _]). Qed.
Lemma dnum_unfold : dnum = (fun (c : C) => dset (s2sf c)).
Proof. by rewrite [LHS](unlock [unlockable of _]). Qed.
Lemma dconj_unfold : dconj = (fun (e : 'D) => \dirac_(i,j) (e i j)^C).
Proof. by rewrite [LHS](unlock [unlockable of _]). Qed.
Lemma dtr_unfold : dtr = (fun   (e : 'D) => \dirac_(i,j) (e j i)^T).
Proof. by rewrite [LHS](unlock [unlockable of _]). Qed.
Lemma dadj_unfold : dadj = (fun  (e : 'D) => \dirac_(i,j) (e j i)^A).
Proof. by rewrite [LHS](unlock [unlockable of _]). Qed.
Lemma dmul_unfold : dmul = (fun e1 e2 => 
  \dirac_(i , j) \sum_(k : {set L}) (e1 k j \o e2 i k : 'F[H]_(i,j))).
Proof. by rewrite [LHS](unlock [unlockable of _]). Qed.
Lemma ddot_unfold : ddot = (fun e1 e2 => 
  \sum_d11 \sum_d12 \sum_d21 \sum_d22 dset (e1 d11 d12 \· e2 d21 d22)).
Proof. by rewrite [LHS](unlock [unlockable of _]). Qed.
Lemma dten_unfold : dten = (fun e1 e2 => 
  \sum_d11 \sum_d12 \sum_d21 \sum_d22 dset (e1 d11 d12 \⊗ e2 d21 d22)).
Proof. by rewrite [LHS](unlock [unlockable of _]). Qed.

Lemma dotd_pairE (e1 e2 : 'D[H]) : 
  ddot e1 e2 = \sum_d1 \sum_d2 dset (e1 d1.1 d1.2 \· e2 d2.1 d2.2).
Proof. by rewrite ddot_unfold pair_big; apply eq_bigr=>d1 _; rewrite pair_big. Qed.
Lemma tend_pairE (e1 e2 : 'D[H]) : 
  dten e1 e2 = \sum_d1 \sum_d2 dset (e1 d1.1 d1.2 \⊗ e2 d2.1 d2.2).
Proof. by rewrite dten_unfold pair_big; apply eq_bigr=>d1 _; rewrite pair_big. Qed.

Definition d2v (S : {set L}) (e : 'D) : 'H[H]_S := f2v (e set0 S).
Definition d2dv (S : {set L}) (e : 'D) : 'H[H]_S := df2v (e S set0).
Definition d2f (S T : {set L}) (e : 'D) : 'F[H]_(S,T) := e S T.
Definition d2c (e : 'D[H]) := sf2s (e set0 set0).

Fact tens_key : unit. Proof. by []. Qed.
Fact dots_key : unit. Proof. by []. Qed.
Definition bigten := locked_with tens_key (@idfun 'D[H]).
Definition bigdot := locked_with dots_key (@idfun 'D[H]).
Local Canonical ten_unlockable := [unlockable fun bigten].
Local Canonical dot_unlockable := [unlockable fun bigdot].
Lemma bigten_unfold : bigten = id.
Proof. by rewrite unlock. Qed.
Lemma bigdot_unfold : bigdot = id.
Proof. by rewrite unlock. Qed.
Definition bigd := (bigten_unfold, bigdot_unfold). 

Lemma dset_eqFnd S T S' T' (f: 'F[H]_(S,T)) (g: 'F_(S',T')) :
  f =c g -> dset f = dset g.
Proof. by move=>P; move: (eq_FndP P); rewrite !to_FndK=><-; rewrite dset_cast. Qed.

Lemma dlin_eqFnd S T S' T' (f: 'F[H]_(S,T)) (g: 'F_(S',T')) :
  f =c g -> dlin f = dlin g.
Proof. by rewrite dlin_unfold; apply dset_eqFnd. Qed.

Lemma dket_eqHnd S S' (f: 'H[H]_S) (g: 'H_S') :
  f =v g -> dket f = dket g.
Proof. by move=>Pe; move: (eq_Hnd1 Pe)=>/= Pv; case: _ / Pv g Pe => g /to_Hnd_inj ->. Qed.

Lemma dbra_eqHnd S S' (f: 'H[H]_S) (g: 'H_S') :
  f =v g -> dbra f = dbra g.
Proof. by move=>Pe; move: (eq_Hnd1 Pe)=>/= Pv; case: _ / Pv g Pe => g /to_Hnd_inj ->. Qed.

End DiracAlgebra.

Ltac to_Fnd := try (match goal with
  | [ |- dset _ = dset _ ] => apply/dset_eqFnd
  | [ |- dlin _ = dlin _ ] => apply/dlin_eqFnd
  | [ |- dket _ = dket _ ] => apply/dket_eqHnd
  | [ |- dbra _ = dbra _ ] => apply/dbra_eqHnd
  | [ |- _ ] => apply/to_Fnd_inj
  | [ |- _ ] => apply/to_Hnd_inj
  end); rewrite ?(to_FndE, Fnd_cast, to_Fnd_tens, to_HndE, Hnd_cast, to_Hnd_tens).

Notation "':1'"  := (@dnum _ _ 1) : dirac_scope.
Notation "c %:D" := (@dnum _ _ c) : dirac_scope.
Notation "'| v >" := (@dket _ _ _ v%VF) : dirac_scope.
Notation "'< v |"  := (@dbra _ _ _ v%VF) : dirac_scope.
Notation "'[ M ]"   := (@dlin _ _ _ _ M%VF) : dirac_scope.
Notation "'\1_' S" := (@dlin _ _ S%SET S%SET \1) : dirac_scope.
Notation "e '^C'" := (dconj e) : dirac_scope.
Notation "e '^T'" := (dtr e) : dirac_scope.
Notation "e '^A'" := (dadj e) : dirac_scope.
Notation " 'o%D' "  := (@dmul _ _) : fun_scope.
Notation " '·%D' "  := (@ddot _ _) : fun_scope.
Notation " '⊗%D' " := (@dten _ _) : fun_scope.
Notation " f '\o' g "  := (dmul f g) : dirac_scope.
Notation " f '\⊗' g " := (dten f g) : dirac_scope.
Notation " f '\·' g "  := (ddot f g) : dirac_scope.

Notation "\ten_ ( i <- r | P ) F" :=
  (bigten (\big[ ⊗%D / :1 ]_(i <- r | P%B) F%D )) : dirac_scope.
Notation "\ten_ ( i <- r ) F" :=
  (bigten (\big[ ⊗%D / :1 ]_(i <- r) F%D)) : dirac_scope.
Notation "\ten_ ( m <= i < n | P ) F" :=
  (bigten ((\big[ ⊗%D / :1 ]_( m%N <= i < n%N | P%B) F%D)%BIG)) 
    : dirac_scope.
Notation "\ten_ ( m <= i < n ) F" :=
  (bigten ((\big[ ⊗%D / :1 ]_(m%N <= i < n%N) F%D)%BIG)) : dirac_scope.
Notation "\ten_ ( i | P ) F" :=
  (bigten (\big[ ⊗%D / :1 ]_(i | P%B) F%D)) : dirac_scope.
Notation "\ten_ i F" :=
  (bigten (\big[ ⊗%D / :1 ]_i F%D)) : dirac_scope.
Notation "\ten_ ( i : t | P ) F" :=
  (bigten (\big[ ⊗%D / :1 ]_(i : t | P%B) F%D)) (only parsing) 
    : dirac_scope.
Notation "\ten_ ( i : t ) F" :=
  (bigten (\big[ ⊗%D / :1 ]_(i : t) F%D)) (only parsing) : dirac_scope.
Notation "\ten_ ( i < n | P ) F" :=
  (bigten ((\big[ ⊗%D / :1 ]_(i < n%N | P%B) F%D)%BIG)) : dirac_scope.
Notation "\ten_ ( i < n ) F" :=
  (bigten ((\big[ ⊗%D / :1 ]_(i < n%N) F%D)%BIG)) : dirac_scope.
Notation "\ten_ ( i 'in' A | P ) F" :=
  (bigten (\big[ ⊗%D / :1 ]_(i in A | P%B) F%D)) : dirac_scope.
Notation "\ten_ ( i 'in' A ) F" :=
  (bigten (\big[ ⊗%D / :1 ]_(i in A) F%D)) : dirac_scope.

Notation "\dot_ ( i <- r | P ) F" :=
  (bigdot (\big[ ·%D / :1 ]_(i <- r | P%B) F%D )) : dirac_scope.
Notation "\dot_ ( i <- r ) F" :=
  (bigdot (\big[ ·%D / :1 ]_(i <- r) F%D)) : dirac_scope.
Notation "\dot_ ( m <= i < n | P ) F" :=
  (bigdot ((\big[ ·%D / :1 ]_( m%N <= i < n%N | P%B) F%D)%BIG)) 
    : dirac_scope.
Notation "\dot_ ( m <= i < n ) F" :=
  (bigdot ((\big[ ·%D / :1 ]_(m%N <= i < n%N) F%D)%BIG)) : dirac_scope.
Notation "\dot_ ( i | P ) F" :=
  (bigdot (\big[ ·%D / :1 ]_(i | P%B) F%D)) : dirac_scope.
Notation "\dot_ i F" :=
  (bigdot (\big[ ·%D / :1 ]_i F%D)) : dirac_scope.
Notation "\dot_ ( i : t | P ) F" :=
  (bigdot (\big[ ·%D / :1 ]_(i : t | P%B) F%D)) (only parsing) 
    : dirac_scope.
Notation "\dot_ ( i : t ) F" :=
  (bigdot (\big[ ·%D / :1 ]_(i : t) F%D)) (only parsing) : dirac_scope.
Notation "\dot_ ( i < n | P ) F" :=
  (bigdot ((\big[ ·%D / :1 ]_(i < n%N | P%B) F%D)%BIG)) : dirac_scope.
Notation "\dot_ ( i < n ) F" :=
  (bigdot ((\big[ ·%D / :1 ]_(i < n%N) F%D)%BIG)) : dirac_scope.
Notation "\dot_ ( i 'in' A | P ) F" :=
  (bigdot (\big[ ·%D / :1 ]_(i in A | P%B) F%D)) : dirac_scope.
Notation "\dot_ ( i 'in' A ) F" :=
  (bigdot (\big[ ·%D / :1 ]_(i in A) F%D)) : dirac_scope.

Section DiracBigLock.
Context {L : finType} (H : L -> chsType).

Lemma bigtenlr (I J : Type) (ri : seq I) (Pi : pred I) (Fi : I -> 'D[H]) 
  (rj : seq J) (Pj : pred J) (Fj : J -> 'D): 
    bigten (dten (\big[⊗%D/:1]_(i <- ri | Pi i) Fi i) 
    (\big[@dten _ _ /:1]_(j <- rj | Pj j) Fj j)) = 
    (\ten_(i <- ri | Pi i) Fi i) \⊗ (\ten_(j <- rj | Pj j) Fj j) .
Proof. by rewrite bigd. Qed.

Lemma bigtenr (I : Type) (r : seq I) (P : pred I) (e1 : 'D[H]) (F : I -> 'D): 
  bigten (dten e1 (\big[⊗%D/:1]_(j <- r | P j) F j)) = dten e1 (\ten_(i <- r | P i) F i).
Proof. by rewrite bigd. Qed.

Lemma bigtenl (I : Type) (r : seq I) (P : pred I) (e1 : 'D[H]) (F : I -> 'D[H]): 
  bigten (dten (\big[⊗%D/:1]_(j <- r | P j) F j) e1) = dten (\ten_(i <- r | P i) F i) e1.
Proof. by rewrite bigd. Qed.

Lemma bigtenE (I : Type) (r : seq I) (P : pred I) (F : I -> 'D[H]): 
  \big[⊗%D/:1]_(j <- r | P j) F j = \ten_(i <- r | P i) F i.
Proof. by rewrite bigd. Qed.

Lemma bigdotlr (I J : Type) (ri : seq I) (Pi : pred I) (Fi : I -> 'D[H]) 
  (rj : seq J) (Pj : pred J) (Fj : J -> 'D[H]): 
  bigdot (ddot (\big[·%D/:1]_(i <- ri | Pi i) Fi i) 
  (\big[·%D/:1]_(j <- rj | Pj j) Fj j)) = 
  (\dot_(i <- ri | Pi i) Fi i) \· (\dot_(j <- rj | Pj j) Fj j) .
Proof. by rewrite bigd. Qed.

Lemma bigdotr (I : Type) (r : seq I) (P : pred I) (e1 : 'D[H]) (F : I -> 'D[H]): 
  bigdot (ddot e1 (\big[·%D/:1]_(j <- r | P j) F j)) = ddot e1 (\dot_(i <- r | P i) F i).
Proof. by rewrite bigd. Qed.

Lemma bigdotl (I : Type) (r : seq I) (P : pred I) (e1 : 'D[H]) (F : I -> 'D[H]): 
  bigdot (ddot (\big[·%D/:1]_(j <- r | P j) F j) e1) = ddot (\dot_(i <- r | P i) F i) e1.
Proof. by rewrite bigd. Qed.

Lemma bigdotE (I : Type) (r : seq I) (P : pred I) (F : I -> 'D[H]): 
  \big[·%D/:1]_(j <- r | P j) F j = \dot_(i <- r | P i) F i.
Proof. by rewrite bigd. Qed.

Definition bigd_lock := (bigtenE, bigdotE).

Definition bigdE := (bigtenlr, bigtenr, bigtenl, bigdotlr, bigdotr, bigdotl).
End DiracBigLock.

(* after using bigop theory, first run this to lock back *)
(* Ltac bigdE := rewrite ?bigd; rewrite ?bigd_locklr. *)
(* move *)
Lemma exchange_bigR (R : Type) (idx : R) (op : Monoid.com_law idx) 
  (I J K : Type) (rI : seq I) (rJ : seq J) (rK : seq K) (P : pred I) 
    (Q : pred J) (S : pred K) (F : I -> J -> K -> R) : 
    \big[op/idx]_(i <- rI | P i) \big[op/idx]_(j <- rJ | Q j) 
        \big[op/idx]_(k <- rK | S k) F i j k = \big[op/idx]_(j <- rJ | Q j) 
            \big[op/idx]_(k <- rK | S k) \big[op/idx]_(i <- rI | P i) F i j k.
Proof. by rewrite exchange_big; apply eq_bigr=>i Pi; apply exchange_big. Qed.

Section DiracOpCorrect.
Context {L : finType} (H : L -> chsType).
Local Canonical dset_linear.

Lemma dlin_cast S T S' T' (eqST: (S = S') * (T = T')) (f: 'F[H]_(S,T)) :
  '[castlf eqST f] = '[f].
Proof. by rewrite dlin_unfold dset_cast. Qed.
Lemma dket_cast S S' (eqS : S = S') (v : 'H[H]_S) :
  '| casths eqS v > = '| v >.
Proof. by case: S' / eqS; rewrite casths_id. Qed.
Lemma dbra_cast S S' (eqS : S = S') (v : 'H[H]_S) :
  '< casths eqS v | = '< v |.
Proof. by case: S' / eqS; rewrite casths_id. Qed.

Lemma dlinK S T : cancel (@dlin _ H S T) (@d2f _ H S T).
Proof. by move=>f; rewrite /d2f dlin_unfold dsetii. Qed.
Lemma dlin_inj S T : injective (@dlin _ H S T).
Proof. exact: (can_inj (@dlinK S T)). Qed.
Lemma dketK S : cancel (@dket _ H S) (@d2v _ H S).
Proof. by move=>f; rewrite dket_unfold /d2v dsetii v2fK. Qed.
Lemma dket_inj S : injective (@dket _ H S).
Proof. exact: (can_inj (@dketK S)). Qed.
Lemma dbraK S : cancel (@dbra _ H S) (@d2dv _ H S).
Proof. by move=>f; rewrite dbra_unfold /d2dv dsetii v2dfK. Qed.
Lemma dbra_inj S : injective (@dbra _ H S).
Proof. exact: (can_inj (@dbraK S)). Qed.
Lemma dnumK : cancel (@dnum _ H) (@d2c _ H).
Proof. by move=>f; rewrite dnum_unfold /d2c dsetii s2sfK. Qed.
Lemma dnum_inj : injective (@dnum _ H).
Proof. exact: (can_inj (@dnumK)). Qed.

Lemma dlin_is_linear S T : linear (@dlin _ H S T).
Proof. by move=>a x y; rewrite dlin_unfold linearP. Qed.
Canonical dlin_linear S T := Linear (@dlin_is_linear S T).

Lemma dket_is_linear S : linear (@dket _ H S).
Proof. by move=>a x y; rewrite dket_unfold !linearP. Qed.
Canonical dket_linear S := Linear (@dket_is_linear S).

Lemma dbra_is_antilinear S : linear_for (conjC \; *:%R) (@dbra _ H S).
Proof. by move=>a x y; rewrite dbra_unfold !linearP. Qed.
Canonical dbra_antilinear S := Linear (@dbra_is_antilinear S).

Lemma dnum_is_additive : additive (@dnum _ H).
Proof. by move=>x y; rewrite dnum_unfold raddfB linearB. Qed.
Canonical dnum_additive := Additive dnum_is_additive.

Lemma d2f_is_linear S T : linear (@d2f _ H S T).
Proof. by move=>a x y; rewrite /d2f !diracE. Qed.
Canonical d2f_linear S T := Linear (@d2f_is_linear S T).

Lemma d2v_is_linear S : linear (@d2v _ H S).
Proof. by move=>a x y; rewrite /d2v !diracE linearP. Qed.
Canonical d2v_linear S := Linear (@d2v_is_linear S).

Lemma d2dv_is_antilinear S : linear_for (conjC \; *:%R) (@d2dv _ H S).
Proof. by move=>a x y; rewrite /d2dv !diracE linearP. Qed.
Canonical d2dv_antilinear S := Linear (@d2dv_is_antilinear S).

Lemma d2c_is_scalar : scalar (@d2c _ H).
Proof. by move=>a x y; rewrite /d2c !diracE linearP. Qed.
Canonical d2c_scalar := Linear (@d2c_is_scalar).

(* correctness of compoistion operators *)
Lemma addd_correct S T (f g: 'F[H]_(S,T)) :
  '[f] + '[g] = '[f + g].
Proof. by rewrite linearD. Qed.

Lemma oppd_correct S T (f : 'F[H]_(S,T)) : 
  - '[f] = '[- f].
Proof. by rewrite linearN. Qed.

Lemma scaled_correct S T (c: C) (f : 'F[H]_(S,T)) :
  c *: '[f] = '[c *: f].
Proof. by rewrite linearZ. Qed.

Definition comp_lfun0 := (comp_lfun0l, comp_lfun0r).

Lemma muld_correct S T W (f: 'F[H]_(S,T)) (g: 'F_(W,S)) :
    '[f] \o '[g] = '[f \o g].
Proof.
apply/diracP=>d1 d2; rewrite dlin_unfold dmul_unfold [LHS]diracE.
rewrite (bigD1 S)//= big1=>[i P|].
by rewrite dset_eq0l ?comp_lfun0l.
case E: (d1 == W); last by rewrite ![_ d1 _]dset_eq0l ?E// comp_lfun0r addr0.
case E1: (d2 == T); last by rewrite/= ![_ _ _ d2]dset_eq0r ?E1// comp_lfun0l addr0.
move: E E1=>/eqP->/eqP->; by rewrite !dsetii addr0.
Qed.

Lemma tend_correct S T S' T' (f: 'F[H]_(S,T)) (g: 'F_(S', T')) :
    '[f] \⊗ '[g] = '[f \⊗ g].
Proof.
apply/diracP=>d1 d2; rewrite dlin_unfold tend_pairE.
rewrite (bigD1 (S,T))//= (bigD1 (S',T'))//= !big1=>[[i1 i2]/=P|[i1 i2]/=P|].
by rewrite [dset g _ _]dset_eq0p// tenf0 linear0.
by rewrite big1=>[j _|]; rewrite 1?dset_eq0p// ?ten0f ?linear0// diracE.
by rewrite !addr0 !dsetii.
Qed.

Lemma dotd_correct S T S' T' (f: 'F[H]_(S,T)) (g: 'F[H]_(S', T')) :
    '[f] \· '[g] = '[f \· g].
Proof.
apply/diracP=>d1 d2; rewrite dlin_unfold dotd_pairE. 
rewrite (bigD1 (S,T))//= (bigD1 (S',T'))//= !big1=>[[i1 i2]/=P|[i1 i2]/=P|]. 
by rewrite [dset g _ _]dset_eq0p// dotf0 linear0.
by rewrite big1=>[j _|]; rewrite 1?dset_eq0p// ?dot0f ?linear0// diracE.
by rewrite !addr0 !dsetii.
Qed.

Lemma sdotd_correct S T (f: 'F[H]_S) (g: 'F[H]_T) :
  '[f] \· '[g] = '[f \O g].
Proof. by rewrite sdot_lfun_unfold dlin_cast dotd_correct. Qed.

Lemma conjd_correct S T (f : 'F[H]_(S,T)) :
  '[f]^C = '[f^C].
Proof.
apply/diracP=>i j; rewrite dconj_unfold dlin_unfold diracE.
case E: ((i,j) == (S,T)); first by move/eqP in E; inversion E; rewrite !dsetii.
by move/negbT: E=>E; rewrite !dset_eq0p// linear0.
Qed.

Lemma adjd_correct S T (f : 'F[H]_(S,T)) :
  '[f]^A = '[f^A].
Proof.
apply/diracP=>i j; rewrite dadj_unfold dlin_unfold diracE.
case E: ((i,j) == (T,S)); first by move/eqP in E; inversion E; rewrite !dsetii.
move/negbT: E=>E; rewrite !dset_eq0p// ?linear0//.
by move: E; apply contraNN=>/eqP P; inversion P.
Qed.

Lemma trd_correct S T (f : 'F[H]_(S,T)) :
  '[f]^T = '[f^T].
Proof.
apply/diracP=>i j; rewrite dtr_unfold dlin_unfold diracE.
case E: ((i,j) == (T,S)); first by move/eqP in E; inversion E; rewrite !dsetii.
move/negbT: E=>E; rewrite !dset_eq0p// ?linear0//.
by move: E; apply contraNN=>/eqP P; inversion P.
Qed.

Definition dirac_correct := (addd_correct, oppd_correct, 
  scaled_correct, muld_correct, tend_correct, dotd_correct, 
  conjd_correct, adjd_correct, trd_correct ).

End DiracOpCorrect.

(* we locally use ringType (+ , \⊗) to ease the proof of theorems *)
Section DiracTheory.
Context {L : finType} (H : L -> chsType).
Implicit Type (e x y z: 'D[H]) (a b c : C) (S T : {set L}).

Local Canonical dset_linear.
Local Notation "c %:D" := (@dnum _ H c).
Local Notation "⊗%D" := (@dten _ H).
Local Notation "o%D"  := (@dmul _ H).
Local Notation "·%D" := (@ddot _ H).
Local Notation ":1" := (@dnum _ H 1).
Local Notation dconj := (@dconj _ H).
Local Notation dtr := (@dtr _ H).
Local Notation dadj := (@dadj _ H).

Lemma dlin_dec x : \sum_i '[x i.1 i.2] = x.
Proof. by rewrite dlin_unfold dset_dec. Qed.

Lemma dlin_id S T (f : 'F[H]_(S,T)) : '[f] S T = f.
Proof. by rewrite dlin_unfold dsetii. Qed.

Lemma dlin_eq0l S T S' T' (f : 'F[H]_(S,T)) :
  S' != S -> '[f] S' T' = 0.
Proof. rewrite dlin_unfold; exact: dset_eq0l. Qed.

Lemma dlin_eq0r S T S' T' (f : 'F[H]_(S,T)) :
  T' != T -> '[f] S' T' = 0.
Proof. rewrite dlin_unfold; exact: dset_eq0r. Qed.

Lemma dlin_eq0p S T S' T' (f : 'F[H]_(S,T)) :
  (S',T') != (S,T) -> '[f] S' T' = 0.
Proof. rewrite dlin_unfold; exact: dset_eq0p. Qed.

Lemma dket_lin S (v : 'H[H]_S) : '| v > = '[v2f v].
Proof. by rewrite dlin_unfold dket_unfold. Qed.
Lemma dbra_lin S (v : 'H[H]_S) : '< v | = '[v2df v].
Proof. by rewrite dlin_unfold dbra_unfold. Qed.
Lemma dlin_ket S (f : 'FV[H]_S) : '[f] = '|f2v f>.
Proof. by rewrite dket_lin f2vK. Qed.
Lemma dlin_bra S (f : 'FdV[H]_S) : '[f] = '<df2v f|.
Proof. by rewrite dbra_lin df2vK. Qed.
Lemma dlin_num (f : 'F[H]_set0) : '[f] = (sf2s f)%:D.
Proof. by rewrite dlin_unfold dnum_unfold sf2sK. Qed.
Lemma dket_num (v : 'H[H]_set0) : '|v> = (sv2s v)%:D.
Proof.
rewrite dket_unfold dnum_unfold; f_equal; apply/lfunPD=>i.
by rewrite v2fE /s2sf/sv2s [v]dec_sv idx0E linearZr/= dv_dot eqxx scale1r lfunE/= lfunE/= mulr1.
Qed.
Lemma dbra_num (v : 'H[H]_set0) : '<v| = (sv2s v)^*%:D.
Proof. by rewrite dbra_lin -v2f_adj sfAC v2f_conj -dket_lin dket_num sv2s_conj. Qed.
Lemma dnum_lin c : c%:D = '[s2sf c].
Proof. by rewrite dlin_num s2sfK. Qed.
Lemma dnum_ket c : c%:D = '|s2sv c>.
Proof. by rewrite dket_num s2svK. Qed.
Lemma dnum_bra c : c%:D = '<s2sv c^*|.
Proof. by rewrite dbra_num s2svK conjCK. Qed.

Lemma dnumI : :1 = \1_set0.
Proof. by rewrite dnum_unfold dlin_unfold; f_equal; rewrite /s2sf scale1r. Qed.

Lemma tendA : associative ⊗%D.
Proof.
move=>f g h; rewrite !tend_pairE [RHS]exchange_big/=.
rewrite  (eq_bigr (fun d1 => \sum_d0 \sum_d3 \sum_d2
 dset (f d1.1 d1.2 \⊗ (dset (g d0.1 d0.2 \⊗ h d3.1 d3.2) d2.1 d2.2)))).
2: rewrite  [RHS](eq_bigr (fun j => \sum_d1 \sum_d2 \sum_i
(dset (dset (f d1.1 d1.2 \⊗ g d2.1 d2.2) i.1 i.2 \⊗ h j.1 j.2)))).
1,2: by move=>i _; rewrite exchange_bigR/= exchange_bigR/=; apply eq_bigr=>j _;
rewrite dirac_sumE 1 ?linear_suml/= 2 ?linear_sum/=; apply eq_bigr=>k _;
rewrite dirac_sumE 1 ?linear_suml/= 2 ?linear_sum/=; apply eq_bigr.
rewrite [RHS]exchange_bigR/=; apply eq_bigr=>[[i1 i2]] _; 
apply eq_bigr=>[[j1 j2]] _; apply eq_bigr=>[[k1 k2]] _.
rewrite (bigD1 (j1 :|: k1, j2 :|: k2))// big1/=.
2: rewrite (bigD1 (i1 :|: j1, i2 :|: j2))// big1/=.
1,2 : by move=>[l1 l2]/=nl; rewrite dset_eq0p// ?tenf0 ?ten0f linear0.
by rewrite !dsetii !addr0; to_Fnd; rewrite tenFA.
Qed.

Lemma tendC : commutative ⊗%D.
Proof.
move=>f g. rewrite 2 !tend_pairE exchange_big/=.
apply eq_bigr=>[[i1 i2]] _; apply eq_bigr=>[[j1 j2]] _/=.
by to_Fnd; rewrite tenFC.
Qed.

Lemma ten1d : left_id :1 ⊗%D.
Proof.
move=>f. rewrite tend_pairE (bigD1 (set0,set0))// big1/=.
move=>[i1 i2]/= ni0. rewrite big1// =>? _/=.
by rewrite dnumI dlin_eq0p// ten0f linear0.
rewrite addr0 -[RHS]dset_dec; apply eq_bigr=>i _.
by rewrite dnumI dlin_id; to_Fnd; rewrite ten1F.
Qed.

Lemma tend1 : right_id :1 ⊗%D.
Proof. by move=>f; rewrite tendC ten1d. Qed.

Lemma linear_tend f : linear (⊗%D f).
Proof.
move=>a v w. rewrite !tend_pairE linear_sum -big_split/=; apply eq_bigr=>i _/=.
rewrite linear_sum -big_split; apply eq_bigr=>j _/=.
by rewrite !diracE !linearP/=.
Qed.
Canonical tend_additive f := Additive (@linear_tend f).
Canonical tend_linear f := Linear (@linear_tend f).
Definition tendr f := (⊗%D)^~ f.
Lemma linear_tendr f : linear (@tendr f).
Proof. by move=>a v w; rewrite/tendr tendC linearP/= ![f \⊗ _]tendC. Qed.
Canonical tendr_additive f := Additive (@linear_tendr f).
Canonical tendr_linear f := Linear (@linear_tendr f).
Canonical tend_rev := [revop (@tendr) of (⊗%D)].
Canonical tend_is_bilinear := [bilinear of (⊗%D)].

Lemma tendAC x y z : x \⊗ y \⊗ z = x \⊗ z \⊗ y.
Proof. by rewrite -tendA [y \⊗ z]tendC tendA. Qed.
Lemma tendCA x y z : x \⊗ (y \⊗ z) = y \⊗ (x \⊗ z).
Proof. by rewrite tendC tendAC -tendA. Qed.
Lemma tendACA x y z t : x \⊗ y \⊗ (z \⊗ t) = x \⊗ z \⊗ (y \⊗ t).
Proof. by rewrite -!tendA (tendCA y). Qed.

Lemma ten0d : left_zero 0 ⊗%D. Proof. exact: linear0l. Qed.
Lemma tend0 : right_zero 0 ⊗%D. Proof. exact: linear0r. Qed.
Lemma tendDl : left_distributive ⊗%D +%R. 
Proof. by move=>x y z; rewrite linearDl. Qed.
Lemma tendDr : right_distributive ⊗%D +%R.
Proof. by move=>x y z; rewrite linearD. Qed.
Lemma tendN x y : x \⊗ (- y) = - (x \⊗ y). Proof. exact: raddfN. Qed.
Lemma tendN1 x : x \⊗ -:1 = - x. Proof. by rewrite tendN tend1. Qed.
Lemma tendBr z : {morph ⊗%D z : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma tendMnr z n : {morph ⊗%D z : x / x *+ n}. Proof. exact: raddfMn. Qed.
Definition tendnAr := tendMnr.
Lemma tendMNnr z n : {morph ⊗%D z : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma tend_sumr z I r (P : pred I) E :
  z \⊗ (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (z \⊗ E i).
Proof. exact: raddf_sum. Qed.
Lemma tendZr z a : {morph ⊗%D z : x / a *: x}. Proof. exact: linearZ. Qed.
Lemma tendPr z a : {morph ⊗%D z : u v / a *: u + v}. Proof. exact: linearP. Qed.
Lemma tenNd x y : (- x) \⊗ y = - (x \⊗ y). Proof. exact: linearNl. Qed.
Lemma tenN1d x : -:1 \⊗ x = - x. Proof. by rewrite tenNd ten1d. Qed.
Lemma tendNN x y : (- x) \⊗ (- y) = x \⊗ y. Proof. by rewrite tendN tenNd opprK. Qed.
Lemma tendBl z : {morph ⊗%D^~ z : x y / x - y}. Proof. exact: linearBl. Qed.
Lemma tendMnl z n : {morph ⊗%D^~ z : x / x *+ n}. Proof. exact: linearMnl. Qed.
Definition tendnAl := tendMnl.
Lemma tendMNnl z n : {morph ⊗%D^~ z : x / x *- n}. Proof. exact: linearMNnl. Qed.
Lemma tend_suml z I r (P : pred I) E :
  (\sum_(i <- r | P i) E i) \⊗ z = \sum_(i <- r | P i) (E i \⊗ z).
Proof. exact: linear_suml. Qed.
Lemma tendZl z a : {morph ⊗%D^~ z : x / a *: x}. Proof. exact: linearZl. Qed.
Lemma tendPl z a : {morph ⊗%D^~ z : u v / a *: u + v}. Proof. exact: linearPl. Qed.
Lemma tendZlr x y a b : (a *: x) \⊗ (b *: y) = a *: (b *: (x \⊗ y)). 
Proof. exact: linearZlr. Qed.
Lemma tendZrl x y a b : (a *: x) \⊗ (b *: y) = b *: (a *: (x \⊗ y)). 
Proof. exact: linearZrl. Qed.

Lemma oned_neq0 : (:1 : 'D[H]) != 0.
Proof.
apply/eqP=> /diracP/(_ set0 set0)/eqP.
by rewrite dnumI dlin_id diracE oner_eq0.
Qed.

Definition tend_comRingMixin :=
  ComRingMixin tendA tendC ten1d tendDl oned_neq0.
Definition tend_ringType := RingType 'D[H] tend_comRingMixin.

Lemma muldA : associative o%D.
Proof.
move=>x y z; rewrite dmul_unfold.
apply/diracP=>i j; rewrite !diracE.
under eq_bigr do rewrite !diracE linear_sumr/=.
rewrite exchange_big/=. apply eq_bigr=>k _.
rewrite diracE/= linear_suml/=. 
by under eq_bigr do rewrite comp_lfunA.
Qed.

Lemma linear_muld f : linear (o%D f).
Proof.
move=>a v w; apply/diracP=>i j; rewrite dmul_unfold.
rewrite !diracE !linear_sum/= -big_split; apply eq_bigr=>k _/=.
by rewrite !diracE linearPr/=.
Qed.
Canonical muld_additive f := Additive (@linear_muld f).
Canonical muld_linear f := Linear (@linear_muld f).
Definition muldr f := (o%D)^~ f.
Lemma linear_muldr f : linear (@muldr f).
Proof.
move=>a v w; apply/diracP=>i j; rewrite /muldr dmul_unfold.
rewrite !diracE !linear_sum/= -big_split; apply eq_bigr=>k _/=.
by rewrite !diracE linearPl/=.
Qed.
Canonical muldr_additive f := Additive (@linear_muldr f).
Canonical muldr_linear f := Linear (@linear_muldr f).
Canonical muld_rev := [revop (@muldr) of o%D].
Canonical muld_is_bilinear := [bilinear of o%D].

Lemma mul0d : left_zero 0 o%D. Proof. exact: linear0l. Qed.
Lemma muld0 : right_zero 0 o%D. Proof. exact: linear0r. Qed.
Lemma muldDl : left_distributive o%D +%R. 
Proof. by move=>x y z; rewrite linearDl. Qed.
Lemma muldDr : right_distributive o%D +%R.
Proof. by move=>x y z; rewrite linearD. Qed.
Lemma muldN x y : x \o (- y) = - (x \o y). Proof. exact: raddfN. Qed.
Lemma muldBr z : {morph o%D z : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma muldMnr z n : {morph o%D z : x / x *+ n}. Proof. exact: raddfMn. Qed.
Definition muldnAr := muldMnr.
Lemma muldMNnr z n : {morph o%D z : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma muld_sumr z I r (P : pred I) E :
  z \o (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (z \o E i).
Proof. exact: raddf_sum. Qed.
Lemma muldZr z a : {morph o%D z : x / a *: x}. Proof. exact: linearZ. Qed.
Lemma muldPr z a : {morph o%D z : u v / a *: u + v}. Proof. exact: linearP. Qed.
Lemma mulNd x y : (- x) \o y = - (x \o y). Proof. exact: linearNl. Qed.
Lemma muldNN x y : (- x) \o (- y) = x \o y. Proof. by rewrite muldN mulNd opprK. Qed.
Lemma muldBl z : {morph o%D^~ z : x y / x - y}. Proof. exact: linearBl. Qed.
Lemma muldMnl z n : {morph o%D^~ z : x / x *+ n}. Proof. exact: linearMnl. Qed.
Definition muldnAl := muldMnl.
Lemma muldMNnl z n : {morph o%D^~ z : x / x *- n}. Proof. exact: linearMNnl. Qed.
Lemma muld_suml z I r (P : pred I) E :
  (\sum_(i <- r | P i) E i) \o z = \sum_(i <- r | P i) (E i \o z).
Proof. exact: linear_suml. Qed.
Lemma muldZl z a : {morph o%D^~ z : x / a *: x}. Proof. exact: linearZl. Qed.
Lemma muldPl z a : {morph o%D^~ z : u v / a *: u + v}. Proof. exact: linearPl. Qed.
Lemma muldZlr x y a b : (a *: x) \o (b *: y) = a *: (b *: (x \o y)). 
Proof. exact: linearZlr. Qed.
Lemma muldZrl x y a b : (a *: x) \o (b *: y) = b *: (a *: (x \o y)). 
Proof. exact: linearZrl. Qed.

Lemma dot1d : left_id :1 ·%D.
Proof.
move=>f; rewrite dotd_pairE (bigD1 (set0,set0))// big1/==>[[i1 i2] ni0|].
by rewrite big1// =>j _; rewrite /= dnumI dlin_eq0p// dot0f linear0.
rewrite addr0 -[RHS]dset_dec; apply eq_bigr=>[[i1 i2]] _/=.
by to_Fnd; rewrite dnumI dlin_id dot1F.
Qed.

Lemma dotd1 : right_id :1 ·%D.
Proof.
move=>f; rewrite dotd_pairE exchange_big (bigD1 (set0,set0))//= 
  [X in _ + X]big1/==>[[i1 i2] ni0|].
by rewrite big1// =>j _; rewrite /= dnumI dlin_eq0p// dotf0 linear0.
rewrite addr0 -[RHS]dset_dec; apply eq_bigr=>[[i1 i2]] _/=.
by to_Fnd; rewrite dnumI dlin_id dotF1.
Qed.

Lemma linear_dotd f : linear (·%D f).
Proof.
move=>a v w; rewrite !dotd_pairE linear_sum -big_split; apply eq_bigr=>i _/=.
rewrite linear_sum -big_split; apply eq_bigr=>j _/=.
by rewrite !diracE !linearP/=.
Qed.
Canonical dotd_additive f := Additive (@linear_dotd f).
Canonical dotd_linear f := Linear (@linear_dotd f).
Definition dotdr f := (·%D)^~ f.
Lemma linear_dotdr f : linear (@dotdr f).
Proof.
move=>a v w; rewrite /dotdr !dotd_pairE linear_sum -big_split; apply eq_bigr=>i _/=.
rewrite linear_sum -big_split; apply eq_bigr=>j _/=.
by rewrite !diracE !(linearP,linearPl)/=.
Qed.
Canonical dotdr_additive f := Additive (@linear_dotdr f).
Canonical dotdr_linear f := Linear (@linear_dotdr f).
Canonical dotd_rev := [revop (@dotdr) of ·%D].
Canonical dotd_is_bilinear := [bilinear of ·%D].

Lemma dot0d : left_zero 0 ·%D. Proof. exact: linear0l. Qed.
Lemma dotd0 : right_zero 0 ·%D. Proof. exact: linear0r. Qed.
Lemma dotdDl : left_distributive ·%D +%R. 
Proof. by move=>x y z; rewrite linearDl. Qed.
Lemma dotdDr : right_distributive ·%D +%R.
Proof. by move=>x y z; rewrite linearD. Qed.
Lemma dotdN x y : x \· (- y) = - (x \· y). Proof. exact: raddfN. Qed.
Lemma dotdN1 x : x \· -:1 = - x. Proof. by rewrite dotdN dotd1. Qed.
Lemma dotdBr z : {morph ·%D z : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma dotdMnr z n : {morph ·%D z : x / x *+ n}. Proof. exact: raddfMn. Qed.
Definition dotdnAr := dotdMnr.
Lemma dotdMNnr z n : {morph ·%D z : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma dotd_sumr z I r (P : pred I) E :
  z \· (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) (z \· E i).
Proof. exact: raddf_sum. Qed.
Lemma dotdZr z a : {morph ·%D z : x / a *: x}. Proof. exact: linearZ. Qed.
Lemma dotdPr z a : {morph ·%D z : u v / a *: u + v}. Proof. exact: linearP. Qed.
Lemma dotNd x y : (- x) \· y = - (x \· y). Proof. exact: linearNl. Qed.
Lemma dotN1d x : -:1 \· x = - x. Proof. by rewrite dotNd dot1d. Qed.
Lemma dotdNN x y : (- x) \· (- y) = x \· y. Proof. by rewrite dotdN dotNd opprK. Qed.
Lemma dotdBl z : {morph ·%D^~ z : x y / x - y}. Proof. exact: linearBl. Qed.
Lemma dotdMnl z n : {morph ·%D^~ z : x / x *+ n}. Proof. exact: linearMnl. Qed.
Definition dotdnAl := dotdMnl.
Lemma dotdMNnl z n : {morph ·%D^~ z : x / x *- n}. Proof. exact: linearMNnl. Qed.
Lemma dotd_suml z I r (P : pred I) E :
  (\sum_(i <- r | P i) E i) \· z = \sum_(i <- r | P i) (E i \· z).
Proof. exact: linear_suml. Qed.
Lemma dotdZl z a : {morph ·%D^~ z : x / a *: x}. Proof. exact: linearZl. Qed.
Lemma dotdPl z a : {morph ·%D^~ z : u v / a *: u + v}. Proof. exact: linearPl. Qed.
Lemma dotdZlr x y a b : (a *: x) \· (b *: y) = a *: (b *: (x \· y)). 
Proof. exact: linearZlr. Qed.
Lemma dotdZrl x y a b : (a *: x) \· (b *: y) = b *: (a *: (x \· y)). 
Proof. exact: linearZrl. Qed.

Lemma dconj_is_antilinear : linear_for (conjC \; *:%R) dconj.
Proof. by move=>a x y/=; apply/diracP=>i j; rewrite dconj_unfold !diracE linearP. Qed.
Canonical dconj_antilinear := Linear dconj_is_antilinear.
Lemma dadj_is_antilinear  : linear_for (conjC \; *:%R) dadj.
Proof. by move=>a x y/=; apply/diracP=>i j; rewrite dadj_unfold !diracE linearP. Qed.
Canonical dadj_antilinear := Linear dadj_is_antilinear.
Lemma dtr_is_linear  : linear dtr.
Proof. by move=>a x y/=; apply/diracP=>i j; rewrite dtr_unfold !diracE linearP. Qed.
Canonical dtr_linear := Linear dtr_is_linear.

Lemma conjd0 : 0^C = (0 : 'D[H]). Proof. exact: linear0. Qed.
Lemma conjdN : {morph dconj : x / - x}. Proof. exact: linearN. Qed.
Lemma conjdD : {morph dconj : x y / x + y}. Proof. exact: linearD. Qed.
Lemma conjdB : {morph dconj : x y / x - y}. Proof. exact: linearB. Qed.
Lemma conjdMn n : {morph dconj : x / x *+ n}. Proof. exact: linearMn. Qed.
Lemma conjdMNn n : {morph dconj : x / x *- n}. Proof. exact: linearMNn. Qed.
Lemma conjd_sum I r (P : pred I) (E : I -> 'D[H]) :
  (\sum_(i <- r | P i) E i)^C = \sum_(i <- r | P i) (E i)^C.
Proof. exact: linear_sum. Qed.
Lemma conjdZ a : {morph dconj : x / a *: x >-> a^* *: x}. Proof. exact: linearZ. Qed.
Lemma conjdP a : {morph dconj : x y / a *: x + y >-> a^* *: x + y}.
Proof. exact: linearP. Qed.
Lemma conjdI S : (\1_S : 'D[H])^C = \1_S.
Proof. by rewrite conjd_correct conjf1. Qed.
Lemma conjd1 : :1^C = (:1 : 'D[H]).
Proof. by rewrite dnumI conjd_correct conjf1. Qed.
Lemma conjdN1 : (-:1)^C = (-:1 : 'D[H]).
Proof. by rewrite conjdN conjd1. Qed.
Lemma conjdK : involutive dconj.
Proof. by move=>x; apply/diracP=>i j; rewrite dconj_unfold !diracE conjfK. Qed.
Lemma conjd_inj : injective dconj.
Proof. exact: (can_inj conjdK). Qed.
Lemma conjd_lin S T (f : 'F[H]_(S,T)) : '[f]^C = '[f^C].
Proof. by rewrite conjd_correct. Qed.
Lemma conjd_ket S (v : 'H[H]_S) : '|v>^C = '|v^*v>.
Proof. by rewrite !dket_lin conjd_lin v2f_conj. Qed.
Lemma conjd_bra S (v : 'H[H]_S) : '<v|^C = '<v^*v|.
Proof. by rewrite !dbra_lin conjd_lin v2df_conj. Qed.
Lemma conjd_num c : c%:D^C = c^*%:D.
Proof. by rewrite !dnum_lin conjd_lin s2sf_conj. Qed.
Lemma conjdM e1 e2 : (e1 \o e2)^C = e1^C \o e2^C.
Proof.
apply/diracP=>i j; rewrite dconj_unfold dmul_unfold !diracE linear_sum/=.
by apply eq_bigr=>s _; rewrite conjf_comp !diracE.
Qed.
Lemma conjdT e1 e2 : (e1 \⊗ e2)^C = e1^C \⊗ e2^C.
Proof.
rewrite -(dlin_dec e1) -(dlin_dec e2) tend_suml !conjd_sum tend_suml.
apply eq_bigr=>??; rewrite !tend_sumr conjd_sum; apply eq_bigr=>??. 
by rewrite !dirac_correct tenf_conj.
Qed.
Lemma conjdG e1 e2 : (e1 \· e2)^C = e1^C \· e2^C.
Proof.
rewrite -(dlin_dec e1) -(dlin_dec e2) dotd_suml !conjd_sum dotd_suml.
apply eq_bigr=>??; rewrite !dotd_sumr conjd_sum; apply eq_bigr=>??. 
by rewrite !dirac_correct dotf_conj.
Qed.

Lemma adjd0 : 0^A = (0 : 'D[H]). Proof. exact: linear0. Qed.
Lemma adjdN : {morph dadj : x / - x}. Proof. exact: linearN. Qed.
Lemma adjdD : {morph dadj : x y / x + y}. Proof. exact: linearD. Qed.
Lemma adjdB : {morph dadj : x y / x - y}. Proof. exact: linearB. Qed.
Lemma adjdMn n : {morph dadj : x / x *+ n}. Proof. exact: linearMn. Qed.
Lemma adjdMNn n : {morph dadj : x / x *- n}. Proof. exact: linearMNn. Qed.
Lemma adjd_sum I r (P : pred I) (E : I -> 'D[H]) :
  (\sum_(i <- r | P i) E i)^A = \sum_(i <- r | P i) (E i)^A.
Proof. exact: linear_sum. Qed.
Lemma adjdZ a : {morph dadj : x / a *: x >-> a^* *: x}. Proof. exact: linearZ. Qed.
Lemma adjdP a : {morph dadj : x y / a *: x + y >-> a^* *: x + y}.
Proof. exact: linearP. Qed.
Lemma adjdI S : (\1_S : 'D[H])^A = \1_S.
Proof. by rewrite adjd_correct adjf1. Qed.
Lemma adjd1 : :1^A = (:1 : 'D[H]).
Proof. by rewrite !dnumI adjd_correct adjf1. Qed.
Lemma adjdN1 : (-:1)^A = (-:1 : 'D[H]).
Proof. by rewrite adjdN adjd1. Qed.
Lemma adjdK : involutive dadj.
Proof. by move=>x; apply/diracP=>i j; rewrite dadj_unfold !diracE adjfK. Qed.
Lemma adjd_inj : injective dadj.
Proof. exact: (can_inj adjdK). Qed.
Lemma adjd_lin S T (f : 'F[H]_(S,T)) : '[f]^A = '[f^A].
Proof. by rewrite adjd_correct. Qed.
Lemma adjd_ket S (v : 'H[H]_S) : '|v>^A = '<v|.
Proof. by rewrite dket_lin adjd_lin v2f_adj dbra_lin. Qed.
Lemma adjd_bra S (v : 'H[H]_S) : '<v|^A = '|v>.
Proof. by rewrite dket_lin dbra_lin adjd_lin v2df_adj. Qed.
Lemma adjd_num c : c%:D^A = c^*%:D.
Proof. by rewrite !dnum_lin adjd_lin s2sf_adj. Qed.
Lemma adjdM e1 e2 : (e1 \o e2)^A = e2^A \o e1^A.
Proof.
apply/diracP=>i j. rewrite dadj_unfold dmul_unfold !diracE linear_sum/=.
by apply eq_bigr=>s _; rewrite adjf_comp !diracE.
Qed.
Lemma adjdT e1 e2 : (e1 \⊗ e2)^A = e1^A \⊗ e2^A.
Proof.
rewrite -(dlin_dec e1) -(dlin_dec e2) tend_suml !adjd_sum tend_suml.
apply eq_bigr=>??; rewrite !tend_sumr adjd_sum; apply eq_bigr=>??. 
by rewrite !dirac_correct tenf_adj.
Qed.
Lemma adjdG e1 e2 : (e1 \· e2)^A = e2^A \· e1^A.
Proof.
rewrite -(dlin_dec e1) -(dlin_dec e2) dotd_suml !adjd_sum dotd_sumr.
apply eq_bigr=>??; rewrite dotd_sumr dotd_suml adjd_sum; apply eq_bigr=>??.
by rewrite !dirac_correct dotf_adj.
Qed.

Lemma trdAC e : e^T = e^A^C.
Proof. by apply/diracP=>i j; rewrite dtr_unfold dadj_unfold dconj_unfold !diracE trfAC. Qed.
Lemma trd0 : 0^T = (0 : 'D[H]). Proof. exact: linear0. Qed.
Lemma trdN : {morph dtr : x / - x}. Proof. exact: linearN. Qed.
Lemma trdD : {morph dtr : x y / x + y}. Proof. exact: linearD. Qed.
Lemma trdB : {morph dtr : x y / x - y}. Proof. exact: linearB. Qed.
Lemma trdMn n : {morph dtr : x / x *+ n}. Proof. exact: linearMn. Qed.
Lemma trdMNn n : {morph dtr : x / x *- n}. Proof. exact: linearMNn. Qed.
Lemma trd_sum I r (P : pred I) (E : I -> 'D[H]) :
  (\sum_(i <- r | P i) E i)^T = \sum_(i <- r | P i) ((E i)^T)%D.
Proof. exact: linear_sum. Qed.
Lemma trdZ a : {morph dtr : x / a *: x}. Proof. exact: linearZ. Qed.
Lemma trdP a : {morph dtr : x y / a *: x + y}. Proof. exact: linearP. Qed.
Lemma trdI S : (\1_S : 'D[H])^T = \1_S.
Proof. by rewrite trd_correct trf1. Qed.
Lemma trd1 : :1^T = (:1 : 'D[H]).
Proof. by rewrite dnumI trd_correct sfT. Qed.
Lemma trdN1 : (-:1)^T = (-:1 : 'D[H]).
Proof. by rewrite trdN trd1. Qed.
Lemma trdK : involutive dtr.
Proof. by move=>x; apply/diracP=>i j; rewrite dtr_unfold !diracE trfK. Qed.  
Lemma trd_inj : injective dtr.
Proof. exact: (can_inj trdK). Qed.
Lemma trdM e1 e2 : (e1 \o e2)^T = e2^T \o e1^T.
Proof. by rewrite !trdAC adjdM conjdM. Qed.
Lemma trdT e1 e2 : (e1 \⊗ e2)^T = e1^T \⊗ e2^T.
Proof. by rewrite !trdAC adjdT conjdT. Qed.
Lemma trdG e1 e2 : (e1 \· e2)^T = e2^T \· e1^T.
Proof. by rewrite !trdAC adjdG conjdG. Qed.
Lemma trd_lin S T (f : 'F[H]_(S,T)) : '[f]^T = '[f^T].
Proof. by rewrite trd_correct. Qed.
Lemma trd_ket S (v : 'H[H]_S) : '|v>^T = '<v^*v|.
Proof. by rewrite trdAC adjd_ket conjd_bra. Qed.
Lemma trd_bra S (v : 'H[H]_S) : '<v|^T = '|v^*v>.
Proof. by rewrite trdAC adjd_bra conjd_ket. Qed.
Lemma trd_num c : c%:D^T = c%:D.
Proof. by rewrite trdAC adjd_num conjd_num conjCK. Qed.

Lemma dACC e : e^A^C = e^C^A.
Proof. by apply/diracP=>i j; rewrite dadj_unfold dconj_unfold !diracE lfACC. Qed.
Lemma trdCA   e : e^T = e^C^A. Proof. by rewrite trdAC dACC. Qed.
Lemma conjdAT e : e^C = e^A^T. Proof. by rewrite trdAC adjdK. Qed.
Lemma conjdTA e : e^C = e^T^A. Proof. by rewrite trdCA adjdK. Qed.
Lemma adjdTC  e : e^A = e^T^C. Proof. by rewrite trdAC conjdK. Qed.
Lemma adjdCT  e : e^A = e^C^T. Proof. by rewrite trdCA conjdK. Qed.
Definition dT2AC := trdAC.
Definition dT2CA := trdCA.
Definition dC2AT := conjdAT.
Definition dC2TA := conjdTA.
Definition dA2TC := adjdTC.
Definition dA2CT := adjdCT.
Lemma dCAC e : e^C^A = e^A^C. Proof. by rewrite dACC. Qed.
Lemma dATC e : e^A^T = e^T^A. Proof. by rewrite -dC2AT dC2TA. Qed.
Lemma dTAC e : e^T^A = e^A^T. Proof. by rewrite dATC. Qed.
Lemma dTCC e : e^T^C = e^C^T. Proof. by rewrite -dA2TC dA2CT. Qed.
Lemma dCTC e : e^C^T = e^T^C. Proof. by rewrite dTCC. Qed.

Lemma dlin0 S T : '[0 : 'F[H]_(S,T)] = 0.
Proof. by rewrite linear0. Qed.
Lemma dket0 S : '| (0 : 'H[H]_S) > = 0.
Proof. by rewrite linear0. Qed.
Lemma dbra0 S : '< (0 : 'H[H]_S) | = 0.
Proof. by rewrite linear0. Qed.

(* recommend: write from dnum -> c *)
Lemma dInum : \1_set0 = :1.
Proof. by rewrite dnumI. Qed.
Lemma dInum_cond S : S = set0 -> \1_S = :1.
Proof. by move=>->; rewrite dInum. Qed.
Lemma dnum0 : 0%:D = 0. Proof. by rewrite raddf0. Qed.
Lemma dnumN a : -a%:D = (-a)%:D. Proof. by rewrite raddfN. Qed.
Lemma dnumD a b : a%:D + b%:D = (a+b)%:D. Proof. by rewrite raddfD. Qed.
Lemma dnumB a b : a%:D - b%:D = (a-b)%:D. Proof. by rewrite raddfB. Qed.
Lemma dnumMn n a : a%:D*+n = (a*+n)%:D. Proof. by rewrite raddfMn. Qed.
Lemma dnumMNn n a : a%:D*-n = (a*-n)%:D. Proof. by rewrite raddfMNn. Qed.
Lemma dnum_sum I r (P : pred I) (E : I -> C) :
  \sum_(i <- r | P i) (E i)%:D = (\sum_(i <- r | P i) E i)%:D.
Proof. by rewrite raddf_sum. Qed.
Lemma dnumZ a b : a*:b%:D = (a*b)%:D.
Proof. by rewrite dnum_unfold /s2sf -!linearZ/= scalerA mulrC. Qed.
Lemma dnumZ1 a : a%:D = a *: :1. Proof. by rewrite dnumZ mulr1. Qed.
Lemma dnumP a b c : a*:b%:D + c%:D= (a*b+c)%:D.
Proof. by rewrite dnumZ dnumD. Qed.
Lemma dnumTl x a : a%:D \⊗ x = a *: x. 
Proof. by rewrite dnumZ1 tendZl ten1d. Qed.
Lemma dnumTr x a : x \⊗ a%:D = a *: x. 
Proof. by rewrite tendC dnumTl. Qed.
Lemma dnumT a b : a%:D \⊗ b%:D = (a*b)%:D. 
Proof. by rewrite dnumTl dnumZ. Qed.
Lemma dnumM a b : a%:D \o b%:D = (a*b)%:D. 
Proof. by rewrite !dnum_lin muld_correct /s2sf -comp_lfunZl -comp_lfunZr scalerA comp_lfun1r. Qed.
Lemma dnumGl x a : a%:D \· x = a *: x. 
Proof. by rewrite dnumZ1 dotdZl dot1d. Qed.
Lemma dnumGr x a : x \· a%:D = a *: x. 
Proof. by rewrite dnumZ1 dotdZr dotd1. Qed.
Lemma dnumG a b : a%:D \· b%:D = (a*b)%:D. 
Proof. by rewrite dnumGl dnumZ. Qed.
Definition dnum_adj := adjd_num.

Definition dnum_linear := (dnum0, dnumI, dnumN, dnumD, dnumB, dnumMn, dnumMNn, dnum_sum, dnumZ, dnumP).
Definition dnum_simp := (dket_num, dbra_num, dlin_num, adjd_num, conjd_num, trd_num, 
  dnumTl, dnumTr, dnumT, dnumM, dnumGl, dnumGr, dnumG).

End DiracTheory.

Section DiracBig.
Context {L : finType} (H : L -> chsType).
(* since generally we need to import GRing.Theory, *)
(* canonical of addoid here will be ignored, so we reclaim distribution lemmas *)
(* Canonical  muld_monoid := Monoid.Law (@muldA _ H) (@mulIId _ H) (@muldII _ H). *)
Canonical  muld_muloid := Monoid.MulLaw (@mul0d _ H) (@muld0 _ H).
Definition muld_addoid := Monoid.AddLaw (@muldDl _ H) (@muldDr _ H).
Canonical  tend_monoid := Monoid.Law (@tendA _ H) (@ten1d _ H) (@tend1 _ H).
Canonical  tend_muloid := Monoid.MulLaw (@ten0d _ H) (@tend0 _ H).
Canonical  tend_comoid := Monoid.ComLaw (@tendC _ H).
Definition tend_addoid := Monoid.AddLaw (@tendDl _ H) (@tendDr _ H).
Canonical  dotd_muloid := Monoid.MulLaw (@dot0d _ H) (@dotd0 _ H).
Definition dotd_addoid := Monoid.AddLaw (@dotdDl _ H) (@dotdDr _ H).

Lemma tensumE : (+%R : 'D[H] -> 'D -> 'D) = tend_addoid. by []. Qed.
Lemma mulsumE : (+%R : 'D[H] -> 'D -> 'D) = muld_addoid. by []. Qed.
Lemma dotsumE : (+%R : 'D[H] -> 'D -> 'D) = dotd_addoid. by []. Qed.

Lemma ket_sum I (r : seq I) (P : pred I) S (F : I -> 'H[H]_S) :
  \sum_(i <- r | P i) '|F i> = '|\sum_(i <- r | P i) (F i)>.
Proof. by rewrite linear_sum/=. Qed.

Lemma bra_sum I (r : seq I) (P : pred I) S (F : I -> 'H[H]_S) :
  \sum_(i <- r | P i) '<F i| = '<\sum_(i <- r | P i) (F i)|.
Proof. by rewrite linear_sum/=. Qed.

Lemma lin_sum I (r : seq I) (P : pred I) S T (F : I -> 'F[H]_(S,T)) :
  \sum_(i <- r | P i) '[F i] = '[\sum_(i <- r | P i) (F i)].
Proof. by rewrite linear_sum/=. Qed.

(*distribution lemmas *)
Lemma tend_sumlr I J rI rJ (pI : pred I) (pJ : pred J) 
  (F : I -> 'D[H]) (G : J -> 'D) :
  (\sum_(i <- rI | pI i) F i) \⊗ (\sum_(j <- rJ | pJ j) G j)
   = \sum_(i <- rI | pI i) \sum_(j <- rJ | pJ j) (F i \⊗ G j).
Proof. rewrite !tensumE; apply: big_distrlr. Qed.

Lemma tend_distr_sum_dep (I J : finType) j0 (P : pred I) (Q : I -> pred J) 
  (F : I -> J -> 'D[H]) :
  (\ten_(i | P i) \sum_(j | Q i j) F i j) =
     \sum_(f in pfamily j0 P Q) \ten_(i | P i) F i (f i).
Proof. rewrite tensumE bigd; apply: big_distr_big_dep. Qed.

Lemma tend_distr_sum (I J : finType) j0 (P : pred I) (Q : pred J) 
  (F : I -> J -> 'D[H]) :
  (\ten_(i | P i) \sum_(j | Q j) F i j) =
     \sum_(f in pffun_on j0 P Q) \ten_(i | P i) F i (f i).
Proof. by rewrite tensumE bigd; apply: big_distr_big. Qed.

Lemma tendA_distr_sum_dep (I J : finType) (Q : I -> pred J) 
  (F : I -> J -> 'D[H]) :
  (\ten_i \sum_(j | Q i j) F i j)
    = \sum_(f in family Q) \ten_i F i (f i).
Proof. by rewrite tensumE bigd; apply: bigA_distr_big_dep. Qed.

Lemma tendA_distr_sum (I J : finType) (Q : pred J) (F : I -> J -> 'D[H]) :
  (\ten_i \sum_(j | Q j) F i j)
    = \sum_(f in ffun_on Q) \ten_i F i (f i).
Proof. exact: tendA_distr_sum_dep. Qed.

Lemma tendA_distr_sumA (I J : finType) (F : I -> J -> 'D[H]) :
  (\ten_(i : I) \sum_(j : J) F i j)
    = \sum_(f : {ffun I -> J}) \ten_i F i (f i).
Proof. by rewrite tensumE bigd; apply: bigA_distr_bigA. Qed.

(*distribution lemmas *)
Lemma muld_sumlr I J rI rJ (pI : pred I) (pJ : pred J) 
  (F : I -> 'D[H]) (G : J -> 'D) :
  (\sum_(i <- rI | pI i) F i) \o (\sum_(j <- rJ | pJ j) G j)
   = \sum_(i <- rI | pI i) \sum_(j <- rJ | pJ j) (F i \o G j).
Proof. rewrite !mulsumE; apply: big_distrlr. Qed.

Lemma dotd_sumlr I J rI rJ (pI : pred I) (pJ : pred J) 
  (F : I -> 'D[H]) (G : J -> 'D) :
  (\sum_(i <- rI | pI i) F i) \· (\sum_(j <- rJ | pJ j) G j)
   = \sum_(i <- rI | pI i) \sum_(j <- rJ | pJ j) (F i \· G j).
Proof. rewrite !dotsumE; apply: big_distrlr. Qed.

Lemma dotd_distr_sum_dep (I J : finType) j0 (P : pred I) (Q : I -> pred J) 
  (F : I -> J -> 'D[H]) :
  (\dot_(i | P i) \sum_(j | Q i j) F i j) =
     \sum_(f in pfamily j0 P Q) \dot_(i | P i) F i (f i).
Proof. by rewrite dotsumE bigd; apply: big_distr_big_dep. Qed.

Lemma dotd_distr_sum (I J : finType) j0 (P : pred I) (Q : pred J) 
  (F : I -> J -> 'D[H]) :
  (\dot_(i | P i) \sum_(j | Q j) F i j) =
     \sum_(f in pffun_on j0 P Q) \dot_(i | P i) F i (f i).
Proof. by rewrite dotsumE bigd; apply: big_distr_big. Qed.

Lemma dotdA_distr_sum_dep (I J : finType) (Q : I -> pred J) 
  (F : I -> J -> 'D[H]) :
  (\dot_i \sum_(j | Q i j) F i j)
    = \sum_(f in family Q) \dot_i F i (f i).
Proof. by rewrite dotsumE bigd; apply: bigA_distr_big_dep. Qed.

Lemma dotdA_distr_sum (I J : finType) (Q : pred J) (F : I -> J -> 'D[H]) :
  (\dot_i \sum_(j | Q j) F i j)
    = \sum_(f in ffun_on Q) \dot_i F i (f i).
Proof. exact: dotdA_distr_sum_dep. Qed.

Lemma dotdA_distr_sumA (I J : finType) (F : I -> J -> 'D[H]) :
  (\dot_(i : I) \sum_(j : J) F i j)
    = \sum_(f : {ffun I -> J}) \dot_i F i (f i).
Proof. by rewrite dotsumE bigd; apply: bigA_distr_bigA. Qed.

(* add dffun for big distr *)
Lemma tendA_distr_big_dffun (I : finType) (J : forall i : I, finType)
  (PJ : forall i : I, pred (J i)) (F : forall i : I, J i -> 'D[H]) :
  (\ten_(i : I) \sum_(j : J i| PJ i j) F i j)
    = \sum_(f : {dffun forall i : I, J i} | 
        family_mem (fun i : I => Mem (PJ i)) f) \ten_i F i (f i).
Proof. rewrite tensumE bigd; apply: big_distr_big_dffun. Qed.

Lemma tendA_distr_dffun (I : finType) (J : forall i : I, finType)
  (F : forall i : I, J i -> 'D[H]) :
  (\ten_(i : I) \sum_(j : J i) F i j)
    = \sum_(f : {dffun forall i : I, J i}) \ten_i F i (f i).
Proof. rewrite tensumE bigd; apply: big_distr_dffun. Qed.

Lemma dotdA_distr_big_dffun (I : finType) (J : forall i : I, finType)
  (PJ : forall i : I, pred (J i)) (F : forall i : I, J i -> 'D[H]) :
  (\dot_(i : I) \sum_(j : J i| PJ i j) F i j)
    = \sum_(f : {dffun forall i : I, J i} | 
        family_mem (fun i : I => Mem (PJ i)) f) \dot_i F i (f i).
Proof. rewrite dotsumE bigd; apply: big_distr_big_dffun. Qed.

Lemma dotdA_distr_dffun (I : finType) (J : forall i : I, finType)
  (F : forall i : I, J i -> 'D[H]) :
  (\dot_(i : I) \sum_(j : J i) F i j)
    = \sum_(f : {dffun forall i : I, J i}) \dot_i F i (f i).
Proof. rewrite dotsumE bigd; apply: big_distr_dffun. Qed.

End DiracBig.

(* conditioned theory, require extra domain conditions *)
(* This section is used for Canonical Structure of dirac *)
(* for example, we can canonical dket to ketdirac and wfdirac *)
(* and in the theory, we may set up a lemma (e : wfdirac) : P e *)
(* the for dket v, we can directly apply the lemma without proving wfd *)
Module WFDirac.

Section ClassDef.
Context (L : finType) (H : L -> chsType).
Implicit Type (S T : {set L}).

Definition wfd_axiom S T (f : 'D[H]) := (f = dlin (f S T)).
Notation sqrd S f := (wfd_axiom S S f).
Notation ketd S f := (wfd_axiom set0 S f).
Notation brad S f := (wfd_axiom S set0 f).

Structure wfdirac S T := WFDirac {
  wf_base : 'D[H];
  _ : wfd_axiom S T wf_base;
}.
Local Coercion wf_base : wfdirac >-> dirac.

Structure sqrdirac S := SqrDirac {
  sqr_base : 'D[H];
  _ : sqrd S sqr_base;
}.
Local Coercion sqr_base : sqrdirac >-> dirac.
Lemma sqrdirac_wf_subproof S (e : sqrdirac S) : 
  wfd_axiom S S (sqr_base e).
Proof. by destruct e. Qed.
Definition sqrdirac_wf S (e : sqrdirac S) := WFDirac (sqrdirac_wf_subproof e).

Structure ketdirac S := KetDirac {
  ket_base : 'D[H];
  _ : ketd S ket_base;
}.
Local Coercion ket_base : ketdirac >-> dirac.
Lemma ketdirac_wf_subproof S (e : ketdirac S) : 
  wfd_axiom set0 S (ket_base e).
Proof. by destruct e. Qed.
Definition ketdirac_wf S (e : ketdirac S) := WFDirac (ketdirac_wf_subproof e).

Structure bradirac S := BraDirac {
  bra_base : 'D[H];
  _ : brad S bra_base;
}.
Local Coercion bra_base : bradirac >-> dirac.
Lemma bradirac_wf_subproof S (e : bradirac S) : 
  wfd_axiom S set0 (bra_base e).
Proof. by destruct e. Qed.
Definition bradirac_wf S (e : bradirac S) := WFDirac (bradirac_wf_subproof e).

Let ex_id (e1 e2 : 'D[H]) := phant_id e1 e2.
Definition clone_wfdirac S T e :=
  fun (opL : wfdirac S T) & ex_id opL e =>
  fun ewf (opL' := @WFDirac S T e ewf)
    & phant_id opL' opL => opL'.

Definition clone_sqrdirac S e :=
  fun (opL : sqrdirac S) & ex_id opL e =>
  fun esqr (opL' := @SqrDirac S e esqr)
    & phant_id opL' opL => opL'.

Definition clone_ketdirac S e :=
  fun (opL : ketdirac S) & ex_id opL e =>
  fun eket (opL' := @KetDirac S e eket)
    & phant_id opL' opL => opL'.

Definition clone_bradirac S e :=
  fun (opL : bradirac S) & ex_id opL e =>
  fun ebra (opL' := @BraDirac S e ebra)
    & phant_id opL' opL => opL'.

End ClassDef.

Module Import Exports.
Coercion wf_base  : wfdirac >-> dirac.
Coercion sqr_base : sqrdirac >-> dirac.
Coercion ket_base : ketdirac >-> dirac.
Coercion bra_base : bradirac >-> dirac.
Canonical sqrdirac_wf.
Canonical ketdirac_wf.
Canonical bradirac_wf.
Definition wfd_axiom := wfd_axiom.
Notation wfd S T f := (@wfd_axiom _ _ S T f).
Notation sqrd S f := (@wfd_axiom _ _ S S f).
Notation ketd S f := (@wfd_axiom _ _ set0 S f).
Notation brad S f := (@wfd_axiom _ _ S set0 f).
Notation WFDirac fL := (WFDirac fL).
Notation SqrDirac fL := (SqrDirac fL).
Notation KetDirac fL := (KetDirac fL).
Notation BraDirac fL := (BraDirac fL).
Notation "''D[' H ]_ ( S , T )" := (@wfdirac _ H S T) (only parsing) : dirac_scope.
Notation "''D_' ( S , T )" := (@wfdirac _ _ S T) : dirac_scope.
Notation "''D[' H ]_ ( S )" := (@sqrdirac _ H S) (only parsing) : dirac_scope.
Notation "''D[' H ]_ S" := (@sqrdirac _ H S) (only parsing) : dirac_scope.
Notation "''D_' ( S )" := (@sqrdirac _ _ S) (only parsing) : dirac_scope.
Notation "''D_' S" := (@sqrdirac _ _ S) : dirac_scope.
Notation "''Ket[' H ]_ ( S )" := (@ketdirac _ H S) (only parsing) : dirac_scope.
Notation "''Ket[' H ]_ S" := (@ketdirac _ H S) (only parsing) : dirac_scope.
Notation "''Ket_' ( S )" := (@ketdirac _ _ S) (only parsing) : dirac_scope.
Notation "''Ket_' S" := (@ketdirac _ _ S) : dirac_scope.
Notation "''Bra[' H ]_ ( S )" := (@bradirac _ H S) (only parsing) : dirac_scope.
Notation "''Bra[' H ]_ S" := (@bradirac _ H S) (only parsing) : dirac_scope.
Notation "''Bra_' ( S )" := (@bradirac _ _ S) (only parsing) : dirac_scope.
Notation "''Bra_' S" := (@bradirac _ _ S) : dirac_scope.
Notation "[ 'WFD' 'of' e | S , T ]" := (@clone_wfdirac _ _ S T e _ id _ id)
  (at level 0, format "[ 'WFD'  'of'  e  |  S  ,  T ]") : form_scope.
Notation "[ 'WFD' 'of' e ]" := (@clone_wfdirac _ _ _ _ e _ id _ id)
  (at level 0, format "[ 'WFD'  'of'  e ]") : form_scope.
Notation "[ 'SqrD' 'of' e | S ]" := (@clone_sqrdirac _ _ S e _ id _ id)
  (at level 0, format "[ 'SqrD'  'of'  e  |  S ]") : form_scope.
Notation "[ 'SqrD' 'of' e ]" := (@clone_sqrdirac _ _ _ e _ id _ id)
  (at level 0, format "[ 'SqrD'  'of'  e ]") : form_scope.
Notation "[ 'Ket' 'of' e | S ]" := (@clone_ketdirac _ _ S e _ id _ id)
  (at level 0, format "[ 'Ket'  'of'  e  |  S ]") : form_scope.
Notation "[ 'Ket' 'of' e ]" := (@clone_ketdirac _ _ _ e _ id _ id)
  (at level 0, format "[ 'Ket'  'of'  e ]") : form_scope.
Notation "[ 'Bra' 'of' e | S ]" := (@clone_bradirac _ _ S e _ id _ id)
  (at level 0, format "[ 'Bra'  'of'  e  | S ]") : form_scope.
Notation "[ 'Bra' 'of' e ]" := (@clone_bradirac _ _ _ e _ id _ id)
  (at level 0, format "[ 'Bra'  'of'  e ]") : form_scope.

End Exports.

End WFDirac.
Include WFDirac.Exports.

(* although it's possible to use only wfdirac and regard sqr ket bra
as special cases, but then in many cases, canonical of a operator will
be ignored and not able to work for all cases 
For example, we might canonical ddot of two sqaure expr as sqaure
then if we want canonical ddot of ket and bra with same S, then 
we will get warning "canonical ignored". *)
(* these structures allow to do some calculations similar to dependent type *)
Section WFDiracTheory.
Context (L : finType) (H : L -> chsType).

Lemma wfd_def S T (e : 'D[H]) : @wfd_axiom _ H S T e <-> e = dlin (e S T).
Proof. by []. Qed.

Lemma wfd_linE S T (e : 'D[H]_(S,T)) : e = '[ e S T ] :> 'D.
Proof. by case: e. Qed.
Lemma sqrd_linE S (e : 'D[H]_S) : e = '[ e S S ] :> 'D.
Proof. by case: e. Qed.
Lemma d2vK S (e : 'Ket[H]_S) : '| d2v S e > = e.
Proof. by case: e=>[v P]; rewrite /=dket_unfold f2vK {2}P dlin_unfold. Qed.
Lemma d2dvK S (e : 'Bra[H]_S) : '< d2dv S e | = e.
Proof. by case: e=>[v P]; rewrite /=dbra_unfold df2vK {2}P dlin_unfold. Qed.

Lemma wfdP S T (e : 'D[H]_(S,T)) : wfd S T e. Proof. by case: e. Qed.
Lemma sqrdP S (e : 'D[H]_S) : sqrd S e. Proof. by case: e. Qed.
Lemma ketP S (e : 'Ket[H]_S) : ketd S e. Proof. by case: e. Qed.
Lemma braP S (e : 'Bra[H]_S) : brad S e. Proof. by case: e. Qed.

Lemma wfdP_eq S T S' T' (e : 'D[H]_(S,T)) : S = S' -> T = T' -> wfd S' T' e.
Proof. by move=><-<-; apply wfdP. Qed.
Lemma sqrdP_eq S S' (e : 'D[H]_S) : S = S' -> sqrd S' e.
Proof. by move=><-; apply sqrdP. Qed.
Lemma ketP_eq S S' (e : 'Ket[H]_S) : S = S' -> ketd S' e.
Proof. by move=><-; apply ketP. Qed.
Lemma braP_eq S S' (e : 'Bra[H]_S) : S = S' -> brad S' e.
Proof. by move=><-; apply braP. Qed.

Lemma wfdE S T (e : 'D[H]) (P : wfd S T e) : e = WFDirac P. Proof. by []. Qed.
Lemma sqrdE S (e : 'D[H]) (P : sqrd S e) : e = SqrDirac P. Proof. by []. Qed.
Lemma ketE S (e : 'D[H]) (P : ketd S e) : e = KetDirac P. Proof. by []. Qed.
Lemma braE S (e : 'D[H]) (P : brad S e) : e = BraDirac P. Proof. by []. Qed.

Lemma wfd_eqD S T S' T' (e1 : 'D[H]_(S,T)) (e2 : 'D_(S',T')) :
  (e1 : 'D) = e2 -> ((S == S') && (T == T')) || ((e1 : 'D) == 0).
Proof.
move=>P; case: eqP; case: eqP=>//= /eqP P1 /eqP P2.
all:apply/eqP/diracP=>i j; rewrite (wfd_linE) dlin_unfold !diracE; case: eqP=>//; 
  case: eqP=>// P3 P4; rewrite P (wfd_linE) dlin_unfold.
1,3: by rewrite dset_eq0r// linear0.
by rewrite dset_eq0l// linear0.
Qed.

Lemma sqrd_eqD S T (e1 : 'D[H]_S) (e2 : 'D_T) :
  (e1 : 'D) = e2 -> (S == T) || ((e1 : 'D) == 0).
Proof. by move/wfd_eqD=>/orP[/andP[->]//|->]; rewrite orbT. Qed.

Lemma ket_eqD S T (e1 : 'Ket[H]_S) (e2 : 'Ket_T) :
  (e1 : 'D) = e2 -> (S == T) || ((e1 : 'D) == 0).
Proof. by move/wfd_eqD=>/orP[/andP[_ ->]//|->]; rewrite orbT. Qed.

Lemma bra_eqD S T (e1 : 'Bra[H]_S) (e2 : 'Bra_T) :
  (e1 : 'D) = e2 -> (S == T) || ((e1 : 'D) == 0).
Proof. by move/wfd_eqD=>/orP[/andP[->]//|->]; rewrite orbT. Qed.

Lemma wfd_eq S T (e1 e2 : 'D_(S,T)) : (e1 : 'D[H]) = e2 <-> e1 = e2.
Proof.
split=>[|->//]; destruct e1 as [e1 wf1]; destruct e2 as [e2 wf2] =>/= P.
by case: e2 / P wf2=> wf2; rewrite (eq_irrelevance wf1 wf2).
Qed.

Lemma sqrd_eq S (e1 e2 : 'D_S) : (e1 : 'D[H]) = e2 <-> e1 = e2.
Proof.
split=>[|->//]; destruct e1 as [e1 wf1]; destruct e2 as [e2 wf2] =>/= P.
by case: e2 / P wf2=> wf2; rewrite (eq_irrelevance wf1 wf2).
Qed.

Lemma ket_eq S (e1 e2 : 'Ket_S) : (e1 : 'D[H]) = e2 <-> e1 = e2.
Proof.
split=>[|->//]; destruct e1 as [e1 wf1]; destruct e2 as [e2 wf2] =>/= P.
by case: e2 / P wf2=> wf2; rewrite (eq_irrelevance wf1 wf2).
Qed.

Lemma bra_eq S (e1 e2 : 'Bra_S) : (e1 : 'D[H]) = e2 <-> e1 = e2.
Proof.
split=>[|->//]; destruct e1 as [e1 wf1]; destruct e2 as [e2 wf2] =>/= P.
by case: e2 / P wf2=> wf2; rewrite (eq_irrelevance wf1 wf2).
Qed.

Lemma dzero_wf S T : @wfd_axiom _ H S T 0.
Proof.
rewrite wfd_def; apply/diracP=>i j.
by rewrite dlin_unfold !diracE; (do 2 case: eqP=>//?); rewrite linear0.
Qed.
Canonical zero_wfdirac S T := WFDirac (@dzero_wf S T).
Canonical zero_sqrdirac S  := SqrDirac (@dzero_wf S S).
Canonical zero_ketdirac S  := KetDirac (@dzero_wf set0 S).
Canonical zero_bradirac S  := BraDirac (@dzero_wf S set0).

Lemma dnum_wf c : @wfd_axiom _ H set0 set0 c%:D.
Proof. by rewrite wfd_def dnum_lin dlin_id. Qed.
Canonical dnum_wfdirac c  := WFDirac (@dnum_wf c).
Canonical dnum_sqrdirac c := SqrDirac (@dnum_wf c).
Canonical dnum_ketdirac c := KetDirac (@dnum_wf c).
Canonical dnum_bradirac c := BraDirac (@dnum_wf c).

Lemma dket_wf S (v : 'H[H]_S) : wfd_axiom set0 S '| v >.
Proof. by rewrite wfd_def dket_lin dlin_id. Qed.
Canonical dket_wfdirac S (v : 'H[H]_S)   := WFDirac (dket_wf v).
Canonical dket_sqrdirac (v : 'H[H]_set0) := SqrDirac (dket_wf v).
Canonical dket_ketdirac S (v : 'H[H]_S)  := KetDirac (dket_wf v).
Canonical dket_bradirac (v : 'H[H]_set0) := BraDirac (dket_wf v).

Lemma dbra_wf S (v : 'H[H]_S) : wfd_axiom S set0 '< v |.
Proof. by rewrite wfd_def dbra_lin dlin_id. Qed.
Canonical dbra_wfdirac S (v : 'H[H]_S)   := WFDirac (dbra_wf v).
Canonical dbra_sqrdirac (v : 'H[H]_set0) := SqrDirac (dbra_wf v).
Canonical dbra_ketdirac (v : 'H[H]_set0) := KetDirac (dbra_wf v).
Canonical dbra_bradirac S (v : 'H[H]_S)  := BraDirac (dbra_wf v).

Lemma dlin_wf S T (v : 'F[H]_(S,T)) : wfd_axiom S T '[ v ].
Proof. by rewrite wfd_def dlin_id. Qed.
Canonical dlin_wfdirac S T (f : 'F[H]_(S,T))  := WFDirac (dlin_wf f).
Canonical dlin_sqrdirac S (f : 'F[H]_S) := SqrDirac (dlin_wf f).
Canonical dlin_ketdirac S (f : 'F[H]_(set0,S)) := KetDirac (dlin_wf f).
Canonical dlin_bradirac S (f : 'F[H]_(S,set0)) := BraDirac (dlin_wf f).

Lemma addd_wf S T (e1 e2 : 'D[H]_(S,T)) : wfd_axiom S T ((e1 : 'D) + e2).
Proof. by rewrite wfd_def wfd_linE (wfd_linE e2) addd_correct dlin_id. Qed.
Canonical addd_wfdirac S T e1 e2  := WFDirac (@addd_wf S T e1 e2).
Canonical addd_sqrdirac S (e1 e2 : 'D[H]_S) := SqrDirac (addd_wf [WFD of e1] [WFD of e2]).
Canonical addd_ketdirac S (e1 e2 : 'Ket[H]_S) := KetDirac (addd_wf [WFD of e1] [WFD of e2]).
Canonical addd_bradirac S (e1 e2 : 'Bra[H]_S) := BraDirac (addd_wf [WFD of e1] [WFD of e2]).

Lemma oppd_wf S T (e : 'D[H]_(S,T)) : wfd_axiom S T (- (e : 'D)).
Proof. by rewrite wfd_def wfd_linE oppd_correct dlin_id. Qed.
Canonical oppd_wfdirac S T e  := WFDirac (@oppd_wf S T e).
Canonical oppd_sqrdirac S (e : 'D[H]_S) := SqrDirac (oppd_wf [WFD of e]).
Canonical oppd_ketdirac S (e : 'Ket[H]_S) := KetDirac (oppd_wf [WFD of e]).
Canonical oppd_bradirac S (e : 'Bra[H]_S) := BraDirac (oppd_wf [WFD of e]).

Lemma scaled_wf c S T (e : 'D[H]_(S,T)) : wfd_axiom S T (c *: (e : 'D)).
Proof. by rewrite wfd_def wfd_linE scaled_correct dlin_id. Qed.
Canonical scaled_wfdirac c S T e  := WFDirac (@scaled_wf c S T e).
Canonical scaled_sqrdirac c S (e : 'D[H]_S) := SqrDirac (scaled_wf c [WFD of e]).
Canonical scaled_ketdirac c S (e : 'Ket[H]_S) := KetDirac (scaled_wf c [WFD of e]).
Canonical scaled_bradirac c S (e : 'Bra[H]_S) := BraDirac (scaled_wf c [WFD of e]).

Lemma conjd_wf S T (e : 'D[H]_(S,T)) : wfd_axiom S T e^C.
Proof. by rewrite wfd_def {1}wfd_linE conjd_correct dconj_unfold diracE. Qed.
Canonical conjd_wfdirac S T (e : 'D_(S,T)) := WFDirac (conjd_wf e).
Canonical conjd_sqrdirac S (e : 'D_S) := SqrDirac (conjd_wf [WFD of e]).
Canonical conjd_ketdirac S (e : 'Ket_S) := KetDirac (conjd_wf [WFD of e]).
Canonical conjd_bradirac S (e : 'Bra_S)  := BraDirac (conjd_wf [WFD of e]).

Lemma adjd_wf S T (e : 'D[H]_(S,T)) : wfd_axiom T S e^A.
Proof. by rewrite wfd_def {1}wfd_linE adjd_correct dadj_unfold diracE. Qed.
Canonical adjd_wfdirac S T (e : 'D_(S,T)) := WFDirac (adjd_wf e).
Canonical adjd_sqrdirac S (e : 'D_S) := SqrDirac (adjd_wf [WFD of e]).
Canonical adjd_ketdirac S (e : 'Bra_S) := KetDirac (adjd_wf [WFD of e]).
Canonical adjd_bradirac S (e : 'Ket_S)  := BraDirac (adjd_wf [WFD of e]).

Lemma trd_wf S T (e : 'D[H]_(S,T)) : wfd_axiom T S e^T.
Proof. by rewrite wfd_def {1}wfd_linE trd_correct dtr_unfold diracE. Qed.
Canonical trd_wfdirac S T (e : 'D_(S,T)) := WFDirac (trd_wf e).
Canonical trd_sqrdirac S (e : 'D_S) := SqrDirac (trd_wf [WFD of e]).
Canonical trd_ketdirac S (e : 'Bra_S) := KetDirac (trd_wf [WFD of e]).
Canonical trd_bradirac S (e : 'Ket_S)  := BraDirac (trd_wf [WFD of e]).

Lemma muld_wf S T W (e1 : 'D[H]_(S,T)) (e2 : 'D_(W,S)) : wfd_axiom W T (e1 \o e2).
Proof. by rewrite wfd_def wfd_linE (wfd_linE e2) muld_correct dlin_id. Qed.
Canonical muld_wfdirac S T W e1 e2 := WFDirac (@muld_wf S T W e1 e2).
Canonical muld_sqrdirac S T e1 e2 := SqrDirac (@muld_wf S T T e1 e2).
Canonical muld_ketdirac S T e1 (e2 : 'Ket_S) := KetDirac (@muld_wf S T _ e1 [WFD of e2]).
Canonical muld_bradirac S T (e1 : 'Bra_S) e2 := BraDirac (@muld_wf S _ T [WFD of e1] e2).

Lemma tend_wf S T S' T' (e1 : 'D[H]_(S,T)) (e2 : 'D_(S',T')) : 
  wfd_axiom (S :|: S') (T :|: T') (e1 \⊗ e2).
Proof. by rewrite wfd_def wfd_linE (wfd_linE e2) tend_correct dlin_id. Qed.
Canonical tend_wfdirac S T S' T' (e1 : 'D_(S,T)) (e2 : 'D_(S',T')) := WFDirac (tend_wf e1 e2).
Canonical tend_sqrdirac S S' (e1 : 'D_S) (e2 : 'D_S') := SqrDirac (tend_wf [WFD of e1] [WFD of e2]).
Lemma tend_wf_ket S S' (e1 : 'Ket[H]_S) (e2 : 'Ket_S') : 
  wfd_axiom set0 (S :|: S') (e1 \⊗ e2).
Proof. by rewrite wfd_def {1}wfd_linE/= setU0. Qed.
Lemma tend_wf_bra S S' (e1 : 'Bra[H]_S) (e2 : 'Bra_S') : 
  wfd_axiom (S :|: S') set0 (e1 \⊗ e2).
Proof. by rewrite wfd_def {1}wfd_linE/= setU0. Qed.
Canonical tend_ketdirac S S' (e1 : 'Ket_S) (e2 : 'Ket_S') := KetDirac (tend_wf_ket e1 e2).
Canonical tend_bradirac S S' (e1 : 'Bra_S) (e2 : 'Bra_S') := BraDirac (tend_wf_bra e1 e2).

Lemma dotd_wf S T S' T' (e1 : 'D[H]_(S,T)) (e2 : 'D_(S',T')) : 
  wfd_axiom (S' :|: S :\: T') (T :|: T' :\: S) (e1 \· e2).
Proof. by rewrite wfd_def wfd_linE (wfd_linE e2) dotd_correct dlin_id. Qed.
Canonical dotd_wfdirac S T S' T' (e1 : 'D_(S,T)) (e2 : 'D_(S',T')) := WFDirac (dotd_wf e1 e2).
Lemma dotd_wf_sqr S S' (e1 : 'D[H]_S) (e2 : 'D_S') : 
  wfd_axiom (S :|: S') (S :|:S') (e1 \· e2).
Proof. by rewrite wfd_def [LHS]wfd_linE/= setUDV setUD. Qed.
Canonical dotd_sqrdirac S S' (e1 : 'D_S) (e2 : 'D_S') := SqrDirac (dotd_wf_sqr e1 e2).
Lemma dotd_wf_ket S S' (e1 : 'Ket[H]_S) (e2 : 'Ket_S') : 
  wfd_axiom set0 (S :|: S') (e1 \· e2).
Proof. by rewrite wfd_def {1}wfd_linE/= set0D setU0 setD0. Qed.
Lemma dotd_wf_bra S S' (e1 : 'Bra[H]_S) (e2 : 'Bra_S') : 
  wfd_axiom (S :|: S') set0 (e1 \· e2).
Proof. by rewrite wfd_def {1}wfd_linE/= setD0 set0D setU0 setUC. Qed.
Canonical dotd_ketdirac S S' (e1 : 'Ket_S) (e2 : 'Ket_S') := KetDirac (dotd_wf_ket e1 e2).
Canonical dotd_bradirac S S' (e1 : 'Bra_S) (e2 : 'Bra_S') := BraDirac (dotd_wf_bra e1 e2).

Lemma tends_wf I (r : seq I) (P : pred I) (df cdf : I -> {set L})
  (F : forall i : I, 'D[H]_(df i, cdf i)) : 
  wfd (\bigcup_(i <- r | P i) df i) (\bigcup_(i <- r | P i) cdf i) (\ten_(i <- r | P i) F i).
Proof.
rewrite !bigd; elim: r=>[|x r P1]; first by rewrite !big_nil; apply/wfdP.
rewrite !big_cons; case: (P x)=>//; rewrite (wfdE P1); apply/wfdP.
Qed.
Canonical tends_wfdirac I (r : seq I) (P : pred I) (df cdf : I -> {set L}) 
  (F : forall i : I, 'D[H]_(df i, cdf i)) 
    := WFDirac (tends_wf r P F).

Lemma tends_wf_sqr I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, 'D[H]_(df i)) : 
  sqrd (\bigcup_(i <- r | P i) df i) (\ten_(i <- r | P i) F i).
Proof. apply/tends_wf. Qed.
Canonical tens_sqrdirac I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, 'D[H]_(df i)) := SqrDirac (tends_wf_sqr r P F).

Lemma tends_wf_ket I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, 'Ket[H]_(df i)) : 
  ketd (\bigcup_(i <- r | P i) df i) (\ten_(i <- r | P i) F i).
Proof. 
have {1}->: (set0 : {set L}) = \bigcup_(i <- r | P i) set0 by rewrite big1. 
apply/tends_wf. 
Qed.
Canonical tens_ketdirac I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, 'Ket[H]_(df i)) := KetDirac (tends_wf_ket r P F).

Lemma tends_wf_bra I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, 'Bra[H]_(df i)) : 
  brad (\bigcup_(i <- r | P i) df i) (\ten_(i <- r | P i) F i).
Proof. 
have {2}->: (set0 : {set L}) = \bigcup_(i <- r | P i) set0 by rewrite big1.
apply/tends_wf.
Qed.
Canonical tens_bradirac I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i : I, 'Bra[H]_(df i)) := BraDirac (tends_wf_bra r P F).

(* generally, its better to use lfun for add after calculations *)
Lemma sumd_wf I (r : seq I) (P : pred I) S T (F : I -> 'D[H]_(S,T)) : 
  wfd S T (\sum_(i <- r | P i) (F i : 'D)).
Proof.
elim: r=>[|x r P1]; first by rewrite !big_nil; apply/wfdP.
rewrite !big_cons; case: (P x)=>//; rewrite (wfdE P1); apply/wfdP.
Qed.
Canonical sumd_wfdirac I (r : seq I) (P : pred I) S T (F : I -> 'D[H]_(S,T)) 
  := WFDirac (sumd_wf r P F).

Lemma sumd_wf_sqr I (r : seq I) (P : pred I) S (F : I -> 'D[H]_S) : 
  sqrd S (\sum_(i <- r | P i) (F i : 'D)).
Proof. apply/sumd_wf. Qed.
Canonical sum_sqrdirac I (r : seq I) (P : pred I) S (F : I -> 'D[H]_S) 
 := SqrDirac (sumd_wf_sqr r P F).

Lemma sumd_wf_ket I (r : seq I) (P : pred I) S (F : I -> 'Ket[H]_S) : 
  ketd S (\sum_(i <- r | P i) (F i : 'D)).
Proof. apply/sumd_wf. Qed.
Canonical sum_ketdirac I (r : seq I) (P : pred I) S (F : I -> 'Ket[H]_S) 
 := KetDirac (sumd_wf_ket r P F).

Lemma sumd_wf_bra I (r : seq I) (P : pred I) S (F : I -> 'Bra[H]_S) : 
  brad S (\sum_(i <- r | P i) (F i : 'D)).
Proof. apply/sumd_wf. Qed.
Canonical sum_bradirac I (r : seq I) (P : pred I) S (F : I -> 'Bra[H]_S) 
 := BraDirac (sumd_wf_bra r P F).

(* big dot only canonical when: all square, all ket and all bra *)
Lemma dotds_wf_sqr I (r : seq I) (P : pred I) (df : I -> {set L})
 (F : forall i, 'D[H]_(df i)) : 
  sqrd (\bigcup_(i <- r | P i) df i) (\dot_(i <- r | P i) (F i : 'D)).
Proof.
rewrite !bigd; elim: r=>[|x r P1]; first by rewrite !big_nil; apply/sqrdP.
rewrite !big_cons; case: (P x)=>//; rewrite (sqrdE P1); apply/sqrdP.
Qed.
Canonical dots_sqrdirac I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i, 'D[H]_(df i)) 
 := SqrDirac (dotds_wf_sqr r P F).

Lemma dotds_wf_ket I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i, 'Ket[H]_(df i)) : 
  ketd (\bigcup_(i <- r | P i) df i) (\dot_(i <- r | P i) (F i : 'D)).
Proof.
rewrite !bigd; elim: r=>[|x r P1]; first by rewrite !big_nil; apply/ketP.
rewrite !big_cons; case: (P x)=>//; rewrite (ketE P1); apply/ketP.
Qed.
Canonical dots_ketdirac I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i, 'Ket[H]_(df i)) 
  := KetDirac (dotds_wf_ket r P F).

Lemma dotds_wf_bra I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i, 'Bra[H]_(df i)) : 
  brad (\bigcup_(i <- r | P i) df i) (\dot_(i <- r | P i) (F i : 'D)).
Proof.
rewrite !bigd; elim: r=>[|x r P1]; first by rewrite !big_nil; apply/braP.
rewrite !big_cons; case: (P x)=>//; rewrite (braE P1); apply/braP.
Qed.
Canonical dots_bradirac I (r : seq I) (P : pred I) (df : I -> {set L})
  (F : forall i, 'Bra[H]_(df i))
 := BraDirac (dotds_wf_bra r P F).

(* extra conditions, used to add user-defined structures *)

Lemma sqr_linP S S' (P : 'F[H]_S) : sqrd S' (dlin P) <-> ((S == S') || (P == 0)).
Proof.
split. move=>/wfd_def. case: eqP=>//; case: eqP=>// H1 /eqP H2 H3.
exfalso. apply H1. move: H3; rewrite dlin_eq0l 1?eq_sym// =>/diracP/(_ S S).
by rewrite dlin_id linear0 diracE.
move=>/orP[/eqP<-|/eqP->]; rewrite ?linear0; apply/sqrdP.
Qed.

(* form is frequently used, define dform to provide canonical structure *)
Definition dform (e1 e2 : 'D[H]) := e1^A \· e2 \· e1.
Lemma dformE (e1 e2 : 'D[H]) : dform e1 e2 = e1^A \· e2 \· e1. Proof. by []. Qed.
Lemma dform_sqr S T W (e1 : 'D[H]_(S,T)) (e2 : 'D_W) :
  sqrd (S :|: W :\: T) (dform e1 e2).
Proof.
rewrite /dform wfd_linE sqrd_linE adjd_lin !dotd_correct.
apply/wfdP_eq=>/=; setdec.
Qed.
Canonical dform_wfdirac S T W e1 e2 := WFDirac (@dform_sqr S T W e1 e2).
Canonical dform_sqrdirac S T W e1 e2 := SqrDirac (@dform_sqr S T W e1 e2).

Lemma dform_is_linear e1 : linear (@dform e1).
Proof. by move=>a x y; rewrite /dform linearPr/= linearPl/=. Qed.
Canonical dform_additive e1 := Additive (@dform_is_linear e1).
Canonical dform_linear e1 := Linear (@dform_is_linear e1).

Lemma dformEV (e1 e2 : 'D[H]) : dform e1^A e2 = e1 \· e2 \· e1^A.
Proof. by rewrite dformE adjdK. Qed.

End WFDiracTheory.

Section ExtraDiracTheory.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T W : {set L}).

Lemma tendfC S T S' T' (f: 'F[H]_(S,T)) (g: 'F_(S',T')) : 
  '[f \⊗ g] = '[g \⊗ f].
Proof. by rewrite -tend_correct tendC tend_correct. Qed.

Lemma tendfA S1 T1 S2 T2 S3 T3 (f: 'F[H]_(S1,T1)) (g: 'F_(S2,T2))
  (h: 'F[H]_(S3,T3)) : 
  '[ f \⊗ (g \⊗ h) ] = '[ (f \⊗ g) \⊗ h ].
Proof. by rewrite -!tend_correct tendA. Qed.

Lemma tendf1 S T (f: 'F[H]_(S,T))  : 
  '[ f \⊗ (\1 : 'F_set0) ] = '[f].
Proof. by rewrite -tend_correct dInum tend1. Qed.

Lemma tend1f S T (f: 'F[H]_(S,T))  : 
  '[ (\1 : 'F_set0) \⊗ f ] = '[f].
Proof. by rewrite tendfC tendf1. Qed.

Lemma dotdfA S1 T1 S2 T2 S3 T3 (f: 'F[H]_(S1,T1)) (g: 'F_(S2,T2))
  (h: 'F_(S3,T3)) : 
  [disjoint S2 & S1 :\: T2] -> [disjoint T2 & T3 :\: S2] ->
  '[ f \· (g \· h) ] = '[ f \· g \· h ].
Proof. by move=>P1 P2; to_Fnd; rewrite dotFA_cond. Qed.  

Lemma dotdA_cond S1 T1 S2 T2 S3 T3 (e1: 'D[H]_(S1,T1)) (e2: 'D_(S2,T2))
  (e3: 'D_(S3,T3)) :
  [disjoint S2 & S1 :\: T2] -> [disjoint T2 & T3 :\: S2] ->
  e1 \· (e2 \· e3) = e1 \· e2 \· e3.
Proof. 
by move=>P1 P2; rewrite wfd_linE (wfd_linE e2) (wfd_linE e3) !dotd_correct dotdfA.
Qed.

Lemma dotdA S1 T1 S2 S3 T3 (e1: 'D[H]_(S1,T1)) (e2: 'D_S2)
  (e3: 'D_(S3,T3)) :
  e1 \· (e2 \· e3) = e1 \· e2 \· e3.
Proof. by rewrite dotdA_cond// disjointXD. Qed.

Lemma dform_comp S T S' W (e1 : 'D[H]_(S,T)) (e2 : 'D_S') (e3 : 'D_W) :
  dform e1 (dform e2 e3) = dform (e2 \· e1) e3.
Proof. by rewrite !dformE adjdG !dotdA_cond//; setdec. Qed.

Lemma dform_compv S S' W W' (e1 : 'Bra[H]_S) (e2 : 'Ket_S') (e3 : 'D_(W,W')) :
  dform e1 (dform e2 e3) = dform (e2 \· e1) e3.
Proof. by rewrite !dformE adjdG !dotdA_cond//; setdec. Qed.

Lemma dotdf_ten S1 T1 S2 T2 (f: 'F[H]_(S1,T1)) (g: 'F_(S2,T2)) :
  [disjoint S1 & T2] -> 
  '[ f \· g ] = '[ f \⊗ g ].
Proof. by move=>P3; to_Fnd; rewrite/= dotFT. Qed.

Lemma dotd_ten S1 T1 S2 T2 (e1: 'D[H]_(S1,T1)) (e2: 'D_(S2,T2)) :
  [disjoint S1 & T2] -> 
  e1 \· e2 = e1 \⊗ e2.
Proof. 
by move=>P1; rewrite wfd_linE (wfd_linE e2) !dotd_correct tend_correct dotdf_ten.
Qed.

Lemma dotdfC S T S' T' (f: 'F[H]_(S,T)) (g: 'F_(S',T')) : 
  [disjoint S & T'] -> [disjoint T & S'] ->
  '[ f \· g ] = '[ g \· f ].
Proof. by move=>P1 P2; to_Fnd; rewrite dotFC. Qed.

Lemma dotdC S T S' T' (e1: 'D[H]_(S,T)) (e2: 'D_(S',T')) :
  [disjoint S & T'] -> [disjoint T & S'] ->
  e1 \· e2 = e2 \· e1.
Proof. 
by move=>P1 P2; rewrite wfd_linE (wfd_linE e2) !dotd_correct dotdfC.
Qed.

Lemma dotdf1 S T (f: 'F[H]_(S,T))  : 
  '[ f \· (\1 : 'F_set0) ] = '[f].
Proof. by to_Fnd; rewrite dotF1. Qed.

Lemma dotd1f S T (f: 'F[H]_(S,T))  : 
  '[ (\1 : 'F_set0) \· f ] = '[f].
Proof. by to_Fnd; rewrite dot1F. Qed.

Lemma dotdf_comp S T W (f: 'F[H]_(S,T)) (g: 'F_(W,S)) :
  '[ f \· g ] = '[ f \o g ].
Proof. by to_Fnd. Qed.

Lemma dotd_mul S T W (e1: 'D[H]_(S,T)) (e2: 'D_(W,S)) :
  e1 \· e2 = e1 \o e2.
Proof. 
by rewrite wfd_linE (wfd_linE e2) !dirac_correct dotdf_comp.
Qed.

Lemma mulId S T (e : 'D[H]_(T,S)) : \1_S \o e = e.
Proof. by rewrite wfd_linE muld_correct comp_lfun1l. Qed.

Lemma muldI S T (e : 'D[H]_(S,T)) : e \o \1_S = e.
Proof. by rewrite wfd_linE muld_correct comp_lfun1r. Qed.

Lemma muld_lin S T W (e1 : 'D[H]_(S,T)) (e2 : 'D_(W,S)) :
  e1 \o e2 = dlin (e1 S T \o e2 W S).
Proof. by rewrite {1}wfd_linE {1}(wfd_linE e2) muld_correct. Qed.

Lemma tend_mul S T S' T' W W' (e1: 'D[H]_(S,T)) (e2: 'D_(W,S)) 
  (e3: 'D_(S',T')) (e4: 'D_(W',S')) :
  [disjoint S & S'] ->
  (e1 \⊗ e3) \o (e2 \⊗ e4) = (e1 \o e2) \⊗ (e3 \o e4).
Proof.
by move=>P; rewrite wfd_linE (wfd_linE e2) (wfd_linE e3) (wfd_linE e4) !dirac_correct tenf_comp.
Qed.

Lemma dotIdT S T W (e : 'D[H]_(T,W)) : \1_S \· e =  \1_(S :\: W) \⊗ e.
Proof.
rewrite wfd_linE !dirac_correct; to_Fnd; 
by rewrite dotIF dotFT//= disjointDX.
Qed.

Lemma dotdIT S T W (e : 'D[H]_(T,W)) : e \· \1_S =  \1_(S :\: T) \⊗ e.
Proof.
rewrite tendC wfd_linE !dirac_correct; to_Fnd;
by rewrite dotFI dotFT//= disjointXD.
Qed.

Lemma dotId S T W (e : 'D[H]_(T,W)) : \1_S \· e =  \1_(S :\: W) \· e.
Proof. by rewrite dotIdT dotd_ten// disjointDX. Qed.

Lemma dotdI S T W (e : 'D[H]_(T,W)) : e \· \1_S = e \· \1_(S :\: T).
Proof. by rewrite dotdIT tendC dotd_ten// disjointXD. Qed.

Lemma dotIdid S T W (e : 'D[H]_(T,W)) : S :<=: W -> \1_S \· e = e.
Proof. by rewrite -setD_eq0 dotIdT=>/eqP->; rewrite dInum ten1d. Qed.

Lemma dotdIid S T W (e : 'D[H]_(T,W)) : S :<=: T -> e \· \1_S = e.
Proof. by rewrite -setD_eq0 dotdIT=>/eqP->; rewrite dInum ten1d. Qed.

Lemma dotd_multen S T S' T' (e1 : 'D[H]_(S,T)) (e2 : 'D_(S',T')) : 
  e1 \· e2 = (e1 \⊗ \1_( T' :\: S )) \o (e2 \⊗ \1_( S :\: T' )).
Proof.
rewrite wfd_linE (wfd_linE e2) !dirac_correct.
by rewrite dot_lfun_unfold -muld_correct dlin_cast -!tend_correct/=.
Qed.

Lemma dotd_muldot S T S' T' (e1 : 'D[H]_(S,T)) (e2 : 'D[H]_(S',T')) :
  e1 \· e2 = (e1 \· \1_T') \o (\1_S \· e2).
Proof. by rewrite dotd_multen/= tendC -dotdIT/= tendC -dotIdT. Qed.

Lemma tendII S T : (\1_S : 'D[H]) \⊗ (\1_T) = \1_(S :|: T).
Proof. by rewrite tend_correct tenf11. Qed.

Lemma dotdII S T : (\1_S : 'D[H]) \· (\1_T) = \1_(S :|: T).
Proof. by rewrite dotdI/= dotd_ten ?disjointXD//= tendII setUD. Qed.

Lemma d2cK (e : 'D[H]_(set0,set0)) : (d2c e)%:D = e.
Proof. by rewrite wfd_linE /d2c dlin_id dnum_lin sf2sK. Qed.

Lemma innerM S (u v : 'H[H]_S) : '<u| \o '|v> = [<u ; v>]%:D.
Proof. by rewrite dbra_lin dket_lin muld_correct comp_dot -dnum_lin. Qed.
Lemma innerG S (u v : 'H[H]_S) : '<u| \· '|v> = [<u ; v>]%:D.
Proof. by rewrite dotd_mul/= innerM. Qed.
Lemma outerM S T (u : 'H[H]_S) (v : 'H[H]_T) : '|v> \o '<u| = '[ [> v ; u <] ].
Proof. by rewrite dbra_lin dket_lin muld_correct comp_out. Qed.
Lemma outerG S T (u : 'H[H]_S) (v : 'H[H]_T) : '|v> \· '<u| = '[ [> v ; u <] ].
Proof. by rewrite dotd_mul/= outerM. Qed.
Definition innerE := (innerM, innerG).
Definition outerE := (outerM, outerG).

Definition ket_conj := (@conjd_ket _ H).
Definition ket_adj  := (@adjd_ket _ H).
Definition ket_tr   := (@trd_ket _ H).
Lemma ketT S T (u: 'H[H]_S) (v: 'H_T) : '|u> \⊗ '|v> = '|u ⊗v v>.
Proof.
rewrite 2!dket_lin tend_correct /v2f tenf_outp tenv_idx0r -outerM -[RHS]muldI/=.
by f_equal; rewrite dbra_cast !dnum_simp /sf2s /sv2s lfunE/= dv_dot eqxx conjc1.
Qed.

Definition bra_conj := (@conjd_bra _ H).
Definition bra_adj  := (@adjd_bra _ H).
Definition bra_tr   := (@trd_bra _ H).
Lemma braT S T (u: 'H[H]_S) (v: 'H_T) : '<u| \⊗ '<v| = '<u ⊗v v|.
Proof. by rewrite -!ket_adj -adjdT ketT. Qed.

Definition lin_conj := (@conjd_lin _ H).
Definition lin_adj  := (@adjd_lin _ H).
Definition lin_tr   := (@trd_lin _ H).
Lemma linM S T W (f : 'F[H]_(S,T)) (g : 'F_(W,S)) : '[f] \o '[g] = '[f \o g].
Proof. by rewrite muld_correct. Qed.

Lemma linG S T W (f : 'F[H]_(S,T)) (g : 'F_(W,S)) : '[f] \· '[g] = '[f \o g].
Proof. by rewrite dotd_mul/= linM. Qed.

Lemma linT S T S' T' (f : 'F[H]_(S,T)) (g : 'F_(S',T')) :
  '[f] \⊗ '[g] = '[f \⊗ g].
Proof. by rewrite tend_correct. Qed.

Lemma lin_lind S T S' T' (f : 'F[H]_(S,T)) (g : 'F_(S',T')) :
  '[f] \· '[g] = '[f \· g].
Proof. by rewrite dotd_correct. Qed.

Lemma lin_ketM S T (f : 'F[H]_(S,T)) (v : 'H_S) : '[f] \o '|v> = '|f v>.
Proof. by rewrite !dket_lin muld_correct -[(_ \o _)%VF]f2vK v2f_comp. Qed. 

Lemma lin_ketG S T (f : 'F[H]_(S,T)) (v : 'H_S) : '[f] \· '|v> = '|f v>.
Proof. by rewrite dotd_mul/= lin_ketM. Qed.

Definition lin_ket := (lin_ketM, lin_ketG).

Lemma lin_braM S T (f : 'F[H]_(S,T)) (v : 'H_T) : '<v| \o '[f] = '<f^A v|.
Proof. by rewrite -[_ \o _]adjdK adjdM bra_adj lin_adj lin_ket ket_adj. Qed.

Lemma lin_braG S T (f : 'F[H]_(S,T)) (v : 'H_T) : '<v| \· '[f] = '<f^A v|.
Proof. by rewrite dotd_mul/= lin_braM. Qed.

Definition lin_bra := (lin_braM, lin_braG).

Lemma dotfTl (S1 S2 S3 T1 T2 T3 : {set L}) (f : 'F[H]_(S1,T1)) 
  (g : 'F_(S2,T2)) (h : 'F_(S3,T3)) :
  [disjoint S1 & T3] -> [disjoint T2 & T3] ->
  f \· (g \⊗ h) =c f \· g \⊗ h.
Proof.
move=>P1 P2; rewrite -{2}[h]comp_lfun1l dot_lfun_unfold tenf_comp/=.
move: P1 P2; setdec. to_Fnd; f_equal.
rewrite -tenFA tenF11; f_equal; apply Fnd_eq1.
rewrite setDUl; f_equal; apply/setDidPl; move: P1 P2; setdec.
rewrite tenFC tenFA; f_equal; rewrite tenFC; f_equal; apply Fnd_eq1.
by move: P1=>/setDidPl; rewrite setUC -setDDl=>->.
Qed.

Lemma dotfTr (S1 S2 S3 T1 T2 T3 : {set L}) (f : 'F[H]_(S1,T1)) 
  (g : 'F[H]_(S2,T2)) (h : 'F[H]_(S3,T3)) :
  [disjoint T1 & S3] -> [disjoint S2 & S3] ->
    (g \⊗ h) \· f =c g \· f \⊗ h.
Proof.
move=> P1 P2; rewrite -{2}[h]comp_lfun1r dot_lfun_unfold tenf_comp/=.
move: P1 P2; setdec. to_Fnd; f_equal.
rewrite -!tenFA; f_equal; rewrite tenFC; f_equal; apply Fnd_eq1.
by move: P1=>/setDidPl; rewrite setUC -setDDl=>->.
rewrite -tenFA tenF11; f_equal; apply Fnd_eq1.
rewrite setDUl; f_equal; apply/setDidPl; move: P1 P2; setdec.
Qed.

Lemma dotdTll S1 S2 S3 T1 T2 T3 (e1 : 'D[H]_(S1,T1)) 
  (e2 : 'D_(S2,T2)) (e3 : 'D_(S3,T3)) :
  [disjoint S1 & T3] -> [disjoint T2 & T3] ->
  e1 \· (e2 \⊗ e3) = e1 \· e2 \⊗ e3.
Proof.
move=>P1 P2. rewrite wfd_linE (wfd_linE e2) (wfd_linE e3).
by rewrite !dirac_correct; apply dlin_eqFnd; rewrite dotfTl.
Qed.

Lemma dotdTlr S1 S2 S3 T1 T2 T3 (e1 : 'D[H]_(S1,T1)) 
  (e2 : 'D_(S2,T2)) (e3 : 'D_(S3,T3)) : 
  [disjoint S1 & T2] -> [disjoint T3 & T2] ->
    e1 \· (e2 \⊗ e3) = e2 \⊗ (e1 \· e3).
Proof. by move=>P1 P2; rewrite tendC dotdTll 1?tendC. Qed.

Lemma dotdTrl S1 S2 S3 T1 T2 T3 (e1 : 'D[H]_(S1,T1)) 
  (e2 : 'D_(S2,T2)) (e3 : 'D_(S3,T3)) :
  [disjoint T1 & S3] -> [disjoint S2 & S3] ->
  (e2 \⊗ e3) \· e1 = (e2 \· e1) \⊗ e3.
Proof.
move=>P1 P2. rewrite wfd_linE (wfd_linE e1) (wfd_linE e3).
by rewrite !dirac_correct; apply dlin_eqFnd; rewrite dotfTr.
Qed.

Lemma dotdTrr S1 S2 S3 T1 T2 T3 (e1 : 'D[H]_(S1,T1)) 
  (e2 : 'D_(S2,T2)) (e3 : 'D_(S3,T3)) :
  [disjoint T1 & S2] -> [disjoint S3 & S2] ->
  (e2 \⊗ e3) \· e1 = e2 \⊗ (e3 \· e1).
Proof. by move=>P1 P2; rewrite tendC dotdTrl 1?tendC. Qed.

Lemma lin_linTll S T S' T' (f : 'F[H]_S) (g : 'F[H]_(T,S)) (e : 'D_(S',T')) : 
  [disjoint S & T'] ->
  '[ f ] \· ('[ g ] \⊗ e) = '[ f \o g ] \⊗ e.
Proof. by move=>P1; rewrite -linG dotdTll. Qed.

Lemma lin_linTlr S T S' T' (f : 'F[H]_S) (g : 'F[H]_(T,S)) (e : 'D_(S',T')) :
  [disjoint S & T'] ->
  '[ f ] \· (e \⊗ '[ g ]) = e \⊗ '[ f \o g ].
Proof. by move=>P1; rewrite -linG dotdTlr. Qed.

Lemma lin_linTrl S T S' T' (f : 'F[H]_(S,T)) (g : 'F[H]_S) (e : 'D_(S',T')) : 
  [disjoint S & S'] ->
  ('[ f ] \⊗ e) \· '[ g ] = '[ f \o g ] \⊗ e.
Proof. by move=>P1; rewrite -linG dotdTrl. Qed.

Lemma lin_linTrr S T S' T' (f : 'F[H]_(S,T)) (g : 'F[H]_S) (e : 'D_(S',T')) : 
  [disjoint S & S'] ->
  (e \⊗ '[ f ]) \· '[ g ] = e \⊗ '[ f \o g ].
Proof. by move=>P1; rewrite -linG dotdTrr. Qed.

Lemma lin_ketTl S S' T' (f : 'F[H]_S) (v : 'H[H]_S) (e : 'D_(S',T')) : 
  [disjoint S & T'] ->
  '[ f ] \· ('|v> \⊗ e) = '|f v> \⊗ e.
Proof. by move=>P1; rewrite -lin_ketG dotdTll. Qed.

Lemma lin_ketTr S S' T' (f : 'F[H]_S) (v : 'H[H]_S) (e : 'D_(S',T')) : 
  [disjoint S & T'] ->
  '[ f ] \· (e \⊗ '|v>) = e \⊗ '|f v>.
Proof. by move=>P1; rewrite -lin_ketG dotdTlr. Qed.

Lemma lin_braTl S S' T' (f : 'F[H]_S) (v : 'H[H]_S) (e : 'D_(S',T')) : 
  [disjoint S & S'] ->
  ('<v| \⊗ e) \· '[ f ] = '<f^A v| \⊗ e.
Proof. by move=>P1; rewrite -lin_braG dotdTrl. Qed.

Lemma lin_braTr S S' T' (f : 'F[H]_S) (v : 'H[H]_S) (e : 'D_(S',T')) : 
  [disjoint S & S'] ->
  (e \⊗ '<v|) \· '[ f ] = e \⊗ '<f^A v|.
Proof. by move=>P1; rewrite -lin_braG dotdTrr. Qed.

Lemma form_dot_mul S T (e : 'D[H]_(S,T)) : e \· e^A = e \o e^A.
Proof. by rewrite dotd_mul. Qed.

Lemma tens_adj (I : Type) (r : seq I) (P : pred I) (F : I -> 'D[H]) :
  (\ten_(i <- r | P i) F i)^A = \ten_(i <- r | P i) (F i)^A.
Proof.
rewrite !bigd; elim: r=>[|x r IH]; first by rewrite !big_nil adjd1.
by rewrite !big_cons; case: (P x)=>//; rewrite adjdT IH.
Qed.

Lemma tens_tr (I : Type) (r : seq I) (P : pred I) (F : I -> 'D[H]) :
  (\ten_(i <- r | P i) F i)^T = \ten_(i <- r | P i) (F i)^T.
Proof.
rewrite !bigd; elim: r=>[|x r IH]; first by rewrite !big_nil trd1.
by rewrite !big_cons; case: (P x)=>//; rewrite trdT IH.
Qed.

Lemma tens_conj (I : Type) (r : seq I) (P : pred I) (F : I -> 'D[H]) :
(\ten_(i <- r | P i) F i)^C = \ten_(i <- r | P i) (F i)^C.
Proof. by rewrite dC2AT tens_adj tens_tr; under eq_bigr do rewrite -dC2AT. Qed.

Lemma ketBT_adj (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
  (\ten_(i <- r | P i) '|F i>)^A = \ten_(i <- r | P i) '<F i|.
Proof. by rewrite tens_adj; under eq_bigr do rewrite ket_adj. Qed.

Lemma ketBT_tr (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
  (\ten_(i <- r | P i) '|F i>)^T = \ten_(i <- r | P i) '<(F i)^*v|.
Proof. by rewrite tens_tr; under eq_bigr do rewrite ket_tr. Qed.

Lemma ketBT_conj (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
(\ten_(i <- r | P i) '|F i>)^C = \ten_(i <- r | P i) '|(F i)^*v>.
Proof. by rewrite tens_conj; under eq_bigr do rewrite ket_conj. Qed.

Lemma braBT_adj (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
  (\ten_(i <- r | P i) '<F i|)^A = \ten_(i <- r | P i) '|F i>.
Proof. by rewrite tens_adj; under eq_bigr do rewrite bra_adj. Qed.

Lemma braBT_tr (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
(\ten_(i <- r | P i) '<F i|)^T = \ten_(i <- r | P i) '|(F i)^*v>.
Proof. by rewrite tens_tr; under eq_bigr do rewrite bra_tr. Qed.

Lemma braBT_conj (I : Type) (r : seq I) (P : pred I) (d : I -> {set L}) 
  (F : forall i, 'H[H]_(d i)) :
  (\ten_(i <- r | P i) '<F i|)^C = \ten_(i <- r | P i) '<(F i)^*v|.
Proof. by rewrite tens_conj; under eq_bigr do rewrite bra_conj. Qed.

Lemma tensZ (T : Type) (r : seq T) (P : pred T) (fz : T -> C) (e : T -> 'D[H]) :
  \ten_(i <- r | P i) ((fz i) *: (e i)) = 
    \prod_(i <- r | P i) (fz i) *: \ten_(i <- r | P i) (e i).
Proof.
elim/big_rec3: _=>[|i e1 c e2 _]; first by rewrite bigd scale1r.
by rewrite bigd=>->; rewrite tendZl tendZr scalerA.
Qed.

Lemma tensI F (r : seq F) (P : pred F) (fd : F -> {set L}) :
  \ten_(i <- r | P i) \1_(fd i) = \1_(\bigcup_(i <- r | P i) fd i) :> 'D[H].
Proof.
elim/big_rec2: _=>[|i x y]; first by rewrite bigd dnumI.
by move=>Pi; rewrite bigd=>->; rewrite tendII.
Qed.

Lemma tensM (I : eqType) (r : seq I) (P : pred I) (d1 d2 d3 : I -> {set L})
  (F : forall i : I, 'D[H]_(d1 i, d2 i)) (G : forall i : I, 'D_(d3 i, d1 i)) :
  (forall i j, P i -> P j -> (i != j) -> [disjoint d1 i & d1 j]) -> 
  uniq r ->
  (\ten_(i <- r | P i) F i) \o \ten_(i <- r | P i) (G i) = 
  (\ten_(i <- r | P i) (F i \o G i)).
Proof.
elim: r=>[_|x r IH]; first by rewrite !big_nil bigd {1}dnumI mulId.
move=>Pij. rewrite cons_uniq=>/andP[Px ur].
rewrite !big_cons; case E: (P x); last by apply IH.
rewrite ?bigdE tend_mul/= ?IH//.
apply/bigcup_disjoint_seqP=>i /andP[ii Pi]; apply Pij=>//.
by move: Px; move=>/memPnC/(_ _ ii).
Qed.

Lemma dnumBT (I : eqType) (r : seq I) (P : pred I) (F : I -> C) :
\ten_(i <- r | P i) ((F i)%:D : 'D[H]) = (\prod_(i <- r | P i) (F i))%:D.
Proof.
elim: r=>[|x r IH]; first by rewrite !big_nil bigd.
by rewrite !big_cons; case: (P x)=>[|//]; rewrite bigdE IH dnumT; f_equal.
Qed.

Lemma outerMBT (I : Type) (r : seq I) (P : pred I) (Dv Du : I -> {set L}) 
  (Vs : forall i, 'H[H]_(Dv i)) (Us : forall i, 'H[H]_(Du i)) : 
  (\ten_(i <- r | P i) '|Vs i>) \o (\ten_(i <- r | P i) '<Us i|) 
  = \ten_(i <- r | P i) ('|Vs i> \o '<Us i|).
Proof.
elim: r=>[|x r IH]; first by rewrite !big_nil bigd {1}dnumI mulId.
rewrite !big_cons; case E: (P x); last by apply IH.
by rewrite ?bigdE tend_mul ?disjoint0X//= IH.
Qed.

Lemma outerGBT (I : Type) (r : seq I) (P : pred I) (Dv Du : I -> {set L}) 
  (Vs : forall i, 'H[H]_(Dv i)) (Us : forall i, 'H[H]_(Du i)) : 
  (\ten_(i <- r | P i) '|Vs i>) \· (\ten_(i <- r | P i) '<Us i|) 
  = \ten_(i <- r | P i) ('|Vs i> \· '<Us i|).
Proof.
rewrite dotd_mul/= outerMBT//. 
by under eq_bigr do rewrite -dotd_mul.
Qed.

Lemma innerMBT (I : eqType) (r : seq I) (P : pred I) (Ds : I -> {set L}) 
  (Vs Us : forall i, 'H[H]_(Ds i)) : 
    (forall i j, P i -> P j -> (i != j) -> [disjoint Ds i & Ds j]) -> uniq r ->
      (\ten_(i <- r | P i) '<Vs i|) \o (\ten_(i <- r | P i) '|Us i>)
        = (\prod_(i <- r | P i) [<Vs i ; Us i>])%:D.
Proof.
by move=>P1 P2; rewrite tensM// -dnumBT; under eq_bigr do rewrite innerM.
Qed.

Lemma innerGBT (I : eqType) (r : seq I) (P : pred I) (Ds : I -> {set L}) 
  (Vs Us : forall i, 'H[H]_(Ds i)) : 
    (forall i j, P i -> P j -> (i != j) -> [disjoint Ds i & Ds j]) -> uniq r ->
      (\ten_(i <- r | P i) '<Vs i|) \· (\ten_(i <- r | P i) '|Us i>)
        = (\prod_(i <- r | P i) [<Vs i ; Us i>])%:D.
Proof. by rewrite dotd_mul/=; apply innerMBT. Qed.

Lemma outerMBTs (r : seq L) (P: pred L) (Vs Us : forall i : L, 'H[H]_[set i]) : 
  (\ten_(i <- r | P i) '|Vs i>) \o (\ten_(i <- r | P i) '<Us i|) 
  = \ten_(i <- r | P i) ('|Vs i> \o '<Us i|).
Proof. by rewrite outerMBT. Qed.

Lemma innerMBTs (r : seq L) (P: pred L) (Vs Us: forall i : L, 'H[H]_[set i]) : 
uniq r ->
(\ten_(i <- r | P i) '<Vs i|) \o (\ten_(i <- r | P i) '|Us i>) 
= (\prod_(i <- r | P i) [<Vs i ; Us i>])%:D.
Proof. by move=>ur; rewrite innerMBT// =>i j _ _; rewrite disjoint1X inE. Qed.

End ExtraDiracTheory.

(* here we give the relation between tenvm tenfm and \ten_s *)
(* they are indeed the same, without any conditions *)
Section BigTenLfun.
Context (L : finType) (H : L -> chsType).

Lemma dket_Hnd_eq (x y : Hnd H) : x = y -> '| of_Hnd x > = '| of_Hnd y >.
Proof. by move=>P; move: (eq_HndP P)=><-; rewrite dket_cast. Qed.
Lemma dlin_Fnd_eq (x y : Fnd H) : x = y -> '[ of_Fnd x ] = '[ of_Fnd y ].
Proof. by move=>P; move: (eq_FndP P)=><-; rewrite dlin_cast. Qed.
Lemma ketBT_Hnd (I : Type) (r : seq I) (P : pred I) 
  (s : I -> {set L}) (v : forall i : I, 'H[H]_(s i)) :
    \ten_(i <- r | P i) '|v i> = '| (\tenv_(i <- r | P i) (v i))%FND >.
Proof.
elim/big_rec2: _; first by rewrite bigd dket_lin /v2f outp_dv0 dInum.
by move=>i y1 y2 _; rewrite bigd=>->; rewrite /Hnd_ten ketT.
Qed.
Lemma linBT_Fnd (I : Type) (r : seq I) (P : pred I) 
  (s t : I -> {set L}) (v : forall i : I, 'F[H]_(s i, t i)) :
    \ten_(i <- r | P i) '[v i] = '[ (\tenf_(i <- r | P i) (v i))%FND ].
Proof.
elim/big_rec2: _; first by rewrite bigd/= dInum.
by move=>i y1 y2 _; rewrite bigd=>->; rewrite /Fnd_ten linT.
Qed.

Lemma tenvm_correct (J : finType) (s : J -> {set L}) 
  (v : forall j : J, 'H[H]_(s j)) :
    \ten_j '|v j> = '|tenvm v>.
Proof. by rewrite - [tenvm v]to_HndK (dket_Hnd_eq (to_Hnd_tens _)); apply/ketBT_Hnd. Qed.

Lemma tenfm_correct (J : finType) (s t : J -> {set L}) (v : forall j : J, 'F[H]_(s j, t j)) :
  \ten_j '[ v j ] = '[ tenfm v ].
Proof. by rewrite - [tenfm v]to_FndK (dlin_Fnd_eq (to_Fnd_tens _)); apply/linBT_Fnd. Qed.

End BigTenLfun.

Reserved Notation "''QONB'".
Reserved Notation "''QONB_' ( F ; S )"      (at level 8, format "''QONB_' ( F ;  S )").
Reserved Notation "''QONB[' H ]_ ( F ; S )"     (at level 8).
Reserved Notation "[ 'QONB' 'of' f 'as' g ]" (at level 0, format "[ 'QONB'  'of'  f  'as'  g ]").
Reserved Notation "[ 'QONB' 'of' f ]"  (at level 0, format "[ 'QONB'  'of'  f ]").

Reserved Notation "''QNS'".
Reserved Notation "''QNS_' S"       (at level 8, S at level 2, format "''QNS_' S").
Reserved Notation "''QNS_' ( S )"   (at level 8).
Reserved Notation "''QNS[' H ]_ S"  (at level 8, S at level 2).
Reserved Notation "''QNS[' H ]_ ( S )"     (at level 8).
Reserved Notation "''QNS' ( S )"    (at level 8, format "''QNS' ( S )").
Reserved Notation "[ 'QNS' 'of' f 'as' g ]" (at level 0, format "[ 'QNS'  'of'  f  'as'  g ]").
Reserved Notation "[ 'QNS' 'of' f ]"  (at level 0, format "[ 'QNS'  'of'  f ]").

Module QEONB.

Section ClassDef.
Variable (L : finType) (H : L -> chsType) (F : finType) (S : {set L}).

Definition axiom (f : F -> 'D[H]) := 
  (forall i, ketd S (f i)) /\
  (forall i j, (f i)^A \o (f j) = (i == j)%:R%:D)  /\ #|F| = Vector.dim 'H[H]_S.

Lemma axiom_split (f : F -> 'D[H]) :
  (forall i, ketd S (f i)) ->
  (forall i j, (f i)^A \o (f j)= (i == j)%:R%:D) ->
  #|F| = Vector.dim 'H[H]_S -> axiom f.
Proof. by rewrite /axiom; split. Qed.

Lemma axiom_split_ket (f : F -> 'Ket[H]_S) :
  (forall i j, (f i)^A \o (f j)= (i == j)%:R%:D) ->
  #|F| = Vector.dim 'H[H]_S -> axiom f.
Proof. apply/axiom_split=>i; apply/ketP. Qed.

Structure map (phUV : phant (F -> 'D[H])) := Pack {
  apply; 
  _ : axiom apply; 
}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (F -> 'D[H])) (f g : F -> 'D[H]) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation qonb f := (axiom f).
Coercion apply : map >-> Funclass.
Notation QONBasis fA fB fC := (Pack (Phant _) (axiom_split fA fB fC)).
Notation QONBket f fA fB := (@Pack _ _ _ _ (Phant _) f (axiom_split_ket fA fB)).
Notation "''QONB[' H ]_ ( F ; S )" := (map S (Phant (F -> 'D[H]))) : type_scope.
Notation "''QONB_' ( F ; S )" := ('QONB[_]_(F;S)) : type_scope.
Notation "''QONB'" := ('QONB_(_;_)) (only parsing) : type_scope.
Notation "[ 'QONB' 'of' f 'as' g ]" := (@clone _ _ _ _ _ f g _ _ idfun id) : form_scope.
Notation "[ 'QONB' 'of' f ]" := (@clone _ _ _ _ _ f f _ _ id id) : form_scope.
End Exports.

End QEONB.
Export QEONB.Exports.

Module QENormalizedState.

Section ClassDef.
Variable (L : finType) (H : L -> chsType) (F : finType) (S : {set L}).
Definition axiom (v : 'D[H]) := 
  ketd S v /\ v^A \o v = 1%:D.

Lemma axiom_split (v : 'D[H]) :
  ketd S v -> v^A \o v = 1%:D -> axiom v.
Proof. by rewrite /axiom; split. Qed.

Lemma axiom_split_ket (v : 'Ket[H]_S) :
  v^A \o v = 1%:D -> axiom v.
Proof. apply/axiom_split/ketP. Qed.

Structure type := Pack { sort; _ : axiom sort; }.
Local Coercion sort : type >-> dirac.

Variables (T : 'D[H]) (cT : type).
Definition class := let: Pack _ c as cT' := cT return (axiom cT') in c.
Definition clone c of phant_id class c := @Pack T c.

End ClassDef.

Module Import Exports.
Coercion sort : type >-> dirac.
Notation QNSType fA fB := (Pack (axiom_split fA fB)).
Notation QNSket v fA := (@Pack _ _ _ v (axiom_split_ket fA)).
Notation "''QNS[' H ]_ S" := (@type _ H S) (only parsing) : type_scope.
Notation "''QNS[' H ]_ ( S )" := ('QNS[H]_S)    (only parsing) : type_scope.
Notation "''QNS_' S"  := ('QNS[_]_S) : type_scope.
Notation "''QNS_' ( S )" := ('QNS_S) (only parsing) : type_scope.
Notation "[ 'QNS' 'of' f 'as' g ]" := (@clone _ _ _ f g _ idfun) : form_scope.
Notation "[ 'QNS' 'of' f ]" := (@clone _ _ _ f _ _ id) : form_scope.
End Exports.

End QENormalizedState.
Export QENormalizedState.Exports.

Section QEONBTheory.
Context {L : finType} (H : L -> chsType).
Variable (F : finType) (S : {set L}) (f : 'QONB[H]_(F;S)).

Lemma onb_wf i : ketd S (f i).
Proof. by case: f=>?/=[?]. Qed.
Canonical onb_wfdirac i := WFDirac (@onb_wf i).
Canonical onb_ketdirac i := KetDirac (@onb_wf i).

Lemma onb_innerM i j : (f i)^A \o (f j) = (i == j)%:R%:D.
Proof. by case: f=>?/=[?][->]. Qed.

Lemma onb_innerG i j : (f i)^A \· (f j) = (i == j)%:R%:D.
Proof. by rewrite dotd_mul/= onb_innerM. Qed.

Lemma donb_card : #|F| = Vector.dim 'H[H]_S.
Proof. by case: f=>?/=[?[??]]. Qed.

Definition onb2d (G : finType) (onb : 'ONB[H]_(G;S)) i := '|onb i>.
Lemma onb2d_dot G onb i j : (@onb2d G onb i)^A \o (@onb2d G onb j) = (i == j)%:R%:D.
Proof. by rewrite /onb2d ket_adj innerM onb_dot. Qed.
Canonical onb2d_qonbasis G onb := QONBket (@onb2d G onb) (@onb2d_dot G onb) (onb_card onb).

Definition d2onb i := d2v S (f i).
Lemma d2onb_dot i j : [< d2onb i ; d2onb j >] = (i == j)%:R.
Proof. by apply/(@dnum_inj _ H); rewrite /d2onb -innerM -ket_adj !d2vK onb_innerM. Qed.
Canonical d2onb_ponbasis := PONBasis d2onb_dot.
Canonical d2onb_onbasis := ONBasis d2onb_dot donb_card.

Lemma sumonb_outerM : \sum_i ((f i) \o (f i)^A) = \1_S.
Proof.
move: (sumonb_out d2onb_onbasis)=><-/=.
rewrite linear_sum/=; apply eq_bigr=>i _.
by rewrite -outerM /d2onb -ket_adj !d2vK.
Qed.

Lemma sumonb_outerG : \sum_i (f i) \· (f i)^A = \1_S.
Proof. by rewrite -sumonb_outerM; apply eq_bigr=>i _; rewrite dotd_mul. Qed.

Lemma onb_vecM (v : 'Ket_S) : (v : 'D) = \sum_i ((f i)^A \o v) \· f i.
Proof.
rewrite -d2vK {1}(onb_vec d2onb_onbasis (d2v S v)).
rewrite linear_sum; apply eq_bigr=>i _/=.
by rewrite linearZ/= -dnumGl /d2onb -innerM -ket_adj !d2vK.
Qed.

Lemma onb_vecG (v : 'Ket_S) : (v : 'D) = \sum_i ((f i)^A \· v) \· f i.
Proof. by rewrite {1}onb_vecM; apply eq_bigr=>i _; rewrite dotd_mul. Qed.

Lemma onb_lfunM (T : {set L}) (e : 'D_(S,T)) : 
  (e : 'D) = \sum_i (e \o (f i) \o (f i)^A).
Proof.
rewrite -[LHS]muldI -sumonb_outerM linear_sum/=.
by apply eq_bigr=>i _/=; rewrite muldA.
Qed.

Lemma onb_lfunM2 (e : 'D_S) : 
  (e : 'D) = \sum_i \sum_j ((f j)^A \o e \o (f i)) \· ((f j) \o (f i)^A).
Proof.
rewrite {1}onb_lfunM; apply eq_bigr=>i _/=.
rewrite [e \o f i]onb_vecM/= linear_suml; apply eq_bigr=>j _/=.
by rewrite !muldA -d2cK/= !dnumGl muldZl.
Qed.

Lemma ns_wf (v : 'QNS[H]_S) : ketd S v.
Proof. by case: v=>/=?[??]. Qed.
Canonical ns_wfdirac v := WFDirac (@ns_wf v).
Canonical ns_ketdirac v := KetDirac (@ns_wf v).

Lemma ns_innerM (v : 'QNS[H]_S) : v^A \o v = 1%:D.
Proof. by case: v=>/=?[??]. Qed.

Lemma ns_innerG (v : 'QNS[H]_S) : v^A \· v = 1%:D.
Proof. by rewrite dotd_mul/= ns_innerM. Qed.

Lemma donb_ns i : (f i)^A \o (f i) = 1%:D.
Proof. by rewrite onb_innerM eqxx. Qed.
Canonical qeonb_qnsType i := QNSType (@onb_wf i) (@donb_ns i).

Lemma ketns_innerM (v : 'NS[H]_S) : '|v>^A \o '|v> = 1%:D.
Proof. by rewrite ket_adj innerM ns_dot. Qed.
Canonical ketns_qnsType (v : 'NS[H]_S) := QNSket (dket v) (@ketns_innerM v).

End QEONBTheory.

Section DiracVOrder.
Context {L : finType} (H : L -> chsType).
Implicit Type (f g h: 'D[H]) (S T W : {set L}).
(* all non-diag are 0, all diag psd *)

Definition psdqe :=
  [qualify A : 'D[H] | 
    [forall S, (A S S \is psdlf) && 
      [forall T, (S == T) || (A S T == 0)]]].
Fact psdqe_key : pred_key psdqe. Proof. by []. Qed.
Canonical psdqe_keyed := KeyedQualifier psdqe_key.

Lemma psddP f : reflect ((forall S, (f S S \is psdlf)) /\ 
  (forall S T : {set L}, S != T -> (f S T == 0))) (f \is psdqe).
Proof.
apply/(iffP idP); rewrite qualifE.
move=>/forallP P; split=>[S|S T/negPf P3]; move: (P S)=>/andP[P1//].
by move=>/forallP/(_ T); rewrite P3.
move=>[P1 P2]; apply/forallP=>S; apply/andP; split=>//.
by apply/forallP=>T; case: eqP=>//= /eqP; apply P2.
Qed.

Definition led_def f g := (g - f) \is psdqe.
Definition ltd_def f g := (g != f) && (led_def f g).

Lemma ltd_def_def : forall f g, ltd_def f g = (g != f) && (led_def f g).
Proof. by rewrite /led_def. Qed.

Lemma led_def_anti : antisymmetric led_def.
Proof.
move=>f g=>/andP[/psddP [P1 P2]/psddP [P3 P4]].
apply/diracP=>S T. case E: (S == T).
move: E=>/eqP->; apply/le_anti; move: (P1 T) (P3 T).
by rewrite !diracE !psdlfE !subv_ge0=>->->.
by move: E=>/eqP/eqP/P4; rewrite !diracE subr_eq0=>/eqP.
Qed.

Lemma led_def_refl : reflexive led_def.
Proof.
move=>x; apply/psddP; split=>[S|S T _].
all: by rewrite !diracE subrr// psdlf0.
Qed.

Lemma led_def_trans : transitive led_def.
Proof.
move=>f g h=>/psddP[P1 P2]/psddP[P3 P4].
apply/psddP; split=>[S|S T P5].
move: (P1 S) (P3 S); rewrite !diracE !psdlfE !subv_ge0; exact: le_trans.
by move: (P2 _ _ P5) (P4 _ _ P5); rewrite !diracE !subr_eq0=>/eqP->/eqP->.
Qed.

Definition lownerqe_porderMixin := LePOrderMixin 
ltd_def_def led_def_refl led_def_anti led_def_trans.

Canonical lownerqe_porderType := POrderType vorder_display 'D[H] lownerqe_porderMixin.

Lemma ged0P f : reflect ((forall S, ((0 : 'End(_)) ⊑ f S S)) /\ 
  (forall S T : {set L}, S != T -> (f S T == 0))) ((0 : 'D) ⊑ f).
Proof. 
apply/(iffP (psddP _)); rewrite subr0=>[[P1 P2]];
by split=>[|//] S; rewrite ?psdlfE// -psdlfE P1.
Qed.

Lemma led_add2rP h f g : f ⊑ g -> (f + h) ⊑ (g + h).
Proof. by rewrite addrC /Order.le/= /led_def opprD addrA addrK. Qed.

Lemma led_pscale2lP (e : C) f g : 0 < e -> f ⊑ g -> (e *: f) ⊑ (e *: g).
Proof.
move=>egt0/psddP[P1 P2]; apply/psddP; split=>[S|S T /P2].
by move: (P1 S); rewrite !psdlfE=>P3; rewrite -scalerBr diracE pscalev_rge0.
by rewrite -scalerBr [in X in _ -> X]diracE=>/eqP->; rewrite scaler0.
Qed.

Import VOrder.Exports.
Definition lownerqe_vorderMixin := VOrderMixin led_add2rP led_pscale2lP.
Canonical lownerqe_vorderType := VOrderType C 'D[H] lownerqe_vorderMixin.

Lemma ltd_ltf f : (0 : 'D) ⊏ f -> 
  exists (S : {set L}), (0 : 'End('H_S)) ⊏ f S S.
Proof.
rewrite lt_def=>/andP[/eqP+/ged0P[P1 P2]].
rewrite not_existsP; apply contra_not=>P3.
apply/diracP=>S T; rewrite diracE.
case E: (S == T); last by apply/eqP/P2; rewrite E.
move: E=>/eqP->; move: (P3 T) (P1 T)=>/negP/negPf.
by rewrite le_eqVlt eq_sym orbC=>->/=/eqP.
Qed.

Lemma pscaled_lge0 f (a : C) : 
  (0 : 'D) ⊏ f -> (0 : 'D) ⊑ a *: f = (0 <= a).
Proof.
move=>P. move: {+}P=>/ltd_ltf[S Ps].
apply/Bool.eq_iff_eq_true; split.
by move=>/ged0P[/(_ S)+ _]; rewrite diracE pscalev_lge0.
by rewrite le0r=>/orP[/eqP->|P1]; 
  rewrite ?scale0r ?lexx// pscalev_rge0//; apply/ltW.
Qed.

Import CanVOrder.Exports.
Definition lownerqe_canVOrderMixin := CanVOrderMixin pscaled_lge0.
Canonical lownerqe_canVOrderType := CanVOrderType C 'D[H] lownerqe_canVOrderMixin.

End DiracVOrder.

Section DiracVOrderTheory.
Context {L : finType} (H : L -> chsType).
Implicit Type (S T : {set L}).
Local Notation "'0" := (0 : 'D[H]).
Local Notation "a '%:E'" := (a : 'D) (at level 2, left associativity, format "a %:E").

Lemma lin_eq0 S T (f : 'F[H]_(S,T)) : ('[ f ] == 0) = (f == 0).
Proof. by rewrite -(inj_eq (@dlin_inj _ _ _ _)) linear0. Qed.

Lemma wf_ge0_eq0 S T (e : 'D[H]_(S,T)) : 
  S != T -> '0 ⊑ e -> e%:E = 0.
Proof.
by move=>P /ged0P[_/(_ S T P)]/eqP; rewrite {2}wfd_linE=>->; rewrite linear0.
Qed.

Lemma wf_gt0_eq0 S T (e : 'D[H]_(S,T)) : 
  S != T -> '0 ⊏ e -> e%:E = 0.
Proof. move=>+/ltW; exact: wf_ge0_eq0. Qed.

Lemma sqr_gef0 S (e : 'D[H]_S) : '0 ⊑ e = (0%:VF ⊑ e S S).
Proof.
apply/Bool.eq_iff_eq_true; split; first by move=>/ged0P[/(_ S)].
move=>P; apply/ged0P; split=>[T|T W PT]; rewrite sqrd_linE.
case E: (S == T); move: E=>/eqP.
by move=>Q; case: T / Q; rewrite dlin_id.
move=>/eqP; rewrite eq_sym=>P1; rewrite dlin_eq0l//.
rewrite dlin_eq0p//=; move: PT; apply contraNN=>/eqP P1.
by inversion P1.
Qed.

Lemma lin_lef S (f g : 'F[H]_S) : '[ f ] ⊑ '[ g ] = (f ⊑ g).
Proof. by rewrite -subv_ge0 -linearB/= sqr_gef0/= dlin_id subv_ge0. Qed.

Lemma lin_ltf S (f g : 'F[H]_S) : '[ f ] ⊏ '[ g ] = (f ⊏ g).
Proof. by rewrite !lt_def -subr_eq0 -linearB/= lin_eq0 subr_eq0 lin_lef. Qed.

Lemma lin_gef0 S (f : 'F[H]_S) : '0 ⊑ '[ f ] = (0%:VF ⊑ f).
Proof. by rewrite -lin_lef linear0. Qed.

Lemma lin_gtf0 S (f : 'F[H]_S) : '0 ⊏ '[ f ] = (0%:VF ⊏ f).
Proof. by rewrite -lin_ltf linear0. Qed.

Lemma sqr_lef S (e1 e2 : 'D[H]_S) : (e1%:E ⊑ e2) = (e1 S S ⊑ e2 S S).
Proof. by rewrite {1}sqrd_linE {1}(sqrd_linE e2) lin_lef. Qed.

Lemma sqr_ltf S (e1 e2 : 'D[H]_S) : (e1%:E ⊏ e2) = (e1 S S ⊏ e2 S S).
Proof. by rewrite {1}sqrd_linE {1}(sqrd_linE e2) lin_ltf. Qed.

Lemma tend_id S1 T1 S2 T2 (f : 'D[H]_(S1,T1)) (g : 'D_(S2,T2)) : 
  (f \⊗ g) (S1 :|: S2) (T1 :|: T2) = (f S1 T1 \⊗ g S2 T2)%VF.
Proof. by rewrite {1}wfd_linE  {1}(wfd_linE g) tend_correct dlin_id. Qed.

Lemma tend_sqr_id S T (f : 'D[H]_S) (g : 'D_T) : 
  (f \⊗ g) (S :|: T) (S :|: T) = (f S S \⊗ g T T)%VF.
Proof. by rewrite tend_id. Qed.

Lemma sqr_eqf S (e1 e2 : 'D[H]_S) : (e1%:E == e2) = (e1 S S == e2 S S).
Proof. by rewrite {1}sqrd_linE {1}(sqrd_linE e2) (inj_eq (@dlin_inj _ _ _ _)). Qed.

Lemma sqr_eqf0 S (e : 'D[H]_S) : (e%:E == 0) = (e S S == 0).
Proof. by rewrite sqr_eqf/= diracE. Qed.

Ltac simp_sqr := rewrite ?(sqr_lef,sqr_ltf,sqr_eqf0,sqr_eqf)/= 
  ?(tend_sqr_id,dlin_id, diracE).

Lemma sqr_gtf0 S (e : 'D[H]_S) : '0 ⊏ e = (0%:VF ⊏ e S S).
Proof. by simp_sqr. Qed.

Lemma sqr_lef0 S (e : 'D[H]_S) : e%:E ⊑ 0 = (e S S ⊑ 0).
Proof. by simp_sqr. Qed.

Lemma sqr_ltf0 S (e : 'D[H]_S) : e%:E ⊏ 0 = (e S S ⊏ 0).
Proof. by simp_sqr. Qed.

Definition sqr_cpf0 := (sqr_gef0, sqr_gtf0, sqr_lef0, sqr_ltf0).

Lemma wf_ge0_ge0 S T (e : 'D[H]_(S,T)) : 
  S = T -> '0 ⊑ e = (0%:VF ⊑ e S S).
Proof.
move=>P; case: T / P e=>e. move: (wfdP e)=>P.
by rewrite (sqrdE P) sqr_gef0.
Qed.

Lemma wf_gt0_gt0 S T (e : 'D[H]_(S,T)) : 
  S = T -> '0 ⊏ e = (0%:VF ⊏ e S S).
Proof.
move=>P; case: T / P e=>e. move: (wfdP e)=>P.
by rewrite (sqrdE P) sqr_gtf0.
Qed.

Lemma led0I S : (0 : 'D[H]) ⊑ \1_S.
Proof. by rewrite sqr_gef0/= dlin_id lef01. Qed.

Lemma ltd0I S : (0 : 'D[H]) ⊏ \1_S.
Proof. by rewrite sqr_gtf0/= dlin_id ltf01. Qed.

Lemma led01 : (0 : 'D[H]) ⊑ :1.
Proof. by rewrite dnumI led0I. Qed.

Lemma ltd01 : (0 : 'D[H]) ⊏ :1.
Proof. by rewrite dnumI ltd0I. Qed.

Lemma sqr_lef1 S (e : 'D[H]_S) : e%:E ⊑ \1_S = (e S S ⊑ \1).
Proof. by simp_sqr. Qed.

Lemma sqr_ltf1 S (e : 'D[H]_S) : e%:E ⊏ \1_S = (e S S ⊏ \1).
Proof. by simp_sqr. Qed.

Lemma sqr_gef1 S (e : 'D[H]_S) : \1_S ⊑ e%:E  = (\1 ⊑ e S S).
Proof. by simp_sqr. Qed.

Lemma sqr_gtf1 S (e : 'D[H]_S) : \1_S ⊏ e%:E  = (\1 ⊏ e S S).
Proof. by simp_sqr. Qed.

Definition sqr_cpf1 := (sqr_lef1, sqr_ltf1, sqr_gef1, sqr_gtf1).

Lemma lin_lef1 S (f : 'F[H]_S) : '[ f ] ⊑ \1_S = (f ⊑ \1).
Proof. by rewrite sqr_lef1/= dlin_id. Qed.

Lemma lin_ltf1 S (f : 'F[H]_S) : '[ f ] ⊏ \1_S = (f ⊏ \1).
Proof. by rewrite sqr_ltf1/= dlin_id. Qed.

Section tend_order.
Variable (S T : {set L}) (dis : [disjoint S & T]).
Implicit Type (x : 'D[H]_S) (y : 'D[H]_T).

Lemma tend_eq0 x y : x \⊗ y == 0 = (x%:E == 0) || (y%:E == 0).
Proof. by simp_sqr; apply: bregv_eq0. Qed.

Lemma ptend_rge0 x y : '0 ⊏ x -> ('0 ⊑ x \⊗ y) = ('0 ⊑ y).
Proof. by simp_sqr; apply: pbregv_rge0. Qed.

Lemma ptend_lge0 y x : '0 ⊏ y -> ('0 ⊑ x \⊗ y) = ('0 ⊑ x).
Proof. by simp_sqr; apply: pbregv_lge0. Qed.

(* bad !! *)
(* Definition tend_bregVOrderMixin S T dis := 
    bregVOrderMixin (@tend_eq0 S T dis) (ptend_rge0 dis) (ptend_lge0 dis).
Canonical tend_bregVOrderType S T dis := 
  bregVOrderType (@ten_lfun _ _ S S T T) (@tenf_bregVOrderMixin S T dis). *)

Lemma ptend_rgt0 x y : '0 ⊏ x -> ('0 ⊏ x \⊗ y) = ('0 ⊏ y).
Proof. by simp_sqr; apply: pbregv_rgt0. Qed.

Lemma ptend_lgt0 y x : '0 ⊏ y -> ('0 ⊏ x \⊗ y) = ('0 ⊏ x).
Proof. by simp_sqr; apply: pbregv_lgt0. Qed.

Lemma tendI_eq0 x y : x%:E != 0 -> (x \⊗ y == 0) = (y%:E == 0).
Proof. by simp_sqr; apply: bregvI_eq0. Qed.

Lemma tendI x y1 y2 : x%:E != 0 -> x \⊗ y1 = x \⊗ y2 -> y1%:E = y2.
Proof.
by rewrite -!eq_iff; simp_sqr; rewrite !eq_iff=>IH1; apply: (bregvI IH1).
Qed.

Lemma tenId_eq0 y x : y%:E != 0 -> (x \⊗ y == 0) = (x%:E == 0).
Proof. by simp_sqr; apply: bregIv_eq0. Qed.

Lemma tenId y x1 x2 : y%:E != 0 -> x1 \⊗ y = x2 \⊗ y -> x1%:E = x2.
Proof.
by rewrite -!eq_iff; simp_sqr; rewrite !eq_iff=>IH1; apply: (bregIv IH1).
Qed.

Lemma le_ptend2lP x y1 y2 : '0 ⊏ x -> y1%:E ⊑ y2 -> x \⊗ y1 ⊑ x \⊗ y2.
Proof. by simp_sqr; apply: lev_pbreg2lP. Qed.

(* mulr and lev/ltv *)
Lemma le_ptend2l x y1 y2 : '0 ⊏ x -> (x \⊗ y1 ⊑ x \⊗ y2) = (y1%:E ⊑ y2).
Proof. by simp_sqr=>IH; apply: lev_pbreg2l. Qed.

Lemma lt_ptend2l x y1 y2 : '0 ⊏ x -> (x \⊗ y1 ⊏ x \⊗ y2) = (y1%:E ⊏ y2).
Proof. by simp_sqr=>IH; apply: ltv_pbreg2l. Qed.
Definition lte_ptend2l := (le_ptend2l, lt_ptend2l).

Lemma le_ptend2r y x1 x2 : '0 ⊏ y -> (x1 \⊗ y ⊑ x2 \⊗ y) = (x1%:E ⊑ x2).
Proof. by simp_sqr=>IH; apply: lev_pbreg2r. Qed.

Lemma lt_ptend2r y x1 x2 : '0 ⊏ y -> (x1 \⊗ y ⊏ x2 \⊗ y) = (x1%:E ⊏ x2).
Proof. by simp_sqr=>IH; apply: ltv_pbreg2r. Qed.
Definition lte_ptend2r := (le_ptend2r, lt_ptend2r).

Lemma le_ntend2l x y1 y2 : x%:E ⊏ 0 -> (x \⊗ y1 ⊑ x \⊗ y2) = (y2%:E ⊑ y1).
Proof. by simp_sqr=>IH; apply: lev_nbreg2l. Qed.

Lemma lt_ntend2l x y1 y2 : x%:E ⊏ 0 -> (x \⊗ y1 ⊏ x \⊗ y2) = (y2%:E ⊏ y1).
Proof. by simp_sqr=>IH; apply: ltv_nbreg2l. Qed.
Definition lte_ntend2l := (le_ntend2l, lt_ntend2l).

Lemma le_ntend2r y x1 x2 : y%:E ⊏ 0 -> (x1 \⊗ y ⊑ x2 \⊗ y) = (x2%:E ⊑ x1).
Proof. by simp_sqr=>IH; apply: lev_nbreg2r. Qed.

Lemma lt_ntend2r y x1 x2 : y%:E ⊏ 0 -> (x1 \⊗ y ⊏ x2 \⊗ y) = (x2%:E ⊏ x1).
Proof. by simp_sqr=>IH; apply: ltv_nbreg2r. Qed.
Definition lte_ntend2r := (le_ntend2r, lt_ntend2r).

Lemma le_wptend2l x y1 y2 : '0 ⊑ x -> y1%:E ⊑ y2 -> x \⊗ y1 ⊑ x \⊗ y2.
Proof. by simp_sqr=>IH1 IH2; apply: lev_wpbreg2l. Qed.

Lemma le_wntend2l x y1 y2 : x%:E ⊑ 0 -> y1%:E ⊑ y2 -> x \⊗ y2 ⊑ x \⊗ y1.
Proof. by simp_sqr=>IH1 IH2; apply: lev_wnbreg2l. Qed.

Lemma le_wptend2r y x1 x2 : '0 ⊑ y -> x1%:E ⊑ x2 -> x1 \⊗ y ⊑ x2 \⊗ y.
Proof. by simp_sqr=>IH1 IH2; apply: lev_wpbreg2r. Qed.

Lemma le_wntend2r y x1 x2 : y%:E ⊑ 0 -> x1%:E ⊑ x2 -> x2 \⊗ y ⊑ x1 \⊗ y.
Proof. by simp_sqr=>IH1 IH2; apply: lev_wnbreg2r. Qed.

(* Binary forms, for backchaining. *)
Lemma le_ptend2 x1 x2 y1 y2 :
  '0 ⊑ x1 -> '0 ⊑ y1 -> x1%:E ⊑ x2 -> y1%:E ⊑ y2 -> x1 \⊗ y1 ⊑ x2 \⊗ y2.
Proof. by simp_sqr; apply: lev_pbreg2. Qed.

Lemma lt_ptend2 x1 x2 y1 y2 :
  '0 ⊑ x1 -> '0 ⊑ y1 -> x1%:E ⊏ x2 -> y1%:E ⊏ y2 -> x1 \⊗ y1 ⊏ x2 \⊗ y2.
Proof. by simp_sqr; apply: ltv_pbreg2. Qed.

Lemma ptend_rlt0 x y : '0 ⊏ x -> (x \⊗ y ⊏ 0) = (y%:E ⊏ 0).
Proof. by simp_sqr; apply: pbregv_rlt0. Qed.

Lemma ptend_rle0 x y : '0 ⊏ x -> (x \⊗ y ⊑ 0) = (y%:E ⊑ 0).
Proof. by simp_sqr; apply: pbregv_rle0. Qed.

Lemma ntend_rgt0 x y : x%:E ⊏ 0 -> ('0 ⊏ x \⊗ y) = (y%:E ⊏ 0).
Proof. by simp_sqr; apply: nbregv_rgt0. Qed.

Lemma ntend_rge0 x y : x%:E ⊏ 0 -> ('0 ⊑ x \⊗ y) = (y%:E ⊑ 0).
Proof. by simp_sqr; apply: nbregv_rge0. Qed.

Lemma ntend_rlt0 x y : x%:E ⊏ 0 -> (x \⊗ y ⊏ 0) = ('0 ⊏ y).
Proof. by simp_sqr; apply: nbregv_rlt0. Qed.

Lemma ntend_rle0 x y : x%:E ⊏ 0 -> (x \⊗ y ⊑ 0) = ('0 ⊑ y).
Proof. by simp_sqr; apply: nbregv_rle0. Qed.

Lemma ptend_llt0 y x : '0 ⊏ y -> (x \⊗ y ⊏ 0) = (x%:E ⊏ 0).
Proof. by simp_sqr; apply: pbregv_llt0. Qed.

Lemma ptend_lle0 y x : '0 ⊏ y -> (x \⊗ y ⊑ 0) = (x%:E ⊑ 0).
Proof. by simp_sqr; apply: pbregv_lle0. Qed.

Lemma ntend_lgt0 y x : y%:E ⊏ 0 -> ('0 ⊏ x \⊗ y) = (x%:E ⊏ 0).
Proof. by simp_sqr; apply: nbregv_lgt0. Qed.

Lemma ntend_lge0 y x : y%:E ⊏ 0 -> ('0 ⊑ x \⊗ y) = (x%:E ⊑ 0).
Proof. by simp_sqr; apply: nbregv_lge0. Qed.

Lemma ntend_llt0 y x : y%:E ⊏ 0 -> (x \⊗ y ⊏ 0) = ('0 ⊏ x).
Proof. by simp_sqr; apply: nbregv_llt0. Qed.

Lemma ntend_lle0 y x : y%:E ⊏ 0 -> (x \⊗ y ⊑ 0) = ('0 ⊑ x).
Proof. by simp_sqr; apply: nbregv_lle0. Qed.

(* weak and symmetric lemmas *)
Lemma tend_ge0 x y : '0 ⊑ x -> '0 ⊑ y -> '0 ⊑ x \⊗ y.
Proof. by simp_sqr; apply: bregv_ge0. Qed.

Lemma tend_le0 x y : x%:E ⊑ 0 -> y%:E ⊑ 0 -> '0 ⊑ x \⊗ y.
Proof. by simp_sqr; apply: bregv_le0. Qed.

Lemma tend_ge0_le0 x y : '0 ⊑ x -> y%:E ⊑ 0 -> x \⊗ y ⊑ 0.
Proof. by simp_sqr; apply: bregv_ge0_le0. Qed.

Lemma tend_le0_ge0 x y : x%:E ⊑ 0 -> '0 ⊑ y -> x \⊗ y ⊑ 0.
Proof. by simp_sqr; apply: bregv_le0_ge0. Qed.

(* bregv_gt0 with only one case *)

Lemma tend_gt0 x y : '0 ⊏ x -> '0 ⊏ y -> '0 ⊏ x \⊗ y.
Proof. by simp_sqr; apply: bregv_gt0. Qed.

Lemma tend_lt0 x y : x%:E ⊏ 0 -> y%:E ⊏ 0 -> '0 ⊏ x \⊗ y.
Proof. by simp_sqr; apply: bregv_lt0. Qed.

Lemma tend_gt0_lt0 x y : '0 ⊏ x -> y%:E ⊏ 0 -> x \⊗ y ⊏ 0.
Proof. by simp_sqr; apply: bregv_gt0_lt0. Qed.

Lemma tend_lt0_gt0 x y : x%:E ⊏ 0 -> '0 ⊏ y -> x \⊗ y ⊏ 0.
Proof. by simp_sqr; apply: bregv_lt0_gt0. Qed.

Lemma tend_le1 x y : '0 ⊑ x -> '0 ⊑ y 
  -> x%:E ⊑ \1_S -> y%:E ⊑ \1_T -> x \⊗ y ⊑ \1_(S :|: T).
Proof. by move=>P1 P2 P3 P4; rewrite -tendII; apply: le_ptend2=>/=. Qed.

Lemma tend_lt1 x y : '0 ⊑ x -> '0 ⊑ y -> x%:E ⊏ \1_S -> y%:E ⊏ \1_T -> x \⊗ y ⊏ \1_(S :|: T).
Proof. by move=>P1 P2 P3 P4; rewrite -tendII; apply: lt_ptend2=>/=. Qed.
Definition tend_lte1 := (tend_le1, tend_lt1).

Lemma tend_ge1 x y : \1_S ⊑ x -> \1_T ⊑ y -> \1_(S :|: T) ⊑ x \⊗ y.
Proof. by rewrite -tendII=>P1 P2; apply: le_ptend2=>/=[||//|//]; apply: led0I. Qed.

Lemma tend_gt1 x y : \1_S ⊏ x -> \1_T ⊏ y -> \1_(S :|: T) ⊏ x \⊗ y.
Proof. by rewrite -tendII=>P1 P2; apply: lt_ptend2=>/=[||//|//]; apply: led0I. Qed.
Definition tend_gte1 := (tend_ge1, tend_gt1).
Definition tend_cp1 := (tend_lte1, tend_gte1).

End tend_order.

Lemma tend_ge0_le1 S T (P : 'D[H]_S) (Q : 'D_T) :
  [disjoint S & T] ->
  '0 ⊑ P%:E ⊑ \1_S -> '0 ⊑ Q%:E ⊑ \1_T ->
  '0 ⊑ P \⊗ Q  ⊑ \1_(S :|: T).
Proof.
move=>dis/andP[]P1 P2/andP[]P3 P4; apply/andP; split.
by apply: tend_ge0. by rewrite -tendII; apply: le_ptend2=>/=.
Qed.

Lemma tens_ge0_seq (I : eqType) (r : seq I) (R : pred I) (S : I -> {set L})
  (P : forall i, 'D_(S i)) :
  (forall i j, R i -> R j -> i != j -> [disjoint (S i) & (S j)]) -> uniq r ->
  (forall i, R i -> (0 : 'D[H]) ⊑ P i) ->
  '0 ⊑ \ten_(i <- r | R i) P i.
Proof.
move=>IH1+IH2; elim: r=>[|a r IH]; first by rewrite big_nil bigd led01.
rewrite cons_uniq=>/andP[na ur]. rewrite big_cons; case E: (R a).
rewrite bigdE sqrd_linE [X in _\⊗X]sqrd_linE/= tend_correct lin_gef0.
apply: bregv_ge0. apply/bigcup_disjoint_seqP=>i/andP[Pi Ri]. 
apply: IH1=>//. by apply: (notin_in_neq na).
1,2: by rewrite -lin_gef0 -sqrd_linE ?IH2//= IH. by apply IH.
Qed.

Lemma tens_ge0 (I : finType) (R : pred I) (S : I -> {set L})
  (P : forall i, 'D_(S i)) :
  (forall i j, R i -> R j -> i != j -> [disjoint (S i) & (S j)]) ->
  (forall i, R i -> (0 : 'D[H]) ⊑ P i) ->
  '0 ⊑ \ten_(i | R i) P i.
Proof. by move=>IH; apply: tens_ge0_seq=>//; apply: index_enum_uniq. Qed.

Lemma tens_ge0_le1_seq (I : eqType) (r : seq I) (R : pred I) (S : I -> {set L})
  (P : forall i, 'D_(S i)) :
  (forall i j, R i -> R j -> i != j -> [disjoint (S i) & (S j)]) -> uniq r ->
  (forall i, R i -> (0 : 'D[H]) ⊑ (P i : 'D) ⊑ \1_(S i)) ->
  '0 ⊑ \ten_(i <- r | R i) P i ⊑ \1_(\bigcup_(i <- r | R i) S i).
Proof.
move=>IH1+IH2; elim: r=>[|a r IH]; first by rewrite !big_nil bigd led01 dnumI/=.
rewrite cons_uniq=>/andP[na ur]. rewrite !big_cons; case E: (R a).
rewrite bigdE. apply: tend_ge0_le1.
apply/bigcup_disjoint_seqP=>i/andP[Pi Ri]. apply: IH1=>//. by apply: (notin_in_neq na).
by apply IH2. all: by apply : IH.
Qed.

Lemma tens_ge0_le1 (I : finType) (r : seq I) (R : pred I) (S : I -> {set L})
  (P : forall i, 'D_(S i)) :
  (forall i j, R i -> R j -> i != j -> [disjoint (S i) & (S j)]) ->
  (forall i, R i -> (0 : 'D[H]) ⊑ (P i : 'D) ⊑ \1_(S i)) ->
  '0 ⊑ \ten_(i | R i) P i ⊑ \1_(\bigcup_(i | R i) S i).
Proof. move=>IH; apply: tens_ge0_le1_seq=>//; apply: index_enum_uniq. Qed.


End DiracVOrderTheory.
