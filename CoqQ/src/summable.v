From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp.classical Require Import boolp cardinality mathcomp_extra
  classical_sets functions.
From mathcomp.analysis Require Import ereal reals signed topology 
  prodnormedzmodule normedtype sequences.
From mathcomp.real_closed Require Import complex.
Require Import mcextra mcaextra xfinmap extnum mxpred.
(* From mathcomp Require Import fintype bigop finmap. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** For Pierre-Yves : definition of sums *)
(* From mathcomp Require fintype bigop finmap. *)
Import Order Order.Theory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Import VNorm.Exports.

Reserved Notation "\dlet_ ( i <- d ) E"
  (at level 36, E at level 36, i, d at level 50,
     format "'[' \dlet_ ( i  <-  d ) '/  '  E ']'").

Reserved Notation "\dlim_ ( n ) E"
  (at level 36, E at level 36, n at level 50,
     format "'[' \dlim_ ( n ) '/  '  E ']'").

Reserved Notation "\P_[ mu ] E" (at level 2, format "\P_[ mu ]  E").
Reserved Notation "\P_[ mu , A ] E" (at level 2, format "\P_[ mu ,  A ]  E").
Reserved Notation "\E?_[ mu ] f" (at level 2, format "\E?_[ mu ]  f").
Reserved Notation "\E_[ mu ] f" (at level 2, format "\E_[ mu ]  f").
Reserved Notation "\E_[ mu , A ] f" (at level 2, format "\E_[ mu ,  A ]  f").

Local Notation "\`| f |" := (fun x => `|f x|) (at level 2).

Lemma max_le_l {disp : unit} {T : porderType disp} (x y : T) :
  (x <= Order.max x y)%O.
Proof. by rewrite maxEle; case E: (x <= y)%O. Qed.
Lemma min_le_r {disp : unit} {T : porderType disp} (x y : T) :
  (Order.min x y <= y)%O.
Proof. by rewrite minEle; case E: (x <= y)%O. Qed.

Section totally.

Local Open Scope fset_scope.
(* :TODO: when eventually is generalized to any lattice *)
(* totally can just be replaced by eventually *)
Definition totally {I : choiceType} : set (set {fset I}) :=
  filter_from setT (fun A => [set B | A `<=` B]).

Canonical totally_filter_source {I : choiceType} X :=
  @Filtered.Source X _ {fset I} (fun f => f @ totally).

Global Instance totally_filter {I : choiceType} : ProperFilter (@totally I).
Proof.
eapply filter_from_proper; last by move=> A _; exists A; rewrite /= fsubset_refl.
apply: filter_fromT_filter; first by exists fset0.
by move=> A B /=; exists (A `|` B) => P /=; rewrite fsubUset => /andP[].
Qed.

Definition psum {I : choiceType} {R : zmodType}
  (x : I -> R) (A : {fset I}) : R := \sum_(i : A) x (val i).

Lemma psumE {I : choiceType} {R : zmodType} (x : I -> R) (A : {fset I}) :
  \sum_(i : A) x (fsval i) = psum x A.
Proof. by []. Qed.

Definition psumr {I : choiceType} (A : {fset I}) 
  {R : zmodType} (x : I -> R) : R := psum x A.

Definition sum (I : choiceType) {K : numFieldType} {R : normedModType K}
   (x : I -> R) : R := lim (psum x).

Definition psum_preset {I : choiceType} {R : zmodType}
  (x : I -> R) := [set y | exists J : {fset I}, y = psum x J ].

(* Definition summable (I : choiceType) {K : numFieldType} {R : normedModType K}
   (x : I -> R) := exists (M : K), \forall J \near totally,
   (psum (fun i => `|x i|) J <= M)%R. *)

(* Definition summable (I : choiceType) {K : realType} {R : normedModType K}
   (x : I -> R) :=
   \forall M \near +oo%R, \forall J \near totally,
   (psum (fun i => `|x i|) J <= M)%R. *)

End totally.

Section PartialSum.
Context {I : choiceType}.
Implicit Type (R : zmodType).

Lemma psum0 {R} (x : I -> R) : psum x fset0 = 0.
Proof. by rewrite/psum big_fset0. Qed.

Lemma psum1 {R} (i : I) (x : I -> R) : psum x [fset i]%fset = x i.
Proof. by rewrite/psum big_fset1. Qed.

Lemma psumrE {R} (x : I -> R) (A : {fset I}) :
  psum x A = psumr A x.
Proof. by []. Qed.

Lemma psumr_is_additive (A : {fset I}) R : 
  additive (@psumr _ A R).
Proof.
move=>x y; rewrite raddf_sum -big_split.
by apply eq_bigr=>i _; rewrite/= !fctE.
Qed.
Canonical psumr_additive (A : {fset I}) R := 
  Additive (@psumr_is_additive A R).

Lemma psumr_is_linear (A : {fset I}) (T : ringType) (V : lmodType T) :
  linear (@psumr _ A V).
Proof.
move=>a x y; rewrite raddf_sum -big_split.
by apply eq_bigr=>i _; rewrite/= !fctE {1}/GRing.scale/=.
Qed.
Canonical psumr_linear (A : {fset I}) T V := 
  Linear (@psumr_is_linear A T V).

Lemma psumD {R} (x y : I -> R) (A : {fset I}) :
  psum (x + y) A = psum x A + psum y A.
Proof. by rewrite !psumrE raddfD. Qed.

Lemma psumN {R} (x : I -> R) (A : {fset I}) :
  psum (- x) A = - psum x A.
Proof. by rewrite !psumrE raddfN. Qed.

Lemma psumB {R} (x y : I -> R) (A : {fset I}) :
  psum (x - y) A = psum x A - psum y A.
Proof. by rewrite !psumrE raddfB. Qed.

Lemma psumZ (T : ringType) (V : lmodType T) (x : I -> V) 
  (A : {fset I}) (a : T) :
  psum (a *: x) A = a *: psum x A.
Proof. by rewrite !psumrE linearZ. Qed.

Lemma psumU {R} (x : I -> R) (A B : {fset I}) :
  [disjoint A & B]%fset -> 
    psum x (A `|` B)%fset = psum x A + psum x B.
Proof. exact: big_fsetU. Qed.

Lemma psumDB {R} (x : I -> R) (A B : {fset I}) :
  psum x (A `\` B)%fset = psum x A - psum x (A `&` B)%fset.
Proof. by rewrite -{2}[A](fsetID B) psumU ?fdisjointID// addrC addKr. Qed.

Lemma psumIB {R} (x : I -> R) (A B : {fset I}) :
  psum x (A `\` B)%fset - psum x (B `\` A)%fset = psum x A - psum x B.
Proof. by rewrite !psumDB opprB fsetIC addrA addrNK. Qed.

Lemma psum_ler_norm (T : numDomainType) (V : normedZmodType T) (x : I -> V) 
  (A : {fset I}) :
  `|psum x A| <= psum \`| x | A.
Proof. exact: ler_norm_sum. Qed.

Lemma psum_ler (T : numDomainType) (x : I -> T) (A B : {fset I}) :
  (forall i, i \in (B `\` A)%fset -> 0 <= x i) -> (A `<=` B)%fset -> psum x A <= psum x B.
Proof.
move=>P P1. rewrite -(fsetUD_sub P1) psumU ?fdisjointXD// lerDl sumr_ge0// =>i _.
by case: i.
Qed. 

Lemma psum_seq_fsetE R (x : I -> R) (A : {fset I}) :
  psum x A = \sum_(i <- A) x i.
Proof. by rewrite/psum big_seq_fsetE. Qed.

Lemma eq_psum R (x y : I -> R) (A B : {fset I}) :
  A =i B -> x =1 y -> psum x A = psum y B.
Proof. by move=>/fsetP-> P2; apply eq_bigr. Qed.

Lemma eq_psuml R (x : I -> R) (A B : {fset I}) :
  A =i B -> psum x A = psum x B.
Proof. by move=>/fsetP->. Qed.

Lemma eq_psumr R (x y : I -> R) (A : {fset I}) :
  x =1 y -> psum x A = psum y A.
Proof. by apply: eq_psum. Qed.

End PartialSum.

(* move *)
Lemma big_fset_seqE (T : Type) (idx : T) (op : Monoid.law idx) (I : choiceType)
  (X : {fset I}) (F : I -> T) :
  \big[op/idx]_(i : X) F (val i) = \big[op/idx]_(x <- X) F x.
Proof. by rewrite big_seq_fsetE. Qed.
Arguments big_fset_seqE [T idx op I] X F.

Module Bounded.

Section ClassDef.

Variables (I : choiceType) (K : numFieldType) (V : normedZmodType K).

Definition axiom (f : I -> V) := exists (M : K), forall i, `| f i | <= M.

Structure map (phUV : phant (I -> V)) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (I -> V)) (f g : I -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

Canonical eqType := EqType (map phUV) gen_eqMixin.
Canonical choiceType := ChoiceType (map phUV) gen_choiceMixin.

End ClassDef.

Module Exports.
Notation bounded f := (axiom f).
Coercion apply : map >-> Funclass.
Notation Bounded fA := (Pack (Phant _) fA).
Notation "{ 'bounded' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'bounded'  fUV }") : type_scope.
Notation "[ 'bounded' 'of' f 'as' g ]" := (@clone _ _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'bounded'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'bounded' 'of' f ]" := (@clone _ _ _ _ f f _ _ id id)
  (at level 0, format "[ 'bounded'  'of'  f ]") : form_scope.
Canonical eqType.
Canonical choiceType.

End Exports.

End Bounded.
Import Bounded.Exports.

Module Summable.

Section ClassDef.

Variables (I : choiceType) (K : numFieldType) (V : normedZmodType K).

Definition axiom (f : I -> V) := exists (M : K), \forall J \near totally,
  (psum \`| f | J <= M)%R.

Notation mixin_of := axiom.

Record class_of f : Prop := Class {base : bounded f; mixin : mixin_of f}.
Local Coercion base : class_of >-> bounded.
Local Coercion mixin : class_of >-> axiom.

Lemma class_of_axiom f : @axiom f -> class_of f.
Proof.
split=>//; move: H=>[M PM]. exists M=>i.
suff: \forall J \near (@totally I), `|f i| <= M by apply: have_near.
near=>J; apply: (@le_trans _ _ (psum \`| f | J)); near: J; last by apply: PM.
exists [fset i]%fset=>// J/=.
have ->: `|f i| = psum \`|f| [fset i]%fset by rewrite psum1.
by apply: psum_ler.
Unshelve. end_near.
Qed.

Structure map (phUV : phant (I -> V)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (I -> V)) (f g : I -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

Definition pack (fZ : mixin_of f) :=
  fun (bF : Bounded.map phUV) fA & phant_id (Bounded.class bF) fA =>
  Pack phUV (Class fA fZ).

Canonical eqType := EqType (map phUV) gen_eqMixin.
Canonical choiceType := ChoiceType (map phUV) gen_choiceMixin.
Definition bounded := Bounded.Pack phUV class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Bounded.axiom.
Coercion mixin : class_of >-> axiom.
Notation summable f := (axiom f).
Coercion apply : map >-> Funclass.
Coercion class_of_axiom : axiom >-> class_of.
Notation Summable fA := (Pack (Phant _) fA).
Notation "{ 'summable' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'summable'  fUV }") : type_scope.
Notation "[ 'summable' 'of' f 'as' g ]" := (@clone _ _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'summable'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'summable' 'of' f ]" := (@clone _ _ _ _ f f _ _ id id)
  (at level 0, format "[ 'summable'  'of'  f ]") : form_scope.
Canonical eqType.
Canonical choiceType.
Coercion bounded : map >-> Bounded.map.
Canonical bounded.

End Exports.

End Summable.
Import Summable.Exports. (* Allows GRing.additive to resolve conflicts. *)


Section BoundedLmod.
Context {I : choiceType} {K : numFieldType} {V : normedModType K}.
Implicit Type (x y : I -> V) (f g : {bounded I -> V}).

Lemma bounded_funD x y : bounded x -> bounded y -> bounded (x \+ y).
Proof.
move=>[Mx Px][My Py]; exists (Mx + My)=>i/=.
by apply/(le_trans (ler_normD _ _))/lerD.
Qed.

Lemma bounded_funN x : 
  bounded x -> bounded (\- x).
Proof. by move=>[M P]; exists M=>i/=; rewrite normrN. Qed.

Lemma bounded_funZ (a : K) x : bounded x -> bounded (a \*: x).
Proof. by move=>[M P]; exists (`|a|*M)=>i/=; rewrite normrZ ler_wpM2l. Qed.

Lemma bounded_fun_comp (a : I -> K) x : 
  bounded a -> bounded x -> bounded (fun i => a i *: x i).
Proof. by move=>[Ma Pa] [My Py]; exists (Ma * My)=>i/=; rewrite normrZ ler_pM. Qed.

Lemma bounded_zero_subproof : bounded (\0 : I -> V).
Proof. by exists 0=>i/=; rewrite normr0. Qed.
Canonical bounded_zero := Bounded bounded_zero_subproof.

Lemma bounded_cst_subproof (v : V) : bounded (fun i : I => v).
Proof. by exists `|v|=>i/=. Qed.
Canonical bounded_cst v := Bounded (bounded_cst_subproof v).

Lemma boundedP f g : f = g <-> f =1 g.
Proof.
split=>[->//|]; move: f g=>[]f+[]g+/funext/= eqf; rewrite eqf=>B1 B2.
by rewrite (Prop_irrelevance B1 B2).
Qed.

Lemma boundedfE x (H : bounded x) : x = Bounded H. Proof. by []. Qed.
Lemma boundedfP f : bounded f. Proof. by case: f. Qed.

Definition bounded_add f g :=
  Bounded (bounded_funD (boundedfP f) (boundedfP g)).

Definition bounded_opp f :=
  Bounded (bounded_funN (boundedfP f)).

Definition bounded_scale (a : K) f :=
  Bounded (bounded_funZ a (boundedfP f)).

Program Definition bounded_zmodMixin :=
  @ZmodMixin {bounded I -> V} bounded_zero bounded_opp bounded_add _ _ _ _.
Next Obligation. by move=>f g h; apply/boundedP=> i/=;rewrite addrA. Qed.
Next Obligation. by move=>f g; apply/boundedP=> i/=;rewrite addrC. Qed.
Next Obligation. by move=>f; apply/boundedP=> i/=; rewrite add0r. Qed.
Next Obligation. by move=>f; apply/boundedP=> i/=; rewrite addNr. Qed.
Canonical bounded_zmodType := ZmodType {bounded I -> V} bounded_zmodMixin.

Program Definition bounded_lmodMixin
  := @LmodMixin K [zmodType of {bounded I -> V}] bounded_scale _ _ _ _.
Next Obligation. by move=>a b f; apply/boundedP=> i/=;rewrite scalerA. Qed.
Next Obligation. by move=>f; apply/boundedP=> i/=; rewrite scale1r. Qed.
Next Obligation. by move=>a f g; apply/boundedP=> i/=; rewrite scalerDr. Qed.
Next Obligation. by move=>a f g; apply/boundedP=> i/=; rewrite scalerDl. Qed.
Canonical bounded_lmodType :=
  LmodType _ {bounded I -> V} bounded_lmodMixin.

Lemma bounded_addE f g i : (f + g) i = f i + g i.         Proof. by []. Qed.
Lemma bounded_oppE f i : (- f) i = - f i.                 Proof. by []. Qed.
Lemma bounded_scaleE (a : K) f i : (a *: f) i = a *: f i. Proof. by []. Qed.
Lemma bounded_zeroE i : (0 : {bounded I -> V}) i = 0.    Proof. by []. Qed.

Definition boundedE :=
  (bounded_zeroE, bounded_addE, bounded_oppE, bounded_scaleE).

Lemma bounded_fun_norm x : bounded x -> bounded (\`| x | : I -> K).
Proof. by move=>[M PM]; exists M=>i; rewrite normr_id. Qed.
Canonical bounded_norm_norm f := Bounded (bounded_fun_norm (boundedfP f)).

End BoundedLmod.

Section SummableLmod.
Context {I : choiceType} {K : numFieldType} {V : normedModType K}.
Implicit Type (x y : I -> V) (f g : {summable I -> V}).

Lemma has_sup_psum_preset x :
    summable x -> has_sup (psum_preset \`| x |).
Proof.
move=>[M PM]; split.
by exists 0=>/=; rewrite/S/=; exists fset0; rewrite /psum big_fset0.
exists M=>z; rewrite/S/==>[[J ->]].
move: PM=>[A _]/(_ (J `|` (A `\` J))%fset)/=.
rewrite {1}fsetUDl fsetDv fsetD0=>/(_ (fsubsetUr _ _)).
apply le_trans.
by rewrite psumU ?fdisjointXD// lerDl /psum sumr_ge0.
Qed.

Lemma summable_funD x y : 
  summable x -> summable y -> summable (x \+ y).
Proof.
move=>[Mx Px][My Py]; exists (Mx + My); near=>J.
suff P1: psum \`| x + y | J <= psum \`| x | J + psum \`| y | J.
apply: (le_trans P1); clear P1; rewrite lerD//; near: J.
apply Px. apply Py.
by rewrite -big_split ler_sum// =>i _; rewrite ler_normD.
Unshelve. end_near.
Qed.

Lemma summable_funN x : 
  summable x -> summable (\- x).
Proof.
move=>[M P]; exists M; near=>J.
rewrite/psum; under eq_bigr do rewrite normrN.
near: J. apply: P. Unshelve. end_near.
Qed.

Lemma summable_funZ (a : K) x : 
  summable x -> summable (a \*: x).
Proof.
move=>[M P]; exists (`|a|*M); near=>J.
rewrite/psum; under eq_bigr do rewrite/=/GRing.scale/= normrZ.
rewrite -mulr_sumr ler_wpM2l//.
near: J. apply: P. Unshelve. end_near.
Qed.

Lemma summable_fun_comp (a : I -> K) x : 
  summable a -> summable x -> summable (fun i => a i *: x i).
Proof.
move=>[Ma Pa] [My Py]; exists (Ma * My); near=>J.
apply: (le_trans (y := Ma * psum \`| x | J)).
rewrite /psum mulr_sumr ler_sum// =>i _.
rewrite normrZ ler_pM//.
2: rewrite ler_pM//.
1,2: apply: (le_trans (y := psum \`| a | J)).
have P3: (val i) \in J by case: i.
by rewrite /psum (big_fset_seqE J \`| a |)/= (big_fsetD1 _ P3)/= lerDl sumr_ge0.
2,4: by rewrite sumr_ge0.
all: near: J; by [apply Pa | apply Py].
Unshelve. end_near.
Qed.

Lemma summable_zero_subproof : summable (\0 : I -> V).
Proof.
exists 0. near=>J.
by rewrite /psum big1// =>i _; rewrite normr0.
Unshelve. end_near.
Qed.

Canonical summable_zero := Summable summable_zero_subproof.

Lemma summableP f g : f = g <-> f =1 g.
Proof.
split=>[->//|]; move: f g=>[]f[]/=++[]g[]/=++/funext eqf; rewrite eqf=>B1 S1 B2 S2.
by rewrite (Prop_irrelevance B1 B2) (Prop_irrelevance S1 S2).
Qed.

Lemma summablefE x (H : summable x) : x = Summable H.
Proof. by []. Qed.

Lemma summablefP f : summable f.
Proof. by case: f=>?[]. Qed.

Definition summable_add f g :=
  Summable (summable_funD (summablefP f) (summablefP g)).

Definition summable_opp f :=
  Summable (summable_funN (summablefP f)).

Definition summable_scale (a : K) f :=
  Summable (summable_funZ a (summablefP f)).

Program Definition summable_zmodMixin :=
  @ZmodMixin {summable I -> V} summable_zero summable_opp summable_add _ _ _ _.
Next Obligation. by move=>f g h; apply/summableP=> i/=;rewrite addrA. Qed.
Next Obligation. by move=>f g; apply/summableP=> i/=;rewrite addrC. Qed.
Next Obligation. by move=>f; apply/summableP=> i/=; rewrite add0r. Qed.
Next Obligation. by move=>f; apply/summableP=> i/=; rewrite addNr. Qed.
Canonical summable_zmodType := ZmodType {summable I -> V} summable_zmodMixin.

Program Definition summable_lmodMixin
  := @LmodMixin K [zmodType of {summable I -> V}] summable_scale _ _ _ _.
Next Obligation. by move=>a b f; apply/summableP=> i/=;rewrite scalerA. Qed.
Next Obligation. by move=>f; apply/summableP=> i/=; rewrite scale1r. Qed.
Next Obligation. by move=>a f g; apply/summableP=> i/=; rewrite scalerDr. Qed.
Next Obligation. by move=>a f g; apply/summableP=> i/=; rewrite scalerDl. Qed.
Canonical summable_lmodType :=
  LmodType _ {summable I -> V} summable_lmodMixin.

Lemma summable_addE f g i : (f + g) i = f i + g i.         Proof. by []. Qed.
Lemma summable_oppE f i : (- f) i = - f i.                 Proof. by []. Qed.
Lemma summable_scaleE (a : K) f i : (a *: f) i = a *: f i. Proof. by []. Qed.
Lemma summable_zeroE i : (0 : {summable I -> V}) i = 0.    Proof. by []. Qed.
Lemma summable_sumE (J : Type) (r : seq J) (P : pred J) (F : J -> {summable I -> V}) i :
  (\sum_(j <- r | P j) F j) i = \sum_(j <- r | P j) F j i.
Proof. by elim/big_rec2: _=>//???? <-; rewrite summable_addE. Qed.

Definition summableE :=
  (summable_zeroE, summable_addE, summable_oppE, summable_scaleE).

Lemma summable_fun_norm x : summable x -> summable (\`| x | : I -> K).
Proof.
move=>[M PM]; exists M; near=>J.
rewrite/psum; under eq_bigr do rewrite normr_id.
near: J; apply: PM.
Unshelve. end_near.
Qed.

Canonical summable_norm_norm f := Summable (summable_fun_norm (summablefP f)).

Lemma summable_sum_cst0 : sum ((fun i : I => 0 : V)) = 0.
Proof.
rewrite/sum; suff ->: (psum (fun _ : I => 0 : V)) = fun=>0 by rewrite lim_cst.
by apply/funext=>i; rewrite/psum big1.
Qed.

Lemma summable_sum0 : sum (0 : {summable I -> V}) = 0.
Proof. exact: summable_sum_cst0. Qed.

End SummableLmod.

Section fset_topologicalType.
Variable (I : choiceType).

Let D : set {fset I} := setT.
Let b : {fset I} -> set {fset I} := fun i => [set i].
Let bT : \bigcup_(i in D) b i = setT.
Proof. by rewrite predeqE => i; split => // _; exists i. Qed.

Let bD : forall i j t, D i -> D j -> b i t -> b j t ->
  exists k, [/\ D k, b k t & b k `<=` b i `&` b j].
Proof. by move=> i j t _ _ -> ->; exists j. Qed.

Definition fset_topologicalTypeMixin := topologyOfBaseMixin bT bD.
Canonical fset_filteredType := FilteredType {fset I} {fset I} (nbhs_of_open (open_from D b)).
Canonical fset_topologicalType := TopologicalType {fset I} fset_topologicalTypeMixin.

End fset_topologicalType.

Section Bounded_NormedMod.
Context {I : choiceType} {R : realType} {C : extNumType R} {V : normedModType C}.
Local Notation F := {bounded I -> V}.
Implicit Type (f g : F).

Definition bounded_norm f := etsup [set y | y = 0 \/ exists i, y = `|f i| ].

Lemma has_sup_bounded_norm f : has_sup [set y | y = 0 \/ exists i, y = `|f i| ].
Proof.
split; first by exists 0=>/=; left.
by move: (boundedfP f)=>[e Pe]; exists (Num.max 0 e)=>y/=[->|[]i->];
rewrite ?max_le_l// max_r//; apply: (le_trans _ (Pe i)).
Qed.

Lemma bounded_norm_upper f i : `|f i| <= bounded_norm f.
Proof.
by apply/etsup_upper_bound; [apply/has_sup_bounded_norm | right; exists i].
Qed.

Lemma bounded_norm_least f e : 0 <= e ->
  (forall i, `|f i| <= e) -> bounded_norm f <= e.
Proof.
move=>Pe P. apply: etsup_least_ubound. apply/has_sup_bounded_norm.
by move=>y/=[->|[]i->].
Qed.

Lemma bounded_norm0_eq0 f : bounded_norm f = 0 -> f = 0.
Proof.
move=>P2; apply/boundedP=>i/=; apply/normr0_eq0.
by move: (bounded_norm_upper f i); rewrite P2 normr_le0=>/eqP->; rewrite normr0.
Qed.

Lemma bounded_norm_ge0 f : 0 <= bounded_norm f.
Proof. by apply/etsup_upper_bound=>/=; [apply/has_sup_bounded_norm |left]. Qed.

Lemma bounded_norm_triangle f g : 
  bounded_norm (f + g) <= bounded_norm f + bounded_norm g.
Proof.
apply/bounded_norm_least=>[|i/=]; first by rewrite addr_ge0// bounded_norm_ge0.
apply/(le_trans (ler_normD _ _))/lerD; apply/bounded_norm_upper.
Qed.

Lemma bounded_normZ (a: C) f : 
  bounded_norm (a *: f) = `|a| * bounded_norm f.
Proof.
apply/le_anti/andP; split; last (case E: (a == 0); move: E=>/eqP).
apply/bounded_norm_least=>[|i/=].
apply/mulr_ge0=>//; apply/bounded_norm_ge0.
rewrite normrZ ler_wpM2l//; apply/bounded_norm_upper.
move=>->; rewrite normrE mul0r; apply/bounded_norm_ge0.
move=>/eqP; rewrite -normr_gt0=>P; rewrite mulrC -ler_pdivlMr//.
apply/bounded_norm_least=>[|i].
by apply/divr_ge0; [apply/bounded_norm_ge0|apply/ltW].
rewrite ler_pdivlMr// mulrC -normrZ.
by apply: (le_trans _ (bounded_norm_upper _ i)).
Qed.

Canonical bounded_norm_vnorm := Vnorm bounded_norm_triangle bounded_norm0_eq0 bounded_normZ.

Lemma bounded_normMn f n : bounded_norm (f *+ n) = bounded_norm f *+ n.
Proof. exact: normvMn. Qed.

Lemma bounded_normN f : bounded_norm (- f) = bounded_norm f.
Proof. exact: normvN. Qed.

Definition bounded_normedZmodMixin := 
    Num.NormedMixin bounded_norm_triangle bounded_norm0_eq0 bounded_normMn bounded_normN.
Canonical bounded_normedZmodType :=
    Eval hnf in NormedZmodType C F bounded_normedZmodMixin.

Canonical bounded_pointedType := [pointedType of F for pointed_of_zmodule [zmodType of F]].
Canonical bounded_filteredType := [filteredType F of F for filtered_of_normedZmod [normedZmodType C of F]].
Canonical bounded_topologicalType := (TopologicalType F (topologyOfEntourageMixin (uniformityOfBallMixin
                                 (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _)))).
Canonical bounded_uniformType := (UniformType F (uniformityOfBallMixin
                            (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _))).
Canonical bounded_pseudoMetricType := (PseudoMetricType F (pseudoMetric_of_normedDomain [normedZmodType C of F])).

Lemma bounded_norm_ball :
  @ball _ [pseudoMetricType C of F] = ball_ (fun x => `| x |).
Proof. by rewrite /normr /ball_ predeq3E/= /ball/=/normr/=. Qed.

Definition bounded_PseudoMetricNormedZmodMixin := PseudoMetricNormedZmodule.Mixin bounded_norm_ball.
Canonical bounded_pseudoMetricNormedZmodType := PseudoMetricNormedZmodType C F bounded_PseudoMetricNormedZmodMixin.

Definition bounded_NormedModMixin := NormedModMixin bounded_normZ.
Canonical bounded_normedModType := NormedModType C F bounded_NormedModMixin.

Lemma boundedE_cvg (T : Type) (F : set (set T)) {FF : Filter F} 
  (f : T -> {bounded I -> V}) (g : {bounded I -> V}) :
  f @ F --> g -> forall i : I, (fun t => f t i) @ F --> g i.
Proof.
move=>/fcvgrPdist_lt P1 i; apply/fcvgrPdist_lt=>e egt0.
rewrite near_simpl; move: (P1 e egt0); rewrite near_simpl=>P2.
near=>t; have: (`|g - f t| < e) by near: t; apply: P2.
apply: le_lt_trans.
by apply: (le_trans _ (bounded_norm_upper _ i)); rewrite boundedE/=.
Unshelve. end_near.
Qed.

Lemma boundedE_is_cvg (T : Type) (F : set (set T)) {FF : ProperFilter F} 
  (f : T -> {bounded I -> V}) :
    cvg (f @ F) -> forall i : I, cvg ((fun t => f t i) @ F).
Proof. by move=>P i; apply/cvg_ex; exists (lim (f @ F) i); apply: boundedE_cvg. Qed.

Lemma boundedE_lim (T : Type) (F : set (set T)) {FF : ProperFilter F} 
  (f : T -> {bounded I -> V}) :
    cvg (f @ F) -> forall i : I, lim ((fun t => f t i) @ F) = lim (f @ F) i.
Proof. by move=>/boundedE_cvg P i; move: (P i)=>/(cvg_lim (@norm_hausdorff _ _)). Qed.

End Bounded_NormedMod.

Section Bounded_Complete.
Context {I : choiceType} {R : realType} {C : extNumType R} {V : completeNormedModType C}.

Lemma bounded_complete (F : set (set {bounded I -> V})) : 
  ProperFilter F -> cauchy F -> cvg F.
Proof.
move=>FF /cauchyP F_cauchy.
pose G i := (fun f=>f i) @ F.
have P1 : forall i : I, cvg (G i).
  move=>j; apply/cauchy_cvgP/cauchyP=>e egt0.
  move: (F_cauchy _ egt0)=>/=[f Pf].
  exists (f j); rewrite/G/= nbhs_filterE; apply: (filterS _ Pf)=>x.
  rewrite -!ball_normE/= {1}/normr/=; apply: le_lt_trans.
  by apply: (le_trans _ (bounded_norm_upper _ j)).
pose g i := lim (G i).
have Pg : bounded g.
  move: (F_cauchy _ ltr01)=>/=[f Pf]; exists (`|f|+1)=>i.
  apply: (le_trans (y := `|f i| + 1));
    last by rewrite lerD2; apply: bounded_norm_upper.
  rewrite/g -lim_norm/=; first apply: P1.
  apply: etlim_le_nearF. apply: is_cvg_norm; apply: P1.
  rewrite near_simpl. near=>J.
  have: ball f 1 J by near: J; rewrite near_simpl/= -nbhs_nearE/nbhs/=.
  rewrite /ball/==>P; rewrite addrC -lerBlDr.
  apply: (le_trans _ (ltW (le_lt_trans (bounded_norm_upper (f - J) i) P))).
  by rewrite/= -[ `| _ - _|]normrN opprB lerB_dist.
apply/cvg_ex; exists (Bounded Pg). rewrite cvgrPdist_le=>e egt0.
move: {+}F_cauchy=>/cauchyP/cauchy_ballP/(_ _ egt0)/nearP_dep P2.
near=>f. apply/bounded_norm_least=>[|i]. by apply/ltW.
rewrite/=/g. have->: `|lim (G i) - f i| = lim (`| (x - f) i | @[x --> F]).
  rewrite/= lim_norm; [apply: is_cvgB | rewrite limB ].
  1,3: apply: P1. 1,2: apply: is_cvg_cst. by rewrite lim_cst. 
apply: etlim_le_nearF. 
by apply: is_cvg_norm; apply: is_cvgB; [apply: P1 | apply: is_cvg_cst].
near=>h; apply/ltW.
have /ball_sym: ball f e h. near: h. near: f. apply: P2.
rewrite -ball_normE/ball_/=; apply/le_lt_trans.
by apply: (le_trans _ (bounded_norm_upper _ i)); rewrite boundedE/=.
Unshelve. all: end_near.
Qed.

Canonical bounded_completeType := 
  CompleteType {bounded I -> V} (@bounded_complete).
Canonical bounded_CompleteNormedModule :=
  [completeNormedModType C of {bounded I -> V}].

End Bounded_Complete.

Section SummableCvg.
Context {I : choiceType} {R : realType} {C : extNumType R} {V : normedModType C}.
Local Notation F := {summable I -> V}.
Implicit Type (f g : {summable I -> V}).

Definition summable_norm f := lim (psum \`| f |).

Lemma summable_norm_cvg f :
  (psum \`| f |) --> (etsup (psum_preset \`| f |)).
Proof.
apply/cvgrPdist_lt=>e egt0.
move: (has_sup_psum_preset (summablefP f))=>hs.
move:{+}hs=>/etsup_adherent hs1; move: (hs1 _ egt0)=>[y]/= [J -> Pj].
exists J=>//= z/= Pz; rewrite ger0_norm.
by rewrite subr_ge0; apply: (etsup_upper_bound hs); rewrite/S/=; exists z.
rewrite ltrBlDr addrC -ltrBlDr; apply: (lt_le_trans Pj).
by rewrite -(fsetUD_sub Pz) psumU ?fdisjointXD// lerDl /psum sumr_ge0.
Qed.
Arguments summable_norm_cvg : clear implicits.

Lemma summable_norm_is_cvg f : cvg (psum \`| f |).
Proof. by move: (summable_norm_cvg f)=>/cvgP. Qed.
Arguments summable_norm_is_cvg : clear implicits.

Lemma summable_normE f :
  summable_norm f = etsup (psum_preset \`| f |).
Proof. apply: cvg_lim=>//; apply/summable_norm_cvg. Qed.

Lemma psum_norm_ler_norm f J : psum \`| f | J <= summable_norm f.
Proof.
suff: (\forall K \near totally, psum \`| f | J <= psum \`| f | K).
move=> /(closed_cvg (>= psum \`| f | J)) P.
move: (summable_norm_is_cvg f); apply/P/etclosed_ge.
near=>K. apply/psum_ler=>//. near: K. exists J=>//.
Unshelve. end_near.
Qed.

Lemma summable_norm0_eq0 f : summable_norm f = 0 -> f = 0.
Proof.
move=>P2; apply/summableP=>i/=; apply/normr0_eq0.
apply/le_anti/andP; split=>//; rewrite -P2.
apply: (le_trans (y := psum \`| f | [fset i]%fset)).
by rewrite psum1. by apply/psum_norm_ler_norm.
Qed.

Lemma summable_norm_triangle f g : 
  summable_norm (f + g) <= summable_norm f + summable_norm g.
Proof.
rewrite /summable_norm -limD; last first. apply: ler_etlimF; last first.
by move=>/= J; rewrite !fctE -psumD ler_sum// =>i _; rewrite fctE ler_normD.
apply: is_cvgD. all: apply: summable_norm_is_cvg.
Qed.

Lemma summable_normZ (a: C) f : 
  summable_norm (a *: f) = `|a| * summable_norm f.
Proof.
rewrite/summable_norm.
transitivity (`|a| *: lim (psum (fun i : I => `|f i|))).
rewrite -limZr; first by apply: summable_norm_is_cvg.
apply: lim_eq=>J; rewrite !fctE /psum scaler_sumr; apply eq_bigr=>i _.
all: by rewrite/= 1?normrZ /GRing.scale.
Qed.

Canonical summable_norm_vnorm := Vnorm summable_norm_triangle summable_norm0_eq0 summable_normZ.

Lemma summable_normMn f n : summable_norm (f *+ n) = summable_norm f *+ n.
Proof. exact: normvMn. Qed.

Lemma summable_normN f : summable_norm (- f) = summable_norm f.
Proof. exact: normvN. Qed.

Definition summable_normedZmodMixin := 
    Num.NormedMixin summable_norm_triangle summable_norm0_eq0 summable_normMn summable_normN.
Canonical summable_normedZmodType :=
    Eval hnf in NormedZmodType C F summable_normedZmodMixin.

Canonical summable_pointedType := [pointedType of F for pointed_of_zmodule [zmodType of F]].
Canonical summable_filteredType := [filteredType F of F for filtered_of_normedZmod [normedZmodType C of F]].
Canonical summable_topologicalType := (TopologicalType F (topologyOfEntourageMixin (uniformityOfBallMixin
                                 (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _)))).
Canonical summable_uniformType := (UniformType F (uniformityOfBallMixin
                            (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _))).
Canonical summable_pseudoMetricType := (PseudoMetricType F (pseudoMetric_of_normedDomain [normedZmodType C of F])).

Lemma summable_norm_ball :
  @ball _ [pseudoMetricType C of F] = ball_ (fun x => `| x |).
Proof. by rewrite /normr /ball_ predeq3E/= /ball/=/normr/=. Qed.

Definition summable_PseudoMetricNormedZmodMixin := PseudoMetricNormedZmodule.Mixin summable_norm_ball.
Canonical summable_pseudoMetricNormedZmodType := PseudoMetricNormedZmodType C F summable_PseudoMetricNormedZmodMixin.

Definition summable_NormedModMixin := NormedModMixin summable_normZ.
Canonical summable_normedModType := NormedModType C F summable_NormedModMixin.

Lemma summableE_cvg (T : Type) (F : set (set T)) {FF : Filter F} 
  (f : T -> {summable I -> V}) (g : {summable I -> V}) :
  f @ F --> g -> forall i : I, (fun t => f t i) @ F --> g i.
Proof.
move=>/fcvgrPdist_lt P1 i; apply/fcvgrPdist_lt=>e egt0.
rewrite near_simpl; move: (P1 e egt0); rewrite near_simpl=>P2.
near=>t; have: (`|g - f t| < e) by near: t; apply: P2.
apply: le_lt_trans.
by apply: (le_trans _ (psum_norm_ler_norm _ [fset i]%fset)); rewrite psum1/=.
Unshelve. end_near.
Qed.

Lemma summableE_is_cvg (T : Type) (F : set (set T)) {FF : ProperFilter F} 
  (f : T -> {summable I -> V}) :
    cvg (f @ F) -> forall i : I, cvg ((fun t => f t i) @ F).
Proof. by move=>P i; apply/cvg_ex; exists (lim (f @ F) i); apply: summableE_cvg. Qed.

Lemma summableE_lim (T : Type) (F : set (set T)) {FF : ProperFilter F} 
  (f : T -> {summable I -> V}) :
    cvg (f @ F) -> forall i : I, lim ((fun t => f t i) @ F) = lim (f @ F) i.
Proof. by move=>/summableE_cvg P i; move: (P i)=>/(cvg_lim (@norm_hausdorff _ _)). Qed.

End SummableCvg.

Section cvg_sum_pseudometric.
Context {K : numFieldType} {V : pseudoMetricNormedZmodType K}.
Context {T : Type} (F : set (set T)).

(* Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V). *)

Lemma cvg_sum_apply  {FF : Filter F}
    (I : Type) (r : seq I) (P : pred I) (f : I -> T -> V) (a : I -> V) :
  (forall i, P i -> f i @ F --> a i) -> 
    (\sum_(i <- r | P i) (f i t)) @[t --> F] --> (\sum_(i <- r | P i) a i).
Proof.
move=>P1. elim: r.
rewrite big_nil. under eq_cvg do rewrite big_nil. apply: cvg_cst.
move=>h t IH. rewrite big_cons.
under eq_cvg do rewrite big_cons.
case E: (P h); last by apply : IH.
move: (P1 _ E)=>P2. apply: cvgD. apply: P2. apply: IH.
Qed.

Lemma is_cvg_sum_apply {FF : Filter F}
    (I : Type) (r : seq I) (P : pred I) (f : I -> T -> V) : 
      (forall i, P i -> cvg (f i @ F)) -> cvg ((\sum_(i <- r | P i) (f i t)) @[t --> F]).
Proof. by have := cvgP _ (cvg_sum_apply _); apply. Qed.

Lemma lim_sum_apply {FF : ProperFilter F}
    (I : Type) (r : seq I) (P : pred I) (f : I -> T -> V) :
  (forall i, P i -> cvg (f i @ F)) ->
    lim ((\sum_(i <- r | P i) (f i t)) @[t --> F]) = \sum_(i <- r | P i) lim (f i @ F). 
Proof. by move=> ?; apply: cvg_lim => //; apply: cvg_sum_apply. Qed.

Lemma lim_sum_apply_fset {FF : ProperFilter F}
    (I : choiceType) (J : {fset I}) (f : I -> T -> V) :
  (forall i : J, cvg (f (val i) @ F)) ->
    lim ((\sum_(i : J) (f (val i) t)) @[t --> F]) = \sum_(i : J) lim (f (val i) @ F). 
Proof. move=>?; exact: lim_sum_apply. Qed.

Lemma cvg_sum  {FF : Filter F}
    (I : Type) (r : seq I) (P : pred I) (f : I -> T -> V) (a : I -> V) :
  (forall i, P i -> f i @ F --> a i) -> 
    (\sum_(i <- r | P i) (f i)) @ F --> (\sum_(i <- r | P i) a i).
Proof.
move=>P1; elim/big_rec2: _ => [|i b /= g Pi cg]; first by apply: cvg_cst.
by apply: cvgD=>//; apply: P1.
Qed. 

Lemma is_cvg_sum {FF : Filter F}
    (I : Type) (r : seq I) (P : pred I) (f : I -> T -> V) : 
      (forall i, P i -> cvg (f i @ F)) -> cvg ((\sum_(i <- r | P i) (f i)) @ F).
Proof. by have := cvgP _ (cvg_sum _); apply. Qed.

Lemma lim_sum {FF : ProperFilter F}
    (I : Type) (r : seq I) (P : pred I) (f : I -> T -> V) :
  (forall i, P i -> cvg (f i @ F)) ->
    lim ((\sum_(i <- r | P i) (f i)) @ F) = \sum_(i <- r | P i) lim (f i @ F). 
Proof. by move=> ?; apply: cvg_lim => //; apply: cvg_sum. Qed.

Lemma lim_sum_fset {FF : ProperFilter F}
    (I : choiceType) (J : {fset I}) (f : I -> T -> V) :
  (forall i : J, cvg (f (val i) @ F)) ->
    lim ((\sum_(i : J) (f (val i))) @ F) = \sum_(i : J) lim (f (val i) @ F). 
Proof. move=>?; exact: lim_sum. Qed.

End cvg_sum_pseudometric.

Section Cauchy_ball_fset.
Context {R : numFieldType} {T : pseudoMetricNormedZmodType R} {I : choiceType}.

Definition cauchy_ball_fset (f : {fset I} -> T) :=
  forall e : R, e > 0 -> \forall x & y \near totally, (x `<=` y)%fset -> ball (f x) e (f y).

Lemma cauchy_ball_fsetP (f : {fset I} -> T) :
  cauchy_ball_fset f <-> cauchy [filter of f].
Proof.
split=>[P1 | /cauchy_ballP P1 e egt0]; last first.
  move: (P1 e egt0); rewrite !near_simpl !near2E=>P2.
  by near=>x; move=>_; near: x; apply P2.
apply/cauchy_ballP=>e egt0; rewrite !near_simpl near2E; apply/filter2P.
have e2gt0 : 0 < e / 2 by rewrite divr_gt0.
move: (P1 _ e2gt0); rewrite near2E=>/filter2P[t [[s1/= _ Ps1] [s2/= _ Ps2]]/= P2].
exists ([set B | (s1 `|` s2 `<=` B)%fset], [set B | (s1 `|` s2 `<=` B)%fset]).
by split; exists (s1 `|` s2)%fset.
move=>x y/=; rewrite !fsubUset=>/andP[Q1 Q2]/andP[Q3 Q4].
have: ball (f x) (e / 2) (f (x `|` y)%fset) /\ ball (f y) (e / 2) (f (x `|` y)%fset).
split; apply: P2. 1,4: by apply: Ps1. 1,3: by apply/Ps2/fsubsetU/orP; right. 
by apply/fsubsetUl. by apply/fsubsetUr.
rewrite -ball_normE/==>[[]]P3 P4.
move: (ltrD P3 P4). rewrite [ `|f y - _ |]distrC -splitr.
apply: le_lt_trans. apply: ler_distD.
Unshelve. end_near.
Qed.

End Cauchy_ball_fset.

Section Summable_Complete.
Context {I : choiceType} {R : realType} {C : extNumType R} {V : completeNormedModType C}.

Lemma summable_cvg (f : {summable I -> V}) : cvg (psum f).
Proof.
move: (summable_norm_is_cvg (f := f))=>/cauchy_cvgP/cauchy_ball_fsetP P1.
suff: cauchy [filter of psum f]. by apply: cauchy_cvg.
apply/cauchy_ball_fsetP=>e egt0; move: (P1 e egt0); rewrite !near2E=>P2.
near=>x. move=> Px.
have: ball (psum \`| f | x.1) e (psum \`| f | x.2).
move: Px; near: x; apply: P2.
move: Px; rewrite -!ball_normE/= -psumIB -[in X in _ -> _ -> X]psumIB -fsetD_eq0=>/eqP->.
rewrite !psum0 !sub0r !normrN. apply: le_lt_trans. apply: (le_trans _ (real_ler_norm _)).
apply: ler_norm_sum. by apply/ger0_real/sumr_ge0.
Unshelve. end_near.
Qed.

Lemma summable_complete (F : set (set {summable I -> V})) : 
  ProperFilter F -> cauchy F -> cvg F.
Proof.
move=>FF /cauchyP F_cauchy.
pose G i := (fun f=>f i) @ F.
have P1 : forall i : I, cvg (G i).
  move=>j; apply/cauchy_cvgP/cauchyP=>e egt0.
  move: (F_cauchy _ egt0)=>/=[f Pf].
  exists (f j); rewrite/G/= nbhs_filterE; apply: (filterS _ Pf)=>x.
  rewrite -!ball_normE/= {1}/normr/=; apply: le_lt_trans.
  apply: (le_trans (y := psum \`| f - x | [fset j]%fset)).
  by rewrite psum1. by apply/psum_norm_ler_norm.
pose g i := lim (G i).
have Pg : summable g.
  move: (F_cauchy _ ltr01)=>/=[f Pf]; exists (`|f|+1); near=>J.
  apply: (le_trans (y := psum \`| f | J + 1));
    last by rewrite lerD2; apply: psum_norm_ler_norm.
  rewrite addrC -lerBlDr -psumB /psum.
  apply: (le_trans (y := \sum_i lim ((fun x=>`|x (val i) - f (val i)|) @ F))).
  - apply: ler_sum=>i _; rewrite/g!fctE -lim_norm; last first. 
  have ->: `|f (val i)| = lim (`|f (val i)| @[x --> fun x : set (I -> V) =>
    [filter of F] (fun x0 => x x0)]) by rewrite lim_cst.
  rewrite -limB; last (apply: ler_etlimF; last by move=>h; rewrite !fctE lerB_dist).
  1,2,4: apply: is_cvg_norm. 3,4: apply: is_cvgB. 5,6: apply: is_cvg_norm.
    1,3,5,7: apply: P1. 1,2,3: apply: is_cvg_cst.
  - rewrite -lim_sum; last (apply: etlim_le_nearF; first apply: is_cvg_sum).  
    1,2: move=>i _/=; apply: is_cvg_norm; apply: is_cvgB; [apply P1 | apply: is_cvg_cst].
    rewrite near_simpl. near=>K. have: ball f 1 K by near: K; apply: Pf.
    rewrite -ball_normE/ball_/= distrC fct_sumE =>P2.
    under eq_bigr do rewrite -!summableE.
    apply/ltW/(le_lt_trans _ P2)/psum_norm_ler_norm.
apply/cvg_ex; exists (Summable Pg). rewrite cvgrPdist_le=>e egt0.
move: {+}F_cauchy=>/cauchyP/cauchy_ballP/(_ _ egt0)/nearP_dep P2.
near=>f. apply: etlim_le_nearF. apply: summable_norm_is_cvg.
near=>J. rewrite/psum.
have->:  \sum_(i : J) `|(Summable Pg - f) (val i)| = (\sum_(i : J) lim (`|(x - f) (val i)| @[x --> F])).
  apply eq_bigr=>i _; rewrite/= lim_norm; [apply: is_cvgB | rewrite limB ]; last by rewrite lim_cst.
  1,3: apply: P1. 1,2: apply: is_cvg_cst.
rewrite -lim_sum; last apply: etlim_le_nearF.
by move=>i _; apply: is_cvg_norm; apply: is_cvgB; [apply P1 | apply: is_cvg_cst].
by apply: is_cvg_sum=>i _; apply: is_cvg_norm; apply: is_cvgB; [apply: P1 | apply: is_cvg_cst].
near=>h; apply/ltW.
have: ball f e h by near: h; near: f; apply: P2.
rewrite -ball_normE/ball_/= fct_sumE distrC; apply: le_lt_trans.
under eq_bigr do rewrite -!summableE; apply: psum_norm_ler_norm.
Unshelve. all: end_near.
Qed.

Canonical summable_completeType := 
  CompleteType {summable I -> V} (@summable_complete).
Canonical summable_CompleteNormedModule :=
  [completeNormedModType C of {summable I -> V}].

Implicit Type (x y z : {summable I -> V}).

Lemma summable_sumP (a : C) x y : 
  sum (a *: x + y) = a *: (sum x) + sum y.
Proof.
rewrite/sum -limZr; first by apply: summable_cvg.
rewrite -limD. apply: is_cvgZr. 1,2: apply: summable_cvg.
apply: eq_lim=>i; rewrite !fctE /psum; under eq_bigr do rewrite !summableE.
by rewrite big_split/= scaler_sumr.
Qed.

Lemma summable_sumD x y : sum (x + y) = sum x + sum y.
Proof. by rewrite -[x]scale1r summable_sumP !scale1r. Qed. 

Lemma summable_sumZ (a : C) x : sum (a *: x) = a *: sum x.
Proof. by rewrite -[a *: x]addr0 summable_sumP summable_sum0 !addr0. Qed.

Lemma summable_sumN x : sum (- x) = - sum x.
Proof. by rewrite -scaleN1r summable_sumZ scaleN1r. Qed.

Lemma summable_sumB x y : sum (x - y) = sum x - sum y.
Proof. by rewrite summable_sumD summable_sumN. Qed.

Lemma summable_sum_sum (J : Type) (r : seq J) (P : pred J) (F : J -> {summable I -> V}) :
  sum (\sum_(j <- r | P j) F j) = \sum_(j <- r | P j) (sum (F j)).
Proof. by elim/big_rec2: _ =>[|???? <-]; rewrite ?summable_sum0// summable_sumD. Qed.

Lemma summable_sum_ler_norm x : `|sum x| <= sum \`| x |.
Proof.
rewrite/sum -lim_norm. apply: summable_cvg.
apply: ler_etlimF. apply: is_cvg_norm. apply: summable_cvg.
apply: summable_norm_is_cvg.
move=>n; rewrite /psum; apply: normv_sum.
Qed.

Definition summable_sum (f : {summable I -> V}) := sum f.

Lemma summable_sum_continuous : continuous summable_sum.
Proof.
move=> x s/= /nbhs_ballP [/=e egt0 Pb]; apply/nbhs_ballP.
exists e=>// y/= P1; apply: Pb; move: P1.
rewrite -!ball_normE/= -summable_sumB. apply: le_lt_trans.
rewrite -lim_norm; first by apply: summable_cvg.
rewrite {5}/Num.Def.normr/summable_norm; apply: ler_etlimF.
apply: is_cvg_norm; apply: summable_cvg.
apply: summable_norm_is_cvg.
move=>S; apply: ler_norm_sum.
Qed.

Lemma summable_sum_cvg (T : Type) (F : set (set T)) {FF : ProperFilter F} 
  (f : T -> {summable I -> V}) (g : {summable I -> V}):
  f @ F --> g -> sum (f i) @[i --> F] --> sum g.
Proof.
have ->: (fun i => sum (f i)) = (fun i => summable_sum (f i)).
by apply/funext=>i.
apply: continuous_cvg. apply: summable_sum_continuous.
Qed.

Lemma summable_sum_is_cvg (T : Type) (F : set (set T)) {FF : ProperFilter F} 
  (f : T -> {summable I -> V}) :
  cvg (f @ F) -> cvg (sum (f i) @[i --> F]).
Proof.
move=>/cvg_ex=>[/= [a Pa]]; apply/cvg_ex.
by exists (sum a); apply: summable_sum_cvg.
Qed.

Lemma summable_sum_lim (T : Type) (F : set (set T)) {FF : ProperFilter F} 
  (f : T -> {summable I -> V}) : cvg (f @ F) -> 
  lim (sum (f i) @[i --> F]) = sum (lim (f @ F)).
Proof. by move=>/summable_sum_cvg P; apply: cvg_lim. Qed.

End Summable_Complete.

Section test.
Context {I : choiceType} {R : realType} {C : extNumType R} {V W : completeNormedModType C} .

Lemma cvg_linear_sumG (x : I -> V) (f : {linear V -> W}) :
  (exists k, 0 < k /\ forall v, `|f v| <= k * `|v|) -> cvg (psum x) ->
  f (sum x) = sum (f \o x)%FUN.
Proof.
move=>[k [Pk1 Pk2]] /cvgrPdist_lt Px.
suff: psum (f \o x) --> f (sum x) by move=>/cvg_lim<-.
apply/cvgrPdist_lt=>e egt0; near=>S.
have: `|sum x - psum x S| < e / k by near: S; apply/Px/divr_gt0.
rewrite ltr_pdivlMr//; apply: le_lt_trans.
rewrite/psum/= -linear_sum/= -linearB mulrC; apply: Pk2.
Unshelve. end_near.
Qed.

Lemma summable_linear_sumG (x : {summable I -> V}) (f : {linear V -> W}) :
  (exists k, 0 < k /\ forall v, `|f v| <= k * `|v|) ->
  f (sum x) = sum (f \o x)%FUN.
Proof. move=>P1; apply: cvg_linear_sumG=>//; apply: summable_cvg. Qed.

End test.


Section Bounded_Cvg.
Context {I : choiceType} {R : realType} {C : extNumType R} {V : completeNormedModType C}.

Lemma norm_bounded_cvg (f : I -> V) : 
  (exists (M : C), \forall J \near totally, (psum \`| f | J <= M)%R) ->
  cvg (psum f).
Proof.
move=>P. have P1: Summable.axiom f. by [].
pose g := Summable P1.
have ->: f = g. by []. apply: summable_cvg.
Qed.

End Bounded_Cvg.

Section FinSupp.

Definition suppf {I} {V : zmodType} (f : I -> V) :=
  [set x | f x != 0].

Lemma foo1 {I : choiceType} (J : {fset I}) (i : I) :
  (i \in J) <-> ([set` J] i).
Proof. by split=>/=. Qed.

Lemma fin_suppf_summable {I : choiceType} {K : numFieldType} 
  {V : normedZmodType K} (f : I -> V) :
    finite_set (suppf f) -> summable f.
Proof.
move=>/finite_fsetP[J PJ].
have P1: forall i, i \notin J -> f i = 0.
by move=>i /negP; rewrite foo1 -PJ/suppf/==>/negP; rewrite negbK=>/eqP.
exists (psum (fun i => `|f i|) J).
near=>L. rewrite -subr_ge0 -psumIB /psum [X in _ - X]big1=>[i _|].
by apply/normr0P/eqP/P1; case: i=>/= i; rewrite in_fsetD=>/andP[].
by rewrite subr0 sumr_ge0.
Unshelve. end_near.
Qed.

Lemma fin_supp_cvg {I : choiceType} {R : realType} {C : extNumType R} 
  {V : normedModType C} (f : I -> V) (S : {fset I}) :
  (forall i, i \notin S -> f i = 0) -> psum f --> psum f S.
Proof.
move=>Pf; apply: cvg_near_cst; exists S=>// T/= PST.
apply/eqP; rewrite -subr_eq0 -psumIB.
move: PST; rewrite -fsetD_eq0=>/eqP ->; rewrite psum0 subr0 /psum big1//.
by move=>[] i + _; rewrite/= !inE=>/andP[]/Pf->.
Qed.

Lemma fin_supp_is_cvg {I : choiceType} {R : realType} {C : extNumType R}
  {V : normedModType C} (f : I -> V) (S : {fset I}) :
  (forall i, i \notin S -> f i = 0) -> cvg (psum f).
Proof. by move=>/fin_supp_cvg Pc; apply/cvg_ex; exists (psum f S). Qed.

Lemma fin_supp_sum {I : choiceType} {R : realType} {C : extNumType R}
  {V : normedModType C} (f : I -> V) (S : {fset I}) :
  (forall i, i \notin S -> f i = 0) -> sum f = psum f S.
Proof. by move=>/fin_supp_cvg; apply: cvg_lim. Qed.

End FinSupp.

(* move to extnum.v *)
Lemma extNum_archiV {R : realType} {C : extNumType R} (x : C) : 
  0 <= x -> exists k : nat, x < k.+1%:R.
Proof.
rewrite le_eqVlt=>/orP[/eqP<-|xgt0]; first by exists 0%N.
move: {+}xgt0; rewrite -invr_gt0=>/extNum_archi[k]; rewrite ltr_pV2 ?inE//.
3: move=>Pk; by exists k.
all: apply/andP; split=>//; rewrite unitfE//; by apply/lt0r_neq0.
Qed.

Section SummableCountable.
Context {I : choiceType} {R : realType} {C : extNumType R} {V : normedModType C}.
Implicit Type (f : {summable I -> V}).

Lemma summable_bounded f : exists2 M, 0 <= M & forall J,
  (psum \`| f | J <= M)%R.
Proof.
move: (summablefP f)=>[M BM]; exists M=>[|J];
move: BM; rewrite nearE/=/totally/=/filter_from/==>[[ i]] _.
move=>/(_ i)/= P; apply: (le_trans (y := psum (fun i : I => `|f i|) i)).
by apply: sumr_ge0. by apply: P.
move=>/(_ (i `|` J)%fset)/= P.
apply: (le_trans (y := psum (fun i : I => `|f i|) (i `|` J)%fset)).
apply: psum_ler=>//. apply/fsubsetUr. apply/P/fsubsetUl.
Qed.

Lemma summable_countn0 f : countable (suppf f).
Proof.
move: (summable_bounded f)=>[M M_ge0 BM].
pose E (p : nat) := [set x | `|f x| > 1 / p.+1%:~R].
have le: suppf f `<=` \bigcup_(p in setT) E p.
  move=>x; rewrite/suppf/= -normr_gt0=>/extNum_archi[k Pk].
  by rewrite/bigcup/=; exists k=>//; rewrite/E/= div1r.
apply/(sub_countable (subset_card_le le))/bigcup_countable=>// i/= _.
apply/finite_set_countable; apply: contrapT.
rewrite infiniteP /E=>/card_leP/injfunPex/=[g _ /in2TT Pg].
have [N PN]: exists N, M / i.+1%:~R^-1 < N.+1%:R
  by apply/extNum_archiV; rewrite divr_ge0// invr_ge0 ler0n.
pose g' := fun n : 'I_N.+1 => val (g (SigSub (mem_setT (val n)))).
have P1: forall n, 1 / i.+1%:~R < `|f (g' n)|
  by move=>n; apply: (set_valP (g (SigSub (mem_setT (val n))))).
pose J := [fset x in [seq g' i | i : 'I_N.+1]]%fset.
suff Pc: \sum_(i : J) `|f (val i)| > M. 
by move: (lt_le_trans Pc (BM J)); rewrite ltxx.
apply/(@lt_le_trans _ _ (\sum_(x : J) 1 / i.+1%:~R)); last first.
  apply/ler_sum=> /= m _; apply/ltW.
  by have:= fsvalP m; rewrite/J in_fset/==>/mapP/=[j _ ->].
rewrite sumr_const -cardfE card_fseq undup_id.
rewrite map_inj_in_uniq ?fintype.enum_uniq// =>a b _ _.
by rewrite/g'=>/val_inj/Pg/(f_equal val)/=/val_inj.
by rewrite size_map fintype.size_enum_ord div1r -mulr_natr mulrC 
  -ltr_pdivrMr// invr_gt0 ltr0n.
Qed.

End SummableCountable.

Require Import ctopology notation.

Module VDistr.

Section ClassDef.

Variables (I : choiceType) (R : realType) (V : vorderFinNormedModType R[i]).

Structure mixin_of (f : I -> V) := Mixin {
  _  :  forall x, (0 : V) ⊑ f x;
  _  :  `|sum f| <= 1;
}.

Record class_of (f : I -> V) : Prop := Class {base : summable f; mixin : mixin_of f}.
Local Coercion base : class_of >-> summable.

Structure map (phUV : phant (I -> V)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (I -> V)) (f g : I -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

Definition pack (fZ : mixin_of f) :=
  fun (bF : Summable.map phUV) fA & phant_id (Summable.mixin (Summable.class bF)) fA =>
  Pack phUV (Class fA fZ).

Canonical eqType := EqType (map phUV) gen_eqMixin.
Definition choiceType := ChoiceType (map phUV) gen_choiceMixin.
Definition bounded := Bounded.Pack phUV class.
Definition summable := Summable.Pack phUV class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Summable.axiom.
Coercion apply : map >-> Funclass.
Canonical eqType.
Canonical choiceType.
Coercion bounded : map >-> Bounded.map.
Canonical bounded.
Coercion summable : map >-> Summable.map.
Canonical summable.
Notation VDistrMixin := Mixin.
Notation VDistr fA := (@pack _ _ _ _ _ fA _ _ id).
Notation "{ 'vdistr' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'vdistr'  fUV }") : type_scope.
Notation "[ 'vdistr' 'of' f 'as' g ]" := (@clone _ _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'vdistr'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'vdistr' 'of' f ]" := (@clone _ _ _ _ f f _ _ id id)
  (at level 0, format "[ 'vdistr'  'of'  f ]") : form_scope.
(* Coercion eqType : map >-> Equality.type. *)

End Exports.
End VDistr.
Import VDistr.Exports. (* Allows GRing.additive to resolve conflicts. *)

(* Section VOrderFinNormedMod_Lim.
Context {R : realType} {V : vorderFinNormedModType R[i]} {I : choiceType}.
Local Notation C := R[i].

Lemma lim_gev_near_fset (x : V) (u : {fset I} -> V) : 
  cvg u -> (\forall n \near totally, x ⊑ u n) -> x ⊑ lim u.
Proof.
move=> /[swap] /(closed_cvg (fun y=>x ⊑ y))/= P1; apply/P1/closed_gev.
Qed.

Lemma lim_lev_near_fset (x : V) (u : {fset I} -> V) : 
  cvg u -> (\forall n \near totally, u n ⊑ x) -> lim u ⊑ x.
Proof.
move=> /[swap] /(closed_cvg (fun y : V=>y ⊑ x))/= P1;apply/P1/closed_lev.
Qed.

Lemma lev_lim_near_fset (u_ v_ : {fset I} -> V) : cvg u_ -> cvg v_ ->
  (\forall n \near totally, u_ n ⊑ v_ n) -> lim u_ ⊑ lim v_.
Proof.
move=> uv cu cv; rewrite -(subv_ge0) -limB//.
apply: lim_gev_near_fset=>//. apply: is_cvgB=>//.
by apply: filterS cv => k; rewrite (subv_ge0).
Qed.

Lemma lim_gev_fset (x : V) (u : {fset I} -> V) : cvg u -> lbounded_by x u -> x ⊑ lim u.
Proof.
by move=>P1 P2; apply: (lim_gev_near_fset P1); apply: nearW.
Qed.

Lemma lim_lev_fset (x : V) (u : {fset I} -> V) : cvg u -> ubounded_by x u -> lim u ⊑ x.
Proof.
by move=>P1 P2; apply: (lim_lev_near_fset P1); apply: nearW.
Qed.

Lemma lev_lim_fset (u v : {fset I} -> V) : cvg u -> cvg v ->
  (forall n, u n ⊑ v n) -> lim u ⊑ lim v.
Proof.
by move=>P1 P2 P3; apply: (lev_lim_near_fset P1 P2); apply: nearW.
Qed.
End VOrderFinNormedMod_Lim. *)

Section VDistrCoreTh.
Context {I : choiceType} {R : realType} {V : vorderFinNormedModType R[i]}.
Variable (f: {vdistr I -> V}).

Lemma vdistrP (g h : {vdistr I -> V}) : g = h <-> g =1 h.
Proof.
split=>[->//|]; move: g h=>[]g[]/=++[]h[]/=++ /funext eqf;
by rewrite eqf=>B1 S1 B2 S2; do !f_equal; apply: Prop_irrelevance.
Qed.

Lemma vdistr_ge0 : forall x, (0 : V) ⊑ f x.
Proof. by case: f=>?[?[]]. Qed.

Lemma vdistr_sum_le1 : `|sum f| <= 1.
Proof. by case: f=>?[?[]]. Qed.

Lemma vdistr_summable : summable f.
Proof. by case: f=>?[?[]]. Qed.

Lemma psum_vdistr_lev (A B : {fset I}) : (A `<=` B)%fset -> psum f A ⊑ psum f B.
Proof.
by move=>PAB; rewrite -(fsetUD_sub PAB) psumU ?fdisjointXD// 
  levDl sumv_ge0// =>? _; apply: vdistr_ge0.
Qed.

Lemma psum_vdistr_ge0 (A : {fset I}) : (0 : V) ⊑ psum f A.
Proof. rewrite sumv_ge0// =>??; apply: vdistr_ge0. Qed.

Lemma psum_vdistr_lev_sum (A : {fset I}) : psum f A ⊑ sum f.
Proof.
apply/lim_gev_nearF; first by apply: summable_cvg.
by exists A%fset=>// J/= PJ; rewrite psum_vdistr_lev.
Qed.

Lemma vdistr_le_sum : forall x, f x ⊑ sum f.
Proof. move=>x; rewrite -[f x]psum1; apply/psum_vdistr_lev_sum. Qed.

Lemma vdistr_sum_ge0 : (0 : V) ⊑ sum f.
Proof. by apply/(le_trans _ (psum_vdistr_lev_sum fset0)); rewrite psum0. Qed.

End VDistrCoreTh.
#[global] Hint Resolve vdistr_ge0 vdistr_le_sum vdistr_summable : core.

Require Import hermitian.

Notation C := hermitian.C.

Definition Distr (I : choiceType) := nosimpl {vdistr I -> C}.

Section DistrTheory.
Context (I : choiceType) (mu : Distr I).

Lemma ge0_mu : forall x, 0 <= mu x.
Proof. move=>x; rewrite -levcE; apply: vdistr_ge0. Qed.

Lemma sum_le1_mu : sum mu <= 1.
Proof.
apply/(le_trans _ (vdistr_sum_le1 mu))/real_ler_norm.
move: (summable_cvg (f := mu)).
apply: (closed_cvg _ etclosed_real)=>//.
near=>J. apply/ger0_real/sumr_ge0=>i _; apply: ge0_mu.
Unshelve. end_near.
Qed.

Lemma summable_mu : summable mu.
Proof. exact: vdistr_summable. Qed.

Lemma le_psum_mu (A : {fset I}) : psum mu A <= sum mu.
Proof. rewrite -levcE; apply: psum_vdistr_lev_sum. Qed.

Lemma le_sum_mu (x : I) : mu x <= sum mu.
Proof. by apply/(le_trans _ (le_psum_mu [fset x]%fset)); rewrite psum1. Qed.

Lemma le1_mu (x : I) : mu x <= 1.
Proof. apply/(le_trans _ sum_le1_mu)/le_sum_mu. Qed.

Lemma sum_ge0_mu : sum mu >= 0.
Proof.  rewrite -levcE; exact: vdistr_sum_ge0. Qed.

Lemma psum_le1_mu (A : {fset I}) : psum mu A <= 1.
Proof. by apply/(le_trans (le_psum_mu A))/sum_le1_mu. Qed.
(* to be continued *)

End DistrTheory.

Lemma lim_in_closed {R : realType} {C : extNumType R} {V : completeNormedModType C} (A : set V) :
  (forall (f : nat -> V), (forall i, A (f i)) -> cvg f -> A (lim f)) 
    -> closed A.
Proof.
move=>P. 
rewrite /closed closure_limit_point=>x/=[//|/=].
rewrite/limit_point/==>P1.
pose g (i : nat) := ball x (i.+1%:R^-1).
have nbhsg: forall i, nbhs x (g i)
  by move=>i; apply/nbhs_ballP; exists (i.+1%:R^-1)=>//=; apply/divr_gt0.
have Pg: forall i, {gi : V | A gi /\ ball x (i.+1%:R^-1) gi}.
by move=>i; move: (P1 (g i) (nbhsg i))=>/cid [y[]] _ Py gy; exists y.
pose f (i : nat) := projT1 (Pg i).
have Pf : forall i, A (f i) /\ ball x (i.+1%:R^-1) (f i) by move=>i; move: (projT2 (Pg i)).
suff Pc: f --> x. have <-: lim f = x by apply: cvg_lim.
apply: P. by move=>i; move: (Pf i)=>[]. by apply/cvg_ex; exists x.
apply/cvg_ballP=>e egt0.
move: (extNum_archi egt0)=>[k Pk].
exists k=>// n/= Pn. move: (Pf n)=>[] _.
rewrite -ball_normE/==>P2; apply/(lt_trans P2)/(le_lt_trans _ Pk).
by rewrite lef_pV2// ?posrE// ler_nat.
Qed.

Section summable_porder.
Context {I : choiceType} {R : realType} {V : vorderFinNormedModType R[i]}.
Implicit Type (f g h : {summable I -> V}).

Definition les_def f g := asbool (forall i, f i ⊑ g i).
Definition lts_def f g := (g != f) && (les_def f g).

Lemma lts_def_def : forall f g, lts_def f g = (g != f) && (les_def f g).
Proof. by []. Qed.

Lemma les_def_anti : antisymmetric les_def.
Proof.
move=>x y/andP[]/asboolP P1/asboolP P2; apply/summableP=>i.
by apply: le_anti; rewrite P1 P2.
Qed.

Lemma les_def_refl : reflexive les_def.
Proof. by move=>x; apply/asboolP. Qed.  

Lemma les_def_trans : transitive les_def.
Proof.
move=>x y z/asboolP P1/asboolP P2; apply/asboolP=>i.
move: (P1 i) (P2 i); apply: le_trans.
Qed.  

Definition summable_porderMixin := LePOrderMixin 
  lts_def_def les_def_refl les_def_anti les_def_trans.

Canonical summable_porderType := POrderType vorder_display {summable I -> V} summable_porderMixin.

Lemma lesE f g : f ⊑ g = asbool (forall i, f i ⊑ g i).
Proof. by []. Qed.
Lemma lesP f g : f ⊑ g <-> (forall i, f i ⊑ g i).
Proof. by rewrite lesE; split=>/asboolP. Qed.
Lemma lesP1 f g : f ⊑ g -> (forall i, f i ⊑ g i).
Proof. by move=>/lesP. Qed.
Lemma lesP2 f g : (forall i, f i ⊑ g i) -> f ⊑ g.
Proof. by move=>/lesP. Qed.

Lemma les_add2rP h f g : f ⊑ g -> (f + h) ⊑ (g + h).
Proof. by move=>/lesP1 P1; apply/lesP2=>i; rewrite !summableE levD2r. Qed.  

Lemma les_pscale2lP (e : R[i]) f g : 0 < e -> f ⊑ g -> (e *: f) ⊑ (e *: g).
Proof. by move=>Pe /lesP1 P1; apply/lesP2=>i; rewrite !summableE lev_pscale2lP. Qed. 

Import VOrder.Exports.
Definition summable_vorderMixin := VOrderMixin les_add2rP les_pscale2lP.
Canonical summable_vorderType := VOrderType R[i] {summable I -> V} summable_vorderMixin.

Lemma closed_summable_ge f : closed [set g : {summable I -> V} | f ⊑ g ].
Proof.
apply: lim_in_closed=>/=g Pg Pc.
apply/lesP=>i; rewrite -summableE_lim//.
apply: lim_gevF. by apply: summableE_is_cvg.
by move=>j; move: (Pg j)=>/lesP.
Qed.

Lemma closed_summable_le f : closed [set g : {summable I -> V} | g ⊑ f].
Proof.
apply: lim_in_closed=>/=g Pg Pc.
apply/lesP=>i; rewrite -summableE_lim//.
apply: lim_levF. by apply: summableE_is_cvg.
by move=>j; move: (Pg j)=>/lesP.
Qed.

Lemma lim_ges_nearF {T : Type} {F : set (set T)} {FF : ProperFilter F} 
  f (u : T -> {summable I -> V}) :
    cvg (u @ F) -> (\forall n \near F, f ⊑ u n) -> f ⊑ lim (u @ F).
Proof. by move=> /[swap] /(closed_cvg (fun y => f ⊑ y))P; apply/P/closed_summable_ge. Qed.

Lemma lim_les_nearF {T : Type} {F : set (set T)} {FF : ProperFilter F} 
  f (u : T -> {summable I -> V}) :
    cvg (u @ F) -> (\forall n \near F, u n ⊑ f) -> lim (u @ F) ⊑ f.
Proof. by move=> /[swap] /(closed_cvg (fun y => (y : {summable _}) ⊑ f))P; apply/P/closed_summable_le. Qed.

Lemma les_lim_nearF {T : Type} {F : set (set T)} {FF : ProperFilter F} 
  (u v : T -> {summable I -> V}) :
    cvg (u @ F) -> cvg (v @ F) -> 
      (\forall n \near F, u n ⊑ v n) -> lim (u @ F) ⊑ lim (v @ F).
Proof.
move=> cu cv uv; rewrite -(subv_ge0) -limB. apply: cv. apply: cu.
apply/lim_ges_nearF. apply: is_cvgB. apply: cv. apply: cu.
by near=>x; rewrite !fctE subv_ge0; near: x.
Unshelve. end_near.
Qed.

Implicit Type (x y : {vdistr I -> V}).
Definition levd_def x y := (x : {summable _}) ⊑ y.
Definition ltvd_def x y := (y != x) && (levd_def x y).

Lemma levd_def_anti : antisymmetric levd_def.
Proof.
move=>x y/andP[]/asboolP P1/asboolP P2; apply/vdistrP=>i.
by apply: le_anti; rewrite P1 P2.
Qed.

Lemma ltvd_def_def : forall x y, ltvd_def x y = (y != x) && (levd_def x y).
Proof. by []. Qed.

Definition vdistr_porderMixin := LePOrderMixin ltvd_def_def 
  les_def_refl levd_def_anti les_def_trans.
Canonical vdistr_porderType := POrderType vorder_display {vdistr I -> V} vdistr_porderMixin.

Lemma levdEsub (x y : {vdistr I -> V}) : (x ⊑ y) = ((x : {summable _}) ⊑ y).
Proof. by []. Qed.

Lemma levdE x y : x ⊑ y = asbool (forall i, x i ⊑ y i).
Proof. by []. Qed.
Lemma levdP x y : x ⊑ y <-> (forall i, x i ⊑ y i).
Proof. exact: lesP. Qed.
Lemma levdP1 x y : x ⊑ y -> (forall i, x i ⊑ y i).
Proof. by move=>/levdP. Qed.
Lemma levdP2 x y : (forall i, x i ⊑ y i) -> x ⊑ y.
Proof. by move=>/levdP. Qed.

End summable_porder.

Lemma psum_abs_ge0E (I : choiceType) (R : numFieldType) (x : I -> R) :
  (forall i, x i >= 0) -> psum \`| x | = psum x.
Proof. by move=>P; apply/funext=>S; rewrite /psum; apply eq_bigr=>i _; rewrite ger0_norm. Qed. 

(* cpo : deal with while loop *)
Section vdistr_lim.
Context {I : choiceType} {R : realType} {V : vorderFinNormedModType R[i]}.
Local Notation C := R[i].

Lemma vdistr_zero_subproof1 : forall i, (0 : V) ⊑ (\0 : I -> V) i.
Proof. by []. Qed.
Lemma vdistr_zero_subproof2 : `|sum (\0 : I -> V)| <= 1.
Proof.
rewrite/sum; have ->: psum (\0 : I -> V) = fun=>0 by apply/funext=>i; rewrite/psum big1.
by rewrite lim_cst// normr0.
Qed.
Canonical vdistr_zero := VDistr 
  (VDistrMixin vdistr_zero_subproof1 vdistr_zero_subproof2).

Lemma vdistr_lim_subproof1 (T : Type) (F : set (set T)) {FF : ProperFilter F} (f : T -> {vdistr I -> V}) :
  cvg ((f : T -> {summable _}) @ F) -> 
    forall i, (0 : V) ⊑ lim ((f : T -> {summable _}) @ F) i.
Proof.
move=>P i; rewrite -summableE_lim//.
move: (summableE_is_cvg (FF := FF) P)=>/(_ i).
apply: (closed_cvg (fun y=>(0 : V) ⊑ y)). apply/closed_gev.
near=>x; apply: vdistr_ge0.
Unshelve. end_near.
Qed.

Lemma vdistr_lim_subproof2 (T : Type) (F : set (set T)) {FF : ProperFilter F} (f : T -> {vdistr I -> V}) :
  cvg ((f : T -> {summable _}) @ F) -> 
    `| sum (lim ((f : T -> {summable _}) @ F)) | <= 1.
Proof.
move=>P.
have <-: lim (`| sum (f i) | @[i --> F]) = `| sum (lim ((f : T -> {summable _}) @ F)) |.
rewrite lim_norm. by apply: summable_sum_is_cvg.
f_equal. by apply: summable_sum_lim.
apply: etlim_leF. apply: is_cvg_norm. by apply: summable_sum_is_cvg.
move=>n. apply: vdistr_sum_le1.
Qed.

Definition vdlim (T : Type) (F : set (set T)) {FF : ProperFilter F} (f : T -> {vdistr I -> V}) : {vdistr I -> V} :=
  match (asboolP (cvg ((f : T -> {summable _}) @ F))) with
  | ReflectT Q1 => VDistr (VDistrMixin (vdistr_lim_subproof1 Q1) (vdistr_lim_subproof2 Q1))
  | ReflectF _ => vdistr_zero
  end.

Lemma vdlimE (T : Type) (F : set (set T)) {FF : ProperFilter F} (f : T -> {vdistr I -> V}) :
  cvg ((f : T -> {summable _}) @ F) -> 
    (@vdlim _ _ FF f : {summable _ }) = lim ((f : T -> {summable _}) @ F).
Proof. by move=>?; rewrite/vdlim; case: asboolP=>[?|//]; apply/summableP. Qed.

Lemma vdlimEE (T : Type) (F : set (set T)) {FF : ProperFilter F} (f : T -> {vdistr I -> V}) :
  cvg ((f : T -> {summable _}) @ F) -> 
    forall i, (@vdlim _ _ FF f) i = lim (f t i @[t --> F]).
Proof.
by move=>P i; move: {+}P=>/vdlimE/summableP/(_ i); rewrite summableE_lim.
Qed.

End vdistr_lim.

Notation "'nondecreasing_fset' f" := ({homo f : n m / (n `<=` m)%fset >-> (n <= m)%O})
  (at level 10).
Notation "'nonincreasing_fset' f" := ({homo f : n m / (n `<=` m)%fset >-> (m <= n)%O})
  (at level 10).

Section fset_R_lemmas.
Variable (R : realType) (I : choiceType).

Lemma nondecreasing_fset_cvg (u_ : {fset I} -> R) :
  nondecreasing_fset u_ -> has_ubound (range u_) ->
  u_ --> sup (range u_).
Proof.
move=> leu u_ub; set M := sup (range u_).
have su_ : has_sup (range u_) by split => //; exists (u_ fset0), fset0.
apply/cvgrPdist_le => _/posnumP[e].
have [p /andP[Mu_p u_pM]] : exists p, M - e%:num <= u_ p <= M.
  have [_ -[p _] <- /ltW Mu_p] := sup_adherent (gt0 e) su_.
  by exists p; rewrite Mu_p; have /ubP := sup_upper_bound su_; apply; exists p.
near=> n; have pn : (p `<=` n)%fset by near: n; exists p.
rewrite ler_distlC (le_trans Mu_p (leu _ _ _))//= (@le_trans _ _ M) ?lerDl//.
by have /ubP := sup_upper_bound su_; apply; exists n.
Unshelve. all: by end_near.
Qed.

Lemma nondecreasing_fset_is_cvg (u_ : {fset I} -> R) :
  nondecreasing_fset u_ -> has_ubound (range u_) -> cvg u_.
Proof. by move=> u_nd u_ub; apply: cvgP; apply: nondecreasing_fset_cvg. Qed.
End fset_R_lemmas.

Lemma cvg_limE (R: numFieldType) (V: completeNormedModType R) (T : Type) 
  (F : set (set T)) {FF : ProperFilter F} (f: T -> V) (a: V) : 
    hausdorff_space V -> f @ F --> a <-> lim (f @ F) = a /\ cvg (f @ F).
Proof. 
split=>[P1|[ <-]//]. split. apply/cvg_lim. apply H.
apply P1. by move: P1=>/cvgP.
Qed.

Section ExtNumMonoFSet.
Variable (R: realType) (C: extNumType R) (I : choiceType).
(* monotone sequence; can extend to any lattice *)
(* once eventually filter applies to lattice *)
Definition etfset_shift (u_ : {fset I} -> C) := u_ - (fun=>u_ fset0).
Definition etfset_real (u_ : {fset I} -> C) := forall i, (u_ i) \is Num.real.

Lemma etfset_shiftE (u_ : {fset I} -> C) : etfset_shift u_ = u_ - (fun=>u_ fset0).
Proof. by []. Qed.
Lemma etfset_shiftEV (u_ : {fset I} -> C) : u_ = etfset_shift u_ + (fun=>u_ fset0).
Proof. by rewrite etfset_shiftE addrNK. Qed.

Lemma etnondecreasing_fset_shift (u_ : {fset I} -> C) : 
  nondecreasing_fset u_ <-> nondecreasing_fset (etfset_shift u_).
Proof. by split=>H i j /H; rewrite lerD2r. Qed.

Lemma etnondecreasing_fset_shift_real (u_ : {fset I} -> C) : 
  nondecreasing_fset u_ -> etfset_real (etfset_shift u_).
Proof. by move=>H i; rewrite ger0_real// subr_ge0 H. Qed.

Lemma etfset_shift_cvg (u_ : {fset I} -> C) a:
  (etfset_shift u_ --> a) -> u_ --> a + u_ fset0.
Proof.
move=>P1; rewrite [u_]etfset_shiftEV.
by apply: cvgD=>//; rewrite /etfset_shift !fctE addrNK; apply: cvg_cst.
Qed.

Lemma etfset_shift_is_cvgE (u_ : {fset I} -> C) : cvg (etfset_shift u_) = cvg u_.
Proof. by rewrite /etfset_shift; apply/is_cvgDlE; apply: is_cvgN; apply: is_cvg_cst. Qed.

Lemma etfset_shift_lim (u_ : {fset I} -> C) :
  cvg u_ -> lim u_ = lim (etfset_shift u_) + u_ fset0.
Proof. by rewrite -etfset_shift_is_cvgE=>/etfset_shift_cvg; rewrite cvg_limE=>[|[]]. Qed.

Lemma etlim_fset_real (u_ : {fset I} -> C) : etfset_real u_ ->
  cvg u_ -> lim u_ \is Num.real.
Proof. by move=>P; apply: (closed_cvg _ etclosed_real)=>//; exists fset0=>/=. Qed.

Lemma c2r_fset_cvg_real (u_ : {fset I} -> C) (x : R) : etfset_real u_ ->
  ((c2r \o u_) --> x) -> (u_ --> r2c x).
Proof.
move=>ru cu; have ->: u_ = r2c \o (c2r \o u_) 
  by apply/funext=>i; rewrite !fctE c2rK//.
apply: etcvg_mapV=>//; apply r2c_continuous.
Qed.

Lemma c2r_fset_cvg_realV (u_ : {fset I} -> C) a : 
  u_ --> a -> (c2r \o u_) --> c2r a.
Proof. by move=>cu; apply: etcvg_map=>//; apply: c2r_continuous. Qed.

Lemma etnondecreasing_fset_cvg (u_ : {fset I} -> C) (M : C) :
      nondecreasing_fset u_ -> (forall n, u_ n <= M) -> 
        u_ --> r2c (lim (c2r \o (etfset_shift u_))) + u_ fset0.
Proof.
move=>nd ub; move: {+}nd {+}nd=>/etnondecreasing_fset_shift P1/etnondecreasing_fset_shift_real P2.
pose v i := c2r ((etfset_shift u_) i).
have cv: cvg v. apply: nondecreasing_fset_is_cvg.
by move=>n m Pnm; rewrite /v -(@ler_r2c _ C) !c2rK// P1.
exists (c2r (M - u_ fset0))=>i [x] _ <-. rewrite -(@ler_r2c _ C) /v !c2rK//.
by rewrite ger0_real// subr_ge0. by rewrite lerD2r.
have Pu: u_ = (r2c \o v) + (fun=>u_ fset0).
by apply/funext=>i; rewrite !fctE /v c2rK// addrNK.
rewrite {1 2}Pu; apply: cvgD; last by apply: cvg_cst.
apply: etcvg_mapV. apply: r2c_continuous. apply: cv.
Qed.

Lemma etnondecreasing_fset_is_cvg (u_ : {fset I} -> C) (M : C) :
       nondecreasing_fset u_ -> (forall n, u_ n <= M) -> cvg u_.
Proof.
move=>nd ub. apply/cvg_ex; exists (r2c (lim (c2r \o (etfset_shift u_))) + u_ fset0).
apply: (etnondecreasing_fset_cvg nd ub).
Qed.

Lemma etnondecreasing_fset_cvg_le (u_ : {fset I} -> C) :
       nondecreasing_fset u_ -> cvg u_ -> (forall n, u_ n <= lim u_).
Proof.
move=>nd cu n. move: {+}nd=>/etnondecreasing_fset_shift_real rus.
move: {+}cu; rewrite -etfset_shift_is_cvgE=>cus.
rewrite etfset_shift_lim// -lerBlDr.
suff: etfset_shift u_ n <= lim (etfset_shift u_) by [].
apply: etlim_ge_nearF. by apply: cus.
by exists n=>// m/=/nd; rewrite /etfset_shift !fctE lerD2.
Qed.

Lemma lt_etlim_fset (u : {fset I} -> C) (x : C) : nondecreasing_fset u -> 
  cvg u -> x < lim u -> \forall n \near totally, x <= u n.
Proof.
move=> ndu cu Ml; have [[n Mun]|/forallNP Mu] := pselect (exists n, x <= u n).
  near=> m; suff : u n <= u m by exact: le_trans.
  by near: m; exists n => // p q; apply/ndu.
have Cn n : comparable x (u n) by apply/(comparabler_trans 
  (lt_comparable Ml))/ge_comparable/etnondecreasing_fset_cvg_le.
have {}Mu : forall y, x > u y. move=> y. rewrite comparable_ltNge.
by rewrite comparable_sym. by apply/negP.
have : lim u <= x by apply: etlim_le_nearF=> //; near=> m; apply/ltW/Mu.
by move/(lt_le_trans Ml); rewrite ltxx.
Unshelve. all: by end_near.
Qed.

End ExtNumMonoFSet.

Section nondecreasing_vdistr_cvg.
Context {I : choiceType} {R : realType} {V : vorderFinNormedModType R[i]}.

Variable (mnorm : vnorm V).
Local Notation C := R[i].
Local Notation "`[ x ]" := (mnorm x).
Hypothesis (mnorm_ge0D : forall x y, (0 : V) ⊑ x -> (0 : V) ⊑ y -> `[x + y] = `[x] + `[y]).

Let c1 : C := nosimpl (projT1 (cid2 (normv_lbounded mnorm)))^-1.
Let c2 : C := nosimpl (projT1 (cid2 (normv_ubounded mnorm))).

Let c1_gt0 : 0 < c1.
Proof. by rewrite invr_gt0; move: (projT2 (cid2 (normv_lbounded mnorm)))=>[] + _. Qed.

Let c2_gt0 : 0 < c2.
Proof. by move: (projT2 (cid2 (normv_ubounded mnorm)))=>[]. Qed.

Let mnorm_ge0_sum (J : Type) (r : seq J) (P : pred J) (f : J -> V) :
  (forall j, P j -> (0 : V) ⊑ f j) ->
    `[ \sum_(j <- r | P j) f j ] = \sum_(j <- r | P j) `[f j].
Proof.
move=>H; suff: (0 : V) ⊑ \sum_(j <- r | P j) f j /\ 
  `[ \sum_(j <- r | P j) f j ] = \sum_(j <- r | P j) `[f j] by move=>[].
elim/big_rec2: _; first by rewrite normv0.
by move=>j ? y Pj [] Py <-; split; rewrite ?addv_ge0 ?mnorm_ge0D// H.
Qed.

Let mnorm_ge0_mono (x y : V) : 
  (0 : V) ⊑ x ⊑ y -> `[x] <= `[y].
Proof.
move=>/andP[]x_ge0; rewrite -subv_ge0=> yx_ge0.
by rewrite -[y](addrNK x) mnorm_ge0D// lerDr.
Qed.

Let ubmnorm (x : V) : `|x| <= c1 * `[x].
Proof.
rewrite mulrC ler_pdivlMr 1?mulrC; 
by move: (projT2 (cid2 (normv_lbounded mnorm)))=>[].
Qed.

Let lbmnorm (x : V) : `[x] <= c2 * `|x|.
Proof. by move: (projT2 (cid2 (normv_ubounded mnorm)))=>[]. Qed.

Let mmap (x : {summable I -> V}) (i : I) := `[x i].
Let summable_mmap x : summable (mmap x).
Proof.
move: (summablefP x)=>[/= M PM].
exists (c2 * M). near=>J. have: psum \`| x | J <= M by near: J.
rewrite /mmap psum_abs_ge0E// -(ler_pM2l c2_gt0); apply/le_trans.
rewrite/psum mulr_sumr ler_sum//.
Unshelve. end_near.
Qed.
Local Canonical mmap_summable x := Summable (@summable_mmap x).

Let smnorm (x : {summable I -> V}) := sum (mmap x).
Let smnorm_ge0_mono (x y : {summable I -> V}) : 
  (0 : {summable _}) ⊑ x ⊑ y -> smnorm x <= smnorm y.
Proof.
move=>/andP[/lesP Px /lesP Pyx].
rewrite /smnorm/sum; apply: ler_etlimF; [apply: summable_cvg.. |].
by move=>S; apply/ler_sum=>i _; apply/mnorm_ge0_mono; rewrite Px Pyx.
Qed.
Let smnorm_ge0D (x y : {summable I -> V}) : 
  (0 : {summable _}) ⊑ x -> (0 : {summable _}) ⊑ y -> smnorm (x + y) = smnorm x + smnorm y.
Proof.
move=>/lesP /= Px /lesP /= Py; rewrite/smnorm -summable_sumD/=.
by f_equal; apply/funext=>i; rewrite /mmap/= mnorm_ge0D.
Qed.
Let smnorm_ge0B (x y : {summable I -> V}) : 
  (0 : {summable _}) ⊑ x ⊑ y -> smnorm (y - x) = smnorm y - smnorm x.
Proof.
move=>/andP[]Px; rewrite -subv_ge0=>Py.
by rewrite -[LHS](addrK (smnorm x)) -smnorm_ge0D// addrNK.
Qed.
Let le_smnorm (x : {summable I -> V}) :
`|x| <= c1 * smnorm x.
Proof.
rewrite /Num.Def.normr/=/summable_norm /smnorm/sum.
have <- : lim (fun _ : {fset I} => c1) = c1. by apply: lim_cst.
rewrite -limM. apply: is_cvg_cst. apply: summable_cvg.
apply: ler_etlimF; [apply: summable_cvg| |].
apply: is_cvgMr; apply: summable_cvg.
by move=>S/=; rewrite/psum mulr_sumr ler_sum// /mmap.
Qed.
Let ge_smnorm (x : {summable I -> V}) :
  smnorm x <= c2 * `|x|.
Proof.
rewrite /Num.Def.normr/=/summable_norm /smnorm/sum.
have <- : lim (fun _ : {fset I} => c2) = c2. by apply: lim_cst.
rewrite -limM. apply: is_cvg_cst. apply: summable_cvg.
apply: ler_etlimF; [apply: summable_cvg| |].
apply: is_cvgMr; apply: summable_cvg.
by move=>S/=; rewrite/psum mulr_sumr ler_sum// /mmap.
Qed.

Local Program Canonical smnorm_vnorm := @VNorm.Vnorm _ _ smnorm _ _ _.
Next Obligation.
move=>x y; rewrite /smnorm -summable_sumD/sum.
apply: ler_etlimF; [apply: summable_cvg.. |].
by move=>S; rewrite/psum ler_sum// =>??; rewrite /=/mmap/= lev_normD.
Qed.
Next Obligation.
move=>x Px; apply/eqP; rewrite -normr_eq0; apply/eqP/le_anti/andP; split=>//.
by apply/(le_trans (le_smnorm _)); rewrite Px mulr0.
Qed.
Next Obligation.
move=>c x; rewrite /smnorm/sum.
have <- : lim (fun _ : {fset I} => `|c|) = `|c|. by apply: lim_cst.
rewrite -limM. apply: is_cvg_cst. apply: summable_cvg.
by apply: eq_lim=>S; rewrite/=/psum/mmap mulr_sumr; apply eq_bigr=>??; rewrite normvZ.
Qed.

Lemma vdistr_norm_ubound : exists c, 0 < c /\ forall (f : {vdistr I -> V}),
  `|f : {summable _}| <= c.
Proof.
exists (c1 * c2).
split. by apply/mulr_gt0.
move=>f. apply/(le_trans (le_smnorm _)). rewrite ler_pM2l//.
rewrite/smnorm/sum. apply: etlim_leF.
apply: summable_cvg.
move=>S. rewrite/psum -mnorm_ge0_sum ?psumE=>[??|]. apply: vdistr_ge0.
apply/(le_trans (y := `[sum f])).
by apply/mnorm_ge0_mono/andP; rewrite psum_vdistr_ge0 psum_vdistr_lev_sum.
by apply/(le_trans (lbmnorm _)); rewrite ger_pMr// vdistr_sum_le1.
Qed.

Lemma snondecreasing_norm_is_cvg (f : nat -> {summable I -> V}) (b : C) :
  nondecreasing_seq f -> (forall i, `|f i| <= b) -> cvg f.
Proof.
move=>P1 P2.
pose g := (fun i => f i - f 0%N).
suff Pg: cvg g.
  have ->: f = (fun i => g i + f 0%N) by apply/funext=>i; rewrite/g addrNK.
  apply: is_cvgD. apply: Pg. apply: is_cvg_cst.
pose gn := (fun x => smnorm x) \o g.
have gmono: nondecreasing_seq g by move=>m n Pmn; rewrite/g levD2r P1.
have: cvg gn.
  apply: (cnondecreasing_is_cvgn (M := c2 * b + smnorm (f 0%N)))=>[m n Pmn|n].
  by apply/smnorm_ge0_mono/andP; rewrite levD2r subv_ge0; split=>//; apply/P1.
  rewrite/gn/=/g; apply/(le_trans (lev_normB _ _)); rewrite lerD2r/=.
  apply/(le_trans (ge_smnorm _)); rewrite ler_pM2l//.

move=>/cauchy_cvgP/cauchy_ballP Pgn.
apply/cauchy_cvgP/cauchy_ballP=>e egt0; rewrite near_simpl.
have ecgt0 : 0 < e / c1 by rewrite divr_gt0.
near=>n. 
have: ball (gn n.1) (e / c1) (gn n.2).
  by near: n; move: (Pgn _ ecgt0); rewrite near_simpl.
near: n. apply: nearW=>[[m n]]/=.
wlog le_ij: m n / (n <= m)%N => [th_sym|].
by case: (orP (leq_total m n))=>/th_sym// Pi /ball_sym Pj; apply/ball_sym/Pi.
rewrite /ball/=/gn/= -{1}[g m](addrNK (g n)) smnorm_ge0D ?subv_ge0 ?P1// ?gmono//.
rewrite addrK ger0_norm// ?normv_ge0// ltr_pdivlMr// mulrC.
by apply/le_lt_trans/le_smnorm.
Unshelve. end_near.
Qed.

Let smnorm_ler_abs (x : {summable I -> V}) : `[sum x] <= sum (mmap x).
Proof.
rewrite/sum -lim_normv. apply: summable_cvg.
apply: ler_etlimF. apply: is_cvg_normv. apply: summable_cvg. apply: summable_cvg.
move=>n; rewrite /psum/mmap. apply: normv_sum.
Qed.

Lemma snondecreasing_fset_norm_is_cvg (J : choiceType) (f : {fset J} -> {summable I -> V}) (b : C) :
  nondecreasing_fset f -> (forall i, `|f i| <= b) -> cvg f.
Proof.
move=>P1 P2.
pose g := (fun i => f i - f fset0).
suff Pg: cvg g.
  have ->: f = (fun i => g i + f fset0) by apply/funext=>i; rewrite/g addrNK.
  apply: is_cvgD. apply: Pg. apply: is_cvg_cst.
pose gn := (fun x => smnorm x) \o g.
have gmono: nondecreasing_fset g by move=>m n Pmn; rewrite/g levD2r P1.
have: cvg gn.
  apply: (etnondecreasing_fset_is_cvg (M := c2 * b + smnorm (f fset0)))=>[m n Pmn|n].
  by apply/smnorm_ge0_mono/andP; rewrite levD2r subv_ge0; split=>//; apply/P1.
  rewrite/gn/=/g; apply/(le_trans (lev_normB _ _)); rewrite lerD2r/=.
  apply/(le_trans (ge_smnorm _)); rewrite ler_pM2l//.

move=>/cauchy_cvgP/cauchy_ballP Pgn.
apply/cauchy_cvgP/cauchy_exP=>e egt0.
have ecgt0 : 0 < e / c1 by rewrite divr_gt0.
move: (Pgn _ ecgt0); rewrite near_simpl.
move=>[[x1 x2]]/=[[s1 _ Ps1][s2 _ Ps2]] Px.
pose S := (s1 `|` s2)%fset.
have Ps: forall s, (S `<=` s)%fset -> ball (gn s) (e/c1) (gn S).
  move=>s Ps; apply: (Px (s, S)); split.
  apply/Ps1/(fsubset_trans _ Ps)/fsubsetUl. apply/Ps2/fsubsetUr.

exists (g S); exists S=>// T/= PST; apply/ball_sym.
move: (Ps _ PST); rewrite/ball/=/gn/= -smnorm_ge0B.
  apply/andP; split; last by apply: gmono.
  by move: (gmono fset0 S (fsub0set _)); rewrite /g addrN.  
rewrite ger0_norm ?normv_ge0// ltr_pdivlMr// mulrC; apply/le_lt_trans/le_smnorm.
Qed.

Lemma snondecreasing_is_cvgn (f : nat -> {summable I -> V}) (b : {summable I -> V}) :
  nondecreasing_seq f -> ubounded_by b f -> cvg f.
Proof.
move=>P1 P2; apply: (snondecreasing_norm_is_cvg (b := c1 * (smnorm (b - f 0%N) + smnorm (f 0%N))))=>//.
move=>i. apply/(le_trans (le_smnorm _)). rewrite ler_pM2l// -lerBlDr.
apply/(le_trans (levB_dist _ _))/smnorm_ge0_mono.
by rewrite subv_ge0 levD2r P2 andbT P1.
Qed.

Lemma vdnondecreasing_is_cvgn (f : nat -> {vdistr I -> V}) :
  nondecreasing_seq f -> cvg (f : nat -> {summable I -> V}).
Proof.
move=>P1. apply: (snondecreasing_norm_is_cvg (b := c1 * c2))=>//.
move=>i. apply/(le_trans (le_smnorm _)). rewrite ler_pM2l//.
rewrite/smnorm/mmap/sum. apply: etlim_leF.
by move: (summable_cvg (f := Summable (summable_mmap (f i)))).
move=>S. apply/(le_trans (y := `[sum (f i)])).
rewrite/psum -mnorm_ge0_sum ?psumE=>[??|]. apply: vdistr_ge0.
by apply/mnorm_ge0_mono; rewrite psum_vdistr_lev_sum psum_vdistr_ge0.
by apply/(le_trans (lbmnorm _)); rewrite ger_pMr// vdistr_sum_le1.
Qed.

Lemma vdnondecreasing_cvg_le (f : nat -> {vdistr I -> V}) :
  nondecreasing_seq f -> ubounded_by (vdlim (FF := eventually_filter) f) f.
Proof.
move=>Ph i; move: (vdnondecreasing_is_cvgn Ph)=>Pc; rewrite levdEsub vdlimE//.
apply: lim_ges_nearF=>//. exists i=>// n/=; apply: Ph.
Qed.

End nondecreasing_vdistr_cvg.

Lemma uniform_nbhsT {U : choiceType} {V : uniformType} (f : U -> V) :
  (nbhs (f : {uniform U -> V})) = nbhs (f : fct_topologicalType U V).
Proof.
rewrite eqEsubset; split=> A.
  case/uniform_nbhs => E [entE] /filterS; apply.
  exists [set fh | forall y, E (fh.1 y, fh.2 y)]; first by exists E.
  by move=> ? /=.
case => J [E entE EJ] /filterS; apply; apply/uniform_nbhs; exists E.
by split => // z /= Efz; apply: EJ => t /=; exact: Efz.
Qed.

Lemma uniform_fct_cvg {U : choiceType} {V : uniformType} (f : U -> V) 
  (F : set (set (U -> V))) {FF: Filter F} :
  {uniform, F --> f} <-> F --> f.
Proof. by rewrite /cvg_to /filter_of uniform_nbhsT. Qed.

Lemma ptws_fct_cvg {I : Type} {U : choiceType} {V : uniformType} (f : I -> U -> V) (g : U -> V)
  (F : set (set I)) {FF: ProperFilter F} :
  {ptws, f i @[i --> F] --> g} <-> forall u : U, f i u @[i --> F] --> g u.
Proof.
rewrite cvg_sup; split. 
all: move=>P u; move: (P u); rewrite cvg_image; 
  first by rewrite eqEsubset; split=> v // _; exists (cst v).
all: apply: cvg_trans => W /=; rewrite nbhs_simpl/=/nbhs/=/nbhs/=.
by move=>[x] Px <-; move: Px; apply: filterS=>i/= Pi; exists (f i).

move=>PF; exists [set h | W (h u) ]; first by move: PF; apply: filterS.
by apply/funext=>v/=; rewrite propeqE; split=>[[h] + <-//|PS]; exists (cst v).
Qed.

Section exchange_lim.
Context {R : numFieldType} {V : completeNormedModType R}.

Lemma e2gt0 (e : R) : e > 0 -> e / 2 > 0. 
Proof. by move=>P; apply: divr_gt0=>//; apply: ltr0n. Qed.

Lemma exchange_lim_cvg {I J : choiceType} {F : set (set I)} {G : set (set J)}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) (b : J -> V) (c : I -> V) :
    {uniform, a i @[i --> F] --> b} -> (forall i, (a i j @[j --> G]) --> c i) ->
    cvg (c i @[i --> F]) /\ 
    b j @[j --> G] --> lim (c i @[i --> F]).
Proof.
move=>/uniform_fct_cvg uc ca.
move: (cvg_switch FF FG uc ca)=>[l []P1 P2].
split. by apply/cvg_ex; exists l.
by rewrite (cvg_lim _ P1).
Qed.
(* have Pc: cvg (c i @[i --> F]).
apply/cauchy_cvgP/cauchy_ballP=>e egt0; rewrite near_simpl.
near=>i; rewrite -ball_normE/ball_/=.
move: (ca i.1) (ca i.2)=>/cvgrPdist_lt/(_ _ (e2gt0 (e2gt0 egt0))) Pi
  /cvgrPdist_lt/(_ _ (e2gt0 (e2gt0 egt0))) Pj.
near G => m; apply: (le_lt_trans (ler_distD (a i.1 m) _ _)).
rewrite [e]splitr {2}[e/2]splitr addrA addrC ltrD//; last by near: m.
apply/(le_lt_trans (ler_distD (a i.2 m) _ _))/ltrD;
  last by rewrite -normrN opprB; near: m.
near: m. apply: nearW. clear Pi Pj.
suff: ball (a i.1) (e / 2) (a i.2) by rewrite/ball/=/fct_ball -ball_normE/=.
by near: i; move: uc=>/cvgP/cauchy_cvgP/cauchy_ballP/(_ _ (e2gt0 egt0)); rewrite near_simpl.

split=>//.
apply/cvgrPdist_lt=>e egt0.
move: {+}Pc=>/cvgrPdist_lt/(_ _ (e2gt0 (e2gt0 egt0))) PF.
move: uc=>/cvg_ball/(_ _ (e2gt0 egt0)); rewrite/ball/=/fct_ball/= -ball_normE/==>PF1.
near F => N; move: (ca N)=>/cvgrPdist_lt/(_ _ (e2gt0 (e2gt0 egt0))) PG; near=>m.
have /(_ m) Pm1: forall t : J, `|b t - a N t| < e / 2 by near: N.
apply: (le_lt_trans (ler_distD (a N m) _ _)).
rewrite [e]splitr ltrD//; last by rewrite -normrN opprB.
rewrite [e/2]splitr; apply/(le_lt_trans (ler_distD (c N) _ _))/ltrD.
by near: N. by near: m.
Unshelve. all: end_near.
Qed. *)

Lemma exchange_lim_near2 {I J : choiceType} {F : set (set I)} {G : set (set J)}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) (b : J -> V) (c : I -> V) :
    {uniform, a i @[i --> F] --> b} -> (forall i, (a i j @[j --> G]) --> c i) ->
    forall e, e > 0 -> \forall i \near F & j \near G, `|lim (c i @[i --> F]) - a i j| < e.
Proof.
move=>uc1 ca. move: {+}uc1=>/uniform_fct_cvg uc.
move: (@exchange_lim_cvg _ _ _ _ FF FG _ _ _ uc1 ca)=>[]Pc Pb.
move=>e egt0.
move: uc=>/cvg_ball/(_ _ (e2gt0 egt0)); rewrite/ball/=/fct_ball/= -ball_normE/= -nbhs_nearE /nbhs/==> F1.
move: Pb=>/cvgrPdist_lt/(_ _ (e2gt0 egt0)); rewrite -nbhs_nearE/nbhs/==>F2.
rewrite near2E -nbhs_nearE!/nbhs/=/filter_prod/=/filter_from/=.
exists ((fun x : I => forall t : J, `|b t - a x t| < e / 2), 
  (fun t : J => is_true (`|lim (c i @[i --> F]) - b t| < e / 2)))=>/=.
by rewrite/nbhs/=; split.
move=>[i j]/=[]/(_ j) P1 P2.
by rewrite [e]splitr; apply/(le_lt_trans (ler_distD (b j) _ _))/ltrD.
Qed.

Lemma exchange_liml {I J : choiceType} {F : set (set I)} {G : set (set J)}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) (c : I -> V) :
    (forall i, (a i j @[j --> G]) --> c i) ->
    lim ((lim (a i j @[j --> G])) @[i --> F]) = lim (c i @[i --> F]).
Proof.
move=>ca; suff ->: (fun i => lim (a i j @[j --> G])) = c by [].
by apply/funext=>i; move: (ca i); apply/cvg_lim.
Qed.

Lemma exchange_limr {I J : choiceType} {F : set (set I)} {G : set (set J)}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) (c : I -> V) :
    cvg (a i @[i --> F]) -> (forall i, (a i j @[j --> G]) --> c i) ->
    lim ((lim (a i j @[i --> F])) @[j --> G]) = lim (c i @[i --> F]).
Proof.
move=>uc ca; move: {+}uc=>/uniform_fct_cvg uc1.
move: (@exchange_lim_cvg _ _ _ _ FF FG _ _ _ uc1 ca)=>[]Pc Pb.
suff ->: (fun j => lim (a i j @[i --> F])) = lim (a i @[i --> F]) by move: Pb=>/cvg_lim ->.
apply/funext=>j; apply: cvg_lim=>//.
by move: uc=>/uniform_fct_cvg/pointwise_uniform_cvg/ptws_fct_cvg.
Unshelve. all: end_near.
Qed.

Lemma exchange_lim {I J : choiceType} {F : set (set I)} {G : set (set J)}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) :
  cvg (a i @[i --> F]) -> (forall i, cvg (a i j @[j --> G])) ->
    lim ((lim (a i j @[j --> G])) @[i --> F]) = 
    lim ((lim (a i j @[i --> F])) @[j --> G]).
Proof. by move=>uc ca; rewrite (exchange_limr uc ca); apply: exchange_liml. Qed.

Lemma fct_diag_cvg {I : choiceType} {F : set (set I)}
  {FF : ProperFilter F} (a : I -> I -> V) (c : I -> V) :
  cvg (a i @[i --> F]) -> (forall i, (a i j @[j --> F]) --> c i) ->
    (a i i @[i --> F]) --> lim (c i @[i --> F]).
Proof.
move=>/uniform_fct_cvg uc ca.
apply/cvgrPdist_lt=>e egt0; move: (@exchange_lim_near2 _ _ _ _ FF FF _ _ _ uc ca _ egt0).
rewrite -nbhs_nearE near2E -nbhs_nearE!/nbhs/=/filter_prod/=/filter_from/=.
move=>[[i1 i2]]/=[] F1 F2 PF; move: (@filterI _ _ FF _ _ F1 F2).
by apply: filterS=>i; move: (PF (i,i))=>/=.
Qed.

Lemma fct_diag_lim {I : choiceType} {F : set (set I)}
  {FF : ProperFilter F} (a : I -> I -> V) (c : I -> V) :
  cvg (a i @[i --> F]) -> (forall i, (a i j @[j --> F]) --> c i) ->
    lim (a i i @[i --> F]) = lim (c i @[i --> F]).
Proof. by move=>uc ca; apply: cvg_lim=>//; apply: (fct_diag_cvg uc ca). Qed.

Lemma fct_diag_liml {I : choiceType} {F : set (set I)}
  {FF : ProperFilter F} (a : I -> I -> V) :
  cvg (a i @[i --> F]) -> (forall i, cvg (a i j @[j --> F])) ->
    lim ((lim (a i j @[j --> F])) @[i --> F]) = lim (a i i @[i --> F]).
Proof. by move=>uc ca; rewrite (fct_diag_lim uc ca) (exchange_liml ca). Qed.

Lemma fct_diag_limr {I : choiceType} {F : set (set I)}
  {FF : ProperFilter F} (a : I -> I -> V) :
  cvg (a i @[i --> F]) -> (forall i, cvg (a i j @[j --> F])) ->
    lim ((lim (a i j @[i --> F])) @[j --> F]) = lim (a i i @[i --> F]).
Proof. by move=>uc ca; rewrite (fct_diag_lim uc ca) (exchange_limr uc ca). Qed.

Lemma exchange_lim_pair_cvg {I J : choiceType} {F : set (set I)} {G : set (set J)}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) (c : I -> V) :
  cvg (a i @[i --> F]) -> (forall i, (a i j @[j --> G]) --> c i) ->
    (a k.1 k.2 @[k --> (F,G)]) --> lim (c i @[i --> F]).
Proof.
move=>/uniform_fct_cvg uc ca; apply/cvgrPdist_lt=>e egt0/=.
apply: (@exchange_lim_near2 _ _ _ _ FF FG _ _ _ uc ca _ egt0).
Qed.

Lemma exchange_lim_pair_is_cvg {I J : choiceType} {F : set (set I)} {G : set (set J)}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) :
  cvg (a i @[i --> F]) -> (forall i, cvg (a i j @[j --> G])) ->
    cvg (a k.1 k.2 @[k --> (F,G)]).
Proof.
move=>uc; move=>/(exchange_lim_pair_cvg uc) P; apply/cvg_ex; 
by exists (lim (lim (a i j @[j --> G]) @[i --> F])). 
Qed.

Lemma exchange_lim_pair_lim {I J : choiceType} {F : set (set I)} {G : set (set J)}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) (c : I -> V) :
  cvg (a i @[i --> F]) -> (forall i, (a i j @[j --> G]) --> c i) ->
    lim (a k.1 k.2 @[k --> (F,G)]) = lim (c i @[i --> F]).
Proof. by move=>uc; move=>/(exchange_lim_pair_cvg uc)/cvg_lim<-. Qed.

Lemma exchange_liml_pair {I J : choiceType} {F : set (set I)} {G : set (set J)}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) :
  cvg (a i @[i --> F]) -> (forall i, cvg (a i j @[j --> G])) ->
    lim (a k.1 k.2 @[k --> (F,G)]) = lim ((lim (a i j @[j --> G])) @[i --> F]).
Proof. move=>uc ca; rewrite (exchange_liml ca); exact: exchange_lim_pair_lim. Qed.

Lemma exchange_limr_pair {I J : choiceType} {F : set (set I)} {G : set (set J)}
  {FF : ProperFilter F} {FG : ProperFilter G} (a : I -> J -> V) :
  cvg (a i @[i --> F]) -> (forall i, cvg (a i j @[j --> G])) ->
    lim (a k.1 k.2 @[k --> (F,G)]) = lim ((lim (a i j @[i --> F])) @[j --> G]).
Proof. move=>uc ca; rewrite (exchange_limr uc ca); exact: exchange_lim_pair_lim. Qed.

End exchange_lim.

(* extend to extNumType *)
Section ExchangeSum.
Variable (R0 : realType).
Implicit Type (R : completeNormedModType R0).
Local Notation "\`| f |" := (fun x => `|f x|) (at level 2).

Definition series2 R (f : nat -> nat -> R) (m n : nat) :  R :=
  series (fun i => series (f i) n) m.
    (* \sum_(0 <= i < m)\sum_(0 <= j < n) f i j. *)

Lemma foo2 R (f : nat -> R) : 
    (exists M, forall N, \sum_(0 <= i < N) `|f i| <= M) -> cvg (series f).
Proof.
move=>[]M PM; suff: cvg (series \`|f|) by exact: normed_cvg.
apply: nondecreasing_is_cvgn.
by move=>m n Pm; rewrite -subr_ge0 sub_series_geq// sumr_ge0//.
exists M=>?/=[]N _<-; apply: PM.
Qed.

Lemma foo3 R (f : nat -> nat -> R) :
    (exists M, forall N1 N2, \sum_(0 <= i < N1)\sum_(0 <= j < N2) `|f i j| <= M) ->
        (forall i, cvg (series (f i))) /\ cvg (series (fun i => lim (series (f i)))).
Proof.
move=>[]M PM.
have P2: forall i, cvg (series (f i)).
    move=>i; apply: foo2; exists M=>N.
    move: (PM (i.+1) N); apply: le_trans.
    by rewrite big_nat_recr/= ?leq0n// lerDr sumr_ge0// =>? _; apply/sumr_ge0.

have Pc: cvg (series (fun i => lim (series (f i)))).
apply/foo2; exists M=>N.
rewrite (eq_bigr (fun i => lim \`|series (f i)|)); last first.
rewrite -lim_sum_apply; last first. apply: limr_le; last first.
near=>N2; apply/(le_trans _ (PM N N2))/ler_sum=>??; apply: ler_norm_sum.
apply: is_cvg_sum_apply. 1,2: move=>??; apply: is_cvg_norm; apply: P2.
move=>??; symmetry; apply: lim_norm; apply: P2.

by split.
Unshelve. end_near.
Qed.

Lemma foo4 R (f : nat -> nat -> R) :
  (exists M, forall N1 N2, \sum_(0 <= i < N1)\sum_(0 <= j < N2) `|f i j| <= M) ->
    cvg (series2 f : nat -> [completeType of nat -> R]) /\
    (forall i, cvg (series2 f i)).
Proof.
move=>P1. move: (foo3 P1)=>[]P2 _.

have Pa: exists M, forall N1 N2, 
    \sum_(0 <= i < N1)\sum_(0 <= j < N2) `|(fun i j => `|f i j|) i j| <= M.
by move: P1=>[]M PM; exists M=>N1 N2; under eq_bigr do under eq_bigr do rewrite normr_id.
move: (foo3 Pa)=>[] P3 P4.

split; last by move=>i; apply: is_cvg_sum_apply=>j _; apply: P2.

apply/cauchy_cvgP/cauchy_ballP=>e egt0; rewrite near_simpl.
move: P4=>/cauchy_cvgP/cauchy_ballP/(_ _ egt0); rewrite near_simpl.
move=>[][]/=a b[][N1] _ PN1[]N2 _ PN2 PN.
exists ([set n | (max N1 N2 <= n)%N] , [set n | (max N1 N2 <= n)%N])=>//=.
split; by exists (max N1 N2).
move=>[m n]/=[].
wlog le_ij: m n / (n <= m)%N => [th_sym|].
case: (orP (leq_total m n))=>/th_sym// + Pi Pj; move=>/(_ Pj Pi); apply: ball_sym.

move=>Pm Pn; rewrite/ball/=/fct_ball=>k; rewrite -ball_normE/= /series2 sub_series le_ij.
have Pab: a m /\ b n by move: Pm Pn; rewrite !geq_max=>/andP[]/PN1+ _ /andP[] _ /PN2.
move: (PN (m, n))=>/(_ Pab)/=; rewrite -ball_normE/= sub_series le_ij.
apply/le_lt_trans/(le_trans (ler_norm_sum _ _ _)); rewrite ger0_norm. 
by apply: sumr_ge0=>??; apply: etlim_ge=>[|?]; [apply: P3| apply: sumr_ge0].
apply: ler_sum=>??. apply: etlim_ge_near. apply: P3.
exists k=>// l/= Pk; apply/(le_trans (ler_norm_sum _ _ _)).
by rewrite -subr_ge0 sub_series Pk sumr_ge0.
Qed.

Lemma series2_liml R (f : nat -> nat -> R) :
    (exists M, forall N1 N2, \sum_(0 <= i < N1)\sum_(0 <= j < N2) `|f i j| <= M)
        -> lim (series (fun i => lim (series (f i)))) = lim (fun i => series2 f i i).
Proof.
move=>P; move: {+}P=>/foo4[] P1 P2.
rewrite -[RHS](fct_diag_liml P1 P2).
apply: eq_lim=>i.
rewrite/series/= -lim_sum_apply// =>j _.
by move: P=>/foo3[]/(_ j) + _.
Qed.

Lemma series2_limr R (f : nat -> nat -> R) :
    (exists M, forall N1 N2, \sum_(0 <= i < N1)\sum_(0 <= j < N2) `|f i j| <= M)
        -> lim (series (fun j => lim (series (f ^~ j)))) = lim (fun i => series2 f i i).
Proof.
move=>P; move: {+}P=>/foo4[] P1 P2.
rewrite -[RHS](fct_diag_limr P1 P2).
apply: eq_lim=>i.
under [RHS]eq_lim do rewrite /series/= exchange_big.
rewrite/series/= -lim_sum_apply// =>j _.
have: exists M : R0, forall N2 N1 : nat, \sum_(0 <= j < N2) \sum_(0 <= i < N1) `|f i j| <= M.
by move: P=>[M PM]; exists M=>N2 N1; move: (PM N1 N2); rewrite exchange_big.
by move=>/foo3[]/(_ j) + _.
Qed.

Lemma series_exchange_lim R (f : nat -> nat -> R) :
  (exists M, forall N1 N2, \sum_(0 <= i < N1)\sum_(0 <= j < N2) `|f i j| <= M) ->
  lim (series (fun i => lim (series (f i)))) = lim (series (fun i => lim (series (f ^~ i)))).
Proof. by move=>P; rewrite series2_liml// series2_limr. Qed.

End ExchangeSum.

Lemma normrB_close_eq (R : numDomainType) (V : normedZmodType R) (u v : V) :
  (forall e, e > 0 -> `| u - v | < e) -> u = v.
Proof.
move=>P. apply/eqP; case E: (u != v); last by move: E=>/eqP->.
move: E=>/eqP/eqP; rewrite -subr_eq0 - normr_gt0=>/(P _).
rewrite lt_def eqxx//.
Qed.

Section ExchangePsum.
Context {R : realType} {C : extNumType R}.
Implicit Type (I J : choiceType) (V : completeNormedModType C).

Let pseries I J V (f : I -> J -> V) Si Sj :=
  psum (fun i : I => psum (fun j : J => f i j) Sj) Si.

Lemma psum_ubounded_summable I V (f : I -> V) : 
  (exists M, forall S, psum \`|f| S <= M) -> summable f.
Proof. by move=>[M PM]; exists M; apply: nearW. Qed.

Lemma pseries_ubounded_cvg (I J : choiceType) (V : completeNormedModType C) 
  (f : I -> J -> V) :
  (exists M, forall Si Sj, pseries (fun i j => `|f i j|) Si Sj <= M) ->
    (forall i, summable (f i)) /\ (forall i, cvg (psum (f i))) /\
    (summable (fun i : I => sum (f i))) /\ (cvg (psum (fun i => sum (f i))))
    /\ cvg (psum (fun x : I => `|sum (f x)|)).
Proof.
move=>[Mu Pu].
have H0: (forall i, summable (f i)).
  by move=>i; exists Mu; near=>Sj; move: (Pu [fset i]%fset Sj); rewrite /pseries psum1.
have H1: (forall i, cvg (psum (f i))) by move=>i; apply: norm_bounded_cvg; apply: H0.
have H2: summable (fun i : I => sum (f i)).
  exists Mu; near=>Si; rewrite/psum.
  rewrite (eq_bigr (fun i : Si => lim (`|psum (f (val i)) x| @[x --> totally]%classic))).
  move=>i _; symmetry; apply: lim_norm. apply: H1.
  rewrite -lim_sum_apply; last apply: etlim_leF; last first.
  move=>Sj; apply/(le_trans _ (Pu Si Sj))/ler_sum=>??; apply: ler_norm_sum.
  apply: is_cvg_sum_apply. 1,2: move=>??; apply: is_cvg_norm; apply: H1.
do !split. apply: H0. apply: H1. apply: H2.
apply: norm_bounded_cvg; apply: H2.
by move: (summable_norm_is_cvg (f := Summable H2))=>/=.
Unshelve. all: end_near.
Qed.

Lemma pseries_uniform_cvg I J V (f : I -> J -> V) :
  (exists M, forall Si Sj, pseries (fun i j => `|f i j|) Si Sj <= M) ->
    cvg (pseries f : {fset I} -> [completeType of {fset J} -> V]) /\
    (forall Si, cvg (pseries f Si)).
Proof.
move=>P1; move: (pseries_ubounded_cvg P1)=>[] _ [] P2 _.
have P1': exists M, forall Si Sj, pseries (fun i : I => \`| (fun i j => `|f i j|) i |) Si Sj <= M.
  move: P1=>[]M PM; exists M=>Si Sj; move: (PM Si Sj); rewrite/pseries/psum; 
  by under [in X in _ -> X]eq_bigr do under eq_bigr do rewrite normr_id.
move: (pseries_ubounded_cvg P1')=>[] _ [] P3 [] _ [] P4 _.

split; last by move=>i; apply: is_cvg_sum_apply=>j _; apply: P2.

apply/cauchy_cvgP/cauchy_ballP=>e egt0; rewrite near_simpl.
move: P4=>/cauchy_cvgP/cauchy_ballP/(_ _ egt0); rewrite near_simpl.
move=>[][]/=a b[][Si1] _ PSi1[]Si2 _ PSi2 PSi.
exists ([set S1 | (Si1 `|` Si2 `<=` S1)%fset] , [set S2 | (Si1 `|` Si2 `<=` S2)%fset])=>//=.
split; by exists (Si1 `|` Si2)%fset.
move=>[S1 S2]/=[] PS1 PS2.
rewrite/ball/=/fct_ball=>Sj; rewrite -ball_normE/= /pseries -psumIB.
apply: (le_lt_trans (y := psum (fun i : I => psum \`|f i| Sj) ((S1 `|` S2) `\` (S1 `&` S2))%fset)).
rewrite fsetDUl !fsetDIr !fsetDv fset0U fsetU0 psumU ?fdisjointXDg// ?fdisjointDX//.
apply/(le_trans (ler_normB _ _))/lerD; rewrite /psum;
apply/(le_trans (ler_norm_sum _ _ _))/ler_sum=>??; apply/ler_norm_sum.
have Pab: a (S1 `|` S2)%fset /\ b (S1 `&` S2)%fset.
  split; last by apply/PSi2/(fsubset_trans (fsubsetUr Si1 _))/fsubsetIP; split.
  by apply/PSi1/(fsubset_trans _ (fsubsetUl _ _))/(fsubset_trans _ PS1)/fsubsetUl.
move: (PSi (S1 `|` S2, S1 `&` S2)%fset)=>/(_ Pab)/=.
rewrite -ball_normE/= -psumIB -fsetDDl fsetDIl fsetDv fset0I fset0D psum0 subr0.
apply/le_lt_trans. rewrite ger0_norm. 
by apply: sumr_ge0=>??; apply: etlim_geF=>[|?]; [apply: P3| apply: sumr_ge0].
apply: ler_sum=>??. apply: etlim_ge_nearF. apply: P3. 
exists Sj=>// Sj'/=; by apply/psum_ler.
Qed.

Lemma pseries2_exchange_lim I J V (f : I -> J -> V) :
    (exists M, forall Si Sj, pseries (fun i j => `|f i j|) Si Sj <= M) ->
      sum (fun i => sum (f i)) = sum (fun j => sum (f ^~ j)).
Proof.
move=>P. move: {+}P=>/pseries_uniform_cvg[] P1 P2; rewrite/sum.
transitivity (lim (lim (pseries f i j @[j --> totally]) @[i --> totally])).
apply: eq_lim=>Si. rewrite /pseries lim_sum_apply//==>i _.
by move: P=>/pseries_ubounded_cvg[] _ []/(_ (fsval i)) + _.
rewrite (exchange_lim P1 P2).
have Q: exists M : C, forall Sj Si , pseries (fun j : J => \`| f ^~ j |) Sj Si <= M.
  move: P=>[M PM]; exists M=>Sj Si; move: (PM Si Sj); apply: le_trans.
  by rewrite/pseries /psum exchange_big.
transitivity (lim (lim (pseries (fun i j => f j i) j i @[i --> totally]) @[j --> totally])).
by apply: eq_lim=>Sj; apply: eq_lim=>Si; rewrite/pseries/psum exchange_big.
apply: eq_lim=>Sj. rewrite /pseries lim_sum_apply//==>j _.
by move: Q=>/pseries_ubounded_cvg[] _ []/(_ (fsval j)) + _.
Qed.

Lemma pseries2_exchange_lim_pair I J V (f : I -> J -> V) :
    (exists M, forall Si Sj, pseries (fun i j => `|f i j|) Si Sj <= M) ->
      sum (fun k => f k.1 k.2) = sum (fun i => sum (f i)).
Proof.
move=>P. move: {+}P=>/pseries_uniform_cvg[] P1 P2; rewrite/sum.
transitivity (lim (lim (pseries f i j @[j --> totally]) @[i --> totally])); last first.
apply: eq_lim=>Si. rewrite /pseries lim_sum_apply//==>i _.
by move: P=>/pseries_ubounded_cvg[] _ []/(_ (fsval i)) + _.
rewrite -exchange_liml_pair. apply: P1. apply: P2.
have /cvgrPdist_lt Pc1: cvg (pseries f k.1 k.2 @[k --> (totally, totally)]).
apply: exchange_lim_pair_is_cvg. apply: P1. apply: P2.
have /cvgrPdist_lt Pc2: cvg (psum (fun k : prod_choiceType I J => f k.1 k.2)).
apply: norm_bounded_cvg. move: {+}P=>[M PM].
exists M. near=>K.
apply/(le_trans (y := \sum_(i <- (fst @` K)%fset)\sum_(j <- (snd @` K)%fset) 
  `|f i j|)).
rewrite pair_big_dep_cond/= big_seq_fsetE psum_ler//=.
apply/fsubsetP=>[[a b PK]]; rewrite !inE/= !andbT; apply/andP; split;
apply/imfsetP; exists (a,b)=>//.
rewrite big_seq_fsetE; under eq_bigr do rewrite big_seq_fsetE; apply PM.
apply: normrB_close_eq=>e egt0.
move: (Pc1 _ (e2gt0 egt0))=>[[/=SSi SSj[[Si/= _ PSi][Sj/= _ PSj] PS]]].
move: (Pc2 _ (e2gt0 egt0))=>[/=S2 _ PS2].
pose Ti := (Si `|` (fst @` S2))%fset.
pose Tj := (Sj `|` (snd @` S2))%fset.
have /PS/=: (SSi `*` SSj) (Ti, Tj) by split=>/=; [apply/PSi/fsubsetUl|apply/PSj/fsubsetUl].
have /PS2/=: [set B | (S2 `<=` B)%fset] [fset ((i, j) : I * J) | i in Ti, j in Tj]%fset.
by apply/fsubsetP=>i Pi; rewrite !inE; apply/andP; split; apply/orP; right; apply/imfsetP; exists i.
have ->: psum (fun k : I * J => f k.1 k.2) [fset ((i, j) : I * J) | i in Ti, j in Tj]%fset = 
  pseries f Ti Tj.
rewrite/pseries !psum_seq_fsetE; under [in RHS]eq_bigr do rewrite psum_seq_fsetE.
by rewrite pair_big_dep_cond/=; apply: eq_fbigl=>i; rewrite !inE andbT andbT.
rewrite -normrN opprB=>Q1 Q2. rewrite -[lim (psum _)](subrK (pseries f Ti Tj)).
rewrite -[_ + _ - _]addrA [e]splitr.
by apply/(le_lt_trans (ler_normD _ _))/ltrD; rewrite -normrN opprB.
Unshelve. end_near.
Qed.

End ExchangePsum.



(* Lemma test4 (I J : choiceType) (V : completeNormedModType C) 
  (f : I -> J -> V) : (forall i, cvg (psum (f i))) -> (forall j, cvg (psum (f^~j))) ->
  {uniform (fun j => sum (f i) -> } *)

(* Lemma testb (I J : choiceType) (f : I -> J -> C) :
  (forall i j, f i j >= 0) -> forall Si1 Si2 Sj1 Sj2, Si1 `<=` Si2 -> Sj1 `<=` Sj2 ->
  psum (fun i : I => psum (fun j : J => f i j) Sj1) Si1
  <= psum (fun i : I => psum (fun j : J => f i j) Sj2) Si2.
Proof.
intros; rewrite -(fsetUD_sub H1) psumU ?fdisjointXD// -[X in X <= _]addr0 lerD//.
by apply: ler_sum=>/=i _; apply/psum_ler. by apply: sumr_ge0=>/=i _; apply: sumr_ge0.
Qed.

Lemma test1 (I J : choiceType) (V : completeNormedModType C) 
  (f : I -> J -> V) :
  (exists M, forall Si Sj, psum (fun i => psum (fun j => `|f i j|) Sj) Si <= M) 
    -> (forall i, summable (f i)) /\ (forall i, cvg (psum (f i))) /\
    (summable (fun i : I => sum (f i))) /\ (cvg (psum (fun i => sum (f i))))
    /\ cvg (psum (fun x : I => `|sum (f x)|)).
Proof.
move=>[Mu Pu].
have H0: (forall i, summable (f i)).
  move=>i; exists Mu; near=>Sj.
  by move: (Pu [fset i] Sj); rewrite psum1.
have H1: (forall i, cvg (psum (f i))). 
  by move=>i; apply: norm_bounded_cvg; apply: H0.
have H2: summable (fun i : I => sum (f i)).
  exists Mu; near=>Si; rewrite/psum.
  rewrite (eq_bigr (fun i : Si => lim (`|psum (f (val i)) x| @[x --> totally]%classic))).
  move=>i _; symmetry; apply: lim_norm. apply: H1.
  rewrite -lim_sum_apply. move=>i _; apply: is_cvg_norm; apply: H1.
  apply: etlim_le_nearF. 
  apply: (is_cvg_sum_apply (f := fun i t => `|psum (f (val i)) t|))=>/=i _; apply: is_cvg_norm; apply: H1.
  near=>Sj. apply: (le_trans (y := psum (fun i : I => psum (fun j : J => `|f i j|) Sj) Si))=>//.
  rewrite/psum ler_sum//==>i _; apply: ler_norm_sum.
do !split. apply: H0. apply: H1. apply: H2.
apply: norm_bounded_cvg; apply: H2.
by move: (summable_norm_is_cvg (f := Summable H2))=>/=.
Unshelve. all: end_near.
Qed.

Lemma test3 (V : normedModType C) (u v : V) :
  (forall e, e > 0 -> `| u - v | < e) -> u = v.
Proof.
move=>P. apply/eqP; case E: (u != v); last by move: E=>/eqP->.
move: E=>/eqP/eqP; rewrite -subr_eq0 - normr_gt0=>/(P _).
rewrite lt_def eqxx//.
Qed.

Local Notation "\`| f |" := (fun x => `|f x|) (at level 2).

Lemma test7 (I : choiceType) (V : completeNormedModType C) (f : I -> V) :
  summable f -> cvg \`| psum f |.
Proof.
move=>Pf; apply/cauchy_cvgP/cauchy_exP=>e egt0/=.
move: (summable_cvg (f := Summable Pf))=>/=/cvgrPdist_lt/=/(_ _ egt0)=>P.
exists `|(lim (psum f))|. rewrite near_simpl.
near=>J; have: `|sum f - psum f J| < e by near: J.
rewrite/= -ball_normE/=. apply: le_lt_trans. apply: ler_dist_dist.
Unshelve. all: end_near.
Qed.

Lemma test6 (I : choiceType) (V : completeNormedModType C) (f : I -> V) :
  summable f -> `| sum f | <= sum \`|f|.
Proof.
move=>Pf; rewrite /sum -lim_norm; first by apply: norm_bounded_cvg.
rewrite -levcE; apply: lev_lim_near_fset; last first.
by near=>J; rewrite levcE /psum ler_norm_sum.
by move: (summable_norm_is_cvg (f := Summable Pf)).
by apply: test7.
Unshelve. all: end_near.
Qed.

Lemma test8 (I : choiceType) (V : completeNormedModType C) (f : I -> V) (J : {fset I}):
  summable f -> (psum (fun i : I => if i \in J then 0 else f i) --> (sum f - psum f J))%classic.
Proof.
set g := (fun i : I => if i \in J then 0 else f i).
have P1: psum g J = 0 by rewrite/psum big1/g //==>[[?/=->]].
move=>Pf.
apply/cvgrPdist_lt=>/=e egt0.
move: (summable_cvg (f := Summable Pf))=>/=/cvgrPdist_lt/=/(_ _ egt0)=>P.
near=>K. have: `|lim (psum f) - psum f K| < e by near: K.
near: K. exists J=>//= J'/= PJ.
suff ->: psum f J' = psum f J + psum g J' by rewrite opprD addrA.
apply/eqP. rewrite addrC -subr_eq -psumIB -[psum g J']subr0 -P1 -[X in _ == X]psumIB.
move: PJ; rewrite -fsetD_eq0=>/eqP->; rewrite !psum0 !subr0; apply/eqP.
by rewrite/psum; apply: eq_bigr=>/=[[i/=]]; rewrite/g inE=>/andP[]/negPf->.
Unshelve. end_near.
Qed.

Lemma test5 (I : choiceType) (V : completeNormedModType C) (f : I -> V) :
  summable f -> forall J,
  `| sum f - psum f J | <= sum \`|f| - psum \`|f| J.
Proof.
move=>Pf J.
have Pf1: summable \`|f|. move: {+}Pf=>[]/=e Pe; exists e.
near=>K; have: psum \`| f | K <= e by near: K.
by rewrite/psum; under [in X in _ -> X]eq_bigr do rewrite normr_id.
move: (@test8 _ _ _ J Pf)=>/norm_cvg_lim/=<-.
move: (@test8 _ _ _ J Pf1)=>/norm_cvg_lim/=<-.
rewrite -lim_norm.

apply: norm_bounded_cvg; move: {+}Pf=>[e Pe]; exists e.
near=>K; have: psum \`| f | K <= e by near: K.
by apply: le_trans; apply: ler_sum=>i _; case: (val i \in J)=>//; rewrite normr0.

apply: ler_etlim_nearF.
apply: is_cvg_norm. apply: norm_bounded_cvg; move: {+}Pf=>[e Pe]; exists e.
near=>K; have: psum \`| f | K <= e by near: K.
by apply: le_trans; apply: ler_sum=>i _; case: (val i \in J)=>//; rewrite normr0.

apply: norm_bounded_cvg; move: {+}Pf1=>[e Pe]; exists e.
near=>K; have: psum \`|\`| f | | K <= e by near: K.
by apply: le_trans; apply: ler_sum=>i _; case: (val i \in J)=>//; rewrite normr0.

near=>K. apply: (le_trans (ler_norm_sum _ _ _)).
by apply: ler_sum=>i _; case: (val i \in J)=>//; rewrite normr0.
Unshelve. all: end_near.
Qed.

Lemma e2gt0 (e : C) : e > 0 -> e / 2 > 0. 
Proof. by move=>P; apply: divr_gt0=>//; apply: ltr0n. Qed.

Lemma ler_etlim_nearF_add_cst {T : Type}
  {F : set (set T)} {FF : ProperFilter F} (u v : T -> C) (c : C): 
    (cvg (u @ F) -> cvg (v @ F) ->
      (\forall n \near F, u n + c <= v n) -> 
        lim (u @ F) + c <= lim (v @ F))%classic.
Proof.
move=>P1 P2 P3. pose fc := (fun _ : T => c).
have <-: lim (fc @ F)%classic = c. apply/norm_lim_near_cst. by near=>K.
rewrite -limD. apply: P1. apply: is_cvg_cst.
apply: ler_etlim_nearF. apply: is_cvgD. apply: P1. apply: is_cvg_cst.
apply: P2. near=>K. rewrite/fc fctE; near: K. by [].
Unshelve. all: end_near.
Qed.

Lemma test2' (I J : choiceType) (V : completeNormedModType C) 
  (f : I -> J -> V) :
  (exists M : C, forall Si Sj, psum (fun i => psum (fun j => `|f i j|) Sj) Si <= M) 
    -> forall e, e > 0 -> exists Si Sj, forall Si' Sj', 
      Si `<=` Si' -> Sj `<=` Sj' ->
        `|sum (fun i => sum (f i)) - psum (fun i => psum (f i) Sj') Si'| < e.
Proof.
move=>P1; move: (test1 P1)=>[]P2[] _ []P4[] _ P6.
have P1': exists M : C, forall Si Sj, 
  psum (fun i : I => psum \`| \`|f i| | Sj) Si <= M.
  move: P1=>[/=e Pe]. exists e=>Si Sj; move: (Pe Si Sj).
  by apply/le_trans/ler_sum=>??; apply/ler_sum=>??; rewrite normr_id.
move: (test1 P1')=>[] _ []P3'[] _ []P5' _; clear P1 P1'.

have R1: forall Si Sj, sum (fun i : I => sum \`| f i |) >= psum (fun i : I => psum \`| f i | Sj) Si.
move=>Si Sj. apply: etlim_ge_nearF. apply: P5'.
exists Si=>//= Ti/= Pi. rewrite -(fsetUD_sub Pi) psumU ?fdisjointXD// -[X in X <= _]addr0 lerD//.
apply: ler_sum=>j _; apply: etlim_ge_nearF. apply: P3'.
exists Sj=>//= Tj/=. by apply/psum_ler.
apply: sumr_ge0=>??; apply: etlim_ge_nearF. apply: P3'.
by near=>K; apply: sumr_ge0.

(* clear P1 P2 P3 P4 P5 P1' P3' P5' P0 P00 R1 R2. *)
have Qi: forall e : C, e > 0 -> exists Si Sj, 
`|sum (fun i => sum \`|f i |) - psum (fun i : I => psum \`| f i | Sj) Si| < e.
move=>e egt0.
move: {+}P5'=>/cvgrPdist_lt/(_ _ (e2gt0 egt0))[]x/= _/(_ x)/=/(_ (fsubset_refl _)).
rewrite {5}/psum -lim_sum_apply=>[|Q2]; first by move=>/=i _; apply: P3'.
have: cvg (\sum_(i : x) psum \`| f (val i) | t @[t --> totally])%classic.
  by apply: is_cvg_sum_apply=>/=i _; apply: P3'.
move=>/cvgrPdist_lt/(_ _ (e2gt0 egt0))[y]/= _/(_ y)/=/(_ (fsubset_refl _))=>Q3.
exists x. exists y.
apply: (le_lt_trans (ler_distD (lim (\sum_(i : x) psum \`| f (fsval i) | t @[t --> totally])%classic) _ _)).
rewrite [e]splitr ltrD//.

move=>/= e egt0; move: (Qi _ egt0)=>[Si[Sj Pi]].
exists Si; exists Sj=>Si' Sj' PSi PSj.

suff R4: `|sum (fun i : I => sum (f i)) - psum (fun i : I => psum (f i) Sj') Si'| 
  <= `|sum (fun i : I => sum (\`|f i|)) - psum (fun i : I => psum \`|f i| Sj') Si'|.
apply: (le_lt_trans R4).
apply: (le_lt_trans _ Pi). rewrite !ger0_norm ?subr_ge0//.
by rewrite lerD2l lerN2; apply: testb.

apply: (le_trans (ler_distD (psum (fun i : I => sum (f i)) Si') _ _)).
have R3: `|sum (fun i : I => sum (f i)) - psum (fun i : I => sum (f i)) Si'| 
  <= sum (fun i : I => sum \`| f i |) - psum (fun i : I => sum \`| f i |) Si'.
move:{+}P4=>/test5/(_ Si')=>R3. apply: (le_trans R3).
rewrite -lerN2 !opprB lerBlDl addrC -addrA -lerBlDl [X in _ <= X]addrC lerBrDr.
rewrite addrC. apply: ler_etlim_nearF_add_cst.
apply: P6. apply: P5'.
exists Si'=>// K/= PK.
rewrite addrCA addrC -lerBrDr -psumIB -[X in _ <= X]psumIB.
move: PK; rewrite -fsetD_eq0=>/eqP->; rewrite !psum0 !subr0.
apply: ler_sum=>i _. apply/test6/P2.

have R4: `|psum (fun i : I => sum (f i)) Si' - psum (fun i : I => psum (f i) Sj') Si'| <= 
  psum (fun i : I => sum \`|f i| - psum \`|f i| Sj') Si'.
rewrite{1 2 4}/psum raddf_sum/= -big_split/=.
apply: (le_trans (ler_norm_sum _ _ _)).
apply: ler_sum=>i _. apply/test5/P2.

apply: (le_trans (lerD R3 R4)).
rewrite/psum raddf_sum/= -addrA -big_split/=.
under eq_bigr do rewrite addrA addNr add0r.
rewrite -raddf_sum/= real_ler_norm//. apply: ger0_real.
rewrite subr_ge0. apply: R1.
Unshelve. all: end_near.
Qed.

Lemma testc (I J : choiceType) (V : zmodType) (h : I -> J -> V) Si Sj :
  psum (fun i : I => psum (h i) Sj) Si =
    psum (fun j : J => psum (h ^~ j) Si) Sj.
Proof. by intros; rewrite /psum exchange_big. Qed.

Lemma test2 (I J : choiceType) (V : completeNormedModType C) 
  (f : I -> J -> V) :
  (exists M : C, forall Si Sj, psum (fun i => psum (fun j => `|f i j|) Sj) Si <= M) ->
      sum (fun i => sum (f i)) = sum (fun j => sum (f ^~ j)).
Proof.
move=>P1.
have P2: exists M : C, forall Sj Si, psum (fun j : J => psum \`| f ^~ j | Si) Sj <= M.
by move: P1=>[e Pe]; exists e=>Sj Si; move: (Pe Si Sj); apply: le_trans; rewrite testc.
move: (test2' P1) (test2' P2)=>Qi Qj.
apply: test3=>/= e egt0.
move: (Qi _ (e2gt0 egt0)) (Qj _ (e2gt0 egt0))=>[Si1[Sj1 Pi]][Sj2[Si2 Pj]].
pose Si := Si1 `|` Si2; pose Sj := Sj1 `|` Sj2.
move: (ltrD (Pi Si Sj (fsubsetUl _ _) (fsubsetUl _ _)) (Pj Sj Si (fsubsetUr _ _) (fsubsetUr _ _))).
rewrite -splitr; apply: le_lt_trans.
apply: (le_trans (ler_distD (psum (fun i : I => psum (f i) Sj) Si) _ _)).
by rewrite lerD2l - normrN opprB testc.
Qed. *)