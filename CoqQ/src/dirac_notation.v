(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From quantum.external Require Import forms.
From mathcomp.analysis Require Import reals.
From mathcomp.real_closed Require Import complex.
Require Import mcextra mcaextra notation hermitian quantum inhabited.

Import Order.TTheory GRing.Theory Num.Theory Num.Def.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Notation C := hermitian.C.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section DiracTRS_SOUND.
Variable (name : eqType).

Definition BType := Set.
Variable (eval_BT : BType -> ihbFinType).

Inductive DType :=
    | DBType (t : BType)
    | DPair (t1 : DType) (t2 : DType).

Fixpoint eval_DType (t : DType) : ihbFinType :=
    match t with
    | DBType t => eval_BT t
    | DPair t1 t2 => prod_ihbFinType (eval_DType t1) (eval_DType t2)
    end.

Notation "''Ht' T" := (ihb_chsType (eval_DType T)) (at level 8, T at level 2, format "''Ht'  T").
Notation "''Hom{' T1 , T2 }" := ('Hom('Ht T1, 'Ht T2)) (at level 8, format "''Hom{' T1 ,  T2 }").
Notation "''End{' T }" := ('End('Ht T)) (at level 8, format "''End{' T }").

Inductive C_cplx :=
    | C_0
    | C_1
    | C_conj (s : C_cplx)
    | C_add (s1 s2 : C_cplx)
    | C_opp (s : C_cplx)
    | C_mul (s1 s2 : C_cplx).

Fixpoint eval_C_cplx (s : C_cplx) : C :=
    match s with
    | C_0 => 0
    | C_1 => 1
    | C_conj s => (eval_C_cplx s)^*
    | C_add s1 s2 => (eval_C_cplx s1) + (eval_C_cplx s2)
    | C_opp s => - (eval_C_cplx s)
    | C_mul s1 s2 => (eval_C_cplx s1) * (eval_C_cplx s2)
    end.

Inductive A_base : DType -> Type :=
    | A_var (T : DType) (n : name) : A_base T
    | A_ground (T : DType) (t : eval_DType T) : A_base T
    | A_pair (T1 T2 : DType) (t1 : A_base T1) (t2 : A_base T2) : A_base (DPair T1 T2)
    | A_fst (T1 T2 : DType) (t : A_base (DPair T1 T2)) : A_base T1
    | A_snd (T1 T2 : DType) (t : A_base (DPair T1 T2)) : A_base T2.

Inductive S_scalar : Type :=
    | S_var (n : name)
    | S_ground (s : C_cplx)
    | S_delta (T : DType) (t1 t2 : A_base T)
    | S_add (s1 s2 : S_scalar)
    | S_opp (s : S_scalar)
    | S_mul (s1 s2 : S_scalar)
    | S_conj (s : S_scalar)
    | BK_inner (T : DType) (b : B_bra T) (k : K_ket T)
with K_ket : DType -> Type :=
    | K_var (T : DType) (n : name) : K_ket T
    | K_0 (T : DType) : K_ket T
    | K_ground (T : DType) (t : A_base T) : K_ket T
    | B_adj (T : DType) (b : B_bra T) : K_ket T
    | K_scale (s : S_scalar) (T : DType) (k : K_ket T) : K_ket T
    | K_add (T : DType) (k1 k2 : K_ket T) : K_ket T
    | K_opp (T : DType) (k : K_ket T) : K_ket T
    | K_apply (T1 T2 : DType) (o : O_opt T1 T2) (k : K_ket T1) : K_ket T2
    | K_ten (T1 T2 : DType) (k1 : K_ket T1) (k2 : K_ket T2) : K_ket (DPair T1 T2)
with B_bra : DType -> Type :=
    | B_var (T : DType) (n : name) : B_bra T
    | B_0 (T : DType) : B_bra T
    | B_ground (T : DType) (t : A_base T) : B_bra T
    | K_adj (T : DType) (b : K_ket T) : B_bra T
    | B_scale (s : S_scalar) (T : DType) (b : B_bra T) : B_bra T
    | B_add (T : DType) (b1 b2 : B_bra T) : B_bra T
    | B_opp (T : DType) (b : B_bra T) : B_bra T
    | B_apply (T1 T2 : DType) (o : O_opt T1 T2) (b : B_bra T2) : B_bra T1
    | B_ten (T1 T2 : DType) (b1 : B_bra T1) (b2 : B_bra T2) : B_bra (DPair T1 T2)
with O_opt : DType -> DType -> Type :=
    | O_var (T1 T2 : DType) (n : name) : O_opt T1 T2
    | O_0 (T1 T2 : DType) : O_opt T1 T2
    | KB_outer (T1 T2 : DType) (k : K_ket T1) (b : B_bra T2) : O_opt T2 T1
    | O_adj (T1 T2 : DType) (o : O_opt T1 T2) : O_opt T2 T1
    | O_scale (s : S_scalar) (T1 T2 : DType) (o : O_opt T1 T2) : O_opt T1 T2
    | O_add (T1 T2 : DType) (o1 o2 : O_opt T1 T2) : O_opt T1 T2
    | O_opp (T1 T2 : DType) (o : O_opt T1 T2) : O_opt T1 T2
    | O_comp (T1 T2 T3 : DType) (o1 : O_opt T1 T2) (o2 : O_opt T3 T1) : O_opt T3 T2
    | O_ten (T1 T2 T3 T4 : DType) (o1 : O_opt T1 T2) (o2 : O_opt T3 T4) : O_opt (DPair T1 T3) (DPair T2 T4).
Arguments K_0 {T}.
Arguments B_0 {T}.
Arguments O_0 {T1 T2}.

Variable (f_A_base : forall (T : DType), name -> eval_DType T).
Variable (f_S_scalar : name -> C).
Variable (f_K_ket : forall (T : DType), name -> 'Ht T).
Variable (f_B_bra : forall (T : DType), name -> 'Ht T).
Variable (f_O_opt : forall (T1 T2 : DType), name -> 'Hom{T1, T2}).

Fixpoint eval_A_base {T : DType} (e : A_base T) : eval_DType T :=
  match e in A_base T return eval_DType T with
  | A_var T n => f_A_base T n
  | A_ground T t => t
  | A_pair T1 T2 t1 t2 => (eval_A_base t1, eval_A_base t2)
  | A_fst T1 T2 t => (eval_A_base t).1
  | A_snd T1 T2 t => (eval_A_base t).2
  end.

Fixpoint eval_S_scalar (s : S_scalar) : C :=
  match s with
  | S_var n => f_S_scalar n
  | S_ground s => eval_C_cplx s
  | S_delta T t1 t2 => (eval_A_base t1 ==  eval_A_base t2)%:R
  | S_add s1 s2 => eval_S_scalar s1 + eval_S_scalar s2
  | S_opp s => - (eval_S_scalar s)
  | S_mul s1 s2 => eval_S_scalar s1 * eval_S_scalar s2
  | S_conj s => (eval_S_scalar s)^*
  | BK_inner T b k => [< eval_B_bra b ; eval_K_ket k>]
  end
with eval_K_ket (T : DType) (k : K_ket T): 'Ht T :=
  match k in K_ket T return 'Ht T with
  | K_var T n => f_K_ket T n
  | K_0 T => 0
  | K_ground T t => ''(eval_A_base t)
  | B_adj T b => eval_B_bra b
  | K_scale s T k => (eval_S_scalar s) *: (eval_K_ket k)
  | K_add T k1 k2 => (eval_K_ket k1) + (eval_K_ket k2)
  | K_opp T k => - (eval_K_ket k)
  | K_apply T1 T2 o k => (eval_O_opt o) (eval_K_ket k)
  | K_ten T1 T2 k1 k2 => (eval_K_ket k1) ⊗t (eval_K_ket k2)
  end
with eval_B_bra (T : DType) (b : B_bra T): 'Ht T :=
  match b in B_bra T return 'Ht T with
  | B_var T n => f_B_bra T n
  | B_0 T => 0
  | B_ground T t => ''(eval_A_base t)
  | K_adj T k => eval_K_ket k
  | B_scale s T b => (eval_S_scalar s) *: (eval_B_bra b)
  | B_add T b1 b2 => (eval_B_bra b1) + (eval_B_bra b2)
  | B_opp T b => - (eval_B_bra b)
  | B_apply T1 T2 o b => ((eval_O_opt o)^A (eval_B_bra b))
  | B_ten T1 T2 b1 b2 => (eval_B_bra b1) ⊗t (eval_B_bra b2)
  end
with eval_O_opt (T1 T2 : DType) (o : O_opt T1 T2) : 'Hom{T1, T2} :=
  match o in O_opt T1 T2 return 'Hom{T1, T2} with
  | O_var T1 T2 n => f_O_opt T1 T2 n
  | O_0 T1 T2 => 0%:VF
  | KB_outer T1 T2 k b => [> eval_K_ket k ; eval_B_bra b <]
  | O_adj T1 T2 o => (eval_O_opt o)^A
  | O_scale s T1 T2 o => (eval_S_scalar s) *: (eval_O_opt o)
  | O_add T1 T2 o1 o2 => (eval_O_opt o1) + (eval_O_opt o2)
  | O_opp T1 T2 o => - (eval_O_opt o)
  | O_comp T1 T2 T3 o1 o2 => (eval_O_opt o1) \o (eval_O_opt o2)
  | O_ten T1 T2 T3 T4 o1 o2 => (eval_O_opt o1) ⊗f (eval_O_opt o2)
  end.

Notation "A '=c' B" := (eval_C_cplx A = eval_C_cplx B) (at level 70).
Notation "A '=bs' B" := (eval_A_base A = eval_A_base B) (at level 70).
Notation "A '=s' B" := (eval_S_scalar A = eval_S_scalar B) (at level 70).
Notation "A '=k' B" := (eval_K_ket A = eval_K_ket B) (at level 70).
Notation "A '=b' B" := (eval_B_bra A = eval_B_bra B) (at level 70).
Notation "A '=o' B" := (eval_O_opt A = eval_O_opt B) (at level 70).

Infix "+" := (C_add) (only printing).
Infix "+" := (S_add) (only printing).
Infix "+" := (K_add) (only printing).
Infix "+" := (B_add) (only printing).
Infix "+" := (O_add) (only printing).
Notation "A '†'" := (B_adj A) (at level 8, format "A '†'", only printing).
Notation "A '†'" := (K_adj A) (format "A '†'", only printing).
Notation "A '†'" := (O_adj A) (format "A '†'", only printing).
Notation "A '†'" := (B_adj A) (format "A '†'", only printing).
Notation "A '^*'" := (C_conj A) (format "A '^*'", only printing).
Notation "A '^*'" := (S_conj A) (format "A '^*'", only printing).
Notation "0" := (C_0) (only printing).
Notation "0" := (B_0) (only printing).
Notation "0" := (K_0) (only printing).
Notation "0" := (O_0) (only printing).
Notation "1" := (C_1) (only printing).
Notation "'C(' A )" := (S_ground A) (format "'C(' A )", only printing).
Notation "- A" := (C_opp A) (only printing).
Notation "- A" := (S_opp A) (only printing).
Notation "- A" := (K_opp A) (only printing).
Notation "- A" := (B_opp A) (only printing).
Notation "- A" := (O_opp A) (only printing).
Notation "A - B" := (C_add A (C_opp B)) (only printing).
Notation "A - B" := (S_add A (S_opp B)) (only printing).
Notation "A - B" := (K_add A (K_opp B)) (only printing).
Notation "A - B" := (B_add A (B_opp B)) (only printing).
Notation "A - B" := (O_add A (O_opp B)) (only printing).
Infix "*" := (C_mul) (only printing).
Infix "*" := (S_mul) (only printing).
Notation "( A , B )" := (A_pair A B) (only printing).
Notation "A '.1'" := (A_fst A) (only printing).
Notation "A '.2'" := (A_snd A) (only printing).
Notation "'δ(' A , B )" := (S_delta A B) (format "'δ(' A , B )", only printing).
Infix "⊗" := (K_ten) (at level 45, only printing).
Infix "⊗" := (B_ten) (only printing).
Infix "⊗" := (O_ten) (only printing).
Notation "c *: A" := (K_scale c A) (only printing).
Notation "c *: A" := (B_scale c A) (only printing).
Notation "c *: A" := (O_scale c A) (only printing).
Infix "·" := (BK_inner) (at level 40, only printing).
Infix "·" := (K_apply) (only printing).
Notation "A · B" := (B_apply B A) (only printing).
Infix "·" := (KB_outer) (only printing).
Infix "·" := (O_comp) (only printing).
Notation "| A >" := (K_ground A) (only printing).
Notation "< A |" := (B_ground A) (only printing).

(* AC symbols : associativity & commutativity *)
Lemma C_addA (c1 c2 c3 : C_cplx) :
  C_add c1 (C_add c2 c3) =c C_add (C_add c1 c2) c3.
Proof. by rewrite/= addrA. Qed.
Lemma C_addC (c1 c2 : C_cplx) :
  C_add c1 c2 =c C_add c2 c1.
Proof. by rewrite/= addrC. Qed.

Lemma C_mulA (c1 c2 c3 : C_cplx) :
  C_mul c1 (C_mul c2 c3) =c C_mul (C_mul c1 c2) c3.
Proof. by rewrite/= mulrA. Qed.
Lemma C_mulC (c1 c2 : C_cplx) :
  C_mul c1 c2 =c C_mul c2 c1.
Proof. by rewrite/= mulrC. Qed.

Lemma S_addA (s1 s2 s3 : S_scalar) :
  S_add s1 (S_add s2 s3) =s S_add (S_add s1 s2) s3.
Proof. by rewrite/= addrA. Qed.
Lemma S_addC (s1 s2 : S_scalar) :
  S_add s1 s2 =s S_add s2 s1.
Proof. by rewrite/= addrC. Qed.

Lemma S_mulA (s1 s2 s3 : S_scalar) :
  S_mul s1 (S_mul s2 s3) =s S_mul (S_mul s1 s2) s3.
Proof. by rewrite/= mulrA. Qed.
Lemma S_mulC (s1 s2 : S_scalar) :
  S_mul s1 s2 =s S_mul s2 s1.
Proof. by rewrite/= mulrC. Qed.

Lemma K_addA T (k1 k2 k3 : K_ket T) :
  K_add k1 (K_add k2 k3) =k K_add (K_add k1 k2) k3.
Proof. by rewrite/= addrA. Qed.
Lemma K_addC T (k1 k2 : K_ket T) :
  K_add k1 k2 =k K_add k2 k1.
Proof. by rewrite/= addrC. Qed.

Lemma B_addA T (b1 b2 b3 : B_bra T) :
  B_add b1 (B_add b2 b3) =b B_add (B_add b1 b2) b3.
Proof. by rewrite/= addrA. Qed.
Lemma B_addC T (b1 b2 : B_bra T) :
  B_add b1 b2 =b B_add b2 b1.
Proof. by rewrite/= addrC. Qed.

Lemma O_addA T1 T2 (o1 o2 o3 : O_opt T1 T2) :
  O_add o1 (O_add o2 o3) =o O_add (O_add o1 o2) o3.
Proof. by rewrite/= addrA. Qed.
Lemma O_addC T1 T2 (o1 o2 : O_opt T1 T2) :
  O_add o1 o2 =o O_add o2 o1.
Proof. by rewrite/= addrC. Qed.

(* C symbols : commutativity *)
Lemma S_deltaC T (t1 t2 : A_base T) :
  S_delta t1 t2 =s S_delta t2 t1.
Proof. by rewrite/= eq_sym. Qed. 

(* BASIS *)
Lemma BASIS_1 T1 T2 (e1 : A_base T1) (e2 : A_base T2) :
  A_fst (A_pair e1 e2) =bs e1.
Proof. by []. Qed.
Lemma BASIS_2 T1 T2 (e1 : A_base T1) (e2 : A_base T2) :
  A_snd (A_pair e1 e2) =bs e2.
Proof. by []. Qed.
Lemma BASIS_3 T1 T2 (e : A_base (DPair T1 T2)) :
  A_pair (A_fst e) (A_snd e) =bs e.
Proof. by rewrite/= -surjective_pairing. Qed.  

(* DELTA *)
Lemma DELTA_1 T1 T2 (u : A_base (DPair T1 T2)) (s : A_base T1) (t : A_base T2) :
  S_delta u (A_pair s t) =s S_mul (S_delta (A_fst u) s) (S_delta (A_snd u) t).
Proof. by rewrite/= -pair_eqE/= -natrM mulnb. Qed.
Lemma DELTA_2 T1 T2 (u v : A_base (DPair T1 T2)) :
  S_mul (S_delta (A_fst u) (A_fst v)) (S_delta (A_snd u) (A_snd v)) =s S_delta u v.
Proof. by rewrite/= -pair_eqE/= -natrM mulnb. Qed.

(* SCR-COMPLEX *)
Lemma SCR_COMPLEX_1 (S : S_scalar) :
  S_add (S_ground (C_0)) S =s S.
Proof. by rewrite/= add0r. Qed.
Lemma SCR_COMPLEX_2 (a b : C_cplx) :
  S_add (S_ground a) (S_ground b) =s S_ground (C_add a b).
Proof. by []. Qed.
Lemma SCR_COMPLEX_3 (S : S_scalar) :
  S_add S S =s S_mul (S_ground (C_add C_1 C_1)) S.
Proof. by rewrite/= mulrDl mul1r. Qed.
Lemma SCR_COMPLEX_4 (a : C_cplx) (S : S_scalar) :
  S_add (S_mul (S_ground a) S) S =s S_mul (S_ground (C_add a C_1)) S.
Proof. by rewrite/= mulrDl mul1r. Qed.
Lemma SCR_COMPLEX_5 (a b : C_cplx) (S : S_scalar) :
  S_add (S_mul (S_ground a) S) (S_mul (S_ground b) S) =s S_mul (S_ground (C_add a b)) S.
Proof. by rewrite/= mulrDl. Qed. 

Lemma SCR_COMPLEX_6 (S : S_scalar) :
  S_mul (S_ground (C_0)) S =s S_ground (C_0).
Proof. by rewrite/= mul0r. Qed.
Lemma SCR_COMPLEX_7 (S : S_scalar) :
  S_mul (S_ground (C_1)) S =s S.
Proof. by rewrite/= mul1r. Qed.
Lemma SCR_COMPLEX_8 (a b : C_cplx) :
  S_mul (S_ground a) (S_ground b) =s S_ground (C_mul a b).
Proof. by []. Qed.
Lemma SCR_COMPLEX_9 (S1 S2 S3 : S_scalar) :
  S_mul S1 (S_add S2 S3) =s S_add (S_mul S1 S2) (S_mul S1 S3).
Proof. by rewrite/= mulrDr. Qed.

Lemma SCR_COMPLEX_10 (a : C_cplx) :
  S_conj (S_ground a) =s S_ground (C_conj a).
Proof. by []. Qed.
Lemma SCR_COMPLEX_11 T (s t : A_base T) :
  S_conj (S_delta s t) =s S_delta s t.
Proof. by rewrite/= conjC_nat. Qed.
Lemma SCR_COMPLEX_12 (S1 S2 : S_scalar) :
  S_conj (S_add S1 S2) =s S_add (S_conj S1) (S_conj S2).
Proof. by rewrite/= rmorphD. Qed.
Lemma SCR_COMPLEX_13 (S1 S2 : S_scalar) :
  S_conj (S_mul S1 S2) =s S_mul (S_conj S1) (S_conj S2).
Proof. by rewrite/= rmorphM. Qed.
Lemma SCR_COMPLEX_14 (S : S_scalar) :
  S_conj (S_conj S) =s S.
Proof. by rewrite/= conjCK. Qed.
Lemma SCR_COMPLEX_15 T (B : B_bra T) (K : K_ket T) :
  S_conj (BK_inner B K) =s BK_inner (K_adj K) (B_adj B).
Proof. by rewrite/= conj_dotp. Qed.

(* SCR-DOT *)
Lemma SCR_DOT_1 T (K : K_ket T) :
  BK_inner B_0 K =s S_ground (C_0).
Proof. by rewrite/= dot0p. Qed.
Lemma SCR_DOT_2 T (B : B_bra T) :
  BK_inner B K_0 =s S_ground (C_0).
Proof. by rewrite/= dotp0. Qed.
Lemma SCR_DOT_3 T (S : S_scalar) (B : B_bra T) (K : K_ket T) :
  BK_inner (B_scale S B) K =s S_mul (S_conj S) (BK_inner B K).
Proof. by rewrite/= dotpZl. Qed.
Lemma SCR_DOT_4 T (S : S_scalar) (B : B_bra T) (K : K_ket T) :
  BK_inner B (K_scale S K) =s S_mul S (BK_inner B K).
Proof. by rewrite/= dotpZr. Qed.
Lemma SCR_DOT_5 T (B1 B2 : B_bra T) (K : K_ket T) :
  BK_inner (B_add B1 B2) K =s S_add (BK_inner B1 K) (BK_inner B2 K).
Proof. by rewrite/= dotpDl. Qed.
Lemma SCR_DOT_6 T (B : B_bra T) (K1 K2 : K_ket T) :
  BK_inner B (K_add K1 K2) =s S_add (BK_inner B K1) (BK_inner B K2).
Proof. by rewrite/= dotpDr. Qed.
Lemma SCR_DOT_7 T (s t : A_base T) :
  BK_inner (B_ground s) (K_ground t) =s S_delta s t.
Proof. by rewrite/= t2tv_dot. Qed.

Lemma SCR_DOT_8 T1 T2 (B1 : B_bra T1) (B2 : B_bra T2) (t : A_base (DPair T1 T2)) :
  BK_inner (B_ten B1 B2) (K_ground t) =s 
    S_mul (BK_inner B1 (K_ground (A_fst t))) (BK_inner B2 (K_ground (A_snd t))).
Proof. by rewrite/=-tentv_dot tentv_t2tv -surjective_pairing. Qed.
Lemma SCR_DOT_9 T1 T2 (t : A_base (DPair T1 T2)) (K1 : K_ket T1) (K2 : K_ket T2) :
  BK_inner (B_ground t) (K_ten K1 K2) =s
    S_mul (BK_inner (B_ground (A_fst t)) K1) (BK_inner (B_ground (A_snd t)) K2).
Proof. by rewrite/= -tentv_dot tentv_t2tv -surjective_pairing. Qed.
Lemma SCR_DOT_10 T1 T2 (B1 : B_bra T1) (B2 : B_bra T2) (K1 : K_ket T1) (K2 : K_ket T2) :
  BK_inner (B_ten B1 B2) (K_ten K1 K2) =s S_mul (BK_inner B1 K1) (BK_inner B2 K2).
Proof. by rewrite/= -tentv_dot. Qed.

(* SCR-SORT *)
Lemma SCR_SORT_1 T1 T2 (B : B_bra T1) (O : O_opt T2 T1) (K : K_ket T2) :
  BK_inner (B_apply O B) K =s BK_inner B (K_apply O K).
Proof. by rewrite/= adj_dotEl. Qed.
Lemma SCR_SORT_2 T1 T2 T3 T4 (s : A_base (DPair T1 T2)) (O1 : O_opt T3 T1) 
  (O2 : O_opt T4 T2) (K : K_ket (DPair T3 T4)) :
    BK_inner (B_ground s) (K_apply (O_ten O1 O2) K) =s
      BK_inner (B_ten (B_apply O1 (B_ground (A_fst s))) (B_apply O2 (B_ground (A_snd s)))) K.
Proof.
rewrite -SCR_SORT_1/=; do 2 f_equal.
by rewrite -tentf_apply tentv_t2tv -surjective_pairing tentf_adj.
Qed.
Lemma SCR_SORT_3 T1 T2 T3 T4 (B1 : B_bra T1) (B2 : B_bra T2) (O1 : O_opt T3 T1) 
  (O2 : O_opt T4 T2) (K : K_ket (DPair T3 T4)) :
    BK_inner (B_ten B1 B2) (K_apply (O_ten O1 O2) K) =s
      BK_inner (B_ten (B_apply O1 B1) (B_apply O2 B2)) K.
Proof.
rewrite -SCR_SORT_1/=; do 2 f_equal.
by rewrite tentf_adj tentf_apply.
Qed.

(* KET-CT *)
Lemma KET_CT_1 T :
  B_adj (@B_0 T) =k K_0.
Proof. by []. Qed.
Lemma KET_CT_2 T (t : A_base T) :
  B_adj (B_ground t) =k K_ground t.
Proof. by []. Qed.
Lemma KET_CT_3 T (K : K_ket T) :
  B_adj (K_adj K) =k K.
Proof. by []. Qed.
Lemma KET_CT_4 T (S : S_scalar) (B : B_bra T) :
  B_adj (B_scale S B) =k K_scale S (B_adj B).
Proof. by []. Qed.
Lemma KET_CT_5 T (B1 B2 : B_bra T) :
  B_adj (B_add B1 B2) =k K_add (B_adj B1) (B_adj B2).
Proof. by []. Qed.
Lemma KET_CT_6 T1 T2 (B : B_bra T2) (O : O_opt T1 T2) :
  B_adj (B_apply O B) =k K_apply (O_adj O) (B_adj B).
Proof. by []. Qed.
Lemma KET_CT_7 T1 T2 (B1 : B_bra T1) (B2 : B_bra T2) :
  B_adj (B_ten B1 B2) =k K_ten (B_adj B1) (B_adj B2).
Proof. by []. Qed.

(* KET-SCAL *)
Lemma KET_SCAL_1 T (K : K_ket T) :
  K_scale (S_ground (C_0)) K =k K_0.
Proof. by rewrite/= scale0r. Qed.
Lemma KET_SCAL_2 T (K : K_ket T) :
  K_scale (S_ground (C_1)) K =k K. 
Proof. by rewrite/= scale1r. Qed.
Lemma KET_SCAL_3 T (S : S_scalar) :
  K_scale S (@K_0 T) =k K_0.
Proof. by rewrite/= scaler0. Qed.
Lemma KET_SCAL_4 T (S1 S2 : S_scalar) (K : K_ket T) :
  K_scale S1 (K_scale S2 K) =k K_scale (S_mul S1 S2) K.
Proof. by rewrite/= scalerA. Qed.
Lemma KET_SCAL_5 T (S : S_scalar) (K1 K2 : K_ket T) :
  K_scale S (K_add K1 K2) =k K_add (K_scale S K1) (K_scale S K2).
Proof. by rewrite/= scalerDr. Qed.

(* KET-ADD *)
Lemma KET_ADD_1 T (K : K_ket T) :
  K_add K K_0 =k K.
Proof. by rewrite/= addr0. Qed.
Lemma KET_ADD_2 T (K : K_ket T) :
  K_add K K =k K_scale (S_ground (C_add C_1 C_1)) K.
Proof. by rewrite/= scalerDl scale1r. Qed.
Lemma KET_ADD_3 T (S : S_scalar) (K : K_ket T) :
  K_add (K_scale S K) K =k K_scale (S_add S (S_ground C_1)) K.
Proof. by rewrite/= scalerDl scale1r. Qed.
Lemma KET_ADD_4 T (S1 S2 : S_scalar) (K : K_ket T) :
  K_add (K_scale S1 K) (K_scale S2 K) =k K_scale (S_add S1 S2) K.
Proof. by rewrite/= scalerDl. Qed.

(* KET-MUL *)
Lemma KET_MUL_1 T1 T2 (K : K_ket T1) :
  K_apply (@O_0 T1 T2) K =k K_0.
Proof. by rewrite/= lfunE. Qed.
Lemma KET_MUL_2 T1 T2 (O : O_opt T1 T2) :
  K_apply O K_0 =k K_0.
Proof. by rewrite/= linear0. Qed.
Lemma KET_MUL_3 T1 T2 (S : S_scalar) (O : O_opt T1 T2) (K : K_ket T1) :
  K_apply (O_scale S O) K =k K_scale S (K_apply O K).
Proof. by rewrite/= lfunE. Qed.
Lemma KET_MUL_4 T1 T2 (S : S_scalar) (O : O_opt T1 T2) (K : K_ket T1) :
  K_apply O (K_scale S K) =k K_scale S (K_apply O K).
Proof. by rewrite/= linearZ. Qed.
Lemma KET_MUL_5 T1 T2 (O1 O2 : O_opt T1 T2) (K : K_ket T1) :
  K_apply (O_add O1 O2) K =k K_add (K_apply O1 K) (K_apply O2 K).
Proof. by rewrite/= lfunE. Qed.
Lemma KET_MUL_6 T1 T2 (O : O_opt T1 T2) (K1 K2 : K_ket T1) :
  K_apply O (K_add K1 K2) =k K_add (K_apply O K1) (K_apply O K2).
Proof. by rewrite/= linearD. Qed.
Lemma KET_MUL_7 T1 T2 (K1 : K_ket T1) (B : B_bra T2) (K2 : K_ket T2) :
  K_apply (KB_outer K1 B) K2 =k K_scale (BK_inner B K2) K1.
Proof. by rewrite/= outpE. Qed.
Lemma KET_MUL_8 T1 T2 T3 (O1 : O_opt T1 T2) (O2 : O_opt T3 T1) (K : K_ket T3) :
  K_apply (O_comp O1 O2) K =k K_apply O1 (K_apply O2 K).
Proof. by rewrite/= lfunE. Qed.
Lemma KET_MUL_9 T1 T2 T3 T1' T2' T3' (O1 : O_opt T1 T2) (O1' : O_opt T3 T1) 
  (O2 : O_opt T1' T2') (O2' : O_opt T3' T1') (K : K_ket (DPair T3 T3')) :
    K_apply (O_ten O1 O2) (K_apply (O_ten O1' O2') K) =k
      K_apply (O_ten (O_comp O1 O1') (O_comp O2 O2')) K.
Proof. by rewrite/= -tentf_comp lfunE. Qed.
Lemma KET_MUL_10 T1 T2 T3 T4 (O1 : O_opt T1 T3) (O2 : O_opt T2 T4) (t : A_base (DPair T1 T2)) :
  K_apply (O_ten O1 O2) (K_ground t) =k 
    K_ten (K_apply O1 (K_ground (A_fst t))) (K_apply O2 (K_ground (A_snd t))).
Proof. by rewrite/= -tentf_apply tentv_t2tv -surjective_pairing. Qed.
Lemma KET_MUL_11 T1 T2 T3 T4 (O1 : O_opt T1 T3) (O2 : O_opt T2 T4) 
  (K1 : K_ket T1) (K2 : K_ket T2) :
    K_apply (O_ten O1 O2) (K_ten K1 K2) =k
      K_ten (K_apply O1 K1) (K_apply O2 K2).
Proof. by rewrite/= tentf_apply. Qed.

(* KET-TSR *)
Lemma KET_TSR_1 T1 T2 (K : K_ket T2) :
  K_ten (@K_0 T1) K =k K_0.
Proof. by rewrite/= ten0tv. Qed.
Lemma KET_TSR_2 T1 T2 (K : K_ket T1) :
  K_ten K (@K_0 T2) =k K_0.
Proof. by rewrite/= tentv0. Qed.
Lemma KET_TSR_3 T1 T2 (s : A_base T1) (t : A_base T2) :
  K_ten (K_ground s) (K_ground t) =k K_ground (A_pair s t).
Proof. by rewrite/= tentv_t2tv. Qed.
Lemma KET_TSR_4 T1 T2 (S : S_scalar) (K1 : K_ket T1) (K2 : K_ket T2) :
  K_ten (K_scale S K1) K2 =k K_scale S (K_ten K1 K2).
Proof. by rewrite/= tentvZl. Qed.
Lemma KET_TSR_5 T1 T2 (S : S_scalar) (K1 : K_ket T1) (K2 : K_ket T2) :
  K_ten K1 (K_scale S K2) =k K_scale S (K_ten K1 K2).
Proof. by rewrite/= tentvZr. Qed.
Lemma KET_TSR_6 T1 T2 (K1 K2 : K_ket T1) (K3 : K_ket T2) :
  K_ten (K_add K1 K2) K3 =k K_add (K_ten K1 K3) (K_ten K2 K3).
Proof. by rewrite/= tentvDl. Qed.
Lemma KET_TSR_7 T1 T2 (K1 : K_ket T1) (K2 K3 : K_ket T2) :
  K_ten K1 (K_add K2 K3) =k K_add (K_ten K1 K2) (K_ten K1 K3).
Proof. by rewrite/= tentvDr. Qed.

(* OPT-OUTER *)
Lemma OPT_OUTER_1 T1 T2 (B : B_bra T2) :
  KB_outer (@K_0 T1) B =o O_0.
Proof. by rewrite/= out0p. Qed.
Lemma OPT_OUTER_2 T1 T2 (K : K_ket T1) :
  KB_outer K (@B_0 T2) =o O_0.
Proof. by rewrite/= outp0. Qed.
Lemma OPT_OUTER_3 T1 T2 (S : S_scalar) (K : K_ket T1) (B : B_bra T2) :
  KB_outer (K_scale S K) B =o O_scale S (KB_outer K B).
Proof. by rewrite/= outpZl. Qed.
Lemma OPT_OUTER_4 T1 T2 (S : S_scalar) (K : K_ket T1) (B : B_bra T2) :
  KB_outer K (B_scale S B) =o O_scale (S_conj S) (KB_outer K B).
Proof. by rewrite/= outpZr. Qed.
Lemma OPT_OUTER_5 T1 T2 (K1 K2 : K_ket T1) (B : B_bra T2) :
  KB_outer (K_add K1 K2) B =o O_add (KB_outer K1 B) (KB_outer K2 B).
Proof. by rewrite/= outpDl. Qed.
Lemma OPT_OUTER_6 T1 T2 (K : K_ket T1) (B1 B2 : B_bra T2) :
  KB_outer K (B_add B1 B2) =o O_add (KB_outer K B1) (KB_outer K B2).
Proof. by rewrite/= outpDr. Qed.

(* OPT-CT *)
Lemma OPT_CT_1 T1 T2 :
  O_adj (@O_0 T1 T2) =o O_0.
Proof. by rewrite/= adjf0. Qed.
Lemma OPT_CT_2 T1 T2 (K : K_ket T1) (B : B_bra T2) :
  O_adj (KB_outer K B) =o KB_outer (B_adj B) (K_adj K).
Proof. by rewrite/= adj_outp. Qed.
Lemma OPT_CT_3 T1 T2 (O : O_opt T1 T2) :
  O_adj (O_adj O) =o O.
Proof. by rewrite/= adjfK. Qed.
Lemma OPT_CT_4 T1 T2 (S : S_scalar) (O : O_opt T1 T2) :
  O_adj (O_scale S O) =o O_scale (S_conj S) (O_adj O).
Proof. by rewrite/= adjfZ. Qed.
Lemma OPT_CT_5 T1 T2 (O1 O2 : O_opt T1 T2) :
  O_adj (O_add O1 O2) =o O_add (O_adj O1) (O_adj O2).
Proof. by rewrite/= adjfD. Qed.
Lemma OPT_CT_6 T1 T2 T3 (O1 : O_opt T1 T2) (O2 : O_opt T3 T1) :
  O_adj (O_comp O1 O2) =o O_comp (O_adj O2) (O_adj O1).
Proof. by rewrite/= adjf_comp. Qed.
Lemma OPT_CT_7 T1 T2 T3 T4 (O1 : O_opt T1 T3) (O2 : O_opt T2 T4) :
  O_adj (O_ten O1 O2) =o O_ten (O_adj O1) (O_adj O2).
Proof. by rewrite/= tentf_adj. Qed.

(* OPT-SCAL *)
Lemma  OPT_SCAL_1 T1 T2 (O : O_opt T1 T2) :
  O_scale (S_ground (C_0)) O =o O_0.
Proof. by rewrite/= scale0r. Qed.
Lemma  OPT_SCAL_2 T1 T2 (O : O_opt T1 T2) :
  O_scale (S_ground (C_1)) O =o O.
Proof. by rewrite/= scale1r. Qed.
Lemma  OPT_SCAL_3 T1 T2 (S : S_scalar) :
  O_scale S (@O_0 T1 T2) =o O_0.
Proof. by rewrite/= scaler0. Qed.
Lemma  OPT_SCAL_4 T1 T2 (S1 S2 : S_scalar) (O : O_opt T1 T2) :
  O_scale S1 (O_scale S2 O) =o O_scale (S_mul S1 S2) O.
Proof. by rewrite/= scalerA. Qed.
Lemma  OPT_SCAL_5 T1 T2 (S : S_scalar) (O1 O2 : O_opt T1 T2) :
  O_scale S (O_add O1 O2) =o O_add (O_scale S O1) (O_scale S O2).
Proof. by rewrite/= scalerDr. Qed.

(* OPT-ADD *)
Lemma OPT_ADD_1 T1 T2 (O : O_opt T1 T2) :
  O_add O O_0 =o O.
Proof. by rewrite/= addr0. Qed.
Lemma OPT_ADD_2 T1 T2 (O : O_opt T1 T2) :
  O_add O O =o O_scale (S_ground (C_add C_1 C_1)) O.
Proof. by rewrite/= scalerDl scale1r. Qed.
Lemma OPT_ADD_3 T1 T2 (S : S_scalar) (O : O_opt T1 T2) :
  O_add (O_scale S O) O =o O_scale (S_add S (S_ground C_1)) O.
Proof. by rewrite/= scalerDl scale1r. Qed.
Lemma OPT_ADD_4 T1 T2 (S1 S2 : S_scalar) (O : O_opt T1 T2) :
  O_add (O_scale S1 O) (O_scale S2 O) =o O_scale (S_add S1 S2) O.
Proof. by rewrite/= scalerDl. Qed.

(* OPT-MUL *)
Lemma OPT_MUL_1 T1 T2 T3 (O : O_opt T3 T1) :
  O_comp (@O_0 T1 T2) O =o O_0.
Proof. by rewrite/= comp_lfun0l. Qed.
Lemma OPT_MUL_2 T1 T2 T3 (O : O_opt T1 T2) :
  O_comp O (@O_0 T3 T1) =o O_0.
Proof. by rewrite/= comp_lfun0r. Qed.
Lemma OPT_MUL_3 T1 T2 T3 (K : K_ket T1) (B : B_bra T2) (O : O_opt T3 T2) :
  O_comp (KB_outer K B) O =o KB_outer K (B_apply O B).
Proof. by rewrite/= outp_compl. Qed.  
Lemma OPT_MUL_4 T1 T2 T3 (O : O_opt T1 T3) (K : K_ket T1) (B : B_bra T2) :
  O_comp O (KB_outer K B) =o KB_outer (K_apply O K) B.
Proof. by rewrite/= outp_compr. Qed.
Lemma OPT_MUL_5 T1 T2 T3 (S : S_scalar) (O1 : O_opt T1 T2) (O2 : O_opt T3 T1) :
  O_comp (O_scale S O1) O2 =o O_scale S (O_comp O1 O2).
Proof. by rewrite/= linearZl. Qed.
Lemma OPT_MUL_6 T1 T2 T3 (S : S_scalar) (O1 : O_opt T1 T2) (O2 : O_opt T3 T1) :
  O_comp O1 (O_scale S O2) =o O_scale S (O_comp O1 O2).
Proof. by rewrite/= linearZr. Qed.
Lemma OPT_MUL_7 T1 T2 T3  (O1 O2 : O_opt T1 T2) (O3 : O_opt T3 T1) :
  O_comp (O_add O1 O2) O3 =o O_add (O_comp O1 O3) (O_comp O2 O3).
Proof. by rewrite/= linearDl. Qed.
Lemma OPT_MUL_8 T1 T2 T3  (O1 : O_opt T1 T2) (O2 O3 : O_opt T3 T1) :
  O_comp O1 (O_add O2 O3) =o O_add (O_comp O1 O2) (O_comp O1 O3).
Proof. by rewrite/= linearDr. Qed.
Lemma OPT_MUL_9 T1 T2 T3 T4 (O1 : O_opt T2 T1) (O2 : O_opt T3 T2) (O3 : O_opt T4 T3) :
  O_comp (O_comp O1 O2) O3 =o O_comp O1 (O_comp O2 O3).
Proof. by rewrite/= comp_lfunA. Qed.
Lemma OPT_MUL_10 T1 T2 T3 T1' T2' T3' (O1 : O_opt T1 T2) (O1' : O_opt T3 T1) 
  (O2 : O_opt T1' T2') (O2' : O_opt T3' T1') :
    O_comp (O_ten O1 O2) (O_ten O1' O2') =o O_ten (O_comp O1 O1') (O_comp O2 O2').
Proof. by rewrite/= tentf_comp. Qed.
Lemma OPT_MUL_11 T1 T2 T3 T1' T2' T3' T4 (O1 : O_opt T1 T2) (O1' : O_opt T3 T1) 
  (O2 : O_opt T1' T2') (O2' : O_opt T3' T1') (O3 : O_opt T4 (DPair T3 T3')):
    O_comp (O_ten O1 O2) (O_comp (O_ten O1' O2') O3) =o 
      O_comp (O_ten (O_comp O1 O1') (O_comp O2 O2')) O3.
Proof. by rewrite -OPT_MUL_9/= tentf_comp. Qed.

(* OPT-TSR *)
Lemma OPT_TSR_1 T1 T2 T3 T4 (O : O_opt T3 T4) :
  O_ten (@O_0 T1 T2) O =o O_0.
Proof. by rewrite/= ten0tf. Qed.
Lemma OPT_TSR_2 T1 T2 T3 T4 (O : O_opt T1 T2) :
  O_ten O (@O_0 T3 T4) =o O_0.
Proof. by rewrite/= tentf0. Qed.
Lemma OPT_TSR_3 T1 T2 T3 T4 (K1 : K_ket T1) (B1 : B_bra T2) (K2 : K_ket T3) (B2 : B_bra T4) :
  O_ten (KB_outer K1 B1) (KB_outer K2 B2) =o KB_outer (K_ten K1 K2) (B_ten B1 B2).
Proof. by rewrite/= tentv_out. Qed.
Lemma OPT_TSR_4 T1 T2 T3 T4 (S : S_scalar) (O1 : O_opt T1 T2) (O2 : O_opt T3 T4) :
  O_ten (O_scale S O1) O2 =o O_scale S (O_ten O1 O2).
Proof. by rewrite/= tentfZl. Qed.
Lemma OPT_TSR_5 T1 T2 T3 T4 (S : S_scalar) (O1 : O_opt T1 T2) (O2 : O_opt T3 T4) :
  O_ten O1 (O_scale S O2) =o O_scale S (O_ten O1 O2).
Proof. by rewrite/= tentfZr. Qed.
Lemma OPT_TSR_6 T1 T2 T3 T4 (O1 O2 : O_opt T1 T2) (O3 : O_opt T3 T4) :
  O_ten (O_add O1 O2) O3 =o O_add (O_ten O1 O3) (O_ten O2 O3).
Proof. by rewrite/= tentfDl. Qed.
Lemma OPT_TSR_7 T1 T2 T3 T4 (O1 : O_opt T1 T2) (O2 O3 : O_opt T3 T4) :
  O_ten O1 (O_add O2 O3) =o O_add (O_ten O1 O2) (O_ten O1 O3).
Proof. by rewrite/= tentfDr. Qed.

Lemma test1 T (K : K_ket T) (S : S_scalar) :
  K_adj (K_scale S K) =b B_scale S (K_adj K).
Proof. by []. Qed.
Lemma test2 T1 T2 (B : B_bra T1) (O : O_opt T2 T1) (S : S_scalar) :
  B_apply (O_scale S O) B =b B_scale (S_conj S) (B_apply O B).
Proof. by rewrite/= adjfZ lfunE. Qed.

End DiracTRS_SOUND.
