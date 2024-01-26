From mathcomp Require Import all_ssreflect all_algebra.
From quantum.external Require Import forms.
From mathcomp.classical Require Import boolp cardinality mathcomp_extra
  classical_sets functions.
From mathcomp.analysis Require Import ereal reals signed topology 
  prodnormedzmodule normedtype sequences.
From mathcomp.real_closed Require Import complex.
Require Import mcextra mcaextra notation mxpred.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order Order.Theory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.
Import VNorm.Exports VOrder.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(* Since most of the topological properties of real and complex matrix are    *)
(* the same, we use the module     ExtNum (R : realType) : numFieldType       *)
(* to mode the number field                                                   *)
(* both R and R[i] belongs to extNumType R                                    *)
(* C : extNumType R : bounded -> compact &                                    *)
(*                    r2c : {rmorphism R -> C}, c2r : C -> R                  *)
(*                    r2c is mono to <=; c2r continuous and linear            *)
(*                    r2c, c2r are bij on real numbers                        *)
(* TODO: ExtNum somewhat non-standard; I haven't seen such a thing before     *)
(*       Change to a more reasonable one?                                     *)
(* Remark : alternative is to define ExtNum as a finite dimensional realType  *)
(*          but since want to treat ExtNum itself as a numFieldType, avoid    *)
(*          to canonical it as a vectType R                                   *)
(* -------------------------------------------------------------------------- *)
(* Theory of matrix over extNumType                                           *)
(*        vector norm are equivalent                                          *)
(*        Bolzano_Weierstrass theorem                                         *)
(*        Monotone convergence theorem (w.r.t. closed vorder)                 *)
(******************************************************************************)

Section closed_eq.

Lemma closed1 (T : topologicalType) : hausdorff_space T -> 
  forall t : T, closed [set t].
Proof. by move=>HT t; apply: compact_closed=>//; apply: compact_set1. Qed.

Lemma closed_eq (R : numFieldType) (V : pseudoMetricNormedZmodType R) (v : V) :
  closed [set x | x = v].
Proof. by apply: closed1; apply: norm_hausdorff. Qed.

End closed_eq.

Section TrivialMatrixFun.
Implicit Type (R: ringType).

Lemma mxf_dim0n R T p : all_equal_to ((fun=>0) : T -> 'M[R]_(0,p)).
Proof. by move=>h/=; apply/funext=>i; rewrite mx_dim0E. Qed.
Lemma mxf_dimn0 R T p : all_equal_to ((fun=>0) : T -> 'M[R]_(p,0)).
Proof. by move=>h/=; apply/funext=>i; rewrite mx_dim0E. Qed.

Lemma vec_mx_dim0n R m : @vec_mx R 0 m = fun=>0.
Proof. by apply/funext=>x; rewrite mx_dim0E. Qed.
Lemma vec_mx_dimn0 R m : @vec_mx R m 0 = fun=>0.
Proof. by apply/funext=>x; rewrite mx_dim0E. Qed.

Definition mx_dim0 := (mx_dim0n,mx_dimn0,mxf_dim0n,
  mxf_dimn0).

Lemma mx_dim0_cond R m n : (m == 0%N) || (n == 0%N) -> 
  all_equal_to (0 : 'M[R]_(m,n)).
Proof.
move=>/orP[/eqP/esym|/eqP/esym] P.
case: m / P; exact: mx_dim0n. case: n / P; exact: mx_dimn0.
Qed.

Lemma mxf_dim0_cond R m n T : (m == 0%N) || (n == 0%N) -> 
  all_equal_to ((fun=>0) : T -> 'M[R]_(m,n)).
Proof.
move=>/orP[/eqP/esym|/eqP/esym] P.
case: m / P; exact: mxf_dim0n. case: n / P; exact: mxf_dimn0.
Qed.
Definition mx_dim0C := (mx_dim0_cond, mxf_dim0_cond).

Variable (C : numFieldType) (p : nat).
Lemma mxcvg_dim0n (h: nat -> 'M[C]_(0,p)) (x : 'M[C]_(0,p)) : h --> x.
Proof. by rewrite !mx_dim0; apply: cvg_cst. Qed.
Lemma mxcvg_dimn0 (h: nat -> 'M[C]_(p,0)) (x : 'M[C]_(p,0)) : h --> x.
Proof. by rewrite !mx_dim0; apply: cvg_cst. Qed.
Lemma is_mxcvg_dim0n (h: nat -> 'M[C]_(0,p)) : cvg h.
Proof. by apply/cvg_ex; exists 0; apply mxcvg_dim0n. Qed.
Lemma is_mxcvg_dimn0 (h: nat -> 'M[C]_(p,0)) : cvg h.
Proof. by apply/cvg_ex; exists 0; apply mxcvg_dimn0. Qed.

End TrivialMatrixFun.

Section mx_norm_vnorm.

Lemma mx_normvZ (K: numDomainType) (m n: nat) (l : K) (x : 'M[K]_(m,n)) : 
  mx_norm (l *: x) = `| l | * mx_norm x.
Proof.
rewrite /= !mx_normE (eq_bigr (fun i => (`|l| * `|x i.1 i.2|)%:nng)); last first.
  by move=> i _; rewrite mxE //=; apply/eqP; rewrite -num_eq /= Num.Theory.normrM.
elim/big_ind2 : _ => // [|a b c d bE dE]; first by rewrite mulr0.
by rewrite !num_max bE dE Num.Theory.maxr_pMr.
Qed.
Canonical mx_norm_vnorm (K: numDomainType) (m n: nat) := 
  Vnorm (@ler_mx_norm_add _ _ _) (@mx_norm_eq0 _ _ _) (@mx_normvZ K m n).

Canonical normedMod_normedVnorm (R : numDomainType) (V : normedModType R) :=
  Vnorm (@Num.Theory.ler_normD _ V) (@Num.Theory.normr0_eq0 _ V) (@normrZ _ V).

Lemma mx_normEV (K: numDomainType) p q : 
  (@mx_norm _ _ _ : 'M[K]_(p.+1,q.+1) -> K) = (@Num.Def.normr _ _).
Proof. by apply/funext. Qed.

Lemma ball_dim0 (K: numFieldType) m n (x : 'M[K]_(m,n)) e y : 
  (m == 0%N) || (n == 0%N) -> ball x e y.
Proof.
move=>/orP[/eqP/esym Pm|/eqP/esym Pn]. 
case: m / Pm x y=>x y. 2: case: n / Pn x y=>x y.
1,2: by rewrite /ball/=/mx_ball=>i j; case: i=>//; case: j.
Qed.

Lemma mxball_normE (K: numFieldType) m n (x : 'M[K]_(m,n)) e y : 
  ball x e y <-> (m == 0%N) || (n == 0%N) || (mx_norm (x-y) < e).
case: m x y=>[x/= y|]; last case: n=>[m x/= y|n m x y/=].
1,2: by split=>// _; apply/ball_dim0.
by rewrite -ball_normE/=.
Qed.

Lemma cst_continuous_eq {T U : topologicalType} (f : T -> U) :
  (exists x : U, f = (fun=>x) ) -> continuous f.
Proof. move=>[x ->] y; apply: cst_continuous. Qed.

Lemma row_mx_norm (T : numDomainType) p m n 
  (M1 : 'M[T]_(p.+1,m.+1)) (M2 : 'M[T]_(p.+1,n.+1)) :
    mx_norm (row_mx M1 M2) = maxr (mx_norm M1) (mx_norm M2).
Proof.
rewrite /mx_norm; apply/le_anti/andP; split.
rewrite (bigmax_eq_arg _ (ord0,ord0))// =>[|i _]; last by rewrite -num_le//=.
set i := [arg max_(i > (ord0, ord0))`|row_mx M1 M2 i.1 i.2|%:nng]%O : 'I_p.+1 * 'I_(m.+1 + n.+1).
case: i=>a b/=; rewrite -(splitK b); case: (fintype.split b)=>/= c;
rewrite ?row_mxEl ?row_mxEr num_le_maxr; apply/orP; [left|right];
rewrite -num_abs_le//; apply/bigmax_geP; right;
by exists (a,c)=>//=; rewrite -num_le/= normr_id.
rewrite num_le_maxl; apply/andP; split;
rewrite (bigmax_eq_arg _ (ord0,ord0))// =>[|i _].
2,4: by rewrite -num_le//=. all: rewrite -num_abs_le//.
set i := [arg max_(i > (ord0, ord0))`|M1 i.1 i.2|%:nng]%O.
have: `|(`|M1 i.1 i.2|%:nng)%:num|%:nng <= `|row_mx M1 M2 
  (i.1,lshift n.+1 i.2).1 (i.1,lshift _ i.2).2|%:nng
  by rewrite/= row_mxEl -num_le/= normr_id.
by apply/bigmax_sup.
set i := [arg max_(i > (ord0, ord0))`|M2 i.1 i.2|%:nng]%O.
have: `|(`|M2 i.1 i.2|%:nng)%:num|%:nng <= `|row_mx M1 M2 
  (i.1,rshift m.+1 i.2).1 (i.1,rshift _ i.2).2|%:nng
  by rewrite/= row_mxEr -num_le/= normr_id.
by apply/bigmax_sup.
Qed.

Lemma mx_norm11 (T : numDomainType) (M : 'M[T]_1) :
  `|M| = `|M ord0 ord0|.
Proof.
rewrite {1}/normr/= mx_normE.
set i0 := (ord0,ord0) : 'I_1 * 'I_1.
have ->: \big[maxr/0%:nng]_i `|M i.1 i.2|%:nng = 
  maxr `|M i0.1 i0.2|%:nng 0%:nng.
  by apply: big_card1E; rewrite card_prod card_ord mul1n.
by rewrite max_l -?num_le//=.
Qed.

Lemma mxnorm_le_alter (T : numDomainType) m n (x : 'M[T]_(m.+1,n.+1))
  (y : T) : `|x| <= y <-> forall i, `|x i.1 i.2| <= y.
Proof.
case E: (y >= 0).
have -> : y = (NngNum E)%:num by [].
rewrite -mx_normEV /mx_norm; split; last first.
move=>H. rewrite num_le; apply/bigmax_leP=>/=; split.
by rewrite -num_le/=. by move=>i _; move: (H i); rewrite -num_le.
by rewrite num_le=>/bigmax_leP[] _ H i; move: (H i); rewrite -num_le/==>P; apply P.
split=>H. by move: (le_trans (normr_ge0 _) H); rewrite E.
move: (H (ord0,ord0))=>/= H1. by move: (le_trans (normr_ge0 _) H1); rewrite E.
Qed.

End mx_norm_vnorm.
Global Arguments mx_norm_vnorm {K m n}.

Section mxvec_norm.
Variable (R: numDomainType) (m n : nat).
Local Notation M := 'M[R]_(m,n).

Lemma mxvec_norm (x : M) : mx_norm x = mx_norm (mxvec x).
Proof.
case: m x=>[x|]; last case: n=>[m' x|n' m' x].
1,2: by rewrite !mx_dim0 ?linear0 !mx_norm0.
apply/le_anti/andP; split; rewrite /normr/=/mx_norm;
rewrite (bigmax_eq_arg _ (ord0, ord0))// ?ord1 ?num_le.
2,4: by move=>i _; rewrite/= -num_le/=.
by rewrite -mxvecE; apply: (le_trans _ (@le_bigmax_cond _ _ _ _ 
  (ord0,(mxvec_index [arg max_(i > (ord0, ord0))`|x i.1 i.2|%:nng]%O.1
  [arg max_(i > (ord0, ord0))`|x i.1 i.2|%:nng]%O.2)) _ _ _)).
set k := [arg max_(i > (ord0, ord0))`|mxvec x i.1 i.2|%:nng]%O.2 : 'I_(m'.+1*n'.+1).
case/mxvec_indexP: k => i j /=; rewrite (mxvecE x i j).
by apply: (le_trans _ (@le_bigmax_cond _ _ _ _ (i,j) _ _ _)).
Qed.

Lemma mxvec_normV x : mx_norm (vec_mx x : M) = mx_norm x.
Proof. by rewrite -{2}(vec_mxK x) mxvec_norm. Qed.

Lemma mx_normrE (x : 'M[R]_(m,n)) :
  mx_norm x = \big[maxr/0]_ij `| x ij.1 ij.2|.
Proof.
rewrite /mx_norm; apply/esym.
elim/big_ind2 : _ => //= a a' b b' ->{a'} ->{b'}.
case: (leP a b) => ab; by [rewrite max_r | rewrite max_l // ltW].
Qed.

Lemma mx_set_trivial (x : set M) :
  (m == 0%N) || (n == 0%N) -> x = set0 \/ x = setT.
Proof.
move=>/orP[/eqP/esym P1|/eqP/esym P1].
case: m / P1 x=>x. 2: case: n / P1 x=>x.
all: move: (EM (x 0))=>[]Px; [right|left];
by rewrite predeqE=>y; rewrite mx_dim0/=.
Qed.

Lemma mx_setT_trivial (x : M) :
  (m == 0%N) || (n == 0%N) -> [set x] = setT.
Proof.
move=>/orP[/eqP/esym P1|/eqP/esym P1].
case: m / P1 x=>x. 2: case: n / P1 x=>x.
all: by rewrite predeqE=>y; rewrite !mx_dim0/=.
Qed.

Lemma mx_set_trivial1 (x : set M) :
  (m == 0%N) || (n == 0%N) -> x = set0 \/ x = [set 0].
Proof.
move=>H; move: (mx_set_trivial x H)=>[]; [left|right]=>//.
by rewrite b mx_setT_trivial.
Qed.

End mxvec_norm.

(* show that mx norms are equivalent *)
Section mxvec_continuous.
Variable (R : numFieldType) (m n : nat).

Lemma vec_mx_continuous : continuous (@vec_mx R m n).
Proof.
move=> x s/= /nbhs_ballP [/=e egt0 Pb]; apply/nbhs_ballP.
exists e =>//=; move=> y /= Pxy.
apply (Pb (vec_mx y)); move: Pxy; clear Pb.
case: m x s y=>[x _ y _|]; last case: n=>[m' x _ y _|n' m' x s y].
1,2: by apply: ball_dim0; rewrite eqxx.
by rewrite -!ball_normE/= -linearB/= -!mx_normEV mxvec_normV.
Qed.

Lemma mxvec_continuous : continuous (@mxvec R m n).
Proof.
move=> x s/= /nbhs_ballP [/=e egt0 Pb];
apply/nbhs_ballP; exists e =>//=;
move=> y /= Pxy; apply (Pb (mxvec y)); move: Pxy; clear Pb.
case: m x s y=>[x _ y _|]; last case: n=>[m' x _ y _|n' m' x s y].
1,2: by apply: ball_dim0; rewrite ?muln0 ?mul0n eqxx.
by rewrite -!ball_normE/= -{1}(mxvecK x) -{1}(mxvecK y) 
  -linearB/= -!mx_normEV mxvec_normV.
Qed.

Lemma mxvec_open_set (A: set 'M[R]_(m,n)) :
  open A <-> open (mxvec @` A).
Proof.
rewrite !openE; split=>/=.
move=>P1 y/= [x Px eqxy]; move: (P1 x Px) =>/=; rewrite /interior.
move/nbhs_ballP=>[/=e egt0 Pb]; apply/nbhs_ballP.
exists e=>// z/= Pz; exists (vec_mx z); last by rewrite vec_mxK.
by apply Pb; move: Pz; rewrite !mxball_normE/= muln_eq0 
  -(mxvecK x) -linearB/= mxvec_normV eqxy.
move=>P1 y/= Py. 
have P3: (exists2 x : 'M_(m, n), A x & mxvec x = mxvec y) by exists y.
move: (P1 (mxvec y) P3); rewrite /interior.
move/nbhs_ballP=>[/=e egt0 Pb]; apply/nbhs_ballP.
exists e=>// z/= Pz; move: Pz (Pb (mxvec z)).
rewrite !mxball_normE/= muln_eq0 -linearB/= mxvec_norm=>P4 P5.
by move: (P5 P4)=>[t Pt] /eqP; rewrite (inj_eq (can_inj mxvecK))=>/eqP <-.
Qed.

Lemma mxvec_setN (A: set 'M[R]_(m,n)) : 
  ~` [set mxvec x | x in A] = [set mxvec x | x in ~` A].
Proof.
rewrite seteqP; split=>x/=; rewrite -forall2NP.
move=>/(_ (vec_mx x)); rewrite vec_mxK =>[[|//]].
by exists (vec_mx x)=>//; rewrite vec_mxK.
move=>[y Py eqxy] z; case E: (y == z).
left; by move/eqP: E=><-.
by right; rewrite -eqxy=>/eqP; rewrite (inj_eq (can_inj mxvecK)) eq_sym E.
Qed.

Lemma mxvec_closed_set (A: set 'M[R]_(m,n)) :
  closed A <-> closed (mxvec @` A).
Proof.
split. by rewrite -openC mxvec_open_set -closedC -{2}(setCK A) -mxvec_setN.
by rewrite -openC mxvec_setN -mxvec_open_set -closedC setCK.
Qed.

Lemma mx_set_compact_trivial (x : set 'M[R]_(m,n)) :
  (m == 0%N) || (n == 0%N) -> compact x.
Proof.
move=>/(mx_set_trivial1 x)[->|->]. apply: compact0. apply: compact_set1.
Qed.

Lemma mx_set_closed_trivial (x : set 'M[R]_(m,n)) :
  (m == 0%N) || (n == 0%N) -> closed x.
Proof.
move=>/(mx_set_trivial x)[->|->]. apply: closed0. apply: closedT.
Qed.

Lemma mx_set_open_trivial (x : set 'M[R]_(m,n)) :
  (m == 0%N) || (n == 0%N) -> open x.
Proof.
move=>/(mx_set_trivial x)[->|->]. apply: open0. apply: openT.
Qed.

End mxvec_continuous.

Lemma normv_snum_subproof (R : numDomainType) (V : lmodType R) (nv : vnorm V) 
  (x : V) : Signed.spec 0 ?=0 >=0 (nv x).
Proof. by rewrite /= normv_ge0. Qed.

Canonical normv_snum (R : numDomainType) (V : lmodType R) (nv : vnorm V) 
  (x : V) := Signed.mk (normv_snum_subproof nv x).

(* non-degenerated, at least 1*1 dim *)
Section MxNormFieldND.
Variable (R: numFieldType) (m n : nat).
Local Notation M := 'M[R]_(m.+1,n.+1).
Variable (mnorm : vnorm [lmodType R of M]).

Let mnorm_max := (\big[maxr/0%:nng]_i (mnorm (delta_mx i.1 i.2))%:nng)%:num.
Let mnorm_elem i := ((mnorm (delta_mx i.1 i.2))%:nng)%:num.
Let mxnorm_elem (x : M) i j := (`|x i j|%:nng)%:num.
Let R0 := (0 : R)%:nng%:num.

Lemma mnorm_ubounded_ND : exists2 c : R, 0 < c & forall x, mnorm x <= c * `|x|.
Proof.
exists ((m.+1 * n.+1)%:R * mnorm_max); last first.
move=>x; rewrite {1}(matrix_sum_delta x) pair_big/=.
apply: (le_trans (normv_sum _ _ _)).
have <-: \sum_(i: 'I_m.+1 * 'I_n.+1) (mnorm_max * `|x|) = (m.+1 * n.+1)%:R * mnorm_max * `|x|.
by rewrite sumr_const card_prod !card_ord -mulr_natl mulrA.
apply: ler_sum=>/= i _; rewrite normvZ mulrC; apply ler_pM.
by apply normv_ge0. by apply normr_ge0.
suff: mnorm_elem i <= mnorm_max by [].
rewrite /mnorm_elem /mnorm_max num_le; by apply: le_bigmax_cond.
suff: mxnorm_elem x i.1 i.2 <= `|x|. by [].
rewrite /mxnorm_elem -mx_normEV mx_normE num_le.
by apply: le_bigmax_cond.
apply mulr_gt0. by rewrite ltr0n.
suff: R0 < mnorm_max. by [].
rewrite /mnorm_max /R0 num_lt. apply/bigmax_gtP. right.
exists (ord0, ord0)=>//=.
rewrite -num_lt/= lt_def normv_ge0 andbT.
have: (delta_mx ord0 ord0 != (0 : M)).
apply/negP=>/eqP/matrixP/(_ ord0 ord0). rewrite !mxE !eqxx/=.
move/eqP. apply/negP. by apply oner_neq0.
apply contraNN. by move/eqP/normv0_eq0=>->.
Qed.

Lemma open_mxnorm_gt (y : R) : open [set x : M | `|x| > y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0.
apply/nbhs_ballP; exists (`|x| - y) => // z.
rewrite -ball_normE/= ltrBrDl -ltrBrDr=>P.
apply (lt_le_trans P). rewrite -{1}(normrN x).
move: (lerB_normD (-x) (x-z)).
by rewrite addKr !normrN.
Qed.

Lemma open_mxnorm_lt (y : R) : open [set x : M | `|x| < y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0.
apply/nbhs_ballP; exists (y - `|x|) => // z.
rewrite -ball_normE/= ltrBrDl=>P.
apply: (le_lt_trans _ P).
move: (ler_normD (-x) (x-z)).
by rewrite addKr !normrN.
Qed.

Lemma closed_mxnorm_le (y : R) : closed [set x : M | `|x| <= y].
Proof.
case E: (y \is Num.real).
rewrite (_ : mkset _ = ~` [set x | `| x | > y]).
rewrite closedC. apply open_mxnorm_gt.
rewrite predeqE => x /=; split=>[|/negP].
move=>P1; apply/negP; move: P1.
1,2: by rewrite real_ltNge// negbK.
rewrite (_ : mkset _ = set0); first by apply: closed0.
rewrite predeqE => x /=; split=>[P1|//].
by move: (le_trans (normr_ge0 _) P1)=>/ger0_real; rewrite E.
Qed.

Lemma closed_mxnorm_sphere (y : R) : closed [set x : M | `|x| = y].
Proof.
case E: (y \is Num.real).
rewrite (_ : mkset _ = ~` [set x | `| x | > y] `&` ~` [set x | `| x | < y]).
apply closedI; rewrite closedC. apply open_mxnorm_gt. apply open_mxnorm_lt.
rewrite predeqE => x /=; split; first by move=>->; rewrite !ltxx.
move=>[/negP P1 /negP P2].
move: P1 P2; rewrite !real_ltNge ?real1// !negbK=>/le_gtF P1.
by rewrite le_eqVlt P1 orbF=>/eqP <-.
rewrite (_ : mkset _ = set0); first by apply: closed0.
rewrite predeqE => x /=; split=>[P1|//].
by move: E; rewrite -P1 ger0_real.
Qed.

Lemma continuous_mnorm_ND : continuous mnorm.
Proof.
move: mnorm_ubounded_ND => [c cgt0 mnormb].
move=> x s/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. exists (e / c) =>//=; first by apply divr_gt0.
move=> y /= Pxy. apply (Pb (mnorm y)). move: Pxy. 
rewrite mx_norm_ball /ball /= => P1.
apply (le_lt_trans (lev_dist_dist x y)). 
apply (le_lt_trans (mnormb (x - y))).
by rewrite mulrC -ltr_pdivlMr.
Qed.

Let R1 := (1 : R)%:nng%:num.

Lemma mxnorm_sphere_neq0_vint : (mnorm @` [set x : M | `|x| = 1%:R]) !=set0.
Proof.
exists (mnorm (const_mx 1))=>/=. exists (const_mx 1)=>//.
have ->: 1%:R = R1 by [].
rewrite /normr/=/mx_norm.
apply/le_anti; apply/andP; split; rewrite /R1 num_le.
by apply/bigmax_leP; split=>[|i _]; rewrite -num_le/=// mxE normr1.
by apply/bigmax_geP=>/=; right; exists (ord0,ord0)=>//; rewrite -num_le/= mxE normr1.
Qed.
End MxNormFieldND.

(* we prove the property without assumption of non-degenerate *)
(* though this is trivial but with .+1 are difficult to use for e.g. vectType *)
Section MxNormFieldEqual.
Variable (R: numFieldType) (m n : nat).
Local Notation M := 'M[R]_(m,n).
Variable (mnorm : vnorm [lmodType R of M]).

Lemma mnorm_ubounded : exists2 c : R, 
  0 < c & forall x : M, mnorm x <= c * mx_norm x.
Proof.
case: m mnorm=>[mnorm'|m']; last case: n=>[mnorm'|n' mnorm'].
1,2: by exists 1=>// x; rewrite mx_dim0 !normv0 mul1r.
exact: mnorm_ubounded_ND.
Qed.

Let cu := projT1 (cid2 mnorm_ubounded).
Let cu_gt0 : cu > 0.
Proof. by move: (projT2 (cid2 mnorm_ubounded))=>[]. Qed.
Let cuP : forall x, mnorm x <= cu * mx_norm x.
Proof. by move: (projT2 (cid2 mnorm_ubounded))=>[]. Qed.
Let cuPV : forall x, mnorm x / cu <= mx_norm x.
Proof. by move=>x; rewrite ler_pdivrMr// mulrC. Qed.

Lemma open_mnorm_gt (y : R) : open [set x : M | mnorm x > y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0.
apply/nbhs_ballP. exists ((mnorm x - y)/cu)=>/=[]; first by rewrite divr_gt0.
move=>z/mxball_normE/orP[/orP[]/=P|].
1,2: by move: xDy_gt0; rewrite !mx_dim0C ?P// ?orbT// subr_gt0.
move=>P/=; move: (le_lt_trans (cuPV _) P).
rewrite ltr_pM2r ?invr_gt0// ltrBrDl addrC -ltrBrDl.
by move=>P1; move: (lt_le_trans P1 (levB_dist _ _)); rewrite subKr.
Qed.

Lemma open_mnorm_lt (y : R) : open [set x : M | mnorm x < y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0.
apply/nbhs_ballP. exists ((y - mnorm x)/cu)=>/=[]; first by rewrite divr_gt0.
move=>z/mxball_normE/orP[/orP[]/=P|].
1,2: by move: xDy_gt0; rewrite !mx_dim0C ?P// ?orbT// subr_gt0.
move=>P/=; move: (le_lt_trans (cuPV _) P).
rewrite ltr_pM2r ?invr_gt0// ltrBrDl.
by move=>P1; move: (le_lt_trans (lev_normB _ _) P1); rewrite subKr.
Qed.

Lemma closed_mnorm_le (y : R) : closed [set x : M | mnorm x <= y].
Proof.
case E: (y \is Num.real).
rewrite (_ : mkset _ = ~` [set x | mnorm x > y]).
rewrite closedC. apply open_mnorm_gt.
rewrite predeqE => x /=; split=>[|/negP].
move=>P1; apply/negP; move: P1.
1,2: by rewrite real_ltNge// negbK.
rewrite (_ : mkset _ = set0); first by apply: closed0.
rewrite predeqE => x /=; split=>[/ler_real|//].
by rewrite E normv_real.
Qed.

Lemma closed_mnorm_ge (y : R) : closed [set x : M | y <= mnorm x].
Proof.
case E: (y \is Num.real).
rewrite (_ : mkset _ = ~` [set x | mnorm x < y]).
rewrite closedC. apply open_mnorm_lt.
rewrite predeqE => x /=; split=>[|/negP].
move=>P1; apply/negP; move: P1.
1,2: by rewrite real_ltNge// negbK.
rewrite (_ : mkset _ = set0); first by apply: closed0.
rewrite predeqE => x /=; split=>[/ler_real|//].
by rewrite E normv_real.
Qed.

Lemma closed_mnorm_sphere (y : R) : closed [set x : M | mnorm x = y].
Proof.
case E: (y \is Num.real).
rewrite (_ : mkset _ = ~` [set x | mnorm x > y] `&` ~` [set x | mnorm x  < y]).
apply closedI; rewrite closedC. apply open_mnorm_gt. apply open_mnorm_lt.
rewrite predeqE => x /=; split; first by move=>->; rewrite !ltxx.
move=>[/negP P1 /negP P2].
move: P1 P2; rewrite !real_ltNge ?real1// !negbK=>/le_gtF P1.
by rewrite le_eqVlt P1 orbF=>/eqP <-.
rewrite (_ : mkset _ = set0); first by apply: closed0.
rewrite predeqE => x /=; split=>[P1|//].
by move: E; rewrite -P1 ger0_real.
Qed.

Lemma continuous_mnorm : continuous mnorm.
Proof.
case: m mnorm=>[mnorm'|m']; last case: n=>[mnorm'|n' mnorm']; last exact: continuous_mnorm_ND.
1,2:by apply: cst_continuous_eq; exists 0; apply/funext=>x; rewrite mx_dim0 normv0.
Qed.

Lemma mxcvg_mnorm (f : M ^nat) (a: M) : 
  f --> a -> (fun x=> mnorm (f x)) --> (mnorm a).
Proof. by apply: continuous_cvg; apply: continuous_mnorm. Qed.

Lemma is_mxcvg_mnorm (f : M ^nat) : cvg f -> cvg (mnorm \o f).
Proof. by have := cvgP _ (mxcvg_mnorm _); apply. Qed.

End MxNormFieldEqual.

(* n-dim number : vectType R, f *)
(* general theory over extNum; R, R[i] are both extNum. *)
Module ExtNum.

Record mixin_of (R : realType) (C : numFieldType)
  := Mixin {
  r2c : {rmorphism R -> C};
  c2r : C -> R;
  _ : {mono r2c : x y / x <= y};
  _ : cancel r2c c2r;
  _ : {in Num.real, cancel c2r r2c};
  _ : continuous c2r;
  _ : forall (a : R) (b c : C), 
      c2r ((r2c a) * b + c) = a * (c2r b) + c2r c;
  _ : forall a : C, compact [set x : C | `|x| <= a];
  (* _ : closed [set x : C | 0 <=  x]; *)
}.

Section ClassDef.
Variable (R : realType).
Set Primitive Projections.
Record class_of C := Class {
  base : Num.NumField.class_of C;
  mixin : @mixin_of R (Num.NumField.Pack base);
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> Num.NumField.class_of.

Structure type (phR : phant R) := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c.

Definition pack b0 (m0 : mixin_of R (@Num.NumField.Pack T b0)) :=
  fun bT b & phant_id (@Num.NumField.class bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
(* Definition normedZmodType := @Num.NormedZmodule.Pack R phR cT class. *)
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition numDomainType := @Num.NumDomain.Pack cT class.
Definition numFieldType := @Num.NumField.Pack cT class.
Definition fieldType := @GRing.Field.Pack cT class.
Definition normedZmodType := NormedZmodType numDomainType cT class.
Definition porder_fieldType := @GRing.Field.Pack porderType class.
Definition normedZmod_fieldType := @GRing.Field.Pack normedZmodType class.
Definition numDomain_fieldType := @GRing.Field.Pack numDomainType class.
Definition numField_fieldType := @GRing.Field.Pack numFieldType class.
End ClassDef.

Module Exports.

Coercion base : class_of >-> Num.NumField.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> Num.NumField.type.
Canonical numFieldType.
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
Canonical porder_fieldType.
Canonical normedZmod_fieldType.
Canonical numDomain_fieldType.
Canonical numField_fieldType.
Notation extNumType R := (type (Phant R)).
Notation ExtNumType R T m := (@pack _ (Phant R) T _ m _ _ id _ id).
Notation ExtNumMixin := Mixin.
Notation "[ 'extNumType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'extNumType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'extNumType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'extNumType'  R  'of'  T ]") : form_scope.

End Exports.
End ExtNum.
Import ExtNum.Exports.


Module ExtNumTopology.
Import numFieldNormedType.Exports Num.Def Num.Theory.

Section ExtNumInternal.
Context {R: realType} {C : extNumType R}.

Canonical extNum_pointedType := [pointedType of C for [numFieldType of C]].
Canonical extNum_filteredType := [filteredType C of C for [numFieldType of C]].
Canonical extNum_topologicalType := [topologicalType of C for [numFieldType of C]].
Canonical extNum_uniformType := [uniformType of C for [numFieldType of C]].
Canonical extNum_pseudoMetricType := [pseudoMetricType C of C for [numFieldType of C]].
Canonical extNum_pseudoMetricNormedZmodType := [pseudoMetricNormedZmodType C of C for [numFieldType of C]].
Canonical extNum_normedModType := [normedModType C of C for [numFieldType of C]].

Definition r2c : {rmorphism R -> C} := ExtNum.r2c (@ExtNum.mixin R C (@ExtNum.class R _ C)).
Definition c2r : C -> R := ExtNum.c2r (@ExtNum.mixin R C (@ExtNum.class R _ C)).
Lemma ler_r2c : {mono r2c : x y / x <= y}.
Proof. by rewrite /r2c; case: C=>?[?[]]. Qed.
Lemma r2cK : cancel r2c c2r.
Proof. by rewrite /r2c/c2r; case: C=>?[?[]]. Qed.
Lemma r2c_inj : injective r2c. Proof. exact: (can_inj r2cK). Qed.
Lemma c2rK : {in Num.real, cancel c2r r2c}.
Proof. by rewrite /r2c/c2r; case: C=>?[?[]]. Qed.
Lemma c2r_continuous : continuous c2r.
Proof. 
suff: continuous (ExtNum.c2r (@ExtNum.mixin R C (@ExtNum.class R _ C))) by [].
by case: C=>?[?[]].
Qed.
Lemma c2rP (a : R) (b c : C) : c2r ((r2c a) * b + c) = a * (c2r b) + c2r c.
Proof. by move: a b c; rewrite /r2c/c2r; case: C=>?[?[]]. Qed.
Lemma c2r_is_additive : additive c2r.
Proof. by move=>a b; rewrite -[in RHS]mulN1r [RHS]addrC -c2rP rmorphN1 mulN1r addrC. Qed.
Canonical c2r_additive := Additive c2r_is_additive.
Lemma r2c0 : r2c 0 = 0. Proof. exact: rmorph0. Qed.
Lemma r2c1 : r2c 1 = 1. Proof. by exact: rmorph1. Qed.
Lemma c2r0 : c2r 0 = 0. Proof. exact: raddf0. Qed.
Lemma c2r1 : c2r 1 = 1. Proof. by rewrite -[RHS]r2cK rmorph1. Qed.
Lemma c2rN : {morph c2r : u / -u}. Proof. exact: raddfN. Qed.
Lemma c2rB : {morph c2r : u v / u - v}. Proof. exact: raddfB. Qed.
Lemma c2rD : {morph c2r : u v / u + v}. Proof. exact: raddfD. Qed.
Lemma c2rMn n : {morph c2r : u / u *+ n}. Proof. exact: raddfMn. Qed.
Lemma c2rMNn n : {morph c2r : u / u *- n}. Proof. exact: raddfMNn. Qed.
Lemma c2rZ (a : R) (b : C) : c2r ((r2c a) * b) = a * c2r b.
Proof. by rewrite -[RHS]addr0 -c2r0 -c2rP addr0. Qed.

Lemma extNum_bounded_compact (a : C) : compact [set x : C | `|x| <= a].
Proof. by move: (@ExtNum.mixin R C (@ExtNum.class R _ C))=>P; case: P. Qed.

End ExtNumInternal.

Section ExtNumTheory.
Context {R: realType} {C : extNumType R}.

Lemma ltr_r2c : {mono @r2c R C : x y / x < y}.
Proof. by move=>x y; rewrite !lt_def ler_r2c (inj_eq r2c_inj). Qed.
Lemma r2c_ge0 x : (0 <= r2c x :> C) = (0 <= x).
Proof. by rewrite -(@ler_r2c _ C) rmorph0. Qed.
Lemma r2c_gt0 x : (0 < r2c x :> C) = (0 < x).
Proof. by rewrite -ltr_r2c rmorph0. Qed.
Lemma r2c_le0 x : (r2c x <= 0 :> C) = (x <= 0).
Proof. by rewrite -(@ler_r2c _ C) rmorph0. Qed.
Lemma r2c_lt0 x : (r2c x < 0 :> C) = (x < 0).
Proof. by rewrite -ltr_r2c rmorph0. Qed.

Lemma ler_c2r x y : x <= y -> @c2r _ C x <= c2r y.
Proof. by rewrite -subr_ge0=>H; rewrite -subr_ge0 -c2rB -r2c_ge0 c2rK// ger0_real. Qed.
Lemma ltr_c2r x y : x < y -> @c2r _ C x < c2r y.
Proof. by rewrite -subr_gt0=>H; rewrite -subr_gt0 -c2rB -r2c_gt0 c2rK// gtr0_real. Qed.
Lemma c2r_ge0 (x : C) : 0 <= x -> 0 <= c2r x.
Proof. by move=>H; rewrite -r2c_ge0 c2rK// ger0_real. Qed.
Lemma c2r_gt0 (x : C) : 0 < x -> 0 < c2r x.
Proof. by move=>H; rewrite -r2c_gt0 c2rK// gtr0_real. Qed.

Lemma r2c_real (r : R) : (r2c r : C) \is Num.real.
Proof. by rewrite realE r2c_ge0 r2c_le0 -realE num_real. Qed.

Lemma r2c_norm x : `|r2c x : C| = r2c `|x|.
Proof.
case E : (0 <= x); first by rewrite !ger0_norm// r2c_ge0.
move: E=>/negP/negP; rewrite -real_ltNge// ?num_real// =>Px.
by rewrite !ler0_norm ?rmorphN//; apply/ltW=>//; rewrite r2c_lt0.
Qed.

Lemma r2c_continuous : continuous (r2c : {rmorphism R -> C}).
Proof.
move=>x y/=; rewrite /nbhs/= /nbhs/==>[[]e/=egt0 P].
exists (c2r e)=>/=. by rewrite -ltr_r2c rmorph0 c2rK// gtr0_real.
move=>z/==>Pxz; apply: (P (r2c z)); rewrite/= -rmorphB r2c_norm.
by move: Pxz; rewrite -ltr_r2c c2rK// gtr0_real.
Qed.

Lemma extNum_compact_minmax (S : (set C)) : 
  S `<=` [set` Num.real] (* real *)
  -> compact S -> S !=set0 -> (* compact & non-empty *)
    (exists2 x, S x & (forall y, S y -> y <= x)) /\
    (exists2 x, S x & (forall y, S y -> x <= y)).
Proof.
move=>Sr Sc S0.
have SrE : S = r2c @` (c2r @` S).
rewrite predeqE=>x/=; split.
move=>Sx. exists (c2r x). by exists x. by rewrite c2rK//; apply Sr.
by move=>[y][z] Sz <- <-; rewrite c2rK//; apply Sr.
have S1 : compact (c2r @` S). apply/continuous_compact=>//. 
apply/continuous_subspaceT=>x ?. apply/c2r_continuous.
have S2: [set c2r x | x in S] !=set0.
by move: S0=>[x Px]; exists (c2r x)=>/=; exists x.
split.
move: (compact_max S1 S2)=>[x Px1 Px2].
2: move: (compact_min S1 S2)=>[x Px1 Px2].
all: move: Px1=>/=[y Py Py1]; exists y=>// z Pz.
all: move: (Px2 (c2r z))=>/==>P1.
all: rewrite -[z]c2rK; last by apply: Sr.
all: rewrite -[y]c2rK; last by apply: Sr.
all: by rewrite Py1 ler_r2c; apply P1; exists z.
Qed.

Lemma extNum_compact_max (S : (set C)) : 
  S `<=` [set` Num.real] (* real *)
  -> compact S -> S !=set0 -> (* compact & non-empty *)
    (exists2 x, S x & (forall y, S y -> y <= x)).
Proof. by move=>P1 P2 P3; move: (extNum_compact_minmax P1 P2 P3)=>[]. Qed.

Lemma extNum_compact_min (S : (set C)) : 
  S `<=` [set` Num.real] (* real *)
  -> compact S -> S !=set0 -> (* compact & non-empty *)
    (exists2 x, S x & (forall y, S y -> x <= y)).
Proof. by move=>P1 P2 P3; move: (extNum_compact_minmax P1 P2 P3)=>[]. Qed.

Lemma extNum_complete (F : set (set C)) : ProperFilter F -> cauchy F -> cvg F.
Proof. apply: bounded_compact_complete. exact: extNum_bounded_compact. Qed.

Canonical extNum_completeType := CompleteType C (@extNum_complete).
Canonical extNum_CompleteNormedModule := [completeNormedModType C of C].

Lemma ethausdorff : hausdorff_space C. Proof. apply: norm_hausdorff. Qed.

Lemma etclosed_real : closed [set x : C | x \is Num.real].
Proof.
rewrite closure_id closureEcvg predeqE=>x/=; split=>[xr|[G PG[] Gx] P].
  exists (at_point x); first by exact: at_point_filter.
  split; last by move=>a/=/(_ _ xr); rewrite/at_point.
  rewrite/cvg_to/==>t/=; rewrite {2}/nbhs/at_point/=.
  by move=>[e]/= egt0; rewrite/= ball_normE=>/(_ x)P; apply/P/ballxx.
have P1: c2r @ G --> c2r x 
  by apply: continuous_cvg=>//; apply: c2r_continuous.
suff P2: G `<=` r2c @ (c2r @ G).
  have P3: r2c @ (c2r @ G) --> x by apply: (subset_trans Gx P2).
  have P4: r2c @ (c2r @ G) --> (r2c (c2r x) : C).
    by apply: continuous_cvg=>//; apply: r2c_continuous.
  have: close x (r2c (c2r x)) by apply: (cvg_close P3 P4).
  by move=>/(close_eq ethausdorff)->; apply: r2c_real.
move=>a/=; rewrite/nbhs/=/nbhs/==>Ga.
have Gr: G [set` Num.real] by apply: P=>/=.
move: (@filterI _ _ PG _ _ Ga Gr).
apply: filterS=>t/=[] P5 P6; rewrite c2rK//.
Qed.

Lemma extNum_ltr_add_invr (y x : C) : y < x -> exists k, y + k.+1%:R^-1 < x.
Proof.
rewrite -subr_gt0=>P1.
have P2 : 0 < c2r (x - y) by rewrite -ltr_r2c c2rK ?rmorph0// gtr0_real.
by move: (ltr_add_invr P2)=>[k]; rewrite add0r -ltr_r2c c2rK ?gtr0_real// 
  fmorphV rmorphMn rmorph1 ltrBrDl=>P; exists k.
Qed.

Lemma extNum_archi (x : C) : 0 < x -> exists k, k.+1%:R^-1 < x.
Proof. by move=>/extNum_ltr_add_invr[k Pk]; exists k; rewrite add0r in Pk. Qed.

(* have convergence subsequence *)
Lemma extNum_bounded_subsvg (f : nat -> C) b : (forall i, `|f i| <= b) -> 
  exists (h: nat -> nat), (forall n, (h n.+1 > h n)%N) /\ cvg (f \o h).
Proof.
move=>Pb; move: (@extNum_bounded_compact _ _ b)=>P1.
apply: (cluster_subsvg _ P1 _)=>[|i//=]; apply: extNum_archi.
Qed.

End ExtNumTheory.

Section matrix_CompleteNormedModule.
Variables (R: realType) (C : extNumType R).

Canonical matrix_completeNormedModule (m n : nat) :=
  [completeNormedModType R of 'M[R]_(m.+1, n.+1)].

Definition extNumMx_cauchy_seq  m n (u: nat -> 'M[C]_(m,n)) := 
  forall e : C, 0 < e -> exists N : nat, 
    forall s t, (N <= s)%N -> (N <= t)%N -> mx_norm (u s - u t) < e.

End matrix_CompleteNormedModule.

Section ExtNumCvg.
Context {R: realType} {C: extNumType R}.
Context {T : Type} {F : set (set T)} {FF : ProperFilter F}.
Implicit Type (f g: T -> C) (s a b : C).

Lemma etcvg_map f a (V : completeType) (h : C -> V) :
  continuous h -> f @ F --> a -> (h \o f) @ F --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ (f @ F) a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_etcvg_map f (V : completeType) (h : C -> V) :
  continuous h -> cvg (f @ F) -> cvg ((h \o f) @ F).
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (etcvg_map P1 Pa).
Qed.

Lemma etlim_map f (V : completeType) (h : C -> V) :
  hausdorff_space V -> continuous h -> 
    cvg (f @ F) -> lim ((h \o f) @ F) = h (lim (f @ F)).
Proof. by move=>hV ch; move/(etcvg_map ch)/cvg_lim=>/(_ hV). Qed.

Lemma etcvg_mapV (V : completeType) (h : V -> C) (h' : T -> V) (a : V) :
  continuous h -> h' @ F --> a -> (h \o h') @ F --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ (h' @ F) a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_etcvg_mapV (V : completeType) (h : V -> C) (h' : T -> V) :
  continuous h -> cvg (h' @ F) -> cvg ((h \o h') @ F).
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (etcvg_mapV P1 Pa).
Qed.

Lemma etlim_mapV (V : completeType) (h : V -> C) (h' : T -> V) :
  continuous h -> cvg (h' @ F) -> lim ((h \o h') @ F) = h (lim (h' @ F)).
Proof. by move=>ch; move/(etcvg_mapV ch)/cvg_lim=>/(_ ethausdorff). Qed.

End ExtNumCvg.

(* Section ExtNumCvg.
Context {R: realType} {C: extNumType R}.
Implicit Type (f g: nat -> C) (n: nat) (s a b : C).

Lemma etcvg_map f a (V : completeType) (h : C -> V) :
  continuous h -> f --> a -> (h \o f) --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ [filter of f] a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_etcvg_map f (V : completeType) (h : C -> V) :
  continuous h -> cvg f -> cvg (h \o f).
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (etcvg_map P1 Pa).
Qed.

Lemma etlim_map f (V : completeType) (h : C -> V) :
  hausdorff_space V -> continuous h -> cvg f -> lim (h \o f) = h (lim f).
Proof. by move=>hV ch; move/(etcvg_map ch)/cvg_lim=>/(_ hV). Qed.

Lemma etcvg_mapV (V : completeType) (h : V -> C) (h' : nat -> V) (a : V) :
  continuous h -> h' --> a -> (h \o h') --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ [filter of h'] a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_etcvg_mapV (V : completeType) (h : V -> C) (h' : nat -> V) :
  continuous h -> cvg h' -> cvg (h \o h').
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (etcvg_mapV P1 Pa).
Qed.

Lemma etlim_mapV (V : completeType) (h : V -> C) (h' : nat -> V) :
  continuous h -> cvg h' -> lim (h \o h') = h (lim h').
Proof. by move=>ch; move/(etcvg_mapV ch)/cvg_lim=>/(_ ethausdorff). Qed.

End ExtNumCvg. *)

Section ExtNumMono.
Variable (R: realType) (C: extNumType R).

Lemma etclosed_ge (y:C) : closed [set x : C | y <= x].
Proof.
rewrite (_ : mkset _ = (fun x=>x-y) @^-1` ([set` Num.real] `&` c2r @^-1` [set x | 0 <= x ])).
apply: closed_comp=>[x _|]; first by apply: addl_continuous.
apply: closedI. apply/etclosed_real. apply: closed_comp=>[x _|].
apply: c2r_continuous. apply/closed_ge.
rewrite predeqE=>x; rewrite/= -[y <= x]subr_ge0; split=>[P1|[P1]].
by rewrite ger0_real// c2r_ge0. by rewrite -(@ler_r2c _ C) c2rK// r2c0.
Qed.

Lemma etclosed_le (y : C) : closed [set x : C | x <= y].
Proof.
rewrite (_ : mkset _ = (fun x=>-x) @^-1` [set x | -y <= x ]).
apply: closed_comp=>[x _|]; first by apply: opp_continuous.
apply: etclosed_ge.
by rewrite predeqE=>x; rewrite/= lerN2.
Qed.

Lemma etclosed_eq (y : C) : closed [set x : C | x = y].
Proof. exact: closed_eq. Qed.

Lemma etlim_ge_nearF {T : Type}
  {F : set (set T)} {FF : ProperFilter F} (x : C) (u : T -> C) :
    cvg (u @ F) -> (\forall n \near F, x <= u n) -> x <= lim (u @ F).
Proof. by move=> /[swap] /(closed_cvg (>= x))P; apply/P/etclosed_ge. Qed.

Lemma etlim_ge_near (x : C) (u : C ^nat) : 
  cvg u -> (\forall n \near \oo, x <= u n) -> x <= lim u.
Proof. exact: etlim_ge_nearF. Qed.

Lemma etlim_le_nearF {T : Type}
  {F : set (set T)} {FF : ProperFilter F} (x : C) (u : T -> C) :
    cvg (u @ F) -> (\forall n \near F, x >= u n) -> x >= lim (u @ F).
Proof. by move=> /[swap] /(closed_cvg (fun y => y <= x))P; apply/P/etclosed_le. Qed.

Lemma etlim_le_near (x : C) (u : C ^nat) : 
  cvg u -> (\forall n \near \oo, x >= u n) -> x >= lim u.
Proof. exact: etlim_le_nearF. Qed.

Lemma ler_etlim_nearF {T : Type}
  {F : set (set T)} {FF : ProperFilter F} (u v : T -> C) : 
    cvg (u @ F) -> cvg (v @ F) ->
      (\forall n \near F, u n <= v n) -> 
        lim (u @ F) <= lim (v @ F).
Proof.
move=> uv cu cv; rewrite -subr_ge0 -limB=>[|//|]; last by apply uv.
apply: etlim_ge_nearF; first by apply: is_cvgB;[| apply uv].
by apply: filterS cv => n; rewrite subr_ge0.
Qed.

Lemma ler_etlim_near (u_ v_ : C ^nat) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, u_ n <= v_ n) -> lim u_ <= lim v_.
Proof. exact: ler_etlim_nearF. Qed.

Lemma etlim_eq_nearF {T : Type}
  {F : set (set T)} {FF : ProperFilter F} (u v : T -> C) : 
    cvg (u @ F) -> cvg (v @ F) ->
      (\forall n \near F, u n = v n) -> 
        lim (u @ F) = lim (v @ F).
Proof.
move=>cu cv uv. apply/le_anti/andP; split; apply/ler_etlim_nearF=>//;
near=>J; suff ->: u J = v J by []; near: J; apply uv. Unshelve. all: end_near.
Qed.

Lemma etlim_eq_near (u_ v_ : C ^nat) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, u_ n = v_ n) -> lim u_ = lim v_.
Proof. exact: etlim_eq_nearF. Qed.

Lemma etlim_geF {T : Type} {F : set (set T)} 
  {FF : ProperFilter F} (x : C) (u : T -> C) : 
    cvg (u @ F) -> (forall n, x <= u n) -> x <= lim (u @ F).
Proof. move=>P1 P2; apply/etlim_ge_nearF=>//; near=>n; by []. Unshelve. end_near. Qed.

Lemma etlim_ge (x : C) (u : C ^nat) : cvg u -> (forall n, x <= u n) -> x <= lim u.
Proof. exact: etlim_geF. Qed.

Lemma etlim_leF {T : Type} {F : set (set T)} 
  {FF : ProperFilter F} (x : C) (u : T -> C) : 
    cvg (u @ F) -> (forall n, x >= u n) -> x >= lim (u @ F).
Proof. move=>P1 P2; apply/etlim_le_nearF=>//; near=>n; by []. Unshelve. end_near. Qed.

Lemma etlim_le (x : C) (u : C ^nat) : cvg u -> (forall n, u n <= x) -> lim u <= x.
Proof. exact: etlim_leF. Qed.

Lemma ler_etlimF {T : Type}
  {F : set (set T)} {FF : ProperFilter F} (u v : T -> C) :  
  cvg (u @ F) -> cvg (v @ F) ->
    (forall n, u n <= v n) -> 
      lim (u @ F) <= lim (v @ F).
Proof. move=>P1 P2 P3; apply/ler_etlim_nearF=>//; near=>n; by []. Unshelve. end_near. Qed.

Lemma ler_etlim (u_ v_ : C^nat) : cvg u_ -> cvg v_ ->
  (forall n, u_ n <= v_ n) -> lim u_ <= lim v_.
Proof. exact: ler_etlimF. Qed.

Lemma lim_eq {T: Type} {V : topologicalType} {F : set (set T)} (u v : T -> V) :
  u =1 v -> lim (u @ F) = lim (v @ F).
Proof. by move=>/funext->. Qed.

(* Lemma etclosed_real : closed [set x : C | x \is Num.real].
Proof.
rewrite (_ : mkset _ = [set x | x <= 0] `|` [set x | 0 <= x ]).
apply: closedU; [apply: etclosed_le|apply: etclosed_ge].
rewrite predeqE=>x; rewrite/= realE; split=>[/orP[]->|[|]->//].
by right. by left. by rewrite orbT.
Qed. *)

Implicit Type (f g: nat -> C) (n: nat) (s a b : C).

(* to use cauchy_seq for other functions *)
Lemma etcvg_limP f a :
  f --> a <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> `|f n - a| < e.
Proof. exact: cvg_limP. Qed.

Lemma etcvg_subseqP f a : 
  f --> a <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N) -> (f \o h) --> a).
Proof. exact: cvg_subseqP. Qed.

Lemma etcvg_subseqPN f a :
  ~ (f --> a) <-> exists e (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ 0 < e /\ (forall n, `|(f \o h) n - a| >= e).
Proof. exact: cvg_subseqPN. Qed.

Definition etcauchy_seq f := forall e, 0 < e -> exists N, forall i j, 
  (N <= i)%N -> (N <= j)%N -> `| f i - f j | < e.

Lemma etcauchy_seqP f : etcauchy_seq f <-> cvg f.
Proof. exact: cauchy_seqP. Qed.

Definition etcvg_seq f a := forall e, 0 < e -> exists N : nat, 
    forall i, (N <= i)%N -> `| a - f i | < e.

Lemma etcvg_seqP f a : etcvg_seq f a <-> f --> a.
Proof. exact: cvg_seqP. Qed.

(* monotone sequence; can extend to any lattice *)
(* once eventually filter applies to lattice *)
Definition etseq_shift (u_ : C ^nat) := u_ - (fun=>u_ 0%N).
Definition etseq_real (u_ : C ^nat) := forall i, (u_ i) \is Num.real.

Lemma etseq_shiftE (u_ : C ^nat) : etseq_shift u_ = u_ - (fun=>u_ 0%N).
Proof. by []. Qed.
Lemma etseq_shiftEV (u_ : C ^nat) : u_ = etseq_shift u_ + (fun=>u_ 0%N).
Proof. by rewrite etseq_shiftE addrNK. Qed.

Lemma etnondecreasing_shift (u_ : C ^nat) : 
  nondecreasing_seq u_ <-> nondecreasing_seq (etseq_shift u_).
Proof. by split=>H i j /H; rewrite lerD2r. Qed.

Lemma etnondecreasing_shift_real (u_ : C ^nat) : 
  nondecreasing_seq u_ -> etseq_real (etseq_shift u_).
Proof. by move=>H i; rewrite ger0_real// subr_ge0 H. Qed.

Lemma etseq_shift_cvg (u_ : C ^nat) a:
  (etseq_shift u_ --> a) -> u_ --> a + u_ 0%N.
Proof.
move=>P1; rewrite [u_]etseq_shiftEV.
by apply: cvgD=>//; rewrite /etseq_shift !fctE addrNK; apply: cvg_cst.
Qed.

Lemma etseq_shift_is_cvgE (u_ : C ^nat) : cvg (etseq_shift u_) = cvg u_.
Proof. by rewrite /etseq_shift; apply/is_cvgDlE; apply: is_cvgN; apply: is_cvg_cst. Qed.

Lemma etseq_shift_lim (u_ : C ^nat) :
  cvg u_ -> lim u_ = lim (etseq_shift u_) + u_ 0%N.
Proof.
rewrite -etseq_shift_is_cvgE=>/etseq_shift_cvg; 
rewrite cvg_limE=>[[]//|]; apply/norm_hausdorff.
Qed.

Lemma etlim_real (u_ : C ^nat) : etseq_real u_ ->
  cvg u_ -> lim u_ \is Num.real.
Proof. by move=>P; apply: (closed_cvg _ etclosed_real)=>//; exists 0%N=>/=. Qed.

Lemma c2r_cvg_real (u_ : C ^nat) (x : R) : etseq_real u_ ->
  ((c2r \o u_) --> x) -> (u_ --> r2c x).
Proof.
move=>ru cu; have ->: u_ = r2c \o (c2r \o u_) 
  by apply/funext=>i; rewrite !fctE c2rK//.
apply: etcvg_mapV=>//; apply r2c_continuous.
Qed.

Lemma c2r_cvg_realV (u_ : C ^nat) a : 
  u_ --> a -> (c2r \o u_) --> c2r a.
Proof. by move=>cu; apply: etcvg_map=>//; apply: c2r_continuous. Qed.

Lemma etnondecreasing_cvg (u_ : C ^nat) (M : C) :
      nondecreasing_seq u_ -> (forall n : nat, u_ n <= M) -> 
        u_ --> r2c (lim (c2r \o (etseq_shift u_))) + u_ 0%N.
Proof.
move=>nd ub; move: {+}nd {+}nd=>/etnondecreasing_shift P1/etnondecreasing_shift_real P2.
pose v i := c2r ((etseq_shift u_) i).
have cv: cvg v. apply: nondecreasing_is_cvgn.
by move=>n m Pnm; rewrite /v -(@ler_r2c _ C) !c2rK// P1.
exists (c2r (M - u_ 0%N))=>i [x] _ <-. rewrite -(@ler_r2c _ C) /v !c2rK//.
by rewrite lerD2r. by rewrite ger0_real// subr_ge0.
have Pu: u_ = (r2c \o v) + (fun=>u_ 0%N).
by apply/funext=>i; rewrite !fctE /v c2rK// addrNK.
rewrite {1 2}Pu; apply: cvgD; last by apply: cvg_cst.
apply: etcvg_mapV. apply: r2c_continuous. apply: cv.
Qed.

Lemma etnondecreasing_is_cvgn (u_ : C ^nat) (M : C) :
       nondecreasing_seq u_ -> (forall n : nat, u_ n <= M) -> cvg u_.
Proof.
move=>nd ub. apply/cvg_ex; exists (r2c (lim (c2r \o (etseq_shift u_))) + u_ 0%N).
apply: (etnondecreasing_cvg nd ub).
Qed.

Lemma etnonincreasing_cvg (u_ : C ^nat) (M : C) :
      nonincreasing_seq u_ -> (forall n : nat, M <= u_ n) -> 
       u_ --> r2c (lim (c2r \o (etseq_shift u_))) + u_ 0%N.
Proof.
rewrite -nondecreasing_opp=>P1 P2.
have P3 n: (-u_) n <= (-M) by rewrite fctE lerN2.
move: (etnondecreasing_cvg P1 P3)=>/cvgN.
rewrite opprK opprD -rmorphN -limN.
rewrite [in (-u_) 0%N]fctE opprK.
suff ->: (- (c2r \o etseq_shift (- u_))) = (c2r \o etseq_shift u_) by [].
by apply/funext=>i; rewrite/etseq_shift !fctE -c2rN opprB opprK addrC.
apply: is_etcvg_map. apply: c2r_continuous.
by rewrite etseq_shift_is_cvgE; apply: etnondecreasing_is_cvgn.
Qed.

Lemma etnonincreasing_is_cvg (u_ : C ^nat) (M : C) :
       nonincreasing_seq u_ -> (forall n : nat, M <= u_ n) -> cvg u_.
Proof.
rewrite -nondecreasing_opp -is_cvgNE =>P1 P2.
apply: (@etnondecreasing_is_cvgn _ (- M) P1 _)=>n.
by rewrite {1}/GRing.opp/= Num.Theory.lerN2.
Qed.

Lemma etnondecreasing_cvgn_le (u_ : C ^nat) :
       nondecreasing_seq u_ -> cvg u_ -> (forall n : nat, u_ n <= lim u_).
Proof.
move=>nd cu n. move: {+}nd=>/etnondecreasing_shift_real rus.
move: {+}cu; rewrite -etseq_shift_is_cvgE=>cus.
rewrite etseq_shift_lim// -lerBlDr.
suff: (c2r \o (etseq_shift u_)) n <= lim (c2r \o (etseq_shift u_)).
rewrite etlim_map//; last by apply: c2r_continuous.
rewrite/= -[c2r _ <= _]subr_ge0 -c2rB -(@r2c_ge0 _ C) c2rK.
by rewrite subr_ge0 /etseq_shift !fctE.
apply: realB=>//. apply: etlim_real=>//.
apply: nondecreasing_cvgn_le=>[i j leij/=|].
by rewrite ler_c2r//; move: nd=>/etnondecreasing_shift/(_ _ _ leij).
apply: is_etcvg_map=>//; apply: c2r_continuous.
Qed.

Lemma etnonincreasing_cvg_ge (u_ : C ^nat) : 
  nonincreasing_seq u_ -> cvg u_ -> (forall n, lim u_ <= u_ n).
Proof.
rewrite -nondecreasing_opp -is_cvgNE =>P1 P2 n.
rewrite -(opprK u_) limN// lerN2.
by apply etnondecreasing_cvgn_le.
Qed.

Lemma lt_etlim (u : C ^nat) (x : C) : nondecreasing_seq u -> 
  cvg u -> x < lim u -> \forall n \near \oo, x <= u n.
Proof.
move=> ndu cu Ml; have [[n Mun]|/forallNP Mu] := pselect (exists n, x <= u n).
  near=> m; suff : u n <= u m by exact: le_trans.
  by near: m; exists n.+1 => // p q; apply/ndu/ltnW.
have Cn n : comparable x (u n) by apply/(comparabler_trans 
  (lt_comparable Ml))/ge_comparable/etnondecreasing_cvgn_le.
have {}Mu : forall y, x > u y. move=> y. rewrite comparable_ltNge. by apply/negP.
by rewrite comparable_sym.
have : lim u <= x by apply etlim_le_near => //; near=> m; apply/ltW/Mu.
by move/(lt_le_trans Ml); rewrite ltxx.
Unshelve. all: by end_near.
Qed.

Lemma gt_etlim (u : C ^nat) (x : C) : nonincreasing_seq u -> 
  cvg u -> x > lim u -> \forall n \near \oo, x >= u n.
Proof.
rewrite -nondecreasing_opp=>P1 P2.
rewrite -ltrN2 -limN// =>P3.
near=>n. suff: -x <= (-u) n by rewrite fctE lerN2. near: n.
by rewrite near_simpl; apply: lt_etlim=>//; apply: is_cvgN.
Unshelve. end_near.
Qed.

End ExtNumMono.

Definition etsup {R : realType} {C : extNumType R} := @supremum _ C 0.
Definition etinf {R : realType} {C : extNumType R} (E : set C) := - etsup (-%R @` E).

Section SetComparable.
Variable (C : numFieldType).
Implicit Type (E : set C).

Definition set_comparable E := forall x y, E x -> E y -> x >=< y.

Lemma comparable_get E : set_comparable E -> 
  forall x, E x -> x >=< get E.
Proof. by move=>Pc x Ex; move: (getI Ex); apply: Pc. Qed.

Lemma comparable_get_ubound E x : E !=set0 ->
  ubound E x -> x >=< get E.
Proof. move=>[y Py] P. apply ge_comparable. apply P. apply (getI Py). Qed.

Lemma comparablerN (R : numDomainType) (x y : R) :
  (-x >=< -y) = (x >=< y).
Proof. by rewrite !comparablerE opprK addrC -realN opprB. Qed.

Lemma comparablerDl (R : numDomainType) (z x y : R) :
  (x + z >=< y + z) = (x >=< y).
Proof. by rewrite !comparablerE [y+z]addrC addrKA. Qed.

Lemma comparablerDr (R : numDomainType) (z x y : R) :
  (z + x >=< z + y) = (x >=< y).
Proof. by rewrite !comparablerE [z+x]addrC addrKA. Qed.

Lemma set_comparableNE E : set_comparable [set - x | x in E] <-> set_comparable E.
Proof.
split=>[P x y/=Ex Ey|P x y/=[a Ea <-][b Eb <-]]. 
by rewrite -comparablerN; apply: P=>/=; [exists x|exists y].
by rewrite comparablerN; apply: P.
Qed.

Lemma contra_ler_forall (x : C) : ~ (forall x1, x <= x1).
Proof.
move=>P. have P1: (x = 0). 
apply/le_anti/andP; split; last rewrite -(lerD2l x) -lerBrDr; by apply P.
rewrite P1 in P. move: (P (-1)).
by rewrite -lerN2 opprK oppr0 ler10 .
Qed.

Lemma ubound_supremumE E x0 x : ubound E x -> 
  (forall y, ubound E y -> x <= y) -> supremum x0 E = x.
Proof.
move=>P2 P3; rewrite /supremum; case: eqP=>P4.
apply/le_anti/andP; split; first rewrite -(lerD2l x) -lerBrDr;
by apply P3; rewrite P4/ubound/=.
apply xget_subset1=>//; by apply is_subset1_supremums.
Qed.

(* Lemma foo8 E x0 : supremums E !=set0 -> 
  ubound E (supremum x0 E) /\ lbound (ubound E) (supremum x0 E).
Proof.
case=> x Ax; rewrite /supremum; move: Ax; case: ifPn => [/eqP -> //|_].
by rewrite/supremums/=/ubound/lbound/==>[[_ P1]]; exfalso; apply (@contra_ler_forall x)=>x1; apply P1.
by move=>Ax; split; case: xgetP => [y yA [P1 P2]|/(_ x) //].
Qed. *)

End SetComparable.


Section extnumsup.
Context {R : realType} {C : extNumType R}.
Implicit Type (E : set C) (F : set R).

Lemma c2rKB (x y : C) : x >=< y -> r2c (c2r (x - y)) = x - y.
Proof. by rewrite comparablerE=>P; rewrite c2rK. Qed.

Lemma nonempty_imageE (S T: Type) (f : S -> T) (F : set S) :
  (f @` F !=set0) = (F !=set0).
Proof. by rewrite propeqE; split=>[|[x Px]]; [apply: nonempty_image|exists (f x)]. Qed.

Lemma image_set0E (S T: Type) (f : S -> T) (F : set S) :
  (f @` F == set0) = (F == set0).
Proof.
case: eqP. by move=>/image_set0_set0->; rewrite eqxx.
by case: eqP=>// ->; rewrite image_set0.
Qed.

Definition c2r_shift E := c2r @` ((fun x=> x - get E) @` E).
Definition r2c_shift (x0 : C) (F : set R) : set C := (fun x=>x + x0) @` (r2c @` F).

Lemma c2r_shiftK E : set_comparable E ->
  r2c_shift (get E) (c2r_shift E) = E.
Proof.
move=>Pc; rewrite predeqE=>x; split;
rewrite /c2r_shift/r2c_shift/=.
move=>[a][b][c][d] Ed<-<-<-.
by rewrite c2rKB ?addrNK// => [ <-//|]; apply comparable_get.
move=>Ex. exists (x - get E); rewrite ?addrNK//.
exists (c2r (x - get E)); last by rewrite c2rKB//; apply/comparable_get.
by exists (x - get E)=>//; exists x.
Qed.

Lemma c2r_shiftP E (x : C) : set_comparable E -> 
  E x -> c2r_shift E (c2r (x - get E)).
Proof. by move=>P1 P2; rewrite/c2r_shift/=; exists (x-get E)=>//; exists x. Qed.

Lemma has_ubound_comparable E : has_ubound E -> set_comparable E.
Proof.
move=>[u Pu] x y Ex Ey; move: (Pu x Ex) (Pu y Ey)=>/le_comparable +/le_comparable.
rewrite [y>=<u]comparable_sym; exact: comparabler_trans.
Qed.

Lemma has_lbound_comparable E : has_lbound E -> set_comparable E.
Proof.
move=>[u Pu] x y Ex Ey; move: (Pu x Ex) (Pu y Ey)=>/le_comparable +/le_comparable.
rewrite comparable_sym; exact: comparabler_trans.
Qed.

Lemma has_sup_comparable E : has_sup E -> set_comparable E.
Proof. move=>[]Ps; apply/has_ubound_comparable. Qed.

Lemma has_inf_comparable E : has_inf E -> set_comparable E.
Proof. move=>[]Ps; apply/has_lbound_comparable. Qed.

Lemma r2c_shift_comparable (x0 : C) (F : set R) : 
  set_comparable (r2c_shift x0 F).
Proof.
move=>x y[]a/=[ar]Far<-<-[]b/=[br]Fbr<-<-; 
by rewrite-subr_comparable0 [r2c br + _]addrC addrKA comparablerE subr0 -raddfB r2c_real.
Qed.

Lemma c2r_shift_ubound E : set_comparable E -> 
  forall x, ubound (c2r_shift E) x = ubound E (r2c x + get E).
Proof.
move=>Pc x; rewrite propeqE; split.
move=>Pu y Ey. rewrite -lerBlDr -c2rKB 1?ler_r2c/=.
by apply/Pu/c2r_shiftP. by apply/comparable_get.
move=>Pu y Ey. rewrite -(@ler_r2c _ C) -(lerD2r (get E)).
apply: Pu. move: Ey; rewrite/c2r_shift/==>[[a][b Eb]]<-<-.
by rewrite c2rKB ?addrNK//; apply/comparable_get.
Qed.

Lemma c2r_ubound E : set_comparable E -> E !=set0 ->
  ubound E = r2c_shift (get E) (ubound (c2r_shift E)).
Proof.
move=>Pc [x0 Px0]; rewrite predeqE=>x; split.
move=>ux; rewrite/r2c_shift/=; exists (x - get E); rewrite?addrNK//.
exists (c2r (x - get E)). rewrite c2r_shift_ubound//.
1,2: rewrite c2rKB// ?addrNK//; move: (ux _ Px0)=>/le_comparable;
by rewrite comparable_sym=>P; apply: (comparabler_trans P); apply: comparable_get.
by rewrite/r2c_shift/==>[[a][b Pb]<-<-]; rewrite -c2r_shift_ubound.
Qed.

Lemma has_sup_c2r_shift (E : set C) : has_sup E -> has_sup (c2r_shift E).
Proof. 
move=>[P1 [x P2]]; split; first by rewrite !nonempty_imageE.
exists (c2r (x - (get E)))=>y [a/= [b Pb]]<-<-.
by apply/ler_c2r/lerB=>//; apply P2.
Qed.

Lemma sup_least_ubound (F : set R) : has_sup F -> lbound (ubound F) (sup F).
Proof.
move=>P1. rewrite/lbound/==>x P2.
case: leP=>//. rewrite -subr_gt0=>/sup_adherent/(_ P1)[e P3].
rewrite subKr. move: P2. rewrite /ubound/==>/(_ _ P3).
by case: leP.
Qed.

Lemma etsup_shift E : has_sup E ->
  etsup E = r2c (sup (c2r_shift E)) + get E.
Proof.
move=>P1. move: (has_sup_c2r_shift P1) (has_sup_comparable P1)=>P2 P5.
move: (sup_least_ubound P2) (sup_upper_bound P2)=>P3 P4.
set F := c2r_shift E in P2 P3 P4 *.
rewrite /etsup. apply/ubound_supremumE.
rewrite /ubound/==>x Px. rewrite -lerBlDr -c2rKB 1?ler_r2c.
by apply/P4/c2r_shiftP. by apply/comparable_get.
move=>y P6. rewrite -lerBrDr -c2rKB.
rewrite ler_r2c. apply P3. rewrite c2r_shift_ubound// c2rKB ?addrNK//.
all: by apply comparable_get_ubound=>//; move: P1=>[].
Qed.

Lemma etsup_adherent (E : set C) (eps : C) : 0 < eps ->
  has_sup E -> exists2 e : C, E e & (etsup E - eps) < e.
Proof.
move=>P1 P2. have P3: 0 < c2r eps by apply/c2r_gt0.
move: (sup_adherent P3 (has_sup_c2r_shift P2))=>[er P4 P5].
exists (r2c er + get E).
move: P4. rewrite /c2r_shift/==>[[e1 [e2]]]P6 <-<-.
by rewrite c2rK ?addrNK// -comparablerE comparable_get//; apply has_sup_comparable.
rewrite etsup_shift// addrC addrA ltrD2 addrC -[eps]c2rK.
by rewrite -rmorphB ltr_r2c. by apply gtr0_real.
Qed.

Lemma etsup_upper_bound E : has_sup E -> ubound E (etsup E).
Proof.
move=>P1. rewrite etsup_shift// -c2r_shift_ubound.
by apply/sup_upper_bound/has_sup_c2r_shift. by apply/has_sup_comparable.
Qed.

Lemma etsup_least_ubound E : has_sup E -> lbound (ubound E) (etsup E).
Proof.
move=>P1. rewrite/lbound/==>x P2.
rewrite etsup_shift// -lerBrDr -c2rKB 1?ler_r2c.
apply/sup_least_ubound. by apply/has_sup_c2r_shift. rewrite c2r_shift_ubound ?c2rKB ?addrNK//.
1,3: by apply/comparable_get_ubound=>//; move: P1=>[].
by apply/has_sup_comparable.
Qed.

End extnumsup.

Section MxExtNumCvg.
Variable (R: realType) (C: extNumType R) (m n : nat).
Local Notation M := 'M[C]_(m,n).
Implicit Type (f g: nat -> M) (r: nat) (a b : M) (s : nat -> C) (k: C).

Lemma mxhausdorff p q : hausdorff_space [topologicalType of 'M[C]_(p,q)].
Proof.
case: p=>[|p]; last first. case: q=>[|q]; last by apply: norm_hausdorff.
all: rewrite ball_hausdorff=>/=a b /negP Pab; exfalso; apply Pab; apply/eqP;
apply/matrixP=>i j. by destruct j. by destruct i.
Qed.

Lemma mxcvg_limE f a : f --> a <-> lim f = a /\ cvg f.
Proof. 
split=>[P1|[ <-]//]. split. apply/cvg_lim. apply mxhausdorff.
apply P1. by move: P1=>/cvgP.
Qed.

(* for quick use. directly use these lemmas have the problem on different canonical routes *)

Lemma mxcvg_cst a : (fun n:nat=>a) --> a. Proof. exact: cvg_cst. Qed.
Lemma is_mxcvg_cst a : cvg (fun n:nat=>a). Proof. exact: is_cvg_cst. Qed.
Lemma mxlim_cst a : lim (fun n:nat=>a) = a. Proof. apply: lim_cst. apply mxhausdorff. Qed.

Lemma mxcvgN f a : f --> a -> (- f) --> - a.
Proof.
case: m f a=>[f a _|m' f a]; [apply mxcvg_dim0n|].
case: n f a=>[f a _|n' f a]; [apply mxcvg_dimn0|exact: cvgN].
Qed.

Lemma is_mxcvgN f : cvg f -> cvg (- f).
Proof. by move=> /mxcvgN /cvgP. Qed.

Lemma is_mxcvgNE f : cvg (- f) = cvg f.
Proof. by rewrite propeqE; split=> /mxcvgN; rewrite ?opprK => /cvgP. Qed.

Lemma mxcvgMn f r a : f --> a -> ((@GRing.natmul _)^~r \o f) --> a *+ r.
Proof.
case: m f a=>[f a _|m' f a]; [apply mxcvg_dim0n|].
case: n f a=>[f a _|n' f a]; [apply mxcvg_dimn0|exact: cvgMn].
Qed.

Lemma is_mxcvgMn f r : cvg f -> cvg ((@GRing.natmul _)^~r \o f).
Proof. by move=> /(@mxcvgMn _ r) /cvgP. Qed.

Lemma mxcvgD f g a b : f --> a -> g --> b -> (f + g) --> a + b.
Proof.
case: m f g a b=>[f g a b _ _|m' f g a b]; [apply mxcvg_dim0n|].
case: n f g a b=>[f g a b _ _|n' f g a b]; [apply mxcvg_dimn0|exact: cvgD].
Qed.

Lemma is_mxcvgD f g : cvg f -> cvg g -> cvg (f + g).
Proof. by have := cvgP _ (mxcvgD _ _); apply. Qed.

Lemma mxcvgB f g a b : f --> a -> g --> b -> (f - g) --> a - b.
Proof. by move=> ? ?; apply: mxcvgD=>[//|]; apply: mxcvgN. Qed.

Lemma is_mxcvgB f g : cvg f -> cvg g -> cvg (f - g).
Proof. by have := cvgP _ (mxcvgB _ _); apply. Qed.

Lemma is_mxcvgDlE f g : cvg g -> cvg (f + g) = cvg f.
Proof.
move=> g_cvg; rewrite propeqE; split; last by move=> /is_mxcvgD; apply.
by move=> /is_mxcvgB /(_ g_cvg); rewrite addrK.
Qed.

Lemma is_mxcvgDrE f g : cvg f -> cvg (f + g) = cvg g.
Proof. by rewrite addrC; apply: is_mxcvgDlE. Qed.

Lemma mxcvgZ s f k a : s --> k -> f --> a -> (fun x => s x *: f x) --> k *: a.
Proof.
case: m f a=>[f a _ _|m' f a]; [apply mxcvg_dim0n|].
case: n f a=>[f a _ _|n' f a]; [apply mxcvg_dimn0|exact: cvgZ].
Qed.

Lemma is_mxcvgZ s f : cvg s -> cvg f -> cvg (fun x => s x *: f x).
Proof. by have := cvgP _ (mxcvgZ _ _); apply. Qed.

Lemma mxcvgZl s k a : s --> k -> (fun x => s x *: a) --> k *: a.
Proof. by move=> ?; apply: mxcvgZ => //; exact: cvg_cst. Qed.

Lemma is_mxcvgZl s a : cvg s -> cvg (fun x => s x *: a).
Proof. by have := cvgP _ (mxcvgZl  _); apply. Qed.

Lemma mxcvgZr k f a : f --> a -> k \*: f --> k *: a.
Proof. apply: mxcvgZ => //; exact: cvg_cst. Qed.

Lemma is_mxcvgZr k f : cvg f -> cvg (k *: f ).
Proof. by have := cvgP _ (mxcvgZr  _); apply. Qed.

Lemma is_mxcvgZrE k f : k != 0 -> cvg (k *: f) = cvg f.
Proof.
move=> k_neq0; rewrite propeqE; split => [/(@mxcvgZr k^-1)|/(@mxcvgZr k)/cvgP//].
by under [_ \*: _]funext => x /= do rewrite scalerK//; apply: cvgP.
Qed.

Lemma mxlimN f : cvg f -> lim (- f) = - lim f.
Proof. by move=> ?; apply: cvg_lim; [apply mxhausdorff|apply: mxcvgN]. Qed.

Lemma mxlimD f g : cvg f -> cvg g -> lim (f + g) = lim f + lim g.
Proof. move=> Pf Pg; apply: cvg_lim; [apply mxhausdorff|apply: mxcvgD;[apply Pf|apply Pg]]. Qed.

Lemma mxlimB f g : cvg f -> cvg g -> lim (f - g) = lim f - lim g.
Proof. move=> Pf Pg; apply: cvg_lim; [apply mxhausdorff|apply: mxcvgB;[apply Pf|apply Pg]]. Qed.

Lemma mxlimZ s f : cvg s -> cvg f -> lim (fun x => s x *: f x) = lim s *: lim f.
Proof. move=> Ps Pf; apply: cvg_lim; [apply mxhausdorff|apply: mxcvgZ;[apply Ps|apply Pf]]. Qed.

Lemma mxlimZl s a : cvg s -> lim (fun x => s x *: a) = lim s *: a.
Proof. by move=> ?; apply: cvg_lim; [apply mxhausdorff|apply: mxcvgZl]. Qed.

Lemma mxlimZr k f : cvg f -> lim (k *: f) = k *: lim f.
Proof. by move=> ?; apply: cvg_lim; [apply mxhausdorff|apply: mxcvgZr]. Qed.

(* since only nontrivial matrix are canonical to normZmodType *)
Lemma mxcvg_norm (h : nat->'M[C]_(m.+1,n.+1)) (x : 'M[C]_(m.+1,n.+1)) : 
  h --> x -> (Num.norm \o h) --> `|x|.
Proof. exact: cvg_norm. Qed.
Lemma is_mxcvg_norm (h : nat->'M[C]_(m.+1,n.+1)) : 
  cvg h -> cvg (Num.norm \o h).
Proof. exact: is_cvg_norm. Qed.
Lemma mxlim_norm (h : nat->'M[C]_(m.+1,n.+1)) : 
  cvg h -> lim (Num.norm \o h) = `|lim h|.
Proof. exact: lim_norm. Qed.

Lemma mxcvg_map f a (V : completeType) (h : M -> V) :
  continuous h -> f --> a -> (h \o f) --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ [filter of f] a h).
by apply ch. by apply cvgf.
Qed.

Lemma mxcvg_mapV (V : completeType) (h : V -> M) (h' : nat -> V) (a : V) :
  continuous h -> h' --> a -> (h \o h') --> h a.
Proof. 
move=>ch cvgf; apply: (@cvg_fmap _ _ [filter of h'] a h).
by apply ch. by apply cvgf.
Qed.

Lemma is_mxcvg_map f (V : completeType) (h : M -> V) :
  continuous h -> cvg f -> cvg (h \o f).
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (mxcvg_map P1 Pa).
Qed.

Lemma is_mxcvg_mapV (V : completeType) (h : V -> M) (h' : nat -> V) :
  continuous h -> cvg h' -> cvg (h \o h').
Proof.
move=>P1 /cvg_ex=>[/= [a Pa]]. apply/cvg_ex.
exists (h a). by move: (mxcvg_mapV P1 Pa).
Qed.

Lemma mxlim_map f a (V : completeType) (h : M -> V) :
  hausdorff_space V -> continuous h -> cvg f -> lim (h \o f) = h (lim f).
Proof. by move=>hV ch; move/(mxcvg_map ch)/cvg_lim=>/(_ hV). Qed.

Lemma mxlim_mapV (V : completeType) (h : V -> M) (h' : nat -> V) :
  continuous h -> cvg h' -> lim (h \o h') = h (lim h').
Proof. by move=>ch; move/(mxcvg_mapV ch)/cvg_lim=>/(_ (@mxhausdorff _ _)). Qed.

Lemma is_mxcvgZlE s a : a != 0 -> cvg (fun x => s x *: a) = cvg s.
Proof.
move=> a_neq0; rewrite propeqE; split; last by apply is_mxcvgZl.
have [i [j Pij]] : exists i j, a i j != 0.
move: a_neq0. apply contraPP. rewrite -forallNP=>P.
apply/negP. rewrite negbK. apply/eqP/matrixP=>i j.
move: (P i). rewrite -forallNP=>/(_ j)/negP. by rewrite mxE negbK=>/eqP->.
set t := (fun x : M => (x i j) / (a i j)).
have P1: s = t \o (fun x : nat => s x *: a).
rewrite funeqE=>p. rewrite /= /t mxE mulfK//.
move=>P. rewrite P1. apply/is_mxcvg_map=>//.
move=>/= x w/= /nbhs_ballP [/=e egt0 Pb].
apply/nbhs_ballP. have P2: 0 < `|a i j|.
rewrite lt_def normr_ge0 andbT.
by move: Pij; apply contraNN=>/eqP/Num.Theory.normr0P.
exists (e * `|a i j|) =>//=. apply Num.Theory.mulr_gt0=>//.
move=> y /= Pxy. apply (Pb (t y)). move: Pxy.
rewrite /ball/= /mx_ball=>/(_ i j). rewrite /ball/=.
rewrite /t -mulrBl Num.Theory.normrM Num.Theory.normrV ?GRing.unitfE//.
rewrite Num.Theory.ltr_pdivrMr// =>P3.
Qed.

Lemma mxcvg_limP p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) :
  h --> x <-> forall e, 0 < e -> exists N, forall n,  (N <= n)%N -> mx_norm (h n - x) < e.
Proof.
case: p h x=>[h x|p]; last case: q=>[h x|q h x].
1,2: split=>_; [move=>e Pe; exists 0%N=>r _; rewrite !mx_dim0 mx_norm0//|].
apply mxcvg_dim0n. apply mxcvg_dimn0. rewrite mx_normEV.
exact: (@cvg_limP _ [completeNormedModType C of 'M_(p.+1, q.+1)] h x).
Qed.

Lemma mxcvg_subseqP p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) : 
  h --> x <-> (forall (h': nat -> nat), (forall n, (h' n.+1 > h' n)%N) -> (h \o h') --> x).
Proof.
case: p h x=>[h x|p]; last case: q=>[h x|q h x].
1,2: split=>_; [move=>??|]; rewrite !mx_dim0; apply: cvg_cst.
exact: (@cvg_subseqP _ [completeNormedModType C of 'M_(p.+1, q.+1)] h x).
Qed.

Lemma mxcvg_subseqPN p q (h: nat -> 'M[C]_(p,q)) (x : 'M[C]_(p,q)) :
  ~ (h --> x) <-> exists e (h': nat -> nat), 
    (forall n, (h' n.+1 > h' n)%N) /\ 0 < e /\ (forall n, mx_norm ((h \o h') n - x) >= e).
Proof.
case: p h x=>[h x|p]; last case: q=>[h x|q h x].
1,2: rewrite not_existsP; rewrite iff_not2; split=>_;[|rewrite !mx_dim0; apply: cvg_cst].
1,2: move=>c; rewrite -forallNP=> h'; rewrite !not_andP; right.
1,2: case E: (0 < c); [right|left=>//]; rewrite -existsNP; exists 0%N; rewrite !mx_dim0 mx_norm0.
1,2: by apply/negP; rewrite -Num.Theory.real_ltNge// ?Num.Theory.real0// Num.Theory.gtr0_real.
rewrite mx_normEV.
exact: (@cvg_subseqPN _ [completeNormedModType C of 'M_(p.+1, q.+1)] h x).
Qed.

Lemma mxnatmul_continuous p : continuous (fun x : M => x *+ p).
Proof.
case: m=>/=[x|m']; last case: n=>/=[x|n' x].
1,2: rewrite !mx_dim0; apply: cst_continuous.
exact: natmul_continuous.
Qed.

Lemma mxscale_continuous : continuous (fun z : C * M => z.1 *: z.2).
Proof.
case: m=>/=[x|m']; last case: n=>/=[x|n' x].
1,2: rewrite !mx_dim0; apply: cst_continuous.
exact: scale_continuous.
Qed.

Global Arguments mxscale_continuous _ _ : clear implicits.

Lemma mxscaler_continuous k : continuous (fun x : M => k *: x).
Proof.
by move=> x; apply: (cvg_comp2 (cvg_cst _) cvg_id (mxscale_continuous (_, _))).
Qed.

Lemma mxscalel_continuous (x : M) : continuous (fun k : C => k *: x).
Proof.
by move=> k; apply: (cvg_comp2 cvg_id (cvg_cst _) (mxscale_continuous (_, _))).
Qed.

(* TODO: generalize to pseudometricnormedzmod *)
Lemma mxopp_continuous : continuous (fun x : M => -x).
Proof.
case: m=>/=[x|m']; last case: n=>/=[x|n' x].
1,2: rewrite !mx_dim0; apply: cst_continuous.
exact: opp_continuous.
Qed.

Lemma mxadd_continuous : continuous (fun z : M * M => z.1 + z.2).
Proof.
case: m=>/=[x|m']; last case: n=>/=[x|n' x].
1,2: rewrite !mx_dim0; apply: cst_continuous.
exact: add_continuous.
Qed.

Global Arguments mxadd_continuous _ _ : clear implicits.

Lemma mxaddr_continuous a : continuous (fun z : M => a + z).
Proof.
by move=> x; apply: (cvg_comp2 (cvg_cst _) cvg_id (mxadd_continuous (_, _))).
Qed.

Lemma mxaddl_continuous a : continuous (fun z : M => z + a).
Proof.
by move=> x; apply: (cvg_comp2 cvg_id (cvg_cst _) (mxadd_continuous (_, _))).
Qed.

(* Variable (f : nat -> 'M[R[i]]_(m,n)) (a : 'M[R[i]]_(m,n)). *)
Definition mxcauchy_seq f := 
  forall e, 0 < e -> exists N, forall i j, 
  (N <= i)%N -> (N <= j)%N -> mx_norm (f i - f j) < e.

Definition mxcvg_seq f a := 
  forall e, 0 < e -> exists N : nat, 
    forall i, (N <= i)%N -> mx_norm (a - f i) < e.

Lemma mxcauchy_seqP f : mxcauchy_seq f <-> cvg f.
Proof.
rewrite /mxcauchy_seq; case: m f=>[f|]; last case: n=>[m' f|m' n' f].
1,2: split=>_. apply/is_mxcvg_dim0n. 2: apply/is_mxcvg_dimn0.
1,2: by move=>e egt0; exists 0%N=>i j _ _; rewrite !mx_dim0 mx_norm0.
exact: (@cauchy_seqP _ [completeNormedModType C of 'M[C]_(n'.+1,m'.+1)]).
Qed.

Lemma mxcvg_seqP f a : mxcvg_seq f a <-> f --> a.
Proof.
rewrite /mxcvg_seq; case: m f a=>[f a|]; last case: n=>[m' f a|m' n' f a].
1,2: split=>[_ |_ e egt0]; last exists 0%N=>i _. 
1,2,3,4: rewrite !mx_dim0 ?mx_norm0//. apply/mxcvg_dim0n. apply/mxcvg_dimn0.
exact: (@cvg_seqP _ [completeNormedModType C of 'M[C]_(n'.+1,m'.+1)]).
Qed.

End MxExtNumCvg.

Section MxLinearContinuous.
Variable (R: realType) (C: extNumType R).


Lemma mxlinear_continuous m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q)) :
  linear f -> continuous f.
Proof.
move: f; case: m=>[|m]; last first. case: n=>[|n]; last first. 
case: p=>[|p]; last first. case: q=>[|q]; last first.
all: move=>f Lf; set LfT := Linear Lf; have P0 : f = LfT by [].
suff: continuous LfT by [].
rewrite -linear_bounded_continuous -bounded_funP=>r/=.
have Pu : exists c, forall i j, `|LfT (delta_mx i j)| <= c.
exists (\sum_i\sum_j`|LfT (delta_mx i j)|)=>i j.
rewrite (bigD1 i)//= (bigD1 j)//= -addrA Num.Theory.lerDl Num.Theory.addr_ge0//.
1,2: rewrite Num.Theory.sumr_ge0//. move=>k _; rewrite Num.Theory.sumr_ge0//.
move: Pu=>[c Pc]. exists ((m.+1)%:R * ((n.+1)%:R * (r * c)))=>x /mxnorm_le_alter Pij.
(* have Pij i j : `|x i j| <= r. by apply (le_trans (mx_norm_element _ (i,j))). *)
rewrite (matrix_sum_delta x) P0 linear_sum/=.
apply: (le_trans (ler_norm_sum _ _ _)). apply/ler_sum_const=>i.
rewrite P0 linear_sum/=.
apply: (le_trans (ler_norm_sum _ _ _)). apply/ler_sum_const=>j.
by rewrite P0 linearZ/= normrZ ler_pM//; move: (Pij (i,j)).
all: by apply: cst_continuous_eq; exists 0; apply/funext=>i; 
  rewrite !mx_dim0// P0 linear0.
Qed.

Lemma mxcvg_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) : 
  linear f -> u --> a -> (fun x=> f (u x)) --> (f a).
Proof. by move/mxlinear_continuous=>P1; apply: continuous_cvg; apply: P1. Qed.

Lemma is_mxcvg_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
(u : nat -> 'M[C]_(m,n))  : linear f -> cvg u -> cvg (f \o u).
Proof. by move=>P1; have := cvgP _ (mxcvg_lfun P1 _); apply. Qed.

Lemma mxlim_lfun m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (u : nat -> 'M[C]_(m,n)) : 
  linear f -> cvg u -> lim (f \o u) = f (lim u).
Proof. move=>P1 ?; apply: cvg_lim => //. apply mxhausdorff. by apply: mxcvg_lfun. Qed.

Lemma mxclosed_comp m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (A : set 'M[C]_(p,q)) :
  linear f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply (mxlinear_continuous lf). Qed.

Lemma mxopen_comp m n p q (f : 'M[C]_(m,n) -> 'M[C]_(p,q))
  (A : set 'M[C]_(p,q)) :
  linear f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply (mxlinear_continuous lf). Qed.

Lemma mxscalar_continuous m n (f : 'M[C]_(m,n) -> C) :
  scalar f -> continuous f.
Proof.
move: f; case: m=>[|m]; last first. case: n=>[|n]; last first.
all: move=>f Lf; set LfT := Linear Lf; have P0 : f = LfT by [].
suff: continuous LfT by [].
rewrite -linear_bounded_continuous -bounded_funP=>r/=.
have Pu : exists c, forall i j, `|LfT (delta_mx i j)| <= c.
exists (\sum_i\sum_j`|LfT (delta_mx i j)|)=>i j.
rewrite (bigD1 i)//= (bigD1 j)//= -addrA lerDl addr_ge0//.
1,2: rewrite sumr_ge0//. move=>k _. rewrite sumr_ge0//.
move: Pu=>[c Pc]. exists ((m.+1)%:R * ((n.+1)%:R * (r * c)))=>x/mxnorm_le_alter Pij.
(* have Pij i j : `|x i j| <= r by apply (le_trans (mx_norm_element _ (i,j))). *)
rewrite (matrix_sum_delta x) P0 linear_sum/=.
apply: (le_trans (ler_norm_sum _ _ _)). apply/ler_sum_const=>i.
rewrite P0 linear_sum/=.
apply: (le_trans (ler_norm_sum _ _ _)). apply/ler_sum_const=>j.
by rewrite P0 linearZ/= normrZ ler_pM//; move: (Pij (i,j)).
all: by apply: cst_continuous_eq; exists 0; apply/funext=>i; rewrite !mx_dim0 P0 linear0.
Qed.

Lemma mxcvg_sfun m n (f : 'M[C]_(m,n) -> C)
  (u : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) : 
  scalar f -> u --> a -> (fun x=> f (u x)) --> (f a).
Proof. by move/mxscalar_continuous=>P1; apply: continuous_cvg; apply: P1. Qed.

Lemma is_mxcvg_sfun m n (f : 'M[C]_(m,n) -> C)
(u : nat -> 'M[C]_(m,n)) : scalar f -> cvg u -> cvg (f \o u).
Proof. by move=>P1; have := cvgP _ (mxcvg_sfun P1 _); apply. Qed.

Lemma mxlim_sfun m n (f : 'M[C]_(m,n) -> C)
  (u : nat -> 'M[C]_(m,n)) : 
  scalar f -> cvg u -> lim (f \o u) = f (lim u).
Proof. move=>P1 ?; apply: cvg_lim => //. by apply: mxcvg_sfun. Qed.

Lemma mxcclosed_comp m n (f : 'M[C]_(m,n) -> C)
  (A : set C) :
  scalar f -> closed A -> closed (f @^-1` A).
Proof. by move=>lf; apply closed_comp=>x _; apply (mxscalar_continuous lf). Qed.

Lemma mxcopen_comp m n (f : 'M[C]_(m,n) -> C)
  (A : set C) :
  scalar f -> open A -> open (f @^-1` A).
Proof. by move=>lf; apply open_comp=>x _; apply (mxscalar_continuous lf). Qed.

End MxLinearContinuous.

Section MxNormExtNumND.
Variable (R: realType) (C: extNumType R) (m n : nat).
Local Notation M := 'M[C]_(m.+1,n.+1).
Variable (mnorm : vnorm [lmodType C of M]).

Lemma compact_mxnorm_le (c : C) : compact [set x : M | `|x| <= c].
Proof.
pose A (i : 'I_(m.+1 * n.+1)) := [set x : C | `|x| <= c].
rewrite (_ : mkset _ = (@vec_mx C m.+1 n.+1) @` [set x : 'rV__ | forall i, A i (x ord0 i)]).
apply: continuous_compact.
apply: continuous_subspaceT=>x ?; apply: vec_mx_continuous.
apply: rV_compact=>i. apply: extNum_bounded_compact.
rewrite predeqE=>x/=; split; last first.
move=>[y Py]<-. apply/mxnorm_le_alter=>i. move: (Py (mxvec_index i.1 i.2)).
by rewrite/A/= -[vec_mx _ _ _]mxvecE vec_mxK.
move=>/mxnorm_le_alter Px; exists (mxvec x)=>[i|]; rewrite ?mxvecK//.
by case/mxvec_indexP: i=>i j; rewrite/A/= mxvecE; move: (Px (i,j)).
Qed.

Lemma compact_mxnorm_eq1 : compact [set x : M | `|x| = 1].
Proof.
suff P1: compact [set x : M | `|x| <= 1].
apply: (subclosed_compact _ P1 _).
apply: closed_mxnorm_sphere.
by move=>t; rewrite/==>->.
exact: compact_mxnorm_le.
Qed.

Lemma compact_mxnorm_eq1_vint : compact (mnorm @` [set x : M | `|x| = 1%:R]).
Proof.
apply continuous_compact; last by apply compact_mxnorm_eq1.
apply/continuous_subspaceT=>x ?; apply continuous_mnorm_ND.
Qed.

Lemma mnorm_lbounded_ND : exists2 c : C, 0 < c & forall x,  c * `|x| <= mnorm x.
Proof.
have sr : [set mnorm x | x in [set x | `|x| = 1%:R]] `<=` [set` Num.real].
by move=>x/=[y _]<-; rewrite normv_real.
move: (extNum_compact_min sr compact_mxnorm_eq1_vint (mxnorm_sphere_neq0_vint mnorm))
  =>[c [v /= Pv1 Pv2] Py].
have Pc: 0 < c by rewrite -Pv2 normv_gt0 -normr_gt0 Pv1 ltr01.
exists c=>// x; case E: (x == 0).
move: E=>/eqP ->. by rewrite normr0 normv0 mulr0.
have E1: `|x| > 0 by rewrite normr_gt0 E.
rewrite -{2}(scale1r x) -(@mulfV _ `|x|); last by move: E1; rewrite lt_def=>/andP[->].
rewrite -scalerA normvZ normr_id mulrC. apply ler_pM=>//.
by apply ltW. apply Py. exists (`|x|^-1 *: x)=>//.
rewrite mx_normZ ger0_norm ?inv_nng_ge0// mulVf//.
by move: E1; rewrite lt_def=>/andP[->].
Qed.

End MxNormExtNumND.

Section MxNormExtNumEqual.
Variable (R: realType) (C: extNumType R) (m n : nat).
Local Notation M := 'M[C]_(m,n).
Variable (mnorm : vnorm [lmodType C of M]).

Lemma mxlim_mnorm (f : M ^nat) : 
  cvg f -> lim (mnorm \o f) = mnorm (lim f).
Proof. by move=> ?; apply: cvg_lim => //; apply: mxcvg_mnorm. Qed.

Lemma mnorm_lbounded : exists2 c : C, 
  0 < c & forall x,  c * mx_norm x <= mnorm x.
Proof.
case: m mnorm=>[mnorm'|m']; last case: n=>[mnorm'|n' mnorm'].
1,2: by exists 1=>// x; rewrite mx_dim0 !normv0 mul1r.
exact: mnorm_lbounded_ND.
Qed.

Let cl := projT1 (cid2 mnorm_lbounded).
Let cl_gt0 : cl > 0.
Proof. by move: (projT2 (cid2 mnorm_lbounded))=>[]. Qed.
Let clP : forall x, cl * mx_norm x <= mnorm x.
Proof. by move: (projT2 (cid2 mnorm_lbounded))=>[]. Qed.
Let clPV : forall x, mx_norm x <= mnorm x / cl.
Proof. by move=>x; rewrite ler_pdivlMr// mulrC. Qed.

Lemma compact_mnorm_le (y : C) : compact [set x : M | mnorm x <= y].
Proof.
suff P: compact [set x : M | mx_norm x <= y / cl].
apply: (subclosed_compact _ P _). apply: closed_mnorm_le.
by move=>z/= P1; move: (le_trans (clP _) P1); rewrite -ler_pdivlMl//= mulrC.
case: m mnorm=>[mnorm'|m']; last case: n=>[mnorm'|n' mnorm']; last exact: compact_mxnorm_le.
1,2: by apply: mx_set_compact_trivial; rewrite eqxx.
Qed.

Lemma compact_mnorm_sphere (y : C) : compact [set x : M | mnorm x = y].
Proof.
suff P1: compact [set x : M | mnorm x <= y].
apply: (subclosed_compact _ P1 _).
apply: closed_mnorm_sphere.
by move=>t; rewrite/==>->.
exact: compact_mnorm_le.
Qed.

Lemma Bolzano_Weierstrass (f : nat -> 'M[C]_(m,n)) (M : C) :
  (forall n, mx_norm (f n) <= M) -> exists (h: nat -> nat), 
    (forall n, (h n.+1 > h n)%N) /\ cvg (f \o h).
Proof.
case: m f. move=>f _; exists id; split=>//. exact: is_mxcvg_dim0n.
case: n. move=>n' f _; exists id; split=>//; exact: is_mxcvg_dimn0.
move=>n' m' f P1; move: (@compact_mxnorm_le _ C m' n' M)=>P2.
set f' := f : nat -> [completeNormedModType C of 'M[C]_(m'.+1,n'.+1)].
apply: (@cluster_subsvg _ _ _ f' _ P2 _)=>[x|i//=].
by move=>/extNum_ltr_add_invr[k Pk]; exists k; move: Pk; rewrite add0r.
by rewrite/f' /normr/=.
Qed.

(* bounded seq: cvg <-> any cvg subseq to a *)
Lemma mxcvg_subseqP_cvg (f : nat -> 'M[C]_(m,n)) (a : 'M[C]_(m,n)) (M : C): 
  (forall n, mx_norm (f n) <= M) ->
  f --> a <-> (forall (h: nat -> nat), (forall n, (h n.+1 > h n)%N) 
    -> cvg (f \o h) -> lim (f \o h) = a).
split.
move=>/mxcvg_subseqP + h Ph _. move=>/(_ h Ph).
apply: cvg_lim. apply mxhausdorff.
move=>P. apply contrapT. rewrite mxcvg_subseqPN.
rewrite -forallNP=> e. rewrite -forallNP=> h.
rewrite -!implyNE=>Ph Pe Pc.
have P1: forall n0 : nat, mx_norm ((f \o h) n0) <= M by move=>n0; apply H.
move: (Bolzano_Weierstrass P1)=>[h' [Ph']]. rewrite -compA=>Pc'.
have P2: ~ ((f \o (h \o h')) --> a).
rewrite mxcvg_subseqPN; exists e; exists id; do 2 split=>//.
move=>n'; apply Pc.
apply P2. rewrite mxcvg_limE; split=>[|//].
apply P=>[|//]. move=>n'/=. by apply nchain_mono.
Qed.

End MxNormExtNumEqual.

Section MxNormExtNumEqual2.
Variable (R: realType) (C : extNumType R) (m n : nat).
Local Notation M := 'M[C]_(m,n).
Implicit Type (mnorm : vnorm [lmodType C of M]).

Lemma mnorm_bounded mnorm1 mnorm2 :
  exists2 c : C, 0 < c & forall x : M, mnorm1 x <= c * mnorm2 x.
Proof.
move: (mnorm_ubounded mnorm1)=>/=[c1 Pc1 P1].
move: (mnorm_lbounded mnorm2)=>/=[c2 Pc2 P2].
exists (c1 / c2)=>[|x]; first by apply Num.Theory.divr_gt0.
apply (le_trans (P1 x)). 
by rewrite -mulrA Num.Theory.ler_pM2l// Num.Theory.ler_pdivlMl.
Qed.

Lemma mxcauchy_seqv_eq mnorm1 mnorm2 (f : nat -> M) :
  cauchy_seqv mnorm1 f -> cauchy_seqv mnorm2 f.
Proof.
move: (mnorm_bounded mnorm2 mnorm1)=> [c Pc le_mn] P e Pe.
have Pec: 0 < (e / c) by apply divr_gt0.
move: (P (e/c) Pec )=>[N PN]; exists N=>s t Ps Pt.
apply: (le_lt_trans (le_mn (f s - f t))).
move: (PN s t Ps Pt); by rewrite ltr_pdivlMr// mulrC.
Qed.

Lemma mxcauchy_seqvE mnorm1 mnorm2 (f : nat -> M) :
  cauchy_seqv mnorm1 f <-> cauchy_seqv mnorm2 f.
Proof. split; by apply: mxcauchy_seqv_eq. Qed.

Lemma mxcauchy_seqE mnorm (f : nat -> M) :
  cauchy_seqv mnorm f <-> mxcauchy_seq f.
Proof. split; by apply: mxcauchy_seqv_eq. Qed.

Lemma mxcauchy_seqvP mnorm (f : nat -> M) :
  cauchy_seqv mnorm f <-> cvg f.
Proof. by rewrite mxcauchy_seqE; apply: mxcauchy_seqP. Qed.

End MxNormExtNumEqual2.

(* TODO : norm is never used; please clean the code *)
Module MxCPorder.

Section Definitions.
Variables (R: realType) (C : extNumType R) (m n : nat).
Variable (B : POrder.class_of 'M[C]_(m,n)) (disp: unit).
Local Notation M := 'M[C]_(m,n).
Local Notation "x '⊑' y" := (@Order.le disp (@POrder.Pack disp M B) x y) 
  (at level 70, y at next level).

Structure mxcporder := MxCPorder {
  _ : forall (z x y : M), x ⊑ y -> x + z ⊑ y + z;
  _ : forall (e : C) (x y : M), 0 < e -> x ⊑ y -> e *: x ⊑ e *: y;
  _ : closed [set x : M | (0 : M) ⊑ x];
}.

End Definitions.

Module Import Exports.
Notation mxcporder := mxcporder.
Notation MxCPorder := MxCPorder.
(* Coercion mnorm : cmxnormcvg >-> vnorm.
Notation "[ 'cmxnormcvg' 'of' f ]" := (@clone_vnormcvg _ _ _ _ _ f _ id _ _ _ _ id)
  (at level 0, format"[ 'cmxnormcvg'  'of'  f ]") : form_scope. *)
End Exports.

Module Theory.

Section Property.
Import Num.Def Num.Theory.
Variable (R: realType) (C: extNumType R) (m n : nat).
Local Notation M := 'M[C]_(m,n).
Variable (B : POrder.class_of M) (disp: unit).
Variable (mxorder : mxcporder B disp).

Local Notation "x '⊏' y" := (@Order.lt disp (@POrder.Pack disp M B) x y) (at level 70, y at next level).
Local Notation "x '⊑' y" := (@Order.le disp (@POrder.Pack disp M B) x y) (at level 70, y at next level).
Notation "'ubounded_by' b f" := (forall i, f i ⊑ b) (at level 10, b, f at next level).
Notation "'lbounded_by' b f" := (forall i, b ⊑ f i) (at level 10, b, f at next level).
Notation "'mxnondecreasing_seq' f" := ({homo f : n m / (n <= m)%nat >-> (n ⊑ m)})
  (at level 10).
Notation "'mxnonincreasing_seq' f" := ({homo f : n m / (n <= m)%nat >-> (m ⊑ n)})
  (at level 10).

Lemma lemx_add2r (z x y : M) : x ⊑ y -> x + z ⊑ y + z.
Proof. by move: z x y; case: mxorder. Qed.
Lemma lemx_pscale2lP (e : C) (x y : M) : 0 < e -> x ⊑ y -> e *: x ⊑ e *: y.
Proof. by move: e x y; case: mxorder. Qed.
Lemma lemx_pscale2l: forall (e : C) (x y : M), 0 < e -> x ⊑ y = (e *: x ⊑ e *: y).
Proof. 
move=> e x y egt0. apply/Bool.eq_true_iff_eq.
split. by apply lemx_pscale2lP. rewrite -{2}(scale1r x) -{2}(scale1r y) -(@mulVf _ e).
rewrite -!scalerA. apply lemx_pscale2lP. rewrite invr_gt0//. by apply/lt0r_neq0.
Qed.
Lemma closed_gemx0: closed [set x : M | (0 : M) ⊑ x].
Proof. by case: mxorder. Qed.

Implicit Type (u v : M^nat).

Lemma submx_ge0 (x y : M) : ((0 : M) ⊑ x - y) = (y ⊑ x).
Proof. 
apply/Bool.eq_iff_eq_true; split=>[/(@lemx_add2r y)|/(@lemx_add2r (-y))];
by rewrite ?addrNK ?add0r// addrN.
Qed.

Lemma lemx_opp2 : {mono (-%R : M -> M) : x y /~ x ⊑ y }.
Proof. by move=>x y; rewrite -submx_ge0 opprK addrC submx_ge0. Qed.

Lemma mxnondecreasing_opp u :
  mxnondecreasing_seq (- u) = mxnonincreasing_seq u.
Proof. by rewrite propeqE; split => du x y /du; rewrite lemx_opp2. Qed.

Lemma mxnonincreasing_opp u :
  mxnonincreasing_seq (- u) = mxnondecreasing_seq u.
Proof. by rewrite propeqE; split => du x y /du; rewrite lemx_opp2. Qed.

Lemma mxlbounded_by_opp (b : M) u :
  lbounded_by (-b) (- u) = ubounded_by b u.
Proof. 
by rewrite propeqE; split => bu i; move: (bu i); 
  rewrite {2}/GRing.opp/= lemx_opp2.
Qed.

Lemma mxubounded_by_opp (b : M) u :
  ubounded_by (-b) (- u) = lbounded_by b u.
Proof. 
by rewrite propeqE; split => bu i; move: (bu i); 
  rewrite {2}/GRing.opp/= lemx_opp2.
Qed.

(* different canonical route. prevent eq_op porderType ringType *)
Lemma ltmx_def (x y : M) : (x ⊏ y) = (y != x) && (x ⊑ y).
Proof.
rewrite lt_def; congr (~~ _ && _); apply/Bool.eq_iff_eq_true.
split=>/eqP/=->; by rewrite eqxx.
Qed.

Lemma submx_gt0 (x y : M) : ((0 : M) ⊏ y - x) = (x ⊏ y).
Proof. by rewrite !ltmx_def submx_ge0 subr_eq0. Qed.

Lemma mxopen_nge0 : open [set x : M | ~ (0 : M) ⊑ x].
Proof. rewrite openC; apply closed_gemx0. Qed.

Lemma mxopen_nge y :  open [set x : M | ~ y ⊑ x].
Proof.
move: (@mxaddr_continuous _ C m n (-y))=>/continuousP/=/(_ _ mxopen_nge0).
suff ->: [set x : M | ~ y ⊑ x] = [set t | [set x | ~ (0 : M) ⊑ x] (- y + t)] by [].
by apply/funext=>x; rewrite /= addrC submx_ge0.
Qed.

Lemma mxopen_nle0 : open [set x : M | ~ x ⊑ (0 : M)].
Proof.
move: (@mxopp_continuous R C m n)=>/continuousP/=/(_ _ mxopen_nge0).
suff ->: [set x | ~ x ⊑ (0 : M)] = [set t | [set x | ~ (0 : M) ⊑ x] (- t)] by [].
by apply/funext=>x; rewrite /= -{2}oppr0 lemx_opp2. 
Qed.

Lemma mxopen_nle y :  open [set x : M | ~ x ⊑ y].
Proof.
move: (@mxopp_continuous R C m n)=>/continuousP/=/(_ _ (@mxopen_nge (-y))).
suff ->: [set x : M | ~ x ⊑ y] = [set t | [set x : M | ~ - y ⊑ x] (- t)] by [].
by apply/funext=>x; rewrite /= lemx_opp2.
Qed.

Lemma mxclosed_ge (x : M) : closed [set y : M | x ⊑ y ].
Proof. 
set A := ~` [set y : M | ~ (x ⊑ y)].
have ->: (fun x0 : 'M_(m, n) => is_true (x ⊑ x0)) = A.
by rewrite predeqE /A => y/=; rewrite notK.
rewrite closedC. apply/mxopen_nge. 
Qed.

Lemma mxclosed_le (x : M) : closed [set y : M | y ⊑ x ].
Proof. 
set A := ~` [set y : M | ~ (y ⊑ x)].
have ->: (fun x0 : 'M_(m, n) => is_true (x0 ⊑ x)) = A.
by rewrite predeqE /A => y/=; rewrite notK.
rewrite closedC. apply/mxopen_nle. 
Qed.

Lemma mxlim_ge_near (x : M) (u : M ^nat) : 
  cvg u -> (\forall n \near \oo, x ⊑ u n) -> x ⊑ lim u.
Proof.
move=> /[swap] /(closed_cvg ((@Order.le disp (@POrder.Pack disp M B) x)))/= P1;
apply P1. apply: mxclosed_ge.
Qed.

Lemma mxlim_le_near (x : M) (u : M ^nat) : 
  cvg u -> (\forall n \near \oo, u n ⊑ x) -> lim u ⊑ x.
Proof.
move=> /[swap] /(closed_cvg (fun y =>(@Order.le disp (@POrder.Pack disp M B) y x)))/= P1;
apply P1. apply: mxclosed_le.
Qed.

Lemma ler_mxlim_near (u_ v_ : M ^nat) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, u_ n ⊑ v_ n) -> lim u_ ⊑ lim v_.
Proof.
move=> uv cu cv; rewrite -(submx_ge0) -mxlimB.
apply: mxlim_ge_near. apply: is_mxcvgB.
3: by apply: filterS cv => k; rewrite (submx_ge0).
1,3: by []. all: apply uv.
Qed.

Lemma mxlim_ge (x : M) (u : M ^nat) : cvg u -> lbounded_by x u -> x ⊑ lim u.
Proof. by move=>P1 P2; apply: (mxlim_ge_near P1); apply: nearW. Qed.

Lemma mxlim_le (x : M) (u : M ^nat) : cvg u -> ubounded_by x u -> lim u ⊑ x.
Proof. by move=>P1 P2; apply: (mxlim_le_near P1); apply: nearW. Qed.

Lemma ler_mxlim (u v : M^nat) : cvg u -> cvg v ->
  (forall n, u n ⊑ v n) -> lim u ⊑ lim v.
Proof. by move=>P1 P2 P3; apply: (ler_mxlim_near P1 P2); apply: nearW. Qed.

Lemma mxnondecreasing_cvgn_le (u : M ^nat) :
       mxnondecreasing_seq u -> cvg u -> ubounded_by (lim u) u.
Proof. move=>Ph Pc i; apply: mxlim_ge_near=>//; exists i=>// j; apply Ph. Qed.

Lemma mxnonincreasing_cvg_ge (u : M ^nat) : 
  mxnonincreasing_seq u -> cvg u -> lbounded_by (lim u) u.
Proof. move=>Ph Pc i; apply: mxlim_le_near=>//; exists i=>// j; apply Ph. Qed.

Lemma nchain_mono1 (h: nat -> nat) :
  (forall n, (h n.+1 > h n)%N) -> forall n m, (n <= m)%N -> (h n <= h m)%N.
Proof.
move=>P1 n' m'; rewrite leq_eqVlt=>/orP[/eqP->//|P2].
by apply/ltnW/nchain_mono.
Qed.

Lemma le0x_mxZ (X Y : M) a : ((0 : M) ⊑ X) && (X ⊑ Y) -> 0 < a < 1 ->
  ((0 : M) ⊑ a*:X) && (a*:X ⊑ Y).
Proof.
move=>/andP[P1 P2]/andP[P3]; rewrite -subr_gt0=>P4; apply/andP; split.
by move: (lemx_pscale2lP P3 P1); rewrite scaler0.
apply: (le_trans (lemx_pscale2lP P3 P2)).
move: (le_trans P1 P2)=>/(lemx_pscale2lP P4).
by rewrite scaler0 scalerBl scale1r=>/(lemx_add2r (a*:Y)); rewrite addrNK add0r.
Qed.

(*----------------------------------------------------------------------------*)
(* proof sketch : by contradiction                                            *)
(* define diverge seq c i := (i+1) * (1 + |Y|)                                *)
(* exists seq X i s.t. |X i| > c i                                            *)
(* seq (X i)/|X i| is bounded, so exists cvg subseq (X \o h)                  *)
(* forall i, 0 <= (X \o h) i <= Y, so 0 <= lim (X \o h)                       *)
(* seq ((Y - X i)/|Y - X i| \o h) --> - lim (X \o h)                          *)
(* but 0 <= (Y - X i)/|Y - X i| <= 1, so 0 <= - lim (X \o h)                  *)
(* note that |lim (X \o h)| = 1, so contradiction                             *)
(*----------------------------------------------------------------------------*)
Lemma porder_mxnorm_bound (Y : M) : exists c, c > 0 /\ 
  (forall X, ((0 : M) ⊑ X) && (X ⊑ Y) -> c * mx_norm X <= mx_norm Y).
Proof.
case E: (Y == 0); first by move/eqP: E=>->; exists 1; split=>// x; 
  rewrite -eq_le=>/eqP<-; rewrite normv0 mulr0.
have Q1: mx_norm Y > 0 by rewrite normv_gt0 E.
pose c i := i.+1%:R * (1 + mx_norm Y).
have cinc i : c i >= 1 + mx_norm Y by rewrite/c ler_pMl ?addr_gt0// ler1Sn.
have Q2 i : c i > i.+1%:R by rewrite/c ltr_pMr// ltrDl.
have Q3 i : c i > 0 by rewrite /c mulr_gt0// addr_gt0.
have Q4 i : 0 < mx_norm Y / c i by rewrite divr_gt0.
rewrite not_existsP=>P1.
have P2 i: {X : M | ((0 : M) ⊑ X) && (X ⊑ Y) /\ (mx_norm X > c i)}.
  apply/cid; move: (P1 (mx_norm Y/c i)); rewrite -implyNE=>/(_ (Q4 i)).
  rewrite not_existsP; apply contra_not=>P2 x P3; move: (P2 x).
  rewrite -implyNE=>/(_ P3)/negP; rewrite -mulrA ger_pMr// ler_pdivrMl//.
  by rewrite mulr1 real_leNgt// ger0_real// ?normv_ge0//; apply/ltW.
pose x i := projT1 (P2 i).
have P7 i : ((0 : M) ⊑ x i) && (x i ⊑ Y) by move: (projT2 (P2 i))=>[].
have P4 i : c i < mx_norm (x i) by move: (projT2 (P2 i))=>[].
have P5 i : 0 < mx_norm (x i) by apply: (lt_trans _ (P4 _)).
pose nx i := (mx_norm (x i))^-1 *: (x i).
have norm_nx i : mx_norm (nx i) = 1.
  by rewrite /nx normvZ/= gtr0_norm ?mulVf// ?invr_gt0//; apply: lt0r_neq0.
have bound_nx i : mx_norm (nx i) <= 1 by rewrite norm_nx.
move: (Bolzano_Weierstrass bound_nx)=>[h [mn]].
move: (nchain_ge mn)=>hgen.
set y := nx \o h=>Cy; pose ly := lim y : M.
have cy : y --> ly by [].
have P3 i : ((0 : M) ⊑ y i) && (y i ⊑ Y).
  rewrite /y/=/nx; apply/le0x_mxZ=>//.
  rewrite invr_gt0 invf_lt1// P5/=; apply: (lt_trans _ (P4 _)).
  by apply: (le_lt_trans _ (Q2 _)); rewrite -addn1 natrD lerDr.
have ly_ge0: ((0 : M) ⊑ ly) by apply: mxlim_ge=>[//|i]; move: (P3 i)=>/andP[].
have Q5 i: mx_norm (Y - x i) > i.+1%:R.
  rewrite addrC; move: (@levB_normD _ _ mx_norm_vnorm (- x i) Y)=>/=.
  apply: lt_le_trans; rewrite mx_normN ltrBrDl.
  apply: (le_lt_trans _ (P4 _)); rewrite addrC/c mulrDr.
  by rewrite mulr1 lerD2l ler_pMl// ler1Sn.
have Q6 i: mx_norm (Y - x i) > 0 by apply: (lt_trans _ (Q5 _)).
pose nnx i := (mx_norm (Y - x (h i)))^-1 *: (Y - x (h i)).
pose nnx1 i := (mx_norm (Y - x (h i)))^-1 *: Y.
pose nnx2 i := (mx_norm (Y - x (h i)))^-1 * mx_norm (x (h i)).
have: nnx --> 0 - 1 *: ly.
  have ->: nnx = nnx1 - (fun i=>nnx2 i *: y i).
    apply/funext=>i; rewrite/nnx/nnx1 {3}/GRing.add/={4}/GRing.opp/=/nnx2/nx.
    by rewrite scalerA -mulrA mulfV ?mulr1 ?scalerBr// lt0r_neq0.
  have Q7 e: 0 < e -> exists N : nat, forall i : nat, (N <= i)%N -> 
    mx_norm Y / (mx_norm (Y - x (h i))) < e.
    move=>egt0; have /extNum_archi: e / mx_norm Y > 0 by rewrite divr_gt0.
    move=>[k Pk]; exists k=>i Pi; rewrite/=mulrC -ltr_pdivlMr//.
    apply: (le_lt_trans _ Pk); rewrite lef_pV2 ?posrE//; apply/ltW.
    by apply: (le_lt_trans _ (Q5 _)); rewrite ler_nat ltnS; apply: (leq_trans Pi).
  apply mxcvgB. 2: apply mxcvgZ=>[|//].
  apply/mxcvg_seqP=>e egt0; move: (Q7 e egt0)=>[k Pk]; exists k=>i/Pk.
  by rewrite add0r mx_normN/nnx1 normvZ/= gtr0_norm ?invr_gt0// mulrC.
  apply cvg_seqP=>e egt0; move: (Q7 e egt0)=>[k Pk]; exists k=>i/Pk.
  rewrite ltr_pdivrMr// =>P6.
  rewrite/nnx2 -(@mulfV _ (mx_norm (Y - x (h i))) _); last by apply/lt0r_neq0.
  rewrite mulrC -mulrBr normrM gtr0_norm ?ltr_pdivrMl// ?invr_gt0// mulrC.
  by apply: (le_lt_trans _ P6); rewrite -[mx_norm (x (h i))]normvN/= 
    -{2}[Y](addrNK (x (h i))) -{4}(opprK (x (h i))); apply: lev_dist_dist.
rewrite scale1r add0r=>cny.
have Cny: cvg nnx by apply/cvg_ex; exists (-ly). 
have nly_ge0: ((0 : M) ⊑ - ly).
  rewrite -(cvg_lim _ cny); last by apply mxhausdorff.
  apply: mxlim_ge=>[//|i].
  suff: ((0 : M) ⊑ nnx i) && (nnx i ⊑ Y) by move=>/andP[].
  rewrite /nnx; apply/le0x_mxZ; apply/andP; split.
  rewrite submx_ge0. 2: rewrite -submx_ge0 opprB addrC addrNK.
  1,2: by move: (P7 (h i))=>/andP[].
  rewrite invr_gt0//. rewrite invf_lt1//; apply/(le_lt_trans _ (Q5 _))/ler1Sn.
have : mx_norm ly = 1.
  rewrite -(mxlim_mnorm (mx_norm_vnorm) Cy)=>/=.
  suff ->: mx_norm (n:=n) \o y = fun=>1 by apply/lim_cst/ethausdorff.
  by apply/funext=>i; rewrite/=/y//=.
have: ((0 : M) ⊑ ly) && (ly ⊑ 0) by rewrite ly_ge0/= -submx_ge0 add0r.
by rewrite -eq_le eq_sym=>/eqP->/eqP; rewrite normv0 eq_sym oner_eq0.
Qed.

Lemma bounded_mxnorm (bl br : M) u :
  lbounded_by bl u -> ubounded_by br u -> 
  exists c : C, forall n, mx_norm (u n) <= c.
Proof.
move: (porder_mxnorm_bound (br-bl))=>[c [Pc P]] Pl Pr.
exists (mx_norm (br - bl) / c + mx_norm bl)=>i.
rewrite -[u i](addrNK bl). apply: (le_trans (ler_mx_norm_add _ _)).
rewrite lerD2r ler_pdivlMr// mulrC P//; apply/andP; split.
by rewrite submx_ge0. by apply lemx_add2r.
Qed.

Lemma mxnondecreasing_is_cvgn (f : nat -> M) (b : M) :
  mxnondecreasing_seq f -> ubounded_by b f -> cvg f.
move=>P1 P2.
have P3: lbounded_by (f 0%N) f by move=>i; by apply/P1.
move: (bounded_mxnorm P3 P2)=>[c Pc].
move: (Bolzano_Weierstrass Pc)=>[h0 [Ph0 cvgh0]].
apply/cvg_ex. exists (lim (f \o h0)).
apply/(mxcvg_subseqP_cvg (lim (f \o h0)) Pc)=>h1 Ph1 cvgh1.
suff: (lim (f \o h1) ⊑ lim (f \o h0)) && (lim (f \o h0) ⊑ lim (f \o h1)).
by rewrite -eq_le=>/eqP.
apply/andP; split; apply: (mxlim_le)=>[|i].
2: have P4: (f \o h1) i ⊑ (f \o h0) (h1 i) by apply/P1/nchain_ge.
4: have P4: (f \o h0) i ⊑ (f \o h1) (h0 i) by apply/P1/nchain_ge.
2,4: apply: (le_trans P4 _); apply (mxnondecreasing_cvgn_le).
1,5: apply cvgh1. 2,4: apply cvgh0.
all: by move=>x y Pxy; apply P1; apply/nchain_mono1.
Qed.

Lemma mxnonincreasing_is_cvg (f : nat -> M) (b : M) :
    mxnonincreasing_seq f -> lbounded_by b f -> cvg f.
Proof.
rewrite -(mxnondecreasing_opp) -(mxubounded_by_opp) -is_mxcvgNE.
exact: mxnondecreasing_is_cvgn.
Qed.

End Property.

End Theory.
End MxCPorder.
Export MxCPorder.
Export MxCPorder.Exports.
Export MxCPorder.Theory.

End ExtNumTopology.

Export ExtNum.Exports.
Export ExtNumTopology.

Module R_extNumType.

Section R_extNumType.
Variable (R : realType).

Program Definition R_extNumMixin := @ExtNumMixin _ _ 
  [rmorphism of (idfun : R -> R)] (idfun : R -> R) _ _ _ _ _ _ .
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. by []. Qed.
Next Obligation. move=>a.
rewrite (_ : mkset _ = [set x : R | x \in `[-a,a]]); first apply: segment_compact.
by rewrite predeqE=>x/=; rewrite itv_boundlr/= [in X in _ <-> X]/<=%O/= Num.Theory.ler_norml.
Qed.

Canonical R_extNumType := ExtNumType R R R_extNumMixin.

End R_extNumType.

End R_extNumType.
Export R_extNumType.
(* 
(* FinNormedModType *)
(* VOrderFinNormedModType *)
Module FinNormedModule.

Section ClassDef.

Variable (R : realType) (C : extNumType R).

Record class_of (T : Type) := Class {
  base : NormedModule.class_of C T ;
  mixin : Vector.mixin_of (GRing.Lmodule.Pack _ base);
}.
Local Coercion base : class_of >-> NormedModule.class_of.
Definition base2 T (cT : class_of T) := @Vector.Class _ _ (@base T cT) (@mixin T cT).
Local Coercion base2 : class_of >-> Vector.class_of.

Structure type (phC : phant C) := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phC : phant C) (T : Type) (cT : type phC).
Definition class := let: Pack _ c  as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phC T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT (b : NormedModule.class_of _ T) & phant_id (@NormedModule.class _ (Phant C) bT) b =>
  fun mT m & phant_id (@Vector.class _ (Phant C) mT) (@Vector.Class _ T b m) =>
    @Pack phC T (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack _ phC cT xclass.
Definition lmodType := @GRing.Lmodule.Pack _ phC cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack _ cT xclass.
Definition pseudoMetricNormedZmodType :=
  @PseudoMetricNormedZmodule.Pack _ phC cT xclass.
Definition normedModType := @NormedModule.Pack _ phC cT xclass.
Definition vectType := @Vector.Pack _ phC cT xclass.
Definition normedMod_zmodType := @GRing.Zmodule.Pack normedModType xclass.
Definition normedMod_lmodType := @GRing.Lmodule.Pack _ phC normedModType xclass.
Definition normedMod_vectType := @Vector.Pack _ phC normedModType xclass.

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
Notation finNormedModType C := (type (Phant C)).
Notation FinNormedModType C T := (@pack _ _ (Phant C) T _ _ id _ _ id).
Notation "[ 'finNormedModType' C 'of' T 'for' cT ]" :=  (@clone _ _ (Phant C) T cT _ idfun)
  (at level 0, format "[ 'finNormedModType'  C  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'finNormedModType' C 'of' T ]" :=  (@clone _ _ (Phant C) T _ _ id)
  (at level 0, format "[ 'finNormedModType'  C  'of'  T ]") : form_scope.
End Exports.

End FinNormedModule.

Import FinNormedModule.Exports.

Module VOrderFinNormedModule.

Section ClassDef.

Record mixin_of (R : realType) (C: extNumType R) (V : finNormedModType C)
  (Rorder : POrder.mixin_of (Equality.class V))
  (le_op := POrder.le Rorder)
  := Mixin {
  _ : closed [set x : V | (le_op 0 x)] ;
}.

Variable (R : realType) (C: extNumType R).

Record class_of (T : Type) := Class {
  base : FinNormedModule.class_of C T;
  order_mixin : POrder.mixin_of (Equality.class (FinNormedModule.Pack _ base));
  vorder_mixin : VOrder.mixin_of order_mixin;
  mixin : mixin_of order_mixin;
}.
Local Coercion base : class_of >-> FinNormedModule.class_of.
Definition vorder_base T (cT : class_of T) :=
  @VOrder.Class _ _ (@base T cT) (order_mixin cT) (vorder_mixin cT).
Local Coercion vorder_base : class_of >-> VOrder.class_of.

Structure type (phC : phant C) := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phC : phant C) (T : Type) (cT : type phC).
Definition class := let: Pack _ c  as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phC T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack (b0 : FinNormedModule.class_of C T)
           (om0 : POrder.mixin_of (Equality.class (FinNormedModule.Pack (Phant C) b0)))
           (m0 : @mixin_of _ C (@FinNormedModule.Pack _ _ (Phant C) T b0) om0) :=
  fun bT (b : FinNormedModule.class_of C T)
      & phant_id (@FinNormedModule.class _ _ (Phant C) bT) b =>
  fun om & phant_id om0 om =>
  fun vmT vm & phant_id (@VOrder.class _ (Phant C) vmT) (@VOrder.Class _ T b om vm) =>
  fun m & phant_id m0 m =>
  @Pack phC T (@Class T b om vm m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack _ phC cT xclass.
Definition lmodType := @GRing.Lmodule.Pack _ phC cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack _ cT xclass.
Definition pseudoMetricNormedZmodType :=
  @PseudoMetricNormedZmodule.Pack _ phC cT xclass.
Definition normedModType := @NormedModule.Pack _ phC cT xclass.
Definition finNormedModType := @FinNormedModule.Pack _ _ phC cT xclass.
Definition vectType := @Vector.Pack _ phC cT xclass.
Definition porderType := @POrder.Pack vorder_display cT xclass.
Definition vorderType := @VOrder.Pack _ phC cT xclass.
Definition finNormedMod_zmodType := @GRing.Zmodule.Pack finNormedModType xclass.
Definition finNormedMod_lmodType := @GRing.Lmodule.Pack _ phC finNormedModType xclass.
Definition finNormedMod_vectType := @Vector.Pack _ phC finNormedModType xclass.
Definition finNormedMod_porderType := @POrder.Pack vorder_display finNormedModType xclass.
Definition finNormedMod_vorderType := @VOrder.Pack _ phC finNormedModType xclass.

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
Notation vorderFinNormedModType C := (type (Phant C)).
Notation VOrderFinNormedModType C T m := 
  (@pack _ _ (Phant C) T _ _ m _ _ id _ id _ _ id _ id).
Notation VOrderFinNormedModMixin := Mixin.
Notation "[ 'vorderFinNormedModType' C 'of' T 'for' cT ]" := (@clone _ _ (Phant C) T cT _ idfun)
  (at level 0, format "[ 'vorderFinNormedModType'  C  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'vorderFinNormedModType' C 'of' T ]" := (@clone _ _ (Phant C) T _ _ id)
  (at level 0, format "[ 'vorderFinNormedModType'  C  'of'  T ]") : form_scope.
End Exports.

End VOrderFinNormedModule.

Import VOrderFinNormedModule.Exports.

Section FinNormedModTypeComplete.
Context {R : realType} {C : extNumType R} {V : finNormedModType C}.
Import Vector.InternalTheory Num.Def Num.Theory numFieldNormedType.Exports.

Lemma bounded_normr_mxnorm m n (f: V -> 'M[C]_(m,n)) (lf: linear f) (bf: bijective f) :
  (exists c, c > 0 /\ forall x : V, `|x| <= c * mx_norm (f x))
  /\ (exists c, c > 0 /\ forall x : V, mx_norm (f x) <= c * `|x|).
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
apply: continuous_subspaceT=>x _; apply: r2v_continuous.
rewrite predeqE=>/=x; split=>[Px|[y Py1 <-//]].
by exists (v2r x); rewrite/= v2rK.
Qed.

Lemma V_complete (F : set (set V)) :
  ProperFilter F -> cauchy F -> cvg F.
Proof. by apply: bounded_compact_complete; apply: compact_norm_le. Qed.

End FinNormedModTypeComplete.

Arguments bijective_to_mx_cvgE [R C V m n f u a].
Arguments bijective_of_mx_cvgE [R C V m n f u a].
Arguments bijective_to_mx_is_cvgE [R C V m n f u].
Arguments bijective_of_mx_is_cvgE [R C V m n f u].
Arguments bijective_to_mx_limE [R C V m n f u].
Arguments bijective_of_mx_limE [R C V m n f u].

Canonical finNormedMod_completeType (R : realType) (C: extNumType R) 
  (V : finNormedModType C) := CompleteType V (@V_complete _ _ V).
Canonical finNormedMod_CompleteNormedModule (R : realType) (C: extNumType R) 
  (V : finNormedModType C) := Eval hnf in [completeNormedModType C of V].
Canonical vorderFinNormedMod_completeType (R : realType) (C: extNumType R)
  (V : vorderFinNormedModType C) := CompleteType V (@V_complete _ _ V).
Canonical vorderFinNormedMod_CompleteNormedModule (R : realType) 
  (C: extNumType R) (V : vorderFinNormedModType C) := 
  Eval hnf in [completeNormedModType C of V].

Canonical extNum_regular_finNormedModType (R : realType) (C: extNumType R) := 
  Eval hnf in (FinNormedModType C C^o).
Canonical extNum_finNormedModType (R : realType) (C: extNumType R) :=
  Eval hnf in [finNormedModType C of C for [finNormedModType C of C^o]].

Section FinNormedModTheory.
Variable (R : realType) (C: extNumType R) (V : finNormedModType C).
Import Num.Def Num.Theory Vector.InternalTheory.
Implicit Type (f g: nat -> V) (n: nat) (s a b : V).

Local Canonical finNormedMod_CompleteNormedModule.

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

End FinNormedModTheory.

Section LinearContinuous.
Context {R : realType} {C : extNumType R}.
Import Vector.InternalTheory.
Implicit Type (U V W: finNormedModType C).
Lemma linear_continuous {U V} (f : {linear U -> V}) :
  continuous f.
Proof.
pose g x := v2r (f (r2v x)); suff <-: r2v \o g \o v2r = f.
apply: continuous_comp_simp; first by apply: v2r_continuous.
apply: continuous_comp_simp; last by apply: r2v_continuous.
by apply/mxlinear_continuous=>a x y; rewrite /g !linearP.
by apply/funext=>x; rewrite /g/= !v2rK.
Qed.

Lemma linear_continuousP {U V} (f : U -> V) :
  linear f -> continuous f.
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_continuous. Qed.

Lemma linear_cvg {U V} (f : {linear U -> V}) (u : nat -> U) (a : U) :
  u --> a -> f \o u --> f a.
Proof. move=>cu. apply: continuous_cvg=>//. apply: linear_continuous. Qed.

Lemma linear_cvgP {U V} (f : U -> V) (u : nat -> U) (a : U) :
  linear f -> u --> a -> f \o u --> f a.
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_cvg. Qed.

Lemma linear_is_cvg {U V} (f : {linear U -> V}) (u : nat -> U) :
  cvg u -> cvg (f \o u).
Proof. move/cvg_ex=>[a Pa]; apply/cvg_ex; exists (f a); by apply: linear_cvg. Qed.

Lemma linear_is_cvgP {U V} (f : U -> V) (u : nat -> U) :
  linear f -> cvg u -> cvg (f \o u).
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_is_cvg. Qed.

Lemma linear_lim {U V} (f : {linear U -> V}) (u : nat -> U) :
  cvg u -> lim (f \o u) = f (lim u).
Proof. by move=>cu; apply: cvg_lim; [apply: Vhausdorff | apply: linear_cvg]. Qed.

Lemma linear_limP {U V} (f : U -> V) (u : nat -> U) :
  linear f -> cvg u -> lim (f \o u) = f (lim u).
Proof. move=>lf; rewrite (linearlfE lf); exact: linear_lim. Qed.

Lemma linearl_continuous {U V W} (f : {bilinear U -> V -> W}) (x : V):
  continuous (f^~ x).
Proof. have <-: applyr f x = f^~x by apply/funext/applyrE. apply: linear_continuous. Qed. 

Lemma linearl_cvg {U V W} (f : {bilinear U -> V -> W}) (x : V)
 (u : nat -> U) (a : U):
  u --> a -> (f^~x) \o u --> f a x.
Proof. have <-: applyr f x = f^~x by apply/funext/applyrE. apply: linear_cvg. Qed.

Lemma linearl_is_cvg {U V W} (f : {bilinear U -> V -> W}) (x : V) (u : nat -> U) :
  cvg u -> cvg (f^~x \o u).
Proof. have <-: applyr f x = f^~x by apply/funext/applyrE. apply: linear_is_cvg. Qed.

Lemma linearl_lim {U V W} (f : {bilinear U -> V -> W}) (x : V) (u : nat -> U) :
  cvg u -> lim (f^~x \o u) = f (lim u) x.
Proof. have <-: applyr f x = f^~x by apply/funext/applyrE. apply: linear_lim. Qed.

Lemma linearr_continuous {U V W} (f : {bilinear U -> V -> W}) (x : U):
  continuous (f x).
Proof. exact: linear_continuous. Qed. 

Lemma linearr_cvg {U V W} (f : {bilinear U -> V -> W}) (x : U)
  (u : nat -> V) (a : V):
  u --> a -> (f x) \o u --> f x a.
Proof. exact: linear_cvg. Qed.

Lemma linearr_is_cvg {U V W} (f : {bilinear U -> V -> W}) (x : U) (u : nat -> V) :
  cvg u -> cvg (f x \o u).
Proof. exact: linear_is_cvg. Qed.

Lemma linearr_lim {U V W} (f : {bilinear U -> V -> W}) (x : U) (u : nat -> V) :
  cvg u -> lim (f x \o u) = f x (lim u).
Proof. exact: linear_lim. Qed.

Lemma linear_to_mx_continuous {U} m n (f : {linear U -> 'M[C]_(m,n)}) :
  continuous f.
Proof.
pose g x := (f (r2v x)); suff <-: g \o v2r = f.
apply: continuous_comp_simp; first by apply: v2r_continuous.
by apply/mxlinear_continuous=>a x y; rewrite /g !linearP.
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
by apply/mxlinear_continuous=>a x y; rewrite /g !linearP.
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
Variable (R : realType) (C: extNumType R) (V : vorderFinNormedModType C).
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

Definition v2r_mxnormcvg := MxCPorder
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

Lemma lim_gev_near (x : V) (u : V ^nat) : 
  cvg u -> (\forall n \near \oo, x ⊑ u n) -> x ⊑ lim u.
Proof.
move=> /[swap] /(closed_cvg (fun y=>x ⊑ y))/= P1; apply/P1/closed_gev.
Qed.

Lemma lim_lev_near (x : V) (u : V ^nat) : 
  cvg u -> (\forall n \near \oo, u n ⊑ x) -> lim u ⊑ x.
Proof.
move=> /[swap] /(closed_cvg (fun y : V=>y ⊑ x))/= P1;apply/P1/closed_lev.
Qed.

Lemma lev_lim_near (u_ v_ : V ^nat) : cvg u_ -> cvg v_ ->
  (\forall n \near \oo, u_ n ⊑ v_ n) -> lim u_ ⊑ lim v_.
Proof.
move=> uv cu cv; rewrite -(subv_ge0) -limB//.
apply: lim_gev_near=>//. apply: is_cvgB=>//.
by apply: filterS cv => k; rewrite (subv_ge0).
Qed.

Lemma lim_gev (x : V) (u : V ^nat) : cvg u -> lbounded_by x u -> x ⊑ lim u.
Proof.
by move=>P1 P2; apply: (lim_gev_near P1); apply: nearW.
Qed.

Lemma lim_lev (x : V) (u : V ^nat) : cvg u -> ubounded_by x u -> lim u ⊑ x.
Proof.
by move=>P1 P2; apply: (lim_lev_near P1); apply: nearW.
Qed.

Lemma lev_lim (u v : V^nat) : cvg u -> cvg v ->
  (forall n, u n ⊑ v n) -> lim u ⊑ lim v.
Proof.
by move=>P1 P2 P3; apply: (lev_lim_near P1 P2); apply: nearW.
Qed.

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
move: (mxnondecreasing_is_cvgn v2r_mxnormcvg P3 P4).
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

(* R is extNumType R *)
(* C is extNumType R *)


Module CTopology.
Import numFieldNormedType.Exports.

(* C : it is the finNormedModType R
Module CRegular.
Local Open Scope complex_scope.

Definition cregular R : Type := R.
Local Notation "R ^c" := (cregular R) (at level 2, format "R ^c") : type_scope.

Section CRegularFinNormedModule.
Variable R : realType.

Implicit Types c x y : R.
Implicit Types z e   : cregular R[i].

Definition scalec c e :=
  let: a +i* b := e in (c * a) +i* (c * b).

Program Definition cregular_lmodMixin :=
  @LmodMixin R [zmodType of R[i]^c] scalec _ _ _ _.
Next Obligation. by move=>c d [a b]; rewrite/= !mulrA. Qed.
Next Obligation. by move=>[a b]; rewrite/= !mul1r. Qed.
Next Obligation. by move=>x [a b] [c d]; rewrite/= !mulrDr; simpc. Qed.
Next Obligation. by move=>[a b] c d; rewrite/= !mulrDl; simpc. Qed.

Canonical cregular_lmodType :=
  Eval hnf in LmodType R R[i]^c cregular_lmodMixin.

Lemma cregular_vectAxiom: Vector.axiom 2 R[i]^c.
Proof.
  exists (fun z => \row_(i < 2) (tnth [tuple (Re z); (Im z)] i)).
  + move=> /= c [a1 b1] [a2 b2]; apply/matrixP=> /= i j.
    by rewrite !mxE {i}!(tnth_nth 0) /=; case: j=> [] [|[|]].
  + exists (fun (v : 'rV[R]_2) => v 0 0 +i* v 0 1).
      by case=> [a b]; rewrite !mxE !(tnth_nth 0).
    move=> v /=; apply/matrixP=> i j; rewrite !mxE.
    rewrite !(tnth_nth 0) !ord1; case: j=> [] [|[|]] //= lt.
      have /eqP->//: Ordinal lt == 0 by rewrite eqE.
      have /eqP->//: Ordinal lt == 1 by rewrite eqE.
Qed.

Definition cregular_vectMixin := VectMixin cregular_vectAxiom.
Canonical complex_vectType :=
  Eval hnf in VectType R R[i]^c cregular_vectMixin.

Definition cr_norm (x : R[i]^c) := Re `|x|.
Program Definition cregular_normedZmodMixin :=
  @Num.NormedMixin _ [zmodType of R[i]^c] (Order.POrder.class R) cr_norm _ _ _ _.
Next Obligation.
move=>x y; move: (Num.Theory.ler_normD x y).
by rewrite lecE=>/andP[] _; rewrite raddfD.
Qed.
Next Obligation. move=>x; rewrite/cr_norm/=; exact: ComplexField.eq0_normc. Qed.
Next Obligation. by move=>x n; rewrite/cr_norm Num.Theory.normrMn raddfMn. Qed.
Next Obligation. by move=>x; rewrite/cr_norm Num.Theory.normrN. Qed.

Canonical cregular_normedZmodType :=
    Eval hnf in NormedZmodType R R[i]^c cregular_normedZmodMixin.

Canonical cregular_pointedType := [pointedType of R[i]^c for pointed_of_zmodule [zmodType of R[i]^c]].
Canonical cregular_filteredType := [filteredType R[i]^c of R[i]^c for filtered_of_normedZmod [normedZmodType R of R[i]^c]].
Canonical cregular_topologicalType := (TopologicalType R[i]^c (topologyOfEntourageMixin (uniformityOfBallMixin
                                 (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _)))).
Canonical cregular_uniformType := (UniformType R[i]^c (uniformityOfBallMixin
                            (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _))).

Check [pointedType of R[i]^c].
Check [uniformType of R[i]^c].
Check @PseudoMetricMixin.
Check PseudoMetricType R[i]^c (pseudoMetric_of_normedDomain [normedZmodType R of R[i]^c]).
(* Definition cregular_pseudoMetricMixin :=
  @PseudoMetricMixin R R[i]^c fct_ball_center fct_ball_sym fct_ball_triangle fct_entourage.
Canonical fct_pseudoMetricType := PseudoMetricType (T -> U) fct_pseudoMetricType_mixin. *)

Canonical cregular_pseudoMetricType := (PseudoMetricType R[i]^c (pseudoMetric_of_normedDomain [normedZmodType R of R[i]^c])).

Lemma cregular_norm_ball :
  @ball _ [pseudoMetricType R of R[i]^c] = ball_ (fun x : R[i]^c => `| x |).
Proof. by rewrite /Num.Def.normr /ball_ predeq3E/= /ball/=/Num.Def.normr/=. Qed.

Definition cregular_PseudoMetricNormedZmodMixin := PseudoMetricNormedZmodule.Mixin cregular_norm_ball.
Canonical cregular_pseudoMetricNormedZmodType := PseudoMetricNormedZmodType R R[i]^c cregular_PseudoMetricNormedZmodMixin.

Lemma cr_normZ (a: R) (f: R[i]^c) : cr_norm (a *: f) = `|a| * cr_norm f.
Proof. 
case: f=>[b c]; rewrite/cr_norm/GRing.scale/= !exprMn -mulrDr.
by rewrite Num.Theory.sqrtrM ?Num.Theory.sqr_ge0// Num.Theory.sqrtr_sqr.
Qed.

Definition cregular_NormedModMixin := NormedModMixin cr_normZ.
Canonical cregular_normedModType := NormedModType R R[i]^c cregular_NormedModMixin.

Canonical cregular_finNormedModType := 
  (FinNormedModType R R[i]^c).

Lemma CR_bounded_compact (e : R) : compact [set x : R[i]^c | `|x| <= e].
Proof. exact: compact_norm_le. Qed.

(* after canonical C as a topology type from numFieldType *)
Lemma C_bounded_compact (a : C): compact [set x : C | `|x| <= a].
Proof.
case E: (a \is Num.real).
rewrite (_ : mkset _ = [set x : R[i] | cr_norm x <= Re a]).
move: (@CR_bounded_compact R (Re a))=>P1.
move=>/=x Px/= P2.
move: (P1 x Px P2).
rewrite/cluster /Num.Def.normr/=.
move=>[b]/=[Pb1] Pb2.
exists b=>/=; split=>// y z Py Pz. apply: (Pb2 y z Py).
move: Pz. rewrite/nbhs/=/nbhs_ball_/==>[[e/= egt0 Pe]].
exists (Re e)=>/=[|w Pw]. by apply: real_gt0.
apply Pe. move: Pw egt0. 
by rewrite/={1}/Num.Def.normr/=/cr_norm !ltcE/==>->/andP[]->.
rewrite predeqE=>x/=; rewrite/cr_norm lecE/=.
suff ->: Im a == 0 by []. by move/RIm_real/eqP: E; rewrite realc_eq0.
rewrite (_ : mkset _ = set0).
apply: compact0.
rewrite predeqE=>x/=; split=>// P; move: E; 
by rewrite Num.Theory.realE (le_trans (Num.Theory.normr_ge0 x) P).
Qed.

End CRegularFinNormedModule.
End CRegular. *)
*)