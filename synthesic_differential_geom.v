From mathcomp Require Import all_ssreflect ssralg.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.
Import GRing.

Section Param1.
Variable R : comUnitRingType.
Definition disk n := { x in R | x ^+ n.+1 == 0 }. (* とりあえず 依存和で *)
Definition zero_disk n : disk n.
Proof. apply (@exist _ _ 0); by rewrite /= expr0n. Defined.
Notation "''D_' k" := (disk k)
    (at level 8, k at level 2, format "''D_' k").

Definition alpha (ab : R * R) (d : 'D_1) :=
  if ab.1 == 0
  then sval d * ab.2
  else ab.1 + sval d * ab.2.
Arguments alpha _ _ /.
Lemma alphaE ab d : alpha ab d = ab.1 + (sval d) * ab.2.
Proof.
rewrite /alpha.
case: ifP => [/eqP ->| ? //].
by rewrite add0r.
Qed.
Lemma alpha0E x : alpha (0, x) = (fun d => sval d * x).
Proof. by rewrite /alpha /= eqxx. Qed.

Variable beta : ('D_1 -> R) -> R * R.
Axiom bijective_alpha : cancel beta alpha /\ cancel alpha beta.

Lemma beta2E t : (beta (fun d => sval d * t)).2 = t.
Proof.
case: bijective_alpha => bac abc.
suff->: beta (fun d : 'D_1 => sval d * t) = (0, t) => //.
by rewrite -alpha0E abc.
Qed.

Section DualRing.
Definition dual_one : R * R := (1, 0).
Definition dual_mul a b : R * R := (a.1 * b.1, a.1 * b.2 + a.2 * b.1).
Lemma dual_mulA : associative dual_mul.
Proof.
case=> [f11 f12] [f21 f22] [f31 f32].
by rewrite /dual_mul ?(mulrDl, mulrA, mulrDr, addrA).
Qed.
Lemma dual_mul_1l : left_id dual_one dual_mul.
Proof.
case=> [f11 f12].
by rewrite /dual_mul !mul1r mul0r addr0. 
Qed.
Lemma dual_mul_1r : right_id dual_one dual_mul.
Proof.
case=> [f11 f12].
by rewrite /dual_mul !mulr1 mulr0 add0r. 
Qed.
Lemma dual_mul_addl : left_distributive dual_mul (@add_pair R R).
Proof.
case=> [f11 f12] [f21 f22] [f31 f32].
rewrite /add_pair /dual_mul ?(mulrDl, mulrA, mulrDr, addrA).
congr (_, _).
congr (_ + _).
rewrite -!addrA.
congr (_ + _).
by rewrite addrC.
Qed.
Lemma dual_mul_addr : right_distributive dual_mul (@add_pair R R).
case=> [f11 f12] [f21 f22] [f31 f32].
rewrite /add_pair /dual_mul ?(mulrDl, mulrA, mulrDr, addrA).
congr (_, _).
congr (_ + _).
rewrite -!addrA.
congr (_ + _).
by rewrite addrC.
Qed.
Fact dual1_nonzero : dual_one != (0, 0).
Proof.
apply/eqP; case.
move/eqP.
by rewrite oner_eq0.
Qed.
Definition dual_ringMixin :=
  RingMixin dual_mulA dual_mul_1l dual_mul_1r dual_mul_addl dual_mul_addr
            dual1_nonzero.
Canonical dual_ringType :=
  Eval hnf in RingType (R * R) dual_ringMixin.

Lemma dual_mulC : commutative dual_mul.
Proof.
case=> [f11 f12] [f21 f22].
rewrite /dual_mul mulrC.
congr (_, _); rewrite addrC.
congr (_ + _); by rewrite mulrC.
Qed.

Canonical dual_comRingType :=
  Eval hnf in ComRingType dual_ringType dual_mulC.
End DualRing.

Lemma fun_eqP : Equality.axiom (fun f g => beta f == beta g).
Proof.
case: bijective_alpha => bac abc.
move=> f g.
case Hfg: (beta f == beta g); constructor.
 apply (can_inj bac); apply/eqP: Hfg.
move=> Hfgn; move: Hfgn Hfg => ->.
by rewrite eqxx.
Qed.

Canonical fun_eqMixin := EqMixin fun_eqP.
Canonical fun_eqType := Eval hnf in EqType _ fun_eqMixin.
Definition fun_choiceMixin := CanChoiceMixin (proj1 bijective_alpha).
Canonical fun_choiceType := Eval hnf in ChoiceType _ fun_choiceMixin.

Section FunZmod.
Definition fun_zero : 'D_1 -> R := alpha (0, 0).
Definition fun_opp f : 'D_1 -> R  := alpha (- beta f).
Definition fun_add f g : 'D_1 -> R := alpha (beta f + beta g).

Lemma fun_addA : associative fun_add.
Proof.
case: bijective_alpha => bac abc.
move=> f1 f2 f3.
apply (can_inj bac).
by rewrite !abc addrA.
Qed.
Lemma fun_addC : commutative fun_add.
Proof.
case: bijective_alpha => bac abc.
move=> f1 f2.
apply (can_inj bac).
by rewrite !abc addrC.
Qed.
Lemma fun_add0 : left_id fun_zero fun_add.
Proof.
case: bijective_alpha => bac abc.
move=> f.
apply (can_inj bac).
by rewrite !abc add0r.
Qed.
Lemma fun_addN : left_inverse fun_zero fun_opp fun_add.
Proof.
case: bijective_alpha => bac abc.
move=> f.
apply (can_inj bac).
by rewrite !abc addNr.
Qed.
Definition fun_zmodMixin :=
  Zmodule.Mixin fun_addA fun_addC fun_add0 fun_addN.
Canonical fun_zmodType := Eval hnf in ZmodType _ fun_zmodMixin.
End FunZmod.

Section FunRing.
Definition fun_one : 'D_1 -> R  := alpha (1, 0).
Definition fun_mul f g : 'D_1 -> R := alpha (dual_mul (beta f) (beta g)).
Lemma fun_mulA : associative fun_mul.
Proof.
case: bijective_alpha => bac abc.
move=> f1 f2 f3.
apply (can_inj bac).
rewrite !abc.
exact: (@mulrA dual_ringType).
Qed.
Lemma fun_mul_1l : left_id fun_one fun_mul.
Proof.
case: bijective_alpha => bac abc.
move=> f.
apply (can_inj bac).
rewrite !abc.
exact: (@mul1r dual_ringType).
Qed.
Lemma fun_mul_1r : right_id fun_one fun_mul.
Proof.
case: bijective_alpha => bac abc.
move=> f.
apply (can_inj bac).
rewrite !abc.
exact: (@mulr1 dual_ringType).
Qed.
Lemma fun_mul_addl : left_distributive fun_mul fun_add.
Proof.
case: bijective_alpha => bac abc.
move=> f1 f2 f3;
apply (can_inj bac).
rewrite !abc.
exact: (@mulrDl dual_ringType).
Qed.
Lemma fun_mul_addr : right_distributive fun_mul fun_add.
case: bijective_alpha => bac abc.
move=> f1 f2 f3;
apply (can_inj bac).
rewrite !abc.
exact: (@mulrDr dual_ringType).
Qed.
Fact fun1_nonzero : fun_one != fun_zero.
Proof.
apply/eqP => H.
move/eqP: (f_equal (fun f => f (zero_disk 1)) H) => {H}.
by rewrite /fun_one /fun_zero /alpha !eqxx !mul0r /= addr0 !oner_eq0.
Qed.
Definition fun_ringMixin :=
  RingMixin fun_mulA fun_mul_1l fun_mul_1r fun_mul_addl fun_mul_addr
            fun1_nonzero.
Canonical fun_ringType :=
  Eval hnf in RingType ('D_1 -> R) fun_ringMixin.
End FunRing.

Section FunComRing.
Lemma fun_mulC : commutative fun_mul.
Proof.
move=> f1 f2; rewrite /fun_mul.
congr alpha.
exact: (@mulrC dual_comRingType).
Qed.
Definition fun_comRingType :=
  Eval hnf in ComRingType fun_ringType fun_mulC.
End FunComRing.

Lemma mulKr z x y : alpha (z, x) = alpha (z, y) -> x = y.
Proof.
case: bijective_alpha => bac abc H.
by case: (can_inj abc H).
Qed.

Lemma beta_hom f g : beta (f * g) = dual_mul (beta f) (beta g).
Proof.
case: bijective_alpha => bac abc.
apply: (can_inj abc).
by rewrite bac.
Qed.

Lemma alpha_hom x y : alpha (dual_mul x y) = alpha x * alpha y.
Proof.
case: bijective_alpha => bac abc.
apply: (can_inj bac).
by rewrite beta_hom !abc.
Qed.

Lemma mul_hom (f g :'D_1 -> R) : forall d, (f * g) d = f d * g d.
Proof.
case: bijective_alpha => bac abc d.
have ->: (f * g) d = (alpha (dual_mul (beta f) (beta g))) d by [].
have ->: f d = alpha (beta f) d by rewrite bac.
have ->: g d = alpha (beta g) d by rewrite bac.
case: (beta f) => f1 f2; case: (beta g) => g1 g2.
rewrite !alphaE.
case: d => /= d H.
rewrite !mulrDr mulrA !mulrDl -!addrA.
congr (_ + _); rewrite addrC mulrA.
congr (_ + _); rewrite mulrCA mulrA.
set A := d * f1 * g2.
rewrite mulrAC mulrA -expr2.
move/eqP: H => ->;
by rewrite !mul0r addr0.
Qed.
  
Local Definition aux (f : R -> R) x :=
  (fun (d : 'D_1) => f (x + (sval d)) - f x).
Definition derivative f x := (beta (aux f x)).2.
Lemma beta_eq0 g : beta g = (g (zero_disk 1), (beta g).2).
Proof.
case: bijective_alpha => bac _.
rewrite -[X in (X _, _)](bac g).
rewrite alphaE /= mul0r addr0.
by case: (beta g) => ? ?.
Qed.
Definition higher_derivative n := iter n derivative.
Notation "g '" := (derivative g) (at level 3, format "g '").
Notation "g ^( n )" := (higher_derivative n g) (at level 3, format "g ^( n )").

Lemma taylor_expansion f x h :
  h ^+ 2 = 0 -> f (x + h) = f x + h * f ' x.
Proof.
move=> H; apply/eqP.
rewrite [X in (_ == X)]addrC -subr_eq.
case: bijective_alpha => bac abc.
have H' : (fun h => f (x + sval h) - f x) = alpha (0, f ' x).
 apply (can_inj bac).
 by rewrite abc /derivative beta_eq0 /= addr0 subrr. 
have d : { d : 'D_1 | sval d = h }
 by apply: (@exist _ _ (@exist _ _ h _))=> //; rewrite H /=.
move: (f_equal (fun e => e (proj1_sig d)) H').
by rewrite /alpha /= eqxx (proj2_sig d) => ->.
Qed.

Lemma beta_auxE f x : beta (aux f x) = (0, f ' x).
Proof.
rewrite beta_eq0 /derivative.
congr (_, _).
by rewrite /aux /= addr0 subrr.
Qed.

Lemma intro_d x y :
  (forall d : R, d ^+ 2 = 0 -> d * x = d * y) -> x = y.
Proof.
move=> H.
apply: (@mulKr 0).
apply functional_extensionality.
case => d /= /eqP dH.
by rewrite /= eqxx /= H // dH.
Qed.

Lemma der_comp f g x : 
  (f \o g) ' x = f ' (g x) * g ' x.
Proof. 
apply: intro_d => d dH.
move/eqP: (@taylor_expansion (f \o g) x d dH) => fgct.
move/eqP: (f_equal (fun x => f x) (@taylor_expansion g x d dH)) => gt.
rewrite (@taylor_expansion f (g x) (d * g 'x)) in gt.
 rewrite [X in (_ == X)]addrC -subr_eq in gt.
 rewrite [X in (_ == X)]addrC -subr_eq in fgct.
 move/eqP: fgct => <-. 
 rewrite [X in d * X]mulrC mulrA.
 by move/eqP: gt => <-.
by rewrite expr2 mulrCA !mulrA -expr2 dH !mul0r.
Qed.

Lemma subrC (x y : R) : x - y = - y + x.
Proof. by rewrite addrC. Qed.

Lemma leibniz_rule f g x :
  (fun x => f x * g x) ' x = f ' x * g x + f x * g ' x.
Proof.
apply: intro_d => d dH.
set fg := (fun x => f x * g x).
rewrite mulrDr.
move/eqP: (@taylor_expansion fg x d dH) => fgt.
move/eqP: (f_equal (fun y => y * g x) (@taylor_expansion f x d dH)) => f'gt.
move/eqP: (f_equal (fun y => f x * y) (@taylor_expansion g x d dH)) => fg't.
rewrite mulrDr [X in (_ == X)]addrC -subr_eq mulrCA in fg't.
rewrite mulrDl [X in (_ == X)]addrC -subr_eq -mulrA in f'gt.
rewrite [X in (_ == X)]addrC -subr_eq in fgt.
move/eqP: fg't => <-. 
move/eqP: f'gt => <-.
move/eqP: fgt => <-.
subst fg => /=.
rewrite (@taylor_expansion f x d dH) (@taylor_expansion g x d dH).
rewrite !mulrDl !mulrDr.
do 2! rewrite subrC !addrA -subrC subrr add0r.
rewrite subrK [in RHS]addrC -!addrA.
congr (_ + _). set A := d * f ' x * g x.
by rewrite mulrCA !mulrA -expr2 dH !mul0r addr0.
Qed.

Fixpoint canonical_element (n : nat) :=
  match n with
  | S n' => 
    (1 : R) + canonical_element n'
  | O => 0
  end.

Section HigherOrder.
Variable k : nat.
Hypothesis I_k1_is_a_unit :
  forall j : 'I_k.+1, canonical_element j \is a unit.
Hypothesis taylor_expansionk :
  forall g x (h : 'D_k),
    g (x + sval h) = \sum_ ( i < k.+1 ) (g ^(i) x / canonical_element i`!) * (sval h) ^+ i.
Lemma taylor_expansionk1 g x (h j : 'D_k) :
  g (x + (sval h + sval j)) =
  \sum_ ( i < k.+1 ) (g ^(i) x / canonical_element i`!) * (sval h + sval j) ^+ i 
                   + (g ^(k.+1) x / canonical_element k.+1`!) * (sval h + sval j) ^+ k.+1.
Proof.
  rewrite addrA taylor_expansionk.
  apply: etrans.
  apply: eq_bigr.
  move=> i _.
  rewrite (taylor_expansionk (fun x => g ^(i) x / canonical_element i`!) x h).
  rewrite big_distrl.

End HigherOrder.
  
Hypothesis taylor_expansionk : 
  
