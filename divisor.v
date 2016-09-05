Require Import Arith Bool.

Definition specification_of_divmod(divmod : nat -> nat -> nat -> nat -> nat * nat) :=
  (forall y q u : nat,
    divmod 0 y q u = (q, u))
  /\
  (forall x y q : nat,
    divmod (S x) y q 0 = divmod x y (S q) y)
  /\
  (forall x y q u : nat,
    divmod (S x) y q (S u) = divmod x y q u).

Definition specification_of_div(div : nat -> nat -> nat) :=
  (forall x : nat,
    div x 0 = 0)
  /\
  (forall (divmod : nat -> nat -> nat -> nat -> nat * nat),
   specification_of_divmod divmod ->
   forall x y : nat,
     div x (S y) = fst (divmod x y 0 y)).

Definition specification_of_mod(mod : nat -> nat -> nat) :=
  (forall x : nat,
    mod x 0 = 0)
  /\
  (forall (divmod : nat -> nat -> nat -> nat -> nat * nat),
   specification_of_divmod divmod ->
   forall x y : nat,
     mod x (S y) = y - snd (divmod x y 0 y)).

Proposition divides_zero :
  forall (divmod : nat -> nat -> nat -> nat -> nat * nat),
    specification_of_divmod divmod ->
  forall (mod : nat -> nat -> nat),
    specification_of_mod mod ->
    forall j : nat,
      mod 0 j = 0.
Proof.
  intros divmod spec_divmod.
  intros mod spec_mod.
  intro j.
  assert (spec_mod2 := spec_mod).
  destruct spec_mod as [mod_bc mod_ic].

  induction j.
    apply mod_bc.
    
    rewrite -> (mod_ic divmod spec_divmod).
    
    destruct spec_divmod as [divmod_bc [divmod_ic1 divmod_ic2]].
    rewrite -> divmod_bc.
    unfold snd.
    rewrite <- (minus_n_n j).  
    reflexivity.
Qed.

Proposition divides_self :
  forall (divmod : nat -> nat -> nat -> nat -> nat * nat),
    specification_of_divmod divmod ->
  forall (mod : nat -> nat -> nat),
    specification_of_mod mod ->
    forall j : nat,
      mod j j = 0.
Proof.
  intros divmod spec_divmod.
  intros mod spec_mod.
  intro j.
  assert (spec_mod2 := spec_mod).
  destruct spec_mod as [mod_bc mod_ic].

  induction j.
    apply mod_bc.
    
    rewrite -> (mod_ic divmod spec_divmod).
    
    destruct spec_divmod as [divmod_bc [divmod_ic1 divmod_ic2]].
    induction j.
      rewrite -> divmod_ic1.
      rewrite -> divmod_bc.
      unfold snd.
      rewrite <- (minus_n_n 0).
      reflexivity.
    
      rewrite -> divmod_ic2.
      destruct mod in IHj0.


    unfold snd.
    rewrite <- (minus_n_n j).  
    reflexivity.
Qed.

Proposition everything_divides_zero :
  forall (divides : nat -> nat -> Prop),
    specification_of_divides divides ->
    forall j : nat,
      divides 0 j.
Proof.
  intros div spec_div.
  intro j.
  destruct spec_div as [div_zero [div_self div_ic]].
  apply div_zero.

  intros divides specification_of_divides.
  intro j.
  rewrite -> specification_of_divides.
  induction j.
    exists 0.
    ring.
Admitted.

Proposition everything_divides_one :
  forall (divides : nat -> nat -> Prop),
    specification_of_divides divides ->
    forall j : nat,
      divides 1 j.
Proof.
  intros divides specification_of_divides.
  intro j.
  rewrite -> specification_of_divides.
  induction j.
    exists 0.
    ring.

    exists (S j).
    ring.
Qed.

Proposition divides_one :
  forall (divides : nat -> nat -> Prop),
    specification_of_divides divides ->
    forall j i : nat,
      divides j i = divides j (j + i).
Proof.
  intros divides specification_of_divides.
  intros j i.
  rewrite ->2 specification_of_divides.
  induction j.
     induction i.
       exists.

     exists.

     exists.

Proposition divides_one :
  forall (divides : nat -> nat -> Prop),
    specification_of_divides divides ->
    forall j : nat,
      divides j 1.
Proof.
  intros divides specification_of_divides.
  intro j.
  (*rewrite -> specification_of_divides.
  *)
  induction j.
    apply (everything_divides_zero divides specification_of_divides 1).

    rewrite -> specification_of_divides.

Qed.

Lemma one_is_divisor_of_six :
  forall (divisor : nat -> nat -> bool),
    specification_of_divisor divisor ->
      divisor 6 1 = true.
Proof.
  intros divisor spec.
  rewrite (divisor_one divisor spec).
  reflexivity.
Qed.

Lemma six_is_divisor_of_six :
  forall (divisor : nat -> nat -> bool),
    specification_of_divisor divisor ->
      divisor 6 6 = true.
Proof.
  intros divisor spec.
  rewrite (divisor_self divisor spec).
  reflexivity.
Qed.

Lemma one_plus_i_equals_S_i :
  forall i : nat,
    plus 1 i = (S i).
Proof.
  intro i.
  unfold plus.
  reflexivity.
Qed.

Lemma simplify_minus :
  forall i j,
    (S i) - (S j) = i - j.
Proof.
  intros i j.
  rewrite (minus_plus_simpl_l_reverse i j 1).
  rewrite -> (one_plus_i_equals_S_i i).
  rewrite -> (one_plus_i_equals_S_i j).
  reflexivity.
Qed.

Lemma two_is_divisor_of_six :
  forall (divisor : nat -> nat -> bool),
    specification_of_divisor divisor ->
      divisor 6 2 = true.
Proof.
  intros divisor spec.
  rewrite ->2 (divisor_ic divisor spec).
  rewrite ->2 simplify_minus.
  rewrite <- minus_n_O.
  rewrite ->2 simplify_minus.
  rewrite <- minus_n_O.
  rewrite (divisor_self divisor spec).
  reflexivity.

  rewrite ->2 simplify_minus.
  rewrite <- minus_n_O.
  rewrite ->2 simplify_minus.
  rewrite <- minus_n_O.
  unfold beq_nat.
  unfold gt_Sn_O.
  rewrite gt_pred.
  ring.
Qed.

Lemma three_is_divisor_of_six :
  forall (divisor : nat -> nat -> bool),
    specification_of_divisor divisor ->
      divisor 6 3 = true.
Proof.
  intros divisor spec.
  rewrite -> (divisor_ic divisor spec).
  rewrite ->3 simplify_minus.
  rewrite <- minus_n_O.
  rewrite (divisor_self divisor spec).
  reflexivity.
Qed.

Definition specification_of_bool_to_int(bool_to_int : bool -> nat) :=
  (bool_to_int false = 0)
  /\
  (bool_to_int true = 1).

Definition specification_of_num_divisors(num_divisors : nat -> nat) :=
  (num_divisors 1 = 1)
  /\
  (forall (divisor : nat -> nat -> bool),
    specification_of_divisor divisor ->
    forall (bool_to_int : bool -> nat),
    specification_of_bool_to_int bool_to_int ->
    forall j : nat,
      num_divisors (S j) = (bool_to_int (divisor (S j) j)) + (num_divisors j)).

Lemma two_has_two_divisors :
  forall (num_divisors : nat -> nat),
    specification_of_num_divisors num_divisors ->
  forall (divisor : nat -> nat -> bool),
    specification_of_divisor divisor ->
  forall (bool_to_int : bool -> nat),
    specification_of_bool_to_int bool_to_int ->
      num_divisors 2 = 2.
Proof.
  intros num_divisor num_spec.

  intros divisor specification_of_divisor.

  intros bool_to_int specification_of_bool_to_int.

  destruct num_spec as [one_bc one_ic].

  rewrite (one_ic divisor specification_of_divisor bool_to_int specification_of_bool_to_int).

  destruct specification_of_bool_to_int as [bti_bc bti_ic].

  rewrite (divisor_one divisor specification_of_divisor).

  rewrite bti_ic.

  rewrite one_bc.

  ring.
Qed.

Lemma seven_has_two_divisors :
  forall (num_divisors : nat -> nat),
    specification_of_num_divisors num_divisors ->
  forall (divisor : nat -> nat -> bool),
    specification_of_divisor divisor ->
  forall (bool_to_int : bool -> nat),
    specification_of_bool_to_int bool_to_int ->
      num_divisors 7 = 2.
Proof.
  intros num_divisor num_spec.

  intros divisor specification_of_divisor.

  intros bool_to_int specification_of_bool_to_int.

  destruct num_spec as [one_bc one_ic].

  rewrite ->6 (one_ic divisor specification_of_divisor bool_to_int specification_of_bool_to_int).

  destruct specification_of_bool_to_int as [bti_bc bti_ic].

  rewrite -> (divisor_ic divisor specification_of_divisor).
  rewrite ->? simplify_minus.
  rewrite <- minus_n_O.
  

  rewrite bti_ic.

  rewrite one_bc.

  ring.
Qed.










