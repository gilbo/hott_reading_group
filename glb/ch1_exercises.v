
Load ch1_ref.

(* Chapter 1 Exercises *)
Section Chapter_1_Exercises.
  (* 1.1. Define Function Composition
          and show associativity *)
  Definition fc {A B C} (g : B -> C) (f : A -> B) : A -> C
    := (* fill in here... *) fun a => g (f a).
  Lemma fc_assoc {A B C D : Type}
    (* fill in full theorem statement here... *)
        {f : A -> B}
        {g : B -> C}
        {h : C -> D}
    : fc h (fc g f) = fc (fc h g) f.
  Proof. trivial. Qed. (* the proof should be trivial *)


  (* 1.2 Derive pair_recursion from fst/snd projections
         and    sigma_recursion from proj1/proj2 *)
  Definition pair_recursion_alt {A B}
             (C : Type)
             (g : A -> B -> C)
             (p : prod A B)
    : C
    := (* fill in here... *) g (fst p) (snd p).
  Definition sigma_recursion_alt {A B}
             (C : Type)
             (g : forall x : A, B x -> C)
             (p : exists x : A, B x )
    : C
    := (* fill in here... *) g p.1 p.2.

  (* 1.3 Derive pair_induction from fst/snd projedtions
         and    sigma_induction from proj1/proj2 *)
  Print uniq_prod. (* recall this lemma *)
  (* use the lemma, but not induction on pairs *)
  Definition pair_induction {A B}
             (C : (prod A B) -> Type)
             (g : forall (x:A) (y:B), (C (pair x y)))
             (x : prod A B)
    : C x
    := (* fill in here... *)
      indiscernability_of_identiticals
      (prod A B) C
      _ _
      (uniq_prod x)
      (g (fst x) (snd x)).
  (* here's a similar lemma to use.
     use it, but not induction on dependent pairs *)
  Lemma uniq_sigma {A B}
        (x : exists a:A, B a)
    : { x.1 ; x.2 } = x.
  Proof. destruct x. trivial. Qed.
  Definition sigma_induction {A B}
             (C : (sigma x : A, B x) -> Type)
             (g : forall (a : A) (b : B a), C {a;b})
             (p : sigma x : A, B x )
    : C p
    := (* fill in here... *)
      indiscernability_of_identiticals
        (sigma a:A, B a) C
        _ _
        (uniq_sigma p)
        (g p.1 p.2).


  (* 1.4 Derive nat recursion from iteration *)
  Fixpoint iter (C:Type) (c0:C) (cs:C->C) (n:nat) : C
    := match n with
       | O   => c0
       | S n => cs (iter C c0 cs n)
       end.
  Definition nat_recursion_iter (C:Type) :
    C -> (nat -> C -> C) -> nat -> C
    := (* fill in here... *)
      fun c0 cs n =>
         snd (iter (nat*C)%type
                   (0,c0)
                   (fun p => (S (fst p), cs (fst p) (snd p)))
                   n).
  Lemma Def_Eq_nat_recursion {C:Type} {c0 cs} (n:nat)
    : (nat_recursion_iter C c0 cs O = c0) *
      (nat_recursion_iter C c0 cs (S n)
       =
       cs n (nat_recursion_iter C c0 cs n)).
  Proof. 
    (* fill in here... *)
    (* Hint: I had to use 'assert' to claim a sub-lemma *)
    (* Hint: you can use the 'pose' tactic to name a subexpression *)
    (* Hint: the tactics 'fold' and 'unfold' help manage
             named expressions *)
    pose (unwrap_rec :=
            iter (nat * C) (0, c0)
                 (fun p : nat * C =>
                    (S (fst p),
                     cs (fst p) (snd p)))).
    assert (forall m:nat, fst (unwrap_rec m) = m) as Count.
        induction m; trivial.
        unfold unwrap_rec; simpl;
        apply eq_S; assumption.
    split; trivial;
    unfold nat_recursion_iter; simpl;
    rewrite Count; trivial.
  Qed.

  
  (* 1.5 Bool Sum *)
  Definition BSum (A B : UU) :=
    exists x:bool, bool_rect (fun y : bool => UU) A B x.
  Definition Binl {A B} (a:A) : BSum A B := {false ; a}.
  Definition Binr {A B} (b:B) : BSum A B := {true ; b}.
  Definition BSum_induction {A B}
             (C : BSum A B -> UU)
             (f : forall a:A, C (Binl a))
             (g : forall b:B, C (Binr b))
             (x : BSum A B)
    : C x
    := (* fill in here... *) (* use sig_rect *)
      sig_rect _ _ C
               (fun tag => match tag with
                           | false => f
                           | true => g end) x.
  Lemma DefEq_BSum_induction {A B} {C f g} :
    (forall a:A, BSum_induction C f g (Binl a) = f a) *
    (forall b:B, BSum_induction C f g (Binr b) = g b).
  Proof. split; trivial. Qed. (* should verify trivially *)


  (* 1.6 Bool Prod *)
  Definition BProd (A B : UU) :=
    forall x:bool, bool_rect (fun x:bool => UU) A B x.
  Definition Bpair {A B} (a : A) (b : B) : BProd A B :=
    fun x:bool => match x with
      | false => a
      | true  => b
    end.
  Axiom funext :
    forall (A : Type) (B : A -> Type)
           (f g : forall x:A, B x),
    (forall x : A, (f x) = (g x)) -> f = g.
  Definition Bfst {A B} (x : BProd A B) : A := x false.
  Definition Bsnd {A B} (x : BProd A B) : B := x true.
  Definition uniq_BProd {A B} {x : BProd A B}
    : Bpair (Bfst x) (Bsnd x) = x
    := (* fill in here... *)
      funext _ _
             (Bpair (Bfst x) (Bsnd x))
             x
             (fun tag : bool => match tag with
                                | true   => idpath (x true)
                                | false  => idpath (x false) end).
  Definition BProd_induction {A B}
             (C : BProd A B -> Type)
             (f : forall (a:A) (b:B), C (Bpair a b))
             (x : BProd A B)
    : C x
    := (* fill in here... *)
      indiscernability_of_identiticals _
            C _ _ uniq_BProd
            (f (Bfst x) (Bsnd x)).
  (* I skipped over this one *)
  (*Lemma DefEq_BProd_induction {A B} {C g} :
    forall (a:A) (b:B),
      BProd_induction C g (Bpair a b) = g a b.*)

  (* 1.7 Alternative Path Induction *)
    (* skipping *)

  (* 1.8 Multiplication and Exponentiation of nat;
         (nat, +, 0, *, 1) is a semi-ring *)
    (* define using nat_recursion *)
  Definition times (x y : nat) : nat :=
    (* fill in here... *)
    nat_rect (fun _ => nat)
             0
             (fun _ => plus x)
             y.
  Definition exp   (x y : nat) : nat :=
    (* fill in here... *)
    nat_rect (fun _ => nat)
             1
             (fun _ => times x)
             y.

  Definition is_a_semiring (A : Type) :=
    exists
      (plus        : A -> A -> A)
      (zero        : A)
      (times       : A -> A -> A)
      (one         : A)
      (* fill in properties here... *)
      (plus_assoc  : forall a b c : A,
          plus (plus a b) c = plus a (plus b c))
      (plus_zero   : forall a : A, (plus zero a = a) * (plus a zero = a))
      (plus_symm   : forall a b : A, plus a b = plus b a)
      (* (A, times, one) is a monoid *)
      (times_assoc : forall a b c : A,
          times (times a b) c = times a (times b c))
      (times_one   : forall a : A, (times one a = a) * (times a one = a))
      (* plus/times distribute *)
      (dist_left   : forall a b c : A,
          times a (plus b c) = plus (times a b) (times a c))
      (dist_right  : forall a b c : A,
          times (plus b c) a = plus (times b a) (times c a))
      (* zero times annihilation *)
      (times_zero  : forall a : A, (times zero a = zero) *
                                   (times a zero = zero))
    , unit.

  (* this tactic helps name properties in the proof *)
  Ltac show_exists nm := match goal with
                         | |- exists (_ : ?T), _ =>
                           assert T as nm; [ | exists nm]
                         end.

  Theorem nat_is_a_semiring :
    is_a_semiring nat.
  Proof. (* fill in here... *)
    unfold is_a_semiring.
    exists plus.
    exists 0.
    exists times.
    exists 1.
    show_exists plus_assoc.
      intros; induction a; natred; trivial.
    show_exists plus_zero.
      intros; natred; split; trivial.
    show_exists plus_symm.
      intros; induction a; natred; trivial.
    assert (forall a b c : nat,
               times a (b + c) = times a b + times a c) as dist_left.
      intros; induction c; natred; trivial.
      rewrite IHc; repeat( rewrite <- plus_assoc );
      rewrite (plus_symm a); trivial.
    show_exists times_assoc.
      intros; induction c; simpl; trivial.
      rewrite dist_left; rewrite IHc; trivial.
    show_exists times_one.
      intros; split; natred; trivial.
      induction a; natred; trivial.
    exists dist_left.
    show_exists dist_right.
      intros; induction a; natred; trivial.
      rewrite IHa;
      repeat (rewrite <- plus_assoc);
      repeat rewrite (plus_symm _ c);
      repeat (rewrite <- plus_assoc); trivial.
    show_exists times_zero.
      intros; split; induction a; natred; trivial.
    exact tt.
  Defined.

  (* 1.9 Define the type family Fin *)
    (* unsure how to do this *)


  (* 1.11 Triple not is constructively just not *)
  Definition intro_double_not {A:Prop} : A -> ~~A :=
    (* fill in here... *)
    fun a na => na a.
  Definition triple_not {A:Prop} : ~~~A -> ~A :=
    (* fill in here... *)
    fun nnna a => nnna (intro_double_not a).

  (* 1.12 More Simple Logic Problems as Types *)
  Definition if_a_then_if_b_then_a {A B}
    : A -> (B -> A)
    := (* fill in here... *)
      fun a => fun b => a.
  Definition if_not_a_or_not_b_then_not_a_and_b {A B}
    : ((~A) + (~B))%type -> ~(A * B)%type
    := (* fill in here... *)
      fun or_nanb and_ab =>
        coprod_rect (fun _ => empty)
                    (fun na => na (fst and_ab))
                    (fun nb => nb (snd and_ab))
                    or_nanb.

  (* 1.13 Not Not Excluded Middle *)
  Definition not_not_excluded_middle {P} :
    ~~(P + ~P)%type
    := (* fill in here... *)
      fun n_OR => (fun np => n_OR (inr np))
                    (fun p  => n_OR (inl p)).

  (* 1.14 *)
    (* skipping for now; no formal work? *)

  (* 1.15 indiscernability from path induction *)
    (* see inline earlier *)

  (* 1.16 commutativity of addition of natural numbers *)
  Lemma nat_commutativity :
    forall i j : nat, i+j = j+i.
  Proof. (* fill in here... *)
    induction i; induction j; natred; trivial.
  Qed.
End Chapter_1_Exercises.


