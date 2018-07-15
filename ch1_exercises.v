
Load ch1_ref.

(* Chapter 1 Exercises *)
Section Chapter_1_Exercises.
  (* 1.1. Define Function Composition
          and show associativity *)
  Definition fc {A B C} (g : B -> C) (f : A -> B) : A -> C
    := (* fill in here... *) .
  Lemma fc_assoc {A B C D : Type}
    (* fill in full theorem statement here... *)
  .
  Proof. trivial. Qed. (* the proof should be trivial *)


  (* 1.2 Derive pair_recursion from fst/snd projections
         and    sigma_recursion from proj1/proj2 *)
  Definition pair_recursion_alt {A B}
             (C : Type)
             (g : A -> B -> C)
             (p : prod A B)
    : C
    := (* fill in here... *) .
  Definition sigma_recursion_alt {A B}
             (C : Type)
             (g : forall x : A, B x -> C)
             (p : exists x : A, B x )
    : C
    := (* fill in here... *) .

  (* 1.3 Derive pair_induction from fst/snd projedtions
         and    sigma_induction from proj1/proj2 *)
  Print uniq_prod. (* recall this lemma *)
  (* use the lemma, but not induction on pairs *)
  Definition pair_induction {A B}
             (C : (prod A B) -> Type)
             (g : forall (x:A) (y:B), (C (pair x y)))
             (x : prod A B)
    : C x
    := (* fill in here... *) .
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
    := (* fill in here... *) .


  (* 1.4 Derive nat recursion from iteration *)
  Fixpoint iter (C:Type) (c0:C) (cs:C->C) (n:nat) : C
    := match n with
       | O   => c0
       | S n => cs (iter C c0 cs n)
       end.
  Definition nat_recursion_iter (C:Type) :
    C -> (nat -> C -> C) -> nat -> C
    := (* fill in here... *) .
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
  Qed.

  
  (* 1.5 Bool Sum *)
  Definition BSum (A B : UU) :=
    exists x:bool, bool_rect (fun y : bool => UU) A B x.
  Definition Binl {A B} (a:A) : BSum A B := {true ; a}.
  Definition Binr {A B} (b:B) : BSum A B := {false ; b}.
  Definition BSum_induction {A B}
             (C : BSum A B -> UU)
             (f : forall a:A, C (Binl a))
             (g : forall b:B, C (Binr b))
             (x : BSum A B)
    : C x
    := (* fill in here... *) (* use sig_rect *) .
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
  Definition Bfst {A B} (x : BProd A B) : A := x true.
  Definition Bsnd {A B} (x : BProd A B) : B := x false.
  Definition uniq_BProd {A B} {x : BProd A B}
    : Bpair (Bfst x) (Bsnd x) = x
    := (* fill in here... *) .
  Definition BProd_induction {A B}
             (C : BProd A B -> Type)
             (f : forall (a:A) (b:B), C (Bpair a b))
             (x : BProd A B)
    : C x
    := (* fill in here... *) .
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
    (* fill in here... *) .
  Definition exp   (x y : nat) : nat :=
    (* fill in here... *) .

  Definition is_a_semiring (A : Type) :=
    exists
      (plus        : A -> A -> A)
      (zero        : A)
      (times       : A -> A -> A)
      (one         : A)
      (* fill in properties here... *)
      (plus_assoc  : (*...*) )
      
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
  Defined.

  (* 1.9 Define the type family Fin *)
    (* unsure how to do this *)


  (* 1.11 Triple not is constructively just not *)
  Definition intro_double_not {A:Prop} : A -> ~~A :=
    (* fill in here... *) .
  Definition triple_not {A:Prop} : ~~~A -> ~A :=
    (* fill in here... *) .

  (* 1.12 More Simple Logic Problems as Types *)
  Definition if_a_then_if_b_then_a {A B}
    : A -> (B -> A)
    := (* fill in here... *) .
  Definition if_not_a_or_not_b_then_not_a_and_b {A B}
    : ((~A) + (~B))%type -> ~(A * B)%type
    := (* fill in here... *) .

  (* 1.13 Not Not Excluded Middle *)
  Definition not_not_excluded_middle {P} :
    ~~(P + ~P)%type
    := (* fill in here... *) .

  (* 1.14 *)
    (* skipping for now; no formal work? *)

  (* 1.15 indiscernability from path induction *)
    (* see inline earlier *)

  (* 1.16 commutativity of addition of natural numbers *)
  Lemma nat_commutativity :
    forall i j : nat, i+j = j+i.
  Proof. (* fill in here... *)
  Qed.
End Chapter_1_Exercises.


