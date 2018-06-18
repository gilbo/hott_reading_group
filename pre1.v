
(* Pre 1 *)
(* For pre-face? pre-lude? pre-load? *)

(* This file is meant to capture anything we want to refer back to
   from chapter 1, while ditching the extraneous stuff *)

(*
   The odd use of UU and redefinition of basic stuff is taken
   from a mixture of using
     https://mdnahas.github.io/doc/Reading_HoTT_in_Coq.pdf
   as a guide, along with the UniMath library
*)

Require Export Coq.Init.Notations.

Definition UU := Type.
Identity Coercion fromUUtoType : UU >-> Sortclass.

Notation "A -> B" := (forall (_ : A), B) : type_scope.



(* Equality, or path types *)
Inductive paths {A:UU} (a:A) : A -> UU :=
  paths_refl : paths a a.
Arguments paths_refl {A a}, [A] a.
Arguments paths_rect [A].
Hint Resolve paths_refl : core .
Notation "a = b" := (paths a b) : type_scope.
Notation idpath := paths_refl.

(* Product/pair types *)
Inductive prod (A B : UU) : UU :=
| pair : A -> B -> prod A B .
Arguments pair [A B].
Notation "X * Y" := (prod X Y) : type_scope.
Notation "( x , y , .. , z )" :=
  (pair .. (pair x y) .. z) : core_scope.

(* the unit or True type *)
Inductive unit  : UU :=
| tt    : unit.

(* pair deconstruction, and uniqueness principle *)
Definition fst {A B : UU} (p:A*B) :=
  match p with (a,b) => a end.
Definition snd {A B : UU} (p:A*B) :=
  match p with (a,b) => b end.
Lemma prod_uniq {X Y} : forall (x : X*Y),
    (fst x, snd x) = x.
Proof. intro x. destruct x. simpl. reflexivity. Defined.

(* dependent pair type / sigma types *)
Inductive sigUU { T: UU } ( P: T -> UU ) :=
| spair : forall x:T, P x -> sigUU P.
Notation "'sigma' x .. y , p" :=
  (sigUU (fun x => .. (sigUU (fun y => p)) ..))
    (at level 200, x binder, y binder, right associativity)
  : type_scope.
Notation "'exists' x .. y , p" :=
  (sigUU (fun x => .. (sigUU (fun y => p)) ..))
    (at level 200, x binder, y binder, right associativity)
  : type_scope.
Notation "{ x ; .. ; y ; z }"
  := (spair _ x .. (spair _ y z) ..) : fibration_scope.
Open Scope fibration_scope.
Delimit Scope fibration_scope with fiber.
(* the odd semicolon at the end notation is unfortunately required *)

(* projection for dependent pairs *)
Definition proj1 {A : UU} {B : A -> UU}
           (p : exists (x:A), B x) : A
  := match p with {a;b} => a end.
Definition proj2 {A : UU} {B : A -> UU}
           (p : exists (x:A), B x) : B (proj1 p)
  := match p with {a;b} => b end.
Notation "x .1" := (proj1 x)
                     (at level 3) : fibration_scope.
Notation "x .2" := (proj2 x)
                     (at level 3) : fibration_scope.

(* type theoretic axiom of choice *)
Definition ac {X Y : UU} {R : X -> Y -> UU}
           (g : forall x:X, exists y:Y, R x y)
  : exists (f:X->Y), forall x:X, R x (f x)
  := let F := (fun (f : X -> Y) =>
                 forall x : X, R x (f x))
     in spair F (fun x => (g x).1) (fun x => (g x).2).

(*
  Definition Magma := exists X, X -> X -> X.
*)

(* sum/co-product/variant types *)
Inductive coprod (A B : UU) : UU :=
| inl : A -> coprod A B
| inr : B -> coprod A B
.
Arguments coprod_rect {_ _} _ _ _ _.
Arguments inl {A B} _, [A] B _.
Arguments inr {A B} _, A [B] _.
Notation "X + Y" := (coprod X Y) : type_scope.

(* empty or False type *)
Inductive empty : UU := .

(* bool type *)
Inductive bool  : UU :=
| false : bool
| true : bool
.
Definition negb (b:bool) := if b then false else true.

(* natural numbers *)
Inductive nat : UU :=
| O : nat
| S : nat -> nat.
Definition succ := S.
Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.
Open Scope nat_scope.

(* The usual Coq mode has a more sophisticated
   num constant parser. But we can kludge small constants
   for most of what we're interested in like this. *)
Notation  "0" := (O) : nat_scope.
Notation  "1" := (S 0) : nat_scope.
Notation  "2" := (S 1) : nat_scope.
Notation  "3" := (S 2) : nat_scope.
Notation  "4" := (S 3) : nat_scope.
Notation  "5" := (S 4) : nat_scope.
Notation  "6" := (S 5) : nat_scope.
Notation  "7" := (S 6) : nat_scope.
Notation  "8" := (S 7) : nat_scope.
Notation  "9" := (S 8) : nat_scope.
Notation "10" := (S 9) : nat_scope.

(* Here is the basic addition function *)
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O     => m
  | S n'  => S (plus n' m)
  end.
Notation "x + y" := (plus x y) : nat_scope.

(* some results about plus and natural numbers *)
Lemma eq_S : forall n m : nat, n = m -> S n = S m.
Proof.
  intros n m E; destruct E; reflexivity.
Qed. 

Lemma plus_n_O : forall n : nat, n = n + 0.
Proof.
  intro n; induction n;
    [ reflexivity |
      simpl; rewrite <- IHn; reflexivity ].
Qed.

Lemma plus_Sn_m : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m; induction n; simpl; try reflexivity;
    apply eq_S; assumption.
Qed.

Lemma plus_assoc {i j k : nat} :
  i + (j + k) = (i + j) + k.
Proof.
  induction i; simpl; try (apply eq_S); trivial.
Qed.

(* will probably need to be updated... *)
Ltac natred := simpl;
               repeat (rewrite <- plus_n_O);
               repeat (rewrite <- plus_Sn_m; simpl);
               repeat (rewrite plus_assoc).

(* standard constructive/intuitionistic definition of not *)
Definition not (A:UU) : UU := A -> empty.
Notation "~ A" := (not A) : type_scope.
Arguments not _%type.
Notation "a <> b" := (not (a = b)) : type_scope.

(* less than or equal for natural numbers *)
Definition LEq n m := exists k:nat, n+k = m.
Notation "n <= m" := (LEq n m) : type_scope.

Lemma LEq_O_n (n:nat) : LEq 0 n.
Proof. exists n. reflexivity. Qed.
Lemma LEq_n (n:nat) : LEq n n.
Proof. exists 0. natred. trivial. Qed.
Lemma LEq_S (n m:nat) : LEq n m -> LEq n (S m).
Proof.
  intro Lnm; destruct Lnm as [p Enm];
  exists (S p); natred; apply eq_S; trivial.
Qed.
Lemma LEq_n_S {n m:nat} : LEq n m -> LEq (S n) (S m).
Proof.
  intro Lnm; destruct Lnm as [p Enm];
  exists p; natred; apply eq_S; trivial.
Qed.

(* some results about paths that we may wish to discard? *)
Lemma indiscernability_of_identiticals {A : UU} :
  forall (C:A->UU),
  forall (x y : A) (p : x = y), (C x) -> (C y).
Proof.
  intros C x y E Cx. induction E. apply Cx.
Defined.

Definition path_induction {A:UU}
           {C : forall x y : A, x=y -> UU}
           (c : forall x : A, C x x idpath)
  : forall x y : A, forall p : x=y, C x y p
  := fun x y p => match p with
                  | idpath _ => c x
                  end.
Definition based_path_induction {A:UU}
           {a : A}
           {C : forall x : A, a=x -> UU}
           (c : C a idpath)
  : forall (x : A) (p : a=x), C x p
  := fun x p => match p with
                | idpath _ => c
                end.

Check nat = nat.

