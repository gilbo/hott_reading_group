
(* Chapter 1 *)

(* Prelude ... *)
(* For reasons that won't be clear until substantially
   later in reading through HoTT, we will need to redefine
   some of the standard functionality in Coq to coincide
   more accurately with the book.
   These definitions will be explained later.  In making
   these changes, I used
   https://mdnahas.github.io/doc/Reading_HoTT_in_Coq.pdf
   as a guide, along with the UniMath library
*)

Definition UU := Type.
Identity Coercion fromUUtoType : UU >-> Sortclass.

Inductive paths {A:UU} (a:A) : (A->UU) :=
  paths_refl : paths a a.
Hint Resolve paths_refl : core .
Notation "a = b" := (paths a b)
  (at level 70, no associativity) : type_scope.
Notation idpath := paths_refl.









Inductive empty : UU := .


Inductive bool  : UU :=
          | true  : bool
          | false : bool
          .

Definition negb (b:bool) := if b then false else true.

Inductive coprod (A B : UU) : UU :=
          | ii1 : A -> coprod A B
          | ii2 : B -> coprod A B
          .

Arguments coprod_rect {_ _} _ _ _ _.
Arguments ii1 {_ _} _.
Arguments ii2 {_ _} _.

Notation inl := ii1.
Notation inr := ii2.

Notation "X + Y" := (coprod X Y).

Inductive nat : UU :=
  | O : nat
  | S : nat -> nat.

Definition succ := S.

Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.
Open Scope nat_scope.

(*
Fixpoint add n m
Fixpoint sub n m
*)
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


(* ... *)



















(* 1.2 Function Types *)
Section Function_Types.
  (* The use of 'Section' here is important in order
      to limit the definition scope of these
      Variables. *)
  Variables A B : UU.
  Variable f : A -> B.
  Variable y : B.
  (* note how we choose to declare A and B in the
      'universe' UU.  We could also declare them in the
      universe type 'Type'.  The exact consequences of
      the difference are beyond me. *)

  (* notice how we can use Definition (y1) to simply bind
      a term to a name.  We can also specify a type
      annotation on the term, (y2) in which case Coq
      will check that annotation for us.
      *** TRY: changing the type to something invalid.
               what does Coq do now? ***
      We can also define parameters/arguments on the
      left side of the := definition assignment. (y3)
      When we do so, those arguments can be typed or
      untyped.  If we then also provide a type annotation
      (y4) we can effectively provide a 'return type'
  *)
  Definition const_y1 := fun x:A => y.
  Definition const_y2 : A -> B := fun x => y.
  Definition const_y3 (x:A) := y.
  Definition const_y4 (x:A) : B := y.
  (* notice how the Print command will output the
     definition of the term and its type *)
  Print const_y3.

  (* TODO: Should we include more details on different
           ways of making definitions in Coq? *)
End Function_Types.


(* Now that we've exited our first Section, which
   names are still in scope? *)
Print const_y3.
(* Notice the parameter list and type for const_y3 now.
    Some of the variables seem to be explicit arguments.
    But did all the variables get 'captured' in this way? *)

(*  ** UNCOMMENT THIS COMMAND and TRY IT **
  Print A.
*)


(* 1.3 Universes and families *)
Section Universes_and_Families.
  Variables A B : UU.

  (* In the following, note the new command 'Check'
      This command runs the typechecker on the given term.
      If a type annotation is provided, the checker attempts
      to verify that the claimed judgement can be derived.
      If no annotation is provided, the checker attempts
      to infer an appropriate type annotation. *)
  Definition const_fam_example : A -> UU := fun(x:A) => B.
  Definition const_fam_ex2 (x:A) := B.
  Check const_fam_ex2.
  Check const_fam_ex2 : A -> UU.
End Universes_and_Families.

(* 1.4 Dependent Function Types *)
Section Dependent_Function_Types.
  Variable A : UU.
  Variable B : A -> UU.

  Definition pi_type_example := forall x:A, B x.

  Definition swap_explicit :
    forall (A:UU) (B:UU) (C:UU),
      (A -> B -> C) -> (B -> A -> C)
  :=
    fun A B C g =>
      fun b a => (g a b).

  (* these curly braces declare that A B C are implicit
     arguments.  So, Coq will try to infer their values
     rather than require them to be explicitly provided.
     Also notice how (and we've snuck this in a bit)
     we can declare multiple variable names with the same
     type by just placing spaces between them.
  *)
  Definition swap {A B C : UU}
  : (A -> B -> C) -> (B -> A -> C)
  := fun g => fun b a => (g a b).
End Dependent_Function_Types.

(* 1.5 Product Types *)
Section Product_Types.
  Variables A B : UU.

  (* Function and Dependent Function types are core parts
     of Coq, unlike pairs/products, sums, and the other
     stuff we'll be looking at.  These are all (to Coq)
     just different 'Inductive' datatypes.
     Unfortunately, the default such types in Coq conflict
     with our UU strategy and modifications for doing HoTT.
     So, to keep things consistent, and break everything
     down as much as possible, we'll be redefining as
     many of these basic constructs as possible.
  *)
  Inductive prod (A B : UU) : UU :=
    | pair : A -> B -> prod A B .
  Implicit Arguments pair [A B].
  Notation "X * Y" := (prod X Y) : type_scope.
  Notation "( x , y , .. , z )" :=
    (pair .. (pair x y) .. z) : core_scope.
  (* Mostly, we can ignore this all as required magic for
     now.  The 'Implicit Arguments' command is a different
     way of achieving the same goal as {A:UU} style
     implicit arguments.  The 'Notation' command allows
     us to do operator overloading by redefining the
     behavior of the Coq parser. *)

  (* Now let's check out what this name is bound to,
     and how we might form product types and pairs *)
  Print prod.
  Check prod A B.

  Variables (a:A) (b:B).
  Check pair a b.
  Check (a,b).
  Check (a,b) : A*B.

  (* If we look back at the preceding, we can see the
      (i) formation rule: prod A B, or equivalently A * B
      (ii) introduction rule: pair a b, or (a,b)
     So we can see any inductive datatype will have
     these two features at least *)

  (* For instance, the unit type is very very boring *)
  Inductive unit  : UU :=
          | tt    : unit.
  Print unit.
  Check tt : unit.

  (* projections for pairs are
      (iii) eliminators: ways to deconstruct a term
     Notice that we can use this special pattern matching
     construct to pull apart a term inside an inductive
     datatype.  In Coq, this pattern matching is actually
     more primitive than the induction principles (coming
     up). *)
  Definition fst {A B : UU} (p:A*B) :=
    match p with (a,b) => a end.
  Definition snd {A B : UU} (p:A*B) :=
    match p with (a,b) => b end.
  Print fst.
  Print snd.
  Check fst (a,b) : A.
  Check snd (a,b) : B.
  (* Here is a new command: 'Compute' which can be used
     to ask Coq's term reduction engine to process a
     term.  Because of the way we defined fst/snd,
     Compute will nicely reduce explicit pairs.  This
     kind of interaction is called a
      (iv) computation rule: which shows how to reduce
              eliminator( introduction( . ) )
     Because this computation rule is provided
     *definitionally*, it will be processed automatically
     by the computation engine.  However, this may not be
     true in general... *)
  Compute fst (a,b).
  Compute snd (a,b).

  (* Now let's do a 'proof' using the tactics subsystem.
     Rather than say 'Definition' we write the command
     'Lemma' which is just a different way of defining
     a term.  Note how everything looks like a definition,
     except we just put a period after the type without
     any := assignment.
     Then, we delimit the proof with the commands
      'Proof' and 'Qed'.  In between are a sequence of
     'tactics' that are applied to successively break
     down the goal.  While this is hardly a full Coq
     tutorial, I'll try to explain.

     Hopefully you're in an IDE or tool that shows you
     the intermediate proof state as you go.
     The first tactic pulls apart the quantifier and
     names the argument x.  Then, this x term, which is
     in the product type is 'destructed', which means
     consider all the cases of what x could be, and then
     simpl is applied, invoking the computation engine
     to reduce terms.  Finally, invoking reflexivity
     resolves a trivial equality.
  *)
  Lemma uniq_prod_try_1 {X Y} : forall (x : X*Y),
    (fst x, snd x) = x.
  Proof. intro x. destruct x. simpl. reflexivity. Qed.
  (* But what happens when we print this term we just
     defined?  Voila!  It's a term.  As we go, this will
     become more obvious--how each part of this term
     corresponds to / was constructed by one of these
     tactics we invoked. *)
  Print uniq_prod_try_1.
  Compute uniq_prod_try_1 (a,b).
  (* Hmm, this computation didn't appear to resolve
     the pattern match like the projection computations
     did.  What's wrong?  Let's try repeating the whole
     proof, but closing with 'Defined' instead of 'Qed' *)
  Lemma uniq_prod {X Y} : forall (x : X*Y),
    (fst x, snd x) = x.
  Proof. intro x. destruct x. simpl. reflexivity. Defined.
  Print uniq_prod.
  Compute uniq_prod (a,b).
  (* Now, the term is actually reduced down further.
     In Coq, when you write Qed this tells the Coq engine
     that you want to treat the proof (i.e. term) of the
     proposition (i.e. type) that you just proved as a
     black-box.  Usually this is the right thing to do,
     but it prevents exploiting any definitional equalities
     that have been created.
    Finally, note that this is a
      (v) uniqueness principle: specifying the behavior of
            introduction( elimination( . ) )
          which is kind of like the dual of a computation
          rule.
     Unlike the computation rules for 'prod A B', the
      uniqueness principle is given as a 'propositional
      equality' rather than a definitional one.  This means
      we'll have to invoke it explicitly rather than count
      on the computation engine to automatically resolve it.
  *)

  (* Note the following possible definitions.
      In Coq, we can build everything out of pattern
      matching. *)
  Definition prod_recurse : forall (C : UU),
    (A -> B -> C) -> A*B -> C
  := fun C g p => match p with | (a,b) => g a b end.

  Definition unit_recurse : forall (C : UU),
    C -> unit -> C := fun C c t => c.

  Definition prod_induction : forall (C : A*B -> UU),
    (forall (x:A) (y:B), C (x,y) ) ->
      forall (x:A*B), C(x)
  := fun C g x => match x with | (a,b) => g a b end.
  Print prod_rect.

  Definition unit_induction : forall (C : unit->UU),
    C tt -> forall (x:unit), C x
  := fun C c x => match x with tt => c end.

  (* But also, Coq gave us built-in versions of these
     induction schemes when we defined the Inductive
     Datatypes. *)
  Print prod_rect.
  Print unit_rect.

  Lemma uniq_unit : forall (x:unit), x = tt.
  Proof. destruct x. reflexivity. Defined.
  Print uniq_unit.
  Compute uniq_unit tt.
End Product_Types.

(* 1.6 Dependent Pair Types *)
Section Dependent_Pair_Types.
  Variable A : Type.
  Variable B : A -> Type.

  (* built-in sigma / dependent-pair type *)
  Print sigT.
  Check @sigT A B.
  Check sigT B.
  Variables (a:A) (b : B a).
  Check existT _ a b.

  (* intro a custom notation for dependent pairs *)
  Notation "( x ; y )" := (existT _ x y) : fibration_scope.
  Open Scope fibration_scope.
  Check (a ; b).
  Check (existT _ a b).
  Check (1 ; 2) : { x : nat & nat }.

  Definition sigma_recursion {C}
    (g : forall x, B x -> C)
  : { x:A & B x } -> C
  := fun p => match p with
      | (a;b) => g a b
     end.
  Print sigT_rect.

  (* intro a custom notation for dependent pairs *)
  Notation "x .1" := (projT1 x )
    (at level 3) : fibration_scope.
  Notation "x .2" := (projT2 x )
    (at level 3) : fibration_scope.
  Print projT1.
  Print projT2.
  Check (a;b) .1 : A.
  Check (a;b) .2 : B a.
  Compute (a;b) .1.
  Compute (a;b) .2.

  (* type theoretic axiom of choice *)
  Definition ac {X Y} {R : X -> Y -> Type}
    (g : forall (x:X), { y:Y & R x y })
  : { f:X->Y & forall (x:X), R x (f x) }
  := let F := (fun (f : X -> Y) =>
                    forall x : X, R x (f x))
     in existT F (fun x => projT1 (g x))
                 (fun x => projT2 (g x)).

  Definition Magma := { X : Type & X -> X -> X }.

  Definition PointedMagma := { X : Type & X -> X -> X & X }.
  Definition PointedMagma2 :=
    { X : Type & ((X->X->X)*X)%type }.
  (* In some sense that I don't understand,
     these ought to be equal *)
End Dependent_Pair_Types.


(* 1.7 Coproduct Types *)
Section Coproduct_Types.
  Variables A B : Type.
  Check (A + B)%type.
  Check eq_refl : (A+B)%type = sum A B.

  Check inl.
  Check inr.
  Variables (a:A) (b:B).
  Check inl a.
  Check inr b.

  Definition sum_recursion : forall (C:Type),
    (A -> C) ->
    (B -> C) ->
    sum A B ->
    C
  := fun C f g p => match p with
      | inl a => f a
      | inr b => g b
     end.

  Print Empty_set.
  Definition Empty_set_recursion
  : forall (C : Type), Empty_set -> C
  := fun C ff => match ff with end.
  (* latin name: ex falso quodlibet
                 from false follows anything *)

  Definition sum_induction : forall (C: sum A B -> Type),
    (forall (a:A), C (inl a)) ->
    (forall (b:B), C (inr b)) ->
    forall (x : sum A B), C x
  := fun C f g x =>
      match x with
        | inl a => f a
        | inr b => g b
      end.
  Print sum_rect.

  Definition Empty_set_induction
  : forall (C : Empty_set -> Type) (z:Empty_set), C z
  := fun C z => match z with end.
  Print Empty_set_rect.
End Coproduct_Types.

(* 1.8 the type of Booleans *)
Section the_type_of_Booleans.
  Check bool.
  Print bool.
  Check false : bool.
  Check true : bool.

  Definition bool_recursion : forall (C:Type),
    C -> C -> bool -> C
  := fun C c0 c1 b => match b with
        | false => c0
        | true => c1
      end.

  Definition bool_induction : forall (C:bool->Type),
    (C false) -> (C true) ->
    forall (x:bool), (C x)
  := fun C c0 c1 b => match b with
        | false => c0
        | true => c1
      end.
  Print bool_rect.

  Theorem bool_true_or_false : forall (x:bool),
    sum (x=false) (x=true).
  Proof.
    intros. destruct x.
      right; trivial.
      left; trivial.
  Qed.
  Print bool_true_or_false.

  Definition bool_true_or_false_2 : forall (x:bool),
    sum (x=false) (x=true)
  := bool_induction (fun x => sum (x=false) (x=true))
                    (inl eq_refl)
                    (inr eq_refl).
End the_type_of_Booleans.


(* 1.9 the Natural Numbers *)
Section the_Natural_Numbers.
  Check nat.
  Print nat.

  Fixpoint double (n : nat) : nat :=
    match n with
      | O   => O
      | S n => S (S (double n))
    end.

  Compute double 2.
  Compute double 4.
  Check eq_refl : double 3 = 6.

  Fixpoint add (n : nat) (m : nat) : nat :=
    match n with
      | O     => m
      | S n'  => S (add n' m)
    end.
  Locate "_ + _".

  Check eq_refl : add 2 3 = 5.

  Definition recursion_nat : forall (C:Type),
    C -> (nat -> C -> C) -> nat -> C
  := fix R C c0 cS n := match n with
        | O     => c0
        | S n'  => cS n' (R C c0 cS n')
     end.

  Definition double2 :=
    recursion_nat nat 0 (fun n y => S (S y)).
  Definition add2 :=
    recursion_nat (nat->nat)
                  (fun n => n)
                  (fun n g m => S (g m)).
  Check add2.

  Definition induction_nat : forall (C:nat -> Type),
    (C 0) ->
    (forall (n:nat), C n -> C (S n)) ->
    forall (n:nat), C n
  := fix R C c0 cS n := match n with
        | O     => c0
        | S n'  => cS n' (R C c0 cS n')
     end.
  Print nat_rect.

  Definition assoc_add_0 : forall (j k : nat),
    (add 0 (add j k)) = (add (add 0 j) k)
  := fun j k => eq_refl (add j k).
  Definition assoc_add_S : forall (i:nat),
    (forall (j k : nat),
      (add i (add j k)) = (add (add i j) k)) ->
    forall (j k : nat),
      (add (S i) (add j k)) = (add (add (S i) j) k)
  := let ap_succ : forall (m n : nat),
            m = n -> S m = S n
         := fun m n =>
              eq_rect m (fun x => S m = S x)
                      eq_refl n
     in fun i h j k => ap_succ _ _ (h j k).
  Definition assoc_add_nat : forall (i j k : nat),
    (add i (add j k)) = (add (add i j) k)
  := fun i j k =>
        induction_nat _ assoc_add_0 assoc_add_S i j k.

End the_Natural_Numbers.


(* 1.10 Pattern Matching and Recursion *)
Section Pattern_Matching_and_Recursion.
  (* nada? *)

End Pattern_Matching_and_Recursion.


(* 1.11 Propositions as Types *)
Section Propositions_as_Types.
  Variables A B : Prop.
  Variables f : A -> B.

  Check eq_refl : (A -> False) = ~A.
  Lemma syntax_not_check : (A -> False) = ~A.
  Proof. unfold not. trivial. Qed.
  Print not.

  Theorem DeMorgan1_natural : and (~A) (~B) -> ~(or A B).
  Proof.
    intro H; destruct H as [x y].
    intro z; destruct z as [a | b].
    apply (x a).
    apply (y b).
  Qed.
  Theorem DeMorgan1_term : and (~A) (~B) -> ~(or A B).
  Proof.
    apply (@and_ind (~A) (~B) (~(A \/ B))
            (fun x y => @or_ind A B False x y)).
  Qed.

  Theorem DeMorgan2_natural : ~(or A B) -> and (~A) (~B).
  Proof.
    intro nAorB. split; intro x; apply nAorB.
      left. apply x.
      right. apply x.
  Qed.
  
  Lemma split_dep_func {P Q} :
    (forall (x:A), P x /\ Q x) ->
    (forall (x:A), P x) /\ (forall (x:A), Q x).
  Proof.
    intro H.
    split; intro x; apply (H x).
  Qed.

  Definition LEq n m := { k : nat & n+k = m }.
  Print LEq.
  Locate "_ <= _".
  Search le.

  Lemma plus_assoc {n m p : nat}
  : n + m + p = n + (m + p).
  Proof.
    induction n as [ | n Scase]. reflexivity.
    simpl. rewrite Scase. reflexivity.
  Qed.

  Lemma LEq_trans {n m p : nat}
  : (LEq n m) -> (LEq m p) -> (LEq n p).
  Proof.
    unfold LEq.
    intros LEnm LEmp.
    destruct LEnm as [dnm enm].
    destruct LEmp as [dmp emp].
    exists (dnm + dmp).
    rewrite <- emp.
    rewrite <- enm.
    rewrite plus_assoc.
    reflexivity.
  Qed.

  Lemma LEq_O_n (n:nat) : LEq 0 n.
  Proof.
    exists n. reflexivity.
  Qed.
  Lemma LEq_n (n:nat) : LEq n n.
  Proof. exists 0. symmetry. apply plus_n_O. Qed.
  Lemma LEq_S (n m:nat) : LEq n m -> LEq n (S m).
  Proof.
    intro Lnm; destruct Lnm as [p Enm].
    rewrite <- Enm. 
    exists (S p). symmetry.
    apply (plus_n_Sm n p).
  Qed.
  Lemma LEq_n_S {n m:nat} : LEq n m -> LEq (S n) (S m).
  Proof.
    intro Lnm; destruct Lnm as [p Enm].
    exists p.
    rewrite <- Enm. reflexivity.
  Qed.
  Lemma LEq_S_n {n m:nat} : LEq (S n) (S m) -> LEq n m.
  Proof.
    intro LS; destruct LS as [p ES].
    exists p. apply eq_add_S.
    apply ES.
  Qed.

  Definition SemiGroup := { A : Type & 
                           { m : (A->A->A) &
                             forall (x y z : A),
                               m x (m y z) = m (m x y) z}}.

  Inductive NAT : Prop :=
    | nO : NAT
    | nS : NAT -> NAT
    .

  Lemma logically_but_not_eqv : NAT <-> True.
  Proof.
    split; intro H.
      trivial.
      apply nO.
  Qed.
  (* So natural numbers are 'equivalent' to True
     logically, but that doesn't mean that True and
     NAT are really equivalent... *)

End Propositions_as_Types.


(* 1.12 Identity Types *)
Section Identity_Types.
  Variables A : Type.
  Variables a b : A.

  Print eq.
  Check eq a b.
  Check @eq A a b.

  Check eq_refl a.
  Print eq_refl.

  Lemma indiscernability_of_identiticals :
    forall (C:A->Type),
    forall (x y : A) (p : x = y), (C x) -> (C y).
    intros C x y E Cx. induction E. apply Cx.
  Defined.

  (* but how does induction work??? *)

  Definition path_induction
    {C : forall x y : A, x=y -> Type}
    (c : forall x : A, C x x eq_refl)
  : forall x y : A, forall p : x=y, C x y p
  := fun x y p => match p with
      | eq_refl _ => c x
      end.

  Definition based_path_induction
    {a : A}
    {C : forall x : A, a=x -> Type}
    (c : C a eq_refl)
  : forall (x : A) (p : a=x), C x p
  := fun x p => match p with
      | eq_refl _ => c
      end.

  Definition normal_from_based_path_induction
    {C : forall x y : A, x=y -> Type}
    (c : forall x : A, C x x eq_refl)
  : forall x y : A, forall p : x=y, C x y p
  := fun x y p =>
      @based_path_induction x (C x) (c x) y p.

  Definition based_from_normal_path_induction
    {a : A}
    {C : forall x : A, a=x -> Type}
    (c : C a eq_refl)
  : forall (x : A) (p : a=x), C x p
  := fun x p =>
      let D : forall (x y : A), x=y -> Type
             := fun x y p =>
                  forall (C : forall z:A, x=z -> Type),
                    (C x eq_refl) -> (C y p)
      in let
          d : forall x:A, D x x eq_refl
            := fun x C (c : C x eq_refl) => c
      in (@path_induction D d a x p) C c.

  Check a <> b.
  Locate "_ <> _".

End Identity_Types.


(* Chapter 1 Exercises *)
Section Chapter_1_Exercises.
  (* 1.1. Define Function Composition
          and show associativity *)
  Definition fc {A B C} (g : B -> C) (f : A -> B)
                : A -> C
                := fun a => g (f a).
  Lemma fc_assoc {A B C D : Type}
                 {f : A -> B}
                 {g : B -> C}
                 {h : C -> D}
        : fc h (fc g f) = fc (fc h g) f.
  Proof. trivial. Qed.


  (* 1.2 Derive pair_recursion from fst/snd projections
         and    sigma_recursion from projT1/projT2 *)
  Definition pair_recursion {A B}
    (C : Type)
    (g : A -> B -> C)
    (p : prod A B)
  : C
  := g (fst p) (snd p).
  Definition sigma_recursion {A B}
    (C : Type)
    (g : forall x : A, B x -> C)
    (p : { x : A & B x })
  : C
  := g (projT1 p) (projT2 p).


  (* 1.3 Derive pair_induction from fst/snd projedtions
         and    sigma_induction from projT1/projT2 *)
  Lemma uniq_pair {A B}
    (x : prod A B)
  : pair (fst x) (snd x) = x.
  Proof. destruct x. trivial. Qed.
  Definition pair_induction {A B}
    (C : (prod A B) -> Type)
    (g : forall (x:A) (y:B), (C (pair x y)))
    (x : prod A B)
  : C x
  := indiscernability_of_identiticals
      (prod A B) C
      _ _
      (uniq_pair x)
      (g (fst x) (snd x)).
  Lemma uniq_sigma {A B}
    (x : {a:A & B a})
  : existT B (projT1 x) (projT2 x) = x.
  Proof. destruct x. trivial. Qed.
  Definition sigma_induction {A B}
    (C : {x : A & B x} -> Type)
    (g : forall (a : A) (b : B a), C (existT B a b))
    (p : { x : A & B x })
  : C p
  := indiscernability_of_identiticals
      {a:A & B a} C
      _ _
      (uniq_sigma p)
      (g (projT1 p) (projT2 p)).


  (* 1.4 Derive nat recursion from iteration *)
  Fixpoint iter (C:Type) (c0:C) (cs:C->C) (n:nat) : C
    := match n with
        | O   => c0
        | S n => cs (iter C c0 cs n)
        end.
  Definition nat_recursion (C:Type) :
    C -> (nat -> C -> C) -> nat -> C
  := fun c0 cs n =>
      snd (iter (nat*C)%type
                (0,c0)
                (fun p => (S (fst p), cs (fst p) (snd p)))
                n).
  Lemma Def_Eq_nat_recursion {C:Type} {c0 cs} (n:nat)
        : nat_recursion C c0 cs O = c0 /\
          nat_recursion C c0 cs (S n) =
                          cs n (nat_recursion C c0 cs n).
  Proof. 
    pose (unwrap_rec :=
                 iter (nat * C) (0, c0)
                      (fun p : nat * C =>
                          (S (fst p),
                           cs (fst p) (snd p)))).
    assert (forall m:nat, fst (unwrap_rec m) = m) as Count.
        induction m; trivial;
        unfold unwrap_rec; simpl; fold unwrap_rec;
        rewrite IHm; trivial.
    split; trivial;
    unfold nat_recursion; simpl; fold unwrap_rec;
    rewrite Count.
    trivial.
  Qed. Print Def_Eq_nat_recursion.

  (* 1.5 Bool Sum *)
  Definition BSum (A B : Type) :=
    { x:bool & bool_rect (fun x : bool => Type) A B x }.
  Definition Binl {A B} (a:A) : BSum A B :=
    existT _ true a.
  Definition Binr {A B} (b:B) : BSum A B :=
    existT _ false b.
  Definition BSum_induction {A B}
    (C : BSum A B -> Type)
    (f : forall a:A, C (Binl a))
    (g : forall b:B, C (Binr b))
    (x : BSum A B)
  : C x
  := sigT_rect C
        (fun tag => match tag with
          | true => f
          | false => g end) x.
  Lemma DefEq_BSum_induction {A B} {C f g} :
    (forall a:A, BSum_induction C f g (Binl a) = f a) /\
    (forall b:B, BSum_induction C f g (Binr b) = g b).
  Proof. split; trivial. Qed.

  (* 1.6 Bool Prod *)
  Definition BProd (A B : Type) :=
    forall x:bool, bool_rect (fun x:bool => Type) A B x.
  Definition Bpair {A B} (a : A) (b : B) : BProd A B :=
    fun x:bool => match x with
      | true  => a
      | false => b
    end.
  Axiom funext :
    forall (A : Type) (B : A -> Type)
           (f g : forall x:A, B x),
    (forall x : A, (f x) = (g x)) -> f = g.
  Definition Bfst {A B} (x : BProd A B) : A :=
    x true.
  Definition Bsnd {A B} (x : BProd A B) : B :=
    x false.
  Definition uniq_BProd {A B} {x : BProd A B}
  : Bpair (Bfst x) (Bsnd x) = x
  := funext _ _
            (Bpair (Bfst x) (Bsnd x))
            x
            (fun tag : bool => match tag with
               | true   => eq_refl (x true)
               | false  => eq_refl (x false) end).
  Definition BProd_induction {A B}
    (C : BProd A B -> Type)
    (f : forall (a:A) (b:B), C (Bpair a b))
    (x : BProd A B)
  : C x
  := indiscernability_of_identiticals _
            C _ _ uniq_BProd
            (f (Bfst x) (Bsnd x)).
  (*Lemma DefEq_BProd_induction {A B} {C g} :
    forall (a:A) (b:B),
      BProd_induction C g (Bpair a b) = g a b.*)

  (* 1.7 Alternative Path Induction *)
    (* skipping *)

  (* 1.8 Multiplication and Exponentiation of nat;
         (nat, +, 0, *, 1) is a semi-ring *)
    (* define using nat_recursion *)
  Definition plus  (x y : nat) : nat :=
    nat_rect (fun _ => nat)
             x
             (fun _ => S)
             y.
  Definition times (x y : nat) : nat :=
    nat_rect (fun _ => nat)
             0
             (fun _ => plus x)
             y.
  Definition exp   (x y : nat) : nat :=
    nat_rect (fun _ => nat)
             1
             (fun _ => times x)
             y.
  Definition is_a_semiring
    (A : Type)
    (plus     : A -> A -> A)
    (zero     : A)
    (times    : A -> A -> A)
    (one      : A)
  :=
    (forall a b c : A,
        plus (plus a b) c = plus a (plus b c))
  /\(forall a : A, plus zero a = a /\
                   plus a zero = a)
  /\(forall a b : A, plus a b = plus b a)
    (* (A, times, one) is a monoid *)
  /\(forall a b c : A,
        times (times a b) c = times a (times b c))
  /\(forall a : A, times one a = a /\
                   times a one = a)
    (* plus/times distribute *)
  /\(forall a b c : A,
        times a (plus b c) = plus (times a b) (times a c))
  /\(forall a b c : A,
        times (plus b c) a = plus (times b a) (times c a))
    (* zero times annihilation *)
  /\(forall a : A, times zero a = zero /\
                   times a zero = zero)
    .
  Theorem nat_is_a_semiring :
    is_a_semiring nat plus 0 times 1.
  Proof. unfold is_a_semiring.
    assert (forall a b c : nat,
        plus (plus a b) c = plus a (plus b c)) as PlusAssoc.
      induction c; simpl; trivial;
                   rewrite IHc; trivial.
    assert (forall a, plus 0 a = a) as ZeroPlus.
      induction a; simpl; trivial; rewrite IHa; trivial.
    assert (forall a b : nat,
        plus a b = plus b a) as PlusSymm.
      intros;
      induction a; simpl; trivial;
                          rewrite <- IHa; clear IHa;
      induction b; simpl; trivial; rewrite IHb; trivial.
    assert (forall a b c : nat,
                times a (plus b c) =
                plus (times a b) (times a c)) as LeftDist.
      induction c; simpl; trivial; rewrite IHc; clear IHc;
      rewrite <- PlusAssoc; rewrite <- PlusAssoc;
      rewrite (PlusSymm a); trivial.
    repeat split; intros.
    (*1*) trivial.
    (*2*) trivial.
    (*3*) trivial.
    (*4*)
      induction c; simpl; trivial;
                   rewrite IHc; trivial;
      rewrite LeftDist; trivial.
    (*5*)
      induction a; simpl; trivial;
                   rewrite IHa; clear IHa;
                   induction a; simpl; trivial;
                   rewrite IHa; trivial.
    (*6*) trivial.
    (*7*)
      induction a; simpl; trivial; rewrite IHa; simpl;
      repeat (rewrite <- PlusAssoc);
      repeat (rewrite (PlusAssoc b));
      rewrite (PlusSymm c); trivial.
    (*8*)
      induction a; simpl; trivial;
                   rewrite IHa; trivial.
  Qed.

  (* 1.9 Define the type family Fin *)
    (* unsure how to do this *)





  (* 1.11 Triple not is constructively just not *)
  Definition intro_double_not {A:Prop} : A -> ~~A :=
    fun a na => na a.
  Definition triple_not {A:Prop} : ~~~A -> ~A :=
    fun nnna a => nnna (intro_double_not a).

  (* 1.12 More Simple Logic Problems as Types *)
  Definition if_a_then_if_b_then_a {A B}
    : A -> (B -> A)
    := fun a => fun b => a.
  Definition if_not_a_or_not_b_then_not_a_and_b {A B}
    : (~A \/ ~B) -> ~(A /\ B)
    := fun or_nanb and_ab =>
          or_ind (fun na => na (proj1 and_ab))
                 (fun nb => nb (proj2 and_ab))
                 or_nanb.

  (* 1.13 Not Not Excluded Middle *)
  Definition not_not_excluded_middle {P} :
      ~~(P \/ ~P)
  := fun n_OR => (fun np => n_OR (or_intror np))
                 (fun p  => n_OR (or_introl p)).

  (* 1.14 *)
    (* skipping for now; no formal work? *)

  (* 1.15 indiscernability from path induction *)
    (* see inline earlier *)

  (* 1.16 commutativity of addition of natural numbers *)
  Lemma nat_commutativity :
    forall i j : nat, i+j = j+i.
  Proof.
    induction i; induction j; simpl; trivial;
      try (rewrite <- IHj); trivial;
      rewrite IHi; simpl; trivial;
      rewrite <- IHi; trivial.
  Qed.


End Chapter_1_Exercises.


