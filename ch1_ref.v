
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

Require Export Coq.Init.Notations.

Definition UU := Type.
Identity Coercion fromUUtoType : UU >-> Sortclass.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Inductive paths {A:UU} (a:A) : (A->UU) :=
  paths_refl : paths a a.
Arguments paths_refl {A a}, [A] a.
Arguments paths_rect [A].
Hint Resolve paths_refl : core .
Notation "a = b" := (paths a b)
  (at level 70, no associativity) : type_scope.
Notation idpath := paths_refl.






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
  Arguments pair [A B].
  Notation "X * Y" := (prod X Y) : type_scope.
  Notation "( x , y , .. , z )" :=
    (pair .. (pair x y) .. z) : core_scope.
  (* Mostly, we can ignore this all as required magic for
     now.  The 'Arguments' command is a different
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

(* Unless we define notations outside the Sections
   they will not be available in the subsequent
   Sections *)

Arguments pair [A B].
Notation "X * Y" := (prod X Y) : type_scope.
Notation "( x , y , .. , z )" :=
  (pair .. (pair x y) .. z) : core_scope.

(* 1.6 Dependent Pair Types *)
Section Dependent_Pair_Types.

  (* We start with some more magic definitions and
     notations to create sigma types as desired *)
  Inductive sig { T: UU } ( P: T -> UU ) :=
    spair : forall x:T, P x -> sig P.
  Notation "'sigma' x .. y , p" :=
    (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, y binder, right associativity)
  : type_scope.
  Notation "'exists' x .. y , p" :=
    (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, y binder, right associativity)
  : type_scope.
  Check spair.
  Notation "{ x ; .. ; y ; z }"
    := (spair _ x .. (spair _ y z) ..) : fibration_scope.
  Open Scope fibration_scope.
  Delimit Scope fibration_scope with fiber.

  (* Here are different ways to write the type *)
  Variable A : Type.
  Variable B : A -> Type.
  Print sig.
  Check @sig A B.
  Check sig B.
  Check exists x, B x.
  Check sigma x, B x.

  (* and ways to introduce a member of the type *)
  Variables (a:A) (b : B a).
  Print spair.
  Check spair _ a b : exists x:A, B x.
  Check {a ; b}.

  (* Let's first look at projection functions *)
  Definition proj1 {A : UU} {B : A -> UU}
    (p : exists (x:A), B x) : A
  := match p with {a;b} => a end.
  Compute proj1 {a ; b}.
  Definition proj2 {A : UU} {B : A -> UU}
    (p : exists (x:A), B x) : B (proj1 p)
  := match p with {a;b} => b end.
  Compute proj2 {a ; b}.

  (* Now, here's the simple recursion principle, but
      also the automatically defined induction principle *)
  Definition sigma_recursion {C : UU}
    (g : forall x, B x -> C)
  : (exists x, B x) -> C
  := fun p => match p with
      | {a;b} => g a b
     end.
  Print sig_rect.

  (* intro a custom notation for deconstructing
     dependent pairs *)
  Notation "x .1" := (proj1 x)
    (at level 3) : fibration_scope.
  Notation "x .2" := (proj2 x)
    (at level 3) : fibration_scope.
  Check {a;b}.1 : A.
  Check {a;b}.2 : B a.
  Compute {a;b}.1.
  Compute {a;b}.2.

  (* type theoretic axiom of choice *)
  Definition ac {X Y : UU} {R : X -> Y -> UU}
    (g : forall x:X, exists y:Y, R x y)
  : exists (f:X->Y), forall x:X, R x (f x)
  := let F := (fun (f : X -> Y) =>
                    forall x : X, R x (f x))
     in spair F (fun x => (g x).1) (fun x => (g x).2).

  Definition Magma := exists X, X -> X -> X.

  Definition PointedMagma :=
    exists (X:Type) (m : X -> X -> X), X.
  Definition PointedMagma2 :=
    exists X, ((X -> X -> X) * X)%type.
  (* In some sense that I don't understand,
     these ought to be equal *)
End Dependent_Pair_Types.

Notation "'sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
  (at level 200, x binder, y binder, right associativity)
  : type_scope.
Notation "'exists' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
  (at level 200, x binder, y binder, right associativity)
  : type_scope.
Notation "{ x ; .. ; y ; z }"
  := (spair _ x .. (spair _ y z) ..) : fibration_scope.
Open Scope fibration_scope.
Delimit Scope fibration_scope with fiber.
Notation "x .1" := (proj1 x)
  (at level 3) : fibration_scope.
Notation "x .2" := (proj2 x)
  (at level 3) : fibration_scope.


(* 1.7 Coproduct Types *)
Section Coproduct_Types.
  (* Note that coprod is the first type we've seen that
     has two different introduction forms *)
  Inductive coprod (A B : UU) : UU :=
            | inl : A -> coprod A B
            | inr : B -> coprod A B
            .
  (* set some implicit arguments *)
  Arguments coprod_rect {_ _} _ _ _ _.
  Arguments inl {A B} _, [A] B _.
  Arguments inr {A B} _, A [B] _.
  Notation "X + Y" := (coprod X Y) : type_scope.

  (* Forming coproduct types *)
  Variables A B : Type.
  Check (A + B)%type.
  Check coprod A B.

  Variables (a:A) (b:B).
  Check inl a.
  Check inl a : A + B.
  Check inr b.
  Check inr b : A + B.

  Definition coprod_recursion : forall (C:UU),
    (A -> C) ->
    (B -> C) ->
    A + B ->
    C
  := fun C f g p => match p with
      | inl a => f a
      | inr b => g b
     end.

  (* The empty type is uninhabited *)
  Inductive empty : UU := .
  (* and the recursion principle is that anything
     follows from 'false' *)
  Definition empty_recursion
    : forall (C:UU), empty -> C
  := fun C ff => match ff with end.
  (* latin name: ex falso quodlibet
                 from false follows anything *)

  Print coprod_rect.
  Print empty_rect.
End Coproduct_Types.

Arguments coprod_rect {_ _} _ _ _ _.
Arguments inl {A B} _, [A] B _.
Arguments inr {A B} _, A [B] _.
Notation "X + Y" := (coprod X Y) : type_scope.

(* 1.8 the type of Booleans *)
Section the_type_of_Booleans.

  (* Again, some stuff we don't need to understand to
      define the basic 'bool' type *)
  Inductive bool  : UU :=
            | false : bool
            | true : bool
            .
  (* and we'll define an inversion *)
  Definition negb (b:bool) := if b then false else true.
  Print negb.
  Print bool.
  Check false : bool.
  Check true : bool.

  (* Coq has already defined
      an induction principle for us *)
  Print bool_rect.

  (* We can prove an exclusion principle for bool *)
  Definition bool_true_or_false
  : forall (x:bool), (x=false) + (x=true)
  := bool_rect (fun x => ((x=false) + (x=true))%type)
               (inl idpath)
               (inr idpath).
  Print bool_true_or_false.
End the_type_of_Booleans.


(* 1.9 the Natural Numbers *)
Section the_Natural_Numbers.

  (* More magic stuff *)
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

  (* ok, pretty straightforward... *)
  Check nat.
  Print nat.

  (* here's a simple example of a function
     to double a natural number.  But note!
     We're using a new command, 'Fixpoint' here *)
  Fixpoint double (n : nat) : nat :=
    match n with
      | O   => O
      | S n => S (S (double n))
    end.
  (* We could have avoided this new command by using
     a special term instead, revealing that the
     Fixpoint command is just syntax sugar *)
  Definition double_2 :=
    (fix double_fix (n:nat) : nat :=
       match n with
       | O   => O
       | S n => S (S (double_fix n))
       end).
  (* note that the result is the same when we print
     modulo renamings *)
  Print double.
  Print double_2.

  Compute double 2.
  Compute double 4.
  Check idpath : double 3 = 6.

  (* Here is the basic addition function *)
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
      | O     => m
      | S n'  => S (plus n' m)
    end.
  Notation "x + y" := (plus x y) : nat_scope.

  Check idpath : plus 2 3 = 5.
  Check idpath : 2 + 3 = 5.

  (* If we define our own recursion principle,
     we can also define operations using that
     without having to use Coq's recursive functions *)
  Definition nat_recursion : forall (C:Type),
    C -> (nat -> C -> C) -> nat -> C
  := fix R C c0 cS n := match n with
        | O     => c0
        | S n'  => cS n' (R C c0 cS n')
     end.
  Definition double_rec :=
    nat_recursion nat 0 (fun n y => S (S y)).
  Definition plus_rec :=
    nat_recursion (nat->nat)
                  (fun n => n)
                  (fun n g m => S (g m)).

  (* Coq defines an induction principle for us *)
  Print nat_rect.

  (* Now, we can prove associativity explicitly. *)
  Definition assoc_plus_0 (j k : nat)
  : (0 + (j + k)) = ((0 + j) + k)
  := idpath (j + k).
  Definition assoc_plus_S : forall (i:nat),
    (forall (j k : nat), i + (j + k) = (i + j) + k) ->
    forall (j k : nat), (S i) + (j + k) = ((S i) + j) + k
  := let ap_succ (m n : nat) : m = n -> S m = S n
         := paths_rect m (fun x p => S m = S x) idpath n
     in fun i h j k => ap_succ _ _ (h j k).
  Definition assoc_plus_nat (i j k : nat)
  : i + (j + k) = (i + j) + k
  := nat_rect _ assoc_plus_0 assoc_plus_S i j k.

End the_Natural_Numbers.

Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.
Open Scope nat_scope.

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
Notation "x + y" := (plus x y) : nat_scope.

(* 1.10 Pattern Matching and Recursion *)
Section Pattern_Matching_and_Recursion.
  (* We've already seen how pattern matching is related
     to recursion/induction *)
  (* I'm going to use this section instead as an opportunity
     to explore the Ltac proof language/system in more excruciating
     detail.
     To do this, we need to have some boring theorems to prove.
     'nat' should do the trick! *)
  (* Here's a handy command you should try: 'Search'.
     Search will do a lookup of the name in question, trying to
     find all the Lemmas, theorems, etc. involving that object as
     it can.  So, here we'll search the *old* natural number type
     that we shadowed when we defined our own 'nat'. *)
  (* Search Datatypes.nat. *)
  (* The above command won't work once we turn on the command line
     argument that prevents the loading of the standard libraries *)
  (* It wouldn't hurt to try to prove some of these results anew *)
  (*
    plus_n_O  : forall n : nat, n = n + 0
    plus_0_n  : forall n : nat, 0 + n = n
    eq_add_S  : forall n m : nat, S n = S m -> n = m
    eq_S      : forall n m : nat, n = m -> S n = S m
    plus_Sn_m : forall n m : nat, S (n + m) = n + (S m)
   *)
  (* To start, let's do this simple one *)
  Lemma eq_S__0 : forall n m : nat, n = m -> S n = S m.
  Proof.
    intros n m Enm.
    induction Enm.
    reflexivity.
  Qed.
  Print eq_S__0.

  Lemma eq_S__1 : forall n m : nat, n = m -> S n = S m.
  Proof.
    intros n m Enm.
    destruct Enm.
    reflexivity.
  Qed.
  Print eq_S__1.

  (* So we can start to see some of the correspondence between
     the tactics (the name for the commands inside the proof)
     and the resulting proof term that is constructed.

     In order to explore this deeper, we're going to look at
     how to define our own proof commands, i.e. tactics *)
  Ltac my_intro x := intro x.
  Print my_intro.

  (* note that we can chain tactics together with ;  *)
  Lemma eq_S__20 : forall n m : nat, n = m -> S n = S m.
  Proof.
    my_intro n; my_intro m; my_intro E.
    Show Proof.
    destruct E.
    Show Proof.
    reflexivity.
  Qed.

  (* in fact, we can see that some of these tactics were defined
     elsewhere, even if we can't see their definition *)
  Print intro.
  Print reflexivity.
  Print elimtype.

  (* idtac is a useful way to debug tactics or give feedback *)
  (* also note that we can define anonymous functions in Ltac, although
     these functions are Ltac, not Coq functions *)
  Ltac my_intro2 := fun x => idtac "myintro_2 -" x; intro x.
  Lemma eq_S__21 : forall n m : nat, n = m -> S n = S m.
  Proof.
    my_intro2 n; my_intro2 m; my_intro2 E.
    destruct E. reflexivity.
  Qed.

  (* We can get much more complicated.  To do that, let's start
     looking at some ways to manage tactic scripts.  First here,
     we can see that let expressions help us capture anything we
     want to introspect on.  We show two useful bits of introspection
     here.  The first is a way to generate a 'fresh' i.e. unused
     name.  This is extremely valuable in order to ensure consistent
     ways to refer to evidence we introduce via one tactic, but then
     want to use in another.  We can give a standard prefix ('my' here)
     to help with debugging.  After introducing the variable, we use
     another introspection facility to get the type of the newly
     introduced term.  Then, we display all this information for
     development purposes. *)
  Ltac my_intro3 := let nm := fresh "my"
                    in intro nm;
                       let T := type of nm
                       in idtac "myintro_3 -" nm ":" T.
  Lemma eq_S__23 : forall n m : nat, n = m -> S n = S m.
  Proof.
    my_intro3. my_intro3. my_intro3.
    destruct my1. reflexivity.
  Qed.

  (* Now lets write a plausibly useful tactic *)
  Ltac in_destruct := let nm := fresh "in_dest_H"
                      in intro nm; destruct nm.
  Lemma eq_S__24 : forall n m : nat, n = m -> S n = S m.
  Proof.
    intros n m. in_destruct. reflexivity.
  Qed.

  (* We're really going overboard on this proof, since the original
     form was already pretty minimal, but let's see if we can
     create a tactic script that *FINDS* an instance of an equality
     proposition and then deliberately destructs it... *)
  Ltac destruct_paths :=
    match goal with
    | p : _ = _ |- _ => destruct p; destruct_paths
    | _ => try (simpl; reflexivity)
    end.
  (* Normally destruct requires that we specify which term/hypothesis
     we want to destruct.  However, Ltac allows us to match on the
     current proof state 'match goal with'.  When we do this match,
     notice that the pattern includes a turnstile '|-'.  This symbol
     is equivalent to the big horizontal line you see in the Coq
     Goal window of your interactive prover environment.  Therefore,
     any patterns before the turnstile are searched for in the
     collection of hypotheses, and the pattern afterwards is matched
     against the current goal directly. *)
  (* The special 'try' command takes another tactic and tries applying
     it.  If we don't use try, then an unsuccessful application will
     abort the entire Ltac script, including the previous 'destruct'
     invocations. *)
  Lemma eq_S__25 : forall n m : nat, n = m -> S n = S m.
  Proof.
    intros; destruct_paths.
  Qed.
  (* Notice that the proof now no longer needs to refer to any
     specific names.  This is a valuable goal for proof automation *)

  (* just going to prove this finally... *)
  Lemma eq_S : forall n m : nat, n = m -> S n = S m.
  Proof.
    intros n m E; destruct E; exact idpath.
  Qed. (* note that 'exact' simply plugs in the specified term *)

  (* note that while the definition of plus allows for reducing
     out a 0 on the left, it does not work if the zero is on the
     right *)
  Variable nn : nat.
  Compute 0 + nn.
  Compute nn + 0.

  (* So, we need to prove the latter equality propositionally *)
  Lemma plus_n_O__try0 : forall n : nat, n = n + 0.
  Proof.
    intro n.
    simpl. (* simpl, i.e. computation/reduction is not enough. *)
    (* we need to apply inductive reasoning here *)
    induction n.
    (* base case is all zeros *) reflexivity.
    (* inductive case will let us *rewrite* *)
      simpl. rewrite <- IHn. reflexivity.
    (* to really understand what 'rewrite' is doing, we'll have to
       wait until we've studied propositional equality more carefully *)
  Qed.

  (* This is all a bit messy, so let's see if we can at least
     concatenate the prior proof together into a single block *)
  Lemma plus_n_O : forall n : nat, n = n + 0.
  Proof.
    intro n; induction n;
      [ reflexivity |
        simpl; rewrite <- IHn; reflexivity ].
  Qed.
  (* Notice how we use the 'tac0; [ tac1 | tac2 ]' construct to
     specify *different* proof scripts for the two different subgoals
     generated by induction. *)

  (* finally, while this lemma seems incredibly odd, it's
     extremely valuable when building up basic proofs about nat,
     because it too expresses an obvious but computationally
     non-trivial fact *)
  Lemma plus_Sn_m : forall n m : nat, S (n + m) = n + (S m).
  Proof.
    (* Here, instead of branching in the script we use ONE common
       continuation to address all sub-goals.  This is a common
       case where 'try' can be valuable. *)
    intros n m; induction n; simpl; try reflexivity;
      apply eq_S; assumption.
  Qed.

  (* Now, what if we try to re-prove associativity, but we
     choose to do induction on the 'wrong' variable... *)
  Lemma assoc_plus_nat_again (i j k : nat) :
    i + (j + k) = (i + j) + k.
  Proof.
    induction k; simpl.
    repeat rewrite <- plus_n_O. reflexivity.
    repeat rewrite <- plus_Sn_m. apply eq_S; assumption.
  Qed.

  (* Ok, so now we're at the OH SHIT THAT IS A GOOD IDEA part of this.
     Since we know these extra rules we proved *ought* to be part of
     a computational reduction, but aren't, can we just come up with our
     own custom reduction? *)
  Ltac natred := simpl; repeat (rewrite <- plus_n_O);
                 repeat (rewrite <- plus_Sn_m; simpl);
                 repeat (apply eq_S).
  Lemma assoc_plus_nat_on_j_now (i j k : nat) :
    i + (j + k) = (i + j) + k.
  Proof.
    induction j; natred; trivial.
    (* trivial is some big bag of tricks, including reflexivity
       and assumption *)
  Qed.

(*
  For reference, here are some links
  General list of basic tactics:
    http://flint.cs.yale.edu/cs428/coq/doc/Reference-Manual010.html#Tactics
  List of constructions for combining tactics in Ltac scripts:
    http://flint.cs.yale.edu/cs428/coq/doc/Reference-Manual011.html
 *)

End Pattern_Matching_and_Recursion.

Ltac natred := simpl; repeat (rewrite <- plus_n_O);
               repeat (rewrite <- plus_Sn_m; simpl);
               repeat (apply eq_S).

(* 1.11 Propositions as Types *)
Section Propositions_as_Types.
  (* Define negation... *)
  Definition not (A:UU) : UU := A -> empty.
  Notation "~ A" := (not A) : type_scope.
  Arguments not _%type.
  
  Variables A B : UU.
  Variables f : A -> B.

  Check ~A.
  Compute ~A.
  Print not.

  Theorem DeMorgan1_with_tactics : (~A) * (~B) -> ~(A + B)%type.
  Proof.
    intro H; destruct H as [na nb].
    intro Nor; destruct Nor as [a | b].
    apply (na a). apply (nb b).
  Qed.
  Definition DeMorgan1_term : (~A) * (~B) -> ~(A + B)%type :=
    prod_rect (~A) (~B) (fun _ => ~(A + B)%type)
              (fun a b => coprod_rect (fun _ => empty) a b).

  Theorem DeMorgan2_natural : ~(A + B)%type -> (~A) * (~B).
  Proof.
    intro nAoB; split; intro x; apply nAoB.
      left; apply x.
      right; apply x.
  Qed.

  Lemma split_dep_func {P Q} :
    (forall x:A, (P x) * (Q x)) ->
    (forall x:A, P x) * (forall x:A, Q x).
  Proof.
    intro H; split; intro x; apply (H x).
  Qed.

  Definition split_dep_func_term {P Q} :
    (forall x:A, (P x) * (Q x)) ->
    (forall x:A, P x) * (forall x:A, Q x)
  :=
    fun H => pair (fun x => fst (H x))
                  (fun x => snd (H x)).

  Definition LEq n m := exists k:nat, n+k = m.
  Print LEq.
  Notation "n <= m" := (LEq n m) : type_scope.

  Print assoc_plus_nat.

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
    rewrite assoc_plus_nat.
    reflexivity.
  Qed.

  Lemma LEq_O_n (n:nat) : LEq 0 n.
  Proof.
    exists n. reflexivity.
  Qed.
  Lemma LEq_n (n:nat) : LEq n n.
  Proof. exists 0. natred. trivial. Qed.
  Lemma LEq_S (n m:nat) : LEq n m -> LEq n (S m).
  Proof.
    intro Lnm; destruct Lnm as [p Enm].
    exists (S p); natred.
    trivial.
  Qed.
  Lemma LEq_n_S {n m:nat} : LEq n m -> LEq (S n) (S m).
  Proof.
    intro Lnm; destruct Lnm as [p Enm].
    exists p; natred; trivial.
  Qed.

  Definition SemiGroup := exists (A:Type) (m:A->A->A),
                            forall (x y z : A), m x (m y z) = m (m x y) z.

  Lemma logically_but_not_eqv : (nat -> unit)*(unit -> nat).
  Proof.
    split; [
      intro n; exact tt
    | intro u; exact 0
    ].
  Qed.
  (* more directly... *)
  Definition logically_but_not_eqv_explicit : (nat -> unit)*(unit -> nat)
    := pair (fun n => tt) (fun u => 0).
  Print logically_but_not_eqv.
  (* So natural numbers are 'equivalent' to unit
     logically, but that doesn't mean that unit and
     nat are really equivalent... *)

End Propositions_as_Types.

Notation "~ A" := (not A) : type_scope.
Arguments not _%type.
Notation "n <= m" := (LEq n m) : type_scope.

(* 1.12 Identity Types *)
Section Identity_Types.
  Variables A : UU.
  Variables a b : A.

  (* Now finally we can come back to our strange overloading
     of the equality operator that we began this file with *)
  Print paths.
  Check paths a b.
  Check @paths A a b.

  Check idpath a.
  Print idpath.
  Print paths_refl.

  (* The indiscernability of identicals is a key principle
     by which equalities may be used to rewrite an expression *)
  Lemma indiscernability_of_identiticals :
    forall (C:A->UU),
    forall (x y : A) (p : x = y), (C x) -> (C y).
  Proof.
    intros C x y E Cx. induction E. apply Cx.
  Defined.

  (* but how does induction work??? *)

  Definition path_induction
    {C : forall x y : A, x=y -> UU}
    (c : forall x : A, C x x idpath)
  : forall x y : A, forall p : x=y, C x y p
  := fun x y p => match p with
      | idpath _ => c x
      end.

  Definition based_path_induction
    {a : A}
    {C : forall x : A, a=x -> UU}
    (c : C a idpath)
  : forall (x : A) (p : a=x), C x p
  := fun x p => match p with
      | idpath _ => c
     end.

  (* Which of these induction principles does the built-in look like? *)
  Print paths_rect.

  Definition normal_from_based_path_induction
    {C : forall x y : A, x=y -> Type}
    (c : forall x : A, C x x idpath)
  : forall x y : A, forall p : x=y, C x y p
  := fun x y p =>
      @based_path_induction x (C x) (c x) y p.

  Definition based_from_normal_path_induction
    {a : A}
    {C : forall x : A, a=x -> Type}
    (c : C a idpath)
  : forall (x : A) (p : a=x), C x p
  := fun x p =>
      let D : forall (x y : A), x=y -> Type
             := fun x y p =>
                  forall (C : forall z:A, x=z -> Type),
                    (C x idpath) -> (C y p)
      in
      let d : forall x:A, D x x idpath
             := fun x C (c : C x idpath) => c
      in (@path_induction D d a x p) C c.

  Notation "a <> b" := (not (a = b)) : type_scope.

End Identity_Types.

Notation "a <> b" := (not (a = b)) : type_scope.

