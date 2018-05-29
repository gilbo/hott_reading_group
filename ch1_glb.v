
(* Chapter 1 *)

(* 1.2 Function Types *)
Section Function_Types.
  Variables A B : Type.
  Variable f : A -> B.
  Variable y : B.

  Check (fun (x:A) => y) : A -> B.

  (* a more complete file would explore different
     valid ways of defining functions in Coq syntax here *)
End Function_Types.

(* 1.3 Universes and families *)
Section Universes_and_Families.
  Variables A B : Type.

  Check (fun (x : A) => B) : A -> Type.
End Universes_and_Families.

(* 1.4 Dependent Function Types *)
Section Dependent_Function_Types.
  Variable A : Type.
  Variable B : A -> Type.

  Check forall (x:A), B x.

  Definition swap_expl : forall (A:Type) (B:Type) (C:Type),
      (A -> B -> C) -> (B -> A -> C)
  :=
    fun A B C g =>
      fun b a => (g a b).

  (* these curly braces declare that A B C are implicit
     arguments.  So, Coq will try to infer their values
     rather than require them to be explicitly provided *)
  Definition swap {A B C : Type}
  : (A -> B -> C) -> (B -> A -> C)
  := fun g => fun b a => (g a b).
End Dependent_Function_Types.

(* 1.5 Product Types *)
Section Product_Types.
  Variable A B : Type.

  Check prod A B.

  Check (A*B)%type.

  Variables (a:A) (b:B).

  Check (a,b) : A*B.

  Variable ab : A*B.

  Check (fst ab) : A.

  Check (snd ab) : B.

  Lemma compute_prod_check : fst (a,b) = a.
  Proof. reflexivity. Qed.
  Search prod.

  Lemma uniq_prod {X Y} : forall (x : X*Y),
    (fst x, snd x) = x.
  Proof. destruct x. reflexivity. Qed.
  Print uniq_prod.

  Definition prod_rec : forall (C : Type),
    (A -> B -> C) -> A*B -> C
  :=
    fun C g p => match p with | (a,b) => g a b end.

  Print True.
  Check I : True.
  Definition True_rec : forall (C : Type),
    C -> True -> C := fun C c t => c.

  Definition prod_ind : forall (C : A*B -> Type),
    (forall (x:A) (y:B), C (x,y) ) ->
      forall (x:A*B), C(x)
  := fun C g x => match x with | (a,b) => g a b end.

  Definition True_ind : forall (C : True->Type),
    C I -> forall (x:True), C x
  := fun C c x => match x with I => c end.

  Lemma uniq_True : forall (x:True), x = I.
  Proof. destruct x. reflexivity. Qed.
End Product_Types.

(* 1.6 Dependent Pair Types *)
Section Dependent_Pair_Types.
  Variable A : Type.
  Variable B : A -> Type.

  Check { x:A & B x }.

  Variable x' : A.
  Variable y' : B x'.
  Check existT _ x' y' : { x:A & B x }.

  Definition sigma_recursion {C} (g : forall x, B x -> C)
  : { x:A & B x } -> C
  := fun p => match p with
      | existT _ a b => g a b
     end.
  Check projT1.
  Check projT2.
  Check eq_refl : projT1 (existT _ x' y') = x'.
  Check eq_refl : projT2 (existT _ x' y') = y'.

  Check @sigT_rect A B :
    forall (C : {x:A & B x} -> Type),
    (forall (a:A) (b:B a), C (existT _ a b))
   -> forall (p : {x:A & B x}), C p.

  (* type theoretic axiom of choice *)
  Reset A.

  Definition ac {A B} {R : A -> B -> Type}
    (g : forall (x:A), { y:B & R x y })
  : { f:A->B & forall (x:A), R x (f x) }
  := let F := (fun (f : A -> B) =>
                    forall x : A, R x (f x))
     in existT F (fun x => projT1 (g x))
                 (fun x => projT2 (g x)).

  Definition Magma := { A : Type & A -> A -> A }.

  Definition PointedMagma := { A : Type & A -> A -> A & A }.
  Definition PointedMagma2 :=
    { A : Type & ((A->A->A)*A)%type }.
  (* In some sense that I don't understand,
     these should be equal *)
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

  Print False.
  Definition False_recursion
  : forall (C : Type), False -> C
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

  Definition False_induction
  : forall (C : False -> Type) (z:False), C z
  := fun C z => match z with end.
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

  Eval compute in double 2.
  Eval compute in double 4.
  Check eq_refl : double 3 = 6.

  Fixpoint add (n : nat) (m : nat) : nat :=
    match n with
      | O     => m
      | S n'  => S (add n' m)
    end.

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

