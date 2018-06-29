
(* If this require statement doesn't work, it's probably because
   you haven't compiled the file pre1.v  To do that, run
   > coqc pre1.v
 *)
(* Require Import Coq.Unicode.Utf8_core. *)
Require Import pre1.

Check 1 + 1 = 2 : UU.
(* aha, the other stuff IS imported! *)

(* recall path induction, and paths_rect.  We'll be using them a lot! *)
Print path_induction.
Print paths_rect.




(* Extra Notation Fun *)
(*   As I started writing up chapter 2, I took the time to install
     the emacs (I'm using this Spacemacs Evil thing) agda input
     mode, which lets me type in unicode symbols using latex-like
     shorthands, such as \prod for ∏ *)
Notation "'∏' x .. y , P" :=
  (forall x, .. (forall y, P) ..)
    (at level 200, x binder, y binder, right associativity) : type_scope.
(* input: \prod  NOT \Pi *)
Notation "'λ' x .. y , t" :=
  (fun x => .. (fun y => t) ..)
    (at level 200, x binder, y binder, right associativity) : core_scope.
(* input: \lambda or \Gl for "greek-l" *)
Notation "'Σ' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, y binder, right associativity) : type_scope.
(* input: \sigma or \GS for "greek-S" *)
Notation "'∀' x .. y , P" :=
  (forall x, .. (forall y, P) ..)
    (at level 200, x binder, y binder, right associativity) : type_scope.
(* input: \forall or \all *)
Notation "'∃' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, y binder, right associativity) : type_scope.
(* input: \exists or \ex *)

Notation "A × B" :=
  (prod A B)
    (at level 40, left associativity) : type_scope.
(* input: \times *)

Notation "'¬' X" := (not X)
                      (at level 75, right associativity) : type_scope.
(* input: \neg *)
Notation "a ≠ b" := (not (a = b))
                        (at level 70, no associativity) : type_scope.
(* input: \ne or \neq *)

Notation "𝟘" := empty : type_scope.
(* input: \b0 *)
Notation "∅" := empty : type_scope.
(* input: \emptyset *)

Notation "𝟙" := unit : type_scope.
(* input: \b1 *)

Notation "𝟚" := bool : type_scope.
(* input: \b2 *)

Notation "'ℕ'" := nat : type_scope.
(* input: \bN *)


(* Function composition and identity *)
(* use this generalized form from UniMath... *)
Definition idfun {T : UU} := λ t:T, t.
Definition funcomp {X Y : UU} {Z:Y->UU}
           (f : X -> Y) (g : forall y:Y, Z y)
  := λ x, g (f x).

Notation "g ∘ f" := (funcomp f g)
                      (at level 40, left associativity) : function_scope.

(* sometimes a useful tactic when dealing heavily with functions *)
Ltac eta_reduce := repeat change (λ x, ?h x) with h.



(* One of the non-obvious themes of this chapter, that I'll try
   to add in some comments about is the question of how we characterize
   equality.

   For instance, in 2.1 we'll see how equality has an algebraic
   (groupoid) structure, but that also this structure must extend
   to higher order paths in interesting ways.

   One of the most important sections of this chapter is 2.14, in
   which we'll look at a purely type-theoretic definition of
   Semi-groups, and look at the meaning of equality structurally.
   For instance, we saw at the end of the last chapter that a
   Semi-group might be defined as
    is_SemiGroup A := Σ (m:A->A->A),
                      ∏ (x y z : A), m (m x y) z = m x (m y z).
       SemiGroup   := Σ A:UU, is_SemiGroup A.
   Then, an element G : SemiGroup would be a dependent triple,
         { A ; m ; assoc }
   and 'm' is a function, and 'assoc' is a dependent function.
   So if we have two semigroups, what does it mean that they're equal?
   we need to understand how equality interacts with Σ-types, and
   simple function types, and with ∏-types, and then finally within
   assoc we need to know what an equality of equalities means!

   And if the two semi-groups are built on different 'carrier types'
       { A ; ... } = { B ; ... }
   then we're going to run into a lot of annoying details about dependent
   typing, because (mA : A->A->A) and (mB : B->B->B) don't inhabit the
   same type, and are thus incomparable.  As we'll see, 'transport' will
   become our solution to this problem of simply stating our claims
   in an acceptable (i.e. type-safe) way.

   If you get lost in why we're doing something, try flipping back to
   this note and see whether something in it helps refresh your motivation.
 *)


(* 2.1 Types are Higher Groupoids *)
Section Types_are_Higher_Groupoids.
  (* We'll start proving the algebraic structure of equality now *)
  Definition path_inverse_explicit {A : UU} {a b : A}
             (p : a = b)
  : b = a
    := paths_rect a (λ x _, x = a)
                  (idpath a) b p.
  Definition path_inverse {A : UU} {a b : A}
             (p : a = b)
    : b = a.
  Proof.
    induction p. reflexivity.
  Defined.
  Print path_inverse.
  (* note that we can approach either definition, but that we should
     use 'Defined' instead of 'Qed' if we want to take advantage of
     the definitional equality *)
  Compute path_inverse (idpath 0).

  (* a convenience name for path inversion... *)
  Definition inv {A : UU} {a b : A} (p : a=b) := @path_inverse A a b p.
  Compute inv (idpath 0).
  Check inv (idpath 0).

  (* we also want to number the lemmas for reference, so... *)
  Definition lem_2_1_1 {A} {a b} := @path_inverse A a b.
  Print lem_2_1_1.


  (* ok, we can be a bit more brief now.  Let's do transitivity *)
  Definition path_compose_try_1 {A : UU} {a b c : A}
             (p : a = b) (q : b = c)
    : a = c.
  Proof.
    induction p; induction q; reflexivity.
  Defined.
  Print path_compose_try_1.
  Compute path_compose_try_1 (idpath 0) (idpath 0).

  (* here, we'll take a look at the consequences of different defs *)
  Definition alt_path_compose {A : UU} {a b c : A}
             (p : a = b) (q : b = c)
    : a = c.
  Proof.
    induction q; apply p.
  Defined.
  Compute λ p:1+1=2, path_compose_try_1 p (idpath 2).
  Compute λ p:1+1=2, alt_path_compose p (idpath 2).

  (* While it seems very much not obvious right now
     the following is the "right" definition, not try 1,
     despite the choice in the HoTT book.

     But don't trust me!  Try redefining 'path_compose'
     for yourself to 'path_compose_try_1' and go all the way down
     to the Eckmann_Hilton theorem below; and try to make that proof
     work.  Why does it break?  Understanding this point will
     bring you a lot of enlightenment about how the computational
     properties of proofs become consequential.
   *)
  Definition path_compose {A : UU} {a b c : A}
             (p : a = b) (q : b = c)
    : a = c.
  Proof.
    induction p; apply q.
  Defined.

  (* let's define a notation for path composition too *)
  Notation "p '∙' q" :=
    (path_compose p q)
      (at level 60, left associativity) : type_scope.
  (* input: \. WARNING: do not use \cdot, which looks the same
                                          but isn't *)

  Check ( λ p:1+1=2, (idpath (1+1)) ∙ p ).

  Definition lem_2_1_2 {A} {a b c} := @path_compose A a b c.


  (* rather than bundling Lemma 2.1.4, we break it down into
     individual results that can be used more easily *)
  Lemma path_compose_lid {A : UU} {a b : A} (p : a = b)
    : p = idpath ∙ p.
  Proof.
    (* the proof of this lemma for different definitions of
       path_compose differs critically *)
    exact (idpath p).
    (* alt proof *)
    (* induction p; reflexivity. *)
  Defined.
  Lemma path_compose_rid {A : UU} {a b : A} (p : a = b)
    : p = p ∙ idpath.
  Proof. induction p; reflexivity. Defined.
  Lemma path_inverse_l {A : UU} {a b : A} (p : a = b)
    : (inv p) ∙ p = idpath.
  Proof. induction p; reflexivity. Defined.
  Lemma path_inverse_r {A : UU} {a b : A} (p : a = b)
    : p ∙ (inv p) = idpath.
  Proof. induction p; reflexivity. Defined.
  Lemma path_inverse_inverse {A : UU} {a b : A} (p : a = b)
    : inv (inv p) = p.
  Proof. induction p; reflexivity. Defined.
  Lemma path_compose_assoc {A : UU} {a b c d : A}
        (p : a = b) (q : b = c) (r : c = d)
    : p ∙ (q ∙ r) = (p ∙ q) ∙ r.
  Proof. induction p; induction q; induction r; reflexivity. Defined.

  (* notated Ω(A) in the HoTT book *)
  Definition loops (A : UU) (a : A) := (a = a).
  (* notated Ω²(A) in the HoTT book *)
  Definition loops2 (A : UU) (a : A) := loops (loops A a) idpath.

  (* We'll avoid defining notation for now.
     We'll want to get it right when we do heavy work with loops later *)

  Definition whisker_r {A : UU} {a b c : A}
             {p q : a = b}
             (α : p = q) (r : b = c)
    : p ∙ r = q ∙ r.
  Proof. induction r;
           pose (ru := @path_compose_rid A a b);
           apply (inv (ru _) ∙ α ∙ (ru _)).
  Defined.
  Definition whisker_l {A : UU} {a b c : A}
             {r s : b = c}
             (p : a = b) (β : r = s)
    : p ∙ r = p ∙ s.
  Proof. induction p;
           pose (lu := @path_compose_lid A a c);
           apply (inv (lu _) ∙ β ∙ (lu _)).
  Defined.

  Definition horizontal_1 {A : UU} {a b c : A}
             {p q : a = b} {r s : b = c}
             (α : p = q) (β : r = s)
    := (whisker_r α r) ∙ (whisker_l q β).
  Definition horizontal_2 {A : UU} {a b c : A}
             {p q : a = b} {r s : b = c}
             (α : p = q) (β : r = s)
    := (whisker_l p β) ∙ (whisker_r α s).
  Lemma EQ_horizontal {A : UU} {a b c : A}
        {p q : a = b} {r s : b = c}
        (α : p = q) (β : r = s)
    : (horizontal_1 α β) = (horizontal_2 α β).
  Proof.
    induction α, β; induction p, r; trivial.
  Qed.
  Theorem Eckmann_Hilton {A : UU} {a : A}
          (α β : loops2 A a)
    : α ∙ β = β ∙ α.
  Proof.
    (* Main Proof of Eckmann Hilton *)
    unfold loops2 in α,β; unfold loops in α,β.
    assert (α ∙ β = horizontal_1 α β) as EQ1.
    { (* this is a sub-goal mechanism for organizing proofs... *)
        unfold horizontal_1; simpl;
          unfold path_compose_lid; repeat rewrite <- path_compose_rid;
            trivial.
    }
    assert (horizontal_2 α β = β ∙ α) as EQ2.
    {
      unfold horizontal_2; simpl;
        unfold path_compose_lid; repeat rewrite <- path_compose_rid;
          trivial.
    }
    exact (EQ1 ∙ (EQ_horizontal α β) ∙ EQ2).
  Qed.

  (* One less obvious point that was made in chapter 1 and applies
     to loop spaces is that once paths are closed into loops, we
     can't just apply path induction anymore.
     We can demonstrate this to ourselves as follows... *)
  (* uncomment to try it out *)
  (*
  Lemma totally_going_to_fail {A : UU} {a : A} (p : a=a)
    : p = idpath a.
  Proof.
    induction p. trivial.
  Qed.
   *)

  (* pointed types *)
  Definition PointedType := Σ A:UU, A.
  Definition loopspace (A : PointedType)
    := { A.2 = A.2 ; idpath A.2 } : PointedType.
  Fixpoint loopspace_n (n:nat) (A : PointedType)
    := match n with
       | 0   => A
       | S n => loopspace_n n (loopspace A)
       end.
End Types_are_Higher_Groupoids.

Notation "p ∙ q" :=
  (path_compose p q)
    (at level 60, left associativity) : type_scope.


Section Functions_are_Functors.
  Lemma ap {A B : UU} {x y : A} (f : A -> B)
  : (x = y) -> (f x) = (f y).
  Proof.
    intro p; induction p; reflexivity.
  Defined.
  Compute ap S (idpath 0).

  Definition lem_2_2_1 {A B} {a b} := @ap A B a b.

  Lemma ap_path_compose {A B : UU} {x y z : A}
        {p : x = y} {q : y = z}
        {f : A -> B}
    : ap f (p ∙ q) = (ap f p) ∙ (ap f q).
  Proof. induction p; reflexivity. Defined.
  Lemma ap_path_inverse {A B : UU} {x y : A}
        {p : x = y}
        {f : A -> B}
    : ap f (inv p) = inv (ap f p).
  Proof. induction p; reflexivity. Defined.
  Lemma ap_func_compose {A B C : UU} {x y : A}
        {p : x = y}
        {f : A -> B} {g : B -> C}
    : ap g (ap f p) = ap (g ∘ f) p.
  Proof. induction p; reflexivity. Defined.
  Lemma ap_idfun {A : UU} {x y : A}
        {p : x = y}
    : ap idfun p = p.
  Proof. induction p; reflexivity. Defined.
End Functions_are_Functors.


Section Type_Families_are_Fibrations.
  (* This definition seems largely superfluous, but we'll see I guess *)
  Definition fibration (X : UU) := X -> UU.
  (* We want to overload some notation in order to allow us
     to form fibrations out of more primitive fibrations in the way
     that we can form types out of more primitive types. *)
  Notation "A -> B" := (λ x, A x -> B x) : fibration_scope.
  Delimit Scope fibration_scope with fiber.

  Definition total   {X:UU} (P : fibration X) := Σ x:X, P x.
  Definition section {X:UU} (P : fibration X) := ∏ x:X, P x.
  

  Lemma transport {A : UU} (P : A -> UU) {x y : A} (p : x=y)
    : P x -> P y.
  Proof. induction p; exact idfun. Defined.
  Definition lem_2_3_1 {A} (P:A->UU) {x y} := @transport A P x y.

  Notation "p # x" :=
    (transport _ p x)
      (right associativity, at level 65, only parsing).

  (* we will later define lift in a way that more explicitly
     reflects the Σ structure of the equality it poses *)
  Lemma lift_direct {A : UU} (P : A -> UU) {x y : A} (u : P x) (p : x=y)
    : { x ; u } = { y ; p#u }.
  Proof. induction p; reflexivity. Defined.
  Definition lem_2_3_2 {A} (P:A->UU) {x y} := @lift_direct A P x y.

  Lemma apd {A : UU} {P : A -> UU} {x y : A}
        (f : ∏ x:A, P x)
    : ∏ p:x=y, p#(f x) = (f y) :> (P y).
  Proof. induction p; reflexivity. Defined.
  Definition lem_2_3_4 {A} {P} {x y} := @apd A P x y.

  Lemma transport_const {A : UU} (B : UU) {x y : A} (p : x=y) (b : B)
    : transport (λ _, B) p b = b.
  Proof. induction p; reflexivity. Defined.
  Definition lem_2_3_5 {A} (B:UU) {x y : A} := @transport_const A B x y.

  Lemma lem_2_3_8 {A B : UU} {x y : A} {f : A->B} {p : x=y}
    : apd f p = (transport_const B p (f x)) ∙ ap f p.
  Proof. induction p; reflexivity. Defined.

  Lemma lem_2_3_9 {A : UU} {P : A -> UU} {x y z : A}
        {p : x=y} {q : y=z} {u : P x}
    :  q#(p#u) = (p ∙ q)#u.
  Proof. induction p; reflexivity. Defined.    
  Lemma lem_2_3_10 {A B : UU} {P : B -> UU} {x y : A}
        {f : A -> B}
        {p : x=y} {u : P (f x)}
    : transport (P ∘ f) p u = transport P (ap f p) u.
  Proof. induction p; reflexivity. Defined.
  Lemma lem_2_3_11 {A : UU} {P Q : A -> UU} {x y : A}
        {f : section (P -> Q)%fiber }
        {p : x=y} {u : P x}
    : transport Q p (f x u) = f y (transport P p u).
  Proof. induction p; reflexivity. Defined.
End Type_Families_are_Fibrations.

Notation "A -> B" := (λ x, A x -> B x) : fibration_scope.
Delimit Scope fibration_scope with fiber.
  
Notation "p # x" :=
  (transport _ p x)
    (right associativity, at level 65, only parsing).


Section Homotopies_and_Equivalences.
  Definition homotopy {A : UU} {P : A -> UU}
             (f g : section P)
    := forall x:A, f x = g x.
  Notation "f ~ g" := (homotopy f g) (at level 70, no associativity).

  Lemma homotopy_refl {A : UU} {P : A -> UU} {f : section P}
    : f ~ f.
  Proof. intros x; reflexivity. Defined.
  Lemma homotopy_symm {A : UU} {P : A -> UU} {f g : section P}
    : f ~ g -> g ~ f.
  Proof. intros H x; exact (inv (H x)). Defined.
  Lemma homotopy_trans {A : UU} {P : A -> UU} {f g h : section P}
    : f ~ g -> g ~ h -> f ~ h.
  Proof. intros FG GH x; exact ((FG x) ∙ (GH x)). Defined.
  (* The above lemmas establish that homotopies are equivalence
     relations *)

  Lemma lem_2_4_3 {A B : UU} {x y : A}
        (p : x=y) (f g : A -> B) (H : f ~ g)
    : (H x) ∙ (ap g p) = (ap f p) ∙ (H y).
  Proof. induction p; simpl; rewrite <- path_compose_rid;
           reflexivity. Defined.
  Definition natural_homotopy {A B} {x y} := @lem_2_4_3 A B x y.

  Corollary cor_2_4_4_try_1 {A : UU} {f : A -> A} {x : A} {H : f ~ idfun}
    : H (f x) = ap f (H x).
  Proof.
    assert ((H (f x)) ∙ ap idfun (H x) = (ap f (H x)) ∙ (H x)) as Eq.
    { apply (natural_homotopy (H x) _ _ H). }
    rewrite ap_idfun in Eq.
    pose (Eq2 := whisker_r Eq (inv (H x))).
    repeat rewrite <- path_compose_assoc in Eq2.
    repeat rewrite path_inverse_r in Eq2.
    unfold idfun in Eq2.
    repeat rewrite <- path_compose_rid in Eq2.
    assumption.
  Qed.

  (* clearly we need some proof automation so we don't go insane... *)
  (* Rather than write our own Ltac script, we're going to try
     building a hint database to use with 'auto' *)

  (* Here, we will create a new hint database to collect
     strategies for simplifying path expressions *)
  Create HintDb PathGroupoid.
  Hint Rewrite @path_inverse_l : PathGroupoid.
  Hint Rewrite @path_inverse_r : PathGroupoid.
  Hint Rewrite @path_inverse_inverse : PathGroupoid.
  Hint Rewrite <- @path_compose_rid : PathGroupoid.
  Hint Rewrite @path_compose_assoc : PathGroupoid.

  Corollary cor_2_4_4_try_2 {A : UU} {f : A -> A} {x : A} {H : f ~ idfun}
    : H (f x) = ap f (H x).
  Proof.
    assert ((H (f x)) ∙ ap idfun (H x) = (ap f (H x)) ∙ (H x)) as Eq.
    { apply (lem_2_4_3 (H x) _ _ H). }
    rewrite ap_idfun in Eq.
    pose (Eq2 := whisker_r Eq (inv (H x))).
    autorewrite with PathGroupoid in Eq2.
    (* hmmm, the autorewrite didn't do anything... *)
    repeat rewrite <- path_compose_assoc in Eq2.
    autorewrite with PathGroupoid in Eq2.
    (* gah, that undid what we did! *)
    repeat rewrite <- path_compose_assoc in Eq2.
    repeat rewrite path_inverse_r in Eq2.
    autorewrite with PathGroupoid in Eq2.
    (* finally! *)
    assumption.
  Qed.

  (* so, we have a problem.  The lemmas that we proved don't form
     a very good rewrite system, because the path_inverse_l/r lemmas
     can't apply until we reassociate the expression in an unnatural
     way.  So, what we'll do is prove two assist lemmas instead *)
  Lemma path_inverse_l_assoc {A : UU} {a b c : A} (p : a = b) (q : c = b)
    : q ∙ (inv p) ∙ p = q.
  Proof. rewrite <- path_compose_assoc;
         rewrite path_inverse_l;
         rewrite <- path_compose_rid;
         reflexivity.
  Qed.
  Lemma path_inverse_r_assoc {A : UU} {a b c : A} (p : a = b) (q : c = a)
    : q ∙ p ∙ inv p = q.
  Proof. rewrite <- path_compose_assoc;
         rewrite path_inverse_r;
         rewrite <- path_compose_rid;
         reflexivity.
  Qed.
  Hint Rewrite @path_inverse_l_assoc : PathGroupoid.
  Hint Rewrite @path_inverse_r_assoc : PathGroupoid.

  Corollary cor_2_4_4 {A : UU} {f : A -> A} {x : A} {H : f ~ idfun}
    : H (f x) = ap f (H x).
  Proof.
    assert ((H (f x)) ∙ ap idfun (H x) = (ap f (H x)) ∙ (H x)) as Eq.
    { apply (lem_2_4_3 (H x) _ _ H). }
    rewrite ap_idfun in Eq.
    pose (Eq2 := whisker_r Eq (inv (H x))).
    autorewrite with PathGroupoid in Eq2.
    (* Hah!  Now the automation works great. *)
    assumption.
  Qed.

  (* Obviously, we could get even more automation if we threw
     in ap_idfun.  The whiskering
     (which is really step 1 in a cancellation of matching terms)
     is harder to automate consistently.  In general we need to be
     careful that any rewriting database we build is
       (a) strongly normalizing, so autorewrite terminates
       (b) not so strong that it will mangle up our work more than
           a programmer may want it to.
     The latter property can be worked around by building multiple
     hint databases, and allowing a user to include or exclude
     databases (or choose stronger/weaker ones) as needed.
   *)

  Definition quasi_inverse {A B : UU} (f : A -> B) :=
    exists g : B -> A, (f ∘ g ~ (@idfun B)) × (g ∘ f ~ (@idfun A)).
  Definition qinv {A B} := @quasi_inverse A B.

  Example qinv_idfun (A : UU) : qinv (@idfun A)
    := { @idfun A ; ((λ y, idpath y), (λ x, idpath x)) }.

  (* This example is reserved for the exercises *)
  (*
  Example example_2_4_8_a {A : UU} {x y z : A} (p : x=y)
    : let p_lcomp : (y=z -> x=z) := λ q, p ∙ q in
      qinv p_lcomp.
   *)

  Example example_2_4_9 {A : UU} {P : A -> UU} {x y : A} (p : x = y)
    : qinv (transport P p : P x -> P y).
  Proof.
    exists (transport P (inv p)).
    unfold funcomp; split; intro; rewrite lem_2_3_9;
      autorewrite with PathGroupoid; reflexivity.
  Defined.

  Definition isequiv {A B : UU} (f : A -> B)
    := (Σ g:B->A, f ∘ g ~ (@idfun B)) × (Σ h:B->A, h ∘ f ~ (@idfun A)).

  Lemma equiv_property_1 (A B : UU) (f : A -> B)
    : qinv f -> isequiv f.
  Proof.
    intro qf; destruct qf as [g (α , β)];
      split; exists g; assumption.
  Defined.
  Lemma equiv_property_2 (A B : UU) (f : A -> B)
    : isequiv f -> qinv f.
  Proof.
    intro ef; destruct ef as [ (g , α) (h , β) ];
    pose (γ x := (inv (β (g x))) ∙ ap h (α x) : g x = h x);
    pose (β' x := (γ ∘ f) x ∙ β x);
    exact { g ; (α, β') }.
  Defined.
  (* the following property is true, but proof is postponed *)
  (*
  Lemma equiv_property_3 (A B : UU) (f : A -> B)
    : forall e1 e2 : isequiv f, e1 = e2.
   *)
  Definition equiv_from_qinv {A B : UU} {f : A -> B}
    := equiv_property_1 A B f.
  Definition qinv_from_equiv {A B : UU} {f : A -> B}
    := equiv_property_2 A B f.

  Definition equiv (A B : UU) := (Σ f:A->B, isequiv f).
  Notation "A ≃ B" :=
    (equiv A B)
      (at level 80, no associativity) : type_scope.
  (* input: \~- or \simeq *)


  Remark transport_isequiv {X : UU} (P : X -> UU) {x y : X} (p : x=y)
    : isequiv (transport P p).
  Proof. apply equiv_from_qinv; apply example_2_4_9. Defined.


  Lemma equiv_refl {A : UU} : A ≃ A.
  Proof.
    exists (@idfun A);
      apply equiv_from_qinv;
      exists (@idfun A); split; intro x; trivial.
  Defined.
  Lemma equiv_symm {A B : UU} : (A ≃ B) -> (B ≃ A).
  Proof.
    intro EAB; destruct EAB as (f, eAB).
    apply qinv_from_equiv in eAB as qAB.
    destruct qAB as (finv, (α,β)).
    exists finv.
    apply equiv_from_qinv.
    exact ( { f;(β,α) } : qinv finv ).
  Defined.
  Lemma equiv_trans {A B C : UU}
    : (A ≃ B) -> (B ≃ C) -> (A ≃ C).
  Proof.
    intros EAB EBC;
      destruct EAB as (f, eAB); destruct EBC as (g, eBC).
    apply qinv_from_equiv in eAB as qAB.
    apply qinv_from_equiv in eBC as qBC.
    destruct qAB as (finv, (fα,fβ)).
    destruct qBC as (ginv, (gα,gβ)).
    exists (g∘f).
    apply equiv_from_qinv.
    exists (finv ∘ ginv); split; eapply homotopy_trans.
    - intro c. apply (ap g (fα (ginv c))).
    - assumption.
    - intro a; apply (ap finv (gβ (f a))).
    - assumption.
  Defined.
End Homotopies_and_Equivalences.

Notation "f ~ g" := (homotopy f g) (at level 70, no associativity).
Notation "A ≃ B" := (Σ f:A->B, isequiv f)
                      (at level 80, no associativity) : type_scope.

Create HintDb PathGroupoid.
Hint Rewrite @path_inverse_l : PathGroupoid.
Hint Rewrite @path_inverse_r : PathGroupoid.
Hint Rewrite @path_inverse_inverse : PathGroupoid.
Hint Rewrite <- @path_compose_rid : PathGroupoid.
Hint Rewrite @path_compose_assoc : PathGroupoid.
Hint Rewrite @path_inverse_l_assoc : PathGroupoid.
Hint Rewrite @path_inverse_r_assoc : PathGroupoid.


Section The_Higher_Groupoid_Structure_of_Type_Formers.
End The_Higher_Groupoid_Structure_of_Type_Formers.


Section Cartesian_Product_Types.
  (* rather than jump into the theorem, we'll build some machinery *)
  Definition fsteq {A B : UU} {x y : A×B} (p : x=y) := ap fst p.
  Definition sndeq {A B : UU} {x y : A×B} (p : x=y) := ap snd p.
  Definition paireq {A B : UU} {x y : A×B}
             (pq : (fst x = fst y)×(snd x = snd y))
    : x = y.
  Proof. destruct pq as (p,q);
           destruct x as (a,b); destruct y as (a',b');
             simpl in p,q; destruct p; destruct q; reflexivity.
  Defined.
  Theorem prodeq_distribute {A B : UU} {x y : A×B}
    : (x = y) ≃ ( (fst x = fst y) × (snd x = snd y) ).
  Proof.
    exists (λ p, (fsteq p, sndeq p)).
    apply equiv_from_qinv.
    exists paireq.
    split; [intro s; simpl in s | intro r].
    - destruct x as (a,b); destruct y as (a',b');
        destruct s as (p,q); simpl in p, q; induction p; induction q;
          reflexivity.
    - induction r; destruct x; reflexivity.
  Defined.

  Definition thm_2_6_2 {A B} {x y} := @prodeq_distribute A B x y.

  Example prod_uniq_as_cor {A B : UU} {z : A×B} : z = (fst z, snd z).
  Proof. apply paireq; split; reflexivity. Qed.

  Corollary fstpaireq {A B : UU} {x y : A×B}
            (p : fst x = fst y) (q : snd x = snd y)
    : fsteq (paireq (p,q)) = p.
  Proof. destruct x as (xa,xb); destruct y as (ya,yb);
           simpl in p, q; destruct p, q; reflexivity. Qed.
  Corollary sndpaireq {A B : UU} {x y : A×B}
            (p : fst x = fst y) (q : snd x = snd y)
    : sndeq (paireq (p,q)) = q.
  Proof. destruct x as (xa,xb); destruct y as (ya,yb);
           simpl in p, q; destruct p, q; reflexivity. Qed.
  Corollary prodeq_uniq {A B : UU} {x y : A×B} {r : x=y}
    : r = paireq (fsteq r, sndeq r).
  Proof. destruct r; destruct x; reflexivity. Qed.
  (* Note that the above are the same proofs we used for
     the homotopies in the theorem. *)

  (* groupoid structure with respect to pairs *)
  Lemma fsteq_refl {A B : UU} {z : A×B}
    : fsteq (idpath z) = idpath (fst z).
  Proof. destruct z; reflexivity. Defined.
  Lemma sndeq_refl {A B : UU} {z : A×B}
    : sndeq (idpath z) = idpath (snd z).
  Proof. destruct z; reflexivity. Defined.
  Lemma paireq_inv {A B : UU} {x y : A×B}
        {p : fst x = fst y} {q : snd x = snd y}
    : paireq (inv p, inv q) = inv (paireq (p,q)).
  Proof. destruct x,y; simpl in p,q; destruct p,q; reflexivity. Defined.
  Lemma paireq_comp {A B : UU} {x y z : A×B}
        {p : fst x = fst y} {q : fst y = fst z}
        {p' : snd x = snd y} {q' : snd y = snd z}
    : paireq(p ∙ q, p' ∙ q') = paireq(p,p') ∙ paireq(q,q').
  Proof. destruct x,y; simpl in p, q, p', q'; destruct p,p';
           reflexivity. Defined.

  (* now we want to take advantage of the fibration notation scope... *)
  Notation "A × B" := (λ x, (A x) × (B x)) : fibration_scope.

  Theorem transport_prod {Z : UU} {A B : Z -> UU}
          {z w : Z} {p : z=w} {x : (A z)×(B z)}
    : transport (A×B)%fiber p x = (transport A p (fst x),
                                   transport B p (snd x)).
  Proof. destruct p; apply paireq; split; reflexivity. Qed.
  Definition thm_2_6_4 {Z} {A B} {z w} {p} {x}
    := @transport_prod Z A B z w p x.

  Theorem ap_paireq {A B A' B' : UU} {x y : A×B}
          {p : fst x = fst y} {q : snd x = snd y}
          {g : A -> A'} {h : B -> B'}
    : let f x := (g (fst x), h (snd x)) in
      let FG x := idpath : fst (f x) = g (fst x) in
      ap f (paireq(p,q)) = paireq( (FG x)∙(ap g p)∙(inv (FG y)), ap h q ).
  Proof. intros f FG; destruct x,y; simpl in p,q;
           destruct p,q; reflexivity. Qed.
  Definition thm_2_6_5 {A B A' B'} {x y} {p} {q} {g} {h}
    := @ap_paireq A B A' B' x y p q g h.
End Cartesian_Product_Types.

Section Σ_Types.
  Definition proj1eq {A : UU} {P : A -> UU} {w w' : total P}
             (p : w = w') : w.1 = w'.1 := ap proj1 p.
 (* Definition rew_proj2eq {A : UU} {P : A->UU} (w : total P)
    : (∏ s : total P, P s.1) -> section P := λ f, λ s, f { s ; w.2 }. *)
  Definition proj2eq {A : UU} {P : A -> UU} {w w' : total P}
             (p : w = w')
    : transport P (proj1eq p) w.2 = w'.2
    := (inv lem_2_3_10) ∙ @apd _ (P∘proj1) _ _ (@proj2 _ P) p.
  Definition projeq {A : UU} {P : A -> UU} {w w' : total P}
             (p : w = w')
    : Σ(p : w.1 = w'.1), p # w.2 = w'.2
    := { proj1eq p ; proj2eq p }.
  Definition spaireq {A : UU} {P : A -> UU} {w w' : Σ x:A, P x}
             (pq : Σ (p : w.1 = w'.1), p # w.2 = w'.2)
    : w = w'.
  Proof. destruct w as (w1,w2); destruct w' as (w'1,w'2);
           simpl in pq; destruct pq as (p,q); destruct p;
             simpl in q; destruct q; reflexivity. Defined.
  Theorem sigeq_distribute {A : UU} {P : A -> UU} {w w' : Σ x:A, P x}
    : (w = w') ≃ Σ(p : w.1 = w'.1), p # w.2 = w'.2.
  Proof.
    exists projeq.
    apply equiv_from_qinv.
    exists spaireq.
    split; [intro r | intro p].
    - destruct w as (w1,w2); destruct w' as (w1',w2');
        simpl in r; destruct r as (r1,r2); destruct r1;
          simpl in r2; destruct r2; reflexivity.
    - destruct p; destruct w as (w1,w2); reflexivity.
  Qed.
  Definition thm_2_7_2 {A} {P} {w w'} := @sigeq_distribute A P w w'.

  Corollary sig_uniq {A : UU} {P : A -> UU} {z : Σ x:A, P x}
    : z = { z.1 ; z.2 }.
  Proof. apply spaireq; exists idpath; exact idpath. Defined.
  Definition cor_2_7_3 {A} {P} {z} := @sig_uniq A P z.

  Corollary lift {A : UU} {P : A -> UU} {x y : A}
            (u : P x) (p : x = y)
    : {x; u} = {y; p#u} :> total P.
  Proof. apply spaireq; exists p; reflexivity. Defined.

  Definition sig_fiber {X : UU} (P : X -> UU) (Q : (total P) -> UU)
    : fibration X := λ x, Σ (u : P x), Q{x;u}.

  Theorem transport_sig {A : UU} (P : A -> UU) (Q : (total P) -> UU)
          {x y : A} (p : x=y) (u : P x) (z : Q {x;u})
    : transport (sig_fiber P Q) p {u;z}
      = 
      { transport P p u ; transport Q (lift u p) z }.
  Proof. induction p; reflexivity. Defined.

  (* a functorality theorem for Σ-types, and interaction with the
     groupoid structure of equality are left as exercises *)
End Σ_Types.

Section The_Unit_Type.
  Theorem thm_2_8_1 {x y : 𝟙} {p : x=y}
  : (x=y) ≃ 𝟙.
  Proof.
    exists (λ _, tt).
    apply equiv_from_qinv.
    exists (λ _, unit_rect (λ a,a=y)
                           (unit_rect (λ b,tt=b) idpath y)
                           x).
    split; [ intro u; destruct u | intro q; destruct q ].
    - reflexivity.
    - destruct x; reflexivity.
  Qed.
End The_Unit_Type.

Section Pi_Types_and_the_Function_Extensionality_Axiom.
  (* the alternate chapter title,
     "Dependent Types and the Sorcerer's Stone"
     was unfortunately already taken. *)
 
  Definition happly {A : UU} {B : A -> UU} {f g : ∏ x:A, B x}
  : (f = g) -> ∏ x:A, f x = g x.
  Proof. intros p x; induction p; reflexivity. Defined.
  
  Axiom funext_qinv : forall (A : UU) (B : A -> UU) (f g : ∏ x:A, B x),
      qinv (@happly A B f g).

  Theorem funext_equiv {A : UU} {B : A -> UU} {f g : ∏ x:A, B x}
    : (f = g) ≃ ∏ x:A, f x = g x.
  Proof. exact { happly ;
                 (equiv_from_qinv (funext_qinv A B f g)) }. Defined.
  Definition axiom_2_9_3 {A} {B} {f g} := @funext_equiv A B f g.

  Definition funext {A : UU} {B : A -> UU} {f g : ∏ x:A, B x}
    : (∏ x:A, f x = g x) -> f = g
    := (funext_qinv A B f g).1.

  Definition funext_compute {A : UU} {B : A -> UU} {f g : ∏ x:A, B x}
             (h : ∏ x:A, f x = g x)
    : happly (funext h) = h
    := (fst (funext_qinv A B f g).2) h.

  Definition funext_uniq {A : UU} {B : A -> UU} {f g : ∏ x:A, B x}
             (p : f = g)
    : p = funext (happly p)
    := inv ((snd (funext_qinv A B f g).2) p).

  (* the groupoid structure of equality w.r.t. funext *)
  Lemma funext_refl {A : UU} {B : A -> UU} {f : ∏ x:A, B x}
    : idpath f = funext (λ x, idpath (f x)).
  Proof. apply (funext_uniq (idpath f)). Defined.
  Lemma funext_symm {A : UU} {B : A -> UU} {f g : ∏ x:A, B x}
        (α : f = g)
    : (inv α) = funext (λ x, inv (happly α x)).
  Proof. induction α. apply funext_refl. Defined.
  Lemma funext_trans {A : UU} {B : A -> UU} {f g h : ∏ x:A, B x}
        (α : f = g) (β : g = h)
    : (α ∙ β) = funext (λ x, (happly α x) ∙ (happly β x)).
  Proof. induction α; apply funext_uniq. Defined.

  Lemma transport_f {X : UU} {x1 x2 : X} (A B : X -> UU)
        (p : x1=x2) (f : A x1 -> B x1)
    : transport (A -> B)%fiber p f
      =
      λ x, transport B p (f (transport A (inv p) x)).
  Proof. destruct p; reflexivity. Defined.
  Definition eqn_2_9_4 {X : UU} {x1 x2 : X}
    := @transport_f X x1 x2.

  (* I don't really know how to think about the type of B
     here, but it's really important for the dependent function
     transport lemma... *)
  Definition pi_fiber {X:UU} (A : X -> UU) (B : ∏ x:X, A x -> UU)
    : fibration X
    := λ x, ∏ a : A x, B x a.
  Definition hat_fiber {X:UU} {A : X -> UU} (B : ∏ x:X, A x -> UU)
    : fibration (total A)
    := λ w, B w.1 w.2 .

  Lemma transport_d {X : UU} {x1 x2 : X}
        (A : X -> UU) (B : ∏ x:X, A x -> UU)
        (p : x1=x2) (f : pi_fiber A B x1) (a : A x2)
    : transport (pi_fiber A B) p f a
      =
      transport (hat_fiber B) (inv (lift a (inv p))) (f ((inv p)#a)).
  Proof. induction p; reflexivity. Defined.
  Definition eqn_2_9_5  {X : UU} {x1 x2 : X}
    := @transport_d X x1 x2.
  
  Lemma lem_2_9_6 {X : UU} {x y : X} {A B : X -> UU} {p : x=y}
        {f : A x -> B x} {g : A y -> B y}
    : (transport (A -> B)%fiber p f = g)
        ≃
      ∏ a : A x, p#(f a) = g (p#a).
  Proof. induction p; apply funext_equiv. Defined.

  (* This is an insane thing to construct, and I don't know or
     care what the book is getting at at this point *)
  Corollary cor_2_9_6 {X : UU} (A B : X -> UU) {x y : X} {p : x=y}
            {f : A x -> B x} {g : A y -> B y}
            (q : transport (A -> B)%fiber p f = g)
            (a : A x)
    : happly q (p#a)
      =
      (happly (transport_f A B p f) (p#a))
      ∙ (ap (transport B p) (ap f
            ((@lem_2_3_9 _ A _ _ _ _ _ _)
               ∙ (happly (ap (transport A) (path_inverse_r p)) a)
               ∙ idpath
            )
        ))
      ∙ ((lem_2_9_6.1 q) a).
  Proof. induction p; reflexivity. Qed.

  (* No, I will not repeat this insanity for dependent functions *)

  Lemma lem_2_9_7 {X : UU} {A : X -> UU} {B : ∏ x:X, A x -> UU}
        {x y : X} {p : x=y}
        {f : pi_fiber A B x} {g : pi_fiber A B y}
    : (transport (pi_fiber A B) p f = g)
        ≃
      (∏ a : A x, transport (hat_fiber B) (lift a p) (f a)
                  =
                  g (p # a)).
  Proof. induction p; apply funext_equiv. Defined.

  (* on reflection, I went back and wrote the note at the beginning of
     this chapter file because it is the only peek into justifying
     this utter insanity delusion *)
  (* Then I went and tried to give construction functions for
     type-families/fibrations, because maybe that's a step in the right
     direction. *)
End Pi_Types_and_the_Function_Extensionality_Axiom.


Section Universes_and_the_Univalence_Axiom.
  (* I depart from the book somewhat here.
     We get a more consistent and useful definition of idtoeqv
     if we base it on an earlier general result about transport
     yielding equivalences *)
  Definition idtoeqv {A B : UU}
  : (A = B) -> (A ≃ B).
  Proof. intro p; exists (transport idfun p);
           apply (transport_isequiv idfun p). Defined.

  (* there is some subtlety I'm probably getting wrong in these
     definitions *)
  Axiom idtoeqv_isequiv : forall A B : UU, isequiv (@idtoeqv A B).
  Definition Univalence {A B : UU}
    : (A = B) ≃ (A ≃ B)
    := { @idtoeqv A B ; idtoeqv_isequiv A B }.

  (* 'univalence axiom' *)
  Definition ua {A B : UU}
    : (A ≃ B) -> (A = B)
    := (qinv_from_equiv (idtoeqv_isequiv A B)).1.
  
  Definition ua_compute {A B : UU} (e : A ≃ B)
    : idtoeqv (ua e) = e
    := (fst (qinv_from_equiv (idtoeqv_isequiv A B)).2) e.
  Definition ua_uniq {A B : UU} {p : A = B}
    : p = ua (idtoeqv p)
    := inv ( (snd (qinv_from_equiv (idtoeqv_isequiv A B)).2) p ).

  Definition ua_compute_1 {A B : UU} {e : A ≃ B}
    : transport idfun (ua e) = e.1
    := ap proj1 (ua_compute e).

  (* easier to do the following lemmas, for which I ignore the
     given transport proofs..., using these lemmas *)
  Lemma idtoeqv_symm {A B : UU} {p : A = B}
    : idtoeqv (inv p) = equiv_symm (idtoeqv p).
  Proof. induction p; reflexivity. Defined.
  Lemma idtoeqv_trans {A B C : UU} {p : A = B} {q : B = C}
    : idtoeqv (p ∙ q) = equiv_trans (idtoeqv p) (idtoeqv q).
  Proof. induction p; induction q; reflexivity. Defined.

  Lemma ua_refl {A : UU}
    : idpath A = ua (@equiv_refl A).
  Proof.  apply (@ua_uniq A A). Defined.
  Lemma ua_symm {A B : UU} {f : A ≃ B}
    : inv (ua f) = ua (equiv_symm f).
  Proof.
    set (p := ua f); rewrite ua_uniq;
      rewrite idtoeqv_symm; unfold p; rewrite ua_compute;
        reflexivity.
  Qed.
  Lemma ua_trans {A B C : UU} {f : A ≃ B} {g : B ≃ C}
    : (ua f) ∙ (ua g) = ua (equiv_trans f g).
  Proof.
    set (p := ua f); set (q := ua g);
      rewrite ua_uniq; rewrite idtoeqv_trans;
        unfold p, q; repeat rewrite ua_compute;
          reflexivity.
  Qed.

  Lemma lem_2_10_5 {A : UU} {B : A -> UU} {x y : A} {p : x=y} (u : B x)
    : transport B p u = (idtoeqv (ap B p)).1 u.
  Proof. apply @lem_2_3_10 with (P := idfun) (f := B). Defined.
End Universes_and_the_Univalence_Axiom.



Section Identity_Type.
  (* of my own devising here... *)
  Lemma natgen_homotopy {A B : UU} {a a' : A} {b : B}
        (p : a = a') (f g : A -> B) {q : b = f a} (H : f ~ g)
  : q ∙ (H a) ∙ (ap g p) = q ∙ (ap f p) ∙ (H a').
  Proof.
    rewrite <- path_compose_assoc;
      rewrite (lem_2_4_3 p f g H);
      autorewrite with PathGroupoid; reflexivity.
  Defined.

  (* the following proof was needlessly brutal to write.
     There should be a more succinct way of expressing equational
     rewriting in practice that still allows a high degree of control *)
  Theorem ap_isequiv {A B : UU} (f : A -> B)
          {a a' : A} (fe : isequiv f)
    : (a = a') ≃ (f a = f a').
  Proof. apply qinv_from_equiv in fe as fq.
         destruct fq as (g, (R, L)).
         exists (ap f); apply equiv_from_qinv.
         exists (λ p, (inv (L a)) ∙ (ap g p) ∙ (L a') ).
         split; [ intro q | intro p ]; unfold funcomp.
         {
           assert ( ap f (inv (L a) ∙ ap g q ∙ L a')
                    = inv (R (f a)) ∙ R (f a)
                          ∙ ap f (inv (L a) ∙ ap g q ∙ L a')
                          ∙ inv (R (f a')) ∙ R (f a') ) as Eq1.
           { autorewrite with PathGroupoid; reflexivity. }
           assert ( inv (R (f a)) ∙ R (f a)
                        ∙ ap f (inv (L a) ∙ ap g q ∙ L a')
                        ∙ inv (R (f a')) ∙ R (f a')
                    = inv (R (f a))
                          ∙ ap f (ap g (ap f (inv (L a) ∙ ap g q ∙ L a')))
                          ∙ R (f a') ) as Eq2.
           { replace (R (f a)) with (R (f (idfun a))) by trivial;
               replace (ap f (inv (L a) ∙ ap g q ∙ L a'))
                 with (ap idfun (ap f (inv (L a) ∙ ap g q ∙ L a')))
               by (rewrite ap_idfun; trivial);
               rewrite (natgen_homotopy
                          (ap f (inv (L a) ∙ ap g q ∙ L a'))
                          _ _ R);
               autorewrite with PathGroupoid;
               rewrite <- ap_func_compose;
               rewrite ap_idfun;  trivial. }
           assert ( inv (R (f a))
                        ∙ ap f (ap g (ap f (inv (L a) ∙ ap g q ∙ L a')))
                        ∙ R (f a')
                    = inv (R (f a))
                          ∙ ap f (L a ∙ inv (L a) ∙ ap g q
                                    ∙ L a' ∙ inv (L a'))
                          ∙ R (f a') ) as Eq3.
           { rewrite (@ap_func_compose _ _ _ _ _ _ f g).
             replace (ap (g ∘ f) (inv (L a) ∙ ap g q ∙ L a'))
               with  (L a ∙ inv (L a) ∙ ap g q ∙ L a' ∙ inv (L a'));
               trivial.
             rewrite path_compose_lid;
               rewrite <- (path_inverse_l (inv (L a))).
             rewrite (natgen_homotopy
                        (inv (L a) ∙ ap g q ∙ L a') _ _ (λ x, inv (L x))).
             rewrite ap_idfun;
               autorewrite with PathGroupoid; trivial. }
           assert ( inv (R (f a))
                        ∙ ap f (L a ∙ inv (L a) ∙ ap g q ∙ L a' ∙ inv (L a'))
                        ∙ R (f a')
                    = inv (R (f a)) ∙ ap f (ap g q) ∙ R (f a') ) as Eq4.
           { autorewrite with PathGroupoid; trivial. }
           assert ( inv (R (f a)) ∙ ap f (ap g q) ∙ R (f a') = q ) as Eq5.
           { rewrite ap_func_compose;
               rewrite <- (natgen_homotopy q _ _ R);
               rewrite ap_idfun; autorewrite with PathGroupoid; trivial. }
           apply (Eq1 ∙ Eq2 ∙ Eq3 ∙ Eq4 ∙ Eq5).
         }
         {
           rewrite ap_func_compose.
           rewrite <- (natgen_homotopy p _ _ L).
           rewrite ap_idfun.
           autorewrite with PathGroupoid; trivial.
         }
  Qed.


  Example prod_eq_equiv {A B : UU} {w w' : A×B}
          (p q : w=w')
    : (p = q) ≃ (fsteq p = fsteq q)×(sndeq p = sndeq q).
  Proof.
    pose (E := ua (@ap_isequiv _ _ (λ x, (fsteq x, sndeq x))
                               p q prodeq_distribute.2)).
    rewrite E.
    apply (@prodeq_distribute _ _ (fsteq p, sndeq p)).
  Qed.
    
  Example dep_eq_equiv {A : UU} {B : A -> UU} {f g : ∏ x:A, B x}
          (p q : f=g)
    : (p = q) ≃ ∏ x:A, happly p x = happly q x.
  Proof.
    pose (E := ua (@ap_isequiv _ _ happly p q funext_equiv.2)).
    rewrite E.
    apply funext_equiv.
  Qed.

  Lemma transport_eq_r {A : UU} {a x1 x2 : A} (p : x1=x2) (q : a = x1)
    : transport (λ x, a = x) p q = q ∙ p.
  Proof. destruct p; autorewrite with PathGroupoid; reflexivity. Defined.
  Lemma transport_eq_l {A : UU} {a x1 x2 : A} (p : x1=x2) (q : x1 = a)
    : transport (λ x, x = a) p q = (inv p) ∙ q.
  Proof. destruct p; autorewrite with PathGroupoid; reflexivity. Defined.
  Lemma transport_eq_both {A : UU} {a x1 x2 : A} (p : x1=x2) (q : x1 = x1)
    : transport (λ x, x = x) p q = (inv p) ∙ q ∙ p.
  Proof. destruct p; autorewrite with PathGroupoid; reflexivity. Defined.

  Theorem  thm_2_11_3 {A B : UU} {a a' : A} {f g : A -> B}
          (p : a=a') (q : f a = g a)
    : transport (λ x, f x = g x) p q = inv (ap f p) ∙ q ∙ ap g p.
  Proof. destruct p; autorewrite with PathGroupoid; reflexivity. Defined.
  
  Theorem thm_2_11_4 {A : UU} {B : A -> UU} {f g : ∏ x:A, B x}
          {a a' : A} (p : a=a') (q : f a = g a)
    : transport (λ x, f x = g x) p q
      = inv (apd f p) ∙ ap (transport B p) q ∙ apd g p.
  Proof. destruct p; simpl; autorewrite with PathGroupoid;
           rewrite ap_idfun; reflexivity. Defined.

  Theorem thm_2_11_5 {A : UU} {a a' : A}
          (p : a = a') (q : a = a) (r : a' = a')
    : (transport (λ x, x = x) p q = r) ≃ (q ∙ p = p ∙ r).
  Proof. destruct p; simpl; autorewrite with PathGroupoid;
           apply equiv_refl. Defined.
End Identity_Type.



Section Coproducts.
  Definition code_coprod_l {A B : UU} (a0 : A) (x : A + B)
    := match x with
       | inl a => (a0 = a)
       | inr b => ∅
       end.
  Definition code_coprod_r {A B : UU} (b0 : B) (x : A + B)
    := match x with
       | inl a => ∅
       | inr b => (b0 = b)
       end.

  Definition encode_coprod_l {A B : UU} (a0 : A) (x : A + B)
    : inl a0 = x -> code_coprod_l a0 x
    := λ p, transport (code_coprod_l a0) p (idpath a0).
  Definition decode_coprod_l {A B : UU} (a0 : A) (x : A + B)
    : code_coprod_l a0 x -> inl a0 = x.
  Proof. intro c; destruct x; simpl in c;
           [ apply ap; assumption | contradiction ]. Defined.
  Definition encode_coprod_r {A B : UU} (b0 : B) (x : A + B)
    : inr b0 = x -> code_coprod_r b0 x
    := λ p, transport (code_coprod_r b0) p (idpath b0).
  Definition decode_coprod_r {A B : UU} (b0 : B) (x : A + B)
    : code_coprod_r b0 x -> inr b0 = x.
  Proof. intro c; destruct x; simpl in c;
           [ contradiction | apply ap; assumption ]. Defined.

  Lemma deencode_coprod_l {A B : UU} (a0 : A) (x : A + B) (p : inl a0 = x)
    : decode_coprod_l a0 x (encode_coprod_l a0 x p) = p.
  Proof. destruct p; reflexivity. Defined.
  Lemma endecode_coprod_l {A B : UU} (a0 : A) (x : A + B)
        (c : code_coprod_l a0 x)
    : encode_coprod_l a0 x (decode_coprod_l a0 x c) = c.
  Proof. destruct x; try contradiction; simpl in c; simpl;
           unfold encode_coprod_l;
           rewrite <- lem_2_3_10; unfold funcomp; simpl;
             rewrite transport_eq_r; reflexivity. Defined.

  Lemma deencode_coprod_r {A B : UU} (b0 : B) (x : A + B) (p : inr b0 = x)
    : decode_coprod_r b0 x (encode_coprod_r b0 x p) = p.
  Proof. destruct p; reflexivity. Defined.
  Lemma endecode_coprod_r {A B : UU} (b0 : B) (x : A + B)
        (c : code_coprod_r b0 x)
    : encode_coprod_r b0 x (decode_coprod_r b0 x c) = c.
  Proof. destruct x; try contradiction; simpl in c; simpl;
           unfold encode_coprod_r;
           rewrite <- lem_2_3_10; unfold funcomp; simpl;
             rewrite transport_eq_r; reflexivity. Defined.

  Theorem coprod_l_eqvcoding {A B : UU} (a0 : A) (x : A + B)
    : (inl a0 = x) ≃ code_coprod_l a0 x.
  Proof. 
    exists (encode_coprod_l a0 x).
    apply equiv_from_qinv.
    exists (decode_coprod_l a0 x).
    split; intro; [ apply endecode_coprod_l | apply deencode_coprod_l ].
  Defined.
  Theorem coprod_r_eqvcoding {A B : UU} (b0 : B) (x : A + B)
    : (inr b0 = x) ≃ code_coprod_r b0 x.
  Proof. 
    exists (encode_coprod_r b0 x).
    apply equiv_from_qinv.
    exists (decode_coprod_r b0 x).
    split; intro; [ apply endecode_coprod_r | apply deencode_coprod_r ].
  Defined.

  Remark bool_is_unit_plus_unit : 𝟚 ≃ 𝟙 + 𝟙.
  Proof.
    exists (λ b, match b with | false => inl tt | true => inr tt end).
    apply equiv_from_qinv.
    exists (λ c, match c with | inl tt => false | inr tt => true end).
    split; intro x; destruct x; trivial; destruct u; trivial.
  Defined.
  Compute (fst (bool_is_unit_plus_unit.2)).1.

  Remark true_is_not_false : true ≠ false.
  Proof.
    intro e; apply (ap bool_is_unit_plus_unit.1) in e; simpl in e.
    apply (encode_coprod_r tt (inl tt) e).
  Defined.
End Coproducts.



Section Natural_Numbers.
  Fixpoint code_nat (m n : ℕ) :=
    match m with
    | O   => match n with
             | O   => 𝟙
             | S _ => 𝟘 end
    | S m => match n with
             | O   => 𝟘
             | S n => code_nat m n end
    end.

  Fixpoint refl_code_nat (n : ℕ) : code_nat n n :=
    match n with O => tt | S n => refl_code_nat n end.

  (* note that generalization (meaning requantifying variables into
     the goal) before doing induction is absolutely critical to
     carrying out this kind of induction on two numbers successfully *)
  Definition encode_nat (m n : ℕ) : m = n -> code_nat m n :=
    λ p : m=n, transport (λ x, code_nat m x) p (refl_code_nat m).
  Definition decode_nat (m n : ℕ) : code_nat m n -> m = n.
  Proof. generalize n as n'; clear n; induction m; intro n; induction n;
           trivial; try contradiction.
         intro c; apply (ap S); simpl in c.
         apply IHm; assumption. Defined.

  Definition deencode_nat (m n : ℕ) (p : m = n)
    : decode_nat m n (encode_nat m n p) = p.
  Proof. induction p; induction m; simpl; trivial;
           replace (idpath (S m)) with (ap S (idpath m)) by trivial;
           apply (ap (ap S)); assumption. Defined.
  Definition endecode_nat (m n : ℕ) (c : code_nat m n)
    : encode_nat m n (decode_nat m n c) = c.
  Proof. generalize c as c'; clear c;
           generalize n as n'; clear n; induction m;
             intro n; induction n; intro c; simpl;
               try (destruct c; trivial; try contradiction).
         unfold encode_nat; rewrite <- lem_2_3_10; unfold funcomp; simpl.
         fold (encode_nat m n (decode_nat m n c)).
         apply IHm.
  Defined.

  Theorem nat_eqvcoding (m n : ℕ) : (m = n) ≃ (code_nat m n).
  Proof. exists (encode_nat m n);
         apply equiv_from_qinv;
         exists (decode_nat m n);
         split; intro X; [ apply endecode_nat | apply deencode_nat ].
  Defined.

  Remark succ_not_zero (m : ℕ) : S m ≠ 0.
  Proof. intro Eq; apply (encode_nat (S m) 0); assumption. Defined.
  Remark succ_injective (m n : ℕ) : (S m = S n) -> (m = n).
  Proof. intro SEq; apply encode_nat in SEq as Eq;
           simpl in Eq; apply decode_nat; assumption. Defined.
End Natural_Numbers.


Section Example_Equality_Of_Structures.
  Definition Binop (A : UU) := (A->A->A)%type.
  Definition Assoc {A : UU} (m : Binop A) :=
    ∀ x y z : A, m x (m y z) = m (m x y) z.
  Definition SemigroupStr (A : UU) :=
    Σ m:Binop A, Assoc m.
  Definition Semigroup := Σ A:UU, SemigroupStr A.

  Definition induced_mult {A B : UU} (p : A=B) (m : A->A->A)
    := transport Binop p m.
  Definition induced_assoc {A B : UU} (p : A=B) (m : Binop A) (a : Assoc m)
    : Assoc (induced_mult p m)
    := transport (λ (Xop : total Binop), Assoc Xop.2)
                 (lift m p) a.

  (* The fact that I need to carefully pose these proofs rather than
     simply use 'rewrite transport_sig' is evidence that something
     got messed up earlier in this whole development...
     I'm thinking a bit that there might be some trick to systematizing
     transport computation via the fibration concept, including
     special notation in a fibration scope to overload all the basic
     type construction notations.
   *)
  Lemma induced_mult_from_equiv {A B : UU} (p : A=B)
        (m : Binop A) (a : Assoc m)
    : (transport SemigroupStr p { m ; a }).1 = induced_mult p m.
  Proof.
    apply (proj1eq (transport_sig Binop (λ Xm, Assoc Xm.2) p m a) ).
  Defined.
  Lemma induced_assoc_from_equiv {A B : UU} (p : A=B)
        (m : Binop A) (a : Assoc m)
    : transport Assoc (induced_mult_from_equiv p m a)
                (transport SemigroupStr p { m ; a }).2
      = induced_assoc p m a.
  Proof.
    apply (proj2eq (transport_sig Binop (λ Xm, Assoc Xm.2) p m a) ).
  Defined.

  Lemma explicit_induced_mult {A B : UU} (e : A≃B) (m : A->A->A)
        (b1 b2 : B)
    : (induced_mult (ua e) m) b1 b2
      = e.1 (m ((equiv_symm e).1 b1) ((equiv_symm e).1 b2)).
  Proof. unfold induced_mult, Binop.
         repeat rewrite transport_f.
         repeat rewrite ua_symm.
         repeat rewrite ua_compute_1.
         trivial.
  Defined.
  (* trying to compute an induced associativity proof is harrowing *)
  
  (* without the set-like properties that we'll investigate in
     Chapter 3, fully stating the equality conditions for associativity
     would be a giant pain in the butt *)
End Example_Equality_Of_Structures.


Section Universal_Properties.
  Definition fstf {X A B : UU} (f : X -> A×B) : X -> A := fst ∘ f.
  Definition sndf {X A B : UU} (f : X -> A×B) : X -> B := snd ∘ f.

  Theorem univf_prod {X A B : UU}
    : isequiv (λ f:X->A×B, (fstf f, sndf f)).
  Proof. apply equiv_from_qinv.
         exists (λ gh : (X->A)×(X->B), λ x, ((fst gh) x, (snd gh) x))%type.
         split; unfold fstf, sndf, funcomp; simpl; [ intro gh | intro f ].
         - eta_reduce; rewrite prod_uniq; trivial.
         - apply funext; intro x; rewrite prod_uniq; trivial.
  Defined.

  Definition fstd {X : UU} {A B : X -> UU} (f : ∏ x:X, (A x) × (B x))
    : ∏ x:X, A x := λ x, fst (f x).
  Definition sndd {X : UU} {A B : X -> UU} (f : ∏ x:X, (A x) × (B x))
    : ∏ x:X, B x := λ x, snd (f x).

  (* this should be LEFT TO THE READER *)
  Theorem univ_prod {X : UU} {A B : X -> UU}
    : (∏ x:X, (A x) × (B x)) ≃ (∏ x:X, A x) × (∏ x:X, B x).
  Proof. exists (λ f, (fstd f, sndd f)).
         apply equiv_from_qinv.
         exists (λ gh x,  ((fst gh) x, (snd gh) x)).
         split; intro; unfold fstd, sndd, funcomp; simpl.
         - eta_reduce; rewrite prod_uniq; trivial.
         - apply funext; intro; rewrite prod_uniq; trivial.
  Defined.

  Theorem univ_sig {X : UU} {A : X -> UU} {P : ∏ x:X, A x -> UU}
    : (∏ x:X, Σ a : A x, P x a) ≃
      (Σ (g : ∏ x:X, A x), ∏ x:X, P x (g x)).
  Proof.
    pose (fwd := λ f : (∏ x:X, Σ a : A x, P x a),
                       (spair (λ g, ∏ x:X, P x (g x))
                              (λ x:X, (f x).1)
                              (λ x:X, (f x).2)) );
      exists fwd.
    apply equiv_from_qinv.
    pose (rev := λ gh : (Σ (g : ∏ x:X, A x), ∏ x:X, P x (g x)),
                        λ x:X, spair (P x) (gh.1 x) (gh.2 x) );
      exists rev.
    split; unfold funcomp, fwd, rev; [ intro gh | intro f ]; simpl.
    - eta_reduce; rewrite <- sig_uniq; trivial.
    - apply funext; intro; rewrite <- sig_uniq; trivial.
  Defined.
End Universal_Properties.



Section Chapter_2_Exercises.
  
  (* TODO *)

  (* one random worked example sitting around from earlier *)
  Example example_2_4_8_a {A : UU} {x y z : A} (p : x=y)
    : let p_lcomp : (y=z -> x=z) := λ q, p ∙ q in
      qinv p_lcomp.
  Proof.
    intro;
    pose (p_inv := λ q:x=z, (inv p) ∙ q);
    exists p_inv.
    unfold funcomp, p_lcomp, p_inv;
    split; intro; autorewrite with PathGroupoid; reflexivity.
  Qed.

End Chapter_2_Exercises.



