
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
           (f : X -> Y) (g : ∏ y:Y, Z y)
  := λ x, g (f x).

Notation "g ∘ f" := (funcomp f g)
                      (at level 40, left associativity) : function_scope.

(* sometimes a useful tactic when dealing heavily with functions *)
Ltac eta_reduce := repeat change (λ x, ?h x) with h.

(* the chapter covers some of the deeper equivalences implied
   by curry-ing functions, but programmers may already be
   familiar with the idea *)
Definition curry {X Y : UU} {Z : X -> Y -> UU}
           (f : ∏ (xy : X×Y), Z (fst xy) (snd xy)) : ∏ (x:X) (y:Y), Z x y
  := λ (x:X) (y:Y), f(x,y).
Definition uncurry {X Y : UU} {Z : X -> Y -> UU}
           (f : ∏ (x:X) (y:Y), Z x y) : ∏ (xy : X×Y), Z (fst xy) (snd xy)
  := λ (xy : X×Y), f (fst xy) (snd xy).

Definition sigcurry {X : UU} {Y : X -> UU} {Z : ∏ x:X, Y x -> UU}
           (f : ∏ (xy : Σ x:X, Y x), Z xy.1 xy.2)
  : ∏ (x : X) (y : Y x), Z x y
  := λ (x : X) (y : Y x), f {x;y}.
Definition siguncurry {X : UU} {Y : X -> UU} {Z : ∏ x:X, Y x -> UU}
           (f : ∏ (x : X) (y : Y x), Z x y)
  : ∏ (xy : Σ x:X, Y x), Z xy.1 xy.2
  := λ (xy : Σ x:X, Y x), f xy.1 xy.2 .



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
  (* lem_2_1_1 *)
  Definition inv {A : UU} {a b : A}
             (p : a = b)
    : b = a.
  Proof.
    induction p. reflexivity.
  Defined.
  Print inv.
  (* note that we can approach either definition, but that we should
     use 'Defined' instead of 'Qed' if we want to take advantage of
     the definitional equality *)
  Compute inv (idpath 0).

  (* lem_2_1_2 *)
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


  (* Sometimes we want to write proofs that chain a sequence of
     equalities together.  Using a basic "foil" scheme from
     grade-school algebra as an example, these are commonly written
     on paper as such.

        (a+b)*(c+d) = a*(c+d) + b*(c+d)         by right-distributivity
                    = a*c + a*d + b*(c+d)       by left-distributivity
                    = a*c + a*d + b*c + b*d     by left-distributivity

     It's not obvious how you would encode this style of proof in
     Ltac.  In order to make these sorts of proofs easier to translate,
     I've written the following higher-order tactic, or "tactical."
     I'll show a 4-element associativity result using it right now.
   *)

  Tactic Notation "chain" constr(Ex) :=
    match goal with
    | |- ?Ey = _ => refine (path_compose (_ : Ey = Ex) _)
    end.
  
  Tactic Notation "chain" constr(Ex) "by" tactic(T) :=
    match goal with
    | |- ?Ey = _ => refine (path_compose (_ : Ey = Ex) _);
                    [ solve[T] | ]
    end.
  
  Remark assoc_5paths {A : UU} {a b c d e f : A}
         (p : a = b) (q : b = c) (r : c = d) (s : d = e) (t : e = f)
    : p ∙ (q ∙ (r ∙ (s ∙ t))) = (((p ∙ q) ∙ r) ∙ s) ∙ t.
  Proof.
    (* executing this tactic breaks the proof of equality into
       two halves by interposing the provided term *)
    chain ((p ∙ q) ∙ (r ∙ (s ∙ t))).
    (* proof of the left-hand *)
    apply path_compose_assoc. (* this exactly discharges the goal *)
    (* for the next rewrite, we use the 'by' clause to immediately
       discharge the left-hand sub-goal. *)
    chain (((p ∙ q) ∙ r) ∙ (s ∙ t)) by apply path_compose_assoc.
    (* now we're almost done, so we'll just solve the final goal
       directly *)
    apply path_compose_assoc.
  Defined.
  Print assoc_5paths.
  (* note that the proof is a composition of paths too! *)

  
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
           set (ru := @path_compose_rid A a b);
           apply (inv (ru _) ∙ α ∙ (ru _)).
  Defined.
  Definition whisker_l {A : UU} {a b c : A}
             {r s : b = c}
             (p : a = b) (β : r = s)
    : p ∙ r = p ∙ s.
  Proof. induction p;
           set (lu := @path_compose_lid A a c);
           apply (inv (lu _) ∙ β ∙ (lu _)).
  Defined.

  (* especially when we're working backwards from a goal
     and want to add whiskers, we need this reverse
     direction form of the above *)
  Definition cancel_whisker_r {A : UU} {a b c : A}
             {p q : a = b}
             (r : b = c) (α : p ∙ r = q ∙ r)
    : p = q.
  Proof. induction r;
           set (ru := @path_compose_rid A a b);
           apply ((ru _) ∙ α ∙ inv (ru _)). Defined.
  Definition cancel_whisker_l {A : UU} {a b c : A}
             {r s : b = c}
             (p : a = b) (β : p ∙ r = p ∙ s)
    : r = s.
  Proof. induction p;
           set (lu := @path_compose_lid A a c);
           apply ((lu _) ∙ β ∙ inv (lu _)). Defined.
  
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
    (* we can use our new chaining form here.
       see the end of the proof in the book for the chaining pattern *)
    unfold loops2 in α,β.
    chain (horizontal_1 α β).
    { (* this is a sub-goal mechanism for organizing proofs... *)
      unfold horizontal_1; simpl;
        unfold path_compose_lid; repeat rewrite <- path_compose_rid;
          trivial.
    }
    chain (horizontal_2 α β) by exact (EQ_horizontal α β).
    {
      unfold horizontal_2; simpl;
        unfold path_compose_lid; repeat rewrite <- path_compose_rid;
          trivial.
    }
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

Notation "p '∙' q" :=
  (path_compose p q)
    (at level 60, left associativity) : type_scope.

Tactic Notation "chain" constr(Ex) :=
  match goal with
  | |- ?Ey = _ => refine (path_compose (_ : Ey = Ex) _)
  end.

Tactic Notation "chain" constr(Ex) "by" tactic(T) :=
  match goal with
  | |- ?Ey = _ => refine (path_compose (_ : Ey = Ex) _);
                  [ solve[T] | ]
  end.


Section Functions_are_Functors.
  (* lem_2_2_1 *)
  Lemma ap {A B : UU} {x y : A} (f : A -> B)
  : (x = y) -> (f x) = (f y).
  Proof.
    intro p; induction p; reflexivity.
  Defined.
  Compute ap S (idpath 0).

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
  
  (* lem_2_3_1 *)
  Lemma transport {A : UU} (P : A -> UU) {x y : A} (p : x=y)
    : P x -> P y.
  Proof. induction p; exact idfun. Defined.

  Notation "p # x" :=
    (transport _ p x)
      (right associativity, at level 65, only parsing).

  (* In the pre2.v file, special notation is introduced for
     _reverse_ transport, as well as many more transport lemmas.
     These are omitted here to prevent readers' brains from melting
     quite so much more than they already are. *)

  (* we will later define lift in a way that more explicitly
     reflects the Σ structure of the equality it poses *)
  (* lem_2_3_2 *)
  Lemma lift_direct {A : UU} (P : A -> UU) {x y : A} (u : P x) (p : x=y)
    : { x ; u } = { y ; p#u }.
  Proof. induction p; reflexivity. Defined.

  (* lem_2_3_4 *)
  Lemma apd {A : UU} {P : A -> UU} {x y : A}
        (f : ∏ x:A, P x)
    : ∏ p:x=y, p#(f x) = (f y) :> (P y).
  Proof. induction p; reflexivity. Defined.

  (* lem_2_3_5 *)
  Lemma transport_const {A : UU} (B : UU) {x y : A} (p : x=y) (b : B)
    : transport (λ _, B) p b = b.
  Proof. induction p; reflexivity. Defined.

  (* lem_2_3_8 *)
  Lemma apd_factor {A B : UU} {x y : A} {f : A->B} {p : x=y}
    : apd f p = (transport_const B p (f x)) ∙ ap f p.
  Proof. induction p; reflexivity. Defined.

  (* lem_2_3_9 *)
  Lemma transport_twice {A : UU} {P : A -> UU} {x y z : A}
        (p : x=y) (q : y=z) (u : P x)
    :  q#(p#u) = (p ∙ q)#u.
  Proof. induction p; reflexivity. Defined.
  (* lem_2_3_10 *)
  Lemma transport_apeq {A B : UU} {P : B -> UU} {x y : A}
        (f : A -> B)
        (p : x=y) (u : P (f x))
    : transport (P ∘ f) p u = transport P (ap f p) u.
  Proof. induction p; reflexivity. Defined.
  (* lem_2_3_11 *)
  Lemma transport_comm_f {A : UU} {P Q : A -> UU} {x y : A}
        (f : section (P -> Q)%fiber )
        (p : x=y) (u : P x)
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
    := ∏ x:A, f x = g x.
  Notation "f ~ g" := (homotopy f g) (at level 70, no associativity).

  (* Uncomment this section if you want to try out the homotopy proofs
     for yourself.  They are very slightly non-trivial. *)
  (*
  Lemma homotopy_refl {A : UU} {P : A -> UU} {f : section P}
    : f ~ f.
  Proof.
  Defined.
  Lemma homotopy_symm {A : UU} {P : A -> UU} {f g : section P}
    : f ~ g -> g ~ f.
  Proof.
  Defined.
  Lemma homotopy_trans {A : UU} {P : A -> UU} {f g h : section P}
    : f ~ g -> g ~ h -> f ~ h.
  Proof.
  Defined.
   *)

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

  (* I am going to inspect this proof in detail in order
     to try to learn what the hell the `rewrite` tactic
     is doing.  Can we relate it to our earlier results
     about paths? *)
  Lemma natural_homotopy  {A B : UU} {x y : A}
        (p : x=y) (f g : A -> B) (H : f ~ g)
    : (H x) ∙ (ap g p) = (ap f p) ∙ (H y).
  Proof.
    Show Proof.
    induction p.
    Show Proof.
    simpl.
    rewrite <- path_compose_rid.
    Show Proof.
    reflexivity.
    Show Proof.
  Defined.
  Definition lem_2_4_3 {A B} {x y} := @natural_homotopy A B x y.
  Print natural_homotopy.

  (* An explanation of the term generated by the above proof *)
  (*
    This is the initial proof state. I will just elaborate the hole
    as we go.
      λ (A B : UU) (x y : A) (p : x = y) (f g : A -> B) (H : f ~ g), □

    The `induction p` introduces a paths_rect form.
    Note that pattern matching has automatically constructed the
    type family (i.e. fibration) for us
      paths_rect x
                 (λ (y':A) (p':x=y'), H x ∙ ap g p' = ap f p' ∙ H y')
                 □
                 y
                 p

    `simpl` constructs no proof terms

    The `rewrite` tactic is not quite so simple.  It generates this
    abominable word salad, which we will return to in one moment.
      internal_paths_rew (f x = g x)
                         (H x)
                         (λ p' : f x = g x, p' = H x)
                         □
                         (H x ∙ idpath (g x))
                         (path_compose_rid (H x))
    Finally, we conclude by filling in that last hole with
      idpath (H x)

    So, what the heck is `internal_paths_rew` ?
   *)
  Print internal_paths_rew.
  (*
    Here is a nicer presentation of that printout:
   *)
  Definition redefined_internal_paths_rew
             (A : UU) (a : A)
             (P : A -> UU)
             (f : P a) (y : A) (p : a = y)
    : P y
    := match p in (_ = y') return (P y') with
       | idpath => f
       end.
  (*
    In other words, we can see that the actual substance of
    internal_paths_rew, like many of our lemmas about paths, boils
    down to a simple path-destruction/induction.  We are likely to
    learn more by examining the type signature in that case.

    Oddly, the last argument `p:a=y` is the most informative.
    Looking back, we can see that `A,a,y` can all be inferred from
    `p` directly.  If we look at the specific value supplied for `p`
    in the proof of the naturality of homotopies, we find the actual
    Lemma that we called `rewrite` with.  We can immediately see that
      y := H x ∙ idpath (g x)
      a := H x
      A := f x = g x
    which is all just an expansion of the statement that
      (path_compose_rid (H x)) := H x = H x ∙ idpath (g x)

    What we don't have from this simple account is the additional data
      P   := λ a':A, a' = H x
      f   := □
      OUT := H x ∙ idpath (g x) = H x
    That is, the remaining bits of the signature define
      1) a context in which rewriting is to occur, `P`
      2) a proof of the context filled with the left of the equality
           `f : (P a)`
      3) the resulting full term which is a proof of the context
         filled with the right side of the equality
           `OUT : (P y)`

    Consider an unreasonably overlooked theorem from Chapter 1.
   *)
  Print indiscernability_of_identicals.
  (*
    i.e. if we rename the variables
    indiscernability_of_identicals
             (A : UU)
             (P : A -> UU)
             (a : A) (y : A)
             (p : a = y)
             (f : P a)
      : P y

    So, this is the generic substitution principle we use for
    rewriting, and we can immediately see that it relies unavoidably
    on the ability of the pattern matching engine to correctly infer
    a context pattern `P : A -> UU`, which may often be a tall task.

    We can learn a crucial lesson about the limits of the rewriting
    tactic as a result.  If the inference of that *type-family* or
    *fibration* function cannot be automagically accomplished, Coq
    will come back and barf to us.

    Furthermore, consider *transport* which is central to stating
    many of the results in this theory.  What is its type?
   *)
  Print transport.
  (*
    (again with liberties in renaming of variables)

    transport (A : UU) (P : A -> UU)
              (a y : A)
              (p : a = y)
              (f : P a)
      : P y

    That is, we've redefined the exact same function multiple times
    in order to conceptualize it different ways.  Maybe this will
    jog some other thoughts about why this chapter is structured the
    way that it is.

   *)


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

  (* ex_2_4_9 *)
  Example transport_is_qinv {A : UU} {P : A -> UU} {x y : A} (p : x = y)
    : qinv (transport P p : P x -> P y).
  Proof.
    exists (transport P (inv p)).
    unfold funcomp; split; intro; rewrite transport_twice;
      autorewrite with PathGroupoid; reflexivity.
  Defined.

  Definition isequiv {A B : UU} (f : A -> B)
    := (Σ g:B->A, f ∘ g ~ (@idfun B)) × (Σ h:B->A, h ∘ f ~ (@idfun A)).

  (* here are the first two of three properties that
     are required for a type to be an equivalence *)
  Lemma equiv_from_qinv {A B : UU} {f : A -> B}
    : qinv f -> isequiv f.
  Proof.
    intro qf; destruct qf as [g (α , β)];
      split; exists g; assumption.
  Defined.
  Lemma qinv_from_equiv {A B : UU} {f : A -> B}
    : isequiv f -> qinv f.
  Proof.
    intro ef; destruct ef as [ (g , α) (h , β) ];
    pose (γ x := (inv (β (g x))) ∙ ap h (α x) : g x = h x);
    pose (β' x := (γ ∘ f) x ∙ β x);
    exact { g ; (α, β') }.
  Defined.
  (* the following property is true, but proof is postponed
     to a later chapter *)
  (*
  Lemma equiv_property_3 (A B : UU) (f : A -> B)
    : ∏ e1 e2 : isequiv f, e1 = e2.
   *)

  Definition equiv (A B : UU) := (Σ f:A->B, isequiv f).
  Notation "A ≃ B" :=
    (equiv A B)
      (at level 80, no associativity) : type_scope.
  (* input: \~- or \simeq *)

  (* This is an important lemma, that I've added
     compared to the book development.
     While it is obviously true on reflection from any number
     of angles having it explicitly as an object can be helpful.
   *)
  Remark transport_isequiv {X : UU} (P : X -> UU) {x y : X} (p : x=y)
    : isequiv (transport P p).
  Proof. apply equiv_from_qinv; apply transport_is_qinv. Defined.


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
Notation "A ≃ B" := (@equiv A B)
                      (at level 80, no associativity) : type_scope.

Create HintDb PathGroupoid.
Hint Rewrite @path_inverse_l : PathGroupoid.
Hint Rewrite @path_inverse_r : PathGroupoid.
Hint Rewrite @path_inverse_inverse : PathGroupoid.
Hint Rewrite <- @path_compose_rid : PathGroupoid.
Hint Rewrite @path_compose_assoc : PathGroupoid.
Hint Rewrite @path_inverse_l_assoc : PathGroupoid.
Hint Rewrite @path_inverse_r_assoc : PathGroupoid.

(* We can use some Coq magic to encode one of the
   "abuses of notation" from the book, namely treating an
   equivalence as if it were simply the function in its first half. *)
Definition equiv_function {A B : UU} (e : A≃B) : A -> B := e.1 .
Coercion equiv_function : equiv >-> Funclass.
(* note how we can now apply an equivalence! *)
Compute equiv_refl 3.
(* the following commands can be used to iterrogate the
   current state of Coercions in the Coq system *)
(*
  Print Classes.
  Print Coercions.
  Print Graph.
 *)

Section The_Higher_Groupoid_Structure_of_Type_Formers.
End The_Higher_Groupoid_Structure_of_Type_Formers.


(* Note that in the pre2.v file the following sections on
   non-dependent and dependent pairs have been significantly
   reworked.  However, I am leaving the other form of them
   here as is.  For whatever reason, I've been very unsatisfied
   with these sections.  Reading through the Foundations library
   inside of UniMath revealed a certain amount of discontent
   also on display there ab out how to provide a more canonical
   presentation of this basic machinery *)

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
  (* thm_2_6_2 *)
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

  (* thm_2_6_4 *)
  Theorem transport_prod {Z : UU} {A B : Z -> UU}
          {z w : Z} {p : z=w} {x : (A z)×(B z)}
    : transport (A×B)%fiber p x = (transport A p (fst x),
                                   transport B p (snd x)).
  Proof. destruct p; apply paireq; split; reflexivity. Qed.


  (* thm_2_6_5 *)
  Theorem ap_paireq {A B A' B' : UU} {x y : A×B}
          {p : fst x = fst y} {q : snd x = snd y}
          {g : A -> A'} {h : B -> B'}
    : ap  (λ x, (g (fst x), h (snd x)))  (paireq(p,q))
      = paireq( (idpath (fst (g (fst x), h (snd x))))
                  ∙ (ap g p)
                  ∙ (idpath (fst (g (fst y), h (snd y)))),
                (ap h q) ).
  Proof. destruct x,y; simpl in p,q; destruct p,q; reflexivity. Defined.
End Cartesian_Product_Types.

Section Σ_Types.
  Definition proj1eq {A : UU} {P : A -> UU} {w w' : total P}
             (p : w = w') : w.1 = w'.1 := ap proj1 p.
 (* Definition rew_proj2eq {A : UU} {P : A->UU} (w : total P)
    : (∏ s : total P, P s.1) -> section P := λ f, λ s, f { s ; w.2 }. *)
  Definition proj2eq {A : UU} {P : A -> UU} {w w' : total P}
             (p : w = w')
    : transport P (proj1eq p) w.2 = w'.2
    := (inv (transport_apeq _ _ _)) ∙ @apd _ (P∘proj1) _ _ (@proj2 _ P) p.
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
  (* thm_2_7_2 *)
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
  Defined.

  Definition sigeq_compute {A : UU} {P : A -> UU} {w w' : Σ x:A, P x}
             (pq : Σ (p : w.1 = w'.1), p # w.2 = w'.2)
    : projeq (spaireq pq) = pq
    := (fst sigeq_distribute.2).2 pq.
  Definition sigeq_compute1 {A : UU} {P : A -> UU} {w w' : Σ x:A, P x}
             (pq : Σ (p : w.1 = w'.1), p # w.2 = w'.2)
    : proj1eq (spaireq pq) = pq.1
    := proj1eq (sigeq_compute pq).
  Definition sigeq_compute2 {A : UU} {P : A -> UU} {w w' : Σ x:A, P x}
             (pq : Σ (p : w.1 = w'.1), p # w.2 = w'.2)
    : transport (λ p : w.1 = w'.1, transport P p w.2 = w'.2)
                (sigeq_compute1 pq) (projeq (spaireq pq)).2
      = pq.2
    := proj2eq (sigeq_compute pq).
  Definition sigeq_uniq {A : UU} {P : A -> UU} {w w' : Σ x:A, P x}
             (p : w=w')
    : spaireq (projeq p) = p
    := (snd sigeq_distribute.2).2 p.

  (* cor_2_7_3 *)
  Corollary sig_uniq {A : UU} {P : A -> UU} {z : Σ x:A, P x}
    : z = { z.1 ; z.2 }.
  Proof. apply spaireq; exists idpath; exact idpath. Defined.

  Corollary lift {A : UU} {P : A -> UU} {x y : A}
            (u : P x) (p : x = y)
    : {x; u} = {y; p#u} :> total P.
  Proof. apply spaireq; exists p; reflexivity. Defined.

  Definition sig_fiber {X : UU} (P : X -> UU) (Q : (total P) -> UU)
    : fibration X := λ x, Σ (u : P x), Q{x;u}.

  Theorem transport_sig {A : UU} (P : A -> UU) (Q : (total P) -> UU)
          {x y : A} (p : x=y) (uz : sig_fiber P Q x)
    : transport (sig_fiber P Q) p uz
      = 
      { transport P p uz.1 ; transport Q (lift uz.1 p) uz.2 }.
  Proof. induction p; reflexivity. Defined.

  (* a functorality theorem for Σ-types, and interaction with the
     groupoid structure of equality are left as exercises *)
End Σ_Types.

Section The_Unit_Type.
  Lemma uniteq (x y : 𝟙) : x = y.
  Proof. induction x,y; reflexivity. Defined.
  (* thm_2_8_1 *)
  Theorem uniteq_is_unit {x y : 𝟙} {p : x=y}
  : (x=y) ≃ 𝟙.
  Proof.
    exists (λ _, tt).
    apply equiv_from_qinv.
    exists (λ _, uniteq x y).
    split; [ intro u; destruct u | intro q; destruct q ].
    - reflexivity.
    - destruct x; reflexivity.
  Qed.

  (* Consider stating and proving the other things
     described briefly in this chapter at the end. *)
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

  (* axiom_2_9_3 *)
  Theorem funext_equiv {A : UU} {B : A -> UU} {f g : ∏ x:A, B x}
    : (f = g) ≃ ∏ x:A, f x = g x.
  Proof. exact { happly ;
                 (equiv_from_qinv (funext_qinv A B f g)) }. Defined.

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

  (* eqn_2_9_4 *)
  Lemma transport_f {X : UU} {x1 x2 : X} (A B : X -> UU)
        (p : x1=x2) (f : A x1 -> B x1)
    : transport (A -> B)%fiber p f
      =
      λ x, transport B p (f (transport A (inv p) x)).
  Proof. destruct p; reflexivity. Defined.

  (* I don't really know how to think about the type of B
     here, but it's really important for the dependent function
     transport lemma... *)
  Definition pi_fiber {X:UU} (A : X -> UU) (B : ∏ x:X, A x -> UU)
    : fibration X
    := λ x, ∏ a : A x, B x a.
  Definition hat_fiber {X:UU} {A : X -> UU} (B : ∏ x:X, A x -> UU)
    : fibration (total A)
    := λ w, B w.1 w.2 .

  (* eqn_2_9_5 *)
  Lemma transport_d {X : UU} {x1 x2 : X}
        (A : X -> UU) (B : ∏ x:X, A x -> UU)
        (p : x1=x2) (f : pi_fiber A B x1) (a : A x2)
    : transport (pi_fiber A B) p f a
      =
      transport (hat_fiber B) (inv (lift a (inv p))) (f ((inv p)#a)).
  Proof. induction p; reflexivity. Defined.
  
  (* In pre2.v these lemmas are given proper names *)
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
            ((@transport_twice _ A _ _ _ _ _ _)
               ∙ (happly (ap (transport A) (path_inverse_r p)) a)
               ∙ idpath
            )
        ))
      ∙ ((lem_2_9_6 q) a).
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

  Definition ua_compute_transport {A B : UU} {e : A ≃ B}
    : transport idfun (ua e) = e
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

  (* lem_2_10_5 *)
  Lemma transport_as_idtoeqv  {A : UU} {B : A -> UU} {x y : A}
        {p : x=y} (u : B x)
    : transport B p u = (idtoeqv (ap B p)) u.
  Proof. apply @transport_apeq with (P := idfun) (f := B). Defined.
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
  (* note that this proof was written before I developed the 'chain'
     tactic earlier.  Can you clean it up some with that? *)
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
  Lemma transport_eq_both {A : UU} {x1 x2 : A} (p : x1=x2) (q : x1 = x1)
    : transport (λ x, x = x) p q = (inv p) ∙ q ∙ p.
  Proof. destruct p; autorewrite with PathGroupoid; reflexivity. Defined.

  (* these results are given proper names in pre2.v *)
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
           rewrite <- (transport_apeq inl); unfold funcomp; simpl;
             rewrite transport_eq_r; reflexivity. Defined.

  Lemma deencode_coprod_r {A B : UU} (b0 : B) (x : A + B) (p : inr b0 = x)
    : decode_coprod_r b0 x (encode_coprod_r b0 x p) = p.
  Proof. destruct p; reflexivity. Defined.
  Lemma endecode_coprod_r {A B : UU} (b0 : B) (x : A + B)
        (c : code_coprod_r b0 x)
    : encode_coprod_r b0 x (decode_coprod_r b0 x c) = c.
  Proof. destruct x; try contradiction; simpl in c; simpl;
           unfold encode_coprod_r;
           rewrite <- (transport_apeq inr); unfold funcomp; simpl;
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

  Remark bool_is_unit_plus_unit : 𝟚 ≃ (𝟙 + 𝟙)%type.
  Proof.
    exists (λ b, match b with | false => inl tt | true => inr tt end).
    apply equiv_from_qinv.
    exists (λ c, match c with | inl tt => false | inr tt => true end).
    split; intro x; destruct x; trivial; destruct u; trivial.
  Defined.
  Compute (fst (bool_is_unit_plus_unit.2)).1.

  Remark true_is_not_false : true ≠ false.
  Proof.
    intro e; apply (ap bool_is_unit_plus_unit) in e; simpl in e.
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
         unfold encode_nat; rewrite <- (transport_apeq S);
           unfold funcomp; simpl.
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
    ∏ x y z : A, m x (m y z) = m (m x y) z.
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
    apply (proj1eq (transport_sig Binop (λ Xm, Assoc Xm.2) p {m;a}) ).
  Defined.
  Lemma induced_assoc_from_equiv {A B : UU} (p : A=B)
        (m : Binop A) (a : Assoc m)
    : transport Assoc (induced_mult_from_equiv p m a)
                (transport SemigroupStr p { m ; a }).2
      = induced_assoc p m a.
  Proof.
    apply (proj2eq (transport_sig Binop (λ Xm, Assoc Xm.2) p {m;a}) ).
  Defined.

  Lemma explicit_induced_mult {A B : UU} (e : A≃B) (m : A->A->A)
        (b1 b2 : B)
    : (induced_mult (ua e) m) b1 b2
      = e (m ((equiv_symm e) b1) ((equiv_symm e) b2)).
  Proof. unfold induced_mult, Binop.
         repeat rewrite transport_f.
         repeat rewrite ua_symm.
         repeat rewrite ua_compute_transport.
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

  (* The following theorem is left to the reader, but is proved
     below so that the file may be used as is. *)
  (*
  Theorem univ_prod {X : UU} {A B : X -> UU}
    : (∏ x:X, (A x) × (B x)) ≃ (∏ x:X, A x) × (∏ x:X, B x).
  Proof.
    (* Left to the reader *)
  Defined.
   *)

  (* the previous axiom of choice result shown is non-dependent,
     and *)
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

  (* The following is left to the reader, but is proved below so
     that the file may be used as is *)
  (*
  Theorem univ_prod_rect {A B : UU} {C : A×B -> UU}
    : (∏ w:A×B, C w) ≃ (∏ x:A, ∏ y:B, C(x,y) ).
  Proof. (* fill in here... *)
  Defined.
  Theorem univ_sig_rect {A : UU} {B : A -> UU} {C : (Σ x:A, B x) -> UU}
    : (∏ w:(Σ x:A, B x), C w) ≃ (∏ x:A, ∏ y:B x, C{x;y} ).
  Proof. (* fill in here... *)
  Defined.
  Theorem univ_paths_rect {A : UU} {a : A} (B : ∏ x:A, a=x -> UU)
    : (∏ (x:A) (p:a=x), B x p) ≃ B a (idpath a).
  Proof. (* fill in here... *)
  Defined.
   *)



  
  (* non-reader derived proofs *)

  Theorem univ_prod {X : UU} {A B : X -> UU}
    : (∏ x:X, (A x) × (B x)) ≃ (∏ x:X, A x) × (∏ x:X, B x).
  Proof.
    exists (λ f, (fstd f, sndd f)).
    apply equiv_from_qinv.
    exists (λ gh x,  ((fst gh) x, (snd gh) x)).
    split; intro; unfold fstd, sndd, funcomp; simpl.
    - eta_reduce; rewrite prod_uniq; trivial.
    - apply funext; intro; rewrite prod_uniq; trivial.
  Defined.

  Theorem univ_prod_rect {A B : UU} {C : A×B -> UU}
    : (∏ w:A×B, C w) ≃ (∏ x:A, ∏ y:B, C(x,y) ).
  Proof.
    pose (eval (f: ∏ w:A×B, C w) (x:A) (y:B) := f (x,y)).
    exists eval.
    apply equiv_from_qinv.
    exists (@prod_rect A B C).
    unfold funcomp, eval, prod_rect; split; intro f; simpl; trivial.
    apply funext; intros (x,y); trivial.
  Defined.
  Theorem univ_sig_rect {A : UU} {B : A -> UU} {C : (Σ x:A, B x) -> UU}
    : (∏ w:(Σ x:A, B x), C w) ≃ (∏ x:A, ∏ y:B x, C{x;y} ).
  Proof.
    pose (eval (f: ∏ w:(Σ x:A, B x), C w) (x:A) (y:B x) := f {x;y}).
    exists eval.
    apply equiv_from_qinv.
    exists (@sig_rect A B C).
    split; intro f; trivial.
  Defined.
  Theorem univ_paths_rect {A : UU} {a : A} (B : ∏ x:A, a=x -> UU)
    : (∏ (x:A) (p:a=x), B x p) ≃ B a (idpath a).
  Proof.
    pose (eval (f : ∏ (x:A) (p:a=x), B x p) := f a (idpath a) ).
    exists eval.
    apply equiv_from_qinv.
    exists (@paths_rect A a B).
    unfold funcomp, eval; split;
      [ intro
      | intro f; apply funext; intro x;
        apply funext; intro p; destruct p
      ]; trivial.
  Defined.

End Universal_Properties.

