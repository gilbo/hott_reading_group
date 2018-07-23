
Require Import pre2.


(* while it ought to be evident, we've neglected to state
   this fact as an object which may be referred to. *)
Remark negb_eqv : 𝟚 ≃ 𝟚.
Proof.
  exists negb; apply equiv_from_qinv; exists negb;
    split; intros [|]; trivial.
Defined.


Section Sets_and_n_Types.

  (* def_3_1_1 *)
  Definition isSet (A : UU) := ∏ (x y : A) (p q : x=y), p=q.

  (* example_3_1_2 *)
  Example unit_isSet_using_ua : isSet 𝟙.
  Proof. intros x y;
           rewrite (ua uniteq_is_unit); apply uniteq. Defined.

  (* note that the above proof uses the univalence axiom to
     do the rewrite.  Can we work around that?  Not that we
     need to, but it's an interesting challenge. *)
  Example unit_isSet : isSet 𝟙.
  Proof.
    intros x y p q.
    set (E := uniteq (uniteq_is_unit.1 p) (uniteq_is_unit.1 q)).
    set (Ladj := snd (@uniteq_is_unit x y).2 ).
    apply (inv (Ladj.2 p) ∙ ap Ladj.1 E ∙ Ladj.2 q).
  Defined.
  (* so, yes. We can use the computation/uniqueness rule of
     the eqiuvalence to reach the same end, although we have to
     plan the proof a little more deliberately rather than
     pointing at some part of the goal and saying "I want that to
     be this other thing seemingly magically." *)

  (* example_3_1_3 *)
  Example empty_isSet : isSet 𝟘.
  Proof. intros x y; apply empty_rect; exact x. Defined.

  (* example_3_1_4 *)
  Example nat_isSet : isSet ℕ.
  Proof. intro n; induction n; intro m; induction m;
           rewrite (ua (nat_eqvcoding _ _));
           try apply uniteq; 
           try (intros p q; apply empty_rect; assumption);
           simpl; rewrite <- (ua (nat_eqvcoding _ _)); apply IHn.
  Defined.

  (* example_3_1_5 *)
  Example prod_isSet {A B : UU} : isSet A -> isSet B -> isSet (A×B).
  Proof.
    intros sA sB x y p q; destruct x as (xa,xb); destruct y as (ya,yb);
      rewrite <- (prodeq_uniq p); rewrite <- (prodeq_uniq q);
        apply ap2; [apply sA | apply sB].
  Defined.

  (* WARNING: skip the following, or just go to the exercises
     and do the corresponding exercise first *)
  Example sig_isSet {A : UU} {B : A -> UU}
    : isSet A -> (∏ x:A, isSet (B x)) -> isSet (total B).
  Proof.
    intros sA sB x y p q; destruct x as (xa,xb); destruct y as (ya,yb);
      rewrite <- (sigeq_uniq p); rewrite <- (sigeq_uniq q);
        set (baseeq := sA _ _ (proj1eq p) (proj1eq q));
        set (fibereq := sB ya _ _
                           ( transport (λ pp, transport _ pp _ = _)
                                       baseeq (proj2eq p) )
                           (proj2eq q)
            );
        apply (ap (siguncurry spaireq) (spaireq baseeq fibereq)).
  Defined.

  (* example_3_1_6 *)
  Example fun_isSet {A : UU} {B : A -> UU}
    : (∏ x:A, isSet (B x)) -> isSet (section B).
  Proof.
    intros sB f g p q;
      rewrite (funext_uniq q); rewrite (funext_uniq p);
        apply ap; apply funext; intro x; apply sB.
  Defined.

  (* def_3_1_7 *)
  Definition is1Type (A : UU) :=
    ∏ (x y : A) (p q : x=y) (r s : p=q), r=s.

  (* lem_3_1_8 *)
  Lemma sets_are_1types {A : UU} : isSet A -> is1Type A.
  Proof.
    intros sA x y p q r s;
      set (g := sA x y p);
      apply (cancel_whisker_l (g p));
      chain (r # (g p)) by symmetry; apply transport_eq_r.
        chain (g q) by apply apd.
        chain (s # (g p)) by symmetry; apply apd.
          apply transport_eq_r.
  Defined.

  (* example_3_1_9 *)
  Example UU_is_not_a_set : ¬ (isSet UU).
  Proof.
    intro sUU.
    set (badeq := sUU 𝟚 𝟚 (ua negb_eqv) idpath).
    set (badeq2 := happly (ap (transport idfun) badeq) false).
    rewrite ua_compute_transport in badeq2.
    simpl in badeq2.
    apply true_is_not_false; assumption.
  Qed.
End Sets_and_n_Types.


Section Propositions_as_Types_or_not.
  (* thm_3_2_2 *)
  Theorem general_double_negation_elim_not_admissable
  : ¬ ∏ A:UU, ¬¬A -> A.
  Proof.
    intro f;
      set (p := ua negb_eqv);
      set (u := (λ n, n true):¬¬𝟚);
      set (q := happly (apd f p) u);
      rewrite (transport_f (λ X, ¬¬X)) in q.
    assert (∏ u' v:¬¬𝟚, u' = v) as negProp.
    { intros u' v; apply funext; intro x; apply empty_rect. }
    assert (transport' (λ X, ¬¬X) p = idfun) as q2.
    { apply funext; intro; apply negProp. }
    rewrite q2 in q; simpl in q; unfold p in q;
      rewrite ua_compute_transport in q.
    assert (∏ x:𝟚, negb_eqv.1 x ≠ x) as noFix.
    { intros x; destruct x; simpl; intro badEq;
        [symmetry in badEq|]; apply (true_is_not_false badEq). }
    apply (noFix (f 𝟚 u) q).
  Qed.

  (* cor_3_2_7 *)
  Theorem general_LEM_not_admissable : ¬ ∏ A:UU, A + ¬A.
  Proof.
    intro g;
      apply general_double_negation_elim_not_admissable.
    intros A u;
      destruct (g A) as [a|na];
      [ assumption | apply empty_rect; apply (u na) ].
  Qed.
End Propositions_as_Types_or_not.


Section Mere_Propositions.
  (* def_3_3_1 *)
  Definition isProp (A : UU) := ∏ x y : A, x = y.

  (* note we already proved this for 𝟙 under a different name *)
  Check uniteq : isProp 𝟙.
  Definition unit_isProp : isProp 𝟙 := uniteq.

  (* lem_3_3_2 *)
  (* lem_3_3_3 *)
  Lemma prop_eqv {P Q : UU}
        (p : isProp P) (q : isProp Q)
        (f : P -> Q) (g : Q -> P)
    : P ≃ Q.
  Proof.
    exists f; apply equiv_from_qinv; exists g;
      split; intro x; try apply p; try apply q.
  Defined.
  Corollary prop_is_unit {P : UU}
            (p : isProp P) (x : P)
    : P ≃ 𝟙.
  Proof.
    exact (prop_eqv p
                    unit_isProp
                    (λ _, tt)
                    (λ _, x)).
  Defined.

  (* lem_3_3_4 *)
  Lemma props_are_sets {A : UU} : isProp A -> isSet A.
  Proof.    
    intros pA x y p q;
      set (g := pA x);
      apply (cancel_whisker_l (g x));
      chain (p # (g x)) by symmetry; apply transport_eq_r.
    chain (g y) by apply apd.
    chain (q # (g x)) by symmetry; apply apd.
    apply transport_eq_r.
  Defined.

  (* lem_3_3_5 *)
  Lemma isProp_isProp {A : UU} : isProp (isProp A).
  Proof.
    intros f g.
    apply funext; intro x; apply funext; intro y.
    apply (props_are_sets f).
  Defined.
  Lemma isSet_isProp {A : UU} : isProp (isSet A).
  Proof.
    intros f g.
    apply funext; intro x; apply funext; intro y;
      apply funext; intro p; apply funext; intro q.
    apply (sets_are_1types f).
  Defined.
End Mere_Propositions.


Section Classical_vs_Intuitionistic_Logic.
  Definition LEM_Statement
    := ∏ A:UU, isProp A -> (A + ¬A).
  Definition Law_of_Double_Negation_Statement
    := ∏ A:UU, isProp A -> (¬¬A -> A).

  Definition Decidable (A : UU) := (A + ¬A)%type.
  Definition DecidableFibration {A : UU} (B : A -> UU)
    := ∏ x:A, Decidable (B x).
  Definition DecidableEq (A : UU) := ∏ a b : A, Decidable (a=b).
End Classical_vs_Intuitionistic_Logic.


Section Subsets_and_Propositional_Resizing.
  (* lem_3_5_1 *)
  Lemma subseteq {A : UU} (P : A -> UU)
        (Pprop : ∏ x:A, isProp (P x))
        (u v : total P)
  : u.1 = v.1 -> u = v.
  Proof.
    intro p.
    apply (spaireq p).
    apply (Pprop v.1).
  Defined.

  (* the following two definitions, like "PointedType" rely on
     some funny business about treating universes kind of like
     other normal types.  This is allowed, because of the type-in-type
     unsafe mode that we're working in, but is worth noting *)
  Definition USet := Σ A:UU, isSet A.
  Definition UProp := Σ A:UU, isProp A.
  (* note that because of the above Lemma, we expect the second
     half of these universe restrictions to be mere propositions,
     and hence these are simply sub-universes *)
  (* In UniMath, the above UProp definition is called hProp *)

  (* typed constructors not needed... but maybe nice *)
  Definition to_USet (A : UU) (SA : isSet A) : USet := {A;SA}.
  Definition to_UProp (A : UU) (PA : isProp A) : UProp := {A;PA}.
  (* these projection aliases are critical for below... *)
  Definition USet_to_UU : USet -> UU := @proj1 _ _ .
  Definition UProp_to_UU : UProp -> UU := @proj1 _ _ .
  Definition to_isSet (A : USet) := A.2 .
  Definition to_isProp (A : UProp) := A.2 .

  (* we don't state propositional resizing here because we're
     ignoring the issue of explicit universe management in the way
     in which we're encoding Homotopy Type Theory in Coq. *)
  (* specifically, the type-in-type flag seems to obviate this problem *)
End Subsets_and_Propositional_Resizing.

(* UniMath also cleverly defines a coercion that forgets
   the trailing classifier when needed *)
Coercion USet_to_UU : USet >-> UU.
Coercion UProp_to_UU : UProp >-> UU.


Section The_Logic_of_Mere_Propositions.
  (* example_3_6_1 *)
  Example prod_isProp (A B : UU) (PA : isProp A) (PB : isProp B)
  : isProp (A×B).
  Proof.
    intros x y; destruct x as (a,b); destruct y as (a',b');
      apply paireq; [ apply PA | apply PB ].
  Defined.

  (* example_3_6_2 *)
  Example fun_isProp {A : UU} {B : A -> UU}
          (BP : ∏ x:A, isProp (B x))
    : isProp (section B).
  Proof.
    intros f g; apply funext; intro x; apply (BP x).
  Defined.

  Remark empty_isProp : isProp 𝟘.
  Proof. intros x y; induction x. Defined.
  Corollary not_isProp {A : UU} : isProp (¬A).
  Proof. apply fun_isProp; intro; apply empty_isProp. Defined.

  Remark bool_not_isProp : ¬ isProp 𝟚.
  Proof. intro P2; exact (true_is_not_false (P2 true false)). Defined.
End The_Logic_of_Mere_Propositions.


Section Propositional_Truncation.
  (* truncation encoding is... tricky.
     The following is taken from UniMath.Foundations.Propositions
   *)
  (* the basis for it is to figure out how to encode the type
        "the type A is inhabited."
     which is the basis for one of the exercises. *)
  Definition PropTrunc (A : UU) := ∏ P:UProp, (A -> P) -> P.
  (* if we just wanted to model inhabitedness, couldn't we just say
       "If we have an element a:A, then ..."
     Maybe we could take off some of these needless arrows to P.
     For example, maybe we could say ∏ P:UProp, A -> P, which
     would mean that for any proposition, we can show the proposition
     is inhabited given an element of A.  But note that ∅ is a
     proposition.  So, it would seem that all this would just say
     that A better NOT! be inhabited.
       This suggests that the pattern places P in exactly the
     spot for defining ¬¬A = (A->∅)->∅.  And we know informally
     that ¬¬ should give an embedding of classical logic into
     constructive, dependent type theory.  So, this seems to be
     generalizing the definition of double negation to both ∅ and 𝟙.
   *)
  (* The following Lemma probably uses some funny
     type-in-type business by pushing things up into UU.
     Apparently it relies on propositional resizing, so that's not
     too surprising overall. *)
  Lemma PropTrunc_isProp (A : UU) : isProp (PropTrunc A).
  Proof.
    intros f g. apply funext; intro P; apply funext; intro AP.
    apply P.2.
  Defined.

  Definition UPropTrunc (A : UU) : UProp :=
    to_UProp (PropTrunc A) (PropTrunc_isProp A).
  Opaque UPropTrunc. (* don't go peeking in this! *)
  Notation "∥ A ∥" := (UPropTrunc A) (at level 20) : type_scope.
  (* to input : \|| *)

  Definition elemP {A : UU} : A -> ∥ A ∥
    := λ (a:A) (P:UProp) (f:A->P), f a.
  Opaque elemP.
  (* recall (λ a, λ na, na a) : A -> ¬¬A *)

  (* note that in the text, it says we need two constructors for
     ∥A∥, `elemP` as above, and `∏ x y : ∥A∥, x=y`.  But because
     we've defiend `UPropTrunc` as a UProp, which carries that proof
     along with the underlying type, we can simply get
       ∥A∥.2 : ∏ x y : ∥A∥.1, x=y
   *)

  (* again, we exploit the strange properties of our specific
     truncation encoding to get us this definitional result *)
  Definition trunc_rec {A : UU} {B : UU} (isB : isProp B) (f : A -> B)
    : ∥A∥ -> B
    := λ truncA, truncA {B;isB} f.

  (* show some more support functions for definitions below *)

  (* unfortunately, I don't quite know what the right machinery
     is to remove this cruft yet... *)
  Lemma sig_of_props {P : UU} {Q : P -> UU}
        (isP : isProp P) (isQ : ∏ p:P, isProp (Q p))
    : isProp (total Q).
  Proof.
    intros (xp,xq) (yp,yq).
    apply (spaireq (isP xp yp)).
    apply (isQ yp).
  Defined.
  Lemma eqv_isProp (P Q : UU) (isP : isProp P) (isQ : isProp Q)
    : isProp (P≃Q).
  Proof.
    set (isHP (f g : P->P) (h0 h1 : f ~ g) :=
           funext (λ x:P, props_are_sets isP (f x) (g x) (h0 x) (h1 x) )).
    set (isHQ (f g : Q->Q) (h0 h1 : f ~ g) :=
           funext (λ x:Q, props_are_sets isQ (f x) (g x) (h0 x) (h1 x) )).
    set (isPQ := fun_isProp (λ _:P, isQ) : isProp (P->Q)).
    set (isQP := fun_isProp (λ _:Q, isP) : isProp (Q->P)).
    set (isEqvProp (f:P->Q) :=
           prod_isProp _ _
                       (sig_of_props isQP (λ fR, isHQ (f ∘ fR) idfun))
                       (sig_of_props isQP (λ fL, isHP (fL ∘ f) idfun)) ).
    apply (sig_of_props isPQ isEqvProp).
  Defined.

  Corollary paths_isProp {A B : UU} (isA : isProp A) (isB : isProp B)
    : isProp (A=B).
  Proof.
    (* use a big hammer and switch it out *)
    rewrite (ua Univalence).
    apply eqv_isProp; assumption.
  Defined.

  Definition unit_to_UProp : UProp := {𝟙;unit_isProp}.
  Definition empty_to_UProp : UProp := {∅;empty_isProp}.
  Definition prod_to_UProp (A B : UProp) : UProp
    := { A × B ; prod_isProp A B A.2 B.2 }.
  Definition simple_fun_to_UProp (A : UU) (B : UProp) : UProp
    := { A -> B ; fun_isProp (λ _:A, B.2) }.
  Definition equiv_to_UProp (A B : UProp) : UProp
    := { A.1 = B.1 ; paths_isProp A.2 B.2 }.
  Definition not_to_UProp (A : UU) : UProp
    := { ¬A ; @not_isProp A }.
  Definition coprod_to_UProp (A B : UProp) : UProp
    := ∥ A.1 + B.1 ∥%type.
  Definition pi_to_UProp (A : UU) (B : A -> UProp) : UProp
    := { ∏ a:A, (B a).1 ; fun_isProp (proj2∘B) }.
  Definition sig_to_UProp (A : UU) (B : A -> UProp) : UProp
    := ∥ Σ a:A, (B a).1 ∥ .

End Propositional_Truncation.

Notation "∥ A ∥" := (UPropTrunc A) (at level 20) : type_scope.
(* to input : \|| *)

Notation "A <-> B" := ((A -> B) × (B -> A)) : type_scope.

(* notational conventions for logic... *)
Notation "⊤" := (unit_to_UProp) : logic_scope.
(* input: \top *)
Notation "⊥" := (empty_to_UProp) : logic_scope.
Notation "P /\ Q" := (prod_to_UProp P Q) : logic_scope.
Notation "P => Q" := (simple_fun_to_UProp P Q)
                       (at level 99, Q at level 200, right associativity)
                     : logic_scope.
Notation "P <=> Q" := (equiv_to_UProp P Q)
                        (at level 95) : logic_scope.
(* overloaded in logic_scope *)
Notation "'¬' X" := (not_to_UProp X) (at level 75, right associativity)
                    : logic_scope.
Notation "P \/ Q" := (coprod_to_UProp P Q) : logic_scope.
Notation "'∀' x .. y , P" :=
  (pi_to_UProp _ (fun x => .. (pi_to_UProp _ (fun y => P)) ..))
    (at level 200, x binder, y binder, right associativity) : logic_scope.
Notation "'∃' x .. y , P" :=
  (sig_to_UProp _ (fun x => .. (sig_to_UProp _ (fun y => P)) ..))
    (at level 200, x binder, y binder, right associativity) : logic_scope.

Delimit Scope logic_scope with logic.


Section The_Axiom_of_Choice.
  (* def_3_8_1 *)
  Definition Axiom_of_Choice_statement
    := ∏ (X : UU) (A : X -> UU) (P : ∏ x:X, A x -> UU)
         (isX : isSet X) (isA : ∏ x:X, isSet (A x))
         (isP : ∏ (x:X) (a:A x), isProp (P x a)),
       ( ∏ x:X, ∥ Σ a : A x, P x a ∥ ) ->
       ∥ Σ (g : ∏ x:X, A x), ∏ (x:X), P x (g x) ∥ .

  Remark Axiom_of_Choice_isProp
    : isProp Axiom_of_Choice_statement.
  Proof.
    (* this follows trivially from fun_isProp, but we
       have to crunch through the proof a bit to get that result *)
    unfold Axiom_of_Choice_statement.
    apply fun_isProp; intro X;
      apply fun_isProp; intro A;
        apply fun_isProp; intro P;
          do 4 (apply fun_isProp; intro).
    apply (∥ Σ (g : ∏ x:X, A x), ∏ (x:X), P x (g x) ∥.2).
  Qed.

  Definition Fam_of_Sets_Axiom_statement
    := ∏ (X : UU) (Y : X -> UU)
         (isX : isSet X) (isY : ∏ x:X, isSet (Y x)),
       (∏ x:X, ∥ Y x ∥) -> ∥ ∏ x:X, Y x ∥ .

  Remark Fam_of_Sets_Axiom_isProp
    : isProp Fam_of_Sets_Axiom_statement.
  Proof.
    unfold Fam_of_Sets_Axiom_statement.
    apply fun_isProp; intro X;
      apply fun_isProp; intro Y;
        do 3 (apply fun_isProp; intro).
    apply (∥ ∏ x : X, Y x ∥.2).
  Qed.

  Definition trunc_fun {A B : UU} (f : A -> B) : ∥ A ∥ -> ∥ B ∥
    := trunc_rec (∥B∥).2 (λ a:A, (elemP (f a))).

  (* lem_3_8_2 *)
  Lemma AC_equivalent_to_Fam_of_Sets
    : Axiom_of_Choice_statement ≃ Fam_of_Sets_Axiom_statement.
  Proof.
    apply (prop_eqv Axiom_of_Choice_isProp Fam_of_Sets_Axiom_isProp);
      unfold Axiom_of_Choice_statement, Fam_of_Sets_Axiom_statement.
    - intros AC X Y isX isY Hfam.
      apply (@trunc_fun (Σ _:(∏ x:X, Y x), X->𝟙)).
      (* discharge trunc_fun *) intro g; apply g.1.
      apply (AC X Y (λ _ _, 𝟙) isX isY (λ _ _, unit_isProp)).
      intro x.
      apply (trunc_fun (λ y:Y x, {y;tt}) (Hfam x)).
    - intros FAM X A P isX isA isP Hac.
      apply (trunc_fun univ_sig).
      set (Y x := total (P x)).
      set (isY x := sig_isSet (isA x) (λ a, props_are_sets (isP x a))).
      apply (FAM X Y isX isY Hac).
  Qed.

  (* remark_3_8_4 *)
  (* this is true without any axioms *)
  Remark inv_Fam_of_Sets {X : UU} {Y : X -> UU}
         (isX : isSet X) (isY : ∏ x:X, isSet (Y x))
    : ∥ ∏ x:X, Y x ∥ -> ∏ x:X, ∥ Y x ∥ .
  Proof.
    intros exFam x.
    apply (trunc_fun (λ f, f x) exFam).
  Qed.

  Remark bool_isSet : isSet 𝟚.
  Proof.
    refine (ua bool_is_unit_plus_unit #' _);
    intros x y; destruct x as [()|()];
      [ rewrite (ua (coprod_l_eqvcoding tt y))
      | rewrite (ua (coprod_r_eqvcoding tt y))
      ]; destruct y as [()|()]; simpl;
        [ apply unit_isSet | apply empty_isProp
          | apply empty_isProp | apply unit_isSet ].
  Qed.

  Remark equiv_isSet {A B : UU} (isA : isSet A) (isB : isSet B)
    : isSet (A≃B).
  Proof.
    apply (sig_isSet (fun_isSet (λ a, isB)));
      intro f; apply prod_isSet;
        apply (sig_isSet (fun_isSet (λ b, isA)));
        intro g; apply fun_isSet; intro x; unfold isSet;
          [ apply (sets_are_1types isB)
          | apply (sets_are_1types isA) ].
  Qed.
  Corollary paths_isSet {A B : UU} (isA : isSet A) (isB : isSet B)
    : isSet (A=B).
  Proof. rewrite (ua Univalence); apply equiv_isSet; assumption. Qed.
    
  (* lem_3_8_5 *)
  (* impossibility of relaxing part of the Axiom of Choice *)
  (* I am misunderstanding some machinery at my disposal...? *)
  Lemma Fam_of_Sets_must_be_set_indexed
    : Σ (X : UU) (Y : X -> UU) (isY : ∏ x:X, isSet (Y x)),
      ¬( (∏ x:X, ∥ Y x ∥) -> ∥ ∏ x:X, Y x ∥ ).
  Proof.
    set (P (A:UU) := ∥ 𝟚 = A ∥.1).
    set (PisProp (A:UU) := ∥ 𝟚 = A ∥.2); simpl in PisProp.
    set (X := Σ A:UU, ∥ 𝟚 = A ∥); exists X.
    set (p2 := elemP (idpath 𝟚)).
    set (x0 := { 𝟚 ; p2 } : X).
    assert (¬(isSet X)) as X_is_not_a_set.
    { (* well, assume X is... *) intro isX.
      set (negb_path :=
             spaireq (P:=P) (ua negb_eqv)
                     (PisProp 𝟚 (ua negb_eqv # p2) p2) : x0 = x0).
      set (badeq := ap (ap proj1) (isX x0 x0 negb_path idpath));
        change (ap proj1 negb_path) with (proj1eq negb_path) in badeq;
        simpl in badeq; unfold negb_path in badeq;
          rewrite sigeq_compute1 in badeq.
      set (badeq2 := happly (ap (transport idfun) badeq) false).
      rewrite ua_compute_transport in badeq2; simpl in badeq2.
      apply (true_is_not_false badeq2).
    }
    assert (is1Type X) as X_is1Type.
    { intros (A0,p0) (A1,p1).
      set (A_isSet (A:UU) (p : ∥ 𝟚 = A ∥) :=
             trunc_rec isSet_isProp (λ eq, eq # bool_isSet) p).
      set (eq_A12 := paths_isSet (A_isSet A0 p0) (A_isSet A1 p1)).
      
      assert (({A0;p0}={A1;p1} :> X) ≃ (A0=A1)) as exchange.
      {
        exists proj1eq; apply equiv_from_qinv.
        exists (subseteq P PisProp {A0;p0} {A1;p1}).
        unfold funcomp, subseteq; split; intro xeq.
        - apply sigeq_compute1.
        - chain (spaireq (proj1eq xeq) (proj2eq xeq)).
          + apply ap;
            set (A1set := props_are_sets (∥ 𝟚 = A1 ∥).2);
            apply A1set.
          + apply sigeq_uniq.
      }
      rewrite (ua exchange).
      apply eq_A12.
    }

    (* now we define Y finally... *)
    set (Y x := x0 = x).
    set (YisSet x := X_is1Type x0 x : isSet (Y x)).
    exists Y.
    exists YisSet.
    set (all_x_eq_x0 (x:X) :=
           trunc_fun (λ p:𝟚=x.1, subseteq P PisProp x0 x p) x.2).
    intro badHyp.
    refine (trunc_rec empty_isProp _ (badHyp all_x_eq_x0)).
    unfold Y; intro allX0.
    set (XisProp (x y : X) := inv (allX0 x) ∙ allX0 y).
    set (XisSet := props_are_sets XisProp).
    contradiction.
  Qed.
End The_Axiom_of_Choice.


Section The_Principle_of_Unique_Choice.
  (* lem_3_9_1 *)
  Lemma propeqv_trunc {P : UU} (isP : isProp P) : P ≃ ∥P∥.
  Proof.
    apply (prop_eqv isP (∥P∥.2) elemP (trunc_rec isP idfun)).
  Defined.

  (* cor_3_9_2 *)
  Corollary unique_choice {A : UU} {P : A -> UU}
            (isP : ∏ x:A, isProp (P x))
            (inP : ∏ x:A, ∥ P x ∥)
    : ∏ x:A, P x.
  Proof. intro x; apply (propeqv_trunc (isP x)); apply inP. Defined.
End The_Principle_of_Unique_Choice.


Section When_are_Propositions_Truncated.
  (* This section is purely exposition in the book *)
End When_are_Propositions_Truncated.


Section Contractibility.
  (* def_3_11_1 *)
  Definition isContr (A : UU) := Σ (a:A), ∏ (x:A), (a = x).

  (* lem_3_11_3 *)
  Lemma isContr_then_inhabited (A : UU)
    : isContr A -> A.
  Proof. exact (λ c, c.1). Defined.
  Lemma isContr_then_isProp (A : UU)
    : isContr A -> isProp A.
  Proof. exact (λ c, λ x y, inv (c.2 x) ∙ (c.2 y)). Defined.
  Lemma isProp_and_inhabited_then_isContr (A : UU)
    : A -> isProp A -> isContr A.
  Proof. exact (λ a isP, { a ; isP a }). Defined.

  Lemma isProp_and_inhabited_then_eqv_unit (A : UU)
    : A -> isProp A -> A ≃ 𝟙.
  Proof. exact (λ a isP, prop_is_unit isP a). Defined.
  Lemma eqv_unit_then_inhabited (A : UU)
    : A ≃ 𝟙 -> A.
  Proof. exact (λ e, (einv e) tt). Defined.
  Lemma eqv_unit_then_isProp (A : UU)
    : A ≃ 𝟙 -> isProp A.
  Proof. exact (λ e, (ua e) #' unit_isProp). Defined.

  (* lem_3_11_4 *)
  Lemma isContr_isProp (A : UU) : isProp (isContr A).
  Proof.
    intros (a,p) (a',p');
      set (q := p a'); apply (spaireq q);
        set(AisProp := isContr_then_isProp A {a;p}).
    set (paths_props := (fun_isProp (λ x, props_are_sets AisProp a' x)));
      apply paths_props.
  Qed.

  (* cor_3_11_5 *)
  Corollary isContr_isContr {A : UU} : (isContr A) -> isContr (isContr A).
  Proof.
    intros isC;
      apply (isProp_and_inhabited_then_isContr (isContr A)
                                               isC
                                               (isContr_isProp A)).
  Qed.

  (* lem_3_11_6 *)
  Lemma fun_isContr {A : UU} {P : A -> UU}
        (isP : ∏ x:A, isContr (P x))
    : isContr (∏ x:A, P x).
  Proof.
    apply (isProp_and_inhabited_then_isContr (section P)
                                             (λ x, (isP x).1));
      apply fun_isProp; intro x; apply isContr_then_isProp; apply isP.
  Qed.

  Definition isRetract {A B : UU} (r : A->B)
    := Σ (s:B->A), (r ∘ s) ~ idfun .
  Definition Retract (B : UU) (A : UU) := Σ r:A->B, isRetract r.

  (* lem_3_11_7 *)
  Lemma Retract_isContr {A B : UU} (R : Retract B A) (isA : isContr A)
    : isContr B.
  Proof.
    destruct R as (r,(s,ε)); destruct isA as (a,Afam).
    set (b0 := r a); exists b0.
    intros b; apply (ap r (Afam (s b)) ∙ (ε b)).
  Defined.

  (* lem_3_11_8 *)
  Lemma based_paths_isContr (A : UU) (a : A)
    : isContr ( Σ x:A, a=x ).
  Proof.
    set (center := { a ; idpath }); exists center.
    intros (x,p).
    apply (spaireq p).
    apply transport_eq_r.
  Defined.

  (* lem_3_11_9 *)
  Lemma contr_sigfiber {A : UU} {P : A -> UU}
        (isC : ∏ x:A, isContr (P x))
    : (Σ x:A, P x) ≃ A.
  Proof.
    exists proj1; apply equiv_from_qinv;
      exists (λ a:A, { a ; (isC a).1 }).
    unfold funcomp; split; intro x; trivial.
    apply (spaireq idpath); simpl.
    apply (isC x.1).2 .
  Defined.
  (* the following part of the book's Lemma is in the exercises *)
  (*
  Lemma contr_sigbase {A : UU} {P : A -> UU}
        (isC : isContr A)
    : (Σ x:A, P x) ≃ P isC.1 .
   *)

  (* lem_3_11_10 *)
  Lemma prop_paths_isContr {A : UU}
    : (isProp A) ≃ ∏ x y : A, isContr(x=y).
  Proof.
    apply (prop_eqv isProp_isProp
                    (fun_isProp
                       (λ x, fun_isProp
                               (λ y, isContr_isProp (x=y))
          ))); unfold section.
    - intros isA x y; refine { isA x y ; (λ p, _) };
        apply (props_are_sets isA).
    - intros isC x y; exact (isC x y).1.
  Defined.
End Contractibility.

