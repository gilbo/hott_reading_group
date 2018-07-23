
Load "ch3_ref".



(* Chapter 3 Exercises *)
Section Chapter_3_Exercises.

  (* Exercise 3.1 *)
  Lemma equiv_of_sets {A B : UU}
        (e : A ≃ B)
        (isA : isSet A)
  : isSet B.
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.2 *)
  Lemma coprod_isSet {A B : UU}
        (isA : isSet A) (isB : isSet B)
    : isSet (A+B)%type.
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.3 *)
  Lemma sig_isSet_exercise {A : UU} {B : A -> UU}
        (isA : isSet A) (isB : ∏ x:A, isSet (B x))
    : isSet (total B).
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.4 *)
  Lemma isProp_iff_automorphisms_isContr (A : UU)
    : (isProp A) <-> (isContr (A -> A)).
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.5 *)
  Lemma isProp_equiv_inhabited_implies_isContr (A : UU)
    : (isProp A) ≃ (A -> isContr A).
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.6. *)
  Lemma coprod_decision_isProp {A : UU}
    : (isProp A) -> (A + ¬A).
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.7 *)
  Lemma coprod_disjoint_isProp {A B : UU}
        (isA : isProp A) (isB : isProp B)
    : ¬(A×B) -> isProp (A + B)%type.
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.8 *)
  Lemma trunc_qinv_is_an_equivalence {A B : UU} (f : A -> B)
        (Eqv_f : UU) (* some equivalence type satisfying... *)
        (from_qinv : (qinv f) -> Eqv_f)
        (to_qinv   : Eqv_f -> (qinv f))
        (is        : isProp Eqv_f)
    : Σ (qfrom     : (qinv f) -> ∥ qinv f ∥)
        (qto       : ∥ qinv f ∥ -> (qinv f))
        (qis       : isProp (∥ qinv f ∥)),
      (Eqv_f ≃ ∥ qinv f ∥).
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.9 *)
  Lemma Props_are_true_or_false_assuming_LEM 
        (LEM : LEM_Statement)
    : UProp ≃ 𝟚.
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.10 *)
  (* work on paper because it involves universes *)

  (* Exercise 3.11 *)
  Lemma truncation_cannot_always_be_removed
    : ¬(∏ A:UU, ∥A∥ -> A).
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.12 *)
  Lemma truncated_truncation_removal_if_LEM {A : UU}
        (LEM : LEM_Statement)
    : ∥ (∥A∥ -> A) ∥.
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.13 *)
  (* NOTE: you need to avoid using Univalence in this proof *)
  (* Check whether some other result relies on univalence as follows: *)
  Print Assumptions bool_isSet.
  (* note how ua occurs in the assumption set *)
  (* next, note what happens if we use this result in another result... *)
  Lemma booleqv_isSet : isSet (𝟚 ≃ 𝟚).
  Proof. apply equiv_isSet; apply bool_isSet. Defined.
  Print Assumptions booleqv_isSet.
  (* and sure enough, there's ua and company again... *)
  Print ua. (* we can see it's defined in terms of idtoeqv_isequiv *)
  Print idtoeqv_isequiv. (* this is the root axiom we used *)
  Lemma naive_LEM_implies_AC
    : (∏ A:UU, A + ¬A) -> Axiom_of_Choice_statement.
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.14 *)
  (* Think about how to state and prove these results
     inside of Coq... *)
  (* fill in here... *)

  (* Exercise 3.15 *)
  (* maybe do this on paper.  We ruined it a bit by doing it
     in the chapter development to get some encoding *)
  (* However, the definition relies on propositional resizing rules.
     Can you ensure those are sound in this approach?  Is the specific
     definition encoded in the chapter 3 reference sound? *)
  
  (* Exercise 3.16 *)
  Lemma double_not_commutes_with_pi_over_sets_assuming_LEM
        {A : UU} {P : A -> UU}
        (isA : isSet A) (isP : ∏ x:A, isProp (P x))
        (LEM : LEM_Statement)
  : (∏ x:A, ¬¬(P x)) ≃ (¬¬∏ x:A, P x).
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.17 *)
  Lemma prop_rect (A : UU) (B : ∥A∥ -> UU)
        (BP : ∏ a:∥A∥, isProp (B a))
        (inB : ∏ a:A, B (elemP a))
    : ∏ a:∥A∥, B a.
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.18 *)
  Lemma LEM_equiv_Double_Negation
    : LEM_Statement <-> Law_of_Double_Negation_Statement.
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.19 *)
  Lemma Untruncate_Decidable_Nat_Indexed_Propositions
        (P : ℕ -> UU)
        (isP : ∏ n:ℕ, isProp (P n))
        (isD : DecidableFibration P)
    : ∥ Σ n:ℕ, P n ∥ -> Σ n:ℕ, P n.
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.20 *)
  Lemma contr_sigbase {A : UU} {P : A -> UU}
        (isC : isContr A)
    : (Σ x:A, P x) ≃ P isC.1 .
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.21 *)
  Lemma isProp_equiv_P_equiv_Ptrunc (P : UU) : (isProp P) ≃ (P ≃ ∥P∥).
  Proof. (* fill in here... *)
  Admitted.

  (* Exercise 3.22 *)
  (* still haven't worked out how to encode Fin ... *)

  (* Exercise 3.23 *)
  Lemma Untruncate_Decidable_Nat_Indexed_Fibration
        (P : ℕ -> UU)
        (isD : DecidableFibration P)
    : ∥ Σ n:ℕ, P n ∥ -> Σ n:ℕ, P n.
  Proof. (* fill in here... *)
  Admitted.

End Chapter_3_Exercises.




