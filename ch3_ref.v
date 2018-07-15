
Require Import pre2.


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
  Lemma sets_are_1types (A : UU) : isSet A -> is1Type A.
  Proof.
    intros sA x y p q r s;
      set (g := sA x y p);
      apply (cancel_whisker_l (g p));
      chain (r # (g p)) by symmetry; apply transport_eq_r.
        chain (g q) by apply apd.
        chain (s # (g p)) by symmetry; apply apd.
          apply transport_eq_r.
  Defined.

  Remark negb_eqv : 𝟚 ≃ 𝟚.
  Proof.
    exists negb; apply equiv_from_qinv; exists negb;
      split; intros [|]; trivial.
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
  Defined.
End Sets_and_n_Types.

Section Propositions_as_Types_or_not.



End Propositions_as_Types_or_not.


