
Load ch2_ref.

(* Chapter 2 Exercises *)
Section Chapter_2_Exercises.

  (* Exercise 2.1 *)
  (* let's redefine path composition 3 ways for the exercise *)
  Lemma pc1 {A : UU} {x y z : A} (p : x=y) (q : y=z) : x=z.
  Proof. induction p; induction q; reflexivity. Defined.
  Lemma pc2 {A : UU} {x y z : A} (p : x=y) (q : y=z) : x=z.
  Proof. induction p; apply q. Defined.
  Lemma pc3 {A : UU} {x y z : A} (p : x=y) (q : y=z) : x=z.
  Proof. induction q; apply p. Defined.

  Lemma pc1_is_2 {A : UU} {x y z : A} (p : x=y) (q : y=z)
    : pc1 p q = pc2 p q.
  Proof. (* fill in here... *)
    induction p; induction q; reflexivity.
  Defined.
  Lemma pc2_is_3 {A : UU} {x y z : A} (p : x=y) (q : y=z)
    : pc2 p q = pc3 p q.
  Proof. (* fill in here... *)
    induction p; induction q; reflexivity.
  Defined.
  Lemma pc1_is_3 {A : UU} {x y z : A} (p : x=y) (q : y=z)
    : pc1 p q = pc3 p q.
  Proof. (* fill in here... *)
    induction p; induction q; reflexivity.
  Defined.


  (* Exercise 2.2 *)
  Lemma pc_proof_triangle {A : UU} {x y z : A} (p : x=y) (q : y=z)
    : pc1 (pc1_is_2 p q) (pc2_is_3 p q) = pc1_is_3 p q.
  Proof. (* fill in here... *)
    induction p; induction q; reflexivity.
  Defined.


  (* Exercise 2.3 *)
  Lemma pc4 {A : UU} {x y z : A} (p : x=y) (q : y=z) : x=z.
  Proof. (* fill in here... *)
    apply inv.
    apply inv in p.
    apply inv in q.
    apply (pc1 q p).
  Defined.
  Lemma pc4_is_1 {A : UU} {x y z : A} (p : x=y) (q : y=z)
    : pc4 p q = pc1 p q.
  Proof. (* fill in here... *)
    induction p; induction q; reflexivity.
  Defined.
  Lemma pc4_is_2 {A : UU} {x y z : A} (p : x=y) (q : y=z)
    : pc4 p q = pc2 p q.
  Proof. (* fill in here... *)
    induction p; induction q; reflexivity.
  Defined.
  Lemma pc4_is_3 {A : UU} {x y z : A} (p : x=y) (q : y=z)
    : pc4 p q = pc3 p q.
  Proof. (* fill in here... *)
    induction p; induction q; reflexivity.
  Defined.


  (* Exercise 2.4 *)
  (* from the book:
       Define, by induction on n, a general notion of
       'n-dimensional path' in a type A, simultaneously with
       the type of boundaries for such paths.

     fill in here... *)
  Definition pathspace (A : UU) := Σ a b : A, a=b.
  Fixpoint n_pathspace (n : ℕ) (A : UU) :=
    match n with
    | 0   => A
    | S n => pathspace (n_pathspace n A)
    end.
  (* an interesting thought.  If we think of these as geometric
     squares, taking the two endpoints gives us only two of 4
     possible sides.  Are the other 2 sides implicit? *)
  (* AHHHH, yes, there is the matter of Σ-type structure... *)
  Lemma pathspace_equality {A : UU}
        (a b c d : A)
        (pab : a=b) (pcd : c=d)
    : ( ({a;b;pab}:pathspace A) = ({c;d;pcd}:pathspace A) )
        -> Σ (pac:a=c) (pbd:b=d), pab ∙ pbd = pac ∙ pcd.
  Proof.
    intro ppeq.
    apply projeq in ppeq; simpl in ppeq.
    destruct ppeq as (pac,ppeq).
    exists pac.
    rewrite (transport_sig (λ _,A) (λ xb, xb.1 = xb.2)) in ppeq.
    apply projeq in ppeq; simpl in ppeq.
    destruct ppeq as (pbd_,ppeq).
    rewrite transport_eq_r in ppeq.
    rewrite thm_2_11_3 in ppeq.
    
    replace (ap (λ x : total (λ _ : A, A), x.1) (lift b pac))
      with pac in ppeq.
    replace (ap (λ x : total (λ _ : A, A), x.2) (lift b pac))
      with (inv (transport_const A pac b)) in ppeq.
    exists ( inv (transport_const A pac b) ∙ pbd_ ).
    apply (whisker_l pac) in ppeq.
    autorewrite with PathGroupoid in ppeq; simpl in ppeq.
    autorewrite with PathGroupoid.
    assumption.

    induction pac; trivial.
    induction pac; trivial.
  Defined.


  (* Exercise 2.5 *)
  (* function 2.3.6 *)
  Definition ap_to_apd {A B : UU} {x y : A} (f : A -> B) (p : x=y)
        (apf : f x = f y)
    : p # (f x) = f y
    := transport_const B p (f x) ∙ apf.
  (* function 2.3.7 *)
  Definition apd_to_ap {A B : UU} {x y : A} (f : A -> B) (p : x=y)
             (apdf : p # (f x) = f y)
    : f x = f y
    := inv (transport_const B p (f x)) ∙ apdf.
  (* state and prove that these are inverse equivalences *)
  (* fill in here... *)
  Definition apd_compute {A B : UU} {x y : A} (f : A -> B) (p : x=y)
             (apf : f x = f y)
    : apd_to_ap f p (ap_to_apd f p apf) = apf.
  Proof. unfold apd_to_ap, ap_to_apd;
           autorewrite with PathGroupoid; trivial. Defined.
  Definition apd_uniq {A B : UU} {x y : A} (f : A -> B) (p : x=y)
             (apdf : p # (f x) = f y)
    : ap_to_apd f p (apd_to_ap f p apdf) = apdf.
  Proof. unfold apd_to_ap, ap_to_apd;
           autorewrite with PathGroupoid; trivial. Defined.
  Lemma apd_equiv {A B : UU} {x y : A} (f : A -> B) (p : x=y)
    : (p # (f x) = f y) ≃ (f x = f y).
  Proof. exists (apd_to_ap f p).
         apply equiv_from_qinv.
         exists (ap_to_apd f p).
         split; intro; [apply apd_compute | apply apd_uniq].
  Defined.


  (* Exercise 2.6 *)
  (* note that this was left as an example in the chapter... *)
  Example example_2_4_8 {A : UU} {x y z : A} (p : x=y)
    : isequiv (λ q:y=z, p ∙ q).
  Proof. (* fill in here... *)
    apply equiv_from_qinv.
    pose (p_inv := λ q:x=z, (inv p) ∙ q);
    exists p_inv.
    unfold funcomp, p_inv;
    split; intro; autorewrite with PathGroupoid; reflexivity.
  Defined.


  (* Exercise 2.7 *)
  Print ap_paireq.
  (* generalize the theorem just printed to Σ-types *)
  (* hint: try drawing topological pictures to get an intuition
           for why and where to use transports etc. *)
  (* fill in here *)
  Theorem ap_spaireq {A A' : UU} (B : A -> UU) (B' : A' -> UU)
          {x y : total B}
          {p : x.1 = y.1} {q : p # x.2 = y.2}
          (g : A -> A') (h : ∏ x:A, B x -> B' (g x))
    : ap (λ w, { g w.1 ; h w.1 w.2 }) (spaireq{p;q})
      = @spaireq _ _
                 { g x.1 ; h x.1 x.2 }
                 { g y.1 ; h y.1 y.2 }
                 (spair (λ gp, transport B' gp (h x.1 x.2)
                               = h y.1 y.2)
                        (ap g p)
                        ((inv (transport_apeq g p _))
                           ∙ (transport_comm_f h p x.2)
                           ∙ (ap (h y.1) q))).
  Proof. destruct x,y; simpl in p,q; destruct p,q; reflexivity. Defined.


  (* Exercise 2.8 *)
  (* generalize the theorem from the last exercise to coproduct types
     instead of Σ-types now *)
  (* fill in here... *)
  (* not sure what this should be *)


  (* Exercise 2.9 *)
  Theorem univf_coprod {A B : UU} {X : UU}
    : (A + B -> X) ≃ (A -> X) × (B -> X).
  Proof. (* fill in here... *)
    pose (elimination (f:A+B->X) :=
            ( (λ a:A, f (inl a)), (λ b:B, f (inr b)) )
         ).
    exists elimination.
    apply equiv_from_qinv.
    pose (introduction (gh : (A -> X) × (B -> X)) :=
            λ ab : A + B, match ab with
                          | inl a => (fst gh) a
                          | inr b => (snd gh) b
                          end ).
    exists introduction.
    split; unfold funcomp, elimination, introduction;
      [ intros (g, h)
      | intro f; apply funext; intro x; destruct x
      ]; trivial.
  Defined.
  (* state and prove a theorem 'univ_coprod', a dependent version *)
  (* note: can you basically copy and paste the proof from above?
           what does it mean to have a more general proposition
           proved by the same proof in light of Curry-Howard? *)
  (* fill in here... *)
  Theorem univ_coprod {A B : UU} {X : A+B -> UU}
    : (∏ ab:A+B, X ab)
        ≃ (∏ a:A, X (inl a)) × (∏ b:B, X (inr b)).
  Proof.
    pose (elimination (f : ∏ ab:A+B, X ab) :=
            ( (λ a:A, f (inl a)), (λ b:B, f (inr b)) )
         ).
    exists elimination.
    apply equiv_from_qinv.
    pose (introduction (gh : (∏ a:A, X (inl a)) × (∏ b:B, X (inr b))) :=
            λ ab : A + B, match ab with
                          | inl a => (fst gh) a
                          | inr b => (snd gh) b
                          end ).
    exists introduction.
    split; unfold funcomp, elimination, introduction;
      [ intros (g, h)
      | intro f; apply funext; intro x; destruct x
      ]; trivial.
  Defined.


  (* Exercise 2.10 *)
  Lemma sig_assoc {A : UU} {B : A -> UU} {C : total B -> UU}
    : (Σ (x:A) (y:B x), C{x;y}) ≃ (Σ (p:total B), C p).
  Proof.
    pose (elimination (tp : Σ (x:A) (y:B x), C{x;y}) :=
            { {tp.1;tp.2.1} ; tp.2.2 }
         ).
    exists elimination.
    apply equiv_from_qinv.
    pose (introduction (tp : Σ (p:total B), C p) :=
            { tp.1.1 ; tp.1.2 ; tp.2 }
            : Σ (x:A) (y:B x), C{x;y}
         ).
    exists introduction.
    split; unfold funcomp, elimination, introduction; intro tp; trivial.
  Defined.


  (* I really need convenience functions to pull apart non-dependent
     dependent pairs... *)
  

  (* Exercise 2.11 *)
  (* how this all gets formalized might be tricky or up for debate. *)
  (* fill in here... *)
  Definition pullback (A B C : UU) (f : A->C) (g : B->C)
    := Σ (a:A) (b:B), f a = g b.
  Definition comm_square (A B C P : UU)
    := Σ (f : A -> C) (g : B -> C)
         (h : P -> A) (k : P -> B),
       f∘h = g∘k .
  (* here is a good example of how we can wring a bit of
     insight out of Coq as a computational engine. *)
  Compute (λ (A B C P : UU), Σ (f : A->C) (g : B->C),
           pullback (P->A) (P->B) (P->C) (λ h, f∘h) (λ k, g∘k)).
  (* Then, once we've massaged an expression into the right form
     we can crystalize it in a proven statement. *)
  Remark comm_via_pullback {A B C P : UU}
    : comm_square A B C P
      = ( Σ (f : A->C) (g : B->C),
          pullback (P->A) (P->B) (P->C) (λ h, f∘h) (λ k, g∘k) ).
  Proof. unfold comm_square, pullback; reflexivity. Defined.

  Definition is_pullback_square {A B C P : UU}
             (sq : comm_square A B C P)
    := ∏ X:UU, (X -> P) ≃ (pullback (X->A) (X->B) (X->C)
                                    (λ h, sq.1 ∘ h) (λ k, sq.2.1 ∘ k)).

  Theorem univ_pullback {A B C : UU} {f : A->C} {g : B->C}
    : is_pullback_square { f ;
                           g ;
                           (λ (p : pullback A B C f g), p.1 ) ;
                           (λ (p : pullback A B C f g), p.2.1 ) ;
                           funext (λ (p : pullback A B C f g), p.2.2) }.
  Proof.
    unfold is_pullback_square; intro X; simpl.
    pose (eliminate (inj : X -> pullback A B C f g) :=
            let h x := (inj x).1 in
            let k x := (inj x).2.1 in
            { h ; k ; funext (λ x, (inj x).2.2) }
            : pullback (X -> A) (X -> B) (X -> C)
                       (λ h : X -> A, f ∘ h) (λ k : X -> B, g ∘ k)
         ).
    exists eliminate.
    apply equiv_from_qinv.
    pose (introduce ( p : pullback (X -> A) (X -> B) (X -> C)
                                   (λ h : X -> A, f ∘ h)
                                   (λ k : X -> B, g ∘ k) ) :=
            λ x:X, let a := p.1 x in
                   let b := p.2.1 x in
                   { a ; b ; happly p.2.2 x }
                   : pullback A B C f g
         ).
    exists introduce.
    unfold funcomp, eliminate, introduce; split; simpl;
      [ intros (h,(k,eq)); simpl; eta_reduce; rewrite <- funext_uniq
      | intro inj; apply funext; intro x; rewrite funext_compute
      ]; trivial.
  Defined.


  (* Exercise 2.12 *)
  (* TODO... *)



  (* support work for 2.13 *)
  Definition bneg (b : 𝟚) :=
    match b with | true => false | false => true end.
  Lemma bneg_isequiv : isequiv bneg.
  Proof.
    apply equiv_from_qinv.
    exists bneg.
    unfold funcomp, bneg; split; intro b; destruct b; trivial.
  Defined.
  Lemma bneg_inv : ∏ x:𝟚, bneg (bneg x) = x.
  Proof. intro x; destruct x; reflexivity. Defined.
  Lemma all_bool_funcs :
    ∏ f:𝟚->𝟚, ((f = idfun) + (f = bneg) +
               (f = λ _,true) + (f = λ _,false))%type.
  Proof.
    intro f.
    pose (g := match f true with
               | true  => match f false with
                          | true  => λ _,true
                          | false => idfun end
               | false => match f false with
                          | true  => bneg
                          | false => λ _,false end
               end).
    assert (f=g) as eq.
    { apply funext; intro x; destruct x;
        destruct (f false); destruct (f true); simpl; trivial; simpl. }
    destruct (f false);
      destruct (f true);
      [ right | left; left; left | left; left; right | left; right ];
      trivial.
  Defined.

  Lemma unit_is_set : ∏ (u v : 𝟙) (p q : u=v), p = q.
  Proof. intros u v p q.
         pose (ueqv := @uniteq_is_unit u v p).
         apply ( inv ((snd ueqv.2).2 p)
                     ∙ ap _ (uniteq _ _)
                     ∙ (snd ueqv.2).2 q ).
  Defined.
  Lemma bool_is_set : ∏ (x y : 𝟚) (p q : x = y), p = q.
  Proof. rewrite (ua bool_is_unit_plus_unit).
         intros x y p q.
         destruct x as [u|u];
           [ pose (xp := encode_coprod_l u y p)
           | pose (xp := encode_coprod_r u y p)
           ];
         [ pose (DEp := deencode_coprod_l u y p);
           pose (DEq := deencode_coprod_l u y q)
         | pose (DEp := deencode_coprod_r u y p);
           pose (DEq := deencode_coprod_r u y q)
         ];  destruct y as [v|v]; try contradiction;
         apply (inv DEp ∙ ap _ (unit_is_set _ _ _ _) ∙ DEq).
  Defined.
  
  Lemma all_bool_eqv
    : ∏ f:𝟚≃𝟚, ((f = equiv_refl) + (f = { bneg ; bneg_isequiv }))%type.
  Proof.
    intro f; destruct f as (fwd,feqv).
    generalize feqv; clear feqv;
      destruct (all_bool_funcs fwd) as [[[p|p]|p]|p];
      rewrite p; clear p; clear fwd;
        intro feqv; destruct feqv as ((r,req),(l,leq)).
    (* case equiv_refl *)
    left; apply spaireq; exists idpath; apply paireq; split;
      apply spaireq;
      [ exists (funext req) | exists (funext leq) ];
      apply funext; intro x; apply bool_is_set.
    (* case bneg_refl *)
    right; apply spaireq; exists idpath; apply paireq; split;
      apply spaireq;
      [ exists (funext(λ x, inv (bneg_inv _) ∙ ap bneg (req x)))
      | exists (funext(λ x, ap l (inv (bneg_inv _)) ∙ leq (bneg x)))
      ]; apply funext; intro x; apply bool_is_set.
    (* constant function cases *)
    pose (BAD := true_is_not_false (req false)); contradiction.
    pose (BAD := true_is_not_false (inv (req true))); contradiction.
  Defined.
  
  (* Exercise 2.13 *)
  Theorem two_is_two_is_two : (𝟚 ≃ 𝟚) ≃ 𝟚.
  Proof. (* fill in here... *)
    pose (code_eqv2 (eqv : 𝟚 ≃ 𝟚) := eqv.1 true).
    exists code_eqv2.
    apply equiv_from_qinv.
    pose (decode_eqv2 (b : 𝟚) :=
            match b with
            | true  => equiv_refl
            | false => { bneg ; bneg_isequiv }
            end).
    exists decode_eqv2.
    unfold funcomp; split;
      [ intro x; destruct x
      | intro eqv;
        destruct (all_bool_eqv eqv) as [E|E]; rewrite E
      ]; trivial; simpl.
  Defined.


  (* Exercise 2.14 *)
  (* left for paper work... *)


  (* Exercise 2.15 *)
  Lemma stronger_2_10_5 {A : UU} {B : A->UU} {x y : A} {p : x=y}
    : transport B p = (idtoeqv (ap B p)).1 .
  Proof. (* fill in here... *)
    induction p; trivial.
  Defined.


  (* Exercise 2.16 *)
  (* skipping, due to comments on difficulty/reliance on
     un-covered material *)


  (* Exercise 2.17 *)
  Theorem prodeqv1 {A A' B B' : UU}
    : (A ≃ A')×(B ≃ B') -> (A×B) ≃ (A'×B').
  Proof. intros (ae,be).
         exists (λ ab, (ae.1 (fst ab), be.1 (snd ab))).
         apply equiv_from_qinv.
         pose (aq := (qinv_from_equiv ae.2));
           pose (bq := (qinv_from_equiv be.2)).
         pose (aq2 := aq.2); pose (bq2 := bq.2);
           unfold funcomp in aq2, bq2.
         exists (λ ab', (aq.1 (fst ab'), bq.1 (snd ab'))).
         unfold funcomp; split; intro x; destruct x as (a,b); simpl;
           [ rewrite (fst aq2 a); rewrite (fst bq2 b)
           | rewrite (snd aq2 a); rewrite (snd bq2 b)
           ]; simpl; trivial.
  Defined.

  Theorem prodeqv2 {A A' B B' : UU}
    : (A ≃ A')×(B ≃ B') -> (A×B) ≃ (A'×B').
  Proof. intros (ae,be).
         destruct (ua ae).
         destruct (ua be).
         apply equiv_refl.
  Defined.

End Chapter_2_Exercises.

