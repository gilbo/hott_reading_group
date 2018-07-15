
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
  Defined.
  Lemma pc2_is_3 {A : UU} {x y z : A} (p : x=y) (q : y=z)
    : pc2 p q = pc3 p q.
  Proof. (* fill in here... *)
  Defined.
  Lemma pc1_is_3 {A : UU} {x y z : A} (p : x=y) (q : y=z)
    : pc1 p q = pc3 p q.
  Proof. (* fill in here... *)
  Defined.


  (* Exercise 2.2 *)
  Lemma pc_proof_triangle {A : UU} {x y z : A} (p : x=y) (q : y=z)
    : pc1 (pc1_is_2 p q) (pc2_is_3 p q) = pc1_is_3 p q.
  Proof. (* fill in here... *)
  Defined.


  (* Exercise 2.3 *)
  Lemma pc4 {A : UU} {x y z : A} (p : x=y) (q : y=z) : x=z.
  Proof. (* fill in here... *)
  Defined.
  Lemma pc4_is_1 {A : UU} {x y z : A} (p : x=y) (q : y=z)
    : pc4 p q = pc1 p q.
  Proof. (* fill in here... *)
  Defined.
  Lemma pc4_is_2 {A : UU} {x y z : A} (p : x=y) (q : y=z)
    : pc4 p q = pc2 p q.
  Proof. (* fill in here... *)
  Defined.
  Lemma pc4_is_3 {A : UU} {x y z : A} (p : x=y) (q : y=z)
    : pc4 p q = pc3 p q.
  Proof. (* fill in here... *)
  Defined.


  (* Exercise 2.4 *)
  (* from the book:
       Define, by induction on n, a general notion of
       'n-dimensional path' in a type A, simultaneously with
       the type of boundaries for such paths.

     fill in here... *)


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


  (* Exercise 2.6 *)
  (* note that this was left as an example in the chapter... *)
  Example example_2_4_8 {A : UU} {x y z : A} (p : x=y)
    : isequiv (λ q:y=z, p ∙ q).
  Proof. (* fill in here... *)
  Defined.


  (* Exercise 2.7 *)
  Print ap_paireq.
  (* generalize the theorem just printed to Σ-types *)
  (* hint: try drawing topological pictures to get an intuition
           for why and where to use transports etc. *)
  (* fill in here *)


  (* Exercise 2.8 *)
  (* generalize the theorem from the last exercise to coproduct types
     instead of Σ-types now *)
  (* fill in here... *)
  (* not sure what this should be *)


  (* Exercise 2.9 *)
  Theorem univf_coprod {A B : UU} {X : UU}
    : (A + B -> X) ≃ (A -> X) × (B -> X).
  Proof. (* fill in here... *)
  Defined.
  (* state and prove a theorem 'univ_coprod', a dependent version *)
  (* note: can you basically copy and paste the proof from above?
           what does it mean to have a more general proposition
           proved by the same proof in light of Curry-Howard? *)
  (* fill in here... *)


  (* Exercise 2.10 *)
  Lemma sig_assoc {A : UU} {B : A -> UU} {C : total B -> UU}
    : (Σ (x:A) (y:B x), C{x;y}) ≃ (Σ (p:total B), C p).
  Proof. (* fill in here... *)
  Defined.


  (* Exercise 2.11 *)
  (* how this all gets formalized might be tricky or up for debate. *)
  (* fill in here... *)
  
 

  (* Exercise 2.12 *)
  (* TODO... *)



  (* Exercise 2.13 *)
  Theorem two_is_two_is_two : (𝟚 ≃ 𝟚) ≃ 𝟚.
  Proof. (* fill in here... *)
  Defined.


  (* Exercise 2.14 *)
  (* left for paper work... *)


  (* Exercise 2.15 *)
  Lemma stronger_2_10_5 {A : UU} {B : A->UU} {x y : A} {p : x=y}
    : transport B p = (idtoeqv (ap B p)).1 .
  Proof. (* fill in here... *)
  Defined.


  (* Exercise 2.16 *)
  (* skipping, due to comments on difficulty/reliance on
     un-covered material *)


  (* Exercise 2.17 *)
  Theorem prodeqv1 {A A' B B' : UU}
    : (A ≃ A')×(B ≃ B') -> (A×B) ≃ (A'×B').
  Proof. (* fill in here... *)
  Defined.

  Theorem prodeqv2 {A A' B B' : UU}
    : (A ≃ A')×(B ≃ B') -> (A×B) ≃ (A'×B').
  Proof. (* fill in here... *)
  Defined.

End Chapter_2_Exercises.

