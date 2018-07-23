
(* If this require statement doesn't work, it's probably because
   you haven't compiled the file pre1.v  To do that, run
   > coqc pre1.v
 *)
(* Note that we `Require Export` in pre2.v, unlike ch2_ref.v
   If we did `Require Import pre1` then the contents of pre1.v would
   be visible here in pre2.v, but not in anything else that requires
   pre2.v, which would be bad since pre1.v has all our basic
   definitions *)
Require Export pre1.



(* ** --                    Extra Notation Fun                    -- ** *)

(* Going to keep around all the fancy pants notation *)
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



(* ** --                        Ltac Support                        -- ** *)

Tactic Notation "unsimpl" constr(E) :=
  let F := (eval simpl in E) in change F with E.
(* from here:
   https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/coqdoc/AdditionalTactics.html
 *)



(* ** --       The Identity Function and Function Composition       -- ** *)

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



(* ** --                     The Path Groupoid                     -- ** *)

Definition inv {A : UU} {a b : A}
           (p : a = b)
  : b = a
  := paths_rect a (λ x _, x = a)
                (idpath a) b p.

Definition path_compose {A : UU} {a b c : A}
           (p : a = b) (q : b = c)
  : a = c.
Proof.
  induction p; apply q.
Defined.
Notation "p '∙' q" :=
  (path_compose p q)
    (at level 60, left associativity) : type_scope.
(* input: \. WARNING: do not use \cdot, which looks the same
                      but isn't *)

(* The groupoid structure of path composition.
   We bundle this as a rewriting system database *)
Lemma path_compose_rid {A : UU} {a b : A} (p : a = b)
  : p ∙ idpath = p.
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
Proof. induction p; reflexivity. Defined.
Lemma path_inv_compose {A : UU} {a b c : A}
      (p : a = b) (q : b = c)
  : inv (p∙q) = (inv q) ∙ (inv p).
Proof. induction p; simpl; rewrite path_compose_rid. reflexivity. Defined.
Lemma path_inverse_l_assoc {A : UU} {a b c : A} (p : a = b) (q : c = b)
  : q ∙ (inv p) ∙ p = q.
Proof. rewrite <- path_compose_assoc;
         rewrite path_inverse_l;
         rewrite path_compose_rid;
         reflexivity.
Defined.
Lemma path_inverse_r_assoc {A : UU} {a b c : A} (p : a = b) (q : c = a)
  : q ∙ p ∙ inv p = q.
Proof. rewrite <- path_compose_assoc;
         rewrite path_inverse_r;
         rewrite path_compose_rid;
         reflexivity.
Defined.

Create HintDb PathGroupoid.
Hint Rewrite @path_inverse_l : PathGroupoid.
Hint Rewrite @path_inverse_r : PathGroupoid.
Hint Rewrite @path_inverse_inverse : PathGroupoid.
Hint Rewrite @path_compose_rid : PathGroupoid.
Hint Rewrite @path_compose_assoc : PathGroupoid.
Hint Rewrite @path_inv_compose : PathGroupoid.
Hint Rewrite @path_inverse_l_assoc : PathGroupoid.
Hint Rewrite @path_inverse_r_assoc : PathGroupoid.

(* some tactics for helping with paths besides rewrite ... *)

Tactic Notation "chain" constr(Ex) :=
  match goal with
  | |- ?Ey = _ => refine (path_compose (_ : Ey = Ex) _)
  end.

Tactic Notation "chain" constr(Ex) "by" tactic(T) :=
  match goal with
  | |- ?Ey = _ => refine (path_compose (_ : Ey = Ex) _);
                  [ solve[T] | ]
  end.

(* example:
   Lemma nn {n : nat} : n = (n + 0) + 0.
   Proof.
     chain (n + 0) by apply plus_n_O.
     apply plus_n_O.
   Defined.
 *)




(* ** --                   Loops & Eckmann-Hilton                   -- ** *)

(* Only for Eckmann-Hilton.  Hopefully will do better later *)
Definition loops2_ (A : UU) (a : A) := (idpath a) = (idpath a).

Definition whisker_r {A : UU} {a b c : A}
           {p q : a = b}
           (r : b = c) (α : p = q)
  : p ∙ r = q ∙ r.
Proof. induction r;
         pose (ru := @path_compose_rid A a b);
         apply (ru _ ∙ α ∙ inv (ru _)).
Defined.
Definition whisker_l {A : UU} {a b c : A}
           {r s : b = c}
           (p : a = b) (β : r = s)
  : p ∙ r = p ∙ s.
Proof. induction p. assumption. Defined.

(* some extra convenience functions... *)
Definition cancel_whisker_r {A : UU} {a b c : A}
           {p q : a = b}
           (r : b = c) (α : p ∙ r = q ∙ r)
  : p = q.
Proof. induction r;
         autorewrite with PathGroupoid in α;
         assumption. Defined.
Definition cancel_whisker_l {A : UU} {a b c : A}
           {r s : b = c}
           (p : a = b) (β : p ∙ r = p ∙ s)
  : r = s.
Proof. induction p;
         autorewrite with PathGroupoid in β;
         assumption. Defined.

Definition horizontal_1 {A : UU} {a b c : A}
           {p q : a = b} {r s : b = c}
           (α : p = q) (β : r = s)
  := (whisker_r r α) ∙ (whisker_l q β).
Definition horizontal_2 {A : UU} {a b c : A}
           {p q : a = b} {r s : b = c}
           (α : p = q) (β : r = s)
  := (whisker_l p β) ∙ (whisker_r s α).
Lemma EQ_horizontal {A : UU} {a b c : A}
      {p q : a = b} {r s : b = c}
      (α : p = q) (β : r = s)
  : (horizontal_1 α β) = (horizontal_2 α β).
Proof.
  induction α, β; induction p, r; trivial.
Defined.
Theorem Eckmann_Hilton {A : UU} {a : A}
        (α β : loops2_ A a)
  : α ∙ β = β ∙ α.
Proof.
  (* Main Proof of Eckmann Hilton *)
  unfold loops2_ in α,β.
  chain (horizontal_1 α β).
  { (* this is a sub-goal mechanism for organizing proofs... *)
    unfold horizontal_1; simpl; autorewrite with PathGroupoid;
      trivial.
  }
  chain (horizontal_2 α β) by exact (EQ_horizontal α β).
  {
    unfold horizontal_2; simpl; autorewrite with PathGroupoid;
      trivial.
  }
Qed.

(* pointed types *)
Definition PointedType := Σ A:UU, A.
Definition loopspace (A : PointedType)
  := { A.2 = A.2 ; idpath A.2 } : PointedType.
Fixpoint loopspace_n (n:nat) (A : PointedType)
  := match n with
     | 0   => A
     | S n => loopspace_n n (loopspace A)
     end.




(* ** --      Function Application & Interaction with Equality      -- ** *)

Definition ap {A B : UU} {x y : A} (f : A -> B)
  : (x = y) -> (f x) = (f y).
Proof. intro p; induction p; reflexivity. Defined.

Lemma ap_path_compose {A B : UU} {x y z : A}
      {p : x = y} {q : y = z}
      {f : A -> B}
  : ap f (p ∙ q) = (ap f p) ∙ (ap f q).
Proof. induction p; reflexivity. Defined.
Lemma ap_inv {A B : UU} {x y : A}
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

(* an addition based on ideas from Unimath transport lemmas,
   and interactions between paths and (dependent-)pair constructors *)
Definition ap2 {A B C : UU} {a a' b b'}
           (f : A -> B -> C) (p : a = a') (q : b = b')
  : f a b = f a' b'.
Proof. induction p; induction q; reflexivity. Defined.
Lemma ap2_path_compose {A B C : UU} {a a' a'' b b' b''}
      {p : a = a'} {p' : a' = a''}
      {q : b = b'} {q' : b' = b''}
      {f : A -> B -> C}
  : ap2 f (p ∙ p') (q ∙ q') = (ap2 f p q) ∙ (ap2 f p' q').
Proof. induction p; induction q; reflexivity. Defined.
Lemma ap2_inv {A B C : UU} {a a' b b'}
      {p : a = a'} {q : b = b'}
      {f : A -> B -> C}
  : ap2 f (inv p) (inv q) = inv (ap2 f p q).
Proof. induction p; induction q; reflexivity. Defined.
Lemma ap2_func_compose {A B C D : UU} {a a' b b'}
      {p : a = a'} {q : b = b'}
      {f : A -> B -> C} {g : C -> D}
  : ap g (ap2 f p q) = ap2 (λ a b, g (f a b)) p q.
Proof. induction p; induction q; reflexivity. Defined.
Lemma ap2_fcomp1 {A' A B C : UU} {a a' b b'}
      {p : a = a'} {q : b = b'}
      {f : A' -> A} {g : A -> B -> C}
  : ap2 g (ap f p) q = ap2 (λ a b, g (f a) b) p q.
Proof. induction p; induction q; reflexivity. Defined.
Lemma ap2_fcomp2 {A B' B C : UU} {a a' b b'}
      {p : a = a'} {q : b = b'}
      {f : B' -> B} {g : A -> B -> C}
  : ap2 g  p (ap f q) = ap2 (λ a b, g a (f b)) p q.
Proof. induction p; induction q; reflexivity. Defined.
Lemma ap2_id1 {A B : UU} {a a' : A} {b b' : B}
      {p : a = a'} {q : b = b'}
  : ap2 (λ a _, a) p q = p.
Proof. induction p; induction q; reflexivity. Defined.
Lemma ap2_id2 {A B : UU} {a a' : A} {b b' : B}
      {p : a = a'} {q : b = b'}
  : ap2 (λ _ b, b) p q = q.
Proof. induction p; induction q; reflexivity. Defined.

Create HintDb ApPushdown.
Hint Rewrite @ap_path_compose : ApPushdown.
Hint Rewrite @ap_inv : ApPushdown.
Hint Rewrite @ap_func_compose : ApPushdown.
Hint Rewrite @ap_idfun : ApPushdown.
Hint Rewrite @ap2_path_compose : ApPushdown.
Hint Rewrite @ap2_inv : ApPushdown.
Hint Rewrite @ap2_func_compose : ApPushdown.
Hint Rewrite @ap2_fcomp1 : ApPushdown.
Hint Rewrite @ap2_fcomp2 : ApPushdown.
Hint Rewrite @ap2_id1 : ApPushdown.
Hint Rewrite @ap2_id2 : ApPushdown.




(* ** --                         Fibrations                         -- ** *)

Definition fibration (X : UU) := X -> UU.
Notation "A -> B" := (λ x, A x -> B x) : fibration_scope.
Delimit Scope fibration_scope with fiber.

Definition total   {X:UU} (P : fibration X) := Σ x:X, P x.
Definition section {X:UU} (P : fibration X) := ∏ x:X, P x.
  
Lemma transport {A : UU} (P : A -> UU) {x y : A} (p : x=y)
  : P x -> P y.
Proof. induction p; exact idfun. Defined.

(* a synonym for transporting in reverse *)
(* this must be defined as notation to ensure automatic unfolding... *)
Notation transport' P p := (transport P (inv p)).
(* as a bonus, printing of complicated transport terms is slightly
   simplified *)

Notation "p # x" :=
  (transport _ p x)
    (right associativity, at level 65, only parsing).
Notation "p #' x" :=
  (transport' _ p x)
     (right associativity, at level 65, only parsing).




(* ** --     Dependent Function Application & Transport Lemmas     -- ** *)

(* Note: I have added a lot of extra lemmas for completeness or
         from a closer reading of the Foundations sub-library of
         UniMath. *)

Lemma apd {A : UU} {P : A -> UU} {x y : A}
      (f : ∏ x:A, P x)
  : ∏ p:x=y, p#(f x) = (f y) :> (P y).
Proof. induction p; reflexivity. Defined.
Lemma apd' {A : UU} {P : A -> UU} {x y : A}
      (f : ∏ x:A, P x)
  : ∏ p:x=y, (f x) = p#'(f y) :> (P x).
Proof. induction p; reflexivity. Defined.

Lemma transport_const {A : UU} (B : UU) {x y : A} (p : x=y) (b : B)
  : transport (λ _, B) p b = b.
Proof. induction p; reflexivity. Defined.

(* lem_2_3_8 *)
Lemma apd_factor {A B : UU} {x y : A} {f : A->B} {p : x=y}
  : apd f p = (transport_const B p (f x)) ∙ ap f p.
Proof. induction p; reflexivity. Defined.
Lemma apd'_factor {A B : UU} {x y : A} {f : A->B} {p : x=y}
  : apd' f p = ap f p ∙ inv (transport_const B (inv p) (f y)).
Proof. induction p; reflexivity. Defined.



(* ** --                     Transport Lemmas                     -- ** *)

(* lem_2_3_9 *)
Lemma transport_twice {A : UU} {P : A -> UU} {x y z : A}
      (p : x=y) (q : y=z) (u : P x)
  : q#(p#u) = (p ∙ q)#u.
Proof. induction p; reflexivity. Defined.
Lemma transport'_twice {A : UU} {P : A -> UU} {x y z : A}
      (p : x=y) (q : y=z) (u : P z)
  : p#'(q#'u) = (p ∙ q)#'u.
Proof. induction p; reflexivity. Defined.
(* lem_2_3_10 *)
Lemma transport_apeq {A B : UU} {P : B -> UU} {x y : A}
      (f : A -> B)
      (p : x=y) (u : P (f x))
  : transport (P ∘ f) p u = transport P (ap f p) u.
Proof. induction p; reflexivity. Defined.
Lemma transport'_apeq {A B : UU} {P : B -> UU} {x y : A}
      (f : A -> B)
      (p : x=y) (u : P (f y))
  : transport' (P ∘ f) p u = transport' P (ap f p) u.
Proof. induction p; reflexivity. Defined.
Lemma transport_comm_f {A : UU} {P Q : A -> UU} {x y : A}
      (f : section (P -> Q)%fiber )
      (p : x=y) (u : P x)
  : transport Q p (f x u) = f y (transport P p u).
Proof. induction p; reflexivity. Defined.
Lemma transport_section {A : UU} {P : A -> UU} {x y : A}
      (f : section P) (p : x=y)
  : transport P p (f x) = (f y).
Proof. induction p; reflexivity. Defined.

(* This formulation can be helpful for isolating the path part of
   a transport for rewriting.
   one would think that `ap transport ...` would suffice, but because
   of the inverted positions of the path and the point y the types
   don't match up right.
 *)
Lemma transport_paths {X : UU} {P : X -> UU} {x1 x2 : X} {p1 p2 : x1 = x2}
      (pp12 : p1 = p2) {y : P x1}
  : transport P p1 y = transport P p2 y.
Proof. induction pp12; reflexivity. Defined.
Opaque transport_paths.
Definition transport_paths' {X : UU} {P : X -> UU}
           {x1 x2 : X} {p1 p2 : x1 = x2}
           (pp12 : p1 = p2) {y : P x1}
  : transport P p2 y = transport P p1 y
  := @transport_paths X P x1 x2 p2 p1 (inv pp12) y.
Definition transport'_paths {X : UU} {P : X -> UU}
           {x1 x2 : X} {p1 p2 : x1 = x2}
           (pp12 : p1 = p2) {y : P x2}
  : transport' P p1 y = transport' P p2 y
  := @transport_paths X P x2 x1 (inv p1) (inv p2) (ap inv pp12) y.

Lemma transport_inv_l {X : UU} (P : X -> UU) {x y : X}
      (p : x=y) (xx : P x)
  : p #' p # xx = xx.
Proof. induction p; reflexivity. Defined.
Lemma transport_inv_r {X : UU} (P : X -> UU) {x y : X}
      (p : x=y) (yy : P y)
  : p # p #' yy = yy.
Proof. induction p; reflexivity. Defined.
Definition transport_inv_l' {X : UU} (P : X -> UU) {x y : X}
           (p : x=y) (xx : P x)
  := inv (transport_inv_l P p xx).
Definition transport_inv_r' {X : UU} (P : X -> UU) {x y : X}
           (p : x=y) (yy : P y)
  := inv (transport_inv_r P p yy).

Lemma flip_transport_r {A : UU} {P : A -> UU}
      {x y : A}
      {xx : P x} {yy : P y}
      (p : x = y)
      (q : p # xx = yy)
  : xx = p #' yy.
Proof. exact (transport_inv_l' _ _ _ ∙ ap (transport' _ p) q). Defined.
Lemma flip_transport_l {A : UU} {P : A -> UU}
      {x y : A}
      {xx : P x} {yy : P y}
      (p : y = x)
      (q : xx = p # yy)
  : p #' xx = yy.
Proof. exact (ap (transport' _ p) q ∙ transport_inv_l _ _ _). Defined.




(* ** --     Dependent Application (of function to path) Lemmas     -- ** *)

Lemma apd_path_compose {A : UU} {P : A -> UU} {x y z : A}
      {p : x = y} {q : y = z}
      {f : ∏ x:A, P x}
  : apd f (p ∙ q) = inv (transport_twice p q (f x))
                      ∙ ap (transport P q) (apd f p)
                      ∙ apd f q.
Proof. induction p; reflexivity. Defined.
Lemma apd'_path_compose {A : UU} {P : A -> UU} {x y z : A}
      {p : x = y} {q : y = z}
      {f : ∏ x:A, P x}
  : apd' f (p ∙ q) = apd' f p
                          ∙ ap (transport' P p) (apd' f q)
                          ∙ transport'_twice p q (f z).
Proof. induction p,q; reflexivity. Defined.
Lemma apd_inv {A : UU} {P : A -> UU} {x y : A}
      {p : x = y}
      {f : ∏ x:A, P x}
  : apd f (inv p) = inv (apd' f p).
Proof. induction p; reflexivity. Defined.
Lemma apd'_inv {A : UU} {P : A -> UU} {x y : A}
      {p : x = y}
      {f : ∏ x:A, P x}
  : apd' f (inv p) = inv (apd f p)
                         ∙ transport_paths' (path_inverse_inverse p).
Proof. induction p; reflexivity. Defined.
Lemma apd_func_compose {A B : UU} {P : B -> UU} {x y : A}
      {p : x = y}
      {f : A -> B} {g : ∏ x:B, P x}
  : apd g (ap f p) = inv (transport_apeq f p (g (f x))) ∙ apd (g ∘ f) p.
Proof. induction p; reflexivity. Defined.
Lemma apd'_func_compose {A B : UU} {P : B -> UU} {x y : A}
      {p : x = y}
      {f : A -> B} {g : ∏ x:B, P x}
  : apd' g (ap f p) = apd' (g ∘ f) p ∙ (transport'_apeq f p (g (f y))).
Proof. induction p; reflexivity. Defined.
(* apd_idfun is covered by apd_factor *)

Create HintDb ApdPushdown.
Hint Rewrite @apd_path_compose : ApdPushdown.
Hint Rewrite @apd'_path_compose : ApdPushdown.
Hint Rewrite @apd_inv : ApdPushdown.
Hint Rewrite @apd'_inv : ApdPushdown.
Hint Rewrite @apd_func_compose : ApdPushdown.
Hint Rewrite @apd'_func_compose : ApdPushdown.
Hint Rewrite @apd_factor : ApdPushdown.
Hint Rewrite @apd'_factor : ApdPushdown.




(* ** --                          Homotopy                          -- ** *)

Definition homotopy {A : UU} {P : A -> UU}
           (f g : section P)
  := ∏ x:A, f x = g x.
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

Definition fun_homotopy {A B : UU} {P : B -> UU} {g g' : section P}
      (f : A -> B) (H : g ~ g')
  : g ∘ f ~ g' ∘ f
  := λ x, H (f x).
Definition homotopy_fun {A B C : UU} {f f' : A -> B}
           (H : f ~ f') (g : B -> C)
  : g ∘ f ~ g ∘ f'
  := λ x, ap g (H x).

Lemma natural_homotopy  {A B : UU} {x y : A}
      (p : x=y) (f g : A -> B) (H : f ~ g)
  : (H x) ∙ (ap g p) = (ap f p) ∙ (H y).
Proof. induction p; simpl; rewrite path_compose_rid; reflexivity. Defined.

(* TODO: bettter name? *)
Corollary cor_2_4_4 {A : UU} {f : A -> A} {x : A} {H : f ~ idfun}
  : H (f x) = ap f (H x).
Proof.
  apply (cancel_whisker_r (H x)).
  chain (H (f x) ∙ ap idfun (H x)) by rewrite ap_idfun; trivial.
  apply (natural_homotopy (H x) _ _ H).
Qed.




(* ** --              Quasi-Inverses and Equivalences              -- ** *)

Definition qinv {A B : UU} (f : A -> B) :=
  exists g : B -> A, (f ∘ g ~ (@idfun B)) × (g ∘ f ~ (@idfun A)).

Definition isequiv {A B : UU} (f : A -> B)
  := (Σ g:B->A, f ∘ g ~ (@idfun B)) × (Σ h:B->A, h ∘ f ~ (@idfun A)).

Definition equiv (A B : UU) := (Σ f:A->B, isequiv f).
Notation "A ≃ B" :=
  (equiv A B)
    (at level 80, no associativity) : type_scope.
(* input: \~- or \simeq *)

(* We can use some Coq magic to encode one of the
   "abuses of notation" from the book, namely treating an
   equivalence as if it were simply the function in its first half. *)
Definition equiv_function {A B : UU} (e : A≃B) : A -> B := e.1 .
Coercion equiv_function : equiv >-> Funclass.

Lemma equiv_from_qinv {A B : UU} {f : A -> B}
  : qinv f -> isequiv f.
Proof.
  intros (g ,(α , β));
    split; exists g; assumption.
Defined.
Lemma qinv_from_equiv {A B : UU} {f : A -> B}
  : isequiv f -> qinv f.
Proof.
  intros ((g , α),(h , β));
    pose (γ x := (inv (β (g x))) ∙ ap h (α x) : g x = h x);
    pose (β' x := (γ ∘ f) x ∙ β x);
    exact { g ; (α, β') }.
Defined.

(* ex_2_4_9 *)
Example transport_is_qinv {A : UU} {P : A -> UU} {x y : A} (p : x = y)
  : qinv (transport P p : P x -> P y).
Proof.
  exists (transport' P p);
  unfold funcomp; split; intro;
    [ apply transport_inv_r | apply transport_inv_l ].
Defined.
Remark transport_is_an_eqv {X : UU} (P : X -> UU) {x y : X} (p : x=y)
  : isequiv (transport P p).
Proof. apply equiv_from_qinv; apply transport_is_qinv. Defined.

Example qinv_id (A : UU) : qinv (@idfun A)
  := { @idfun A ; ((λ y, idpath y), (λ x, idpath x)) }.
Lemma equiv_refl {A : UU} : A ≃ A.
Proof.
  exists (@idfun A);
    apply (equiv_from_qinv (qinv_id A)).
Defined.
Lemma einv {A B : UU} : (A ≃ B) -> (B ≃ A).
Proof.
  intros (f, eAB).
  destruct (qinv_from_equiv eAB) as (finv, (α,β)).
  exists finv; apply equiv_from_qinv.
  exact ( { f;(β,α) } : qinv finv ).
Defined.
Lemma equiv_trans {A B C : UU}
  : (A ≃ B) -> (B ≃ C) -> (A ≃ C).
Proof.
  intros (f, eAB) (g, eBC).
  destruct (qinv_from_equiv eAB) as (finv, (fα,fβ)).
  destruct (qinv_from_equiv eBC) as (ginv, (gα,gβ)).
  exists (g∘f).
  apply equiv_from_qinv; exists (finv ∘ ginv).
  split; [intro c | intro a]; unfold funcomp, idfun.
  - chain (g (ginv c)) by exact (ap g (fα (ginv c))). exact (gα c).
  - chain (finv (f a)) by exact (ap finv (gβ (f a))). exact (fβ a).
Defined.




(* ** --         Dependent path conventions are equivalent         -- ** *)

Lemma flip_transport'_r {A : UU} {P : A -> UU} {x y : A}
      {xx : P x} {yy : P y}
      (p : x = y) (q : xx = p #' yy)
  : p # xx = yy.
Proof. exact (ap (transport P p) q ∙ transport_inv_r _ _ _). Defined.
Theorem flip_transport_eqv {A : UU} {P : A -> UU}
      {x y : A}
      {xx : P x} {yy : P y}
      (p : x = y)
  : (p # xx = yy) ≃ (xx = p #' yy).
Proof.
  exists (flip_transport_r p).
  apply equiv_from_qinv.
  exists (flip_transport'_r p).
  induction p; split; intro q;
    change _ with (xx=yy) in q; induction q; reflexivity.
Defined.




(* ** --   Paths of Simple Products are Simple Products of Paths   -- ** *)

Definition fsteq {A B : UU} {x y : A×B} (p : x=y) := ap fst p.
Definition sndeq {A B : UU} {x y : A×B} (p : x=y) := ap snd p.
Definition paireq {A B : UU} {a a' b b'}
           (p : a = a') (q : b = b')
  : (a,b) = (a',b')
  := ap2 (@pair A B) p q.

Definition prodeq_comp_fst {A B : UU} {a a' b b'}
           (p : a = a') (q : b = b')
  : @fsteq A B _ _ (paireq p q) = p.
Proof. unfold fsteq, paireq; autorewrite with ApPushdown;
         reflexivity. Defined.
Definition prodeq_comp_snd {A B : UU} {a a' b b'}
           (p : a = a') (q : b = b')
  : @sndeq A B _ _ (paireq p q) = q.
Proof. unfold sndeq, paireq; autorewrite with ApPushdown;
         reflexivity. Defined.
Definition prodeq_uniq {A B : UU} {a a' : A} {b b' : B}
           (p : (a, b) = (a', b'))
  : paireq (fsteq p) (sndeq p) = p.
Proof.
  (* wow, I did not realize you can solve problems by being this
     explicit.  Amazing *)
  exact (paths_rect (a,b)
                    (λ ab', match ab' with
                              (a',b') => λ p,
                                         paireq (fsteq p) (sndeq p) = p
                            end)
                    (idpath _) (a',b') p).
Defined.
Theorem prodeq_distribute {A B : UU} {a a' : A} {b b' : B}
  : ((a,b) = (a',b')) ≃ ( (a = a') × (b = b') ).
Proof.
  exists (λ p, (fsteq p, sndeq p)).
  apply equiv_from_qinv.
  exists (uncurry paireq).
  split; [intros (p,q) | intro p]; unfold uncurry, funcomp; simpl.
  - exact (paireq (prodeq_comp_fst p q) (prodeq_comp_snd p q)).
  - exact (prodeq_uniq p).
Defined.


(* ** --         Non-Dependent Pairs and the Path Groupoid         -- ** *)
(* ** --              Transport in Non-Dependent Pairs             -- ** *)
(* ** --            Functorality of Non-Dependent Pairs            -- ** *)

Lemma paireq_refl {A B : UU} {a:A} {b:B}
  : paireq (idpath a) (idpath b) = idpath (a,b).
Proof. unfold paireq; autorewrite with ApPushdown; trivial. Defined.
Lemma paireq_symm {A B : UU} {a a' : A} {b b' : B}
      {p : a = a'} {q : b = b'}
  : paireq (inv p) (inv q) = inv (paireq p q).
Proof. unfold paireq; autorewrite with ApPushdown; trivial. Defined.
Lemma paireq_trans {A B : UU} {a a' a'' : A} {b b' b'' : B}
      {p : a = a'} {p' : a' = a''}
      {q : b = b'} {q' : b' = b''}
  : paireq (p ∙ p') (q ∙ q') = paireq p q ∙ paireq p' q'.
Proof. unfold paireq; autorewrite with ApPushdown; trivial. Defined.

(* now we want to take advantage of the fibration notation scope... *)
Notation "A × B" := (λ x, (A x) × (B x)) : fibration_scope.

(* thm_2_6_4 *)
Theorem transport_prod {Z : UU} {A B : Z -> UU}
        {z w : Z} {p : z=w} {x : (A z)×(B z)}
  : transport (A×B)%fiber p x = (transport A p (fst x),
                                 transport B p (snd x)).
Proof. destruct p, x; reflexivity. Defined.
Theorem transport'_prod {Z : UU} {A B : Z -> UU}
        {z w : Z} {p : z=w} {y : (A w)×(B w)}
  : transport' (A×B)%fiber p y = (transport' A p (fst y),
                                  transport' B p (snd y)).
Proof. destruct y; destruct p; reflexivity. Defined.

Theorem ap_paireq {A B A' B' : UU} {a a' : A} {b b' : B}
        {p : a = a'} {q : b = b'}
        {g : A -> A'} {h : B -> B'}
  : ap (λ x, (g (fst x), h (snd x))) (paireq p q)
    = paireq (ap g p) (ap h q).
Proof. unfold paireq; autorewrite with ApPushdown; reflexivity. Defined.




(* ** -- Paths in a total space are a base path and path in a Fiber -- ** *)
(* note: we can choose whether to get the fiber-path in the
         fiber over the beginning of the path or over the end.
         These two choices are called `proj2eq` and `proj2eq'`.
         They are related to the question of whether we are
         transporting forward or backwards along the base path.
 *)

Definition proj1eq {A : UU} {P : A -> UU} {w w' : total P}
           (p : w = w') : w.1 = w'.1 := ap proj1 p.
Definition proj2eq {A : UU} {P : A -> UU} {w w' : total P}
           (p : w = w')
  : (proj1eq p) # w.2 = w'.2.
Proof. induction p; reflexivity. Defined.
Definition proj2eq' {A : UU} {P : A -> UU} {w w' : total P}
           (p : w = w')
  : w.2 = (proj1eq p) #' w'.2.
Proof. induction p; reflexivity. Defined.
(* get the base/fiber path breakdown as a dependent pair... *)
Definition projeq {A : UU} {P : A -> UU} {w w' : total P}
           (p : w = w')
  : Σ(p : w.1 = w'.1), p # w.2 = w'.2
  := { proj1eq p ; proj2eq p }.
Definition projeq' {A : UU} {P : A -> UU} {w w' : total P}
           (p : w = w')
  : Σ(p : w.1 = w'.1), w.2 = p #' w'.2
  := { proj1eq p ; proj2eq' p }.
Definition spaireq {A : UU} {P : A -> UU}
           {a a' : A} {b : P a} {b' : P a'}
           (p : a = a') (q : p # b = b')
  : {a;b} = {a';b'}.
Proof. induction p; induction q; reflexivity. Defined.
Definition spaireq' {A : UU} {P : A -> UU}
           {a a' : A} {b : P a} {b' : P a'}
           (p : a = a') (q : b = p #' b')
  : {a;b} = {a';b'}.
Proof. induction p; change _ with (b=b') in q;
         induction q; reflexivity. Defined.

Definition sigeq_compute1 {A : UU} {P : A -> UU}
           {a a' : A} {b : P a} {b' : P a'}
           (p : a=a') (q : p # b = b')
  : proj1eq (spaireq p q) = p.
Proof. induction p; induction q; reflexivity. Defined.
Definition sigeq'_compute1 {A : UU} {P : A -> UU}
           {a a' : A} {b : P a} {b' : P a'}
           (p : a=a') (q : b = p #' b')
  : proj1eq (spaireq' p q) = p.
Proof. induction p; change _ with (b=b') in q;
         induction q; reflexivity. Defined.
Definition sigeq_compute2 {A : UU} {P : A -> UU}
           {a a' : A} {b : P a} {b' : P a'}
           (p : a=a') (q : p # b = b')
  :  transport (λ p', p' # b = b')
               (sigeq_compute1 p q) (proj2eq (spaireq p q))
     = q.
Proof. induction p; induction q; reflexivity. Defined.
Definition sigeq'_compute2 {A : UU} {P : A -> UU}
           {a a' : A} {b : P a} {b' : P a'}
           (p : a=a') (q : b = p #' b')
  :  (proj2eq' (spaireq' p q))
     = transport' (λ p', b = p' #' b') (sigeq'_compute1 p q) q.
Proof. induction p; change _ with (b=b') in q;
         induction q; reflexivity. Defined.
Definition sigeq_compute {A : UU} {P : A -> UU}
           {a a' : A} {b : P a} {b' : P a'}
           (pq : Σ (p : a=a'), p # b = b')
  : projeq (siguncurry spaireq pq) = pq.
Proof. destruct pq as (p,q);
         exact ( spaireq (sigeq_compute1 p q)
                          (sigeq_compute2 p q) ). Defined.
Definition sigeq'_compute {A : UU} {P : A -> UU}
           {a a' : A} {b : P a} {b' : P a'}
           (pq : Σ (p : a=a'), b = p #' b')
  : projeq' (siguncurry spaireq' pq) = pq.
Proof. destruct pq as (p,q);
         exact ( spaireq' (sigeq'_compute1 p q)
                           (sigeq'_compute2 p q) ). Defined.
Definition sigeq_uniq {A : UU} {P : A -> UU}
           {a a' : A} {b : P a} {b' : P a'}
           (p : {a;b} = {a';b'})
  : spaireq (proj1eq p) (proj2eq p) = p.
Proof. induction p; reflexivity. Defined.
Definition sigeq'_uniq {A : UU} {P : A -> UU}
           {a a' : A} {b : P a} {b' : P a'}
           (p : {a;b} = {a';b'})
  : spaireq' (proj1eq p) (proj2eq' p) = p.
Proof. induction p; reflexivity. Defined.
Theorem sigeq_distribute {A : UU} {P : A -> UU}
        {a a' : A} {b : P a} {b' : P a'}
  : ({a;b} = {a';b'}) ≃ Σ(p : a = a'), p # b = b'.
Proof.
  exact { projeq ;
          equiv_from_qinv {
              siguncurry spaireq ; (sigeq_compute,sigeq_uniq)
            }
        }.
Defined.
Theorem sigeq'_distribute {A : UU} {P : A -> UU}
        {a a' : A} {b : P a} {b' : P a'}
  : ({a;b} = {a';b'}) ≃ Σ(p : a = a'), b = p #' b'.
Proof.
  exact { projeq' ;
          equiv_from_qinv {
              siguncurry spaireq' ; (sigeq'_compute,sigeq'_uniq)
            }
        }.
Defined.


(* ** --           Dependent Pairs and the Path Groupoid           -- ** *)

Lemma projeq_refl {A : UU} {P : A -> UU} {z : total P}
  : projeq (idpath z) = { idpath z.1 ; idpath z.2 }.
Proof. reflexivity. Defined.
Lemma projeq'_refl {A : UU} {P : A -> UU} {z : total P}
  : projeq' (idpath z) = { idpath z.1 ; idpath z.2 }.
Proof. reflexivity. Defined.
Lemma proj1eq_symm {A : UU} {P : A -> UU} {w w' : total P}
      {p : w = w'}
  : proj1eq (inv p) = inv (proj1eq p).
Proof. apply ap_inv. Defined.
Lemma proj2eq_symm {A : UU} {P : A -> UU} {w w' : total P}
      {p : w = w'}
  : proj2eq (inv p) = inv (proj2eq' p
                                    ∙ transport_paths' proj1eq_symm).
Proof. induction p; reflexivity. Defined.
Lemma proj2eq'_symm {A : UU} {P : A -> UU} {w w' : total P}
      {p : w = w'}
  : proj2eq' (inv p) = inv ((transport_paths (ap inv proj1eq_symm))
                              ∙ (transport_paths
                                   (path_inverse_inverse (proj1eq p)))
                              ∙ proj2eq p
                           ).
Proof. induction p; reflexivity. Defined.
Lemma proj1eq_trans {A : UU} {P : A -> UU} {w w' w'' : total P}
      {p : w = w'} {q : w' = w''}
  : proj1eq (p∙q) = proj1eq p ∙ proj1eq q.
Proof. apply ap_path_compose. Defined.
Lemma proj2eq_trans {A : UU} {P : A -> UU} {w w' w'' : total P}
      {p : w = w'} {q : w' = w''}
  : proj2eq (p∙q) = (transport_paths proj1eq_trans)
                      ∙ (inv (transport_twice _ _ _))
                      ∙ (ap (transport P (proj1eq q))
                            (proj2eq p) )
                      ∙ proj2eq q.
Proof. induction p, q; reflexivity. Defined.
Lemma proj2eq'_trans {A : UU} {P : A -> UU} {w w' w'' : total P}
      {p : w = w'} {q : w' = w''}
  : proj2eq' (p∙q) = (proj2eq' p)
                       ∙ (ap (transport' P (proj1eq p))
                             (proj2eq' q) )
                       ∙ transport'_twice _ _ _
                       ∙ transport'_paths (inv proj1eq_trans).
Proof. induction p, q; reflexivity. Defined.

Lemma spaireq_refl {A : UU} {P : A -> UU}
      {a : A} {b : P a}
  : spaireq (idpath a) (idpath b) = idpath {a;b}.
Proof. reflexivity. Defined.
Lemma spaireq'_refl {A : UU} {P : A -> UU}
      {a : A} {b : P a}
  : spaireq' (idpath a) (idpath b) = idpath {a;b}.
Proof. reflexivity. Defined.
Lemma spaireq_symm {A : UU} {P : A -> UU}
      {a a' : A} {b : P a} {b' : P a'}
      (p : a = a') (q : b = p #' b')
  : spaireq (inv p) (inv q) = inv (spaireq' p q).
Proof. induction p; change _ with (b=b') in q;
         induction q; reflexivity. Defined.
Lemma spaireq'_symm {A : UU} {P : A -> UU}
      {a a' : A} {b : P a} {b' : P a'}
      (p : a = a') (q : p # b = b')
  : spaireq' (inv p) (inv q ∙ transport_paths' (path_inverse_inverse p))
    = inv (spaireq p q).
Proof. induction p; change _ with (b=b') in q;
         induction q; reflexivity. Defined.
Lemma spaireq_trans {A : UU} {P : A -> UU}
      {a a' a'' : A} {b : P a} {b' : P a'} {b'' : P a''}
      (p : a = a') (p' : a' = a'')
      (q : p # b = b') (q' : p' # b' = b'')
  : spaireq (p ∙ p') (inv (transport_twice _ _ _)
                           ∙ ap (transport P p') q
                           ∙ q')
    = (spaireq p q)
        ∙ (spaireq p' q').
Proof. induction p; change _ with (b=b') in q;
         induction q; reflexivity. Defined.
Lemma spaireq'_trans {A : UU} {P : A -> UU}
      {a a' a'' : A} {b : P a} {b' : P a'} {b'' : P a''}
      (p : a = a') (p' : a' = a'')
      (q : b = p #' b') (q' : b' = p' #' b'')
  : spaireq' (p ∙ p') (q
                          ∙ ap (transport' P p) q'
                          ∙ transport'_twice _ _ _)
    = (spaireq' p q)
        ∙ (spaireq' p' q').
Proof. induction p; change _ with (b=b') in q;
         induction q; autorewrite with PathGroupoid ApPushdown;
           reflexivity. Defined.


(* ** --     Lifting paths into the total space of a Fibration     -- ** *)
(* ** --              Transport in Non-Dependent Pairs             -- ** *)
(* ** --            Functorality of Non-Dependent Pairs            -- ** *)
Corollary sig_uniq {A : UU} {P : A -> UU} {z : Σ x:A, P x}
  : { z.1 ; z.2 } = z.
Proof. exact (spaireq idpath idpath). Defined.

Corollary lift {A : UU} {P : A -> UU} {x y : A}
          (u : P x) (p : x = y)
  : {x; u} = {y; p#u} :> total P.
Proof. exact (spaireq p idpath). Defined.
Corollary lift' {A : UU} {P : A -> UU} {x y : A}
          (v : P y) (p : x = y)
  : {x; p#'v} = {y; v} :> total P.
Proof. exact (spaireq' p idpath). Defined.

Definition sig_fiber {X : UU} (P : X -> UU) (Q : (total P) -> UU)
  : fibration X := λ x, Σ (u : P x), Q{x;u}.
Theorem transport_sig {A : UU} (P : A -> UU) (Q : (total P) -> UU)
        {x y : A} (p : x=y) (uz : sig_fiber P Q x)
  : transport (sig_fiber P Q) p uz
    = 
    { transport P p uz.1 ; transport Q (lift uz.1 p) uz.2 }.
Proof. induction p; reflexivity. Defined.
Theorem transport'_sig {A : UU} (P : A -> UU) (Q : (total P) -> UU)
        {x y : A} (p : x=y) (uz : sig_fiber P Q y)
  : transport' (sig_fiber P Q) p uz
    = 
    { transport' P p uz.1 ; transport' Q (lift' uz.1 p) uz.2 }.
Proof. induction p; reflexivity. Defined.

Theorem ap_spaireq {A A' : UU} (B : A -> UU) (B' : A' -> UU)
          {a1 a2 : A} {b1 : B a1} {b2 : B a2}
          {p : a1 = a2} {q : p # b1 = b2}
          (g : A -> A') (h : ∏ x:A, B x -> B' (g x))
  : ap (λ w, { g w.1 ; h w.1 w.2 }) (spaireq p q)
    = spaireq (ap g p) ((inv (transport_apeq g p (h a1 b1)))
                           ∙ (transport_comm_f h p b1)
                           ∙ ap (h a2) q).
Proof. induction p, q; reflexivity. Defined.
Theorem ap_spaireq' {A A' : UU} (B : A -> UU) (B' : A' -> UU)
          {a1 a2 : A} {b1 : B a1} {b2 : B a2}
          {p : a1 = a2} {q : b1 = p #' b2}
          (g : A -> A') (h : ∏ x:A, B x -> B' (g x))
  : ap (λ w, { g w.1 ; h w.1 w.2 }) (spaireq' p q)
    = spaireq' (ap g p) (ap (h a1) q
                             ∙ inv (transport_comm_f h (inv p) b2)
                             ∙ transport'_apeq g p (h a2 b2)).
Proof. induction p; change _ with (b1=b2) in q;
         induction q; reflexivity. Defined.




(* ** --               Paths in Unit (𝟙) are Trivial               -- ** *)

(* thm_2_8_1 *)
(* most of the components are useless, but sometimes uniteq
   is nice to have constructively without having to mangle
   induction tactics *)
Lemma uniteq (x y : 𝟙) : x = y.
Proof. induction x, y; reflexivity. Defined.
Theorem uniteq_is_unit {x y : 𝟙}
  : (x=y) ≃ 𝟙.
Proof.
  exists (λ _, tt).
  apply equiv_from_qinv.
  exists (λ _, uniteq x y).
  split; [ intro u; destruct u | intro q; destruct q; destruct x ];
    reflexivity.
Qed.




(* ** --      Equality of Functions is equality at all points      -- ** *)

Definition happly {A : UU} {B : A -> UU} {f g : ∏ x:A, B x}
  : (f = g) -> ∏ x:A, f x = g x.
Proof. intros p x; induction p; reflexivity. Defined.

(* we rarely use this axiom directly.  It is re-/de-constructed below *)
Axiom funext_qinv : forall (A : UU) (B : A -> UU) (f g : ∏ x:A, B x),
    qinv (@happly A B f g).

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


(* ** --       Function Extensionality and the Path Groupoid       -- ** *)
(* ** --                Transport in Function Spaces               -- ** *)

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
    λ x : A x2, transport B p (f (transport' A p x)).
Proof. destruct p; reflexivity. Defined.
Lemma transport'_f {X : UU} {x1 x2 : X} (A B : X -> UU)
      (p : x1=x2) (f : A x2 -> B x2)
  : transport' (A -> B)%fiber p f
    =
    λ x : A x1, transport' B p (f (transport A p x)).
Proof. destruct p; reflexivity. Defined.

Definition pi_fiber {X:UU} (A : X -> UU) (B : ∏ x:X, A x -> UU)
  : fibration X
  := λ x, ∏ a : A x, B x a.
Definition hat_fiber {X:UU} {A : X -> UU} (B : ∏ x:X, A x -> UU)
  : fibration (total A)
  := siguncurry B.

Lemma transport_d {X : UU} {x1 x2 : X}
      (A : X -> UU) (B : ∏ x:X, A x -> UU)
      (p : x1=x2) (f : pi_fiber A B x1) (a : A x2)
  : transport (pi_fiber A B) p f a
    =
    transport (hat_fiber B) (lift' a p) (f (p #' a)).
Proof. induction p; reflexivity. Defined.
Lemma transport'_d {X : UU} {x1 x2 : X}
      (A : X -> UU) (B : ∏ x:X, A x -> UU)
      (p : x1=x2) (f : pi_fiber A B x2) (a : A x1)
  : transport' (pi_fiber A B) p f a
    =
    transport' (hat_fiber B) (lift a p) (f (p#a)).
Proof. induction p; reflexivity. Defined.

(* Note that when we have dependent pairs of paths, the fiber-path
   always has the form  (p # x) = y  or  x = (p #' y) .
   That is, these particular forms of equality arise relatively
   naturally.  The following Lemmas treat these forms in the case
   that the objects x,y are (dependent) functions.  They show
   that such _families_ of function equalities are equivalent to
   families of homotopies where transport has been more balanced
   between the left and right sides of the equation.
 *)

(* lem_2_9_6 *)
Lemma transport_f_as_homotopy {X : UU} {x y : X} {A B : X -> UU} {p : x=y}
      {f : A x -> B x} {g : A y -> B y}
  : (transport (A -> B)%fiber p f = g)
      ≃
      ∏ a : A x, p#(f a) = g (p#a).
Proof. induction p; apply funext_equiv. Defined.
Lemma transport'_f_as_homotopy {X : UU} {x y : X} {A B : X -> UU} {p : x=y}
      {f : A x -> B x} {g : A y -> B y}
  : ( f = transport' (A->B)%fiber p g )
      ≃
      ∏ a : A y, f (p #' a) = p #' (g a).
Proof. induction p; apply funext_equiv. Defined.
(* lem_2_9_7 *)
Lemma transport_d_as_homotopy {X : UU} {A : X -> UU} {B : ∏ x:X, A x -> UU}
      {x y : X} {p : x=y}
      {f : pi_fiber A B x} {g : pi_fiber A B y}
  : (transport (pi_fiber A B) p f = g)
      ≃
      (∏ a : A x, transport (hat_fiber B) (lift a p) (f a)
                  =
                  g (p # a)).
Proof. induction p; apply funext_equiv. Defined.
Lemma transport'_d_as_homotopy {X : UU} {A : X -> UU} {B : ∏ x:X, A x -> UU}
      {x y : X} {p : x=y}
      {f : pi_fiber A B x} {g : pi_fiber A B y}
  : ( f = transport' (pi_fiber A B) p g )
      ≃
      (∏ a : A y, f (p #' a)
                  =
                  transport' (hat_fiber B) (lift' a p) (g a)).
Proof. induction p; apply funext_equiv. Defined.




(* ** --                        Univalence                        -- ** *)
(* I depart from the book somewhat here.
   We get a more consistent and useful definition of idtoeqv
   if we base it on an earlier general result about transport
   yielding equivalences *)
Definition idtoeqv {A B : UU}
  : (A = B) -> (A ≃ B).
Proof. intro p; exists (transport idfun p);
         apply (transport_is_an_eqv idfun p). Defined.

Axiom idtoeqv_isequiv : forall A B : UU, isequiv (@idtoeqv A B).
Definition Univalence {A B : UU}
  : (A = B) ≃ (A ≃ B)
  := { @idtoeqv A B ; idtoeqv_isequiv A B }.

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
  : transport idfun (ua e) = e.1
  := ap proj1 (ua_compute e).

Lemma idtoeqv_symm {A B : UU} {p : A = B}
  : idtoeqv (inv p) = einv (idtoeqv p).
Proof. induction p; reflexivity. Defined.
Lemma idtoeqv_trans {A B C : UU} {p : A = B} {q : B = C}
  : idtoeqv (p ∙ q) = equiv_trans (idtoeqv p) (idtoeqv q).
Proof. induction p; induction q; reflexivity. Defined.

Lemma ua_refl {A : UU}
  : idpath A = ua (@equiv_refl A).
Proof. apply (@ua_uniq A A). Defined.
Lemma ua_symm {A B : UU} {f : A ≃ B}
  : inv (ua f) = ua (einv f).
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

Lemma transport_as_idtoeqv {A : UU} {B : A -> UU} {x y : A}
      {p : x=y} (u : B x)
  : transport B p u = (idtoeqv (ap B p)).1 u.
Proof. apply @transport_apeq with (P := idfun) (f := B). Defined.




(* ** --               Path Spaces / Identity Types               -- ** *)
(* this is an extension of natural_homotopy that allows
   for application instances to be hidden in a left-associated
   chain of path compositions, which is how things tend to arise
 *)
Lemma natgen_homotopy {A B : UU} {a a' : A} {b : B}
      (p : a = a') (f g : A -> B) {q : b = f a} (H : f ~ g)
  : q ∙ (H a) ∙ (ap g p) = q ∙ (ap f p) ∙ (H a').
Proof.
  rewrite <- path_compose_assoc;
    rewrite (natural_homotopy p f g H);
    autorewrite with PathGroupoid; reflexivity.
Defined.

Theorem ap_isequiv {A B : UU} (f : A -> B)
        {a a' : A} (fe : isequiv f)
  : (a = a') ≃ (f a = f a').
Proof.
  apply qinv_from_equiv in fe as fq.
  destruct fq as (g, (R, L)).
  exists (ap f); apply equiv_from_qinv.
  exists (λ p, (inv (L a)) ∙ (ap g p) ∙ (L a') ).
  split; [ intro q | intro p ]; unfold funcomp.
  {
    chain ( inv (R (f (idfun a))) ∙ R (f (idfun a))
                ∙ ap idfun (ap f (inv (L a) ∙ ap g q ∙ L a'))
                ∙ inv (R (f a')) ∙ R (f a') )
      by rewrite ap_idfun; autorewrite with PathGroupoid; reflexivity.
    chain ( inv (R (f a))
                ∙ ap f (idpath ((g∘f) a)
                               ∙ ap g (ap f (inv (L a) ∙ ap g q ∙ L a')))
                ∙ R (f a') ).
    rewrite (natgen_homotopy
               (ap f (inv (L a) ∙ ap g q ∙ L a'))
               _ _ R).
    autorewrite with PathGroupoid.
    rewrite <- ap_func_compose.
    reflexivity.
    chain ( inv (R (f a))
                ∙ ap f (L a ∙ inv (L a) ∙ ap g q
                          ∙ L a' ∙ inv (L a'))
                ∙ R (f a') ).
    apply whisker_r; apply whisker_l; apply (ap (ap f));
      (* note this composes a different pair than just was decomposed *)
      rewrite ap_func_compose;
      rewrite <- (path_inverse_l (inv (L a)));
      rewrite (natgen_homotopy (inv (L a) ∙ ap g q ∙ L a')
                               _ _ (λ x, inv (L x)));
      rewrite ap_idfun; autorewrite with PathGroupoid; trivial.
    chain (inv (R (f a)) ∙ ap f (ap g q) ∙ R (f a'))
      by autorewrite with PathGroupoid; trivial.
    (* final equation to solve *)
    rewrite ap_func_compose; rewrite <- (natgen_homotopy q _ _ R);
      rewrite ap_idfun; autorewrite with PathGroupoid; trivial.
  }
  {
    rewrite ap_func_compose;
      rewrite <- (natgen_homotopy p _ _ L);
      rewrite ap_idfun;
      autorewrite with PathGroupoid; trivial.
  }
Qed.

Example prod_eq_equiv {A B : UU} {a a' : A} {b b' : B}
        (p q : (a,b)=(a',b'))
  : (p = q) ≃ (fsteq p = fsteq q)×(sndeq p = sndeq q).
Proof.
  set (E := ua (@ap_isequiv _ _ _ p q prodeq_distribute.2)).
  rewrite E.
  apply prodeq_distribute.
Qed.

Example dep_eq_equiv {A : UU} {B : A -> UU} {f g : ∏ x:A, B x}
        (p q : f=g)
  : (p = q) ≃ ∏ x:A, happly p x = happly q x.
Proof.
  set (E := ua (@ap_isequiv _ _ happly p q funext_equiv.2)).
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

(* thm_2_11_3 *)
Theorem transport_eq_f {A B : UU} {a a' : A} {f g : A -> B}
         (p : a=a') (q : f a = g a)
  : transport (λ x, f x = g x) p q = inv (ap f p) ∙ q ∙ ap g p.
Proof. destruct p; autorewrite with PathGroupoid; reflexivity. Defined.
(* thm_2_11_4 *)
Theorem transport_eq_d {A : UU} {B : A -> UU} {f g : ∏ x:A, B x}
        {a a' : A} (p : a=a') (q : f a = g a)
  : transport (λ x, f x = g x) p q
    = inv (apd f p) ∙ ap (transport B p) q ∙ apd g p.
Proof. destruct p; simpl; autorewrite with PathGroupoid;
         rewrite ap_idfun; reflexivity. Defined.
(* thm_2_11_5 *)
Theorem transport_loop {A : UU} {a a' : A}
        (p : a = a') (q : a = a) (r : a' = a')
  : (transport (λ x, x = x) p q = r) ≃ (q ∙ p = p ∙ r).
Proof. destruct p; simpl; autorewrite with PathGroupoid;
         apply equiv_refl. Defined.




(* ** --   Coproduct Interaction with Equality via Encode/Decode   -- ** *)
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

Remark true_is_not_false : true ≠ false.
Proof.
  intro e; apply (ap bool_is_unit_plus_unit.1) in e; simpl in e.
  apply (encode_coprod_r tt (inl tt) e).
Defined.




(* ** --         Natural Number Equality via Encode/Decode         -- ** *)
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
    = e.1 (m ((einv e).1 b1) ((einv e).1 b2)).
Proof. unfold induced_mult, Binop.
       repeat rewrite transport_f.
       repeat rewrite ua_symm.
       repeat rewrite ua_compute_transport.
       trivial.
Defined.




(* ** --                 Some Universal Properties                 -- ** *)
Definition fstf {X A B : UU} (f : X -> A×B) : X -> A := fst ∘ f.
Definition sndf {X A B : UU} (f : X -> A×B) : X -> B := snd ∘ f.

Theorem univf_prod {X A B : UU}
  : (X -> A×B) ≃ (X -> A)×(X -> B).
Proof.
  exists (λ f, (fstf f, sndf f)).
  apply equiv_from_qinv.
  exists (λ gh : (X->A)×(X->B), λ x, ((fst gh) x, (snd gh) x))%type.
  split; unfold fstf, sndf, funcomp; simpl; [ intro gh | intro f ].
  - eta_reduce; rewrite prod_uniq; trivial.
  - apply funext; intro x; rewrite prod_uniq; trivial.
Defined.

Definition fstd {X : UU} {A B : X -> UU} (f : ∏ x:X, (A x) × (B x))
  : ∏ x:X, A x := λ x, fst (f x).
Definition sndd {X : UU} {A B : X -> UU} (f : ∏ x:X, (A x) × (B x))
  : ∏ x:X, B x := λ x, snd (f x).

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

Theorem univ_sig {X : UU} {A : X -> UU} {P : ∏ x:X, A x -> UU}
  : (∏ x:X, Σ a : A x, P x a)
      ≃
      (Σ (g : ∏ x:X, A x), ∏ x:X, P x (g x)).
Proof.
  set (fwd := λ f : (∏ x:X, Σ a : A x, P x a),
                    (spair (λ g, ∏ x:X, P x (g x))
                           (λ x:X, (f x).1)
                           (λ x:X, (f x).2)) ).
  exists fwd.
  apply equiv_from_qinv.
  set (rev := λ gh : (Σ (g : ∏ x:X, A x), ∏ x:X, P x (g x)),
                     λ x:X, spair (P x) (gh.1 x) (gh.2 x) ).
  exists rev.
  split; unfold funcomp, fwd, rev; [ intro gh | intro f ]; simpl.
  - eta_reduce; rewrite <- sig_uniq; trivial.
  - apply funext; intro; rewrite <- sig_uniq; trivial.
Defined.

(* note these are currying and uncurrying... *)
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

