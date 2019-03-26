Require Import  Coq.Program.Equality. (* enables "dependent induction" *)
Require Import Setoid.

Ltac verysimple := easy.

Definition UU := Type.

Identity Coercion fromUUtoType : UU >-> Sortclass.

Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* type this in emacs in agda-input method with \prod *)

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).
(* type this in emacs in agda-input method with \lambda *)


Definition compose {A B C: UU} (f: A -> B) (g: B -> C): A -> C.
Proof. intro a. now apply g, f. Defined.

Record total2 { T: UU } ( P: T -> UU ): UU := 
  tpair 
  { pr1 : T;
    pr2 : P pr1 
  }.

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

Notation "{ x ; .. ; y ; z }" := (tpair _ x .. (tpair _ y z) ..).

Notation "'∑'  x .. y , P" := (total2 (λ x, .. (total2 (λ y, P)) ..))
(at level 200, x binder, y binder, right associativity) : type_scope.

(* paths *)
Inductive Id {A: UU}: A -> A -> UU: UU :=
  refl: forall a, Id a a.
Arguments refl {A a} , [A] a.

Print Id_rect.

Definition Id_eql: ∏ {A: UU} (a b: A), Id a b -> a = b.
Proof. intros A a b p. now induction p. Defined.

Definition Id_eqr: ∏ {A: UU} (a b: A), a = b -> Id a b.
Proof. intros A a b p. now rewrite p. Defined.

(* groupoid structure *)

Definition inverse {A: UU} {a b: A}: Id a b -> Id b a.
Proof. intro p. now induction p. Defined.

Definition concat {A: UU} {a b c: A}: Id a b -> Id b c -> Id a c.
Proof. intros p q. now induction p; induction q. Defined.

Definition symm {A: UU} {a b: A}: Id a b -> Id b a.
Proof. intro p. now induction p. Defined.
(* /groupoid structure *)

Definition ap {A B: UU} {a b: A} (f: A -> B): Id a b -> Id (f a) (f b).
Proof. intro p. now induction p. Defined.

(** prove ap + concat, ap + inverse basics here *)
Lemma ap_refl: ∏ {A B: UU} {a: A} (f: A -> B), Id (ap f (refl a)) (refl (f a)).
Proof. intros. now cbn. Defined.

Lemma app_concat: ∏ {A B: UU} {a b c: A} (f: A -> B) (p: Id a b) (q: Id b c),
Id (ap f (concat p q)) (concat (ap f p) (ap f q)).
Proof. intros. now induction p, q. Defined.

Lemma concat_inverse_l: ∏ {A: UU} (a b: A) (p: Id a b),
  Id (concat (inverse p) p) refl.
Proof. intros. now induction p. Defined.

Lemma concat_inverse_r: ∏ {A: UU} (a b: A) (p: Id a b), Id (concat p (inverse p)) refl.
Proof. intros. now induction p. Defined.
(* /paths *)

(* transport and facts *)
(** dependent application -- dependent lifting requires transport *)
Definition transport {A: UU} (P: A -> UU) {a b: A} (p: Id a b): P a -> P b.
Proof. now induction p. Defined.

Definition apd {A: UU} {P: A -> UU} (f: ∏ a: A, P a) {a b: A} (p: Id a b): 
  Id (transport P p (f a)) (f b).
Proof. now induction p. Defined.

(** h235 *)
Definition transportconst {A: UU} (B: UU) {a b: A} (p: Id a b) (c: B):
  Id (@transport A (λ a, B) a b p c) c.
Proof. now induction p. Defined.

Definition constr1 {X : UU} (P : X -> UU) {x x' : X} (e : Id x x') :
  ∑ (f : P x -> P x'),
  ∑ (ee : ∏ p : P x, (Id (tpair _ x p) (tpair _ x' (f p)))), ∏ (pp : P x), Id (ap pr1 (ee pp)) e.
Proof. induction e. 
       unshelve econstructor.
       - exact id.
       - unshelve econstructor; easy.
Defined.

Definition transportf {X : UU} (P : X -> UU) {x x' : X} (e: Id x x'): 
  P x -> P x' := pr1 (constr1 P e).

Definition transportD {A: UU} (B: A -> UU) (C: ∏ a : A, B a -> UU)
           {x1 x2: A} (p: Id x1 x2) (y: B x1) (z: C x1 y): C x2 (transportf _ p y).
Proof. now induction p. Defined.

Lemma transport_eq: ∏ {X : UU} (P : X -> UU) {x x' : X} (e: Id x x'),
  Id (transport P e) (transportf P e).
Proof. intros. now induction e. Defined.

(** Armin's thesis => lift *)
Lemma h1167: ∏ {A: UU} (P: A -> UU) {x y: A} (u: P x) (p: Id x y), 
  Id (tpair _ x u) (tpair _ y (transport P p u)).
Proof. intros. now induction p. Defined.

(** h238 *)
Definition apdconst {A B: UU} (f: A -> B) {a b: A} (p: Id a b):
  Id (apd f p) (concat (transportconst B p (f a)) (ap f p)).
Proof. now induction p. Defined.

Lemma transport_refl: ∏ {A: UU} {P: A -> UU} {a b: A} (p: Id a b) (u: P a),
  Id (transport P refl u) u.
Proof. intros. now induction p. Defined.

(* diprect products *)
Definition dirprod (A B : UU): UU := ∑ a: A, B.
(* /direct products *)

(* hompotopy *)
Definition homotopy {A: UU} {P: A -> UU} (f g: (∏ a: A, P a)): UU :=
  ∏ a: A, Id (f a) (g a).
(* /hompotopy *)

(* equivalences *)
Definition qinv {A B: UU} (f: A -> B): UU :=
  ∑ (g: B -> A), (dirprod (homotopy (compose g f) (@id B))
                          (homotopy (compose f g) (@id A))).

Definition isequiv {A B: UU} (f: A -> B): UU :=
  dirprod (∑ (g: B -> A),(homotopy (compose g f) (@id B))) 
          (∑ (h: B -> A),(homotopy (compose f h) (@id A))).


Definition ishae {A B: UU} (f: A -> B) :=
  ∑ g: B -> A, 
    ∑ eta: (homotopy (compose f g) (@id A)),
    ∑ eps: (homotopy (compose g f) (@id B)),
      ∏ x: A, Id (ap f (eta x)) (eps (f x)).

Example h249_i: ∏ {A B: UU} {f: A -> B}, qinv f -> isequiv f.
Proof. intros A B f eq.
       destruct eq as (g, (pd1, pd2)).
       unshelve econstructor.
       - exists g. exact pd1.
       - exists g. exact pd2.
Defined.

Example h249_ii: ∏  {A B: UU} {f: A -> B}, isequiv f -> qinv f.
Proof. intros A B f eq.
       destruct eq as ((g, alpha), (h, beta)).
       unshelve econstructor.
       - exact g.
       - unshelve econstructor.
         + exact alpha.
         + intro a. compute in *.
           pose proof beta as beta'.
           specialize (beta (g (f a))).
           apply Id_eql in beta.
           specialize (alpha (f a)).
           apply Id_eql in alpha. 
           rewrite alpha in beta.
           now rewrite <- beta.
Defined.

(** ~= *)
Definition Equiv (A B: UU): UU := (∑ f: A -> B, isequiv f).

Lemma h2412_i: ∏ {A: UU}, Equiv A A.
Proof. intro A.
       unshelve econstructor.
       - exact id.
       - unshelve econstructor.
         + exists id. now compute.
         + exists id. now compute.
Defined.

Lemma h2412_ii: ∏ {A B: UU} (f: Equiv A B), Equiv B A.
Proof. intros.
       destruct f as (f, equivf).
       apply h249_ii in equivf.
       destruct equivf as (invf, (alpha, beta)).
       unshelve econstructor.
       - exact invf.
       - unshelve econstructor.
         + exists f. exact beta.
         + exists f. exact alpha.
Defined.

Lemma h2412_iii: ∏ {A B C: UU} (f: Equiv A B) (g: Equiv B C), Equiv A C.
Proof. intros.
       destruct f as (f, iseqf).
       destruct g as (g, iseqg).
       unshelve econstructor.
       - exact (compose f g).
       - apply h249_ii in iseqf.
         apply h249_ii in iseqg.
         destruct iseqf as (finv, (alpha_f, beta_f)).
         destruct iseqg as (ginv, (alpha_g, beta_g)).
         unshelve econstructor.
         + exists (compose ginv finv).
           compute in *.
           intro c.
           assert (g (f (finv (ginv c))) = c).
           { specialize (alpha_f (ginv c)).
             apply Id_eql in alpha_f.
             rewrite alpha_f. 
             specialize (alpha_g c).
             now apply Id_eql in alpha_g.
           }
           now rewrite H.
         + exists (compose ginv finv).
           compute in *.
           intro a.
           assert ((finv (ginv (g (f a)))) = a).
           { specialize (beta_g (f a)).
             apply Id_eql in beta_g.
             rewrite beta_g. 
             specialize (beta_f a).
             now apply Id_eql in beta_f.
           }
           now rewrite H.
Defined.

(*/equivalences *)

(*
Fail Inductive Rec (A : Type) :=
  In : (Rec A -> A) -> Rec A.

Inductive Rec (A : Type) :=
  In : (A -> A) -> Rec A.

Fail Definition Y {A: Type} := 
  λ f: (A -> A -> Type) => (λ x:A => (f x x)) (λ x:A => (f x x)).
*)

(* axioms *)

(* FUNEXT *)
Definition happly {A: UU} {B: A -> UU} (f g: ∏x: A, B x): (Id f g) -> homotopy f g.
Proof. intros p a. now induction p. Defined.

(** h293 *)
Definition funext_def_qinv: UU := ∏  (A: UU) (B: A -> UU) (f g: ∏x:A, B x),
  qinv (@happly A B f g).
Axiom FE: funext_def_qinv.

Definition funext {A: UU} {B: A -> UU} {f g: ∏ x: A, B x}: (∏ x: A, Id (f x) (g x)) -> Id f g.
Proof. destruct (FE A B f g) as (inv_happly, cc2).
       exact inv_happly.
(*     exact (pr1 (FE A B f g)). *)
Defined.

Definition funext_def_isequiv : ∏  (A: UU) (B: A -> UU) (f g: ∏x:A, B x),
  isequiv (@happly A B f g).
Proof. intros. apply h249_i.
       exact (FE A B f g).
Defined.

Definition happly_funext {A: UU} {B: A -> UU} {f g: ∏ x:A, B x} 
                         (h: ∏ x:A, Id (f x) (g x)): Id (happly _ _ (funext h)) h.
Proof. unfold funext.
       destruct (FE A B f g) as (inv_happly, cc).
       destruct cc as (cc1, cc2).
       unfold homotopy, compose, id in cc2.
       exact (cc1 h).
(*     exact ((pr1 (pr2 (FE A B f g)) h)). *)
Defined.

Definition funext_happly {A: UU} {B: A -> UU} {f g: ∏ x: A, B x} 
                         (p: Id f g): Id (funext (happly _ _ p)) p.
Proof. unfold funext.
       destruct (FE A B f g) as (inv_happly, cc).
       destruct cc as (cc1, cc2).
       unfold homotopy, compose, id in cc2.
       exact (cc2 p).
(*     exact (pr2 (pr2 (FE A B f g)) p). *)
Defined.

(* UA *)
Definition idtoeqv: ∏ {A B: UU}, Id A B -> Equiv A B.
Proof. intros A B p.
       exists (transport (@id UU) p).
(*     apply transport_isequiv with (P := idU). (** defines it *) *)
       apply h249_i.
       unshelve econstructor.
       + exact (transport _ (inverse p)).
       + now induction p.
Defined.

(** Definition UA_def: UU :=  Equiv (Equiv A B) (Id A B). *)
Definition UA_def: UU := ∏ (A B: UU), isequiv (@idtoeqv A B).
Axiom UA: UA_def.

Definition ua {A B : UU}: (Equiv A B) -> (Id A B).
Proof. destruct (h249_ii (UA A B)) as (eqvtoid, cc).
       exact eqvtoid.
(*     exact (pr1 (h249_ii (UA A B))). *)
Defined.

Definition ua_f {A B : UU} (f: A-> B): (isequiv f) -> (Id A B).
Proof. intro e.
       destruct (h249_ii (UA A B)) as (eqvtoid, cc).
       apply eqvtoid.
       exists f. exact e.
(*     exact (pr1 (h249_ii (UA A B))). *)
Defined.

(* /axioms *)


(* homotopy levels *)
Definition fiber  {A B: UU} (f: A -> B) (y: B): UU := ∑ x: A, Id (f x) y.
Definition isSurj {A B: UU} (f: A -> B): UU := ∏ (y: B), fiber f y.
(** total *)
Definition totalA {A: UU} (P Q: A -> UU) (f: ∏ x: A, P x -> Q x): (∑ x: A, P x) -> (∑ x: A, Q x).
Proof. intro w. exact { (pr1 w); (f (pr1 w) (pr2 w)) }. Defined.

Definition isContr  (A: UU): UU := ∑ a: A, ∏ x: A, Id a x.
Definition isContrP {A: UU} (P: A -> UU): UU :=  ∏ x: A, isContr (P x).
Definition isContrf {A B: UU} (f: A -> B): UU := ∏ y: B, isContr (fiber f y).

Definition fibration (X: UU) := X -> UU.
Definition section {X: UU} (P: fibration X):= ∏ x: X, P x.
Definition retract (A B: UU) := ∑ r: A -> B, ∑ s: B -> A, ∏ y: B, Id (r (s y)) y.
(*/homotopy levels *)

(* axioms *)

(* WFE *)
Definition wfunext_def: UU := ∏  (A: UU) (P: A -> UU),
  (∏x: A, isContr (P x)) -> isContr (∏x: A, P x).

(* /axioms *)

(** Armin's thesis -- preparatory lemmas *)
Lemma h431: ∏ {X: UU} (A: X -> UU) (P: ∏ x: X, (A x -> UU)),
  (∏ x: X, ∑ a: A x, P x a) -> (∑ g: (∏ x: X, A x), ∏ x: X, P x (g x)).
Proof. intros X A P H.
       unshelve econstructor.
       - intro x. specialize (H x).
         exact (pr1 H).
       - intro x. apply H.
Defined.

Lemma h431_i: ∏ {X: UU} (A: X -> UU) (P: ∏ x: X, (A x -> UU)),
  (∑ g: (∏ x: X, A x), ∏ x: X, P x (g x)) -> (∏ x: X, ∑ a: A x, P x a).
Proof. intros X A P (g, cc) x.
        exists (g x). apply cc.
Defined.

Corollary h432c: ∏ {A B: UU} (f: A -> B) (e: isequiv f) (x x':A) (y: B),
  Id (f x) y /\ Id (f x') y -> Id x x'.
Proof. intros A B f e x x' y (p, q).
        apply h249_ii in e.
        destruct e as (g, (cc0, cc1)).
        unfold homotopy, compose, id in *.
        apply Id_eql in p. apply Id_eql in q.
        pose proof cc1 as cc2.
        specialize (cc1 x).
        specialize (cc2 x').
        assert (g (f x)  = g y) by now rewrite p.
        assert (g (f x') = g y) by now rewrite q.
        apply Id_eql in cc1. apply Id_eql in cc2.
        rewrite cc2 in H0.
        rewrite cc1 in H.
        rewrite <- H in H0.
        now rewrite H0.
Qed.

Corollary h432d: ∏ {A B: UU} (f: A -> B) (e: isequiv f) (y: B)
  (a b: ∑x: A, Id (f x) y), Id a b.
Proof. intros.
        destruct a as (a, p).
        destruct b as (b, q).
        specialize (@h432c A B f e a b y); intro H.
        assert (H0: Id (f a) y /\ Id (f b) y ) by easy.
        specialize (H H0).
        induction H. dependent induction p.
        dependent induction q. easy.
Defined.

Lemma h432_i: ∏ {A B: UU} (f: A -> B), isequiv f -> isContrf f.
Proof. intros A B f e.
        unfold isContrf. intro y.
        specialize (@h432d A B f e y); intro H.
        unshelve econstructor.
        - unfold fiber.
          apply h249_ii in e.
          destruct e as (g, (cc0, cc1)).
          unfold homotopy, compose, id in *.
          exists (g y). easy.
        - cbn. destruct (h249_ii e), pr4. cbn. 
          intro a. specialize (H a).
          specialize (H {pr3 y; pr4 y}). easy.
Defined.

Lemma h432_ii: ∏ {A B: UU} (f: A -> B), isContrf f -> isequiv f.
Proof. unfold isContrf.
        intros A B f e.
        apply h249_i.
        unshelve econstructor.
        - intro y.
          specialize (e y).
          destruct e as (fib, cc).
          destruct fib as (x, p).
          exact x.
        - compute. unshelve econstructor.
          + intro a. destruct (e a).
            destruct pr3. easy.
          + intro a. destruct (e (f a)) as ((x, p), cc).
            specialize (e (f a)).
            destruct e as (g, cc0).
            destruct g as (b, q). 
            specialize (cc {a; refl}).
            apply Id_eql in cc.
            now inversion cc. 
Defined.

Lemma h433: ∏ {A: UU} (P Q: A -> UU) {x: A} {v: Q x} (f: ∏ x: A, (P x -> Q x)),
  Equiv (fiber (totalA P Q f) {x; v}) (fiber (f x) v).
Proof. intros A P Q x v f.
       unshelve econstructor.
       - unfold totalA, fiber. intros Hf.
         destruct Hf as ((x0, t), q). cbn in *.
         inversion q. subst.
         unshelve econstructor.
         + exact t.
         + easy.
       - apply h249_i.
         + cbn. unshelve econstructor.
           * intro Hf. unfold totalA, fiber.
             unfold fiber in Hf.
             unshelve econstructor.
             exists x. destruct Hf. exact pr3.
             cbn. destruct Hf.
             now induction pr4.
           * split.
             ++ cbn. unfold homotopy, compose.
                intro a. destruct a.
                dependent induction pr4. now cbn.
             ++ cbn. unfold homotopy, compose.
                intro a. destruct a. destruct pr3.
                dependent induction pr4. now cbn.
Defined.

Lemma h434: ∏ {A: UU} (P: A -> UU) {a: A},
  Equiv (fiber (@pr1 A P) a) (P a).
Proof. intros.
       unshelve econstructor.
       - intros Hf. destruct Hf as ((y, t), q).
         inversion q. subst. cbn. exact t.
       - apply h249_i.
         unshelve econstructor.
         + intro p.
           unfold fiber.
           unshelve econstructor.
           exists a. exact p.
           now cbn.
         + split.
           * unfold homotopy, compose, id.
             intro p. now cbn.
           * unfold homotopy, compose, id.
             intro p. destruct p as ((y, t), q).
             dependent induction q. now cbn.
Qed.

(** supposed to use h432? *)
Lemma h435: ∏ {A B: UU} (f: A -> B), isequiv f -> isSurj f.
Proof. intros A B f Hs.
       destruct Hs as ((g, cc1), (h, cc2)).
       unshelve econstructor.
       - exact (g y).
       - unfold homotopy, compose, id in *.
         exact (cc1 y).
Qed.

Lemma h436_i: ∏ {A B: UU} (e: Equiv A B), isContr A -> isContr B.
Proof. intros A B e alpha.
       destruct alpha as (a, P).
       destruct e as (f, iseqf).
       unshelve econstructor.
       + exact (f a).
       + intro b.
         apply h435 in iseqf.
         unfold isSurj, fiber in *.
         specialize (iseqf b).
         destruct iseqf as (cc1, cc2).
         specialize (P cc1).
         now induction P.
Defined.

Lemma h436_ii: ∏ {A B: UU} (e: Equiv A B), isContr B -> isContr A.
Proof. intros A B e alpha.
        destruct alpha as (b, P).
        destruct e as (f, iseqf).
        unshelve econstructor.
        + exact (pr1 (pr2 iseqf) b).
        + intro a.
          destruct iseqf as ((g, Hg), (h, Hh)).
          cbn.
          unfold homotopy, compose, id in *.
          specialize (P (f a)).
          specialize (Hh a).
          apply Id_eql in P. 
          now rewrite P in *.
Defined.

Lemma h437: ∏ {A B: UU} (re: retract A B), isContr A -> isContr B.
Proof. intros A B e alpha.
        destruct alpha as (a, P).
        destruct e as (r, (s, eps)).
        unshelve econstructor.
        - exact (r a).
        - intro y.
          specialize (P (s y)).
          apply Id_eql in P. rewrite P. easy.
Defined.

Lemma h437C: ∏ {A B: UU} (re: retract A B) (x:A) (y y': B),
  Id ((pr1 re) x) y /\ Id ((pr1 re) x) y' -> Id y y'.
Proof. intros A B e x y y' (p, q).
        destruct e as (f, (g, cc)). cbn in *.
        pose proof cc as cc1.
        specialize (cc  y).
        specialize (cc1 y').
        apply Id_eql in p.
        apply Id_eql in q.
        rewrite <- p in cc at 1.
        rewrite <- q in cc1 at 1.
        apply Id_eql in cc.
        apply Id_eql in cc1.
        now rewrite <- cc, <- cc1.
Qed.

Lemma h438: ∏ {A: UU} (a: A), isContr (∑ x: A, Id a x).
Proof. intros.
        unshelve econstructor.
        - exists a. easy.
        - intro p. destruct p as (x, p).
          now induction p.
Defined.


Lemma h432: ∏ {A B: UU} (f: A -> B), (isContrf f) <-> (isequiv f).
Proof. intros. split. apply h432_ii. apply h432_i. Defined.

Definition fibeq {A: UU} (P Q: A -> UU) (f: ∏x: A, (P x -> Q x)) := ∏x: A, isequiv (f x).

Lemma h439: ∏ {A: UU} (P Q: A -> UU) (f: ∏x: A, (P x -> Q x)),
  @fibeq A P Q f <-> isequiv (@totalA A P Q f).
Proof. intros. 
        specialize (λ x, @h432 _ _  (f x)); intro H.
        specialize (@h432 _ _ (totalA P Q f)); intro HH.
        unfold fibeq.
        assert (((∏ x : A, isequiv (f x)) <-> ((∏ x : A, isContrf (f x))))).
        { split; intros. apply H. easy. apply H. easy. }
        rewrite H0.
        assert ((isContrf (totalA P Q f)) <-> (isequiv (totalA P Q f))).
        { split; intros. apply HH. easy. apply HH. easy. }
        rewrite <- H1. unfold isContrf.

        split. intros.
        induction y as (x0, v0).

        specialize (@h436_ii (fiber (totalA P Q f) {x0; v0}) (fiber (f x0) v0)); 
        intro HHH. apply HHH.
        specialize (@h433 A P Q x0 v0 f); intro HHHH.
        apply HHHH. easy.

        intros.
        specialize (@h436_i (fiber (totalA P Q f) {x; y}) (fiber (f x) y));
        intro HHH. apply HHH.
        specialize (@h433 A P Q x y f); intro HHHH. easy. apply X.
Qed.

Lemma h4310: ∏ {A B: UU} (f: A -> B), isContr A /\ isContr B -> isContrf f.
Proof. intros A B f (e1, e2).
        set (a := pr1 e1).
        set (b := pr1 e2).
        assert (p1: Id b (f a)).
        { unfold a, b. destruct e1, e2. cbn in *.
          easy. }
        assert (p2: forall y: B, Id b y).
        { unfold b. destruct e2. cbn in *.
          intro y. easy. }
        unshelve econstructor.
        - set (q := concat (inverse (pr2 e2 (f a))) (pr2 e2 y)).
          unfold fiber. exists a. exact q.
        - cbn. intros. destruct x as (c, g). dependent induction g.
          induction p1. specialize (p2 (f a0)). induction p2. cbn in *.
          assert (Id a0 c). destruct e1. easy. 
          induction X.
          destruct e2. cbn.
          specialize (@concat_inverse_l _ _ _ (pr4 (f a0))); intro p.
          now induction p.
Defined.

Lemma h442: ∏ {A B X: UU} (e: Equiv A B), Equiv (X -> A) (X -> B).
Proof. intros A B X (f, e).
        unshelve econstructor.
        - exact (λ (a: (X -> A)) (x: X), f (a x)).
        - assert (H: ∑p: Id A B, Id {f; e} (idtoeqv p)).
          { unshelve econstructor.
             + apply ua_f in e. exact e.
             + cbn. unfold ua_f.
               destruct (h249_ii (UA A B)).
               destruct pr4 as (c, d).
               unfold compose, homotopy, id in *.
               specialize (c ({f; e})). easy.
          }
         destruct H as (p, q).
         induction p. apply Id_eql in q.
         inversion q. rewrite H0.
         unshelve econstructor.
         + exists id. now compute.
         + exists id. now compute.
Defined.


Corollary h443: ∏ {A: UU} (P: A -> UU) (p: ∏ x : A, isContr (P x)), 
  Equiv (A -> ∑ x: A, P x) (A -> A).
Proof. intros A P p.
        apply h442.
        unshelve econstructor.
        + exact pr1.
        + apply h432. unfold isContrf.
          specialize (@h434 A P); intro H.
          intro a.
          specialize (@h436_ii _ _ (H a)); intro HH.
          apply HH. easy.
Defined.

(*
   given "ua" show that the type 
      "∏ x : A, isContr (P x) -> isContr (∏ x : A, P x)"
   is inhabited.

1. lemma h442:
  An important consequence of UA is that
  it makes the arrow type "->" preserve equivalences.
  That is "Equiv A -> B" gives "Equiv (X -> A) (X -> B)" 
  for some type "X".

2. Corollary h443: 
  "Equiv (A -> ∑ x: A, P x) (A -> A)" holds with the obvious
   underlying function: "λa: (A ->  ∑x: A, P x) (x: A), pr1 (a x)"
   being an equivalence: 

       "isequiv (λ (a : A -> ∑ x : A, P x) (x : A), pr1 (a x))".

3. lemma h432: 
  an equivalence can also be identified via its fibers: all contractible.
  A  _____                 B  _____
    |     |                  |     |   fiber of f at "y: B" is defined as 
    |  x  | ------ f ----->  |  y  |   "∑ x: A, Id (f x) y". When f is an equivalence
    |_____|                  |_____|   all its fibers are contractibe.

         "isContr (fiber (λ (a : A -> ∑ x : A, P x) (x : A), pr1 (a x)) id)".

4.if we can prove that
  "(fiber (λ (a : A -> ∑ x : A, P x) (x : A), pr1 (a x)) id)" is a retract of 
  "(∏ x : A, P x)", then we are done

                                       ||
                                       vv

5. since "retract A B -> isContr A -> isContr B" thanks to h437. 
*)

Theorem h444: wfunext_def.
Proof. unfold wfunext_def.
        intros A P p.
        (** 2 *)
        specialize (pr2 (h443 P p)); intros uf_equiv; cbn in uf_equiv.
        (** 3 *)
        apply h432 in uf_equiv.
        unfold isContrf in uf_equiv; cbn in uf_equiv.
        specialize (uf_equiv id).
        (** 4 *)
        assert (R: retract (fiber (λ (a : A -> ∑ x : A, P x) (x : A), pr1 (a x)) id) 
                           (∏ x : A, P x)).
        { unshelve econstructor.
          - intro X.
            destruct X as (g, q).
            exact (λ x, @transport A P _ _ ((@happly _ _ _ _ q) x) (pr2 (g x))).
          - cbn. unshelve econstructor.
            + intro f. cbn in *.
              exact ({λ x: A, {x; (f x)}; refl}).
            + intros. cbn. easy.
        }
        (** 5 *)
        specialize (@h437 _ _ R); intros HH. apply HH.
        easy.
Defined.

(*
   given 
      "(∏ x : A, isContr (P x)) -> isContr (∏ x : A, P x)" and
      "f, g : ∏ x : A, P x"
   show that the type 
      "qinv (happly f g)"
   is inhabited.

1. we have "isequiv (happly f g)".

2. we can write "happly f g" as total type of sections:
      "isequiv (totalA (Id f) (homotopy f) (happly f)):
         ∑ (h: ∏ x: A, P(x)), Id f h ->  ∑ (h: ∏ x: A, P(x)), homotopy f g"

3. lemma h432: 
  an equivalence is a contractible function (all fibers are contractibe):
      "isContrf (totalA (Id f) (homotopy f) (happly f))"

4. if some "f: A -> B" is a contractibe function, 
   then types "A" and "B" must be contractibe.
      * (i)  "isContr (∑ (h: ∏ x: A, P(x)), Id f h)"
      * (ii) "isContr (∑ (h: ∏ x: A, P(x)), homotopy f h)"

5. (i) is trivial since, there exists "f" itself. 

6. (ii) requires a retraction proof:
      "(∏ x : A, ∑ a : P x, Id (f x) a)" is a retraction of
      "(∑ h : ∏ x : A, P x, ∏ a : A, Id (f a) (h a))".

7. "retract A B -> isContr A -> isContr B" thanks to h437. 
      "isContr (∏ x : A, ∑ a : P x, Id (f x) a)"

8. follows from the assumption.
*)

Theorem h445: wfunext_def -> funext_def_qinv.
Proof. (* intros. exact FE. (** "for sure, no use of FE!" *) *)
        unfold wfunext_def, funext_def_qinv.
        intros H A P f g.
        (** 1 *)
        apply h249_ii.
        (** 2 *)
        apply h439.
        (** 3 *) 
        apply h432. unfold isContrf.
        (** 4 *)
        apply h4310; split. 
        (** 5 *)
        apply h438.
        (** 6 *)
        unfold homotopy.
        assert (R: retract (∏ x : A, ∑ a : P x, Id (f x) a) 
                           (∑ x : ∏ x : A, P x, ∏ a : A, Id (f a) (x a))).
        { unshelve econstructor.
          - eapply @h431.
          - unshelve econstructor.
            + specialize (@h431_i A P (λ x, Id (f x))); intro HH. cbn in HH.
              apply HH. 
            + cbn. unfold h431, h431_i. intros.
              destruct y. cbn. easy.
        }
        (** 7 *)
        specialize (@h437 _ _ R); intros HH. apply HH.
        (** 8 *)
        apply H. intros. apply h438.
Defined.

Theorem main: funext_def_qinv.
Proof. now apply h445, h444. Qed.





