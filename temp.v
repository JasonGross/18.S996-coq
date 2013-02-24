Require Import FunctionalExtensionality Setoid.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Require Import SwapExercise.

Local Open Scope type_scope.
Local Open Scope product_scope.

Require Import Setoid Utf8.

Lemma fiber_is_relation X B (f : X -> B) : Equivalence (fun x y => f x = f y).
  split; repeat intro; simpl;
  repeat match goal with
           | [ H : context[f _] |- _ ] => revert H
           | [ |- context[f ?x] ] => generalize (f x); intro
         end;
  intros; subst; reflexivity.
Qed.

Section set_products.
  (** Coq has a built-in product type, called [prod].  Prove that it
  satisfies the universal property. *)

  Definition build_product A B : A * B
    := @Build_product A B
                      (prod A B)
                      (@fst _ _)
                      (@snd _ _)
                      (fun A f g a => @pair _ _ (f a) (g a))
                      (fun _ f g _ => eq_refl)
                      (fun _ f g _ => eq_refl)
                      (fun _ f g prod_map' H0 H1 a => match H0 a in (_ = y) return (prod_map' a = (y, _)) with
                                                        | eq_refl => match H1 a in (_ = y) return (prod_map' a = (_, y)) with
                                                                       | eq_refl => let (x, x0) as p return (p = (fst p, snd p)) :=
                                                                                        prod_map' a in eq_refl
                                                                     end
                                                      end).
End set_products.

(** printing × %\ensuremath{\times}% #&times;# *)

(*Infix "×" := build_product (left associativity, at level 40) : product_scope.
Infix "×" := build_product (left associativity, at level 40) : type_scope. *)

Section function_prod.
  (** If [A * B] and [A' * B'] exist, then we can build a function
  from [A * B] to [A' * B'] *)

  Definition function_prod A A' B B' (f : A -> A') (g : B -> B') (AB : A * B) (A'B' : A' * B') : AB -> A'B'
    := fun x => f (π₁ x) * g (π₂ x).

π₁₂
Section lift_prod.
  Definition lift_prod0 A B T : (T -> A * B) -> (T -> A) * (T -> B).
    intro fg.
    Check @prod_fst A B.
    Check @prod_fst (T -> A) (T -> B) _.
    refine (@Build_product (T -> A) (T -> B)
                           (forall x, prodXY (fg x))
                           (fun z x => prod_fst (fg x) (prod_map (fg x) _ _ _))
                           (fun z x => prod_snd (fg x) (prod_map (fg x) _ _ _))
                           (fun A f g a => _ (prod_map (fg _) (f a) (g a) _))
                           (fun A f g => functional_extensionality_dep
                                           _
                                           _
                                           (fun x => functional_extensionality_dep
                                                       _
                                                       _
                                                       (fun x' => let H := (prod_fst_commutes (fg x') (f x) (g x)) in _)))
                           (fun A f g => functional_extensionality_dep
                                           _
                                           _
                                           (fun x => functional_extensionality_dep
                                                       _
                                                       _
                                                       (fun x' => let H := (prod_snd_commutes (fg x') (f x) (g x)) in _)))
                           (fun A f g prod_map' H0 H1 => functional_extensionality_dep
                                                           _
                                                           _
                                                           (fun x => _)));
      unfold prod_fst_commutes_prop, prod_snd_commutes_prop in *; simpl in *;
      fg_equal; simpl in *.
    Focus 3.
    pose (proj
    etransitivity; try apply H.
    unfold
    intros x'.
    simpl.
    pose ().
    hnf in *.
    apply functional_extensionality_dep.
      repeat intro;
      repeat (apply functional_extensionality_dep; intro); simpl;
      repeat match goal with | [ |- appcontext[?E] ] => let H:= fresh in is_evar E; set (H := E) in * end.
    pose (prod_fst_commutes (fg x0)).
    Print product.
    Focus 2.
    repe
    match goal with | [ |- appcontext[prod_snd ??E] ] => let H:= fresh in is_evar E; pose E end.
    simpl in *.
  Definition lift_prod1 A B T : (T -> A) * (T -> B) -> (T -> A * B).
    intros fg x.
    pose (fun A f g => prod_map fg (A := A) f g).
    Print product.
    refine (@Build_product A B
                           _
                           (fun z => prod_fst fg z x)
                           (fun z => prod_snd fg z x)
                           (fun A f g => prod_map fg (A := _) (fun x0 _ => f x0) (fun x0 _ => g x0))
                           (fun A f g => _ (prod_fst_commutes fg (fun x0 _ => f x0) (fun x0 _ => g x0)))
                           (fun A f g => _ (prod_snd_commutes fg (fun x0 _ => f x0) (fun x0 _ => g x0)))
                           (fun A f g prod_map' H0 H1 => prod_map_unique (p := fg) _ _));
      repeat intro;
      unfold prod_fst_commutes_prop, prod_snd_commutes_prop in *; simpl in *;
      try solve [
      repeat (apply functional_extensionality_dep; intro); simpl;
      fg_equal;
      trivial ].
    apply functional_extensionality_dep.
      repeat intro;
      unfold prod_fst_commutes_prop, prod_snd_commutes_prop in *; simpl in *;
      fg_equal;
      repeat (apply functional_extensionality_dep; intro); simpl;
      trivial.
      repeat intro;
      unfold prod_fst_commutes_prop, prod_snd_commutes_prop in *; simpl in *;
      fg_equal;
      repeat (apply functional_extensionality_dep; intro); simpl;
      trivial.
    simpl.
    pose (prod_map_unique (p := fg)).
    etransitivity; try apply H0.

    simpl.
    clear H1 H2.
    pose (prod_map_unique (p := fg)).
    fg_equal_in H.
    etransitivity. Focus 2.
    pose (H _ (fun x0 _ => f x0)); simpl in *; fg_equal.
    apply H.
    destruct fg; simpl in *.
    unfold compose in *.
    fg_equal.
    simpl in *.

Section homs.
  Definition Hom A B := A -> B.

  Lemma hom_lemma A X Y : (Hom A X * Hom A Y)%category ≅ Hom A (X * Y)%category.
    unfold Hom.
    match goal with
      | [ |- ?A ≅ ?B ] => assert (A -> B)
    end.
    intro fg.
    intro x.

    exists (fun fg => (fun x => (fst fg x, snd fg x))).


Section products_unique.
  (** Products are unique up to unique isomorphism *)
  Definition products_unique A B : forall x y : A * B, x ≅ y.
    intros x y.
    exists (prod_map y π₁ π₂).
    exists (prod_map x π₁ π₂);
      repeat (apply functional_extensionality_dep; intro); unfold id; simpl.
    match goal with
      | [ |- prod_map ?a ?p1 ?p2 _ = _ ] =>
        let H := fresh in pose (prod_map_unique (p := y) (f := p1) (g := p2)) as H
    end.
    pose (prod_fst_commutes x); unfold prod_fst_commutes_prop, prod_snd_commutes_prop in *; simpl in *;
    fg_equal.
    specialize (p _ (@id _)); unfold id in *; simpl in *.

    pose (prod_map_unique (p := x)) as H; try erewrite <- H; clear H.

    let H := fresh in
    pose (prod_map_unqiue y) as H.
      erewrite <- H.
    erewrite <- (prod_map_unqiue x).
    destruct x, y; simpl in *.
    subst_body; simpl in *.
    erewrite <- prod_map_unique0.
    intuition.
    congruence.
hnf in x0.

    let H := fresh in
    pose (prod_map_unique (p := y)) as H;
      fg_equal_in H.
    symmetry; etransitivity; try apply H.
    fg_equal.
    apply e.
    fg_equal.
    destruct y; simpl in *.

    destruct x, y.
    simpl in *.
    fg_equal.
    congruence.
    compute.
    hnf.
π₁'" := (@prod_fst _ _ _).
Notation "'π₂
    exists (prod_map _ _ _).
    destruct x, y; simpl.


    unfold prodXY.
    destruct x.
    exists
End products_unique.




Section set_products_unique.
  (** Products are unique up to unique isomorphism *)
  Definition set_product_eta A B : forall x : A * B, A × B ≅ x.
    intro x.
    exists (prod_map x π₁ π₂).
    exists (prod_map (A × B) π₁ π₂);
      repeat intro; simpl.
    pose (prod_map_unique (p := x) (f := (fst (B := B))) (g := (snd (B := B)))).
    pose (prod_fst_commutes x) as H; simpl in H; fg_equal_in H. rewrite H; clear H.
    pose (prod_snd_commutes (A × B)) as H; simpl in H; fg_equal_in H; rewrite H; clear H;
    destruct_head_hnf @prod; reflexivity.

    Focus 2.
    let H := fresh in
    pose (prod_fst_commutes x) as H; simpl in H; fg_equal_in H; rewrite H; clear H.
    pose (prod_snd_commutes x) as H; simpl in H; fg_equal_in H; rewrite H; clear H;
    destruct_head_hnf @prod; reflexivity.
      fg_equal.
    rewrite (prod_fst_commutes x).
    destruct x0; simpl.
    destruct x; subst_body; simpl in *.

    pose (prod_map_unique
    destruct x; simpl in *.
    exists (prod_map x π₁ π₂);
      repeat (apply functional_extensionality_dep; intro); unfold id; simpl.
    match goal with
      | [ |- prod_map ?a ?p1 ?p2 _ = _ ] =>
        let H := fresh in pose (prod_map_unique (p := y) (f := p1) (g := p2)) as H
    end.
    pose (prod_fst_commutes y).
    pose (prod_map_unique (p := x)) as H; try erewrite <- H; clear H.

    let H := fresh in
    pose (prod_map_unqiue y) as H.
      erewrite <- H.
    erewrite <- (prod_map_unqiue x).
    destruct x, y; simpl in *.
    subst_body; simpl in *.
    erewrite <- prod_map_unique0.
    intuition.
    congruence.
hnf in x0.

    let H := fresh in
    pose (prod_map_unique (p := y)) as H;
      fg_equal_in H.
    symmetry; etransitivity; try apply H.
    fg_equal.
    apply e.
    fg_equal.
    destruct y; simpl in *.

    destruct x, y.
    simpl in *.
    fg_equal.
    congruence.
    compute.
    hnf.
π₁'" := (@prod_fst _ _ _).
Notation "'π₂
    exists (prod_map _ _ _).
    destruct x, y; simpl.


    unfold prodXY.
    destruct x.
    exists
End products_unique.
