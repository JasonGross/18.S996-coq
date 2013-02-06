Require Import FunctionalExtensionality Setoid.
Require Import Common.

Set Implicit Arguments.

Generalizable All Variables.

Local Open Scope type_scope.

Definition compose X Y Z (f : Y -> Z) (g : X -> Y) := fun x => f (g x).

Arguments compose [X Y Z] f g x / .

Local Infix "o" := (@compose _ _ _) (at level 70).

Record is_isomorphism X Y (f : X -> Y) :=
  {
    isomorphism_inverse : Y -> X;
    isomorphism_right_inverse : f o isomorphism_inverse = @id _;
    isomorphism_left_inverse : isomorphism_inverse o f = @id _
  }.

Section univ_prod.
  Variables X Y : Type.

  Record product :=
    {
      prodXY :> Type;
      prod_fst : prodXY -> X;
      prod_snd : prodXY -> Y;
      prod_map : forall A (f : A -> X) (g : A -> Y), A -> prodXY;
      prod_fst_commutes_prop := (fun A f g prod_map => prod_fst o prod_map = f);
      prod_snd_commutes_prop := (fun A f g prod_map => prod_snd o prod_map = g);
      prod_fst_commutes : forall A f g, prod_fst_commutes_prop A f g (@prod_map A f g);
      prod_snd_commutes : forall A f g, prod_snd_commutes_prop A f g (@prod_map A f g);
      prod_map_unique : forall A f g prod_map', prod_fst_commutes_prop A f g prod_map'
                                                -> prod_snd_commutes_prop A f g prod_map'
                                                -> prod_map' = (prod_map f g)
    }.

  Lemma product_eta :
    forall x, x = @Build_product (@prodXY x)
                                 (@prod_fst x)
                                 (@prod_snd x)
                                 (@prod_map x)
                                 (@prod_fst_commutes x)
                                 (@prod_snd_commutes x)
                                 (@prod_map_unique x).
    intro x; destruct x; simpl; reflexivity.
  Qed.
End univ_prod.

Local Infix "*" := product : category_scope.

Delimit Scope category_scope with category.

Section swap.
  Definition swap X Y : (X * Y)%category -> (Y * X)%category :=
    fun xy =>
      {|
        prodXY := prodXY xy;
        prod_fst := prod_snd xy;
        prod_snd := prod_fst xy;
        prod_map := (fun A f g => prod_map xy g f);
        prod_fst_commutes := (fun A f g => prod_snd_commutes xy g f);
        prod_snd_commutes := (fun A f g => prod_fst_commutes xy g f);
        prod_map_unique := (fun A f g prod_map' Hfst Hsnd => @prod_map_unique _ _ xy A g f prod_map' Hsnd Hfst)
      |}.

  Definition swap_iso X Y : is_isomorphism (@swap X Y).
    exists (@swap _ _);
    abstract (
        apply functional_extensionality_dep;
        repeat intro;
        expand; destruct_head_hnf @product;
        repeat progress change (fun a b c => ?f a b c) with f;
        reflexivity
      ).
  Defined.

End swap.
