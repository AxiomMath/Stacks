module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality

/-!
# The map of pointwise groupoid fibrations attached to a morphism of groupoids in presheaves

A groupoid in presheaves on `𝒞ᵒᵖ` has a groupoid of points at every test object, and those
groupoids assemble into a category fibred in groupoids over `𝒞`, the *pointwise groupoid
fibration*. A morphism of groupoids in presheaves induces a 1-morphism of pointwise groupoid
fibrations over `𝒞`, whose component at a test object is the evaluated functor of the morphism.

This is the construction of Stacks 046Q at the level of groupoids in presheaves, where it
already makes sense: the morphism need not come from a morphism of groupoids in algebraic
spaces, and the two groupoids in presheaves need not be the groupoids of points of anything.

## Main definitions

* `AlgebraicGeometry.Stack.pointwiseMapData`: the strict map between the presenting
  pseudofunctors, with its component at a test object identified.
* `AlgebraicGeometry.Stack.pointwiseMap`: the induced 1-morphism of pointwise groupoid
  fibrations over `𝒞`.

## Main results

* `AlgebraicGeometry.Stack.evaluationHom_naturality`: evaluating a morphism of groupoids in
  presheaves commutes strictly with pullback of points.

## References

* [Stacks Project, Tag 044P](https://stacks.math.columbia.edu/tag/044P)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 06KB](https://stacks.math.columbia.edu/tag/06KB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Deformation
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace AlgebraicGeometry.Stack

universe u v w

/- The presenting pseudofunctor of the pointwise groupoid fibration is reached through
`CategoryTheory.Functor.toPseudofunctor'` and the groupoid-to-category inclusion, none of which
the `implicit` transparency level unfolds; naming that chain is what lets the ordinary tactics
see through its objects and morphisms. -/
attribute [local implicit_reducible] Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc BasedCategory.ofFunctor
  Grpd.forgetToCat Grpd.of

/-- **Evaluating a morphism of groupoids in presheaves commutes strictly with pullback of
points**: the square of evaluated functors over a morphism of test objects commutes on the
nose. -/
theorem evaluationHom_naturality {I : Type u} [Category.{v} I]
    {𝒢 ℋ : GroupoidInFunctors.{u, v, w} I} (f : GroupoidInFunctors.Hom 𝒢 ℋ)
    {a b : LocallyDiscrete I} (g : a ⟶ b) :
    ((evaluationGroupoidFunctor 𝒢 ⋙ Grpd.forgetToCat).toPseudofunctor').map g ≫
          (f.evaluation b.as).toCatHom =
      (f.evaluation a.as).toCatHom ≫
        ((evaluationGroupoidFunctor ℋ ⋙ Grpd.forgetToCat).toPseudofunctor').map g := by
  dsimp only [Grpd.of, Cat.of] at *
  change ((evaluationGroupoidFunctor 𝒢).map g.as).toCatHom ≫ (f.evaluation b.as).toCatHom =
    (f.evaluation a.as).toCatHom ≫ ((evaluationGroupoidFunctor ℋ).map g.as).toCatHom
  apply Cat.Hom.ext
  let hObj := fun x => f.mapObjects.naturality_apply g.as x
  refine CategoryTheory.Functor.ext hObj fun x y m => ?_
  exact Deformation.hom_eq_transport ℋ b.as (hObj x) (hObj y) _ _ (by
    change (ℋ.evaluationArrowEquiv b.as _ _
        ((f.evaluation b.as).map ((Deformation.evaluationMap 𝒢 g.as).map m))).1 =
      (ℋ.evaluationArrowEquiv b.as _ _
        ((Deformation.evaluationMap ℋ g.as).map ((f.evaluation a.as).map m))).1
    simp only [Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow,
      Deformation.evaluationMap_map_arrow]
    exact f.mapArrows.naturality_apply g.as
      (𝒢.evaluationArrowEquiv a.as x y m).1)

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-- **The strict map between the presenting pseudofunctors of two pointwise groupoid
fibrations** induced by a morphism of groupoids in presheaves: its component at a test object
is the evaluated functor of the morphism, and its naturality isomorphisms are transports, so
there is no twisting. -/
noncomputable def pointwiseMapData {𝒢 ℋ : GroupoidInFunctors.{u, v, w} 𝒞ᵒᵖ}
    (f : GroupoidInFunctors.Hom 𝒢 ℋ) :
    { α : (evaluationGroupoidFunctor 𝒢 ⋙ Grpd.forgetToCat).toPseudofunctor' ⟶
          (evaluationGroupoidFunctor ℋ ⋙ Grpd.forgetToCat).toPseudofunctor' //
      (∀ T : 𝒞, (α.app ⟨op T⟩).toFunctor = f.evaluation (op T)) ∧
      (∀ {a b} (g : a ⟶ b),
        ∃ hg : ((evaluationGroupoidFunctor 𝒢 ⋙ Grpd.forgetToCat).toPseudofunctor').map g ≫
              α.app b =
            α.app a ≫ ((evaluationGroupoidFunctor ℋ ⋙
              Grpd.forgetToCat).toPseudofunctor').map g,
          α.naturality g = eqToIso hg) } := by
  let α : (evaluationGroupoidFunctor 𝒢 ⋙ Grpd.forgetToCat).toPseudofunctor' ⟶
      (evaluationGroupoidFunctor ℋ ⋙ Grpd.forgetToCat).toPseudofunctor' := {
    app := fun a => (f.evaluation a.as).toCatHom
    naturality := fun g => eqToIso (evaluationHom_naturality f g)
    naturality_naturality := by
      intro a b u g η
      obtain rfl := obj_ext_of_isDiscrete η
      obtain rfl : η = 𝟙 u := Subsingleton.elim _ _
      rw [(evaluationGroupoidFunctor 𝒢 ⋙
          Grpd.forgetToCat).toPseudofunctor'.toPrelaxFunctor.map₂_id u,
        (evaluationGroupoidFunctor ℋ ⋙
          Grpd.forgetToCat).toPseudofunctor'.toPrelaxFunctor.map₂_id u,
        Bicategory.id_whiskerRight, Bicategory.whiskerLeft_id]
      simp
    naturality_id := by cat_disch
    naturality_comp := by cat_disch
  }
  exact ⟨α, fun _ => rfl, fun g => ⟨evaluationHom_naturality f g, rfl⟩⟩

/-- **The 1-morphism of pointwise groupoid fibrations over `𝒞` induced by a morphism of
groupoids in presheaves.** -/
noncomputable def pointwiseMap {𝒢 ℋ : GroupoidInFunctors.{u, v, w} 𝒞ᵒᵖ}
    (f : GroupoidInFunctors.Hom 𝒢 ℋ) :
    BasedFunctor (presheafOfGroupoids (evaluationGroupoidFunctor 𝒢))
      (presheafOfGroupoids (evaluationGroupoidFunctor ℋ)) where
  toFunctor := CoGrothendieck.map (pointwiseMapData f).val
  w := CoGrothendieck.map_comp_forget (pointwiseMapData f).val

end AlgebraicGeometry.Stack

end
