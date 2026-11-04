module

public import StacksFrontier.CategoryTheory.Functor.Derived.EverywhereDefinedTriangulated

/-!
# The comparison out of a right derived functor, read on the comparison cocones

Let `L : C ⥤ D` be a localization functor for `W`, let `F : C ⥤ H` be a functor, let `RF` with
`α : F ⟶ L ⋙ RF` be a right derived functor of `F`, and let `G : D ⥤ H` be *any* functor
equipped with a comparison `β : F ⟶ L ⋙ G`. The universal property of `RF` produces a canonical
natural transformation `θ = RF.rightDerivedDesc α W G β : RF ⟶ G`, and no property of `G` is
needed to produce it: that is the point of the construction, which is used where `G` is known
only through `β`.

This file records how `θ` interacts with the cocones of Tag 05S9. For every object `X` of `C`
both `RF` with `α` and `G` with `β` carry a cocone
`CategoryTheory.Functor.derivedUnitCocone` on Deligne's ind-object
`(s : X ⟶ X') ↦ F(X')`, with vertices `RF(L X)` and `G(L X)`. The single lemma here says that
`θ` at `L X` is a morphism of those cocones: it is compatible with every coprojection. Nothing is
assumed of `G` beyond `β`, and nothing of `W` beyond that `L` inverts it.

That compatibility is what makes `θ` computable leg by leg, which is how it is shown invertible:
the coprojections of the left-hand cocone are jointly surjective whenever that cocone is a
colimit, so a formula for `θ` on each leg is a formula for `θ`. The two corollaries below are the
two ways of using it — formally, when both cocones are colimits, and (the case that matters for
Tag 09LK) through an identification of the two vertices that is known leg by leg.

## Main results

* `CategoryTheory.Functor.derivedUnitCocone_ι_app_comp_rightDerivedDesc_app`: the canonical
  comparison `θ : RF ⟶ G` at `L X` carries the coprojection of the comparison cocone of `RF` at
  `(s : X ⟶ X')` to the coprojection of the comparison cocone of `G`.
* `CategoryTheory.Functor.isIso_rightDerivedDesc_app_of_isColimit`: consequently, if both
  comparison cocones at `X` are colimit cocones then `θ` at `L X` is invertible.

## References

* [Stacks Project, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9), being defined at an
  object, whose cocones these are.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]
  (F : C ⥤ H) (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W]
  (RF : D ⥤ H) (α : F ⟶ L ⋙ RF) [RF.IsRightDerivedFunctor α W]
  (G : D ⥤ H) (β : F ⟶ L ⋙ G)

/-- **The canonical comparison is a morphism of comparison cocones.** Let `RF` with `α` be a
right derived functor of `F` and let `β : F ⟶ L ⋙ G` be a comparison into an arbitrary functor
`G`. Composing the coprojection at `(s : X ⟶ X')` of the cocone of Tag 05S9 attached to `α` with
the canonical transformation `θ = RF.rightDerivedDesc α W G β` at `L X` gives the coprojection at
`(s : X ⟶ X')` of the cocone attached to `β`.

Both coprojections are a comparison at `X'` followed by the inverse of the image of `L s`, so
this is naturality of `θ` together with the defining compatibility `α ≫ θ = β` of `θ`. -/
theorem derivedUnitCocone_ι_app_comp_rightDerivedDesc_app (X : C) (s : W.Under ⊤ X) :
    (derivedUnitCocone F W L RF α X).ι.app s ≫ (RF.rightDerivedDesc α W G β).app (L.obj X) =
      (derivedUnitCocone F W L G β X).ι.app s := by
  dsimp
  rw [assoc, (RF.rightDerivedDesc α W G β).naturality, ← assoc, rightDerived_fac_app]

/-- **The canonical comparison is invertible at `L X` whenever both comparison cocones compute
the ind-object at `X`.** Two colimit cocones on one and the same diagram have canonically
isomorphic vertices, and by
`CategoryTheory.Functor.derivedUnitCocone_ι_app_comp_rightDerivedDesc_app` the canonical
comparison is the morphism of cocones between them.

This is the formal half of the comparison argument. It is not the half Tag 09LK can use: there
the right-hand cocone is not known to be a colimit — knowing it would be knowing the conclusion —
and the invertibility is obtained instead from an identification of the vertex `G(L X)` that is
known coprojection by coprojection. -/
theorem isIso_rightDerivedDesc_app_of_isColimit (X : C)
    (hα : IsColimit (derivedUnitCocone F W L RF α X))
    (hβ : IsColimit (derivedUnitCocone F W L G β X)) :
    IsIso ((RF.rightDerivedDesc α W G β).app (L.obj X)) := by
  have key : (RF.rightDerivedDesc α W G β).app (L.obj X) =
      (IsColimit.coconePointUniqueUpToIso hα hβ).hom :=
    hα.hom_ext fun s => (derivedUnitCocone_ι_app_comp_rightDerivedDesc_app F W L RF α G β X
      s).trans (IsColimit.comp_coconePointUniqueUpToIso_hom hα hβ s).symm
  rw [key]
  exact (IsColimit.coconePointUniqueUpToIso hα hβ).isIso_hom

end CategoryTheory.Functor

end
