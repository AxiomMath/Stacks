module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionULiftTransfer

/-!
# Factorizations on the completion, from the completion sheaf to its subfunctor

Let `S` be a scheme contained in a big fppf site `B`, let `Z` be an fppf sheaf over `S` and let
`T` be a set of points of `Z`. The completion `Z_{/T}`, `AlgebraicGeometry.Space.completionSheaf`,
is the sheafification of the subfunctor `AlgebraicGeometry.Space.completionSubfunctor` of
sections with point-set image in `T`. This file shows that a factorization through a morphism out
of the completion sheaf gives a factorization through a morphism out of the completion
subfunctor, the form of the completion hypothesis of
`AlgebraicGeometry.FormalSpace.exists_factorization_of_openComplement_and_completion`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.completionToULift` is the inclusion `Z_{/T} ⟶ Z` of the
  completion of an fppf sheaf of `Type u` into its universe lift, *before* sheafifying that
  universe lift.
* `AlgebraicGeometry.FormalSpace.toCompletionSheaf` is the unit presenting `Z_{/T}` as the
  sheafification of the subfunctor of sections with point-set image in `T`.

## Main results

* `AlgebraicGeometry.FormalSpace.toSheafify_comp_completionToULift`: that inclusion restricts
  along the unit of the sheafification to the inclusion of the completion subfunctor.
* `AlgebraicGeometry.FormalSpace.completionSheafMap_comp_completionToULift`: it is natural, a
  morphism of completions composing with it to the universe lift of the morphism.
* `AlgebraicGeometry.FormalSpace.exists_factorization_completionSubfunctor_of_completionSheaf`:
  a factorization on the completion sheaf gives one on the completion subfunctor.

## References

* [Stacks Project, Tag 0AR6](https://stacks.math.columbia.edu/tag/0AR6)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion `Z_{/T} ⟶ Z` of the completion of an fppf sheaf of `Type u` along a set of
its points into the universe lift of `Z`, before sheafifying that universe lift. -/
def completionToULift (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z)
    (T : Set (Space.points B S hS Z)) :
    (Space.completionSheaf B S hS Z T).obj ⟶ Z ⋙ uliftFunctor.{u + 1} :=
  (Space.completionSheafInclusion B S hS Z T).hom ≫
    (Space.sheafifiedULiftIso B S hS Z hZ).inv

/-- The unit presenting the completion of `Z` along `T` as the sheafification of the subfunctor
of sections with point-set image in `T`. -/
def toCompletionSheaf (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (Space.points B S hS Z)) :
    (Space.completionSubfunctor B S hS Z T).toFunctor ⟶
      (Space.completionSheaf B S hS Z T).obj :=
  (BigFppfOver.topology B S hS).toSheafify _

/-- The unit of a sheafification composed with the sheafification of a morphism into a sheaf,
read back in that sheaf through the inverse of its sheafification isomorphism, is the morphism
itself. -/
private theorem toSheafify_comp_sheafifyMap_comp_isoSheafify_inv
    {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q) (η : P ⟶ Q) :
    (BigFppfOver.topology B S hS).toSheafify P ≫
        ((BigFppfOver.topology B S hS).sheafifyMap η ≫
          ((BigFppfOver.topology B S hS).isoSheafify hQ).inv) = η := by
  simp

/-- The inclusion of a completion into the universe lift restricts along the unit of the
sheafification to the inclusion of the completion subfunctor. -/
@[reassoc]
theorem toSheafify_comp_completionToULift (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z)
    (T : Set (Space.points B S hS Z)) :
    toCompletionSheaf B S hS Z T ≫ completionToULift B S hS Z hZ T =
      (Space.completionSubfunctor B S hS Z T).ι :=
  toSheafify_comp_sheafifyMap_comp_isoSheafify_inv B S hS _ _

/-- The inclusion of a completion into the universe lift is natural: a morphism of completions
composed with it is it composed with the universe lift of the morphism. -/
@[reassoc]
theorem completionSheafMap_comp_completionToULift
    {Z' Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z')
    (hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z) (f : Z' ⟶ Z)
    (T : Set (Space.points B S hS Z)) :
    (Space.completionSheafMap B S hS f T).hom ≫ completionToULift B S hS Z hZ T =
      completionToULift B S hS Z' hZ' (Space.pointsMap B S hS Z' f ⁻¹' T) ≫
        Functor.whiskerRight f uliftFunctor.{u + 1} := by
  rw [← cancel_mono (Space.sheafifiedULiftIso B S hS Z hZ).hom]
  simp only [completionToULift, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Space.sheafifiedULiftMap_hom_eq B S hS hZ' hZ f]
  exact (congrArg (fun φ : Space.completionSheaf B S hS Z'
      (Space.pointsMap B S hS Z' f ⁻¹' T) ⟶ Space.sheafifiedULift B S hS Z ↦ φ.hom)
    (Space.isPullback_completionSheafMap B S hS f T).w).symm

/-- If the inclusion of the completion `W_{/T}` into `W` composed with `f` factors through
`g` by a morphism out of the completion *sheaf*, then it factors through `g` by a morphism out
of the completion *subfunctor*. -/
theorem exists_factorization_completionSubfunctor_of_completionSheaf
    {W Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W) (f : W ⟶ Y) (g : Z ⟶ Y)
    (T : Set (Space.points B S hS W))
    (h : ∃ v : (Space.completionSheaf B S hS W T).obj ⟶ Z ⋙ uliftFunctor.{u + 1},
      v ≫ Functor.whiskerRight g uliftFunctor.{u + 1} =
        completionToULift B S hS W hW T ≫ Functor.whiskerRight f uliftFunctor.{u + 1}) :
    ∃ v : (Space.completionSubfunctor B S hS W T).toFunctor ⟶ Z ⋙ uliftFunctor.{u + 1},
      v ≫ Functor.whiskerRight g uliftFunctor.{u + 1} =
        (Space.completionSubfunctor B S hS W T).ι ≫
          Functor.whiskerRight f uliftFunctor.{u + 1} := by
  obtain ⟨v, hv⟩ := h
  exact ⟨toCompletionSheaf B S hS W T ≫ v, by
    simp only [Category.assoc, hv, toSheafify_comp_completionToULift_assoc]⟩

end AlgebraicGeometry.FormalSpace

end
