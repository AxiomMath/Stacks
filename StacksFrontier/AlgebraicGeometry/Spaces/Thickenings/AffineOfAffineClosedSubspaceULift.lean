module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismFlatCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineClosedSubspace

/-!
# A thickening of an affine scheme is affine, for algebraic spaces in a larger universe

`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective` says that the
target of a surjective closed immersion of algebraic spaces with affine source is affine (the
thickening case of Stacks 07VT). It is stated for presheaves with values in the universe of the
schemes. The formal algebraic spaces of Stacks 0AI7 are sheaves with values in a larger universe,
and their algebraic spaces are `AlgebraicGeometry.Space.IsAlgebraicSpaceULift`. This file
transfers the statement to that setting.

## Main results

* `AlgebraicGeometry.Space.exists_isAffine_iso_uliftYoneda_of_isRepresentableThickeningULift`:
  an algebraic space `F` with values in `Type (max w u)` receiving a representable thickening
  from the presheaf represented by an affine object `G` of the site is itself represented by an
  affine object of the site.

## Implementation notes

An algebraic space with values in `Type (max w u)` is the universe lift of an algebraic space with
values in `Type u`
(`AlgebraicGeometry.Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift`), every morphism
of universe lifts is the lift of a morphism (`AlgebraicGeometry.Space.exists_whiskerRight_eq`),
and a relative morphism property is unchanged by the universe lift
(`AlgebraicGeometry.Space.relative_comp_map_iff`). The statement then is the one in `Type u`.

## References

* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A representable thickening of an affine scheme into an algebraic space has an affine
target**, for presheaves with values in `Type (max w u)`. Let `F` be an algebraic space over `S`
in the sense of `AlgebraicGeometry.Space.IsAlgebraicSpaceULift` and `i : F₀ ⟶ F` a representable
thickening whose source is represented by an affine object `G` of the site. Then `F` is
represented by an affine object of the site.

This is `AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective` (the
thickening case of Stacks 07VT) for the universe-lifted algebraic spaces of Stacks 0AI7. -/
theorem exists_isAffine_iso_uliftYoneda_of_isRepresentableThickeningULift
    {F₀ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (i : F₀ ⟶ F)
    (hF : IsAlgebraicSpaceULift.{w} B S hS F)
    (hi : IsRepresentableThickeningULift.{w} B S hS i)
    (G : BigFppfOver B S hS) (hG : IsAffine ((BigFppfOver.toScheme B S hS).obj G))
    (e : F₀ ≅ uliftYoneda.{w}.obj G) :
    ∃ T : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      Nonempty (F ≅ uliftYoneda.{w}.obj T) := by
  obtain ⟨F', hF', ⟨eF⟩⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hF
  let a : yoneda.obj G ⋙ uliftFunctor.{w} ⟶ F' ⋙ uliftFunctor.{w} := e.inv ≫ i ≫ eF.inv
  obtain ⟨a', ha'⟩ := exists_whiskerRight_eq B S hS a
  have hthick : IsRepresentableThickeningULift.{w} B S hS a :=
    (MorphismProperty.cancel_left_of_respectsIso _ e.inv _).mpr
      ((MorphismProperty.cancel_right_of_respectsIso _ i eF.inv).mpr hi)
  have hpre : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a' := by
    rw [← ha'] at hthick
    exact (relative_comp_map_iff yoneda
      ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
        (Type (max w u))).obj uliftFunctor.{w}) _ a').mp hthick
  obtain ⟨T, hT, ⟨eT⟩⟩ := isAffineSpace_of_isClosedImmersion_of_isSurjective B S hS a'
    (isAlgebraicSpace_yoneda B S hS G) hF'
    (MorphismProperty.relative_monotone (fun _ _ _ hf ↦ hf.1) _ hpre)
    (isSurjective_of_presheafSurjective B S hS a'
      (MorphismProperty.relative_monotone (fun _ _ _ hf ↦ ⟨hf.2⟩) _ hpre))
    ⟨G, hG, ⟨Iso.refl _⟩⟩
  exact ⟨T, hT, ⟨eF.symm ≪≫ Functor.isoWhiskerRight eT uliftFunctor.{w}⟩⟩

end AlgebraicGeometry.Space

end
