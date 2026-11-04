module

public import StacksFrontier.Deformation.Artin.Versality.RepresentableSmoothVersality
public import StacksFrontier.Deformation.Artin.Versality.SmoothPredeformation

/-!
# Smoothness on predeformation categories: the three cases

Let `S` be a locally Noetherian scheme and `F : 𝒳 → 𝒴` a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. Suppose that

1. `F` is formally smooth on objects, or
2. `F` is representable by algebraic spaces and formally smooth, or
3. `F` is representable by algebraic spaces and smooth.

Then for every finite type field `k` over `S` and every object `x₀` of `𝒳` over `Spec k` the
functor of predeformation categories induced by `F` is smooth. This is
[Stacks Project, Tag 07WK].

Case (1) is `Deformation.Artin.isSmoothOnPredeformationCategories_of_isFormallySmoothOnObjects`
and case (2) is reduced to it by
`Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelyFormallySmooth`. Case (3)
is `Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth'`, which tests
formal smoothness only along Artinian local test objects, where a smooth morphism of algebraic
spaces is formally smooth (Stacks 04AM).

## Main results

* `Deformation.Artin.isSmoothOnPredeformationCategories_of_formallySmooth_or_smooth`:
  **Stacks 07WK**, the three cases together.

## References

* [Stacks Project, Tag 07WK](https://stacks.math.columbia.edu/tag/07WK)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace Deformation.Artin

/-- **Stacks 07WK.** Let `S` be a locally Noetherian scheme and `F : 𝒳 → 𝒴` a 1-morphism of
categories fibred in groupoids over the big fppf category of `S` which is (1) formally smooth on
objects, or (2) representable by algebraic spaces and formally smooth, or (3) representable by
algebraic spaces and smooth. Then for every finite type field `k` over `S` and every object `x₀`
of `𝒳` over `Spec k` the induced functor of predeformation categories is smooth. -/
@[stacks 07WK]
theorem isSmoothOnPredeformationCategories_of_formallySmooth_or_smooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (h : Stack.IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p ∨
      (Stack.IsRepresentableByAlgebraicSpaces B S hS p.hom ∧
        BigFppfOver.IsRelativelyFormallySmooth B S hS p) ∨
      Stack.IsRelativelySmooth B S hS p) :
    IsSmoothOnPredeformationCategories B S hS 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p)
      (CatFiberedInGroupoids.homFunctor_comp_p p) := by
  rcases h with h | ⟨hrep, hform⟩ | h
  · exact isSmoothOnPredeformationCategories_of_isFormallySmoothOnObjects B S hS p h
  · exact isSmoothOnPredeformationCategories_of_isRelativelyFormallySmooth B S hS p hrep hform
  · exact isSmoothOnPredeformationCategories_of_isRelativelySmooth' B S hS p h

end Deformation.Artin

end
