module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Finite
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Basic

/-!
# Set-theoretic covering as surjectivity of the map from the coproduct

[Stacks, Tag 09NL](https://stacks.math.columbia.edu/tag/09NL) is stated for a finite family of
closed immersions `f i : Z i ⟶ X` whose set-theoretic covering of `X` is expressed as
`AlgebraicGeometry.Surjective (CategoryTheory.Limits.Sigma.desc f)`, the morphism from the
coproduct being onto. `StacksDraft.AlgebraicGeometry.F3b.AffineClosedUnion.Finite` states the
reduced case of that tag with the covering written as `⋃ i, Set.range (f i).base = Set.univ`.
This file identifies the two, so that the statement proved there is available in the vocabulary of
the tag.

The identification is the computation of the range of `Sigma.desc f`: it contains each
`Set.range (f i).base` because `Sigma.ι Z i ≫ Sigma.desc f = f i`, and it is contained in their
union because every point of the coproduct lies in one of the summands. The latter is where the
work is: `CategoryTheory.Limits.Sigma.desc` is available for any `Small.{u}`-indexed family, but
Mathlib's homeomorphism `AlgebraicGeometry.sigmaMk` onto the coproduct is stated only for an
index type in the *same* universe as the schemes, so a shrinking argument is needed. That
argument is proved as `StacksTag09NE.exists_component_point_of_sigma`, and is used here rather
than repeated.

## Main results

* `Stacks.AffineClosedUnion.range_sigmaDesc`: the range of the morphism out of the coproduct is
  the union of the ranges.
* `Stacks.AffineClosedUnion.surjective_sigmaDesc_iff`: that morphism is onto exactly when the
  ranges cover.
* `Stacks.AffineClosedUnion.isAffine_of_surjective_sigmaDesc`: **the reduced case of
  [Stacks, Tag 09NL] in the tag's own vocabulary** — a reduced scheme with a finite family of
  affine closed subschemes whose coproduct maps onto it is affine.

## Implementation notes

The tag has no reducedness hypothesis on the ambient scheme, so what is proved here is its
reduced case. The `@[stacks 09NL]` attribute sits on
`Stacks.AffineClosedUnion.isAffine_of_surjective_sigmaDesc_unconditional` in
`StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Unconditional`, which has this file's covering
hypothesis and no reducedness hypothesis at all. See the module docstring there.

## References

* [Stacks Project, Tag 09NL](https://stacks.math.columbia.edu/tag/09NL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Stacks.AffineClosedUnion

variable {X : Scheme.{u}} {ι : Type v} {Z : ι → Scheme.{u}}

/-- The range of the morphism out of a finite coproduct is the union of the ranges. -/
theorem range_sigmaDesc [Finite ι] (f : ∀ i, Z i ⟶ X) :
    Set.range (Sigma.desc f).base = ⋃ i, Set.range (f i).base := by
  have : Small.{u} ι := inferInstance
  refine Set.eq_of_subset_of_subset ?_ (Set.iUnion_subset fun i ↦ ?_)
  · rintro _ ⟨p, rfl⟩
    obtain ⟨i, z, rfl⟩ := StacksTag09NE.exists_component_point_of_sigma Z p
    exact Set.mem_iUnion.mpr ⟨i, z, by simp [← Scheme.Hom.comp_apply]⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨Sigma.ι Z i z, by simp [← Scheme.Hom.comp_apply]⟩

/-- The morphism out of a finite coproduct of schemes is onto exactly when the ranges of the
components cover. -/
theorem surjective_sigmaDesc_iff [Finite ι] (f : ∀ i, Z i ⟶ X) :
    Surjective (Sigma.desc f) ↔ ⋃ i, Set.range (f i).base = Set.univ := by
  have : Small.{u} ι := inferInstance
  rw [AlgebraicGeometry.surjective_iff, ← Set.range_eq_univ, range_sigmaDesc]

/-- **The reduced case of [Stacks, Tag 09NL], in the tag's own vocabulary.** A reduced scheme
admitting a finite family of affine closed subschemes whose coproduct maps onto it is affine.

This is `Stacks.AffineClosedUnion.isAffine_of_isClosedImmersion_iUnion` with the set-theoretic
covering hypothesis written as surjectivity of
`CategoryTheory.Limits.Sigma.desc`. The tag itself has no reducedness hypothesis; it holds
without one as
`Stacks.AffineClosedUnion.isAffine_of_surjective_sigmaDesc_unconditional`. -/
theorem isAffine_of_surjective_sigmaDesc [IsReduced X] [Finite ι] (f : ∀ i, Z i ⟶ X)
    [∀ i, IsAffine (Z i)] [∀ i, IsClosedImmersion (f i)]
    [hsurj : Surjective (Sigma.desc f)] : IsAffine X :=
  have : Small.{u} ι := inferInstance
  isAffine_of_isClosedImmersion_iUnion f ((surjective_sigmaDesc_iff f).mp hsurj)

end Stacks.AffineClosedUnion

end
