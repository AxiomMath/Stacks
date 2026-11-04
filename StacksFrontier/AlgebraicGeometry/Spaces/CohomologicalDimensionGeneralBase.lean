module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZariskiLocallyQuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology

/-!
# The choices (1)–(3) of Stacks 072C over an arbitrary base scheme

`AlgebraicGeometry.Space.exists_affine_etale_surjective_cover_hasUniversallyBoundedFibers` of
`StacksFrontier.AlgebraicGeometry.Spaces.CohomologicalDimension` makes the first three choices of the
proof of [Stacks, Tag 072C] — an affine scheme `U`, a surjective étale morphism `U ⟶ X` and an
integer bounding the degrees of its fibres — for a quasi-compact and quasi-separated algebraic
space over an affine base `Spec A`. This file makes them over an arbitrary base scheme `S`, as in
the source.

## Main results

* `AlgebraicGeometry.Space.exists_affine_etale_surjective_cover_hasUniversallyBoundedFibers'`:
  the choices (1)–(3) of Stacks 072C over an arbitrary base scheme.

## References

* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space

section GeneralBase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

include hX in
/-- **The choices (1)–(3) of Stacks 072C.** A quasi-compact, quasi-separated algebraic space
over an arbitrary base scheme `S` carries a surjective étale morphism from an affine scheme
whose fibres are universally bounded in the sense of Stacks 03JL.

The base is an arbitrary scheme, as in the source: nothing in the two inputs — the affine étale
chart of [Stacks, Tag 03H6] and the chain `(η) ⇒ (ζ) ⇒ (ε) ⇒ (δ)` of [Stacks, Tag 03JX] —
restricts it, and quasi-separatedness is taken in the absolute form of [Stacks, Tag 03BS]
part (3), which does not mention `S` either. -/
@[stacks 072C "parts (1)-(3): an affine scheme U, a surjective étale morphism U ⟶ X, and an \
integer bounding the degrees of its fibres, for X a quasi-compact and quasi-separated algebraic \
space over an arbitrary base scheme S"]
theorem exists_affine_etale_surjective_cover_hasUniversallyBoundedFibers'
    (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) :
    ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        IsEtale B S hS g ∧
        HasUniversallyBoundedFibers B S hS U g := by
  obtain ⟨U, g, hU, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).1 hqc
  refine ⟨U, g, hU, hsurj, het, ?_⟩
  refine IsReasonableSpace.hasUniversallyBoundedFibers B S hS X
    (isReasonableSpace_of_isVeryReasonableSpace B S hS X hX
      (isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ
        X hX (isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated
          B S hS X hZ hX hqs))) U hU g ?_
  exact (isEtale_iff_presheaf_of_yoneda B S hS g).1 het

end GeneralBase

end AlgebraicGeometry.Space

end
