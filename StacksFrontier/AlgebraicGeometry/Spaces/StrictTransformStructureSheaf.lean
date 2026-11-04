module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformComparisonOffExceptional
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsEtaleRestriction

/-!
# The strict transform of the structure sheaf

Let `b : A' ⟶ A` be the blowup of an algebraic space `A` in a closed subspace `Z` and let
`f : X ⟶ A` be a morphism of algebraic spaces.  The strict transform `X'` of `X` is the closed
subspace of `X ×_A A'` cut out by the ideal of sections of the structure sheaf supported on the
exceptional preimage (Stacks 0862, and
`AlgebraicGeometry.Space.definingIdealSheaf_strictTransform_of_isBlowupAlong` for a blowup).
Consequently the strict transform of the `𝒪_X`-module `𝒪_X` is `j_*𝒪_{X'}`, where
`j : X' ⟶ X ×_A A'` is the inclusion: the two strict transforms of Stacks 0862 match.

## Main results

* `AlgebraicGeometry.Space.nonempty_strictTransformSheaf_unit_iso`: the strict transform of the
  structure sheaf with respect to a blowup is the structure sheaf of the strict transform.

## References

* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 09RP](https://stacks.math.columbia.edu/tag/09RP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The strict transform of the structure sheaf is the structure sheaf of the strict
transform.**  For `b : A' ⟶ A` the blowup of `A` in a closed subspace `Z` and `f : X ⟶ A`, the
strict transform of `𝒪_X` relative to `b` is `j_*𝒪_{X'}`, where `j : X' ⟶ X ×_A A'` is the
inclusion of the strict transform of `X`.

The pullback of `𝒪_X` to `X ×_A A'` is the structure sheaf, the quotient of the structure sheaf
by its sections supported on the exceptional preimage is the quotient by the defining ideal of
`X'` (`AlgebraicGeometry.Space.definingIdealSheaf_strictTransform_of_isBlowupAlong`), and that
quotient is `j_*𝒪_{X'}` (Stacks 09RP in degree zero). -/
theorem nonempty_strictTransformSheaf_unit_iso {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (b : A' ⟶ A) {Z : ClosedSubspaces B S hS A.1} (hb : IsBlowupAlong B S hS Z b) :
    Nonempty (strictTransformSheaf B S hS f b (Z.1.preimage b.hom)
        (SheafOfModules.unit (structureRingSheaf B S hS X)) ≅
      pushforwardStructureSheaf B S hS (strictTransformPullback B S hS f b)
        (strictTransform B S hS f b (Z.1.preimage b.hom))) := by
  have e₂ := conormalAlgebraDegreeZeroIso B S hS (strictTransformPullback B S hS f b)
    (strictTransform B S hS f b (Z.1.preimage b.hom))
  change cokernel (definingIdealSheaf B S hS (strictTransformPullback B S hS f b)
    (strictTransform B S hS f b (preimageClosedSubspace b Z).1)).ι ≅ _ at e₂
  rw [definingIdealSheaf_strictTransform_of_isBlowupAlong B S hS f b Z hb] at e₂
  exact ⟨supportedSectionsQuotientMapIso B S hS _ _ _
      (modulePullbackUnitIso B S hS (strictTransformPullbackToSource B S hS f b)) ≪≫ e₂⟩

end AlgebraicGeometry.Space

end
