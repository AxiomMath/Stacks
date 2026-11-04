module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.BaseChangeAcyclicity

/-!
# The overlaps of the cover of `X ×_R Y` induced by an open cover of `X`

Let `R` be a commutative ring and let `X` and `Y` be schemes over `R`.  An open subscheme `U` of
`X` gives the open immersion `U ×_R Y ⟶ X ×_R Y`, which is
`AlgebraicGeometry.baseChangeOpenTargetMap`, with open range `pr_1^{-1}(U)`
(`AlgebraicGeometry.opensRange_baseChangeOpenTargetMap`), and the charts attached to the affine
opens of `X` cover `X ×_R Y` (`AlgebraicGeometry.iSup_opensRange_baseChangeOpenTargetMap`).  This
family is closed under overlaps: the intersection of the chart of `U` and the chart of `V` is the
chart of `U ⊓ V`, because `pr_1^{-1}` preserves intersections.

## Main results

* `AlgebraicGeometry.opensRange_baseChangeOpenTargetMap_inf`: the overlap of two charts of
  `X ×_R Y` is the chart of the intersection.

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### The overlap of two charts -/

section Relative

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))

/-- The overlap of the charts `U ×_R Y` and `V ×_R Y` of `X ×_R Y` is the chart
`(U ⊓ V) ×_R Y`. -/
theorem opensRange_baseChangeOpenTargetMap_inf (U V : X.left.Opens) :
    (baseChangeOpenTargetMap R X Y U).opensRange ⊓
        (baseChangeOpenTargetMap R X Y V).opensRange =
      (baseChangeOpenTargetMap R X Y (U ⊓ V)).opensRange := by
  rw [opensRange_baseChangeOpenTargetMap, opensRange_baseChangeOpenTargetMap,
    opensRange_baseChangeOpenTargetMap]
  rfl

end Relative

end AlgebraicGeometry

end
