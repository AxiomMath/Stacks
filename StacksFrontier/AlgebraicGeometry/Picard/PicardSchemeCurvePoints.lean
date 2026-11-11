module

public import StacksFrontier.AlgebraicGeometry.Picard.PicardSchemeCurve

/-!
# The `k`-points of the degree components of the Picard scheme of a curve

Clause (2) of [Stacks, Tag 0BA0] in the setting of
`StacksFrontier/AlgebraicGeometry/Picard/PicardSchemeCurve.lean`: for a smooth projective curve `X`
over a separably closed field `k`, the natural map from the `k`-points of `Pic^d_{X/k}` to `Pic(X)`
is a bijection onto the classes of degree `d`. The natural map sends a `k`-point `q` to the class
`Stacks.PicardFunctor.picardPointsEquiv` assigns to `q` followed by the inclusion of `Pic^d_{X/k}`:
the invertible `𝒪_X`-module whose class in `Pic_{X/k}(Spec k)` is the one `q` classifies.

## Main results

* `Stacks.AbelMap.picardScheme_clause_two_bijOn`: [Stacks, Tag 0BA0], clause (2).

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.PicardFunctor Stacks.PicardCurve

universe u

namespace Stacks.AbelMap

variable {k : Type u} [Field k] [IsSepClosed k] (B : BigFppfSite.{u}) {X : Scheme.{u}}
  (hX : B.Contains X) (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [Smooth (B.inclusion.map f)]
  (hproj : IsProjective (B.inclusion.map f))

include hproj in
/-- **Stacks Project, Tag 0BA0, clause (2).** For a smooth projective curve `X` over a separably
closed field `k`, the natural map from the `k`-points of `Pic^d_{X/k}` to `Pic(X)`, sending a
point `q` to the invertible `𝒪_X`-module whose class in `Pic_{X/k}(Spec k)` is classified by `q`
followed by the inclusion `Pic^d_{X/k} ⟶ Pic_{X/k}`, is a bijection onto the invertible modules of
degree `d`. -/
@[stacks 0BA0 "(2)"]
theorem picardScheme_clause_two_bijOn (d : ℤ) :
    haveI := geometricallyIrreducible_of_isSepClosed B hX hk f
    haveI := isProjectiveVariety_of_isProjective B hX hk f hproj
    haveI := isRepresentable_picardFunctor_of_isSepClosed B hX hk f
    Set.BijOn
      (fun q : baseOver B hk ⟶ picardSchemeDegreeComponent B hX hk f (curveSection B hX hk f)
          (curveSection_comp B hX hk f) d =>
        picardPointsEquiv B hX hk f (curveSection B hX hk f) (curveSection_comp B hX hk f)
          (isIso_baseChangeProj_c_of_isCurve B hX hk f (curveSection B hX hk f)
            (curveSection_comp B hX hk f))
          (q ≫ picardSchemeDegreeComponentι B hX hk f (curveSection B hX hk f)
            (curveSection_comp B hX hk f) d))
      Set.univ
      {x : Stacks.Picard.ofScheme X |
        @invertibleCurveDegree k _ X (B.inclusion.map f) _
          (IsCurve.topologicalKrullDim_eq_one (k := k) (f := B.inclusion.map f)).le (rep x)
          (Stacks.Picard.picardRepresentative X.toRingedSpace x).property = d} := by
  have := geometricallyIrreducible_of_isSepClosed B hX hk f
  have := isProjectiveVariety_of_isProjective B hX hk f hproj
  have := isRepresentable_picardFunctor_of_isSepClosed B hX hk f
  let E := degreePointsEquiv' B hX hk f (curveSection B hX hk f) (curveSection_comp B hX hk f) d
  refine ⟨fun q _ => (E q).2, fun q₁ _ q₂ _ h => E.injective (Subtype.ext h), fun x hx =>
    ⟨E.symm ⟨x, hx⟩, Set.mem_univ _, congrArg Subtype.val (E.apply_symm_apply ⟨x, hx⟩)⟩⟩

end Stacks.AbelMap

end
