module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.CubeSectionRing
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveAlgebraization

/-!
# Ampleness of the conormal sheaf of a curve with conormal `𝒪_C(p)`

Let `C` be a proper smooth geometrically connected curve over a field `k` and `p` a `k`-point of
`C`. The invertible module `𝒪_C(p)` has degree one, so it is ample ([Stacks, Tag 0B5X]). Hence if
`C ⊆ X` is an effective Cartier divisor whose conormal sheaf `𝒪_X(-C)|_C` is isomorphic to
`𝒪_C(p)`, the conormal sheaf is ample: this is the ampleness hypothesis of
`AlgebraicGeometry.Scheme.IdealSheafData.exists_isProper_algebraization`, in the situation of
Stacks 0D5E.

## Main results

* `AlgebraicGeometry.GenusOne.isAmple_pointDivisorSheaf_one`: `𝒪_C(p)` is ample.
* `AlgebraicGeometry.Scheme.IdealSheafData.isAmple_conormalModule_of_iso_pointDivisorSheaf`: the
  conormal sheaf is ample when it is `𝒪_C(p)`.

## References

* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.Divisors (IsEffectiveCartierDivisor)

universe u

namespace AlgebraicGeometry

namespace GenusOne

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  (h0 : Module.finrank k (structureSheafCohomology (X ↘ Spec (.of k)) 0) = 1)
  (p : Spec (.of k) ⟶ X) (hp : p ≫ (X ↘ Spec (.of k)) = 𝟙 _)
  [IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
    (⟨{point p}, isClosed_point (X ↘ Spec (.of k)) p hp⟩ : Closeds X) ^ 1)]

include h0 in
/-- **`𝒪_X(p)` is ample on a proper smooth curve with `H⁰(X, 𝒪_X) = k`**: it has degree one
([Stacks, Tag 0B5X]). -/
theorem isAmple_pointDivisorSheaf_one :
    Stacks.Ample.IsAmple X (pointDivisorSheaf p hp 1) := by
  have := isCurve (X ↘ Spec (.of k)) h0
  have hdim : topologicalKrullDim X ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := X ↘ Spec (.of k))).le
  have hdeg1 := invertibleCurveDegree_vanishingIdeal_point_pow (X ↘ Spec (.of k)) h0 hdim p hp 1
  exact Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X _
    ((isAmple_iff_invertibleCurveDegree_pos k (X ↘ Spec (.of k)) hdim _).mpr
      (by rw [hdeg1]; norm_num))

end GenusOne

namespace Scheme.IdealSheafData

variable {k : Type u} [Field k] {Z : Scheme.{u}} (D : Z.IdealSheafData)
  [IsEffectiveCartierDivisor D]
  [D.subscheme.Over (Spec (.of k))] [IsProper (D.subscheme ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 1 (D.subscheme ↘ Spec (.of k))]

/-- **The conormal sheaf of a curve is ample when it is `𝒪_C(p)`.** Let `C ⊆ Z` be an effective
Cartier divisor which is a proper smooth curve over `k` with `H⁰(C, 𝒪_C) = k`, and `p` a `k`-point
of `C`. If `𝒪_Z(-C)|_C ≅ 𝒪_C(p)`, then `𝒪_Z(-C)|_C` is ample. -/
theorem isAmple_conormalModule_of_iso_pointDivisorSheaf
    (h0 : Module.finrank k (structureSheafCohomology (D.subscheme ↘ Spec (.of k)) 0) = 1)
    (p : Spec (.of k) ⟶ D.subscheme) (hp : p ≫ (D.subscheme ↘ Spec (.of k)) = 𝟙 _)
    [IsEffectiveCartierDivisor (vanishingIdeal
      (⟨{GenusOne.point p}, GenusOne.isClosed_point (D.subscheme ↘ Spec (.of k)) p hp⟩ :
        Closeds D.subscheme) ^ 1)]
    (ψ : (Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.negativeTwist D) ≅
      GenusOne.pointDivisorSheaf p hp 1) :
    Stacks.Ample.IsAmple D.subscheme (conormalModule D) :=
  (Stacks.RelativeVeryAmple.isAmple_congr _ _ ψ).mpr
    (GenusOne.isAmple_pointDivisorSheaf_one h0 p hp)

end Scheme.IdealSheafData

end AlgebraicGeometry

end
