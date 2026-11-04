module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable

/-!
# Smoothness of the moduli stacks of stable curves over `Spec(ℤ)` (towards Stacks 0E79)

`𝓜̄ = Curves^{stable}` and `𝓜̄_g` are open substacks of `Curves^{nodal}`, a stable family of curves
being at-worst-nodal of relative dimension one. Smoothness of `Curves^{nodal}` over `Spec(ℤ)`
(Tag 0E00) therefore passes to them, which is the proof of Tag 0E79.

## Main results

* `AlgebraicGeometry.isSmoothOverIntegers_stable_of_nodal`: `𝓜̄ ⟶ Spec(ℤ)` is smooth if
  `Curves^{nodal} ⟶ Spec(ℤ)` is.
* `AlgebraicGeometry.isSmoothOverIntegers_stableOfGenus_of_nodal`: the same for `𝓜̄_g`.

## References

* [Stacks Project, Tag 0E79](https://stacks.math.columbia.edu/tag/0E79)
* [Stacks Project, Tag 0E00](https://stacks.math.columbia.edu/tag/0E00)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **Tag 0E79 from Tag 0E00, for `𝓜̄`.** If `Curves^{nodal}` is smooth over `Spec(ℤ)`, so is the
open substack `𝓜̄ = Curves^{stable}`, a stable family of curves being at-worst-nodal of relative
dimension one. -/
theorem isSmoothOverIntegers_stable_of_nodal
    (hst : IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ))
    (hsm : IsSmoothOverIntegers B hZ h (isOpenCurvesLocus_isAtWorstNodal B hZ)) :
    IsSmoothOverIntegers B hZ h hst :=
  isSmoothOverIntegers_of_imp B hZ h _ _ (fun _ hF => hF.1.1) hsm

/-- **Tag 0E79 from Tag 0E00, for `𝓜̄_g`.** If `Curves^{nodal}` is smooth over `Spec(ℤ)`, so is the
open substack `𝓜̄_g` of stable curves of genus `g`. -/
theorem isSmoothOverIntegers_stableOfGenus_of_nodal (g : ℕ)
    (hst : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g))
    (hsm : IsSmoothOverIntegers B hZ h (isOpenCurvesLocus_isAtWorstNodal B hZ)) :
    IsSmoothOverIntegers B hZ h hst :=
  isSmoothOverIntegers_of_imp B hZ h _ _ (fun _ hF => hF.1.1.1) hsm

end AlgebraicGeometry

end
