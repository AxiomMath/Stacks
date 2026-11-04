module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSemistableGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothOfLimitPreserving

/-!
# `Curves^{semistable}` and `Curves^{semistable}_g` are smooth over `Spec(ℤ)`

A semistable family of curves is prestable, hence at-worst-nodal of relative dimension one, so
`Curves^{semistable}` and each `Curves^{semistable}_g` are open substacks of `Curves^{nodal}`,
which is smooth over `Spec(ℤ)`. The statements are about the small model
`AlgebraicGeometry.curvesAlgebraicStack B hZ h` of the stack of curves, and take as hypotheses
`h`, the algebraicity of the stack of curves, and `hlim`, its limit preservation; the open
substacks are those cut out by `hss` and `hssg`.

## Main results

* `isSmoothOverIntegers_semistable_of_isLimitPreserving`: `Curves^{semistable} → Spec(ℤ)` is
  smooth.
* `isSmoothOverIntegers_semistableOfFibreGenus_of_isLimitPreserving`:
  `Curves^{semistable}_g → Spec(ℤ)` is smooth.
* `isSmoothOverIntegers_semistable_and_ofFibreGenus_of_isLimitPreserving`: both, for every `g`.

## References

* [Stacks Project, Tag 0E72](https://stacks.math.columbia.edu/tag/0E72)
* [Stacks Project, Tag 0E00](https://stacks.math.columbia.edu/tag/0E00)
* [Stacks Project, Tag 0E70](https://stacks.math.columbia.edu/tag/0E70)
* [Stacks Project, Tag 0E71](https://stacks.math.columbia.edu/tag/0E71)
-/

@[expose] public section

universe u w

namespace AlgebraicGeometry.C1590Private

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- With `h` the algebraicity of the stack of curves and `hlim` its limit preservation, the open
substack `Curves^{semistable}` cut out by `hss` is smooth over `Spec(ℤ)`. -/
theorem isSmoothOverIntegers_semistable_of_isLimitPreserving
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hss : IsOpenCurvesLocus B hZ (IsSemistableCurveFamily B hZ)) :
    IsSmoothOverIntegers B hZ h hss :=
  isSmoothOverIntegers_of_imp B hZ h _ _ (fun _ hF => hF.1.1)
    (isSmoothOverIntegers_nodal_of_isLimitPreserving B hZ h hlim)

/-- With `h` the algebraicity of the stack of curves and `hlim` its limit preservation, the open
substack `Curves^{semistable}_g` of semistable curves of genus `g`, cut out by `hssg`, is smooth
over `Spec(ℤ)`. -/
theorem isSmoothOverIntegers_semistableOfFibreGenus_of_isLimitPreserving
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ)) (g : ℕ)
    (hssg : IsOpenCurvesLocus B hZ (IsSemistableCurveFamilyOfFibreGenus B hZ g)) :
    IsSmoothOverIntegers B hZ h hssg :=
  isSmoothOverIntegers_of_imp B hZ h _ _ (fun _ hF => hF.1.1.1)
    (isSmoothOverIntegers_nodal_of_isLimitPreserving B hZ h hlim)

/-- With `h` the algebraicity of the stack of curves and `hlim` its limit preservation,
`Curves^{semistable}` (cut out by `hss`) is smooth over `Spec(ℤ)`, and for every `g` so is
`Curves^{semistable}_g` (cut out by `hssg g`). -/
theorem isSmoothOverIntegers_semistable_and_ofFibreGenus_of_isLimitPreserving
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hss : IsOpenCurvesLocus B hZ (IsSemistableCurveFamily B hZ))
    (hssg : ∀ g : ℕ, IsOpenCurvesLocus B hZ (IsSemistableCurveFamilyOfFibreGenus B hZ g)) :
    IsSmoothOverIntegers B hZ h hss ∧ ∀ g : ℕ, IsSmoothOverIntegers B hZ h (hssg g) :=
  ⟨isSmoothOverIntegers_semistable_of_isLimitPreserving B hZ h hlim hss,
    fun g =>
      isSmoothOverIntegers_semistableOfFibreGenus_of_isLimitPreserving B hZ h hlim g (hssg g)⟩

end AlgebraicGeometry.C1590Private

end
