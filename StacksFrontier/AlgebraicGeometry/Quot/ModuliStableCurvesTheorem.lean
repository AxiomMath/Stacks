module

public import StacksFrontier.AlgebraicGeometry.Quot.ModuliCurves
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack

/-!
# The moduli stack of stable curves of genus `g`

Let `g ≥ 2`, and let `𝓜̄_g` and `𝓜_g` be the open substacks of the small model
`curvesAlgebraicStack B hZ h` of the stack of curves cut out by being stable of genus `g` and by
being smooth of genus `g`. If `𝓜̄_g` is a Deligne–Mumford stack proper over `Spec(ℤ)`,
`Curves^{nodal}` is smooth over `Spec(ℤ)` (Stacks 0E00) and `|𝓜_g| ⊂ |𝓜̄_g|` is dense, then
`𝓜̄_g` is a Deligne–Mumford stack, proper and smooth over `Spec(ℤ)`, and `𝓜_g` is a dense open
substack of it.

## Main results

* `AlgebraicGeometry.moduliStableCurvesOfGenus_isDeligneMumford_proper_smooth`: under these
  hypotheses, `𝓜̄_g` is a proper smooth Deligne–Mumford stack over `Spec(ℤ)` in which `𝓜_g` is a
  dense open substack.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- Let `g ≥ 2`, and let `𝓜̄_g` and `𝓜_g` be the open substacks of the small model of the stack
of curves cut out by being stable of genus `g` and by being smooth of genus `g`. If `𝓜̄_g` is a
Deligne–Mumford stack, proper over `Spec(ℤ)`, `Curves^{nodal}` is smooth over `Spec(ℤ)`, and
`|𝓜_g| ⊂ |𝓜̄_g|` is dense, then `𝓜̄_g` is a Deligne–Mumford stack, proper and smooth over
`Spec(ℤ)`, and `𝓜_g` is a dense open substack of it. -/
theorem moduliStableCurvesOfGenus_isDeligneMumford_proper_smooth (g : ℕ) (_hg : 2 ≤ g)
    (hP : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g))
    (hQ : IsOpenCurvesLocus B hZ
      (fun X => IsSmoothH0Family B hZ X ∧ CurveFamily.HasGenus B hZ X g))
    (hnodal : IsSmoothOverIntegers B hZ h (isOpenCurvesLocus_isAtWorstNodal B hZ))
    (hDM : Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ
      (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val.val)
    (hproper : Stack.AlgebraicStacks.IsProper B integerBase hZ
      ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
    (hdense : (curvesSmallOpenSubstack B hZ h hQ).pointSet ⊆
        (curvesSmallOpenSubstack B hZ h hP).pointSet ∧
      (curvesSmallOpenSubstack B hZ h hP).pointSet ⊆
        @closure _ (Stack.pointTopology B integerBase hZ (curvesAlgebraicStack B hZ h).val)
          (curvesSmallOpenSubstack B hZ h hQ).pointSet) :
    Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ
        (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val.val ∧
      Stack.AlgebraicStacks.IsProper B integerBase hZ
        ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
          Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) ∧
      IsSmoothOverIntegers B hZ h hP ∧
      (curvesSmallOpenSubstack B hZ h hQ).pointSet ⊆
          (curvesSmallOpenSubstack B hZ h hP).pointSet ∧
        (curvesSmallOpenSubstack B hZ h hP).pointSet ⊆
          @closure _ (Stack.pointTopology B integerBase hZ (curvesAlgebraicStack B hZ h).val)
          (curvesSmallOpenSubstack B hZ h hQ).pointSet :=
  ⟨hDM, hproper, isSmoothOverIntegers_stableOfGenus_of_nodal B hZ h g hP hnodal, hdense⟩

end AlgebraicGeometry
