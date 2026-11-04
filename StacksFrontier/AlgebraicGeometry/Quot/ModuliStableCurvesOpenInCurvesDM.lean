module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyAffineDualizingSheafInvertible
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesIsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesInCurvesDMOfStableFibres
public import StacksCore.Tactic.StacksAttribute

/-!
# `𝓜̄` and `𝓜̄_g` are open substacks of `Curves^{DM}` (Stacks 0E7A)

The moduli stacks `𝓜̄` of stable curves and `𝓜̄_g` of stable curves of genus `g` (Stacks 0E77) are
open substacks of `Curves^{DM}`, the Deligne–Mumford locus of `Curves` (Stacks 0DSW); in
particular they are DM (Stacks 050D) and Deligne–Mumford stacks (Stacks 03YO).

## Main results

* `AlgebraicGeometry.curvesSmall.moduliStableCurves_isOpenSubstack_curvesDM`: `𝓜̄` and `𝓜̄_g` are
  open substacks of `Curves^{DM}`, and they are DM and Deligne–Mumford stacks.

## References

* [Stacks Project, Tag 0E7A](https://stacks.math.columbia.edu/tag/0E7A)
* [Stacks Project, Tag 0E77](https://stacks.math.columbia.edu/tag/0E77)
* [Stacks Project, Tag 0DSW](https://stacks.math.columbia.edu/tag/0DSW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u

namespace AlgebraicGeometry.curvesSmall

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The stacks `𝓜̄` and `𝓜̄_g` are open substacks of `Curves^{DM}`; in particular they are DM
(Stacks 050D) and Deligne–Mumford stacks (Stacks 03YO).

In the statement, `Curves` is the algebraic stack `AlgebraicGeometry.curvesAlgebraicStack` (the
small model of the stack of curves, equivalent over the site to the category of families of
curves through `AlgebraicGeometry.curvesSmallEquivalence`), algebraic by Stacks 0D5A
(`AlgebraicGeometry.curvesFiberedCategory_isAlgebraicStack`). `W` is `Curves^{DM}`: the open
substack whose objects are those of the Deligne–Mumford locus `Stack.dmLocus` (Stacks 0DSW), and
it is DM. `M` is `𝓜̄`: an open substack of `Curves` whose objects are exactly the stable families
of curves (Stacks 0E75), the families of `AlgebraicGeometry.moduliStableCurves`; `M_g` is `𝓜̄_g`:
an open substack whose objects are exactly the stable families whose fibre over every point has
genus `g`, the families of `AlgebraicGeometry.moduliStableCurvesOfGenus` (Stacks 0E77, 0E78).
Both are contained in `W` (an open substack of `Curves` contained in the open substack `W` is an
open substack of `W`), DM, and Deligne–Mumford stacks.

The statement holds for every `g`, not only in the range `g ≥ 2` of Stacks 0E77. -/
@[stacks 0E7A]
theorem moduliStableCurves_isOpenSubstack_curvesDM (g : ℕ) :
    ∃ W M Mg : Stack.OpenSubstack
        (curvesAlgebraicStack B hZ (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)),
      (W.property =
          Stack.dmLocus B integerBase hZ B.contains_terminal
            (curvesAlgebraicStack B hZ (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)) ∧
        Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
          W.toAlgebraicStack) ∧
      ((∀ F : CurveFamily B hZ,
          M.property ((curvesSmallEquivalence B hZ
            (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).functor.obj F) ↔
            IsStableCurveFamily B hZ F) ∧
        M.property ≤ W.property ∧
        Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
          M.toAlgebraicStack ∧
        Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ M.toAlgebraicStack.val.val) ∧
      ((∀ F : CurveFamily B hZ,
          Mg.property ((curvesSmallEquivalence B hZ
            (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ)).functor.obj F) ↔
            IsStableCurveFamilyOfFibreGenus B hZ g F) ∧
        Mg.property ≤ W.property ∧
        Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
          Mg.toAlgebraicStack ∧
        Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ Mg.toAlgebraicStack.val.val) :=
  exists_curvesDM_moduliStableCurves_le_and_isDeligneMumfordStack_of_hasStableFibres
    (curvesFiberedCategory_isAlgebraicStack.{u, w} B hZ) g
    CurveFamily.isOpenCurvesLocusWithin_hasStableFibres

end AlgebraicGeometry.curvesSmall

end
