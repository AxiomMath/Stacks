module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ModuliSmoothCurvesOpen
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothOfLimitPreserving

/-!
# `𝓜` and `𝓜_g` are smooth over `Spec(ℤ)`

Let `𝓜 = Curves^{smooth, h0}` be the moduli stack of smooth proper curves, the open substack of
`Curves` of families `f : X → S` smooth of relative dimension one with `f_*𝒪_X = 𝒪_S`
universally (`AlgebraicGeometry.IsSmoothH0Family`), and `𝓜_g ⊂ 𝓜` the open and closed substack
of those families whose fibres have genus `g`
(`AlgebraicGeometry.C1590Private.IsSmoothH0FamilyOfFibreGenus`). If the stack of curves is
algebraic and limit preserving, then `𝓜` and every `𝓜_g` are smooth over `Spec(ℤ)`.

The statements are about the model `AlgebraicGeometry.curvesAlgebraicStack B hZ h` of the stack
of curves. They take as hypotheses `h`, the algebraicity of the stack of curves, `hlim`, its limit
preservation, and the openness conditions `hM` of `𝓜` and `hMg` of the `𝓜_g`.

## Main results

* `AlgebraicGeometry.C1590Private.isSmoothOverIntegers_of_le_isSmoothFamily`: if `Curves^{lci+}`
  is smooth over `Spec(ℤ)`, an open substack of `Curves` all of whose families are smooth is
  smooth over `Spec(ℤ)`.
* `AlgebraicGeometry.C1590Private.isSmoothOverIntegers_moduliSmoothCurves_of_isLimitPreserving`:
  given `h`, `hlim`, `hM` and `hMg`, `𝓜 → Spec(ℤ)` and every `𝓜_g → Spec(ℤ)` are smooth.

## References

* [Stacks Project, Tag 0E84](https://stacks.math.columbia.edu/tag/0E84)
* [Stacks Project, Tag 0E81](https://stacks.math.columbia.edu/tag/0E81)
* [Stacks Project, Tag 0E82](https://stacks.math.columbia.edu/tag/0E82)
* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
* [Stacks Project, Tag 0DZX](https://stacks.math.columbia.edu/tag/0DZX)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.C1590Private

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **Open substacks of smooth curves are smooth over `Spec(ℤ)`.** If `Curves^{lci+}` is smooth
over `Spec(ℤ)` and every family with the property `P` is smooth, then the open substack cut out by
`P` is smooth over `Spec(ℤ)`. -/
theorem isSmoothOverIntegers_of_le_isSmoothFamily {P : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) (hPs : ∀ F, P F → IsSmoothFamily B hZ F)
    (hsm : IsSmoothOverIntegers B hZ h (isOpenCurvesLocus_lciPlus B hZ)) :
    IsSmoothOverIntegers B hZ h hP :=
  isSmoothOverIntegers_of_imp B hZ h _ _
    (fun F hF => isSmoothFamily_le_lciPlus B hZ F (hPs F hF)) hsm

/-- **The moduli stacks of smooth proper curves are smooth over `Spec(ℤ)`.** Given `h`, the
algebraicity of the stack of curves, and `hlim`, its limit preservation, the moduli stack
`𝓜 = Curves^{smooth, h0}` of smooth proper curves, open by `hM`, is smooth over `Spec(ℤ)`, and so
is, for every `g`, the moduli stack `𝓜_g` of smooth proper curves of genus `g`, open by
`hMg g`. -/
theorem isSmoothOverIntegers_moduliSmoothCurves_of_isLimitPreserving
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hM : IsOpenCurvesLocus B hZ (IsSmoothH0Family B hZ))
    (hMg : ∀ g : ℕ, IsOpenCurvesLocus B hZ (IsSmoothH0FamilyOfFibreGenus B hZ g)) :
    IsSmoothOverIntegers B hZ h hM ∧ ∀ g : ℕ, IsSmoothOverIntegers B hZ h (hMg g) :=
  have hsm := isSmoothOverIntegers_lciPlus_of_isLimitPreserving B hZ h hlim
  ⟨isSmoothOverIntegers_of_le_isSmoothFamily B hZ h hM (fun _ hF => hF.1.1) hsm,
    fun g => isSmoothOverIntegers_of_le_isSmoothFamily B hZ h (hMg g)
      (fun _ hF => hF.1.1.1) hsm⟩

end AlgebraicGeometry.C1590Private

end
