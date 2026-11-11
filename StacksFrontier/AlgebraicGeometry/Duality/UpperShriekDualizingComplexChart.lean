module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplex

/-!
# `f^!` of a dualizing complex, reduced to the affine-chart description of `f^!`

`Stacks.Duality.isDualizingComplex_upperShriek_of_fts` proves [Stacks, Tag 0AA3] over two carried
inputs: `h0A86`, the cover criterion for dualizing complexes, and `h0AA1`, the affine-chart
description of `f^!`. The first is now a theorem, [Stacks, Tag 0A86]
(`Stacks.Duality.isDualizingComplex_of_hasDualizingModelOn_cover`), and this file discharges it:
`Stacks.Duality.isDualizingComplex_upperShriek_of_fts_of_chart` asks only for the chart
description.

## Main results

* `Stacks.Duality.isDualizingComplex_upperShriek_of_fts_of_chart` — if an exceptional inverse image
  functor `f^!` restricts on every affine chart `U ⊆ f⁻¹(V)` to the algebraic upper shriek of a
  polynomial presentation of `Γ(V) → Γ(U)`, it carries dualizing complexes to dualizing complexes.

## Implementation notes

**No `stacks 0AA3` attribute is placed here**: the chart hypothesis `hchart` is the content of
[Stacks, Tag 0AA1] together with clause (b) of [Stacks, Remark 0BV2], so this statement is
conditional on it. The unconditional [Stacks, Tag 0AA3], for the constructed functor
`Stacks.Duality.upperShriek f j` of [Stacks, Tag 0A9Y], is
`Stacks.Duality.isDualizingComplex_upperShriek_obj` in
`StacksFrontier/AlgebraicGeometry/Duality/UpperShriekDualizingComplexOfCharts.lean`; there the chart
description is the theorem `Stacks.Duality.upperShriekCharts` ([Stacks, Tag 0BV2]), proved through
[Stacks, Tag 0AA1] (`Stacks.Duality.nonempty_upperShriekPlus_affineLineProj_iso`).

The hypothesis is not provable for `fShriek := Stacks.Duality.twistedInverseImage f` (the right
adjoint of `Rf_*`) when `f` is not proper: for an open immersion `j` that right adjoint is not
`j^*` (for `U = D(t) ⊆ Spec k[t]` it sends `k[t]` to a module other than `k[t, 1/t]`), and the
identification `j^! = j^*` of [Stacks, Tag 0AU0] is a statement about the compactification
construction, `Stacks.Duality.upperShriekIsoDerivedPullbackOfOpenImmersion`. For `f` proper the
two functors agree (`Stacks.Duality.upperShriekProperIso`) and `hchart` is true.

## References

* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0AA1](https://stacks.math.columbia.edu/tag/0AA1)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

/-- **`f^!` of a dualizing complex is dualizing, given the affine-chart description of `f^!`.**
The cover criterion of [Stacks, Tag 0A86], carried by
`Stacks.Duality.isDualizingComplex_upperShriek_of_fts`, is discharged; the remaining hypothesis
`hchart` is [Stacks, Tag 0AA1] with clause (b) of [Stacks, Remark 0BV2]. -/
theorem isDualizingComplex_upperShriek_of_fts_of_chart {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FTS S} (f : X ⟶ Y)
    (fShriek : quasiCoherentDerivedCategoryPlus Y.left ⥤ quasiCoherentDerivedCategoryPlus X.left)
    (K : quasiCoherentDerivedCategoryPlus Y.left)
    (hchart : ∀ (U : X.left.Opens) (hU : IsAffineOpen U) (V : Y.left.Opens)
      (hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V)
      (ω : DerivedCategory (ModuleCat.{u} Γ(Y.left, V))),
      IsTildeModelOn K.obj.obj V hV ω →
      ∃ p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom,
        IsTildeModelOn (fShriek.obj K).obj.obj U hU (p.upperShriekFunctor.{u, u}.obj ω))
    (hK : IsDualizingComplex K.obj.obj) :
    IsDualizingComplex (fShriek.obj K).obj.obj :=
  isDualizingComplex_upperShriek_of_fts f fShriek K
    (fun L hL => by
      choose U hU hxU hL using hL
      exact isDualizingComplex_of_hasDualizingModelOn_cover U hU
        (eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) hL)
    hchart hK

end Stacks.Duality

end
