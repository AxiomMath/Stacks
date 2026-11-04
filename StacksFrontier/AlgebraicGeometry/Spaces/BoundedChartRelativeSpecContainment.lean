module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartRestriction

/-!
# The chart-level relative spectrum of a bounded algebra, from a dominating chart

Let `𝒜` be an algebra sheaf on an algebraic space `X` whose sections over every étale chart have
cardinality below the cutoff of the big fppf site. If `V'` is an étale chart of `X` from which
the restriction maps of `𝒜` to the affine opens `W` of `chartScheme V` are all surjective, then
`#(𝒜(V'))` bounds every `#(𝒜(W))` and lies below the cutoff. For a quasi-coherent algebra this
makes the relative spectrum of its restriction to `chartScheme V` an object of the site.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.exists_bound_restrictToChartScheme_of_dominatingChart`:
  a chart dominating the affine opens of `chartScheme V` gives a bound below the cutoff on the
  sections of `𝒜` over all of them.
* `AlgebraicGeometry.Space.contains_relativeSpec_restrictToChartScheme_of_dominatingChart`: given
  such a chart, the relative spectrum of the restriction of `𝒜` to `chartScheme V` is an object
  of the site.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ)
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS}

/-- **A single chart dominating the affine opens of a given one gives a uniform bound.**
If `V'` is an étale chart of `X` and the restriction map of `𝒜` from `V'` to the chart
`W ⊆ chartScheme V` is surjective for every affine open `W`, then `#(𝒜(V'))` bounds `#(𝒜(W))`
for all of them at once, and it is below the cutoff because
`AlgebraicGeometry.Space.AlgebraSheaf.SectionsBelowCutoff` holds at `V'`. -/
theorem AlgebraSheaf.exists_bound_restrictToChartScheme_of_dominatingChart
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A)
    (V V' : SmallEtale B S hS X.1)
    (hdom : ∀ W : (chartScheme V).affineOpens,
      ∃ g : (chartOpens B S hS V).obj (W : (chartScheme V).Opens) ⟶ V',
        Function.Surjective ((CategoryTheory.forget CommRingCat.{u}).map (A.right.obj.map g.op))) :
    ∃ μ < B.cutoff, ∀ W : (chartScheme V).affineOpens,
      #((A.restrictToChartScheme B S hS V).right.obj.obj
        (op (W : (chartScheme V).Opens))) ≤ μ := by
  refine ⟨#(A.right.obj.obj (op V')), hA V', fun W => ?_⟩
  obtain ⟨g, hg⟩ := hdom W
  exact mk_le_of_surjective hg

/-- **The relative spectrum of the chart restriction is an object of the site**, given one chart
dominating the affine opens of the chart in question. -/
theorem contains_relativeSpec_restrictToChartScheme_of_dominatingChart
    (A : QuasicoherentAlgebra B S hS X)
    (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A.obj)
    (V V' : SmallEtale B S hS X.1)
    (hdom : ∀ W : (chartScheme V).affineOpens,
      ∃ g : (chartOpens B S hS V).obj (W : (chartScheme V).Opens) ⟶ V',
        Function.Surjective
          ((CategoryTheory.forget CommRingCat.{u}).map (A.obj.right.obj.map g.op))) :
    B.Contains (Stacks.AffineAlgebraEquivalence.relativeSpec
      (A.obj.restrictToChartScheme B S hS V)) := by
  obtain ⟨μ, hμ, hbound⟩ :=
    AlgebraSheaf.exists_bound_restrictToChartScheme_of_dominatingChart B S hS hA V V' hdom
  exact B.contains_relativeSpec (A.obj.restrictToChartScheme B S hS V)
    V.obj.left.left.property hμ hbound

end AlgebraicGeometry.Space

end
