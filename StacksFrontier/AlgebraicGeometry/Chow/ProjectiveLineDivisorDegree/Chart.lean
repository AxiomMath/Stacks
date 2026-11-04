module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.SpecDegree

/-!
# The contribution of an affine chart to the degree of a principal divisor

Let `P` be an integral scheme over `Spec k`, `k` a field, and let `j : Spec k[T] ⟶ P` be an open
immersion over `Spec k`. Then the part of the weighted sum of orders of vanishing of a rational
function on `P` which is supported on the image of `j` is the integer degree of the rational
function read in the coordinate `T`.

## Main definitions

* `Stacks.Chow.chartFunctionFieldEquiv` — the identification of the function field of `P` with
  `RatFunc k` given by a chart.

## Main results

* `Stacks.Chow.isDominant_of_isOpenImmersion` — a nonempty open immersion into an irreducible
  scheme is dominant.
* `Stacks.Chow.dominantFunctionFieldMap_chartFunctionFieldEquiv_symm` — the chart identification
  is undone by the function-field map of the chart.
* `Stacks.Chow.ord_chart_irreduciblePoint` — the order of vanishing at the image of the point cut
  out by a monic irreducible polynomial is `Stacks.Chow.ordAt` of it.
* `Stacks.Chow.finsum_mem_range_ord_mul_residueDegree` — **the chart contribution**: the sum over
  the image of the chart is the integer degree.

## Implementation notes

The compatibility of the chart with the two structure morphisms is taken as the hypothesis
`hj : j ≫ c = specPolynomialOver k`.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace Polynomial

universe u

namespace Stacks.Chow

/-- A nonempty open immersion into an irreducible scheme is dominant: its image is a nonempty
open subset, hence dense. -/
theorem isDominant_of_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    [IrreducibleSpace Y] [Nonempty X] : IsDominant j := by
  rw [isDominant_iff]
  exact (IsOpenImmersion.isOpen_range j).dense (Set.range_nonempty _)

variable (k : Type u) [Field k] {P : Scheme.{u}} [AlgebraicGeometry.IsIntegral P]
  [IsLocallyNoetherian P] (j : specPolynomial k ⟶ P) [IsOpenImmersion j] [IsDominant j]

/-- The identification of the function field of `P` with the field of rational functions given by
an affine chart: an open immersion induces an isomorphism of function fields, and the function
field of `Spec k[T]` is `RatFunc k`. -/
def chartFunctionFieldEquiv : P.functionField ≃+* RatFunc k :=
  (functionFieldEquiv_openImmersion j).trans (ratFuncEquivFunctionField k)

omit [IsLocallyNoetherian P] in
/-- `Stacks.Chow.chartFunctionFieldEquiv` is the function-field map of the chart, followed by the
identification of the function field of `Spec k[T]` with `RatFunc k`. -/
theorem chartFunctionFieldEquiv_apply (h : P.functionField) :
    chartFunctionFieldEquiv k j h
      = ratFuncEquivFunctionField k (dominantFunctionFieldMap j h) := rfl

omit [IsLocallyNoetherian P] in
/-- The function-field map of the chart undoes `Stacks.Chow.chartFunctionFieldEquiv`: it carries
the rational function with a prescribed reading in the chart to that reading. -/
theorem dominantFunctionFieldMap_chartFunctionFieldEquiv_symm (y : RatFunc k) :
    dominantFunctionFieldMap j ((chartFunctionFieldEquiv k j).symm y)
      = (ratFuncEquivFunctionField k).symm y := by
  have h : (chartFunctionFieldEquiv k j).symm y
      = (functionFieldEquiv_openImmersion j).symm ((ratFuncEquivFunctionField k).symm y) := rfl
  rw [h]
  exact (functionFieldEquiv_openImmersion j).apply_symm_apply _

/-- The order of vanishing of a rational function on `P` at the image of the point of `Spec k[T]`
cut out by a monic irreducible polynomial `p` is `Stacks.Chow.ordAt p` of the rational function
read in the chart. -/
theorem ord_chart_irreduciblePoint [DecidableEq k] {p : Polynomial k} (hp : Irreducible p)
    (hpm : p.Monic) (h : P.functionField) (hh : h ≠ 0) :
    P.ord h (j.base (irreduciblePoint (CommRingCat.of (Polynomial k)) hp))
      = ordAt p (chartFunctionFieldEquiv k j h) := by
  rw [← ord_dominantFunctionFieldMap_of_isOpenImmersion j h,
    chartFunctionFieldEquiv_apply]
  exact ord_irreduciblePoint_eq_ordAt k hp hpm _
    (((_root_.map_ne_zero _).2 hh))

/-- **The contribution of an affine chart to the degree of a principal divisor.** The weighted sum
of the orders of vanishing of a nonzero rational function on `P`, restricted to the image of the
chart, is the integer degree of the rational function read in the chart. -/
theorem finsum_mem_range_ord_mul_residueDegree (c : P ⟶ Spec (CommRingCat.of k))
    (hj : j ≫ c = specPolynomialOver k) (h : P.functionField) (hh : h ≠ 0) :
    (∑ᶠ x ∈ Set.range j.base, P.ord h x * (c.residueDegree x : ℤ))
      = (chartFunctionFieldEquiv k j h).intDegree := by
  classical
  have hbij : Set.BijOn j.base Set.univ (Set.range j.base) := by
    rw [← Set.image_univ]
    exact (Scheme.Hom.isOpenEmbedding j).injective.injOn.bijOn_image
  have hpoint : ∀ y : specPolynomial k, y ∈ (Set.univ : Set (specPolynomial k)) →
      (specPolynomial k).ord (dominantFunctionFieldMap j h) y
          * ((specPolynomialOver k).residueDegree y : ℤ)
        = P.ord h (j.base y) * (c.residueDegree (j.base y) : ℤ) := by
    intro y _
    rw [ord_dominantFunctionFieldMap_of_isOpenImmersion j h y,
      ← residueDegree_isOpenImmersion_comp j c y, hj]
  calc (∑ᶠ x ∈ Set.range j.base, P.ord h x * (c.residueDegree x : ℤ))
      = ∑ᶠ y ∈ (Set.univ : Set (specPolynomial k)),
          (specPolynomial k).ord (dominantFunctionFieldMap j h) y
            * ((specPolynomialOver k).residueDegree y : ℤ) :=
        (finsum_mem_eq_of_bijOn j.base hbij hpoint).symm
    _ = ∑ᶠ y : specPolynomial k, (specPolynomial k).ord (dominantFunctionFieldMap j h) y
            * ((specPolynomialOver k).residueDegree y : ℤ) := finsum_mem_univ _
    _ = (ratFuncEquivFunctionField k (dominantFunctionFieldMap j h)).intDegree :=
        finsum_ord_mul_residueDegree_specPolynomial k _
          (((_root_.map_ne_zero _).2 hh))
    _ = (chartFunctionFieldEquiv k j h).intDegree := rfl

end Stacks.Chow

end
