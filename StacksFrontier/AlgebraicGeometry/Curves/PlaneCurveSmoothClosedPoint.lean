module

public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveSeparablePoint
public import StacksFrontier.RingTheory.Smooth.PlaneHypersurface

/-!
# A smooth closed point of small separable degree on an affine plane curve

Let `k` be an infinite field and let `f ∈ k[x₀, x₁]` be nonzero and not a unit.  This file puts
together the two halves of the affine content of [Stacks, Tag 0CCU]:

* `Stacks.Curves.isSmoothAt_iff_exists_pderiv_notMem`, which turns smoothness of
  `k[x₀, x₁] ⧸ (f)` over `k` at a prime into the nonvanishing of one of the two partial
  derivatives of `f` there, and
* `Stacks.Curves.exists_isMaximal_isSeparable_finrank_le_totalDegree`, which moves from such a
  prime to a *maximal* ideal with the same property and with small separable residue field.

The result is the statement of Tag 0CCU with the projective plane replaced by the affine chart:
from one smooth point of the affine plane curve `V(f)` one gets a closed point of `V(f)` at which
`V(f)` is still smooth over `k` and whose residue field is finite separable over `k` of degree at
most `deg f`.

## Main results

* `Stacks.Curves.exists_isMaximal_isSmoothAt_isSeparable_finrank_le_totalDegree`: the statement
  above.

## Implementation notes

The smooth closed point is returned as a maximal ideal `m` of `k[x₀, x₁]` containing `f` together
with an index `i` for which `∂f/∂xᵢ ∉ m`; feeding that back into
`Stacks.Curves.isSmoothAt_iff_exists_pderiv_notMem` gives smoothness of `k[x₀, x₁] ⧸ (f)` over `k`
at the corresponding prime of the quotient, which is why the smoothness clause is not repeated in
the conclusion.  Stating it there would need the primality of `Ideal.map` inside the existential.

This is not Tag 0CCU: the source's statement is about a closed subscheme of `𝐏²_k` and the closed
point it produces is a point of that scheme, with the scheme-theoretic smooth locus and the
residue field `κ(z)` of the structure sheaf.  Transporting the statement below along the chart
`D₊(T_j)` is what remains; the affine equation of the curve on that chart, with its degree bound,
is `Stacks.ProjectiveChart.ker_app_basicOpen_X_eq_span_dehomCoeff`.

## References

* [Stacks Project, Tag 0CCU](https://stacks.math.columbia.edu/tag/0CCU)
* [Stacks Project, Tag 00TE](https://stacks.math.columbia.edu/tag/00TE)
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k]

/-- **From one smooth point of an affine plane curve to a closed one with small separable residue
field.**  Let `k` be an infinite field and let `f ∈ k[x₀, x₁]` be nonzero and not a unit.  If
`k[x₀, x₁] ⧸ (f)` is smooth over `k` at some prime, then there is a *maximal* ideal `m` of
`k[x₀, x₁]` containing `f` at which some `∂f/∂xᵢ` is still invertible — so that
`Stacks.Curves.isSmoothAt_iff_exists_pderiv_notMem` makes `k[x₀, x₁] ⧸ (f)` smooth over `k` there
too — and whose residue field `k[x₀, x₁] ⧸ m` is a finite separable extension of `k` of degree at
most `deg f`.

This is the whole commutative-algebra content of [Stacks, Tag 0CCU]: the geometric hypothesis
"`Z → Spec(k)` is smooth in at least one point" enters only as smoothness at one prime of the
affine equation on a standard chart, and the conclusion is the closed point with its degree bound.
What Tag 0CCU adds on top is the transport of this statement through the chart of the projective
plane; see `Stacks.ProjectiveChart.ker_app_basicOpen_X_eq_span_dehomCoeff` for the affine equation
of the curve on that chart. -/
theorem exists_isMaximal_isSmoothAt_isSeparable_finrank_le_totalDegree [Infinite k]
    {f : MvPolynomial (Fin 2) k} (hf0 : f ≠ 0) (hfu : ¬ IsUnit f)
    (Q : Ideal (MvPolynomial (Fin 2) k ⧸ Ideal.span {f})) [Q.IsPrime]
    (hQ : Algebra.IsSmoothAt k Q) :
    ∃ m : Ideal (MvPolynomial (Fin 2) k), m.IsMaximal ∧ f ∈ m ∧
      (∃ i : Fin 2, pderiv i f ∉ m) ∧
      Module.Finite k (MvPolynomial (Fin 2) k ⧸ m) ∧
      Algebra.IsSeparable k (MvPolynomial (Fin 2) k ⧸ m) ∧
      Module.finrank k (MvPolynomial (Fin 2) k ⧸ m) ≤ f.totalDegree := by
  obtain ⟨i, hi⟩ := (isSmoothAt_iff_exists_pderiv_notMem hf0 hfu Q).mp hQ
  have hq : (Q.comap (Ideal.Quotient.mk (Ideal.span {f}))).IsPrime :=
    Ideal.IsPrime.comap _
  have hfq : f ∈ Q.comap (Ideal.Quotient.mk (Ideal.span {f})) := by
    refine Ideal.mem_comap.mpr ?_
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]
    exact Q.zero_mem
  obtain ⟨m, hm, hfm, hdm, hfin, hsep, hrank⟩ :=
    exists_isMaximal_isSeparable_finrank_le_totalDegree i hq hfq hi
  exact ⟨m, hm, hfm, ⟨i, hdm⟩, hfin, hsep, hrank⟩

end Stacks.Curves

end
