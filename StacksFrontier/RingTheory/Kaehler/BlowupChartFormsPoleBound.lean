module

public import Mathlib.SetTheory.Cardinal.Order
public import StacksFrontier.LinearAlgebra.ExteriorPower.DivisibleRetraction
public import StacksFrontier.RingTheory.Kaehler.BlowupChartDifferentials

/-!
# The pole bound for differential forms on an affine blowup chart

Let `R` be a commutative ring, let `A = MvPolynomial (σ ⊕ τ) R` be the coordinate ring of
`𝐀^σ × 𝐀^τ` over `R` with `τ` finite, and fix `i : τ`. The affine chart of the blowup of
`Spec(A)` along the coordinate subspace `y = 0` belonging to `i` is again a polynomial ring over
`R`, in the variables `x_k`, `y_i` and the ratios `t_j = y_j / y_i` for `j ≠ i`; the
corresponding `R`-algebra endomorphism of `A` is `Stacks.Kaehler.blowupChartHom`, and the
equation of the exceptional divisor on the chart is `y_i`.

This file assembles the two halves of the pole computation in the proof of
[Stacks, Tag 0G5G]: chart-locally `d t_j = (d y_j - t_j d y_i) / y_i` has a simple pole along
the exceptional divisor, and an `a`-fold wedge of coordinate differentials involves at most
`#τ - 1` of the `d t_j`. The conclusion is that the canonical map on `a`-forms

`⋀^a (A ⊗_A Ω[A⁄R]) ⟶ ⋀^a Ω[A⁄R]`

is injective and admits a retraction after multiplication by `y_i ^ (#τ - 1)`, **for every `a`,
with an exponent that does not depend on `a`**. That uniform exponent is exactly the twist by
`(n-1)E` in the statement of the source.

## Main results

* `Stacks.Kaehler.X_mem_nonZeroDivisors`: a variable is a non-zero-divisor of a polynomial ring.
* `Stacks.Kaehler.blowupChartDividedRetractionValue`: the chart retraction divided by `y_i`
  wherever that is possible.
* `Stacks.Kaehler.exists_comp_exteriorPower_map_blowupChartMapBaseChange`: **the pole bound**, in
  every degree `a`.
* `Stacks.Kaehler.injective_exteriorPower_map_blowupChartMapBaseChange`: the canonical map on
  `a`-forms is injective on the chart.

## Implementation notes

The two inputs are `Stacks.Kaehler.mapBaseChange_comp_retraction` (the chart-local retraction up
to `y_i`, that is, the displayed computation of the source) and
`exteriorPower.exists_comp_map_eq_pow_smul_of_forall` (the combinatorial bound on how many factors
of `y_i` an `a`-fold wedge can lose). The finite set of indices on which the retraction is *not*
divisible by `y_i` is the image of `τ \ {i}` under `Sum.inr`, of cardinality `#τ - 1`: these are
the basis vectors `d y_j` whose preimages `d t_j` have a pole.

On the remaining indices the division by `y_i` is carried out inside the proof rather than through
a named lemma, because the two `A`-module structures on `A ⊗_A Ω[A⁄R]` discussed in
`StacksFrontier.RingTheory.Kaehler.BlowupChartDifferentials` make a bare `•` ambiguous: a standalone
statement `… = y_i • (1 ⊗ d x_v)` would be read with the action through
`Stacks.Kaehler.blowupChartHom`, whereas the hypothesis of
`exteriorPower.exists_comp_map_eq_pow_smul_of_forall` is about the chart's own action, which is
the one pinned in the goal. There the identity is definitional up to `mul_one`, since the chart's
action multiplies the left factor of the tensor.

Indexing the induced basis of an exterior power needs a linear order on the index type `σ ⊕ τ`.
It does not appear in either statement, so one is chosen inside each proof from
`WellOrderingRel`, as Mathlib's `Module.Basis.exteriorPower` lemmas do; this also supplies the
decidability of membership in the finite set of pole indices, which is why neither statement
carries a `DecidableEq σ` hypothesis.

## References

* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
-/

@[expose] public noncomputable section

open scoped TensorProduct

open KaehlerDifferential MvPolynomial

namespace Stacks.Kaehler

variable (R : Type*) [CommRing R] (σ τ : Type*)

/-- A variable is a non-zero-divisor of a polynomial ring: multiplying by `X v` shifts the
exponent of `v` in every monomial, so it is injective on coefficients. -/
theorem X_mem_nonZeroDivisors (v : σ) :
    (X v : MvPolynomial σ R) ∈ nonZeroDivisors (MvPolynomial σ R) := by
  rw [mem_nonZeroDivisors_iff_left]
  intro f hf
  refine MvPolynomial.ext _ _ fun d => ?_
  have h := congrArg (coeff (Finsupp.single v 1 + d)) hf
  rw [coeff_X_mul, coeff_zero] at h
  rw [h, coeff_zero]

variable [DecidableEq τ] (i : τ)

/-- The chart retraction divided by `y_i` wherever that is possible: on the differential of a
ratio coordinate `y_j`, `j ≠ i`, it is the retraction itself, and on the differentials of the
ambient coordinates and of the pivot it is the corresponding vector `1 ⊗ d x_v` of the
base-changed basis, the retraction there being `y_i ⊗ d x_v`. -/
def blowupChartDividedRetractionValue : σ ⊕ τ → blowupChartTensor R σ τ i :=
  Sum.elim (fun k => blowupChartBaseChangeBasis R σ τ i (Sum.inl k))
    fun j => if j = i then blowupChartBaseChangeBasis R σ τ i (Sum.inr i)
      else blowupChartRetractionValue R σ τ i (Sum.inr j)

/-- On the differential of an ambient coordinate the divided retraction is the corresponding
vector `1 ⊗ d x_k` of the base-changed basis. -/
@[simp]
theorem blowupChartDividedRetractionValue_inl (k : σ) :
    blowupChartDividedRetractionValue R σ τ i (Sum.inl k) =
      blowupChartBaseChangeBasis R σ τ i (Sum.inl k) := rfl

/-- On the differential of the equation of the exceptional divisor the divided retraction is the
corresponding vector `1 ⊗ d y_i` of the base-changed basis. -/
@[simp]
theorem blowupChartDividedRetractionValue_inr_self :
    blowupChartDividedRetractionValue R σ τ i (Sum.inr i) =
      blowupChartBaseChangeBasis R σ τ i (Sum.inr i) := by
  simp [blowupChartDividedRetractionValue]

/-- On the differential of a ratio coordinate `y_j`, `j ≠ i`, the divided retraction is the
retraction itself: there is nothing to divide out, which is the pole. -/
@[simp]
theorem blowupChartDividedRetractionValue_inr_of_ne {j : τ} (hj : j ≠ i) :
    blowupChartDividedRetractionValue R σ τ i (Sum.inr j) =
      blowupChartRetractionValue R σ τ i (Sum.inr j) := by
  simp [blowupChartDividedRetractionValue, hj]

/-- **The pole bound of [Stacks, Tag 0G5G] on an affine blowup chart.** For every degree `a` the
canonical map `⋀^a (A ⊗_A Ω[A⁄R]) ⟶ ⋀^a Ω[A⁄R]` on `a`-forms of the chart admits a retraction
after multiplication by `y_i ^ (#τ - 1)`.

The exponent `#τ - 1` does not depend on `a`: a wedge of `a` coordinate differentials of the
chart involves at most `#τ - 1` of the ratio differentials `d t_j`, and only those contribute a
pole along the exceptional divisor `y_i = 0`. -/
theorem exists_comp_exteriorPower_map_blowupChartMapBaseChange [Fintype τ] (a : ℕ) :
    letI := blowupChartTensorModule R σ τ i
    ∃ ψ : (⋀[MvPolynomial (σ ⊕ τ) R]^a Ω[MvPolynomial (σ ⊕ τ) R⁄R]) →ₗ[MvPolynomial (σ ⊕ τ) R]
        (⋀[MvPolynomial (σ ⊕ τ) R]^a (blowupChartTensor R σ τ i)),
      exteriorPower.map a (blowupChartMapBaseChange R σ τ i) ∘ₗ ψ =
        ((X (Sum.inr i) : MvPolynomial (σ ⊕ τ) R) ^ (Fintype.card τ - 1)) • LinearMap.id := by
  let := blowupChartModule R σ τ i
  let := blowupChartTensorModule R σ τ i
  let : LinearOrder (σ ⊕ τ) := IsWellOrder.linearOrder WellOrderingRel
  refine exteriorPower.exists_comp_map_eq_pow_smul_of_forall
    (mvPolynomialBasis R (σ ⊕ τ)) (X_mem_nonZeroDivisors R (σ ⊕ τ) (Sum.inr i))
    (blowupChartMapBaseChange R σ τ i) (blowupChartDifferentialRetraction R σ τ i)
    (mapBaseChange_comp_retraction R σ τ i)
    ((Finset.univ.erase i).map ⟨Sum.inr, Sum.inr_injective⟩)
    (blowupChartDividedRetractionValue R σ τ i) (fun v hv => ?_) (fun v hv => ?_) ?_
  · obtain ⟨j, hjmem, hjv⟩ := Finset.mem_map.1 hv
    simp only [Function.Embedding.coeFn_mk] at hjv
    subst hjv
    rw [mvPolynomialBasis_apply, blowupChartDifferentialRetraction_apply_D_X,
      blowupChartDividedRetractionValue_inr_of_ne _ _ _ _ (Finset.mem_erase.1 hjmem).1]
  · obtain k | j := v
    · rw [mvPolynomialBasis_apply, blowupChartDividedRetractionValue_inl,
        blowupChartDifferentialRetraction_D_X_inl, blowupChartBaseChangeBasis_apply]
      show _ = (X (Sum.inr i) * (1 : MvPolynomial (σ ⊕ τ) R))
        ⊗ₜ[MvPolynomial (σ ⊕ τ) R] D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inl k))
      rw [mul_one]
    · have hj : j = i := by
        by_contra hj
        exact hv (Finset.mem_map_of_mem _ (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩))
      rw [hj, mvPolynomialBasis_apply, blowupChartDividedRetractionValue_inr_self,
        blowupChartDifferentialRetraction_D_X_inr_self, blowupChartBaseChangeBasis_apply]
      show _ = (X (Sum.inr i) * (1 : MvPolynomial (σ ⊕ τ) R))
        ⊗ₜ[MvPolynomial (σ ⊕ τ) R] D R (MvPolynomial (σ ⊕ τ) R) (X (Sum.inr i))
      rw [mul_one]
  · rw [Finset.card_map, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]

/-- **The canonical map on `a`-forms is injective on an affine blowup chart.** The chart
retraction composed with it is multiplication by `y_i`, so the `a`-th exterior power of the
composite is multiplication by `y_i ^ a`, which is injective because `y_i` is a non-zero-divisor
of the chart's polynomial ring. -/
theorem injective_exteriorPower_map_blowupChartMapBaseChange (a : ℕ) :
    letI := blowupChartTensorModule R σ τ i
    Function.Injective (exteriorPower.map a (blowupChartMapBaseChange R σ τ i)) := by
  let := blowupChartModule R σ τ i
  let := blowupChartTensorModule R σ τ i
  let : LinearOrder (σ ⊕ τ) := IsWellOrder.linearOrder WellOrderingRel
  have key : exteriorPower.map a (blowupChartDifferentialRetraction R σ τ i) ∘ₗ
      exteriorPower.map a (blowupChartMapBaseChange R σ τ i) =
        ((X (Sum.inr i) : MvPolynomial (σ ⊕ τ) R) ^ a) • LinearMap.id := by
    rw [← exteriorPower.map_comp, retraction_comp_mapBaseChange, exteriorPower.map_smul_id]
  intro z w hzw
  have hz := LinearMap.congr_fun key z
  have hw := LinearMap.congr_fun key w
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hz hw
  refine sub_eq_zero.1 (exteriorPower.eq_zero_of_smul_eq_zero
    (blowupChartBaseChangeBasis R σ τ i)
    (pow_mem (X_mem_nonZeroDivisors R (σ ⊕ τ) (Sum.inr i)) a) a _ ?_)
  rw [smul_sub, ← hz, ← hw, hzw, sub_self]

end Stacks.Kaehler

end
