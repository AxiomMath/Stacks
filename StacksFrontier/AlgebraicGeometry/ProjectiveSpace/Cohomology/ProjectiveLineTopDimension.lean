module

public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveGenus

/-!
# `dim_k H¹(𝐏¹_k, 𝒪(-d)) = d - 1`

Let `k` be a field and `d : ℕ`. [Stacks, Tag 01XT] presents `H¹(𝐏¹_k, 𝒪(-d))` — the top-degree
cohomology of a twist on the projective line — as the free module on the Laurent monomials
`T₀^{e₀}T₁^{e₁}` of total degree `-d` with both exponents negative
(`Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoNegative` together with
`Stacks.ProjectiveSpace.Cohomology.negativeTwistPartBasis`). This file counts them: they match
the degree-`d - 2` monomials in two variables, of which there are `d - 1`.

The same bookkeeping on the projective plane is
`Stacks.ProjectiveSpace.Cohomology.nat_card_negativeLaurentMonomials_plane` and
`Stacks.ProjectiveSpace.Cohomology.finrank_twistCohomology_plane_top`, the arithmetic content of
the genus formula of [Stacks, Tag 0BYD]; the match with ordinary monomials,
`Stacks.ProjectiveSpace.Cohomology.negativeLaurentMonomialsEquivMonomials`, is already stated for
an arbitrary number of variables and is reused here.

## Main results

The elided prefix is `Stacks.ProjectiveSpace.Cohomology`.

* `nat_card_negativeLaurentMonomials_line`: there are `d - 1` Laurent monomials of degree `-d` in
  two variables with both exponents negative.
* `finrank_twistCohomology_line_top`: **`dim_k H¹(𝐏¹_k, 𝒪(-d)) = d - 1`**.
* `length_twistCohomology_line_top`: the same as a length, `𝓁_k H¹(𝐏¹_k, 𝒪(-d)) = d - 1`, which
  is the shape in which a length computation over a base ring with residue field `k` consumes it.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0BYD](https://stacks.math.columbia.edu/tag/0BYD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ProjectiveSpace.Cohomology

/-- **The degree-`-d` Laurent monomials of the line with both exponents negative number `d - 1`.**
They match the degree-`d - 2` monomials in two variables, of which there are
`(d - 1).choose (d - 2) = (d - 1).choose 1`; for `d ≤ 1` there are none. -/
theorem nat_card_negativeLaurentMonomials_line (d : ℕ) :
    Nat.card (negativeLaurentMonomials 1 (-(d : ℤ))) = d - 1 := by
  rcases le_or_gt 2 d with hd | hd
  · rw [Nat.card_eq_of_bijective _ (negativeLaurentMonomialsEquivMonomials 1 d hd).bijective,
      MvPolynomial.nat_card_degree_eq]
    rw [show Fintype.card (Fin 2) + (d - 2) - 1 = d - 1 by simp; omega,
      show d - 2 = (d - 1) - 1 by omega, Nat.choose_symm (by omega), Nat.choose_one_right]
  · have he : negativeLaurentMonomials 1 (-(d : ℤ)) = ∅ :=
      (negativeLaurentMonomials_eq_empty_iff 1 (-(d : ℤ))).2 (by push_cast; omega)
    have h1 : d - 1 = 0 := by omega
    rw [he, h1]
    simp

/-- **`dim_k H¹(𝐏¹_k, 𝒪(-d)) = d - 1`.** By [Stacks, Tag 01XT] that module is free on the
degree-`-d` Laurent monomials with both exponents negative, and `d = 0` is the degenerate case
where the cohomology vanishes. -/
theorem finrank_twistCohomology_line_top (k : Type u) [Field k] (d : ℕ) :
    Module.finrank k (twistCohomology k 1 (-(d : ℤ)) 1) = d - 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hz : IsZero (twistCohomology k 1 (0 : ℤ) 1) :=
      isZero_twistCohomology k 1 0 1 (by norm_num)
    have hs := ModuleCat.subsingleton_of_isZero hz
    rw [show -((0 : ℕ) : ℤ) = 0 by norm_num]
    exact Module.finrank_zero_of_subsingleton
  · have hneg : -(d : ℤ) < 0 := by omega
    rw [(twistCohomologyIsoNegative k 1 (-(d : ℤ)) hneg).toLinearEquiv.finrank_eq,
      Module.finrank_eq_nat_card_basis (negativeTwistPartBasis k 1 (-(d : ℤ))),
      nat_card_negativeLaurentMonomials_line]

/-- **`𝓁_k H¹(𝐏¹_k, 𝒪(-d)) = d - 1`.** The length of a finite-dimensional vector space is its
dimension, so this is `finrank_twistCohomology_line_top`. -/
theorem length_twistCohomology_line_top (k : Type u) [Field k] (d : ℕ) :
    Module.length k (twistCohomology k 1 (-(d : ℤ)) 1) = (d - 1 : ℕ) := by
  have : Module.Finite k (twistCohomology k 1 (-(d : ℤ)) 1) :=
    moduleFinite_twistCohomology k 1 (-(d : ℤ)) 1
  rw [Module.length_eq_finrank, finrank_twistCohomology_line_top]

end Stacks.ProjectiveSpace.Cohomology

end
