module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.GrassmannianPoint
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialFreeTwist
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

/-!
# The rank bound `p ≤ N` for `Quot^P`

Let `n ≥ 0`, `r ≥ 1`, `P ∈ ℚ[t]`, `m = AlgebraicGeometry.ProjectiveQuot.regularityIndex n r P`,
`N = freeRank n r m` and `p = quotRank n r P = ⌊P(m)⌋₊`. If some scheme `T` with a point `t`
carries a member `K` of `Quot^P(T)`, then `p ≤ N`: on the fibre over `t` the map
`Γ(ℙⁿ_{κ(t)}, 𝒪^{⊕ r}(m)) ⟶ Γ(ℙⁿ_{κ(t)}, 𝒬_t(m))` is onto, the source has dimension
`r · (m + n choose n) = N` and the target has dimension `P(m)`. Hence when `p > N` the functor
`Quot^P` is empty on every nonempty scheme, and the bound `p ≤ N` used to build the classifying
morphism `T ⟶ G(N - p, N)` (`AlgebraicGeometry.ProjectiveQuot.toGrassmannian`) is automatic.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.nat_card_monomialIndex`: there are `(m + n choose n)`
  monomials of degree `m` in `n + 1` variables.
* `AlgebraicGeometry.ProjectiveQuot.freeRank_eq`: `freeRank n r m = r · (m + n choose n)`.
* `AlgebraicGeometry.ProjectiveQuot.quotRank_le_freeRank`: `p ≤ N` once `Quot^P(T)` has a member
  over a scheme with a point.
* `AlgebraicGeometry.ProjectiveQuot.hilbertFamilies_eq_empty_of_lt`: `Quot^P(T) = ∅` for every
  nonempty `T` when `N < p`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage
  (MonomialIndex MonomialIndex.natEquiv)

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable {n r : ℕ}

variable (n) in
/-- **There are `(m + n choose n)` monomials of degree `m` in `n + 1` variables.** -/
theorem nat_card_monomialIndex (m : ℕ) :
    Nat.card (MonomialIndex.{u} n (m : ℤ)) = (m + n).choose n := by
  classical
  have h : {e : ULift.{u} (Fin (n + 1)) →₀ ℕ | e.degree = m} =
      ↑((Finset.univ : Finset (ULift.{u} (Fin (n + 1)))).finsuppAntidiag m) := by
    ext e
    simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [Nat.card_congr (MonomialIndex.natEquiv n m), Nat.card_coe_set_eq, h, Set.ncard_coe_finset,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_ulift,
    Fintype.card_fin, show n + 1 + m - 1 = m + n by omega, Nat.choose_symm_add]

variable (n r) in
/-- **`N = r · (m + n choose n)`**: the rank of `π_*(𝒪^{⊕ r}(m))`. -/
theorem freeRank_eq (m : ℕ) : freeRank.{u} n r m = r * (m + n).choose n := by
  have : Finite (MonomialIndex.{u} n (m : ℤ)) :=
    Nat.finite_of_card_ne_zero (by
      rw [nat_card_monomialIndex]
      exact (Nat.choose_pos (Nat.le_add_left n m)).ne')
  rw [freeRank, Nat.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    nat_card_monomialIndex]

variable (hr : 1 ≤ r) {P : Polynomial ℚ}

include hr in
/-- **`p ≤ N`.** If `K ∈ Quot^P(T)` for a scheme `T` with a point `t`, then
`⌊P(m)⌋₊ ≤ freeRank n r m`: on the fibre over `t` the sections map
`Γ(ℙⁿ_{κ(t)}, 𝒪^{⊕ r}(m)) ⟶ Γ(ℙⁿ_{κ(t)}, 𝒬_t(m))` is onto, between spaces of dimensions
`r · (m + n choose n)` and `P(m)`. -/
theorem quotRank_le_freeRank {T : Scheme.{u}} {K : Subobject (freeModule n r T)}
    (hK : K ∈ hilbertFamilies n r P T) (t : T) :
    quotRank.{u} n r P ≤ freeRank.{u} n r (regularityIndex.{u} n r P) := by
  obtain ⟨hcoh, hval⟩ := hK.2 t
  let k := T.residueField t
  let q : freeModules k n r ⟶ fibre t (quotient K) :=
    baseChangeQuotientMap (T.fromSpecResidueField t) K
  have : Epi q := inferInstanceAs (Epi (baseChangeQuotientMap (T.fromSpecResidueField t) K))
  obtain ⟨-, -, hfin, hsurj, -⟩ := regularityIndex_spec n r P k (fibre t (quotient K)) q hval
  let m := regularityIndex.{u} n r P
  let f := projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)
  -- the dimension of the source
  have hsrc : Module.finrank k (cohomologyOverField k f
      (projectiveTwist n (freeModules k n r) (m : ℤ)) 0) = r * (m + n).choose n := by
    refine Nat.cast_injective (R := ℤ) ?_
    rw [← hilbertPolynomial_eq_finrank_cohomologyOverField_zero k n _ _ fun i hi =>
      (isZero_cohomologyOverField_iff_isZero_hgroup k f _ i).2
        (isZero_Hgroup_projectiveTwist_freeModules k n r m (Int.natCast_nonneg m) i hi)]
    exact_mod_cast hilbertPolynomial_freeModules k n r m
  have hfinite : Module.Finite k (cohomologyOverField k f
      (projectiveTwist n (freeModules k n r) (m : ℤ)) 0) :=
    Module.finite_of_finrank_pos (by
      rw [hsrc]
      exact Nat.mul_pos hr (Nat.choose_pos (Nat.le_add_left n m)))
  have : Module.Finite k (cohomologyOverField k f
      ((twistFunctorModules k n (m : ℤ)).obj (freeModules k n r)) 0) := hfinite
  have hle : Module.finrank k (cohomologyOverField k f
        ((twistFunctorModules k n (m : ℤ)).obj (fibre t (quotient K))) 0) ≤
      Module.finrank k (cohomologyOverField k f
        ((twistFunctorModules k n (m : ℤ)).obj (freeModules k n r)) 0) := by
    have h1 := LinearMap.finrank_range_le
      (cohomologyOverFieldMap k f ((twistFunctorModules k n (m : ℤ)).map q) 0).hom
    rwa [LinearMap.range_eq_top.2 hsurj, finrank_top] at h1
  have hP : P.eval ((m : ℕ) : ℚ) = (Module.finrank k (cohomologyOverField k f
      (projectiveTwist n (fibre t (quotient K)) (m : ℤ)) 0) : ℚ) := hfin.symm
  rw [quotRank, freeRank_eq, hP, Nat.floor_natCast, ← hsrc]
  exact hle

include hr in
/-- **`Quot^P` is empty over a nonempty scheme when `N < p`.** -/
theorem hilbertFamilies_eq_empty_of_lt
    (h : freeRank.{u} n r (regularityIndex.{u} n r P) < quotRank.{u} n r P)
    {T : Scheme.{u}} (t : T) : hilbertFamilies n r P T = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hK => (quotRank_le_freeRank hr hK t).not_gt h

end AlgebraicGeometry.ProjectiveQuot

end
