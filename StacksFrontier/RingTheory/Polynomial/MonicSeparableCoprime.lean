module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# A monic separable polynomial over a domain avoiding the roots of a given polynomial

Let `A` be a domain with fraction field `K` and let `b ∈ K[X]` be nonzero. There is a monic
separable `h ∈ A[X]` of positive degree which is coprime to `b` in `K[X]`, i.e. has no root in
common with `b`.

* If `A` is infinite, `h = X - c` for any `c ∈ A` which is not a root of `b`; `b` has finitely
  many roots.
* If `A` is finite, it is a finite field with `q` elements and `K = A`. Then
  `h = X ^ (q ^ N) - X - 1` with `N = (deg b)!` works: its derivative is `-1`, so it is separable
  over `A` itself, and a root `β` of `b` generates an extension of `K` of degree `d ≤ deg b`, a
  finite field with `q ^ d` elements, so `β ^ (q ^ N) = β` as `d ∣ N` and `h(β) = -1`.

The zero locus `V(h) ⊆ 𝔸¹_A` is then finite étale over `Spec A` and misses the finite set
`V(b) ⊆ 𝔸¹_K` of the generic fibre. This chooses the divisor of a relative Noether normalization
along which the Gysin map of `R² g_!` is taken in the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Polynomial.isCoprime_X_pow_card_pow_sub_X_sub_one`: the finite field case.
* `Polynomial.monic_separable_X_pow_card_pow_sub_X_sub_one`: that polynomial is monic and
  separable.
* `Polynomial.exists_monic_separable_isCoprime_map`: the statement.
-/

@[expose] public section

open Polynomial IntermediateField

namespace Polynomial

/-- Over a finite field with `q` elements, `X ^ (q ^ (deg b)!) - X - 1` is coprime to every nonzero
`b`: each root of `b` lies in an extension of degree `d ≤ deg b`, a field with `q ^ d` elements,
and is fixed by `x ↦ x ^ (q ^ (deg b)!)`. -/
theorem isCoprime_X_pow_card_pow_sub_X_sub_one {K : Type*} [Field K] [Fintype K] {b : K[X]}
    (hb : b ≠ 0) :
    IsCoprime (X ^ (Fintype.card K ^ b.natDegree.factorial) - X - 1 : K[X]) b := by
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K)]
  intro a
  by_cases hab : aeval a b = 0
  · left
    have hint : IsIntegral K a := ⟨b * C b.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hb, by
      rw [← aeval_def, map_mul, hab, zero_mul]⟩
    have hfin : FiniteDimensional K K⟮a⟯ := IntermediateField.adjoin.finiteDimensional hint
    have : Finite K⟮a⟯ := Module.finite_of_finite K
    let : Fintype K⟮a⟯ := Fintype.ofFinite _
    set d := Module.finrank K K⟮a⟯
    have hd : d ∣ b.natDegree.factorial := by
      refine Nat.dvd_factorial Module.finrank_pos ?_
      rw [show d = (minpoly K a).natDegree from IntermediateField.adjoin.finrank hint]
      exact natDegree_le_of_dvd (minpoly.dvd K a hab) hb
    have hcard : Fintype.card K⟮a⟯ = Fintype.card K ^ d := Module.card_eq_pow_finrank
    obtain ⟨e, he⟩ := hd
    have hfix : (⟨a, IntermediateField.mem_adjoin_simple_self K a⟩ : K⟮a⟯) ^
        Fintype.card K ^ b.natDegree.factorial =
          ⟨a, IntermediateField.mem_adjoin_simple_self K a⟩ := by
      rw [he, pow_mul, ← hcard]
      exact FiniteField.pow_card_pow e _
    have hfix' : a ^ Fintype.card K ^ b.natDegree.factorial = a := by
      have := congrArg Subtype.val hfix
      simpa using this
    simp [hfix']
  · exact Or.inr hab

/-- Over a field with `q` elements, `X ^ (q ^ N) - X - 1` (for `N ≥ 1`) is monic, of positive
degree and separable, its derivative being `-1`. -/
theorem monic_separable_X_pow_card_pow_sub_X_sub_one (K : Type*) [Field K] [Fintype K] {N : ℕ}
    (hN : 1 ≤ N) :
    (X ^ (Fintype.card K ^ N) - X - 1 : K[X]).Monic ∧
      0 < (X ^ (Fintype.card K ^ N) - X - 1 : K[X]).natDegree ∧
      (X ^ (Fintype.card K ^ N) - X - 1 : K[X]).Separable := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have := hp
  have hq : 1 < Fintype.card K ^ N := Nat.one_lt_pow (by omega) Fintype.one_lt_card
  have hdeg : (X ^ (Fintype.card K ^ N) - X - 1 : K[X]).natDegree = Fintype.card K ^ N := by
    rw [sub_sub, natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp [hq]
  refine ⟨?_, by rw [hdeg]; omega, ?_⟩
  · rw [sub_sub]
    exact monic_X_pow_sub (by
      rw [show (X + 1 : K[X]) = X + C 1 by simp, degree_X_add_C]; exact_mod_cast hq)
  · rw [separable_def, derivative_sub, derivative_sub, derivative_X_pow, derivative_X,
      derivative_one, sub_zero]
    have hc : ((Fintype.card K ^ N : ℕ) : K) = 0 := by
      obtain ⟨n, hn, hcard⟩ := FiniteField.card K p
      rw [hcard, ← pow_mul, Nat.cast_pow, CharP.cast_eq_zero, zero_pow]
      exact Nat.mul_ne_zero (PNat.ne_zero n) (by omega)
    rw [show (C ((Fintype.card K ^ N : ℕ) : K) : K[X]) = 0 by rw [hc, map_zero], zero_mul,
      zero_sub]
    exact isCoprime_one_right.neg_right

/-- **A monic separable polynomial over a domain avoiding the roots of a nonzero polynomial over
its fraction field**: for `A` a domain with fraction field `K` and `b ∈ K[X]` nonzero, there is a
monic separable `h ∈ A[X]` of positive degree coprime to `b` in `K[X]`. For `A` infinite take
`h = X - c` with `b(c) ≠ 0`; for `A` finite, `A = K` is a finite field with `q` elements and
`h = X ^ (q ^ (deg b)!) - X - 1`. -/
theorem exists_monic_separable_isCoprime_map (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] {b : K[X]} (hb : b ≠ 0) :
    ∃ h : A[X], h.Monic ∧ 0 < h.natDegree ∧ h.Separable ∧
      IsCoprime (h.map (algebraMap A K)) b := by
  classical
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  by_cases hA : Finite A
  · -- `A` is a finite field and `A → K` is a bijection
    let : Field A := (Finite.isField_of_domain A).toField
    let : Fintype A := Fintype.ofFinite A
    have hsurj : Function.Surjective (algebraMap A K) :=
      (IsFractionRing.surjective_iff_isField (R := A) (K := K)).2 (Finite.isField_of_domain A)
    let e : A ≃ K := Equiv.ofBijective _ ⟨hinj, hsurj⟩
    let : Fintype K := Fintype.ofEquiv A e
    have hcard : Fintype.card K = Fintype.card A := Fintype.card_congr e.symm
    obtain ⟨hmon, hdeg, hsep⟩ :=
      monic_separable_X_pow_card_pow_sub_X_sub_one A (N := b.natDegree.factorial)
        (Nat.factorial_pos _)
    refine ⟨_, hmon, hdeg, hsep, ?_⟩
    have := isCoprime_X_pow_card_pow_sub_X_sub_one hb
    rw [hcard] at this
    simpa using this
  · -- `b` has finitely many roots, and `A` is infinite
    rw [not_finite_iff_infinite] at hA
    have hfin : {c : A | b.IsRoot (algebraMap A K c)}.Finite :=
      (b.roots.toFinset.finite_toSet.preimage hinj.injOn).subset fun c hc => by
        simpa [Multiset.mem_toFinset, mem_roots hb] using hc
    obtain ⟨c, hc⟩ := (Set.infinite_univ (α := A)).sdiff hfin |>.nonempty
    refine ⟨X - C c, monic_X_sub_C c, by rw [natDegree_X_sub_C]; exact one_pos,
      separable_X_sub_C, ?_⟩
    rw [Polynomial.map_sub, map_X, map_C, (irreducible_X_sub_C _).coprime_iff_not_dvd,
      dvd_iff_isRoot]
    exact hc.2

end Polynomial
