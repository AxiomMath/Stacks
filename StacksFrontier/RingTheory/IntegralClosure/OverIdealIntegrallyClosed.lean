module

public import StacksFrontier.RingTheory.Blowup.IntegrallyClosed
public import StacksFrontier.RingTheory.IntegralClosure.OverIdeal
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Blowup.IntegrallyClosedSupplement

/-!
# Integrality over an ideal: the absolute case and the degree-zero witness

This file complements `StacksFrontier/RingTheory/IntegralClosure/OverIdeal.lean`.

## Main results

* `Ideal.isIntegralOver_iff_isIntegralElemOverIdeal`: over the identity ring map,
  `RingHom.IsIntegralElemOverIdeal` is `Ideal.IsIntegralOver` of
  `StacksFrontier/RingTheory/Blowup/IntegrallyClosed.lean`, the spelling in which the affine blowup
  charts test integral closedness of an ideal.
* `isIntegralElem_of_isIntegralElemOverIdeal`: the forward implication of [Stacks, Tag 00H3] stated
  for `RingHom.IsIntegralElemOverIdeal`, which, unlike `IsIntegralOverIdeal`, does not ask for a
  positive degree.

## References

* [Stacks Project, Tag 00H2](https://stacks.math.columbia.edu/tag/00H2)
* [Stacks Project, Tag 00H3](https://stacks.math.columbia.edu/tag/00H3)
-/

@[expose] public section

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **Over the identity ring map, [Stacks, Tag 00H2] is `Ideal.IsIntegralOver`.** An element of
`R` is integral over `I ⊆ R` in the sense of this file exactly when it is integral over `I` in the
sense of `StacksFrontier/RingTheory/Blowup/IntegrallyClosed.lean`, where the blowup charts test
integral closedness of the powers of an ideal.

One direction assembles the monic witness `X ^ k + ∑_{j < k} C (c j) · X ^ j`, whose degree is `k`
because the sum has degree less than `k`, and reads its coefficients: `c j` below `k`, the leading
`1 ∈ I ^ 0` at `k`, and `0` above. The other reads the coefficients of a given witness off as the
coefficient family. A monic witness of degree zero is `1`, which vanishes at no element of a
nontrivial ring, so the positive degree `Ideal.IsIntegralOver` asks for costs nothing. -/
theorem Ideal.isIntegralOver_iff_isIntegralElemOverIdeal (I : Ideal R) (x : R) :
    I.IsIntegralOver x ↔ (RingHom.id R).IsIntegralElemOverIdeal I x := by
  constructor
  · rintro ⟨k, c, hk, hc, hrel⟩
    rcases subsingleton_or_nontrivial R with _ | _
    · exact ⟨X, monic_X, fun j => by
        rw [Subsingleton.elim ((X : R[X]).coeff j) 0]
        exact Submodule.zero_mem _, Subsingleton.elim _ _⟩
    have hqdeg : (∑ j ∈ Finset.range k, C (c j) * X ^ j : R[X]).degree < (k : WithBot ℕ) := by
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
        ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j hj => ?_)
      exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le j (c j))
        (by exact_mod_cast Finset.mem_range.mp hj)
    have hnd : (X ^ k + ∑ j ∈ Finset.range k, C (c j) * X ^ j : R[X]).natDegree = k := by
      rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
        Polynomial.natDegree_X_pow]
    refine ⟨_, Polynomial.monic_X_pow_add hqdeg, fun j => ?_, ?_⟩
    · rw [hnd]
      rcases lt_trichotomy j k with h | h | h
      · rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), zero_add,
          Polynomial.finsetSum_coeff]
        simpa [Polynomial.coeff_C_mul_X_pow, Finset.mem_range.mpr h] using hc j h
      · -- at the leading degree the ambient ideal is `I ^ 0 = ⊤`
        rw [h, Nat.sub_self, pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        exact Submodule.zero_mem _
    · simpa only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, RingHom.id_apply] using hrel
  · rintro ⟨p, hp, hcoeff, heval⟩
    rcases Nat.eq_zero_or_pos p.natDegree with h0 | hk
    · rw [hp.natDegree_eq_zero.mp h0, Polynomial.eval₂_one] at heval
      have := subsingleton_of_zero_eq_one heval.symm
      exact ⟨1, fun _ => 0, Nat.one_pos, fun j _ => Submodule.zero_mem _, Subsingleton.elim _ _⟩
    · refine ⟨p.natDegree, p.coeff, hk, fun j _ => hcoeff j, ?_⟩
      rw [monic_eval₂_expand (RingHom.id R) p hp x] at heval
      simpa only [RingHom.id_apply] using heval

/-- **[Stacks, Tag 00H3], the forward implication.** If `s : S` is integral over the ideal
`I ⊆ R` with respect to `φ : R →+* S`, then `C s · X ∈ S[X]` is integral over the Rees
subalgebra `reesAlgebra I`, viewed inside `S[X]` along the coefficientwise extension of `φ`.

A monic witness of degree zero is `1`, whose vanishing at `s` makes `s = 0`, and then `C s · X`
is zero and `X` is a witness; otherwise `forwardWitness` multiplies the `i`-th coefficient by
`X ^ (n - i)` to land in the Rees algebra. -/
@[stacks 00H3 "Forward implication only: integral over I implies C s * X integral over \
reesAlgebra I. The converse half of the equivalence is not formalized."]
theorem isIntegralElem_of_isIntegralElemOverIdeal (φ : R →+* S) (I : Ideal R) (s : S)
    (h : φ.IsIntegralElemOverIdeal I s) :
    (reesToPolyS φ I).IsIntegralElem (C s * X) := by
  obtain ⟨p, hp, hcoeff, heval⟩ := h
  have hc : ∀ i, i < p.natDegree → p.coeff i ∈ I ^ (p.natDegree - i) := fun i _ => hcoeff i
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hn
  · rw [hp.natDegree_eq_zero.mp h0, Polynomial.eval₂_one] at heval
    have hs : s = 0 := by rw [← mul_one s, heval, mul_zero]
    refine ⟨X, monic_X, ?_⟩
    rw [Polynomial.eval₂_X, hs, Polynomial.C_0, zero_mul]
  · refine ⟨forwardWitness I p hc, forwardWitness_monic I p hc hn, ?_⟩
    rw [forwardWitness_eval₂_factor φ I p s hp hc, heval, Polynomial.C_0, zero_mul]

end
