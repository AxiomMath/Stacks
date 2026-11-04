module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Finite extensions without intermediate fields

A finite field extension `L / K` with no intermediate field other than `K` and `L` is either
separable, or purely inseparable of degree `p`, the characteristic of `K`. This is the dichotomy
on which the base case of the source's proof of [Stacks, Tag 0BGN] rests: for a minimal
extension of fraction fields either the separable going-up of [Stacks, Tag 0AXL] or the
degree-`p` inseparable case of [Stacks, Tag 0B4U] applies.

## Main results

* `IntermediateField.isSeparable_or_finrank_eq_ringChar_of_forall_eq_bot_or_eq_top`: the
  dichotomy.

## Implementation notes

The separable closure of `K` in `L` is an intermediate field, so it is `K` or `L`. In the second
case `L / K` is separable. In the first `L / K` is purely inseparable, of degree `q ^ n` for the
exponential characteristic `q`; an element `x ∉ K` generates `L`, its minimal polynomial is
`X ^ q ^ n - y`, so `x ^ q` has degree at most `q ^ (n - 1)` and cannot generate `L`. Hence
`x ^ q ∈ K`, the degree is at most `q`, and so it is `q`, which is then a prime and the
characteristic.

## References

* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
-/

@[expose] public section

open Module Polynomial IntermediateField

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **A finite extension with no proper intermediate field is separable, or purely inseparable of
degree the characteristic.** If every intermediate field of the finite extension `L / K` is `K`
or `L`, then either `L / K` is separable, or the characteristic `p` of `K` is a prime, `L / K`
is purely inseparable, and `[L : K] = p`. -/
theorem isSeparable_or_finrank_eq_ringChar_of_forall_eq_bot_or_eq_top [FiniteDimensional K L]
    (h : ∀ M : IntermediateField K L, M = ⊥ ∨ M = ⊤) :
    Algebra.IsSeparable K L ∨
      ((ringChar K).Prime ∧ IsPurelyInseparable K L ∧ finrank K L = ringChar K) := by
  rcases h (separableClosure K L) with hbot | htop
  · by_cases hsep : Algebra.IsSeparable K L
    · exact Or.inl hsep
    right
    have hpi : IsPurelyInseparable K L := separableClosure.eq_bot_iff.mp hbot
    obtain ⟨q, hq⟩ := ExpChar.exists K
    -- some element is not in `K`, and it generates `L`
    obtain ⟨x, hx⟩ : ∃ x : L, x ∉ (algebraMap K L).range := by
      by_contra hall
      push Not at hall
      exact hsep ⟨fun x => by
        obtain ⟨c, rfl⟩ := hall x
        exact isSeparable_algebraMap c⟩
    have hxint : IsIntegral K x := .of_finite K x
    -- an element outside `K` generates `L`, so its minimal polynomial has degree `[L : K]`
    have hgen : ∀ z : L, z ∉ (algebraMap K L).range → (minpoly K z).natDegree = finrank K L := by
      intro z hz
      have hztop : K⟮z⟯ = ⊤ := (h K⟮z⟯).resolve_left fun h' =>
        hz (IntermediateField.mem_bot.mp (adjoin_simple_eq_bot_iff.mp h'))
      rw [← IntermediateField.adjoin.finrank (.of_finite K z), hztop,
        IntermediateField.finrank_top']
    -- a root of `X ^ n - C c` has minimal polynomial of degree at most `n`
    have hroot_le : ∀ (z : L) (n : ℕ) (c : K), n ≠ 0 → aeval z (X ^ n - C c) = 0 →
        (minpoly K z).natDegree ≤ n := by
      intro z n c hn hz
      have := natDegree_le_natDegree
        (minpoly.degree_le_of_ne_zero K z (monic_X_pow_sub_C c hn).ne_zero hz)
      rwa [natDegree_sub_C, natDegree_X_pow] at this
    have hdegx := hgen x hx
    obtain ⟨m, y, hmy⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C K q x
    have hdeg : (minpoly K x).natDegree = q ^ m := by
      rw [hmy, natDegree_sub_C, natDegree_X_pow]
    have hx2 : 2 ≤ (minpoly K x).natDegree := (minpoly.two_le_natDegree_iff hxint).mpr hx
    have hq2 : 2 ≤ q := by
      rcases hq with _ | ⟨hp⟩
      · rw [one_pow] at hdeg
        omega
      · exact hp.two_le
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hdeg
      omega
    -- `x ^ q` lies in `K`
    have hxq : x ^ q ∈ (algebraMap K L).range := by
      by_contra hxq
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      -- `x ^ q` is a root of `X ^ q ^ k - y`, a nonzero polynomial of degree `q ^ k`
      have hroot : aeval (x ^ q) (X ^ q ^ k - C y) = 0 := by
        have h0 : aeval x (minpoly K x) = 0 := minpoly.aeval K x
        rw [hmy] at h0
        simpa [← pow_mul, ← pow_succ'] using h0
      have hle := hroot_le _ _ y (pow_pos (by omega) k).ne' hroot
      have hlt : q ^ k < q ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
      have h1 : (minpoly K x).natDegree ≤ q ^ k := by rw [hdegx, ← hgen _ hxq]; exact hle
      rw [hdeg] at h1
      exact absurd h1 (not_le.mpr hlt)
    -- hence the degree is at most `q`
    obtain ⟨c, hc⟩ := hxq
    have hroot : aeval x (X ^ q - C c) = 0 := by
      simp [hc]
    have hle : finrank K L ≤ q := by
      rw [← hdegx]
      exact hroot_le x q c (by omega) hroot
    have hfin : finrank K L = q := by
      apply le_antisymm hle
      rw [← hdegx, hdeg]
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ m := Nat.pow_le_pow_right (by omega) (Nat.one_le_iff_ne_zero.mpr hm0)
    rcases hq with _ | ⟨hp⟩
    · omega
    · rw [ringChar.eq K q]
      exact ⟨hp, hpi, hfin⟩
  · exact Or.inl ((separableClosure.eq_top_iff K L).mp htop)

end IntermediateField
