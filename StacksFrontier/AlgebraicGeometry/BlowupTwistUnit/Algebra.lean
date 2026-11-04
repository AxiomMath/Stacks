module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Height

/-!
# A scalar that is a unit away from the closed point of a local ring of dimension two

Let `A` be a Noetherian local ring of Krull dimension at least two and let `t ∈ A` be a scalar
which lies in no prime ideal other than the maximal one. Then `t` is a unit.

This is the piece of commutative algebra behind the comparison `𝒪_X ⟶ b_*𝒪_{X'}(E)` of a blowup
in a closed point: the comparison is an isomorphism away from the point, so the scalar by which
it acts on the stalk at the point is a unit in every other localization, and the statement below
upgrades that to invertibility.

## The argument

If `t` were not a unit then `(t)` would be a proper ideal, so it would have a minimal prime `p`.
Krull's principal ideal theorem bounds the height of `p` by one
(`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`), while the hypothesis forces `p` to
be the maximal ideal, whose height is the Krull dimension
(`IsLocalRing.maximalIdeal_height_eq_ringKrullDim`). So the dimension would be at most one.

Nothing more than "dimension at least two" is used: no regularity, no normality, and no
assumption that `A` is a domain.

## Main results

* `Stacks.BlowupTwistUnit.isUnit_of_forall_isPrime_eq_maximalIdeal`: a scalar of a Noetherian
  local ring of dimension at least two lying in no prime but the maximal one is a unit.

## References

* [Stacks Project, Tag 00KE](https://stacks.math.columbia.edu/tag/00KE)
-/

@[expose] public section

universe u

namespace Stacks.BlowupTwistUnit

/-- **A scalar lying in no prime ideal but the maximal one is a unit**, in a Noetherian local
ring of Krull dimension at least two.

Were `t` a non-unit, the principal ideal `(t)` would be proper and would therefore admit a
minimal prime `p`, of height at most one by Krull's principal ideal theorem.  The hypothesis
identifies `p` with the maximal ideal, whose height is the Krull dimension of `A`; so the
dimension would be at most one. -/
theorem isUnit_of_forall_isPrime_eq_maximalIdeal {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (hdim : 2 ≤ ringKrullDim A) {t : A}
    (ht : ∀ p : Ideal A, p.IsPrime → t ∈ p → p = IsLocalRing.maximalIdeal A) : IsUnit t := by
  by_contra hu
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes
    (I := Ideal.span {t}) (mt Ideal.span_singleton_eq_top.mp hu)
  have : p.IsPrime := hp.1.1
  have hmem : t ∈ p := hp.1.2 (Ideal.mem_span_singleton_self t)
  have hheight : p.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {t}) p hp
  rw [ht p ‹p.IsPrime› hmem] at hheight
  have hle : ringKrullDim A ≤ (1 : WithBot ℕ∞) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast hheight
  exact absurd (hdim.trans hle) (by decide)

end Stacks.BlowupTwistUnit

end
