module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsDimensionBounds

/-!
# Condition (5) of Stacks 0EFL at `s = 1`, from condition (3) of Stacks 0EIF

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and let `M` be a finite `A`-module. Condition (5)
of Stacks 0EFL offers three alternatives at a prime `𝔭` lying off `V(I)`, off
`T = Stacks.Algebraization.associatedSubset I 𝔞`, having a specialization in `V(𝔞) ∩ V(I)` and
having `depth(M_𝔭) < s`: the support of `M_𝔭` has dimension less than `s + 2`, or
`δ(𝔭) > d + δmax - 1`, or `depth(M_𝔭) + dim((A/𝔭)_𝔮) > d + s + δmax - δmin - 2` along every
such specialization.

At `s = 1` the depth hypothesis says `depth(M_𝔭) = 0`, that is, `𝔭 ∈ Ass(M)`. The two
alternatives of condition (3) of Stacks 0EIF each settle one of the three:

* condition (3)(a) — `M` is `(S₁)` off `V(I)` — bounds the dimension of the support of `M_𝔭` by
  `0` at an associated prime, which is the first alternative;
* condition (3)(b) — the values of a dimension function on `V(𝔞)` differ by at most `2` — makes
  `d + 1 + δmax - δmin - 2 ≤ d + 1`, and condition (2) of Stacks 0EIF already gives
  `depth(M_𝔭) + dim((A/𝔭)_𝔮) > d + 1`, which is the third alternative.

Under condition (3)(b) the extreme values `δmax` and `δmin` that condition (5) is stated against
also *exist*: a dimension function whose values on `V(𝔞)` differ pairwise by at most `2` has a
bounded, hence extremal, image there.

## Main results

* `Stacks.Algebraization.eq_zero_of_enatToEInt_lt_one` — a depth whose image in `EInt` is less
  than `1` is zero.
* `Stacks.Algebraization.exists_isGreatest_isLeast_of_bddBelow_bddAbove` — a two-sidedly bounded
  nonempty set of integers has a greatest and a least element.
* `Stacks.Algebraization.exists_isGreatest_isLeast_of_le_add_two` — under condition (3)(b) the
  extreme values of `δ` on `V(𝔞) ∩ V(I)` exist and differ by at most `2`.
* `Stacks.Algebraization.supplementaryBound_of_supportDim` — **condition (5) of Stacks 0EFL at
  `s = 1` from condition (3)(a)**.
* `Stacks.Algebraization.supplementaryBound_of_le_add_two` — **condition (5) of Stacks 0EFL at
  `s = 1` from condition (3)(b)**, together with condition (2) of Stacks 0EIF.

## Implementation notes

Condition (3)(a) of Stacks 0EIF is a condition on the stalks of the coherent module on
`U ∖ V(I)`; it enters here in its ring-theoretic form, as a bound on the dimension of the
support of `M_𝔭` at the associated primes of `M` off `V(I)`. Serre's condition `(S₁)` says
`min(1, dim Supp M_𝔭) ≤ depth M_𝔭`, which at an associated prime — where the depth is zero —
forces `dim Supp M_𝔭 ≤ 0`; so the hypothesis below is what `(S₁)` gives, with room to spare.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A]

/-- The value of `Stacks.Algebraization.krullDimToEInt` at zero. -/
private theorem krullDimToEInt_zero :
    krullDimToEInt (0 : WithBot ℕ∞) = ((0 : ℤ) : EInt) := rfl

/-- An extended natural number whose image in `EInt` is less than `1` is zero. This is how the
depth hypothesis of condition (5) of Stacks 0EFL reads at `s = 1`. -/
theorem eq_zero_of_enatToEInt_lt_one {x : ℕ∞} (h : enatToEInt x < ((1 : ℤ) : EInt)) :
    x = 0 := by
  cases x using ENat.recTopCoe with
  | top => exact absurd h (not_lt_of_ge le_top)
  | coe n =>
    have hn : (n : ℤ) < 1 := WithBotTop.coe_lt_coe.1 h
    have hz : n = 0 := by omega
    simp [hz]

/-- **A two-sidedly bounded nonempty set of integers has a greatest and a least element.** This
is all that stands between a bound on a dimension function and the data `δmax`, `δmin` against
which condition (5) of Stacks 0EFL is stated; the two consumers differ only in where the bound
comes from — `Stacks.Algebraization.exists_isGreatest_isLeast_of_le_add_two` reads it off
condition (3)(b) of Stacks 0EIF, and
`Stacks.Algebraization.exists_isGreatest_isLeast_dualizingDimension` reads it off the injective
amplitude of a dualizing complex. -/
theorem exists_isGreatest_isLeast_of_bddBelow_bddAbove {S : Set ℤ} (hne : S.Nonempty)
    {lo hi : ℤ} (hlo : ∀ y ∈ S, lo ≤ y) (hhi : ∀ y ∈ S, y ≤ hi) :
    ∃ smax smin : ℤ, IsGreatest S smax ∧ IsLeast S smin := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨smax, hmaxmem, hmaxub⟩ := Int.exists_greatest_of_bdd ⟨hi, hhi⟩ ⟨y₀, hy₀⟩
  obtain ⟨smin, hminmem, hminlb⟩ := Int.exists_least_of_bdd ⟨lo, hlo⟩ ⟨y₀, hy₀⟩
  exact ⟨smax, smin, ⟨hmaxmem, hmaxub⟩, ⟨hminmem, hminlb⟩⟩

/-- **The extreme values of a dimension function on a small closed set.** If the values of `δ` on
`V(𝔞)` differ pairwise by at most `2` and `V(𝔞) ∩ V(I)` is nonempty, then `δ` attains a greatest
and a least value on `V(𝔞) ∩ V(I)`, and the two differ by at most `2`.

These are the data `δmax` and `δmin` against which condition (5) of Stacks 0EFL is stated. -/
theorem exists_isGreatest_isLeast_of_le_add_two (I a : Ideal A) (δ : PrimeSpectrum A → ℤ)
    (hδ : ∀ x z : PrimeSpectrum A, a ≤ x.asIdeal → a ≤ z.asIdeal → δ x ≤ δ z + 2)
    (hne : (PrimeSpectrum.zeroLocus (a : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A)).Nonempty) :
    ∃ δmax δmin : ℤ,
      IsGreatest (δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))) δmax ∧
      IsLeast (δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))) δmin ∧
      δmax ≤ δmin + 2 := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hmem : ∀ x ∈ PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A),
      a ≤ x.asIdeal := fun x hx => (PrimeSpectrum.mem_zeroLocus _ _).1 hx.1
  set S := δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
  have hupper : ∀ y ∈ S, y ≤ δ z₀ + 2 := by
    rintro y ⟨x, hx, rfl⟩
    exact hδ x z₀ (hmem x hx) (hmem z₀ hz₀)
  have hlower : ∀ y ∈ S, δ z₀ - 2 ≤ y := by
    rintro y ⟨x, hx, rfl⟩
    linarith [hδ z₀ x (hmem z₀ hz₀) (hmem x hx)]
  obtain ⟨δmax, δmin, hmax, hmin⟩ :=
    exists_isGreatest_isLeast_of_bddBelow_bddAbove (S := S) ⟨δ z₀, z₀, hz₀, rfl⟩ hlower hupper
  obtain ⟨xM, hxM, rfl⟩ := hmax.1
  obtain ⟨xm, hxm, rfl⟩ := hmin.1
  exact ⟨δ xM, δ xm, hmax, hmin, hδ xM xm (hmem xM hxM) (hmem xm hxm)⟩

/-- **Condition (5) of Stacks 0EFL at `s = 1`, from condition (3)(a) of Stacks 0EIF.** If the
support of `M_𝔭` has dimension at most `0` at every associated prime `𝔭` of `M` which does not
contain `I` — which is what Serre's condition `(S₁)` off `V(I)` gives — then the first
alternative of condition (5) holds at every prime off `V(I)` and off `T` at which the depth is
less than `1`. -/
theorem supplementaryBound_of_supportDim [IsNoetherianRing A]
    (I a : Ideal A) (d : ℤ) (δ : PrimeSpectrum A → ℤ) (δmax δmin : ℤ)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hS : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M → ¬ I ≤ p.asIdeal →
      Module.supportDim (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) ≤ (0 : WithBot ℕ∞))
    (p : PrimeSpectrum A)
    (hpI : p ∉ PrimeSpectrum.zeroLocus (I : Set A))
    (_hpT : p ∉ associatedSubset I a)
    (_hne : ((PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
      PrimeSpectrum.zeroLocus (a : Set A)) ∩
      PrimeSpectrum.zeroLocus (I : Set A)).Nonempty)
    (hdep : enatToEInt
      (Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M)) < ((1 : ℤ) : EInt)) :
    (krullDimToEInt (Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M)) < ((1 + 2 : ℤ) : EInt) ∨
      (d + δmax - 1 < δ p) ∨
      (∀ q : PrimeSpectrum A,
        q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
          PrimeSpectrum.zeroLocus (a : Set A)) ∩
          PrimeSpectrum.zeroLocus (I : Set A) →
        enatToEInt
            (Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl M)) +
            krullDimToEInt
              (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
                p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) >
          ((d + 1 + δmax - δmin - 2 : ℤ) : EInt))) := by
  refine Or.inl ?_
  have hass : p.asIdeal ∈ associatedPrimes A M :=
    (Module.depth_localized_eq_zero_iff (M := M) p).1 (eq_zero_of_enatToEInt_lt_one hdep)
  have hpInot : ¬ I ≤ p.asIdeal := fun h => hpI ((PrimeSpectrum.mem_zeroLocus _ _).2 h)
  refine lt_of_le_of_lt (krullDimToEInt_mono (hS p hass hpInot)) ?_
  rw [krullDimToEInt_zero]
  exact WithBotTop.coe_lt_coe.2 (by omega)

/-- **Condition (5) of Stacks 0EFL at `s = 1`, from condition (3)(b) of Stacks 0EIF.** If the
extreme values of `δ` on `V(𝔞) ∩ V(I)` differ by at most `2`, then the bound
`depth(M_𝔭) + dim((A/𝔭)_𝔮) > d + 1` of condition (2) of Stacks 0EIF — which is condition (4) of
Stacks 0EFL at `s = 1` — already gives the third alternative of condition (5). -/
theorem supplementaryBound_of_le_add_two [IsNoetherianRing A]
    (I a : Ideal A) (d : ℤ) (δ : PrimeSpectrum A → ℤ) (δmax δmin : ℤ)
    (hδ : δmax ≤ δmin + 2)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hbound : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M →
      ¬ I ≤ p.asIdeal →
      (∃ y : PrimeSpectrum A, p.asIdeal ≤ y.asIdeal ∧ I ≤ y.asIdeal ∧ ¬ a ≤ y.asIdeal) →
      ∀ z : PrimeSpectrum A, p.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
        ((d + 1 : ℤ) : EInt) < krullDimToEInt (closureLocalDimension A p z))
    (p : PrimeSpectrum A)
    (hpI : p ∉ PrimeSpectrum.zeroLocus (I : Set A))
    (hpT : p ∉ associatedSubset I a)
    (_hne : ((PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
      PrimeSpectrum.zeroLocus (a : Set A)) ∩
      PrimeSpectrum.zeroLocus (I : Set A)).Nonempty)
    (hdep : enatToEInt
      (Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M)) < ((1 : ℤ) : EInt)) :
    (krullDimToEInt (Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M)) < ((1 + 2 : ℤ) : EInt) ∨
      (d + δmax - 1 < δ p) ∨
      (∀ q : PrimeSpectrum A,
        q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
          PrimeSpectrum.zeroLocus (a : Set A)) ∩
          PrimeSpectrum.zeroLocus (I : Set A) →
        enatToEInt
            (Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl M)) +
            krullDimToEInt
              (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
                p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) >
          ((d + 1 + δmax - δmin - 2 : ℤ) : EInt))) := by
  refine Or.inr (Or.inr fun q hq => ?_)
  have hstrong :=
    (depthOrDimensionBound_of_closureLocalDimension I a d (M := M) hbound p hpI hpT).resolve_left
      (not_le_of_gt hdep) q hq
  exact lt_of_le_of_lt (WithBotTop.coe_le_coe.2 (by omega)) hstrong

end Stacks.Algebraization

end
