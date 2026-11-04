module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EqualCharacteristicStructure
public import StacksFrontier.RingTheory.PowerSeries.PSpanned

/-!
# Condition (b) of Tag 09F9's third paragraph, over a complete ring with perfect residue field

The third paragraph of [Stacks: Tag 09F9](https://stacks.math.columbia.edu/tag/09F9) descends a
weak solution from the completion, and to do so it needs the finite extension upstairs to be

> a compositum of a separable extension and an extension obtained by adjoining a `p`-power root
> of `π`.

That is condition **(b)**. This file discharges it from perfectness of the residue field, which is
the hypothesis the complete case of Epp's theorem already carries — so nothing upstream has to be
strengthened to supply it. Precisely, for `A` a **complete** discrete valuation ring with perfect
residue field of characteristic `p`, uniformizer `π`, and fraction field `K`, every finite
extension `M / K` contains a `p ^ n`-th root `ρ` of `π` with `M / K⟮ρ⟯` separable, and
`minpoly K ρ = X ^ p ^ n - C π`.

## The shape of the statement, and why it is this one

`Stacks.EppTheorem.exists_pow_eq_and_isSeparable_adjoin` names `ρ` rather than the intermediate
field and asserts `Algebra.IsSeparable ↥K⟮ρ⟯ M`. This is the form step 3 consumes, and it is
**not** the external-compositum form, which asks for
`M · K(π^{1/p^n}) / K(π^{1/p^n})` separable — a statement about an *external* compositum, in which
`K(π^{1/p^n})` need not sit inside `M`. Step 3 needs `F` inside `M`, because it feeds `M` to Tag
09EJ as a finite *separable* extension of `F = Frac((A_n)^∧)`; the compositum form does not
provide that. The consumable form is what is proved here.

The `minpoly` conjunct is load-bearing rather than decorative: it is what identifies `K⟮ρ⟯` with
`K^ ⊗_K K_n` for `K_n = Stacks.KummerExtension.K1 K π (p ^ n)`, both sides becoming `K[T]/(T ^ p ^
n
  - π)`.
Degree alone would not do it — it gives `[K⟮ρ⟯ : K] = p ^ n` but not that the generator satisfies
*that* polynomial.

## Where each hypothesis is spent

* **`PerfectField (ResidueField A)`** — only in `PowerSeries.isPSpannedBy_X`, via the `p`-th roots
  of the coefficients.
* **`IsAdicComplete`** — only in the equal-characteristic structure theorem
  `Stacks.EppTheorem.exists_powerSeriesRingEquiv_of_irreducible`, which is what turns `A` into
  `κ_A⟦X⟧`. The conclusion is **false** without completeness, so this statement must not be
  weakened to a general discrete valuation ring.
* **`Irreducible π`** — twice: to have `X` land on `π` under the structure theorem, and to know
  `π` is not a `p`-th power in `K` (a `p`-th root would be integral over `A`, hence in `A` since a
  discrete valuation ring is integrally closed, hence a unit, making `π` one).

Residue characteristic zero and mixed characteristic need no work: there `K` has characteristic
zero, every finite extension is separable, and `n = 0` with `ρ = π` serves.

## Main results

* `Stacks.EppTheorem.isPSpannedBy_of_isAdicComplete`: the equal-characteristic input, `IsPSpannedBy
  p π`.
* `Stacks.EppTheorem.exists_pow_eq_and_isSeparable_adjoin`: condition (b).
-/

@[expose] public section

open IsLocalRing Polynomial

namespace Stacks.EppTheorem

/-- **A complete equal-characteristic discrete valuation ring with perfect residue field is
`p`-spanned by any uniformizer.**

The structure theorem writes `A` as `κ_A⟦X⟧` with `X ↦ π`, and `PowerSeries.isPSpannedBy_X`
settles it there. The hypothesis `(p : A) = 0` is equal characteristic: it is what distinguishes
`𝔽_p⟦t⟧` from `ℤ_p`, and the conclusion fails for the latter. -/
theorem isPSpannedBy_of_isAdicComplete (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
    [PerfectField (ResidueField A)] (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField A) p]
    (hpA : (p : A) = 0) {π : A} (hπ : Irreducible π) :
    IsPSpannedBy p π := by
  have hringChar : ringChar (ResidueField A) = p := ringChar.eq (ResidueField A) p
  have hchar : ((ringChar (ResidueField A) : ℕ) : A) = 0 := by rw [hringChar]; exact hpA
  obtain ⟨e, heX, -⟩ := exists_powerSeriesRingEquiv_of_irreducible A hchar hπ
  have hX := (PowerSeries.isPSpannedBy_X (κ := ResidueField A) p).map_ringEquiv e
  rwa [heX] at hX

/-- **Condition (b) of Tag 09F9's third paragraph.**

Let `A` be a complete discrete valuation ring with perfect residue field of characteristic `p`,
let `π` be a uniformizer, let `K = Frac A`, and let `M / K` be finite. Then there are `n` and
`ρ ∈ M` with

* `ρ ^ p ^ n = π`,
* `minpoly K ρ = X ^ p ^ n - C π`, so `K⟮ρ⟯` is `K(π^{1/p^n})` and `[K⟮ρ⟯ : K] = p ^ n`, and
* `M / K⟮ρ⟯` separable.

In mixed characteristic and in residue characteristic zero this holds with `n = 0` and `ρ = π`,
since `K` then has characteristic zero. -/
theorem exists_pow_eq_and_isSeparable_adjoin {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
    [PerfectField (ResidueField A)] {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {M : Type*} [Field M] [Algebra K M] [Module.Finite K M]
    (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField A) p] (π : A) (hπ : Irreducible π) :
    ∃ (n : ℕ) (ρ : M), ρ ^ p ^ n = algebraMap K M (algebraMap A K π) ∧
      minpoly K ρ = X ^ p ^ n - C (algebraMap A K π) ∧
      Algebra.IsSeparable (IntermediateField.adjoin K {ρ}) M := by
  have hinjAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hp2 : 2 ≤ p := hp.out.two_le
  -- `π` is not a `p`-th power in `K`: a `p`-th root is integral over `A`, hence lies in `A`
  -- because a discrete valuation ring is integrally closed, hence is a unit — which would make
  -- `π` a unit.
  have hnp : ∀ a : K, a ^ p ≠ algebraMap A K π := by
    intro a ha
    have hint : IsIntegral A a :=
      ⟨X ^ p - C π, Polynomial.monic_X_pow_sub_C π hp.out.ne_zero, by simp [ha]⟩
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have hbp : b ^ p = π := hinjAK (by rw [map_pow, hb, ha])
    have hu : IsUnit b := by
      rcases hπ.isUnit_or_isUnit (show π = b * b ^ (p - 1) by
        rw [← pow_succ', show p - 1 + 1 = p from by omega, hbp]) with h | h
      · exact h
      · exact (isUnit_pow_iff (by omega)).mp h
    exact hπ.not_isUnit (hbp ▸ hu.pow p)
  by_cases hpA : (p : A) = 0
  · -- Equal characteristic `p`: the structure theorem applies.
    have hCA : CharP A p := by
      have hCr := ringChar.charP A
      have hdvd : ringChar A ∣ p := ringChar.dvd hpA
      rcases hp.out.eq_one_or_self_of_dvd _ hdvd with h1 | hpe
      · exfalso
        have h1A : ((1 : ℕ) : A) = 0 :=
          (CharP.cast_eq_zero_iff A (ringChar A) 1).mpr (by rw [h1])
        simp at h1A
      · exact hpe ▸ hCr
    have hCK : CharP K p := charP_of_injective_algebraMap hinjAK p
    exact exists_pow_eq_minpoly_eq_and_isSeparable_adjoin p
      ((isPSpannedBy_of_isAdicComplete A p hpA hπ).algebraMap_fractionRing hp.out.ne_zero) hnp
  · -- Residue characteristic `p` but `(p : A) ≠ 0`: then `A`, hence `K`, has characteristic zero,
    -- and every finite extension of `K` is separable.
    have hCZA : CharZero A := by
      have hCr := ringChar.charP A
      rcases CharP.char_is_prime_or_zero A (ringChar A) with hprime | hzero
      · refine absurd ?_ hpA
        have hq0 : ((ringChar A : ℕ) : ResidueField A) = 0 := by
          rw [← map_natCast (IsLocalRing.residue A) (ringChar A),
            CharP.cast_eq_zero A (ringChar A), map_zero]
        have hpq : p ∣ ringChar A := (CharP.cast_eq_zero_iff (ResidueField A) p _).mp hq0
        have hpe : p = ringChar A :=
          (hprime.eq_one_or_self_of_dvd p hpq).resolve_left hp.out.ne_one
        rw [hpe]
        exact CharP.cast_eq_zero A _
      · have : CharP A 0 := hzero ▸ hCr
        exact CharP.charP_to_charZero A
    have hCZK : CharZero K := charZero_of_injective_algebraMap hinjAK
    refine ⟨0, algebraMap K M (algebraMap A K π), by simp, ?_, ?_⟩
    · simpa using
        minpoly.eq_X_sub_C_of_algebraMap_inj (algebraMap A K π) (algebraMap K M).injective
    · have hCZF : CharZero
          (IntermediateField.adjoin K ({algebraMap K M (algebraMap A K π)} : Set M)) :=
        charZero_of_injective_algebraMap (algebraMap K _).injective
      have hFin : Module.Finite
          (IntermediateField.adjoin K ({algebraMap K M (algebraMap A K π)} : Set M)) M :=
        Module.Finite.of_restrictScalars_finite K _ M
      infer_instance

end Stacks.EppTheorem
