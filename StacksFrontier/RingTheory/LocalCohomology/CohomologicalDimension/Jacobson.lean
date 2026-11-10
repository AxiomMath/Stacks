module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Jacobson.Radical
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.F6Sweep.LocalCohomologySupportSurjectivity
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing.MaximalIdeal

/-!
# Cohomological dimension drops to a smaller ideal inside the Jacobson radical

Let `A` be a Noetherian ring of dimension `d` and let `I ⊆ I' ⊆ A` be ideals with `I'` contained
in the Jacobson radical of `A`. If the cohomological dimension of `I'` is less than `d`, then so
is that of `I`.

## Main results

* `Stacks.LocalCohomology.cohomologicalDimension_lt_of_le_of_le_jacobson` — the strict
  cohomological-dimension bound passes to the smaller ideal.

## References

* [Stacks Project, Tag 0EB1](https://stacks.math.columbia.edu/tag/0EB1)
* [Stacks Project, Tag 0DWV](https://stacks.math.columbia.edu/tag/0DWV)
* [Stacks Project, Tag 0DX8](https://stacks.math.columbia.edu/tag/0DX8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- Let `A` be a Noetherian ring of dimension `d` and let `I ≤ I'` be ideals of `A` with `I'`
inside the Jacobson radical. If the cohomological dimension of `I'` is less than `d`, then the
cohomological dimension of `I` is less than `d` as well. -/
@[stacks 0EB1]
theorem cohomologicalDimension_lt_of_le_of_le_jacobson
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞))
    (I I' : Ideal A) (hII' : I ≤ I') (hI' : I' ≤ Ring.jacobson A)
    (hcd : cohomologicalDimension A I' (Ideal.fg_of_isNoetherianRing I') < (d : ℤ)) :
    cohomologicalDimension A I (Ideal.fg_of_isNoetherianRing I) < (d : ℤ) := by
  classical
  have hdim_ne_bot : ringKrullDim A ≠ ⊥ := by simp [hd]
  have hdim_ne_top : ringKrullDim A ≠ ⊤ := by
    rw [hd]
    change ((d : ℕ∞) : WithBot ℕ∞) ≠ ⊤
    intro h
    exact ENat.natCast_ne_top d (by injection h)
  have : FiniteRingKrullDim A :=
    finiteRingKrullDim_iff_ne_bot_and_top.2 ⟨hdim_ne_bot, hdim_ne_top⟩
  have hzero : ∀ i : ℤ, (d : ℤ) ≤ i →
      IsZero (localCohomologyModule A I (Ideal.fg_of_isNoetherianRing I)
        (ModuleCat.of A A) i) := by
    intro i hi
    have hI'zero : IsZero (localCohomologyModule A I' (Ideal.fg_of_isNoetherianRing I')
        (ModuleCat.of A A) i) :=
      (isLocalCohomologyBound_cohomologicalDimension A I'
        (Ideal.fg_of_isNoetherianRing I')).2 i (lt_of_lt_of_le hcd hi)
    have hvan : ∀ (p : Ideal A) [p.IsPrime], I ≤ p → ¬ I' ≤ p →
        IsZero (localCohomologyModule (Localization.AtPrime p)
          (p.map (algebraMap A (Localization.AtPrime p)))
          ((Ideal.fg_of_isNoetherianRing p).map (algebraMap A (Localization.AtPrime p)))
          (ModuleCat.of (Localization.AtPrime p)
            (LocalizedModule p.primeCompl (ModuleCat.of A A))) i) := by
      intro p hp _hIp hI'p
      have hpmax : ¬ p.IsMaximal := fun _ ↦ hI'p (hI'.trans (Ring.jacobson_le_of_isMaximal p))
      obtain ⟨q, hqmax, hpq⟩ := p.exists_le_maximal hp.ne_top
      have hpq' : p < q := hpq.lt_of_ne (by rintro rfl; exact hpmax hqmax)
      have : q.IsPrime := hqmax.isPrime
      have hpheightlt : p.height < q.height :=
        Ideal.height_strict_mono_of_isPrime_of_isPrime hpq'
      have hqdim : (q.height : WithBot ℕ∞) ≤ ringKrullDim A :=
        Ideal.height_le_ringKrullDim_of_isPrime
      have hpd : p.height < (d : ℕ∞) := by
        rw [hd] at hqdim
        have : (p.height : WithBot ℕ∞) < ((d : ℕ∞) : WithBot ℕ∞) :=
          (WithBot.coe_lt_coe.mpr hpheightlt).trans_le hqdim
        exact_mod_cast this
      obtain ⟨m, hm⟩ : ∃ m : ℕ, p.height = (m : ℕ∞) :=
        ⟨p.height.toNat, (ENat.natCast_toNat (ne_top_of_lt hpd)).symm⟩
      have hmd : m < d := by rw [hm] at hpd; exact_mod_cast hpd
      have hdimle : ringKrullDim (Localization.AtPrime p) ≤ (m : WithBot ℕ∞) := by
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hm]
        exact le_of_eq rfl
      have hzl : PrimeSpectrum.zeroLocus
            ((p.map (algebraMap A (Localization.AtPrime p)) :
              Ideal (Localization.AtPrime p)) : Set (Localization.AtPrime p)) =
          PrimeSpectrum.zeroLocus
            ((maximalIdeal (Localization.AtPrime p) :
              Ideal (Localization.AtPrime p)) : Set (Localization.AtPrime p)) := by
        rw [Localization.AtPrime.map_eq_maximalIdeal]
      exact isZero_localCohomologyModule_of_zeroLocus_eq_maximalIdeal
        (Localization.AtPrime p) _ _ hzl hdimle _ i (by omega)
    have hsurj := localCohomologyModuleMapOfLE_surjective A I I'
      (Ideal.fg_of_isNoetherianRing I) (Ideal.fg_of_isNoetherianRing I') hII'
      (ModuleCat.of A A) i (by omega) hvan
    exact ModuleCat.isZero_iff_subsingleton.mpr <|
      @Function.Surjective.subsingleton _ _ _ (ModuleCat.isZero_iff_subsingleton.mp hI'zero) hsurj
  have hbound : IsLocalCohomologyBound A I (Ideal.fg_of_isNoetherianRing I) ((d : ℤ) - 1) :=
    ⟨by omega, fun i hi => hzero i (by omega)⟩
  have hle := cohomologicalDimension_le A I (Ideal.fg_of_isNoetherianRing I) ((d : ℤ) - 1) hbound
  omega

end Stacks.LocalCohomology

end
