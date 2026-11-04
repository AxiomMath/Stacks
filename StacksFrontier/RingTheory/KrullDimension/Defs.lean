module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Height

import StacksCore.Tactic.StacksAttribute

/-!
# Krull dimension and height of a ring
-/

@[expose] public section

-- The former @[stacks 00KE] declaration is now the Mathlib definition.
add_to_stacks 00KE "the Krull dimension of a ring" ringKrullDim
add_to_sga "2 XI 3.10" ringKrullDim
add_to_ega "0 16.3.1" ringKrullDim
add_to_ega "II 7.1.5" ringKrullDim
add_to_ega "II 8.10.3" ringKrullDim
add_to_ega "IV 10.5.1" ringKrullDim
add_to_ega "IV 17.15.8" ringKrullDim
add_to_ega "0 16.1.1" "definition of dim A" ringKrullDim
-- The former @[stacks 00KF] declaration is now the Mathlib theorem.
add_to_stacks 00KF IsLocalization.AtPrime.ringKrullDim_eq_height

/-- The Krull dimension of `R` equals the supremum of the heights of its prime ideals. -/
@[stacks 00KG]
theorem ringKrullDim_eq_iSup_height (R : Type*) [CommRing R] :
    ringKrullDim R = ⨆ (I : PrimeSpectrum R), (I.asIdeal.height : WithBot ℕ∞) := by
  simp_rw [PrimeSpectrum.height_eq_orderHeight]
  exact Order.krullDim_eq_iSup_height

/-- The Krull dimension of `R` equals the supremum of the heights of its maximal ideals. -/
@[stacks 00KG]
theorem ringKrullDim_eq_iSup_height_maximal (R : Type*) [CommRing R] :
    ringKrullDim R =
      ⨆ (I : {I : PrimeSpectrum R // I.asIdeal.IsMaximal}),
        (I.val.asIdeal.height : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_iSup_height]
  refine le_antisymm (iSup_le fun I ↦ ?_)
    (iSup_le fun ⟨I, _⟩ ↦ le_iSup (fun K : PrimeSpectrum R ↦
      (K.asIdeal.height : WithBot ℕ∞)) I)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I.asIdeal I.isPrime.ne_top
  exact le_trans (by exact_mod_cast Ideal.height_mono hIm)
    (le_iSup (fun K : {K : PrimeSpectrum R // K.asIdeal.IsMaximal} ↦
      (K.val.asIdeal.height : WithBot ℕ∞)) ⟨⟨m, hm.isPrime⟩, hm⟩)

-- @[stacks 00KH] is already attached to Mathlib's equivalence.

-- The former @[stacks_fixed 0GIE] structure is represented by Mathlib's series.
add_to_stacks 0GIE "chains of prime ideals" LTSeries.mk
add_to_stacks 0GIE "the length of a chain of prime ideals" RelSeries.length

end
