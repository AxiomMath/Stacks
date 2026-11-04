module

public import StacksFrontier.RingTheory.AdicCompletion.LiftToComplete
public import StacksFrontier.RingTheory.DiscreteValuationRing.EqualCharacteristicStructure

/-!
# Coefficient fields of Artinian local `ℚ`-algebras

An Artinian local ring `A` containing `ℚ` has a coefficient field: a ring map
`σ : κ(A) → A` from its residue field splitting the residue map. This is the Cohen structure
theorem (Tag 032A) in the form `Stacks.EppTheorem.exists_residue_comp_eq_id`, since an Artinian
local ring is complete for its nilpotent maximal ideal and its residue characteristic is zero.

## Main results

* `IsArtinianRing.exists_residue_comp_eq_id_of_algebraRat`: the coefficient field.
-/

@[expose] public section

open IsLocalRing

namespace IsArtinianRing

/-- **An Artinian local `ℚ`-algebra has a coefficient field**: the residue map `A → κ(A)` has a
ring-homomorphism section. -/
theorem exists_residue_comp_eq_id_of_algebraRat (A : Type*) [CommRing A] [IsArtinianRing A]
    [IsLocalRing A] [Algebra ℚ A] :
    ∃ σ : ResidueField A →+* A, (residue A).comp σ = RingHom.id (ResidueField A) := by
  have := IsAdicComplete.of_isNilpotent (maximalIdeal A)
    ((isArtinianRing_iff_isNilpotent_maximalIdeal A).mp ‹_›)
  let : Algebra ℚ (ResidueField A) := ((residue A).comp (algebraMap ℚ A)).toAlgebra
  have : CharZero (ResidueField A) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (ResidueField A)).injective
  refine Stacks.EppTheorem.exists_residue_comp_eq_id A ?_
  rw [ringChar.eq_zero, Nat.cast_zero]

end IsArtinianRing
