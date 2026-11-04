module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RamificationInertia.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.WeakSolutionObstruction

/-!
# The local fundamental identity for an extension of discrete valuation rings

For a module-finite flat extension of discrete valuation rings `A → B` with fraction fields
`K ⊆ L`, the degree `[L : K]` is the product of the ramification index and the residue degree.
Two consequences are recorded alongside it: the residue degree is one when the residue field
downstairs is algebraically closed, and in that case ramification index one forces the extension
of fraction fields to be trivial.

## Main results

* `Stacks.DiscreteValuationRing.Ramification.ramificationIdx_mul_inertiaDeg_eq_finrank`: the
  identity `[L : K] = e f`.
* `Stacks.DiscreteValuationRing.Ramification.inertiaDeg_eq_one_of_isAlgClosed_residueField`:
  `f = 1` over an algebraically closed residue field.
* `bijective_algebraMap_of_ramificationIdx_eq_one_of_isAlgClosed_residueField`: over an
  algebraically closed residue field, `e = 1` makes `K → L` bijective.
-/

@[expose] public section

namespace Stacks.DiscreteValuationRing.Ramification

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [FaithfulSMul A B]

variable (K L : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra B L] [IsFractionRing B L] [Algebra A L] [Algebra K L] [IsScalarTower A B L]
  [IsScalarTower A K L]

/-- The local fundamental identity `[L : K] = e f` for a finite flat extension of discrete
valuation rings, expressed using the fraction fields. Here `e` is the ramification index and `f`
is the residue degree. -/
theorem ramificationIdx_mul_inertiaDeg_eq_finrank [IsLocalHom (algebraMap A B)]
    [Module.Finite A B] [Module.Flat A B] :
    ramificationIdx A B * Ideal.inertiaDeg (IsLocalRing.maximalIdeal B) A =
      Module.finrank K L := by
  rw [ramificationIdx_def,
    Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal B) (IsDiscreteValuationRing.not_a_field A),
    IsFractionRing.finrank_eq A K B L]
  classical
  let _ : Fintype ((IsLocalRing.maximalIdeal A).primesOver B) := Fintype.ofFinite _
  have hset := IsLocalRing.primesOver_eq B (IsDiscreteValuationRing.not_a_field A)
  let _ : Unique ((IsLocalRing.maximalIdeal A).primesOver B) :=
    { default := ⟨IsLocalRing.maximalIdeal B, by simp [hset]⟩
      uniq q := Subtype.ext (by simpa [hset] using q.2) }
  have hdefault : ((default : (IsLocalRing.maximalIdeal A).primesOver B) : Ideal B) =
      IsLocalRing.maximalIdeal B := rfl
  simpa [hdefault] using Ideal.sum_ramification_inertia_eq_finrank (IsLocalRing.maximalIdeal A) B

omit [FaithfulSMul A B] in
/-- The residue degree of a finite local extension of discrete valuation rings is one if the
residue field downstairs is algebraically closed. -/
theorem inertiaDeg_eq_one_of_isAlgClosed_residueField
    [IsLocalHom (algebraMap A B)]
    [Module.Finite A B] [IsAlgClosed (IsLocalRing.maximalIdeal A).ResidueField] :
    Ideal.inertiaDeg (IsLocalRing.maximalIdeal B) A = 1 := by
  let _ := Localization.AtPrime.algebraOfLiesOver (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal B)
  rw [Ideal.inertiaDeg_eq (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)]
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
    IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- A finite extension of discretely valued fraction fields with ramification index one is
trivial if the residue field downstairs is algebraically closed. -/
theorem bijective_algebraMap_of_ramificationIdx_eq_one_of_isAlgClosed_residueField
    [IsLocalHom (algebraMap A B)] [Module.Finite A B] [Module.Flat A B]
    [IsAlgClosed (IsLocalRing.maximalIdeal A).ResidueField]
    (he : ramificationIdx A B = 1) : Function.Bijective (algebraMap K L) := by
  have hdeg := ramificationIdx_mul_inertiaDeg_eq_finrank A B K L
  rw [he, inertiaDeg_eq_one_of_isAlgClosed_residueField A B, one_mul] at hdeg
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdeg.symm

end Stacks.DiscreteValuationRing.Ramification
