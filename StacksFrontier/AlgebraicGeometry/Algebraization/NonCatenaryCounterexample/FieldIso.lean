module

public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Basic.Denumerable

/-!
# A field isomorphic to a purely transcendental extension of itself

For a field `k`, the field `K = k(t₀, t₁, …)` of rational functions in countably many variables
is isomorphic, as a ring, to `K(y₁, y₂, y₃)`: both are fraction fields of polynomial rings over
`k` in countably many variables.

This is what allows the two residue fields `K` and `K(x₄, x₅, x₆)` of the semilocal ring of the
counterexample to Stacks 0EJA to be identified.

## Main results

* `Stacks.NonCatenaryExample.fieldEquiv` — `K ≃+* K(y₁, y₂, y₃)`.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.NonCatenaryExample

/-- If `S` is a localization of a domain `R` at a submonoid of nonzero elements, then a fraction
field of `S` is a fraction field of `R`. -/
theorem isFractionRing_of_isLocalization_of_isFractionRing {R S F : Type*} [CommRing R]
    [IsDomain R] [CommRing S] [IsDomain S] [CommRing F] [Algebra R S] [Algebra S F] [Algebra R F]
    [IsScalarTower R S F] (M : Submonoid R) (hM : M ≤ nonZeroDivisors R) [IsLocalization M S]
    [IsFractionRing S F] : IsFractionRing R F := by
  have h := IsLocalization.localization_localization_isLocalization_of_has_all_units M
    (nonZeroDivisors S) F (fun x hx => hx.mem_nonZeroDivisors)
  have hinj : Function.Injective (algebraMap R S) := IsLocalization.injective S hM
  have heq : (nonZeroDivisors S).comap (algebraMap R S) = nonZeroDivisors R := by
    ext x
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    exact (map_ne_zero_iff _ hinj)
  rw [heq] at h
  exact h

variable (k : Type u) [Field k]

/-- The field `K = k(t₀, t₁, …)`. -/
abbrev BigField := FractionRing (MvPolynomial ℕ k)

/-- `Fin 3 ⊕ ℕ ≃ ℕ`. -/
def finThreeSumNatEquiv : Fin 3 ⊕ ℕ ≃ ℕ :=
  haveI := Denumerable.ofEncodableOfInfinite (Fin 3 ⊕ ℕ)
  Denumerable.eqv (Fin 3 ⊕ ℕ)

/-- `k[t][y₁, y₂, y₃] ≅ k[t]`. -/
def polyEquiv : MvPolynomial (Fin 3) (MvPolynomial ℕ k) ≃+* MvPolynomial ℕ k :=
  (MvPolynomial.sumRingEquiv k (Fin 3) ℕ).symm.trans
    (MvPolynomial.renameEquiv k (finThreeSumNatEquiv)).toRingEquiv

/-- `K(y₁, y₂, y₃) ≅ K`. -/
def fieldEquiv : BigField k ≃+* FractionRing (MvPolynomial (Fin 3) (BigField k)) := by
  letI : Algebra (MvPolynomial (Fin 3) (MvPolynomial ℕ k)) (MvPolynomial (Fin 3) (BigField k)) :=
    MvPolynomial.algebraMvPolynomial
  have hM : (nonZeroDivisors (MvPolynomial ℕ k)).map
      (MvPolynomial.C (σ := Fin 3) : MvPolynomial ℕ k →+* _) ≤
      nonZeroDivisors (MvPolynomial (Fin 3) (MvPolynomial ℕ k)) := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a ≠ 0 := nonZeroDivisors.ne_zero ha
    exact mem_nonZeroDivisors_of_ne_zero (by simpa using ha')
  haveI : IsFractionRing (MvPolynomial (Fin 3) (MvPolynomial ℕ k))
      (FractionRing (MvPolynomial (Fin 3) (BigField k))) :=
    isFractionRing_of_isLocalization_of_isFractionRing
      (S := MvPolynomial (Fin 3) (BigField k)) _ hM
  exact (IsFractionRing.ringEquivOfRingEquiv (polyEquiv k)).symm

end Stacks.NonCatenaryExample

end
