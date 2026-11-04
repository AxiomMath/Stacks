module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksCore.Tactic.StacksAttribute

/-!
# The punctured spectrum of a local ring

The *punctured spectrum* of a local ring `A` is the open complement of the closed point in
`Spec A`, as an object of `(Spec (.of A)).Opens`, so that it carries an open subscheme structure.

## Main definitions

* `Stacks.puncturedSpectrum` is the open complement of the closed point in the spectrum of a
  local ring.

## Implementation notes

The closed point of `Spec A` is `IsLocalRing.closedPoint A`, and its singleton is closed because
the maximal ideal is maximal, so the complement is open with no Noetherian hypothesis.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing

universe u

namespace Stacks

/-- The punctured spectrum of a local ring, obtained by removing its unique closed point. -/
def puncturedSpectrum (A : Type u) [CommRing A] [IsLocalRing A] : (Spec (.of A)).Opens :=
  ⟨({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A))ᶜ,
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2
      (IsLocalRing.maximalIdeal.isMaximal A)).isOpen_compl⟩

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- A point lies in the punctured spectrum exactly when it is not the closed point. -/
theorem mem_puncturedSpectrum {x : PrimeSpectrum A} :
    x ∈ puncturedSpectrum A ↔ x ≠ IsLocalRing.closedPoint A :=
  Iff.rfl

/-- The closed point does not lie in the punctured spectrum. -/
theorem notMem_puncturedSpectrum_closedPoint :
    IsLocalRing.closedPoint A ∉ puncturedSpectrum A := by
  simp [mem_puncturedSpectrum]

end Stacks
