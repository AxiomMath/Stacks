module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.Regular

/-!
# Regular Noetherian schemes of every dimension

Affine space `𝔸ⁿ_k = Spec k[x₁, …, xₙ]` over a field is a regular Noetherian scheme of
topological Krull dimension exactly `n`.

## Main results

* `AlgebraicGeometry.isRegular_Spec_mvPolynomial`: affine space over a field is regular.
* `AlgebraicGeometry.topologicalKrullDim_Spec_mvPolynomial`: its dimension is the number of
  variables.
* `AlgebraicGeometry.exists_isRegular_topologicalKrullDim_eq`: for every `n` there is a
  Noetherian scheme which is regular and of topological Krull dimension `n`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Affine space over a field is a regular scheme. -/
theorem isRegular_Spec_mvPolynomial (k : Type u) [Field k] (n : ℕ) :
    IsRegular (Spec (CommRingCat.of (MvPolynomial (Fin n) k))) := fun _ =>
  ⟨⟨⊤, isAffineOpen_top _⟩, trivial, IsRegularRing.of_ringEquiv
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) k))).commRingCatIsoToRingEquiv.symm⟩

/-- Affine `n`-space over a field has topological Krull dimension `n`. -/
theorem topologicalKrullDim_Spec_mvPolynomial (k : Type u) [Field k] (n : ℕ) :
    topologicalKrullDim ↥(Spec (CommRingCat.of (MvPolynomial (Fin n) k))) = n := by
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (MvPolynomial (Fin n) k)).trans ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- Over any field and for every `n` there is a Noetherian scheme that is regular and of
topological Krull dimension `n`. -/
theorem exists_isRegular_topologicalKrullDim_eq (k : Type u) [Field k] (n : ℕ) :
    ∃ X : Scheme.{u}, IsNoetherian X ∧ IsRegular X ∧ topologicalKrullDim X = n := by
  exact ⟨Spec (CommRingCat.of (MvPolynomial (Fin n) k)), inferInstance,
    isRegular_Spec_mvPolynomial k n, topologicalKrullDim_Spec_mvPolynomial k n⟩

end AlgebraicGeometry

end
