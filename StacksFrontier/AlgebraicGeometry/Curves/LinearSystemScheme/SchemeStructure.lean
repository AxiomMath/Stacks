module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.Representability
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CanonicalSectionOrder
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-!
# The scheme structure on a complete linear system

Let `X` be a smooth projective curve over an algebraically closed field `k` and `D ⊆ X` an
effective Cartier divisor of degree `d`. This file collects the inputs for representing the
fibre of the Abel map `γ_d` over the point of `𝒪_X(D)` by the projective space
`𝐏(H⁰(X, 𝒪_X(D))^∨)` of [Stacks, Example 0FCY]; the representability itself is
`Stacks.LinearSystemScheme.exists_abelFibre_equiv_projectiveSpace_canonical`.

## Main results

* `Stacks.LinearSystemScheme.projectiveSpaceOfModuleOverIso`: `𝐏(V) ≅ Proj k[T₀, …, Tₙ]` over `k`.
* `Stacks.LinearSystemScheme.one_le_finrank_globalSections`: `h⁰(𝒪_X(D)) ≥ 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.SectionsBaseChange Stacks.Hilbert

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.LinearSystemScheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- `𝐏(V)` and `Proj k[T₀, …, Tₙ]` are isomorphic as `k`-schemes, for a basis of `V`. -/
def projectiveSpaceOfModuleOverIso {V : Type u} [AddCommGroup V] [Module k V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) k V) :
    (projectiveSpaceOfModule k V).asOver (Spec (.of k)) ≅ projOver k (n := n) :=
  Over.isoMk (projectiveSpaceOfModuleIsoProjMvPolynomial b)
    (projectiveSpaceOfModuleIsoProjMvPolynomial_hom_comp_toSpecZero b)

variable [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
  (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

omit [IsAlgClosed k] [IsProjectiveVariety k f] [Smooth f] in
include k f in
/-- The underlying space of the curve `X` has Krull dimension at most `1`. -/
theorem topologicalKrullDim_le_one : topologicalKrullDim X ≤ 1 :=
  (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le

omit [IsAlgClosed k] [IsCurve k f] [Smooth f] in
/-- The space `H⁰(X, 𝒪_X(D))` of global sections of `𝒪_X(D)` has dimension at least `1`. -/
theorem one_le_finrank_globalSections :
    1 ≤ Module.finrank k (cohomologyOverField k f
      (Stacks.Divisors.modulesInvertibleSheaf D) 0) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : (Stacks.Divisors.modulesInvertibleSheaf D).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X _
  have hfd := finiteDimensional_cohomologyOverField_of_isProper k f
    (Stacks.Divisors.modulesInvertibleSheaf D) 0
  let e := (cohomologyOverFieldZeroIsoSections k f
    (Stacks.Divisors.modulesInvertibleSheaf D)).toLinearEquiv
  rw [Nat.one_le_iff_ne_zero, Ne, Module.finrank_eq_zero_iff_of_free,
    not_subsingleton_iff_nontrivial]
  refine ⟨⟨e.symm ((Stacks.Divisors.canonicalSections D).eval (op ⊤)), 0, ?_⟩⟩
  intro h
  exact canonicalSections_eval_top_ne_zero D ‹_› (e.symm.injective (h.trans e.symm.map_zero.symm))

end Stacks.LinearSystemScheme

end
