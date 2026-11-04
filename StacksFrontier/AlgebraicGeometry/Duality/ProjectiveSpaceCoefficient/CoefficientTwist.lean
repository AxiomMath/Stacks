module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Smooth
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US

/-!
# The coefficient twists on projective space

For a commutative ring `R` and `n ≥ 0`, write `p : ℙⁿ_R = Proj R[T₀, …, Tₙ] ⟶ Spec R`. This file
sets up the functor `M ↦ p^*M~ ⊗ 𝒪(d)` from `R`-modules to `𝒪_{ℙⁿ_R}`-modules and records that it
is exact and a left adjoint: `M~` is exact in `M`, `p` is flat (it is smooth), and tensoring with
the invertible module `𝒪(d)` is an equivalence.

These are the coefficient sheaves of the computation of the twisted inverse image of
`ℙⁿ_R ⟶ Spec R` with coefficients, [Stacks, Tag 0A9W] at `p^*M~(-n-1)[n]`.

## Main definitions

* `Stacks.Duality.ProjCoeff.coeffFunctor`: `M ↦ p^*M~ ⊗ 𝒪(d)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence Stacks.Ample

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality.ProjCoeff

variable (R : Type u) [CommRing R] (n : ℕ)

/-- Projective space `ℙⁿ_R = Proj R[T₀, …, Tₙ]`. -/
abbrev P : Scheme.{u} := AlgebraicGeometry.Proj (polyGrading R n)

/-- The twisting sheaf `𝒪(d)` on `ℙⁿ_R`. -/
abbrev O (d : ℤ) : (P R n).Modules := ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d

/-- The twisting sheaf `𝒪(d)` is invertible. -/
instance (d : ℤ) : IsInvertibleModule (P R n) (O R n d) := inferInstance

/-- `p : ℙⁿ_R ⟶ Spec R` is flat, being smooth. -/
instance : Flat (projToSpecCoeff R n) := by
  have := smooth_projToSpecCoeff R n
  infer_instance

/-- `M ↦ p^*M̃ ⊗ 𝒪(d)`. -/
def coeffFunctor (d : ℤ) : ModuleCat.{u} R ⥤ (P R n).Modules :=
  tilde.functor (.of R) ⋙ Scheme.Modules.pullback (projToSpecCoeff R n) ⋙
    tensorRightModules (P R n) (O R n d)

/-- `M ↦ p^*M~ ⊗ 𝒪(d)` is left exact: `~` is, `p^*` is because `p` is flat, and tensoring with
the invertible module `𝒪(d)` is an equivalence. -/
instance (d : ℤ) : PreservesFiniteLimits (coeffFunctor R n d) := by
  have := AlgebraicGeometry.preservesFiniteLimits_pullback_of_flat (projToSpecCoeff R n)
  have := AlgebraicGeometry.tilde.preservesFiniteLimits (.of R)
  unfold coeffFunctor
  infer_instance

/-- `M ↦ p^*M~ ⊗ 𝒪(d)` is a left adjoint, being a composite of left adjoints. -/
instance (d : ℤ) : (coeffFunctor R n d).IsLeftAdjoint := by
  have := (tilde.adjunction (R := .of R)).isLeftAdjoint
  have : (tensorRightModules (P R n) (O R n d)).IsEquivalence :=
    Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule _ _
  have : (tensorRightModules (P R n) (O R n d)).IsLeftAdjoint :=
    ((tensorRightModules (P R n) (O R n d)).asEquivalence.toAdjunction).isLeftAdjoint
  unfold coeffFunctor
  infer_instance

end Stacks.Duality.ProjCoeff
