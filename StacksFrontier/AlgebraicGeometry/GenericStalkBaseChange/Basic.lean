module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.AlgebraicGeometry.AssociatedPointPrime.Basic

/-!
# The stalk of a quasi-coherent module at the generic point

Let `X` be an integral scheme with generic point `η`, let `F` be a quasi-coherent `𝒪_X`-module
and let `U` be a nonempty affine open of `X`. Writing `A = Γ(X, U)` and `M = Γ(F, U)`, the germ
at `η` exhibits the stalk `F_η` as the localization of `M` at the nonzerodivisors of `A`, and
hence as the base change `K(X) ⊗_A M`, where `K(X) = 𝒪_{X, η}` is the function field.

## Main results

* `Stacks.AlgebraicGeometry.GenericStalkBaseChange.primeCompl_primeIdealOf_genericPoint`: on a
  nonempty affine open of an integral scheme the functions not vanishing at the generic point
  are exactly the nonzerodivisors.
* `Stacks.AlgebraicGeometry.GenericStalkBaseChange.isLocalizedModule_germ_genericPoint`: the
  germ at the generic point localizes the sections at the nonzerodivisors.
* `Stacks.AlgebraicGeometry.GenericStalkBaseChange.isBaseChange_germ_genericPoint` and
  `Stacks.AlgebraicGeometry.GenericStalkBaseChange.functionFieldTensorSectionsEquiv`: the
  resulting identification `K(X) ⊗_{Γ(X, U)} Γ(F, U) ≅ F_η`.

## Implementation notes

The quasi-coherence input is
`Stacks.AlgebraicGeometry.AssociatedPointPrime.isLocalizedModule_germₗ`, which presents the
stalk at a point of an affine open as the localization at the prime of that point. What is added
here is the identification of that prime at the *generic* point: it is the zero ideal, by
`AlgebraicGeometry.IsAffineOpen.primeIdealOf_genericPoint` and
`AlgebraicGeometry.genericPoint_eq_bot_of_affine`, so its prime complement is the
nonzerodivisors — the same submonoid at which `AlgebraicGeometry.functionField` is a
localization of `Γ(X, U)`. Matching the two submonoids is what turns the localization statement
into a base change, by `IsLocalizedModule.isBaseChange`.

The two module structures on the stalk are not found by instance search, for the reason recorded
in `Stacks.AlgebraicGeometry.AssociatedPointPrime`: the `Γ(X, U)`-action cannot unfold
`AlgebraicGeometry.Scheme.Modules.presheaf`. They are introduced with `letI`, and the statements
below therefore carry `letI` binders.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 0BXL](https://stacks.math.columbia.edu/tag/0BXL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.AssociatedPointPrime
open Stacks.AlgebraicGeometry.AssociatedPointsMono
open scoped nonZeroDivisors

universe u

namespace Stacks.AlgebraicGeometry.GenericStalkBaseChange

variable {X : Scheme.{u}} [IsIntegral X]

/-- On a nonempty affine open of an integral scheme the prime of the generic point is the zero
ideal, so the sections not vanishing at the generic point are exactly the nonzerodivisors. -/
theorem primeCompl_primeIdealOf_genericPoint {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (h : genericPoint X ∈ U) :
    (hU.primeIdealOf ⟨genericPoint X, h⟩).asIdeal.primeCompl = Γ(X, U)⁰ := by
  rw [show (⟨genericPoint X, h⟩ : U) =
      ⟨genericPoint X,
        ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)⟩ from
    rfl, IsAffineOpen.primeIdealOf_genericPoint hU, genericPoint_eq_bot_of_affine]
  ext
  exact mem_nonZeroDivisors_iff_ne_zero.symm

/-- **The germ at the generic point localizes the sections of a quasi-coherent module at the
nonzerodivisors.** On a nonempty affine open `U` of an integral scheme, the germ map
`Γ(F, U) → F_η` exhibits the stalk at the generic point as the localization of `Γ(F, U)` at the
nonzerodivisors of `Γ(X, U)`. -/
theorem isLocalizedModule_germ_genericPoint (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] (h : genericPoint X ∈ U) :
    letI := sectionsStalkModule F h
    IsLocalizedModule Γ(X, U)⁰ (germₗ F h) := by
  let _ := sectionsStalkModule F h
  have hloc := isLocalizedModule_germₗ F hU h
  -- `Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ` states its conclusion through
  -- Mathlib's `IsLocalizedModule.AtPrime` abbrev, so the abbrev is unfolded before the rewrite:
  -- the two are reducibly defeq but `rw` matches syntactically.
  rw [IsLocalizedModule.AtPrime] at hloc
  rwa [primeCompl_primeIdealOf_genericPoint hU h] at hloc

/-- The `Γ(X, U)`-action on the stalk at the generic point is compatible with the function
field's. -/
theorem isScalarTower_functionField (F : X.Modules) {U : X.Opens} [Nonempty U]
    (h : genericPoint X ∈ U) :
    letI := stalkModule F (genericPoint X)
    letI := sectionsStalkModule F h
    IsScalarTower Γ(X, U) X.functionField (F.presheaf.stalk (genericPoint X)) :=
  let := stalkModule F (genericPoint X)
  let := sectionsStalkModule F h
  ⟨fun a b z => mul_smul (X.germToFunctionField U a) b z⟩

/-- **The stalk of a quasi-coherent module at the generic point is a base change of its sections
over a nonempty affine open**: `F_η = K(X) ⊗_{Γ(X, U)} Γ(F, U)`. -/
theorem isBaseChange_germ_genericPoint (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] (h : genericPoint X ∈ U) :
    letI := stalkModule F (genericPoint X)
    letI := sectionsStalkModule F h
    letI := isScalarTower_functionField F h
    IsBaseChange X.functionField (germₗ F h) :=
  let := stalkModule F (genericPoint X)
  let := sectionsStalkModule F h
  let := isScalarTower_functionField F h
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let := isLocalizedModule_germ_genericPoint F hU h
  IsLocalizedModule.isBaseChange Γ(X, U)⁰ X.functionField (germₗ F h)

/-- The identification `K(X) ⊗_{Γ(X, U)} Γ(F, U) ≅ F_η` of
`Stacks.AlgebraicGeometry.GenericStalkBaseChange.isBaseChange_germ_genericPoint`. -/
noncomputable def functionFieldTensorSectionsEquiv (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] (h : genericPoint X ∈ U) :
    letI := stalkModule F (genericPoint X)
    letI := sectionsStalkModule F h
    TensorProduct Γ(X, U) X.functionField Γ(F, U) ≃ₗ[X.functionField]
      F.presheaf.stalk (genericPoint X) :=
  letI := stalkModule F (genericPoint X)
  letI := sectionsStalkModule F h
  letI := isScalarTower_functionField F h
  (isBaseChange_germ_genericPoint F hU h).equiv

end Stacks.AlgebraicGeometry.GenericStalkBaseChange

end

