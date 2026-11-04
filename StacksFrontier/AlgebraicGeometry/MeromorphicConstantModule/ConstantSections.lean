module

public import StacksFrontier.AlgebraicGeometry.MeromorphicConstantModule.Basic

/-!
# The constant sections of the constant presheaf on the generic stalk

On an integral scheme, over an open set containing the generic point, the comparison
`Stacks.AlgebraicGeometry.MeromorphicConstantModule.toTotalQuotient` from the function field to
the sections of the sheaf of total quotient rings is an isomorphism, and consequently every
section of the presheaf `U ↦ K_X(U) ⊗_{K(X)} M` is the constant section determined by a unique
element of `M`.

## Main definitions

* `Stacks.AlgebraicGeometry.MeromorphicConstantModule.toTotalQuotientLinearEquiv`: the function
  field, as a `K(X)`-linear equivalence onto the sections of the sheaf of total quotient rings over
  an open set containing the generic point.

## Main results

* `Stacks.AlgebraicGeometry.MeromorphicConstantModule.isIso_toSheafify_constPresheaf_app`: over an
  open set containing the generic point the sheafification unit of the constant presheaf is an
  isomorphism.
* `Stacks.AlgebraicGeometry.MeromorphicConstantModule.bijective_toTotalQuotient_app`: over an open
  set containing the generic point the comparison `toTotalQuotient` is bijective.
* `Stacks.AlgebraicGeometry.MeromorphicConstantModule.bijective_constSection`: over such an open
  set the constant sections exhaust the sections of `constModuleOverTotalQuotient`, and are
  determined by their value.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.MeromorphicConstantModule

open Stacks.AlgebraicGeometry.MeromorphicConstant

variable (X : Scheme.{u}) [IsIntegral X]

/-- Over an open set containing the generic point the sheafification unit of the constant presheaf
with value the function field is an isomorphism. -/
theorem isIso_toSheafify_constPresheaf_app {U : X.Opens} (h : genericPoint X ∈ U) :
    IsIso ((toSheafify (Opens.grothendieckTopology X) (constPresheaf X)).app (op U)) := by
  have := isIso_constantToSkyscraper_app X h
  rw [← toSheafify_comp_constantPresheafSkyscraperIso X (op U)] at this
  exact IsIso.of_isIso_comp_right _ ((constantPresheafSkyscraperIso X).hom.app (op U))

/-- Over an open set containing the generic point the comparison from the function field to the
sections of the sheaf of total quotient rings is bijective. -/
theorem bijective_toTotalQuotient_app {U : X.Opens} (h : genericPoint X ∈ U) :
    Function.Bijective (ConcreteCategory.hom ((toTotalQuotient X).app (op U))) := by
  have := isIso_toSheafify_constPresheaf_app X h
  exact (ConcreteCategory.bijective_of_isIso ((presheafIso X).app (op U)).inv).comp
    (ConcreteCategory.bijective_of_isIso
      ((toSheafify (Opens.grothendieckTopology X) (constPresheaf X)).app (op U)))

/-- The function field, as a `K(X)`-linear equivalence onto the sections of the sheaf of total
quotient rings over an open set containing the generic point. -/
noncomputable def toTotalQuotientLinearEquiv {U : X.Opens} (h : genericPoint X ∈ U) :
    letI := algebraOfFunctionField X U
    X.functionField ≃ₗ[X.functionField]
      (totalQuotientSheaf X.sheaf).obj.obj (op U) :=
  let := algebraOfFunctionField X U
  LinearEquiv.ofBijective
    (Algebra.linearMap X.functionField ((totalQuotientSheaf X.sheaf).obj.obj (op U)))
    (bijective_toTotalQuotient_app X h)

/-- **The constant sections exhaust the sections, over an open set containing the generic
point.** Every section of `U ↦ K_X(U) ⊗_{K(X)} M` over such a `U` is the constant section
determined by a unique element of `M`. -/
theorem bijective_constSection (M : ModuleCat.{u} X.functionField) {U : X.Opens}
    (h : genericPoint X ∈ U) :
    Function.Bijective (constSection X M U) := by
  let := algebraOfFunctionField X U
  let e := (TensorProduct.lid X.functionField M).symm.trans
    (TensorProduct.congr (toTotalQuotientLinearEquiv X h) (LinearEquiv.refl X.functionField M))
  have hfun : constSection X M U = fun v ↦ e v := funext fun v ↦
    (constSection_eq X M U v).trans <| congrArg (· ⊗ₜ[X.functionField] v)
      (map_one (algebraMap X.functionField ((totalQuotientSheaf X.sheaf).obj.obj (op U)))).symm
  rw [hfun]
  exact e.bijective

end Stacks.AlgebraicGeometry.MeromorphicConstantModule

end
