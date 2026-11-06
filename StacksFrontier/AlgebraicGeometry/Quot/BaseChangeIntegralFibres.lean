module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.IntegralGeometricFibres

/-!
# Base changes to fields of a morphism with integral geometric fibres

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` whose geometric fibres are
integral, `AlgebraicGeometry.Space.HasIntegralGeometricFibres`. Then for every test scheme
`T = Spec(k) ⟶ Y` which is the spectrum of a field, the base change
`X_T = AlgebraicGeometry.Space.baseChangeSpace f T` is an integral algebraic space.

This is the form in which the hypothesis of Stacks 0DNJ, that the geometric fibres of
`X ⟶ B` are integral, enters the valuative argument: the closed fibre of `X` over a valuation
ring is a base change of this kind.

## Main results

* `AlgebraicGeometry.Space.isIntegralSpace_baseChangeSpace_of_hasIntegralGeometricFibres`.

## Implementation notes

The base change along a test scheme is the presheaf fibre product with the morphism of
algebraic spaces from the test scheme, so it is the fibre of
`AlgebraicGeometry.Space.fieldFibre` over the field-valued point that morphism represents, and
`AlgebraicGeometry.Space.isIntegralSpace_fieldFibre_of_hasIntegralGeometricFibres` applies.

## References

* [Stacks Project, Tag 0DNJ](https://stacks.math.columbia.edu/tag/0DNJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_baseChangeIntegralFibres :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_baseChangeIntegralFibres
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_baseChangeIntegralFibres.has_limit _

/-- **Base changes to fields of a morphism with integral geometric fibres are integral.** Let
`f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose geometric fibres are integral, and
let `T = Spec(k) ⟶ Y` be a test scheme over `Y` which is the spectrum of a field `k`. Then the
base change `X_T` is an integral algebraic space. -/
theorem isIntegralSpace_baseChangeSpace_of_hasIntegralGeometricFibres
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : HasIntegralGeometricFibres B S hS f.hom)
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (a : Spec (.of k) ⟶ S)
    (h : (schemeSpaceFunctor B S hS).obj (siteObject B S hS hk a) ⟶ Y) :
    IsIntegralSpace B S hS (baseChangeSpace f (CostructuredArrow.mk h)).1 := by
  let p : FieldValuedPoint B S hS Y.1 :=
    { carrier := k
      contained := hk
      toBase := a
      value := yonedaEquiv h.hom }
  have key : ∀ g : yoneda.obj (siteObject B S hS hk a) ⟶ Y.1, g = h.hom →
      IsIntegralSpace B S hS (pullback f.hom g) →
        IsIntegralSpace B S hS (pullback f.hom h.hom) := fun _ e hg => e ▸ hg
  exact key _ (yonedaEquiv.symm_apply_apply h.hom)
    (isIntegralSpace_fieldFibre_of_hasIntegralGeometricFibres B S hS X.2 Y.2 hf p)

end AlgebraicGeometry.Space

end
