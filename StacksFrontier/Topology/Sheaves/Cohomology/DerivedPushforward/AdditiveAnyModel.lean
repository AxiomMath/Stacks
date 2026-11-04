module

public import StacksFrontier.Homology.DerivedCategory.Bridge.Pushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# The derived direct image is additive, for every model of the derived categories

For a morphism of ringed spaces `f : X ⟶ Y`, the derived direct image
`Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` of `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces` is an additive
functor, whatever models of the two derived categories are chosen. At the standard models it is
triangulated, being the right adjoint of the derived pullback
(`derivedPushforward_isTriangulated`), hence additive; at any other models it is isomorphic to the
standard one conjugated by the comparison equivalences of the models
(`StacksDraft.DerivedModel.derivedPushforwardModelEquivIso`), which are additive.

## Main results

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_additive`: the instance.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory StacksDraft.DerivedModel RingedSpaceModuleAdjunction

universe w₁ w₂ u

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [hX : HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
  [hY : HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]

/-- **The derived direct image is additive**, at every model of the derived categories. -/
instance derivedPushforward_additive : (derivedPushforward f).Additive := by
  have h₁ : (@derivedPushforward X Y f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _)).Additive := by
    let := derivedPushforwardCommShift f
    have := derivedPushforward_isTriangulated f
    infer_instance
  have := modelEquiv_functor_additive (HasDerivedCategory.standard
    (SheafOfModules.{u} (structureSheafRing Y))) hY
  have := modelEquiv_functor_additive (HasDerivedCategory.standard
    (SheafOfModules.{u} (structureSheafRing X))) hX
  let EX := modelEquiv (HasDerivedCategory.standard
    (SheafOfModules.{u} (structureSheafRing X))) hX
  let e := derivedPushforwardModelEquivIso f (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _) hX hY
  exact Functor.additive_of_iso
    (Functor.isoWhiskerLeft EX.inverse e ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight EX.counitIso _ ≪≫ Functor.leftUnitor _)

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end
