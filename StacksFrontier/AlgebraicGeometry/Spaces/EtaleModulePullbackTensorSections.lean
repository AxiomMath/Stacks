module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleKFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackBoundedAbove
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparisonAdjunction

/-!
# The comparison of the two pullbacks of modules along a morphism of algebraic spaces

For a morphism `a : X' ⟶ X` of algebraic spaces, the pullback of modules of the morphism of
small étale ringed topoi, built from `toModulesHom`, and `AlgebraicGeometry.Space.modulePullback`,
built from `toRingedToposModulesHom`, are compared by
`AlgebraicGeometry.Space.pullbackModulesIsoModulePullback`, a uniqueness of left adjoints. This
file shows that this comparison is the `eqToIso` of the equation of the two four-field morphisms
of ringed topoi, so that it is transparent to every construction made from the pullback, such as
the comparison of Stacks 03EL.

## Main results

* `AlgebraicGeometry.Space.pullbackModulesIsoModulePullback_eq_eqToIso`.
* `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_inv_app`: the inverse of the
  comparison of Stacks 03LW sends a local section of the étale restriction to the unit of
  Tag 03CZ of its preimage under the comparison of Stacks 03LQ.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' : AlgebraicSpaces B S hS}

/-- **The comparison of the two pullbacks of modules along a morphism of algebraic spaces is an
`eqToIso`**: it is the identification induced by
`AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom`. -/
theorem pullbackModulesIsoModulePullback_eq_eqToIso (a : X' ⟶ X) :
    pullbackModulesIsoModulePullback B S hS a =
      eqToIso (congrArg (fun g : Stacks.Sheaves.RingedToposModules.RingedToposHom
          (smallEtaleRingedTopos B S hS X') (smallEtaleRingedTopos B S hS X) ↦
          Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X) g)
        (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom
          (smallEtaleRingedToposHom B S hS a))) := by
  simp only [pullbackModulesIsoModulePullback, modulePullbackAdjunction,
    pushforwardModulesIsoModulePushforward_eq_eqToIso, modulePushforwardIso_eq_eqToIso]
  exact Stacks.Sheaves.RingedToposModules.leftAdjointUniq_ofNatIsoRight_eq_eqToIso
    (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom (smallEtaleRingedToposHom B S hS a))
    (smallEtaleRingedToposHom B S hS a).toModulesPushforwardIso
    (smallEtaleRingedToposHom B S hS a).pushforwardModulesIso
    (pushforwardModules_eq_modulePushforward B S hS a)
    (RingedToposHom.pushforwardModulesIso_hom_app_comp_eqToHom (smallEtaleRingedToposHom B S hS a))

section InverseOnSections

open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
  Stacks.Sheaves.ToposPushforward

/-- **The inverse of the comparison of Stacks Equation 03LW on local sections**: a section `x` of
the étale restriction `G|_{X'}` over a chart is sent to the unit of Tag 03CZ of the section of
the inverse image `a⁻¹G` which the comparison of Stacks 03LQ carries to `x`. -/
theorem modulePullbackIsoEtaleModulePullback_inv_app (a : X' ⟶ X) (ha : IsEtale B S hS a.hom)
    (G : Modules.{u, u} B S hS X.1 X.2) (U : (SmallEtale B S hS X'.1)ᵒᵖ)
    (x : ((etaleModulePullback B S hS a ha).obj G).val.obj U) :
    ((modulePullbackIsoEtaleModulePullback B S hS a ha).inv.app G).val.app U x =
      ((extendScalarsFSharpAdjunction B S hS a).unit.app
          ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
            (smallEtaleRingedToposHom B S hS a).toToposHom
            (structureRingSheaf B S hS X)).obj G)).val.app U
        (((etaleModuleInverseImageIsoRestrictionTransport B S hS a ha).inv.app G).val.app U x) :=
  (congrArg (fun z ↦ ((modulePullbackIsoEtaleModulePullback B S hS a ha).inv.app G).val.app U z)
      ((modulePullbackIsoEtaleModulePullback_unit_app B S hS a ha G U _).trans
        (Stacks.SheafOfModules.hom_val_app_inv_val_app
          ((etaleModuleInverseImageIsoRestrictionTransport B S hS a ha).app G) U x)).symm).trans
    (Stacks.SheafOfModules.inv_val_app_hom_val_app
      ((modulePullbackIsoEtaleModulePullback B S hS a ha).app G) U _)

end InverseOnSections

end AlgebraicGeometry.Space

end
