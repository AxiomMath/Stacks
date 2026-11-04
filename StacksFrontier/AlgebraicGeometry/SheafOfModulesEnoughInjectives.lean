module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Module sheaves on a scheme have enough injectives

The category of sheaves of modules over the sheaf of rings of a scheme is a Grothendieck abelian
category, so it has enough injectives. Instance search does not find this at the `sheafCompose`
expression `X.ringCatSheaf`, which is why the instance is stated; and it does not find it at the
`structureSheafRing` spelling of the same sheaf of rings either, which is why the second instance
is stated.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Cohomology

universe u

/-- Sheaves of modules over the ring sheaf of a scheme have enough injectives. -/
instance enoughInjectives_sheafOfModules_ringCatSheaf (X : AlgebraicGeometry.Scheme.{u}) :
    EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
  IsGrothendieckAbelian.enoughInjectives

/-- Sheaves of modules over the structure sheaf of a scheme have enough injectives, at the
`structureSheafRing` spelling of that sheaf of rings. The two spellings are equal by `rfl`, but
instance search reaches the statement for `AlgebraicGeometry.Scheme.ringCatSheaf` only after
unfolding, which is expensive inside the derived-functor instances that consume it. -/
instance enoughInjectives_sheafOfModules_structureSheafRing
    (X : AlgebraicGeometry.Scheme.{u}) :
    EnoughInjectives (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
  enoughInjectives_sheafOfModules_ringCatSheaf X

end Stacks.Cohomology
