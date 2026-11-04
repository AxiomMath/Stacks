module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves of modules on a ringed space have enough injectives

The category of sheaves of modules over the sheaf of rings of a ringed space is Grothendieck
abelian, so it has enough injectives.

## Implementation notes

Instance search does not find these instances through the `forget₂ CommRingCat RingCat` that
`structureSheafRing` postcomposes with, so they are stated here for `structureSheafRing`.
-/

@[expose] public section

open CategoryTheory

namespace RingedSpaceModuleAdjunction

universe u

/-- Sheaves of modules on a ringed space form a Grothendieck abelian category. -/
noncomputable instance isGrothendieckAbelian_sheafOfModules
    (X : AlgebraicGeometry.RingedSpace.{u, u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing X)) :=
  SheafOfModules.instIsGrothendieckAbelian (structureSheafRing X)

/-- Sheaves of modules on a ringed space have enough injectives. -/
@[sga "4½ Etat_0 6.2" "special case"]
noncomputable instance enoughInjectives_sheafOfModules
    (X : AlgebraicGeometry.RingedSpace.{u, u}) :
    EnoughInjectives (SheafOfModules.{u} (structureSheafRing X)) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

end RingedSpaceModuleAdjunction
