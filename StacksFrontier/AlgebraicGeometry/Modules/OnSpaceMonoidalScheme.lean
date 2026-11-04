module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sheafified tensor product at the scheme spellings of the modules of a scheme

`Stacks.SheafOfModules.OnSpace.monoidal` is the monoidal structure of [Stacks, Tag 01CA] on the
sheaves of modules over a ringed space: its tensor product is the sheafified tensor product and
its unit is the structure sheaf. A scheme-level statement cannot reach it through that
declaration alone, because `AlgebraicGeometry.Scheme.Modules` is a `def` for
`SheafOfModules _.ringCatSheaf` and instance search does not unfold a `def`. This file names the
structure once at both spellings of the category.

Neither declaration is a global instance. The modules of a scheme carry several monoidal
structures with the same isomorphism class and different terms — `Stacks.SheafInternalHom`'s
`schemeMonoidalCategory` and `Stacks.SheafOfModules.sheafTensorMonoidal` among them — so a file
that wants this one asks for it with `attribute [local instance]`.

## Main definitions

* `AlgebraicGeometry.onSpaceModulesMonoidal`: the structure at `X.Modules`.
* `AlgebraicGeometry.onSpaceModulesMonoidal'`: the same structure at
  `SheafOfModules X.ringCatSheaf`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The sheaves of modules on a scheme with the sheafified tensor product of [Stacks, Tag 01CA]:
the tensor product is the sheafified tensor product and the unit is the structure sheaf. -/
@[instance_reducible, sga "4 IV 12.7" "special case"]
def onSpaceModulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace

/-- `AlgebraicGeometry.onSpaceModulesMonoidal` at the other spelling of the same category: instance
search does not unfold the `def` `AlgebraicGeometry.Scheme.Modules`, so a goal written over
`SheafOfModules X.ringCatSheaf` needs the structure named there as well. -/
@[instance_reducible]
def onSpaceModulesMonoidal' (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace

end AlgebraicGeometry

end
