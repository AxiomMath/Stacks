module

public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulDerivedSystem
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso

/-!
# The structure sheaf of `Spec A` in degree zero, in three spellings

On `X = Spec A` the structure sheaf placed in degree zero as an object of `D(𝒪_X)` occurs under
three names.  The Koszul lifting machinery of [Stacks, Tag 08DD] calls it
`Koszul.DerivedSystem.structureSheafObject`; the derived tensor product of [Stacks, Tag 06YU]
calls it `Stacks.DerivedTensor.RingedSite.unitObject`, the unit of the tensor product; and the
derived internal Hom calls it `AlgebraicGeometry.RingedSite.derivedStructureSheaf`.  All three
are the degree-zero single complex on `SheafOfModules.unit` of the same sheaf of rings, so the
three are the same object, by `rfl`.

The identification is what lets the general case of [Stacks, Tag 08EH] feed a map out of the
tensor unit into `Koszul.DerivedSystem.exists_isPerfect_lift_of_structureSheaf`, whose source is
the Koszul spelling.

## Main results

* `Stacks.DerivedQCoh.OpenLift.structureSheafObject_eq_unitObject`: the Koszul spelling is the
  unit of the derived tensor product.
* `Stacks.DerivedQCoh.OpenLift.structureSheafObject_eq_derivedStructureSheaf`: it is also the
  structure sheaf of the derived internal Hom.

## Implementation notes

No project tag is attached: nothing is proved here beyond the coincidence of three names for one
object.

## References

* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08DD](https://stacks.math.columbia.edu/tag/08DD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Koszul.DerivedSystem

namespace Stacks.DerivedQCoh.OpenLift

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (A : CommRingCat.{u})

/-- **The structure sheaf of `Spec A` in degree zero is the unit of the derived tensor
product.**  `Koszul.DerivedSystem.structureSheafObject`, the spelling the Koszul lifting
machinery of [Stacks, Tag 08DD] uses, is `Stacks.DerivedTensor.RingedSite.unitObject` of the
ringed site of `Spec A`. -/
theorem structureSheafObject_eq_unitObject :
    structureSheafObject A =
      Stacks.DerivedTensor.RingedSite.unitObject
        (Stacks.SheafOfModules.ringedSite (Spec A).sheaf) :=
  rfl

/-- **The structure sheaf of `Spec A` in degree zero is the one the derived internal Hom is
stated over.** -/
theorem structureSheafObject_eq_derivedStructureSheaf :
    structureSheafObject A =
      RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite (Spec A).sheaf) :=
  rfl

end Stacks.DerivedQCoh.OpenLift

end
