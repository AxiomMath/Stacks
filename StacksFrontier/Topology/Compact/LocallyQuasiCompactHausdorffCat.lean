module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import StacksCore.Topology.Compact.LocallyQuasiCompact

/-!
# The category of Hausdorff locally quasi-compact spaces

This file introduces the category of Hausdorff, locally quasi-compact topological spaces and
continuous maps. It is the ambient category of Stacks, Section 21.31 (Tag 09WY).

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactHausdorff`: the full subcategory of `TopCat` on the
  Hausdorff, locally quasi-compact spaces.
* `Stacks.Topology.locallyQuasiCompactHausdorffToTop`: its canonical inclusion into `TopCat`.

## Main results

Objects of `LocallyQuasiCompactHausdorff` carry their Hausdorff structure and satisfy
`LocallyCompactSpace` as instances, so the usual topological API applies to them directly.

## Implementation notes

The category is a full subcategory of `TopCat`, so its morphisms are exactly the continuous
maps and the inherited concrete-category API exposes their underlying functions. Local
quasi-compactness in the sense of Stacks 0068 is Mathlib's `LocallyCompactSpace`, as recorded
in `StacksCore/Topology/Compact/LocallyQuasiCompact.lean`.

## References

* [Stacks Project, Section 21.31 (Tag 09WY)](https://stacks.math.columbia.edu/tag/09WY)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Topology

universe u

/-- The category of Hausdorff, locally quasi-compact topological spaces and continuous
maps. -/
@[stacks 09WY "the category LC of Hausdorff and locally quasi-compact spaces"]
abbrev LocallyQuasiCompactHausdorff :=
  ObjectProperty.FullSubcategory
    (fun X : TopCat.{u} => T2Space X ∧ LocallyCompactSpace X)

namespace LocallyQuasiCompactHausdorff

/-- The underlying type of a Hausdorff, locally quasi-compact space. -/
instance : CoeSort LocallyQuasiCompactHausdorff.{u} (Type u) where
  coe X := X.obj

/-- Regard a Hausdorff, locally quasi-compact topological space as an object of
`LocallyQuasiCompactHausdorff`. -/
abbrev of (X : Type u) [TopologicalSpace X] [T2Space X]
    (hX : LocallyCompactSpace X) : LocallyQuasiCompactHausdorff.{u} :=
  ⟨TopCat.of X, inferInstance, hX⟩

/-- Every object of `LocallyQuasiCompactHausdorff` is Hausdorff. -/
instance (X : LocallyQuasiCompactHausdorff.{u}) : T2Space X :=
  X.property.1

/-- Every object of `LocallyQuasiCompactHausdorff` is locally quasi-compact. -/
instance (X : LocallyQuasiCompactHausdorff.{u}) : LocallyCompactSpace X :=
  X.property.2

end LocallyQuasiCompactHausdorff

/-- The canonical inclusion of Hausdorff, locally quasi-compact spaces into topological
spaces. -/
abbrev locallyQuasiCompactHausdorffToTop :
    LocallyQuasiCompactHausdorff.{u} ⥤ TopCat.{u} :=
  ObjectProperty.ι _

end Stacks.Topology
