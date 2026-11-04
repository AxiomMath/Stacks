module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Coherent sheaves of modules

A sheaf of modules on a ringed space is coherent when it is of finite type and
the relations among every finite family of sections over every open subset are
locally finitely generated. The coherent sheaves form a full subcategory of all
sheaves of modules.

## Main definitions

* `SheafOfModules.IsCoherent` is the predicate that a sheaf of modules is
  coherent.
* `AlgebraicGeometry.SheafOfModules.CoherentModules` is the category of coherent sheaves of
  modules.

## Implementation notes

The class `SheafOfModules.IsCoherent` states both conditions in the source. Its second field
quantifies over maps from finite free sheaves after restriction to an open;
`SheafOfModules.freeHomEquiv` identifies these maps with finite families of sections. The
category denoted `Coh` in the source is represented by the corresponding full subcategory.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

add_to_stacks 01BV "the coherence predicate" SheafOfModules.IsCoherent

namespace AlgebraicGeometry.SheafOfModules

/-- The full category of coherent sheaves of modules over a ringed space. -/
@[stacks 01BV "the category Coh"]
abbrev CoherentModules {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :=
  ObjectProperty.FullSubcategory (C := _root_.SheafOfModules.{u} R) (fun M => M.IsCoherent)

/-- An object of `CoherentModules R` is coherent. -/
instance {X : Type u} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} (M : CoherentModules R) :
    M.obj.IsCoherent :=
  M.property

end AlgebraicGeometry.SheafOfModules
