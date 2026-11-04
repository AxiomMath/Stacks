module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import StacksCore.Tactic.StacksAttribute

/-!
# The relative structure sheaf map of a morphism of schemes

A morphism of schemes `f : X ⟶ Y` induces a map `f⁻¹𝒪_Y ⟶ 𝒪_X` from the inverse image of the
structure sheaf of `Y` to the structure sheaf of `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.relativeStructureSheafMap`: the map `f⁻¹𝒪_Y ⟶ 𝒪_X`.

## References

* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory Opposite

universe u

/-- The map `f⁻¹𝒪_Y ⟶ 𝒪_X` of sheaves of rings on `X`, adjoint to
`Scheme.Hom.toRingCatSheafHom f`. -/
noncomputable def Scheme.Hom.relativeStructureSheafMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback RingCat f.base).obj Y.ringCatSheaf ⟶ X.ringCatSheaf :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat f.base).homEquiv _ _ |>.symm
    f.toRingCatSheafHom

end AlgebraicGeometry
