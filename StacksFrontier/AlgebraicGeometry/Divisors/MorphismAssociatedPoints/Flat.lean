module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat

/-!
# The structure sheaf of a flat scheme is flat over the base

A morphism of schemes is flat exactly when its stalk maps are flat ring maps, and the stalk of the
structure sheaf of the source, read as a module over itself, is the local ring of the source. So a
flat morphism makes the structure sheaf of its source a flat module over the base in the sense of
Stacks 08KT.

## Main results

* `AlgebraicGeometry.isFlatOver_structureSheafModule`: the structure sheaf of the source of a flat
  morphism is flat over the target.

## Implementation notes

`AlgebraicGeometry.IsFlatOverAt` is phrased for a morphism of ringed spaces and fixes the module
structure on the stalk of `F` to the one carried by the underlying presheaf of modules. Every
module structure in the proof is therefore written at that spelling, and at the ringed-space
spelling of the base map, so that no instance has to be matched across two spellings.

This module deliberately does not import
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace`: with
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` in scope, typeclass resolution picks it
  rather than the structure that
`AlgebraicGeometry.structureSheafStalkLinearEquiv` is stated against, and the two are only
propositionally equal.

## References

* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 08KT** for the structure sheaf: the structure sheaf of the source of a flat morphism
of schemes, read as a module over itself, is flat over the target. -/
theorem isFlatOver_structureSheafModule {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] :
    IsFlatOver f.toLRSHom.toShHom (structureSheafModule X) := by
  intro x
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
    (structureSheafModule X).val
  let : Module (S.presheaf.stalk (f.toLRSHom.toShHom.hom.base x)) (X.presheaf.stalk x) :=
    Module.compHom _ (f.toLRSHom.toShHom.hom.stalkMap x).hom
  let : Module (S.presheaf.stalk (f.toLRSHom.toShHom.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :=
    Module.compHom _ (f.toLRSHom.toShHom.hom.stalkMap x).hom
  have : Module.Flat (S.presheaf.stalk (f.toLRSHom.toShHom.hom.base x))
      (X.presheaf.stalk x) := Flat.stalkMap f x
  let e : (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)
      ≃ₗ[X.presheaf.stalk x] (X.presheaf.stalk x) := structureSheafStalkLinearEquiv X x
  let e' : (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)
      ≃ₗ[S.presheaf.stalk (f.toLRSHom.toShHom.hom.base x)] (X.presheaf.stalk x) :=
    { e.toAddEquiv with
      map_smul' := fun r m ↦ e.map_smul ((f.toLRSHom.toShHom.hom.stalkMap x).hom r) m }
  exact Module.Flat.of_linearEquiv e'

end AlgebraicGeometry
