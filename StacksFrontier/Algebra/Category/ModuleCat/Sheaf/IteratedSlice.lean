module

public import Mathlib.Algebra.Homology.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree

/-!
# Sheaves of modules on an iterated slice site

Let `R` be a sheaf of rings on a site `(C, J)` and let `f : V ⟶ U` be an arrow of `C`.
Restriction of `R.over U`-modules to the slice of `C/U` over the object `Over.mk f`, namely
`SheafOfModules.overFunctor (R.over U) (Over.mk f)`, lands in modules on the *iterated* slice
`(C/U)/(Over.mk f)`, whereas most of the development speaks of the slice `C/V`. The two
descriptions agree, and this file records the comparison: it is the pushforward of sheaves of
modules along `CategoryTheory.Over.iteratedSliceBackward`, Mathlib's canonical functor
`C/V ⥤ (C/U)/(Over.mk f)`.

## Main definitions

* `Stacks.SheafOfModules.sliceBackward`: transport of sheaves of modules from the iterated
  slice `(C/U)/(Over.mk f)` down to the slice `C/V`.
* `Stacks.SheafOfModules.sliceBackwardIso`: the comparison
  `overFunctor (R.over U) (Over.mk f) ⋙ sliceBackward R f ≅ overMap R f`.
* `Stacks.SheafOfModules.sliceBackwardComplexIso` and
  `Stacks.SheafOfModules.overFunctorMapComplexIso`: the degreewise forms, on cochain
  complexes, of `sliceBackwardIso` and of `SheafOfModules.overFunctorMap`.

## Main results

* `Stacks.SheafOfModules.overFunctor_comp_sliceBackward`: the comparison as an equality of
  functors, which holds by `rfl`.

## Implementation notes

Two facts about this comparison are load-bearing for its consumers.

* `overFunctor_comp_sliceBackward` is an **equality**, by `rfl`: both sides are the pushforward
  of sheaves of modules along one and the same functor `C/V ⥤ C/U`. That is what lets a
  development be phrased entirely with `SheafOfModules.overMap`, for which exactness is
  available (`Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits`,
  `overMap_preservesEpimorphisms`, `overMap_preservesFiniteColimits`) and for which the
  comparison `overFunctor R U ⋙ overMap R f ≅ overFunctor R V` is
  `SheafOfModules.overFunctorMap`.

* The analogue of `sliceBackwardIso` **at the level of complexes** must not be written as an
  `Iso.refl`, even though the two functors are again equal: elaborating that `Iso.refl` forces
  the kernel to unfold two concrete functors on cochain complexes together with the components
  of the identity isomorphism between them, and it exhausts the default heartbeat budget. The
  cheap route, taken by `sliceBackwardComplexIso` and `overFunctorMapComplexIso` below, is
  Mathlib's `CategoryTheory.Functor.mapHomologicalComplexCompIso`, which discharges the
  defeq once and generically, so that at a use site the isomorphism already has the shape
  `F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅ H.mapHomologicalComplex c`. Do not
  "simplify" either of them back to an `Iso.refl`, and do not raise `maxHeartbeats`.

Additivity of the functors involved is not proved here: restriction along a continuous functor
is additive by `SheafOfModules.instAdditivePushforward`, with its unfoldings
`SheafOfModules.instAdditiveOverFunctor` and `SheafOfModules.instAdditiveOverMap`, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/OverFiniteFree.lean`. Only `sliceBackward`
needs its own instance, because it is a `def` and instance search does not unfold it.

## References

* [Stacks Project, Tag 08FP](https://stacks.math.columbia.edu/tag/08FP) — the first statement
  whose formalization needs this comparison. This file carries no tag of its own.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{w}) {U V : C} (f : V ⟶ U)

/-- Continuity of `CategoryTheory.Over.iteratedSliceBackward` for the slice topologies, in the
spelling instance search needs: Mathlib states it with the base written as `(Over.mk f).left`
rather than as `V`. -/
instance isContinuous_iteratedSliceBackward :
    (Over.mk f).iteratedSliceBackward.IsContinuous (J.over V)
      ((J.over U).over (Over.mk f)) :=
  inferInstanceAs ((Over.mk f).iteratedSliceBackward.IsContinuous
    (J.over (Over.mk f).left) ((J.over U).over (Over.mk f)))

/-- Transport of sheaves of modules from the iterated slice `(C/U)/(Over.mk f)` down to the
slice `C/V`, namely the pushforward along `CategoryTheory.Over.iteratedSliceBackward`. The
structure sheaves match on the nose, so the comparison morphism of sheaves of rings is the
identity. -/
def sliceBackward :
    SheafOfModules.{w} ((R.over U).over (Over.mk f)) ⥤ SheafOfModules.{w} (R.over V) :=
  SheafOfModules.pushforward (F := (Over.mk f).iteratedSliceBackward) (𝟙 _)

/-- Transport from the iterated slice is additive: it reindexes the components of a morphism
of sheaves of modules, so sums of morphisms are preserved on the nose. Stated separately from
`SheafOfModules.instAdditivePushforward` because `sliceBackward` is a `def`, which instance
search does not unfold. -/
instance sliceBackward_additive : (sliceBackward R f).Additive :=
  inferInstanceAs (SheafOfModules.pushforward
    (F := (Over.mk f).iteratedSliceBackward) (𝟙 _)).Additive

/-- Restricting a sheaf of `R.over U`-modules to the iterated slice over `Over.mk f` and then
transporting to the slice `C/V` is restriction along `f`: both are the pushforward of sheaves
of modules along one and the same functor `C/V ⥤ C/U`.

This is an equality of functors, not merely an isomorphism; see the implementation notes. -/
theorem overFunctor_comp_sliceBackward :
    SheafOfModules.overFunctor.{w} (R.over U) (Over.mk f) ⋙ sliceBackward R f =
      SheafOfModules.overMap.{w} R f := rfl

/-- The isomorphism form of `overFunctor_comp_sliceBackward`, witnessed by the identity. -/
def sliceBackwardIso :
    SheafOfModules.overFunctor.{w} (R.over U) (Over.mk f) ⋙ sliceBackward R f ≅
      SheafOfModules.overMap.{w} R f :=
  Iso.refl _

/-- The degreewise form of `overFunctor_comp_sliceBackward` on cochain complexes: restricting
a complex to the iterated slice and transporting down is isomorphic to restricting it along
the arrow.

Built from Mathlib's `CategoryTheory.Functor.mapHomologicalComplexCompIso` rather than written
as a single `Iso.refl` at the level of complexes, which does not elaborate within the default
heartbeat budget; see the implementation notes. -/
def sliceBackwardComplexIso :
    (SheafOfModules.overFunctor.{w} (R.over U) (Over.mk f)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
      (sliceBackward R f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (SheafOfModules.overMap.{w} R f).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (sliceBackwardIso R f) (ComplexShape.up ℤ)

/-- The degreewise form of `SheafOfModules.overFunctorMap` on cochain complexes: restricting a
complex of `R`-modules to the slice over `U` and then along `f : V ⟶ U` is isomorphic to
restricting it to the slice over `V`.

Built from Mathlib's `CategoryTheory.Functor.mapHomologicalComplexCompIso` for the same reason
as `sliceBackwardComplexIso`. -/
def overFunctorMapComplexIso :
    (SheafOfModules.overFunctor.{w} R U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      (SheafOfModules.overMap.{w} R f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (SheafOfModules.overFunctor.{w} R V).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (SheafOfModules.overFunctorMap.{w} R f)
    (ComplexShape.up ℤ)

end Stacks.SheafOfModules

end
