module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.LocallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEssentiallySmall

/-!
# Smallness of module categories over an essentially small site

Let `C` be a category which is essentially `v`-small, but whose objects and morphisms may live in
larger universes — the fppf site of an algebraic stack is the example this library needs, with
objects in `Type (u + 1)`, morphisms in `Type u`, and essentially `u`-small.  A morphism of
presheaves of modules on `C` is a family of maps indexed by the objects of `C`, so its type is
visibly only small in the universe of those objects; and a subobject is a family of submodules
indexed by the same objects.  Both are nevertheless `v`-small, because a natural transformation
and a stable family of submodules are determined by their values at a set of representatives of
the isomorphism classes of objects.  The first is
`PresheafOfModules.locallySmall_of_essentiallySmall`; this file adds its sheaf form and the
second.

## Main results

* `PresheafOfModules.wellPowered_of_essentiallySmall` and
  `SheafOfModules.wellPowered_of_essentiallySmall`: presheaves and sheaves of modules with
  sections in `Type v` on an essentially `v`-small site are well-powered at `v`.

## Implementation notes

The representatives for well-poweredness are the objects `e.inverse.obj X` for `X` in
`CategoryTheory.SmallModel`, `e` being `CategoryTheory.equivSmallModel`; every object `Y` of `C`
is isomorphic to `e.inverse.obj (e.functor.obj Y)` through the unit of `e`, and a stable family
of submodules is transported along that isomorphism.

Compare `PresheafOfModules.wellPowered'` and `SheafOfModules.wellPowered`, which give
well-poweredness at the universe `max u₁ v` of the objects of the site and of the sections; at a
site whose objects lie in a universe larger than the sections, as for an algebraic stack, those
do not reach the section universe.
-/

@[expose] public section

open CategoryTheory Opposite

universe v v₁ u u₁

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{v} C] (R : Cᵒᵖ ⥤ RingCat.{u})

variable {R} in
/-- A stable family of submodules of a presheaf of modules on an essentially small site is
determined by its values at the representatives of the small model. -/
theorem small_submodule_of_essentiallySmall (M : PresheafOfModules.{v} R) :
    Small.{v} M.Submodule := by
  let e := equivSmallModel.{v} Cᵒᵖ
  have key : ∀ (N : M.Submodule) (Y : Cᵒᵖ) (x : M.obj Y),
      x ∈ N.obj Y ↔ M.map (e.unitIso.hom.app Y) x ∈ N.obj (e.inverse.obj (e.functor.obj Y)) := by
    intro N Y x
    refine ⟨fun hx => N.map_mem _ hx, fun hx => ?_⟩
    have h := N.map_mem (e.unitIso.inv.app Y) hx
    rwa [← M.map_comp_apply, Iso.hom_inv_id_app, M.map_id] at h
  refine small_of_injective
    (f := fun (N : M.Submodule) (X : SmallModel.{v} Cᵒᵖ) => N.obj (e.inverse.obj X)) ?_
  intro N N' h
  ext Y x
  have hY : N.obj (e.inverse.obj (e.functor.obj Y)) = N'.obj (e.inverse.obj (e.functor.obj Y)) :=
    congrFun h (e.functor.obj Y)
  rw [key N, key N', hY]

/-- **Presheaves of modules on an essentially small site are well-powered**, in the universe of
their sections: subobjects are stable families of submodules, which are determined by their
values at a small set of representatives. -/
theorem wellPowered_of_essentiallySmall :
    letI := locallySmall_of_essentiallySmall R
    WellPowered.{v} (PresheafOfModules.{v} R) :=
  let := locallySmall_of_essentiallySmall R
  { subobject_small := fun M =>
      have := small_submodule_of_essentiallySmall M
      small_of_injective (subobjectSubmodule M).injective }

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- **Sheaves of modules on an essentially small site are well-powered**, in the universe of
their sections. -/
theorem wellPowered_of_essentiallySmall :
    letI := PresheafOfModules.locallySmall_of_essentiallySmall.{v} R.obj
    letI := locallySmall_of_faithful (forget R)
    WellPowered.{v} (SheafOfModules.{v} R) :=
  let := PresheafOfModules.locallySmall_of_essentiallySmall.{v} R.obj
  let := locallySmall_of_faithful (forget R)
  { subobject_small := fun M =>
      have := PresheafOfModules.small_submodule_of_essentiallySmall M.val
      small_of_injective (subobjectSubmodule M).injective }

end SheafOfModules

end
