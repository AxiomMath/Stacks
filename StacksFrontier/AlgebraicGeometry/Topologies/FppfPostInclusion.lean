module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The big fppf category over `S` is determined by its image in schemes over `S`

The functor `Over.post B.inclusion` taking an object of the big fppf category over `S` to the
underlying scheme over `S` is injective on objects: the site is a full subcategory of schemes cut
out by a size bound, so an object of it is a scheme together with a proof, and the slice adds
only a structure morphism, which a full subcategory inclusion reflects by faithfulness.

This is wanted whenever two objects of a category over the site are known to have the same image
in `Over S` — for instance two deformations recorded as lying over `Spec` of the same Artinian
local algebra — and one needs them to lie over the same object of the site itself, so that a
vertical morphism between them can be written down.

## Main results

* `AlgebraicGeometry.BigFppfOver.obj_injective_post_inclusion`.
* `AlgebraicGeometry.BigFppfOver.map_injective_post_inclusion`, the same for morphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.BigFppfOver

universe u

/-- Two objects of a slice category are equal when their left objects agree and their structure
morphisms agree after that transport. -/
private theorem over_ext {C : Type*} [Category C] {Z : C} {X Y : Over Z}
    (h1 : X.left = Y.left) (h2 : eqToHom h1 ≫ Y.hom = X.hom) : X = Y := by
  obtain ⟨xl, xr, xh⟩ := X
  obtain ⟨yl, yr, yh⟩ := Y
  change xl = yl at h1
  subst h1
  change eqToHom rfl ≫ yh = xh at h2
  rw [eqToHom_refl, Category.id_comp] at h2
  subst h2
  congr 1
  exact Subsingleton.elim _ _

/-- The structure morphisms of two equal objects of a slice category agree. -/
private theorem over_hom_of_eq {C : Type*} [Category C] {Z : C} {X Y : Over Z} (h : X = Y) :
    eqToHom (congrArg Over.left h) ≫ Y.hom = X.hom := by
  subst h
  simp

/-- **`Over.post B.inclusion` is injective on objects.** An object of the big fppf category over
`S` is recovered from its underlying scheme over `S`: the underlying object of the site is
recovered because the site is a full subcategory cut out by a proposition, and the structure
morphism because a full subcategory inclusion is faithful. -/
public theorem obj_injective_post_inclusion (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : BigFppfOver B S hS}
    (h : (Over.post B.inclusion).obj X = (Over.post B.inclusion).obj Y) : X = Y := by
  refine over_ext (ObjectProperty.FullSubcategory.ext_iff.mpr (congrArg Over.left h)) ?_
  apply B.inclusion.map_injective
  rw [Functor.map_comp, eqToHom_map]
  exact over_hom_of_eq h

/-- **`Over.post B.inclusion` is injective on morphisms.** A morphism of a slice category is
determined by its underlying morphism, and a full subcategory inclusion is faithful.

This is the morphism counterpart of `obj_injective_post_inclusion`, and it is what lets one
conclude an equality of morphisms of a category over the site from an equality of their images
in schemes over `S` -- for instance from the two `arrow_base` fields of a pair of
deformations. -/
public theorem map_injective_post_inclusion (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : BigFppfOver B S hS} {u v : X ⟶ Y}
    (h : (Over.post B.inclusion).map u = (Over.post B.inclusion).map v) : u = v :=
  Over.OverMorphism.ext (B.inclusion.map_injective (congrArg Over.Hom.left h))

end AlgebraicGeometry.BigFppfOver

end
