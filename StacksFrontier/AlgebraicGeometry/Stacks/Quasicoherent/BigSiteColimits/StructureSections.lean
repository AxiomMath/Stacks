module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf

/-!
# Sections of the structure sheaf of a category fibred in groupoids

The structure sheaf of an associated site of a category fibred in groupoids over a big fppf
category of schemes is the inverse image of the structure sheaf of the big site, whose presheaf
sends an object to the global functions on the underlying scheme.  Its sections at an object are
therefore the global functions on the scheme underlying the image of that object, and its
restriction maps are the corresponding maps of global functions, on the nose.

Those identifications are definitional, but definitional equations between objects are not
rewritable and instance search does not unfold them, so they are named here and used as
rewrites.  Having them as lemmas is what lets a statement about the sections of a sheaf of
modules over such a site be matched with a statement about modules over the ring of global
functions on an affine, which is where faithfully flat descent happens.

## Main results

* `AlgebraicGeometry.FibredSite.structureSheaf_obj_obj` and
  `AlgebraicGeometry.FibredSite.ringStructureSheafCore_obj_obj`: **the sections of the structure
  sheaf at an object are the global functions on the underlying scheme.**
* `AlgebraicGeometry.FibredSite.structureSheaf_obj_map` and
  `AlgebraicGeometry.FibredSite.ringStructureSheafCore_obj_map`: its restriction maps are the
  maps of global functions.
* `AlgebraicGeometry.FibredSite.ringStructureSheafCore_carrier`: the same identification of the
  underlying types, for use where only the carrier is at issue.

## Implementation notes

None of these is a `simp` lemma.  They are equations between objects of `CommRingCat` and
`RingCat`, so rewriting with them inside a type would raise a motive problem; they are meant to
be applied to a goal which has been arranged to mention one side, exactly as a named
definitional equation is.

The sections are described through `AlgebraicGeometry.Scheme.Γ` rather than through an
isomorphism with the coordinate ring of an affine, since the identification holds at every
object and affineness plays no part in it.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (τ : SiteKind)

/-- **The sections of the structure sheaf of an associated site at an object are the global
functions on the underlying scheme.** -/
theorem structureSheaf_obj_obj (x : 𝒳) :
    (structureSheaf B S hS p hp τ).obj.obj (op x) =
      CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤) := rfl

/-- The restriction map of the structure sheaf of an associated site along a morphism is the map
of global functions along the underlying morphism of schemes. -/
theorem structureSheaf_obj_map {x y : 𝒳} (f : x ⟶ y) :
    (structureSheaf B S hS p hp τ).obj.map f.op =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (p.map f)).op := rfl

/-- **The sections of the coefficient sheaf of rings of an associated site at an object are the
global functions on the underlying scheme.**  This is
`AlgebraicGeometry.FibredSite.structureSheaf_obj_obj` after forgetting commutativity, which is
the form modules over the site are taken in. -/
theorem ringStructureSheafCore_obj_obj (x : 𝒳) :
    (ringStructureSheafCore B S hS p hp τ).obj.obj (op x) =
      RingCat.of Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤) := rfl

/-- The restriction map of the coefficient sheaf of rings of an associated site along a morphism
is the map of global functions along the underlying morphism of schemes. -/
theorem ringStructureSheafCore_obj_map {x y : 𝒳} (f : x ⟶ y) :
    (ringStructureSheafCore B S hS p hp τ).obj.map f.op =
      (forget₂ CommRingCat RingCat).map
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (p.map f)).op) := rfl

/-- The type of sections of the coefficient sheaf of rings of an associated site at an object is
the type of global functions on the underlying scheme. -/
theorem ringStructureSheafCore_carrier (x : 𝒳) :
    ((ringStructureSheafCore B S hS p hp τ).obj.obj (op x) : Type u) =
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤) := rfl

end AlgebraicGeometry.FibredSite

end
