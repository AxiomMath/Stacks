module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Open subschemes of an object of the big fppf site

An open subscheme of the scheme underlying an object `T` of the big fppf site over `S` is
again an object of that site, since an open subscheme is no larger than its ambient scheme,
and it comes with a canonical morphism to `T` whose underlying morphism of schemes is the
open inclusion.

## Main definitions

* `AlgebraicGeometry.Space.openSiteObject` is the object of the site attached to an open
  subscheme, and `AlgebraicGeometry.Space.openSiteObjectHom` the canonical morphism to the
  ambient object.

## Main results

* `AlgebraicGeometry.Space.contains_coe_opens`: an open subscheme of an object of the site
  belongs to the site.
* `AlgebraicGeometry.Space.toScheme_obj_openSiteObject` and
  `AlgebraicGeometry.Space.map_openSiteObjectHom`: the underlying scheme is the open
  subscheme and the underlying morphism is its inclusion, both by `rfl`.

## Implementation notes

The structure morphism is built with `CategoryTheory.ObjectProperty.homMk`, which is
transparent, so both identifications of the underlying scheme and morphism hold by `rfl` --
which is what consumers unfold through.

This module previously carried a second spelling of the same notion, building the structure
morphism with the inclusion functor's `CategoryTheory.Functor.preimage`. That route goes
through the full subcategory's `CategoryTheory.Functor.Full` instance and hence through
`Exists.choose`, so it is irreducible: the two spellings were the same object of the site but
only propositionally, and `rfl` did not identify them even with all unfolding. The
`preimage` spelling has been removed in favour of the transparent one, which is why
`map_openSiteObjectHom` is now `rfl` where it once needed
`CategoryTheory.Functor.map_preimage`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS) (V : ((BigFppfOver.toScheme B S hS).obj T).Opens)

/-- An open subscheme of the scheme underlying an object of the big fppf site over `S` again
belongs to the site: it is no larger than the ambient scheme. -/
theorem contains_coe_opens : B.Contains V.toScheme :=
  (Scheme.size_coe_opens_le _ V).trans_lt T.left.2

/-- The object of the big fppf site over `S` given by an open subscheme of the scheme
underlying an object `T`, with the structure morphism obtained by composing the open
inclusion with that of `T`. -/
def openSiteObject : BigFppfOver B S hS :=
  Over.mk (Y := ⟨V.toScheme, lt_of_le_of_lt (Scheme.size_coe_opens_le _ V) T.left.property⟩)
    (ObjectProperty.homMk V.ι ≫ T.hom)

/-- The canonical morphism from the object attached to an open subscheme to the ambient
object. -/
def openSiteObjectHom : openSiteObject B S hS T V ⟶ T :=
  Over.homMk (ObjectProperty.homMk V.ι) rfl

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.openSiteObjectHom` is the
open inclusion. -/
@[simp]
theorem toScheme_obj_openSiteObject :
    (BigFppfOver.toScheme B S hS).obj (openSiteObject B S hS T V) = V.toScheme := rfl

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.openSiteObjectHom` is the
open inclusion. -/
@[simp]
theorem map_openSiteObjectHom :
    (BigFppfOver.toScheme B S hS).map (openSiteObjectHom B S hS T V) = V.ι := rfl

end AlgebraicGeometry.Space

end
