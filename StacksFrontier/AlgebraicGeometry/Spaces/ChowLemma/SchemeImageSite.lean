module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# The scheme-theoretic image of a morphism of the big fppf site

The proof of Stacks 089J cuts its cover out of the `d`-fold fibre power of a projective
compactification `Y` of an étale chart: the cover is built from the scheme-theoretic image `Z`
of the complement of the diagonals `V` inside that fibre power, in which `V` sits as a
*scheme-theoretically dense open* subscheme. For `Z` to be usable where the algebraic space
lives, it has to be an object of the chosen big fppf site.

This file puts it there. The scheme-theoretic image is Mathlib's
`AlgebraicGeometry.Scheme.Hom.image` and is not rebuilt; what is added is that it satisfies the
site's size cutoff — being a closed
subscheme of an object of the site, by Stacks 000R (4) — and the two morphisms of the site which
present it, `V ⟶ Z ⟶ T`.

## Main definitions

* `AlgebraicGeometry.Space.schemeImageObj`: **the scheme-theoretic image of a morphism of the
  big fppf category over `S`, as an object of the big fppf category over `S`.**
* `AlgebraicGeometry.Space.schemeImageObjι`: its closed immersion into the target.
* `AlgebraicGeometry.Space.toSchemeImageObj`: the morphism from the source to it.

## Main results

* `AlgebraicGeometry.Space.toSchemeImageObj_comp_schemeImageObjι`: the two morphisms compose to
  the given one.
* `AlgebraicGeometry.Space.isClosedImmersion_schemeImageObjι`: the inclusion of the image is a
  closed immersion of schemes.
* `AlgebraicGeometry.Space.isOpenImmersion_toSchemeImageObj`: **Stacks 01RG in the site.** A
  morphism of the site which is an immersion of schemes and either quasi-compact or has reduced
  source is an *open* immersion into its scheme-theoretic image.

## What is and is not proved

Stacks 089J is **not** proved here, and no declaration in this file carries a Stacks attribute.
Stacks 01RG is already carried by `AlgebraicGeometry.isOpenImmersion_toImage`, Stacks 000R (4)
by `AlgebraicGeometry.Scheme.size_lt_of_isClosedImmersion`, and what is proved below is the
transport of both into the slice category which is the big fppf category over `S`.

The hypothesis that the morphism be an immersion is kept as a hypothesis and not derived: in
Stacks 089J it holds because the complement of the diagonals is open and closed in the fibre
power of the chart over the algebraic space, which is in turn a closed subscheme of the fibre
power over the base because the algebraic space is separated over the base. Neither of those two
facts is proved here.

Scheme-theoretic density of the image, which is the other half of Stacks 01RG and the input to
Stacks 084N in the source's argument, is not restated: it is
`AlgebraicGeometry.isSchemeTheoreticallyDominant_toImage_of_quasiCompact`.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {V T : BigFppfOver B S hS}

/-- **The scheme-theoretic image of a morphism of the big fppf category over `S`, as an object
of the big fppf category over `S`.** Its underlying scheme is Mathlib's
`AlgebraicGeometry.Scheme.Hom.image`, which satisfies the site's size cutoff because it is a
closed subscheme of the underlying scheme of the target; its structure morphism is the closed
immersion followed by the structure morphism of the target. -/
def schemeImageObj (h : V ⟶ T) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS
    (Scheme.size_lt_of_isClosedImmersion ((BigFppfOver.toScheme B S hS).map h).imageι T.left.2)
    (((BigFppfOver.toScheme B S hS).map h).imageι ≫ B.inclusion.map T.hom)

theorem schemeImageObj_toScheme (h : V ⟶ T) :
    (BigFppfOver.toScheme B S hS).obj (schemeImageObj B S hS h) =
      ((BigFppfOver.toScheme B S hS).map h).image :=
  rfl

theorem schemeImageObj_hom (h : V ⟶ T) :
    B.inclusion.map (schemeImageObj B S hS h).hom =
      ((BigFppfOver.toScheme B S hS).map h).imageι ≫ B.inclusion.map T.hom :=
  rfl

/-- The closed immersion of the scheme-theoretic image into the target, as a morphism of the big
fppf category over `S`. -/
def schemeImageObjι (h : V ⟶ T) : schemeImageObj B S hS h ⟶ T :=
  Over.homMk (ObjectProperty.homMk ((BigFppfOver.toScheme B S hS).map h).imageι)
    (by apply ObjectProperty.hom_ext; rfl)

theorem schemeImageObjι_toScheme (h : V ⟶ T) :
    (BigFppfOver.toScheme B S hS).map (schemeImageObjι B S hS h) =
      ((BigFppfOver.toScheme B S hS).map h).imageι :=
  rfl

/-- The morphism from the source onto its scheme-theoretic image, as a morphism of the big fppf
category over `S`. -/
def toSchemeImageObj (h : V ⟶ T) : V ⟶ schemeImageObj B S hS h :=
  BigFppfOver.homMk B S hS _ _ ((BigFppfOver.toScheme B S hS).map h).toImage
    (by
      rw [← Category.assoc, Scheme.Hom.toImage_imageι,
        show (BigFppfOver.toScheme B S hS).map h = B.inclusion.map h.left from rfl,
        ← Functor.map_comp, Over.w])

theorem toSchemeImageObj_toScheme (h : V ⟶ T) :
    (BigFppfOver.toScheme B S hS).map (toSchemeImageObj B S hS h) =
      ((BigFppfOver.toScheme B S hS).map h).toImage :=
  rfl

/-- **The two morphisms through the scheme-theoretic image compose to the given one.** -/
theorem toSchemeImageObj_comp_schemeImageObjι (h : V ⟶ T) :
    toSchemeImageObj B S hS h ≫ schemeImageObjι B S hS h = h :=
  BigFppfOver.map_toScheme_injective B S hS
    (Scheme.Hom.toImage_imageι ((BigFppfOver.toScheme B S hS).map h))

/-- **The inclusion of the scheme-theoretic image is a closed immersion.** -/
theorem isClosedImmersion_schemeImageObjι (h : V ⟶ T) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (schemeImageObjι B S hS h)) :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map h).imageι)

/-- **Stacks 01RG in the big fppf category over `S`.** A morphism of the site which is an
immersion of schemes, and which is either quasi-compact or has reduced source, is an *open*
immersion onto its scheme-theoretic image.

This is `AlgebraicGeometry.isOpenImmersion_toImage`; the disjunctive hypothesis is not an
instance, so it is passed explicitly, and in Stacks 089J its left branch is taken, the
complement of the diagonals in a fibre power of a quasi-compact chart being quasi-compact. -/
theorem isOpenImmersion_toSchemeImageObj (h : V ⟶ T)
    (himm : _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map h))
    (hq : QuasiCompact ((BigFppfOver.toScheme B S hS).map h) ∨
      IsReduced ((BigFppfOver.toScheme B S hS).obj V)) :
    _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (toSchemeImageObj B S hS h)) := by
  rw [toSchemeImageObj_toScheme]
  have _ := himm
  exact isOpenImmersion_toImage ((BigFppfOver.toScheme B S hS).map h) hq

end AlgebraicGeometry.Space

end
