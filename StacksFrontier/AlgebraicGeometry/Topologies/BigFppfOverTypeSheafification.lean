module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness

/-!
# Sheafification of presheaves of types on the big fppf site over a scheme

The objects of the big fppf category over a scheme `S` in universe `u` form a type in
universe `u + 1`, with homomorphisms in universe `u`. Mathlib's size-matched instances for
`Type`-valued presheaves on a site `C : Type u'` with `Category.{v'} C` are stated for
`Type (max u' v')`, which for this site is `Type (u + 1)` and not `Type u`. So neither
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective (Type u)` nor
`CategoryTheory.HasSheafify _ (Type u)` is available by instance synthesis, even though the
functor of points of a scheme over `S` takes values in `Type u`.

Both hold all the same, because the big fppf category over `S` is essentially small: it is a
slice of a category of schemes below a size cutoff, which
`AlgebraicGeometry.essentiallySmall_schemeBelow` shows is essentially small. On a small model
the two universes agree and Mathlib's instances fire, and
`CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall` transport them
back along `CategoryTheory.equivSmallModel`.

These are `theorem`s rather than `instance`s, as the `AddCommGrpCat`-valued statements
`AlgebraicGeometry.BigFppfOver.hasWeakSheafify` and
`AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective` already in the library are: they are
claims about particular sites, and the general forms are the two Mathlib lemmas named above.
Make them local instances where they are needed.

## Main results

* `AlgebraicGeometry.BigFppfOver.hasSheafify_type`: presheaves of types in the universe of the
  sections sheafify on the big fppf site over `S`.
* `AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective_type`: on that site, the morphisms of
  such presheaves which sheafification inverts are exactly the locally bijective ones.
* `AlgebraicGeometry.BigFppfOver.hasSheafify_type_over` and
  `AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective_type_over`: the same two statements for
  the localization of the site at one of its objects.
* `AlgebraicGeometry.BigFppfOver.hasSheafify_type_baseOver` and
  `AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective_type_baseOver`: the same two statements
  for each of the five localized topologies on the big fppf category over `S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Presheaves of types in the universe of the sections sheafify on the big fppf site over `S`.
This is not the size-matched instance — the objects of the site lie one universe above the
sections — and it holds because the site is essentially small. -/
theorem hasSheafify_type : HasSheafify (topology B S hS) (Type u) :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- On the big fppf site over `S`, a morphism of presheaves of types in the universe of the
sections is inverted by sheafification exactly when it is locally bijective. As for
`AlgebraicGeometry.BigFppfOver.hasSheafify_type` this is not the size-matched instance, and it
holds because the site is essentially small. -/
instance wEqualsLocallyBijective_type :
    (topology B S hS).WEqualsLocallyBijective (Type u) :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- `AlgebraicGeometry.BigFppfOver.hasSheafify_type` for the localization of the site at an
object. -/
theorem hasSheafify_type_over (X : BigFppfOver B S hS) :
    HasSheafify ((topology B S hS).over X) (Type u) :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- `AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective_type` for the localization of the
site at an object. -/
theorem wEqualsLocallyBijective_type_over (X : BigFppfOver B S hS) :
    ((topology B S hS).over X).WEqualsLocallyBijective (Type u) :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- `AlgebraicGeometry.BigFppfOver.hasSheafify_type` for each of the five localized topologies
on the big fppf category over `S`. -/
theorem hasSheafify_type_baseOver (τ : SiteKind) :
    HasSheafify (baseOverTopology B S hS τ) (Type u) :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- `AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective_type` for each of the five localized
topologies on the big fppf category over `S`. -/
theorem wEqualsLocallyBijective_type_baseOver (τ : SiteKind) :
    (baseOverTopology B S hS τ).WEqualsLocallyBijective (Type u) :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end AlgebraicGeometry.BigFppfOver

end
