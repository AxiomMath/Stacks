module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction

/-!
# The projective compactification of the chart lies in the big fppf site

The proof of Stacks 089J replaces the affine étale chart `W` of the algebraic space by an open
subscheme of a scheme `Y` which is H-projective over the base, and then forms the `d`-fold fibre
power of `Y` over the base. That fibre power is taken as an *object of the big fppf site* by
`AlgebraicGeometry.Space.overProdObj`, whose factors are objects of the site; so `Y` itself has to
be shown to satisfy the site's size cutoff. This file does that.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.contains_of_isProjectiveMorphism`: a scheme H-projective over the
  underlying scheme of an object of the big fppf category over `S` is contained in the site.

## What is and is not proved

Stacks 089J is **not** proved here, and no declaration in this file carries a Stacks attribute:
Stacks 000R (5) is already carried by
`AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact`, which is applied
through `AlgebraicGeometry.Space.contains_of_locallyOfFiniteType_of_quasiCompact`, and Stacks
01WC — an H-projective morphism is proper — by
`AlgebraicGeometry.isProper_of_isProjectiveMorphism`.

Nothing is said here about the compactification itself; the statement that an affine scheme
locally of finite type over `Spec R` is an open subscheme of a scheme projective over `Spec R` is
`AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isAffine_toSpec`.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A scheme H-projective over the underlying scheme of an object of the big fppf category over
`S` is contained in the site.** An H-projective morphism is proper by Stacks 01WC, hence
quasi-compact and locally of finite type, so this is
`AlgebraicGeometry.Space.contains_of_locallyOfFiniteType_of_quasiCompact`, that is Stacks
000R (5).

This is what puts the projective compactification `Y` of the étale chart of Stacks 089J into the
site, so that `AlgebraicGeometry.Space.overProdObj` may be applied to it. Taking the object of
the site to be the base itself — whose underlying scheme is `S` — gives the case the proof of
Stacks 089J uses, with `S = Spec A`. -/
theorem contains_of_isProjectiveMorphism {D : BigFppfOver B S hS} {Y : Scheme.{u}}
    (p : Y ⟶ (BigFppfOver.toScheme B S hS).obj D) (hp : IsProjectiveMorphism p) :
    B.Contains Y :=
  have := isProper_of_isProjectiveMorphism p hp
  contains_of_locallyOfFiniteType_of_quasiCompact B S hS p

end AlgebraicGeometry.Space

end
