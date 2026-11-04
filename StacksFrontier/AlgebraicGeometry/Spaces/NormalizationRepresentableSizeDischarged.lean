module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.GenericPointsSize
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction

/-!
# The normalization of a representable algebraic space, with no size hypothesis

`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction` constructs the normalization of
the algebraic space represented by an object of the big fppf site,
`AlgebraicGeometry.Space.NormalizationData.ofRepresentable`, under the hypothesis that the site
contains the normalization scheme of the representing scheme.  This file discharges that
hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.NormalizationData.ofRepresentableOfFiniteIrreducibleComponents` is
  that construction with the containment hypothesis discharged, so it carries no size
  hypothesis.

## Implementation notes

Containment in the big fppf site, `AlgebraicGeometry.BigFppfSite.Contains`, is a bound on
`AlgebraicGeometry.Scheme.size`, and `AlgebraicGeometry.Scheme.size_normalizationScheme_le`
bounds the size of a normalization by the size of the scheme it normalizes, so the
normalization scheme of the representing scheme is in the site outright.  The bound reduces the
absolute case to the relative one — the missing clause of Tag 000R, proved in
`StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Size` — together with a count of the
generic points of `X`.

The same bound is proved again, as a statement about objects of the site, by
`AlgebraicGeometry.Space.contains_normalizationScheme`
(`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSiteObject`); the bound is applied directly
here instead.

**No tag.** This is the existence of the normalization in the representable case only, which is
neither one of the four numbered parts of Tag 07U4 nor the existence statement in the generality
the tag asks for; that is `AlgebraicGeometry.Space.nonempty_normalizationData`
(`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceConstruction`).

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace NormalizationData

/-- **The normalization of a representable algebraic space, with no size hypothesis.** This is
`AlgebraicGeometry.Space.NormalizationData.ofRepresentable` with its containment hypothesis
discharged: containment in the big fppf site, `AlgebraicGeometry.BigFppfSite.Contains`, is a
bound on `AlgebraicGeometry.Scheme.size`, and
`AlgebraicGeometry.Scheme.size_normalizationScheme_le` bounds the size of a normalization by the
size of the scheme it normalizes, so the normalization scheme of the representing scheme is in
the site outright.

The two are not independent constructions: this one is the instance of `ofRepresentable` at that
bound, so every property proved of `ofRepresentable` holds of it. -/
def ofRepresentableOfFiniteIrreducibleComponents (X : BigFppfOver B S hS)
    (hX : ∀ V : ((BigFppfOver.toScheme B S hS).obj X).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj X)) →
        (irreducibleComponents V).Finite) :
    NormalizationData B S hS (yoneda.obj X) :=
  ofRepresentable B S hS X hX ((Scheme.size_normalizationScheme_le _ hX).trans_lt X.left.property)

end NormalizationData

end AlgebraicGeometry.Space

end
