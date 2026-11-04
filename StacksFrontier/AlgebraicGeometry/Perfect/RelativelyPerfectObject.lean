module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimension
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Objects perfect relative to a base scheme, over a family of certificates

For a morphism of schemes `f : X ⟶ S` which is flat and locally of finite presentation, an object
`E` of `D(𝒪_X)` is *perfect relative to `S`*, or *`S`-perfect*, when it is pseudo-coherent and,
viewed over `f^{-1}𝒪_S`, locally has finite Tor dimension. That is Stacks 0DI0, and it is
`AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect` in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObjectCanonical`.

This file states the generalisation in which the second clause is read against an arbitrary
family of certificates for the derived tensor product, one on each open subspace of the
inverse-image ringed space. The two clauses are already available:
`AlgebraicGeometry.RingedSpace.IsPseudoCoherent` is part (3) of Stacks 08CB, and
`AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension` is part (3) of Stacks 08CG, applied
to the image of `E` under `AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction`, restriction of
scalars along `f^{-1}𝒪_S ⟶ 𝒪_X` on derived categories.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo` is relative perfectness over a family of
  certificates.

## Implementation notes

As everywhere in `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring`, the derived
tensor product on the inverse-image ringed space is a parameter here — a family of certificates
indexed by the opens of that space, since part (3) of Stacks 08CG restricts to an open covering.
The underived half of a certificate is free data, so at a general family this predicate is weaker
than Stacks 0DI0: at
`AlgebraicGeometry.RingedSpace.firstProjectionFamily` it degenerates to pseudo-coherence together
with local boundedness of the cohomology. It is Stacks 0DI0 exactly on the families pinned by
`AlgebraicGeometry.Scheme.Hom.IsGenuineRelativeTensorFamily`, by
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_iff_isRelativelyPerfect`.

Flatness and local finite presentation of `f` are the standing hypotheses under which the source
makes this definition. They are carried as instance arguments and are not used by either clause.

## References

* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Definition 20.47.1 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
  [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [∀ U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    HasDerivedCategory.{d'}
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding))]

/-- **A generalisation of Stacks 0DI0.** An object `E` of `D(𝒪_X)` is perfect relative to `S`
when it is pseudo-coherent and, after restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X`, locally
has finite Tor dimension on the inverse-image ringed space `(X, f^{-1}𝒪_S)`.

The derived tensor product is read off the family of certificates `D`, one on each open subspace
of the inverse-image ringed space, as in part (3) of Stacks 08CG. Since the underived half of a
certificate is free data, this is weaker than Stacks 0DI0 at a general `D`, and it is
Stacks 0DI0 — `AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect` — exactly when `D` is pinned to
the tensor product of sheaves of modules; see
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_iff_isRelativelyPerfect`. -/
@[stacks 0DHZ "the notion of a relatively perfect object, for a morphism flat and \
locally of finite presentation, generalised to an arbitrary family of certificates",
  sga "6 III 4.1" "flat, l.f.p. case"]
public def IsPerfectRelativeTo [Flat f] [LocallyOfFinitePresentation f]
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) : Prop :=
  RingedSpace.IsPseudoCoherent E ∧
    RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace f.base) D
      ((derivedScalarRestriction f).obj E)

end AlgebraicGeometry.Scheme.Hom

end
