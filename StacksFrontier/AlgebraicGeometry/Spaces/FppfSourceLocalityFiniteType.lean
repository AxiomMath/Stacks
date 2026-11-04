module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FppfSourceLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFppfSourceLocalityTransfer

/-!
# Local finite type is fppf local on the source for algebraic spaces

**Stacks 06EW** says that being locally of finite type, as a property of morphisms of algebraic
spaces over a scheme, is local on the source for the fppf topology. This module proves it, as one
application of the fppf case of **Stacks 06ER**
(`AlgebraicGeometry.Space.isLocalAtSource_fppf_of_schemes`) to local finite type of morphisms of
schemes, which is étale local on the source and target (**Stacks 04R3**) and — by
`AlgebraicGeometry.LocallyOfFiniteType.isLocalAtSource_fppfPrecoverage`, the content of
**Stacks 036O** — local on the source for the fppf topology of schemes.

The fppf statement does not follow from the smooth one already available as
`AlgebraicGeometry.Space.isLocallyOfFiniteType_isLocalAtSource_smooth`: a smooth covering is an
fppf covering and not conversely, so fppf source locality is the stronger assertion and
`CategoryTheory.MorphismProperty.IsLocalAtSource.of_le` runs the wrong way. The fppf statement is
what a covering obtained by base change of a flat morphism locally of finite presentation
supplies, and the smooth statement is not.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_isLocalAtSource_fppf`: **Stacks 06EW**.

## Implementation notes

The declaration is registered `@[stacks 06EW]`, a **Chapter 74** result. The registration is a
complete one: Stacks 06EW is a single assertion and this is its statement.

The statement does not follow from the smooth one already available as
`AlgebraicGeometry.Space.isLocallyOfFiniteType_isLocalAtSource_smooth`, which is why it is proved
separately; see the introduction.

## References

* [Stacks Project, Tag 036O](https://stacks.math.columbia.edu/tag/036O)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 06ER](https://stacks.math.columbia.edu/tag/06ER)
* [Stacks Project, Tag 06EW](https://stacks.math.columbia.edu/tag/06EW)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06EW.** Being locally of finite type, as a property of morphisms of algebraic spaces
over `S`, is local on the source for the fppf topology. -/
@[stacks 06EW]
instance isLocallyOfFiniteType_isLocalAtSource_fppf :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        IsLocallyOfFiniteType B S hS f.hom)
      (Topology.precoverage.{u, v} .fppf B S hS) :=
  isLocalAtSource_fppf_of_schemes B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget

end AlgebraicGeometry.Space

end
