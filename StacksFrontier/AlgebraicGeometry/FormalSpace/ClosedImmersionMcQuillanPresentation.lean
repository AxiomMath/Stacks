module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentationQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SurjectivePresentationRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFromRepresentable

/-!
# The homomorphism presenting a closed immersion into a McQuillan affine formal algebraic space

Let `S` be a scheme and let `f : Y ⟶ X` be a closed immersion of formal algebraic spaces over
`S` whose target is a McQuillan affine formal algebraic space, say `X = Spf A` for a weakly
admissible topological ring `A` over `S`. **Stacks 0ANQ** asserts that `Y` is McQuillan as well,
that `f` arises from a continuous homomorphism `A ⟶ C` of weakly admissible topological rings
over `S`, and that this homomorphism is taut, has closed kernel and has dense image.

`StacksFrontier/AlgebraicGeometry/FormalSpace/ClosedImmersionMcQuillan.lean` proves the McQuillan
property of the source, the closed kernel and the dense image. This file supplies the two
remaining assertions: that the closed immersion arises from a continuous homomorphism at all,
and that this homomorphism is taut.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_formalSpectrumMap_of_isClosedImmersion`:
  **Stacks 0ANQ**, a closed immersion into a formal spectrum arises from a continuous
  homomorphism of weakly admissible topological rings over `S`.
* `AlgebraicGeometry.FormalSpace.isTaut_of_isClosedImmersion_formalSpectrumMap`:
  **Stacks 0ANQ**, that homomorphism is taut.

## Implementation notes

The source writes `Y = Spf C` and reads off the homomorphism from the full faithfulness of
`Spf`. Here the McQuillan property of the source,
`AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_of_isClosedImmersion`, is fed to
the implication (4) ⟹ (1) of **Stacks 0AIC**,
`AlgebraicGeometry.FormalSpace.exists_isPresentingRing_of_hasSomeSurjectivePresentation`, which
produces a weakly admissible topological ring `C` presenting `Y` by the quotients by its weak
ideals of definition; that presentation contains a quotient system in the sense of
**Stacks 0AIF** and identifies `Y` with its formal spectrum
(`AlgebraicGeometry.FormalSpace.exists_quotientSystem_iso_formalSpectrum_of_isPresentingRing`).
Full faithfulness of `Spf`, **Stacks 0AN0**, then turns the resulting morphism of formal spectra
into the continuous homomorphism `A ⟶ C`, uniquely.

Tautness is the implication (2) ⟹ (3) of **Stacks 0AN5**: a closed immersion of fppf sheaves is
relatively representable, which is exactly condition (2) for the morphism of formal spectra, so
`AlgebraicGeometry.FormalSpace.isTaut_of_isClosedImmersionInto_formalSpectrumMap` applies with no
further hypothesis. Nothing of the source's countability or affineness is used.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0ANP](https://stacks.math.columbia.edu/tag/0ANP)
* [Stacks Project, Tag 0ANQ](https://stacks.math.columbia.edu/tag/0ANQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

section Taut

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

end Taut

section Presentation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

attribute [local instance] sheaf_hasColimits

end Presentation

end AlgebraicGeometry.FormalSpace

end
