module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Types
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation
public import StacksFrontier.Topology.Algebra.AdicTopology.IdealOfDefinition
public import StacksFrontier.Topology.Algebra.AdicTopology.IdealOfDefinitionSupplement

/-!
# The formal spectrum of an admissible ring is classical (Stacks 0AIE)

Let `S` be a scheme contained in a big fppf site `B` and let `A` be a topological ring over `S`,
presented by a `AlgebraicGeometry.FormalSpace.QuotientSystem`. Stacks 0AIF builds from that
datum the formal spectrum `Spf A = colim Spec (A ⧸ I)`, an affine formal algebraic space over
`S`. Stacks 0AIE observes that when `A` is *admissible* — and not merely weakly admissible —
this affine formal algebraic space is *classical* in the sense of Stacks 0AID (1).

The proof is immediate once the two descriptions of the same situation are matched up. Being
classical means being McQuillan, condition (4) of Stacks 0AIC, together with the existence of
an admissible topological ring presenting the sheaf; a quotient system presents its own formal
spectrum, by `AlgebraicGeometry.FormalSpace.QuotientSystem.weakIdealColimitPresentation`, and
McQuillan-ness of a sheaf with such a presentation is the implication (1) ⇒ (5) ⇒ (4) of
Stacks 0AIC, which the library already has. The one ring-theoretic input is that an admissible
topological ring is weakly admissible, `TopologicalRing.isWeaklyAdmissible_of_isAdmissible`.

## Main results

* `AlgebraicGeometry.FormalSpace.isPresentingRing_formalSpectrum`: a weakly admissible
  topological ring with a quotient system is a presenting ring of its own formal spectrum, in
  the sense of condition (1) of Stacks 0AIC.
* `AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_formalSpectrum`: a formal
  spectrum is McQuillan, condition (4) of Stacks 0AIC.
* `AlgebraicGeometry.FormalSpace.isClassical_formalSpectrum_of_satisfiesSetTheoreticCondition`
  and `AlgebraicGeometry.FormalSpace.isClassical_formalSpectrum`: **Stacks 0AIE**, the formal
  spectrum of an *admissible* topological ring is a classical affine formal algebraic space.

## Implementation notes

*Which `Spf A`.* The two developments in this library both write `Spf A`. On the formal-scheme
side `AlgebraicGeometry.spfFormalScheme` is an object of `AlgebraicGeometry.FormalScheme`, a
locally topologically ringed space in the sense of EGA, and its functor of points is a presheaf
of `Type u` on all schemes. On the formal-space side
`AlgebraicGeometry.FormalSpace.formalSpectrum` is an object of
`AlgebraicGeometry.FormalSpace.FppfSheaf B S hS`, a sheaf of `Type (u + 1)` on the big fppf site
of `S`. The predicates of Stacks 0AID are about the latter, so that is what this file is about;
the identification of the two, which is the first half of Stacks 0AIE, is the subject of
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeSpectrumComparison`.

*The set-theoretic side condition.* `AlgebraicGeometry.FormalSpace.IsClassical` is a predicate
on affine formal algebraic spaces, and `AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace`
carries the set-theoretic condition of Stacks 0AIS. It is therefore part of the conclusion, not
an extra hypothesis, but it has to be supplied; the two forms below differ only in how.
`AlgebraicGeometry.FormalSpace.isClassical_formalSpectrum` asks for the size hypothesis in the
form the source states it, namely that the coproduct of the quotient spectra lies in the chosen
big fppf site, and is the direct reading of Stacks 0AIE. The other form asks for the
set-theoretic condition itself, and is what a caller who already has it should use.

*Direction.* Everything here goes from the ring to the sheaf: admissibility of `A` gives
classicality of `Spf A`. The converse — that the presenting ring of a classical affine formal
algebraic space is admissible — is not available. The equivalence of the five conditions of
Stacks 0AIC is itself proved in this library, so that is not the obstacle; what is missing is a
choice of presenting ring as a function of the sheaf, 0AIC giving only that one exists and is
unique up to isomorphism of topological rings. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Types`.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIE](https://stacks.math.columbia.edu/tag/0AIE)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- **Condition (1) of Stacks 0AIC for a formal spectrum.** A weakly admissible topological
ring carrying a quotient system over `S` is a presenting ring of the formal spectrum it builds:
that formal spectrum is by construction the colimit of the spectra of the quotients of the ring
by its weak ideals of definition. -/
theorem isPresentingRing_formalSpectrum (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) : IsPresentingRing B S hS A (formalSpectrum D) :=
  ⟨hA, ⟨D.weakIdealColimitPresentation⟩⟩

/-- **Condition (4) of Stacks 0AIC for a formal spectrum.** The formal spectrum of a weakly
admissible topological ring over `S` is McQuillan: it is an affine formal algebraic space and
some presentation of it by affine thickenings has surjective section-ring projections. This is
condition (5) for a formal spectrum, restricted to one presentation. -/
theorem hasSomeSurjectivePresentation_formalSpectrum
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (hX : SatisfiesSetTheoreticCondition B S hS (formalSpectrum D)) :
    HasSomeSurjectivePresentation B S hS (formalSpectrum D) :=
  (hasAllSurjectivePresentations_formalSpectrum hA D hX).hasSomeSurjectivePresentation

/-- **Stacks 0AIE**, with the set-theoretic condition of Stacks 0AIS supplied directly. The
formal spectrum of an *admissible* topological ring over `S` is a classical affine formal
algebraic space in the sense of Stacks 0AID (1): it is McQuillan, and the admissible ring it is
built from presents it.

Admissibility is used twice: through
`TopologicalRing.isWeaklyAdmissible_of_isAdmissible` to see that the formal spectrum is an
affine formal algebraic space at all, and then as the second clause of Stacks 0AID (1). -/
theorem isClassical_formalSpectrum_of_satisfiesSetTheoreticCondition
    (hA : TopologicalRing.IsAdmissible A) (D : QuotientSystem B S hS A)
    (hX : SatisfiesSetTheoreticCondition B S hS (formalSpectrum D)) :
    IsClassical B S hS (formalSpectrum D) :=
  ⟨hasSomeSurjectivePresentation_formalSpectrum
      (TopologicalRing.isWeaklyAdmissible_of_isAdmissible hA) D hX,
    A, ‹CommRing A›, ‹TopologicalSpace A›, ‹IsTopologicalRing A›, ‹IsLinearTopology A A›,
    isPresentingRing_formalSpectrum (TopologicalRing.isWeaklyAdmissible_of_isAdmissible hA) D,
    hA⟩

/-- **Stacks 0AIE.** Let `A` be an admissible topological ring over `S`. If the coproduct of the
spectra of the quotients of `A` by its weak ideals of definition lies in the chosen big fppf
site, then the formal spectrum `Spf A` is a *classical* affine formal algebraic space over `S`
in the sense of Stacks 0AID (1).

This is the second conclusion of the source's remark, for the object its colimit formula
produces. The size hypothesis is the source's own: the source needs the coproduct of the
quotient spectra to lie in the chosen big fppf site, which is what supplies the representable
atlas demanded by the set-theoretic condition of Stacks 0AIS. The source's colimit runs over the
ideals of definition of `A` and this one over its weak ideals of definition; the two agree,
because in a pre-admissible ring the ideals of definition are cofinal below the weak ideals of
definition (`TopologicalRing.exists_isIdealOfDefinition_le_of_isWeakIdealOfDefinition`).

Only this direction holds: see the implementation notes of this file. -/
@[stacks 0AIE "the formal spectrum of an admissible topological ring is a classical affine \
formal algebraic space"]
theorem isClassical_formalSpectrum (hA : TopologicalRing.IsAdmissible A)
    (D : QuotientSystem B S hS A) (hB : D.HasLargeSite) :
    IsClassical B S hS (formalSpectrum D) :=
  isClassical_formalSpectrum_of_satisfiesSetTheoreticCondition hA D
    (isAffineFormalAlgebraicSpace_formalSpectrum
      (TopologicalRing.isWeaklyAdmissible_of_isAdmissible hA) D hB).1

end AlgebraicGeometry.FormalSpace

end
