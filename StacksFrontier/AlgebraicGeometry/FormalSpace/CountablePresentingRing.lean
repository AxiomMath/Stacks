module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness

/-!
# Countable indexing and a countable fundamental system in a presenting ring (Stacks 0AN1)

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0AN1** identifies countable
indexing of an affine formal algebraic space `X` over `S` with the existence of a weakly
admissible topological ring `A` over `S` such that `X = Spf A` and `nhds (0 : A)` is countably
generated. `StacksFrontier/AlgebraicGeometry/FormalSpace/CountablyIndexedSpectrum.lean` proves
that in the shape `AlgebraicGeometry.FormalSpace.SpfPresentation`, where `X = Spf A` is an
isomorphism with the formal spectrum of an
`AlgebraicGeometry.FormalSpace.QuotientSystem`. Several places in the library instead need it
in the shape `AlgebraicGeometry.FormalSpace.IsPresentingRing`, where `X` is presented as the
colimit of the spectra of the quotients of `A` by its weak ideals of definition. This file is
the translation, in both directions.

The passage from a quotient system to a weak-ideal colimit presentation is
`AlgebraicGeometry.FormalSpace.QuotientSystem.weakIdealColimitPresentation`; the passage back
is `AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation.quotientSystem` together with
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation.formalSpectrumIso`.

## Main results

* `AlgebraicGeometry.FormalSpace.isPresentingRing_of_spfPresentation` and
  `AlgebraicGeometry.FormalSpace.spfPresentation_of_isPresentingRing`: the two shapes of
  "`A` presents `X`" agree.
* `AlgebraicGeometry.FormalSpace.exists_countable_isPresentingRing_of_isCountablyIndexed`:
  **Stacks 0AN1, condition (1) implies condition (2)**, in the `IsPresentingRing` shape.
* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isPresentingRing`:
  **Stacks 0AN1, condition (2) implies condition (1)**, in the `IsPresentingRing` shape.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
* [Stacks Project, Tag 0AN1](https://stacks.math.columbia.edu/tag/0AN1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Filter

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] sheaf_hasColimits

/-- A presentation of `X` as the formal spectrum of a weakly admissible topological ring over
`S` presents `X` in the sense of `AlgebraicGeometry.FormalSpace.IsPresentingRing`: the
canonical quotient system of a formal spectrum is a weak-ideal colimit presentation of it, and
that presentation transports along the identification of `X` with the formal spectrum. -/
theorem isPresentingRing_of_spfPresentation {X : FppfSheaf B S hS}
    (P : SpfPresentation B S hS X) (hP : TopologicalRing.IsWeaklyAdmissible P.ring) :
    IsPresentingRing B S hS P.ring X :=
  ⟨hP, P.iso.map fun e ↦ P.system.weakIdealColimitPresentation.ofIso e⟩

/-- A weakly admissible topological ring presenting `X` in the sense of
`AlgebraicGeometry.FormalSpace.IsPresentingRing` presents `X` as its formal spectrum. -/
def spfPresentation_of_isPresentingRing {X : FppfSheaf B S hS} {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : IsPresentingRing B S hS A X) : SpfPresentation B S hS X where
  ring := A
  system := hA.2.some.quotientSystem
  iso := ⟨hA.2.some.formalSpectrumIso⟩

/-- **Stacks 0AN1, condition (1) implies condition (2)**, in the `IsPresentingRing` shape. A
countably indexed affine formal algebraic space over `S` has a presenting weakly admissible
topological ring whose neighbourhood filter of zero is countably generated. -/
@[stacks 0AN1 "condition (1) implies condition (2), with `X = Spf A` read as the weak-ideal \
colimit presentation of Stacks 0AIC rather than as an isomorphism with a formal spectrum"]
theorem exists_countable_isPresentingRing_of_isCountablyIndexed (X : FppfSheaf B S hS)
    (hX : IsAffineFormalAlgebraicSpace B S hS X) (hXc : IsCountablyIndexed B S hS X) :
    ∃ (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : IsLinearTopology C C), IsPresentingRing B S hS C X ∧
        (nhds (0 : C)).IsCountablyGenerated := by
  obtain ⟨P, hP, hcount⟩ :=
    hasCountableWeakPresentation_of_isCountablyIndexedAffine B S hS X ⟨hX, hXc⟩
  exact ⟨P.ring, P.commRing, P.topology, P.topologicalRing, P.linearTopology,
    isPresentingRing_of_spfPresentation B S hS P hP, hcount⟩

/-- **Stacks 0AN1, condition (2) implies condition (1)**, in the `IsPresentingRing` shape. If a
weakly admissible topological ring with countably generated neighbourhood filter of zero
presents `X`, then `X` is countably indexed. -/
@[stacks 0AN1 "condition (2) implies condition (1), with `X = Spf A` read as the weak-ideal \
colimit presentation of Stacks 0AIC rather than as an isomorphism with a formal spectrum"]
theorem isCountablyIndexed_of_isPresentingRing (X : FppfSheaf B S hS) (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : IsPresentingRing B S hS A X) (hc : (nhds (0 : A)).IsCountablyGenerated) :
    IsCountablyIndexed B S hS X :=
  (isCountablyIndexedAffine_of_hasCountableWeakPresentation B S hS X
    ⟨spfPresentation_of_isPresentingRing B S hS hA, hA.1, hc⟩).2

end AlgebraicGeometry.FormalSpace

end
