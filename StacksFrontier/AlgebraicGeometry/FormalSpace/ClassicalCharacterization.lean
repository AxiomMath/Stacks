module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumClassical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentationQuotientSystem

/-!
# Classical affine formal algebraic spaces are exactly the formal spectra of admissible rings

Stacks 0AID (1) calls a McQuillan affine formal algebraic space *classical* when its associated
topological ring is admissible, and Stacks 0AIE observes that the classical affine formal
algebraic spaces are the affine formal schemes of EGA. This file proves the object half of that
correspondence, on the formal-space side: an fppf sheaf over `S` satisfying the set-theoretic
condition of Stacks 0AIS is classical exactly when it is isomorphic to the formal spectrum of
Stacks 0AIF of an admissible topological ring over `S`.

Both directions come from pieces already in the library.

Forwards, `AlgebraicGeometry.FormalSpace.IsClassical` already hands over an admissible ring `A`
presenting the sheaf in the sense of condition (1) of Stacks 0AIC, and
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation.quotientSystem` turns that
presentation into the quotient system which builds `Spf A`.

Backwards, a formal spectrum is presented by its own ring, and being presented is invariant
under isomorphism, so the sheaf is presented by `A`; the McQuillan condition is then the
implication (1) ⇒ (5) ⇒ (4) of Stacks 0AIC.

## Main results

* `AlgebraicGeometry.FormalSpace.isClassical_iff_exists_admissible_quotientSystem`:
  **Stacks 0AIE**, the objects. A sheaf satisfying the set-theoretic condition of Stacks 0AIS is
  a classical affine formal algebraic space exactly when it is isomorphic to the formal spectrum
  of an admissible topological ring over `S`.

## Implementation notes

The set-theoretic condition of Stacks 0AIS is carried as a hypothesis rather than derived. It is
implied by the left-hand side, since `AlgebraicGeometry.FormalSpace.IsClassical` contains
`AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace`, but not by the right-hand side,
which says nothing about the size of the coproduct of the quotient spectra; a caller who has the
size hypothesis of Stacks 0AIE in the form
`AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite` gets it from
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_formalSpectrum` and
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_iso`.

This is the correspondence between classical affine formal algebraic spaces and formal spectra,
not between classical affine formal algebraic spaces and affine formal *schemes*. The remaining
step, identifying the formal spectrum with the functor of points of the affine formal scheme
`Spf A`, is proved over a terminal base in
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeSpectrumComparisonIso`, as
`AlgebraicGeometry.FormalSpace.isIso_spfFormalSchemeFppfComparison`. The equivalence of
categories which Stacks 0AIE ends with is nevertheless still not available: neither of its two
categories is built in this library, and the functor of points reaches the big fppf site only
as the presheaf-valued
`AlgebraicGeometry.FormalSpace.formalSchemeFppfPresheafFunctor`, for which neither full
faithfulness nor essential surjectivity is proved. Its full faithfulness is in any case
Stacks 0AI1.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIE](https://stacks.math.columbia.edu/tag/0AIE)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AIE, the objects.** An fppf sheaf over `S` satisfying the set-theoretic condition
of Stacks 0AIS is a *classical* affine formal algebraic space in the sense of Stacks 0AID (1)
exactly when it is isomorphic to the formal spectrum of Stacks 0AIF of an admissible topological
ring over `S`.

This is the object half of the correspondence the source's remark describes, read on the
formal-space side of the bridge: the classical affine formal algebraic spaces are the `Spf A`
for `A` admissible, and nothing else. Both directions hold, with no hypothesis beyond the
set-theoretic condition, which the left-hand side implies.

The correspondence with affine formal *schemes*, and the equivalence of categories the source
concludes with, need in addition the identification of the formal spectrum with the functor of
points of `Spf A` and the full faithfulness of Stacks 0AI1; see the implementation notes of
this file. -/
@[stacks 0AIE "the objects: a sheaf is a classical affine formal algebraic space exactly when \
it is the formal spectrum of an admissible topological ring"]
theorem isClassical_iff_exists_admissible_quotientSystem {X : FppfSheaf B S hS}
    (hX : SatisfiesSetTheoreticCondition B S hS X) :
    IsClassical B S hS X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLinearTopology A A),
        TopologicalRing.IsAdmissible A ∧
          ∃ D : QuotientSystem B S hS A, Nonempty (X ≅ formalSpectrum D) := by
  constructor
  · rintro ⟨-, A, instCR, instTS, instTR, instLT, hpr, hAd⟩
    let := instCR
    let := instTS
    let := instTR
    let := instLT
    obtain ⟨D, hD⟩ := exists_quotientSystem_iso_formalSpectrum_of_isPresentingRing hpr
    exact ⟨A, instCR, instTS, instTR, instLT, hAd, D, hD⟩
  · rintro ⟨A, instCR, instTS, instTR, instLT, hAd, D, ⟨e⟩⟩
    let := instCR
    let := instTS
    let := instTR
    let := instLT
    have hwa : TopologicalRing.IsWeaklyAdmissible A :=
      TopologicalRing.isWeaklyAdmissible_of_isAdmissible hAd
    have hpr : IsPresentingRing B S hS A X :=
      isPresentingRing_of_iso B S hS A e.symm (isPresentingRing_formalSpectrum hwa D)
    exact ⟨(hasAllSurjectivePresentations_of_weakIdealColimitPresentation B S hS A hwa hX
        hpr.2.some).hasSomeSurjectivePresentation,
      A, instCR, instTS, instTR, instLT, hpr, hAd⟩

end AlgebraicGeometry.FormalSpace

end
