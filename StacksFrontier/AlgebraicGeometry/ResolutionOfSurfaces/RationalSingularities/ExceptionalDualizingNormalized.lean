module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalDualizingGenerationCanonical
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingExistence
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomSupplement
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingExistenceSupplement
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpExceptionalDualizingSupplement

/-!
# Clauses (2) and (3) of [Stacks, Tag 0B64] under the normalization of [Stacks, Remark 0B4R]

In Situation [Stacks, Tag 0B4W] with `A` not regular, let `X` be the blowup of `Spec(A)` in the
maximal ideal, `i : E ⟶ X` its exceptional divisor and `ω_A` a dualizing module for `A`. Clauses
(2) and (3) of [Stacks, Tag 0B64] are both stated by the source for `ω_X` **the** dualizing module
of `X`, pinned by the normalization of [Stacks, Remark 0B4R]: `ω_X[2] ≅ f^!(ω_A[2])`.

This file restates the two clause reductions of
`…/RationalSingularities/BlowUpExceptionalDualizing.lean` and
`…/RationalSingularities/ExceptionalDualizingGenerationCanonical.lean` against that
normalization — `AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization` of
`…/RationalSingularities/NormalizedDualizingExistence.lean` — in place of the weaker hypotheses
they currently carry.

## Why the hypothesis has to change

Both reductions carry the isomorphism

`ecan : exceptionalDualizingModule A ω_X ≅ Stacks.Duality.dualizingSheafOverField g`

for `g : E ⟶ Spec(κ)` the structure morphism, and that single isomorphism is what clause (2) and
clause (3) are each missing. **It is not derivable from the hypotheses the two reductions
currently carry**, and the obstruction is not a missing tag:

* clause (2)'s reduction `AlgebraicGeometry.BlowUpDualizing`
  `.isZero_firstCohomology_dualizingTwist_of_exceptionalDualizingIso` assumes only that `ω_X` is
  *a* dualizing module, and
* clause (3)'s reduction
  `AlgebraicGeometry.BlowUpDualizing.epi_dualizingPullbackMap_of_isoDualizingSheaf` assumes
  `AlgebraicGeometry.RationalSingularitySituation.NormalizedDualizingModule`, the degree-zero
  duality pairing condition on a trace map.

By [Stacks, Tag 0A7F] a dualizing complex is unique only up to shift and invertible twist, so
dualizingness alone cannot single out `ω_E`; and the degree-zero condition does not either, because
the implication from the normalization of the remark to it — which is
`AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization.normalizedDualizingModule`
— **does not reverse**. The implementation notes of
`AlgebraicGeometry.RationalSingularitySituation.NormalizedDualizingModule` exhibit the failure: on
the blowup of `ℚ[x, y, z]/(xz - y²)` localized at `(x, y, z)` both `𝒪_X` and `𝒪_X(E)` satisfy the
degree-zero condition with the same trace, and
`AlgebraicGeometry.RationalSingularitySituation.isEmpty_dualizingNormalization_of_not_isIsomorphic`
says at most one isomorphism class satisfies the normalization of the remark.

So the statements below are a **strengthening of the hypothesis set towards the source's own**, not
a weakening: they ask of `ω_X` exactly what [Stacks, Remark 0B4R] asks, which is what the source's
own proof of these clauses has available, and `ecan` is a consequence of it. The two reductions
they restate are kept where they are — the `NormalizedDualizingModule` form of clause (3) is what
`…/RationalSingularities/BlowUpDualizingGenerationEquivalence.lean` compares against, and the
`IsDualizingModule` form of clause (2) is the weakest hypothesis under which that reduction holds.

## What `ecan` needs

The source's route to `ecan` propagates the normalization along the square
`AlgebraicGeometry.BlowUpDualizing.exceptionalDivisorToCentre_comp`, `i ≫ f = g ≫ j`, with
`j : Spec(κ) ⟶ Spec(A)` the closed point:

`i^!(ω_X) ≅ i^!(f^!ω_A) ≅ (f ∘ i)^!(ω_A) ≅ g^!(j^!(ω_A)) ≅ g^!(κ[2])`,

whose `H¹` is `H^{-1}(g^×(𝒪_{Spec κ}))`, which is `Stacks.Duality.dualizingSheafOverField g`. Of
its steps:

* the normalization `ω_X ≅ f^!(ω_A)` is now the hypothesis `N`;
* `i^! ∘ f^! ≅ (f ∘ i)^!` and `(g ∘ j)^! ≅ g^! ∘ j^!` are [Stacks, Tag 0ATX],
  `Stacks.Duality.twistedInverseImageCompIso`;
* `j^!(ω_A) ≅ RHom_A(κ, ω_A)` is [Stacks, Tag 0A9F] at the twisted inverse image,
  `AlgebraicGeometry.twistedInverseImage_residuePoint_isoDerivedHom`;
* `RHom_A(κ, ω_A) ≅ κ[2]` is the normalization convention of [Stacks, Tag 0A7M] at the shift
  `-dim(A) = -2`, `Dualizing.isNormalizedDualizingComplex_single_neg_localRingDimension`.

The last two of these are now spliced, as
`AlgebraicGeometry.RationalSingularitySituation`
`.nonempty_twistedInverseImage_residuePoint_iso_single` of
`…/RationalSingularities/ClosedPointNormalizedDualizing.lean`: the model crossing between
[Stacks, Tag 0A7M], stated at `CategoryTheory.HasDerivedCategory.standard`, and
[Stacks, Tag 0A9F], stated at the locally small model
`StacksDraft.ModuleCat.hasDerivedCategory`, is `Dualizing.AnyModel.derivedHomModelIso`, and the
`IsCohenMacaulayLocalRing A` that pins the normalizing shift is discharged in the situation by
`AlgebraicGeometry.RationalSingularitySituation.isCohenMacaulayLocalRing`.

Both of the remaining steps are now in place. [Stacks, Tag 0ATX] across the square is spliced
with the reading at the closed point in `AlgebraicGeometry.RationalSingularitySituation`
`.nonempty_homologyOne_twistedInverseImage_iso_dualizingSheaf_of_dualizingNormalization` of
`…/RationalSingularities/ExceptionalDualizingSheafNormalized.lean`. And the identification of
`exceptionalDualizingModule` — `H¹` of derived sheaf Hom at the standard model — with `H¹` of
the [Stacks, Tag 0A9E] right adjoint at `i`, which is the locally small model, follows from
[Stacks, Tag 0A9X] restated at that model as
`Stacks.Duality.isDerivedSheafHomRightAdjoint_twistedInverseImage` of
`…/Duality/ClosedImmersionRightAdjointLocallySmall.lean`, which *produces* the right adjoint
instead of taking it as a parameter the way
`Stacks.Duality.isDerivedSheafHomRightAdjointAtModel_of_pseudoCoherent` does at the standard model,
where the `HasCoproducts` of Brown representability fails and no parameter could be produced.
The two together give `ecan` as `AlgebraicGeometry.BlowUpDualizing`
`.nonempty_exceptionalDualizingModule_iso_dualizingSheafOverField` of
`…/Duality/ExceptionalDualizingSheafIdentification.lean`.

No `@[stacks]` attribute is attached to either statement below, both of which still take `ecan`
as an explicit isomorphism rather than producing it. Clause (2) is registered on
`…isZero_firstCohomology_dualizingTwist_of_isDualizingRingModule` of
`…/Duality/ExceptionalDualizingSheafIdentification.lean`, where `ecan` is supplied, and
clause (3) on
`AlgebraicGeometry.BlowUpDualizing.epi_dualizingPullbackMap_of_normalized` of
`…/RationalSingularities/BlowUpDualizingGeneration.lean`, which still takes the global generation
of [Stacks, Tag 0B5H].

## References

* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.Cohomology.FormalFunctions (cohomologyDeltaFunctor cohomologyDeltaFunctor_functor)

universe u

namespace AlgebraicGeometry.BlowUpDualizing

variable (S : RationalSingularitySituation.{u})

/-- **The conclusion of clause (2) of [Stacks, Tag 0B64] for `ω_X` normalized in the sense of
[Stacks, Remark 0B4R]**, granted the one isomorphism `ecan`.

This is `isZero_firstCohomology_dualizingTwist_of_exceptionalDualizingIso` with its
`IsDualizingModule` hypothesis replaced by the normalization `N`. -/
public theorem isZero_firstCohomology_dualizingTwist_of_dualizingNormalization
    (ωA : ModuleCat.{u} S.A) (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).DualizingNormalization ωA ωX)
    (ecan : exceptionalDualizingModule S.A ωX ≅
      Stacks.Duality.dualizingSheafOverField
        (X := (cohenMacaulayCurveSituationExceptionalDivisor S).X)
        (cohenMacaulayCurveSituationExceptionalDivisor S).f)
    (n : ℕ) :
    IsZero (((cohomologyDeltaFunctor (blowUpScheme S.A)).functor 1).obj
      (schemeTwist S.A ωX n)) := by
  let : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
    isLocallyNoetherian_blowUpScheme S.A
  exact isZero_firstCohomology_dualizingTwist_of_exceptionalDualizingIso S ωX N.isDualizing ecan n

/-- **Clause (3) of [Stacks, Tag 0B64] for `ω_X` normalized in the sense of
[Stacks, Remark 0B4R]**, granted the two isomorphisms `ecan` and `e0E32`.

This is `AlgebraicGeometry.BlowUpDualizing.epi_dualizingPullbackMap_of_isoDualizingSheaf` with its
`AlgebraicGeometry.RationalSingularitySituation.NormalizedDualizingModule` hypothesis replaced by
the normalization of the remark, which implies it by
`AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization.normalizedDualizingModule`
and is strictly stronger; the conclusion is therefore read at the trace that implication
produces, `S.normalizationTrace ω_A ω_X N.normalizedIso.inv`. -/
public theorem epi_dualizingPullbackMap_of_dualizingNormalization
    (hnot : ¬ IsRegularLocalRing S.A) (ωA : ModuleCat.{u} S.A)
    (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).DualizingNormalization ωA ωX)
    (ecan : exceptionalDualizingModule S.A ωX ≅
      Stacks.Duality.dualizingSheafOverField
        (X := (cohenMacaulayCurveSituationExceptionalDivisor S).X)
        (cohenMacaulayCurveSituationExceptionalDivisor S).f)
    (e0E32 : (Scheme.Modules.pullback
          (cohenMacaulayCurveSituationExceptionalDivisor S).algebraicClosureProj).obj
          (Stacks.Duality.dualizingSheafOverField
            (X := (cohenMacaulayCurveSituationExceptionalDivisor S).X)
            (cohenMacaulayCurveSituationExceptionalDivisor S).f) ≅
        Stacks.Duality.dualizingSheafOverField
          (X := (cohenMacaulayCurveSituationExceptionalDivisor S).algebraicClosure.X)
          (cohenMacaulayCurveSituationExceptionalDivisor S).algebraicClosure.f) :
    letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
      isLocallyNoetherian_blowUpScheme S.A
    Epi ((rationalSingularitySituationBlowUp S).dualizingPullbackMap ωA hωA ωX N.isDualizing
      ((rationalSingularitySituationBlowUp S).dualizingTraceSequenceOfNormalized
        (RationalSingularitySituation.DualizingNormalization.normalizedDualizingModule
          (rationalSingularitySituationBlowUp S) N))) := by
  let : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
    isLocallyNoetherian_blowUpScheme S.A
  exact epi_dualizingPullbackMap_of_isoDualizingSheaf S hnot ωA hωA ωX
    (RationalSingularitySituation.DualizingNormalization.normalizedDualizingModule
      (rationalSingularitySituationBlowUp S) N) ecan e0E32

end AlgebraicGeometry.BlowUpDualizing

end
