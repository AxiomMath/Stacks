module

public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectColimit

/-!
# Stacks 0DKW, reduced to its pending inputs

Stacks 0DKW (`AlgebraicGeometry.Space.RelativeDescentSituation.RelativelyPerfectColimit`) is
the conjunction of five clauses.  This file proves the first two, that the transition and
comparison functors preserve relative perfectness, from Stacks 0DKT, and assembles the tag from
those and the two remaining halves, stated as named propositions:

* `AlgebraicGeometry.Space.RelativeDescentSituation.RelativelyPerfectFullyFaithful`: fullness
  and faithfulness of the comparison out of the colimit.  In the source this is Stacks 0DKV
  applied to the situation reindexed at a stage (Stacks 0DKV is not yet proved here); the
  translation of Stacks 0DKV, stated for
  `AlgebraicGeometry.Space.RelativeDescentSituation.HomDescent` with the derived pullback
  `smallEtaleDerivedModulePullback`, into this clause is internal and in progress.
* `AlgebraicGeometry.Space.RelativeDescentSituation.RelativelyPerfectEssentiallySurjective`:
  essential surjectivity.  In the source this is the induction of Stacks 08GP with the glueing of
  Stacks 08HB, reducing to the affine case, which is Stacks 0DI8 read through Stacks 0DKQ (not yet
  proved here); it is internal and in progress.

Both halves, like the tag itself, are stated for a situation whose limit is a limit of schemes
(`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`): without it the faithfulness
clause fails, and the source's affine case, which reads the limit as a limit of schemes, is not
available.

Nothing here is registered.

## Main results

* `AlgebraicGeometry.Space.RelativeDescentSituation.isStagePerfect_transition` and
  `isLimitPerfect_projection`: the first two clauses of Stacks 0DKW, from Stacks 0DKT.
* `AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectColimit_of_held`:
  Stacks 0DKW from Stacks 0DKT and the two named halves.

## References

* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 0DKT](https://stacks.math.columbia.edu/tag/0DKT)
* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 0DKQ](https://stacks.math.columbia.edu/tag/0DKQ)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Tag 0DI8](https://stacks.math.columbia.edu/tag/0DI8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space.RelativeDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-- **Clause (1) of Stacks 0DKW, from Stacks 0DKT** (`h0DKT`, not yet proved here):
the transition functors `Lf_{ji}^*` carry `Yᵢ`-perfect objects to `Yⱼ`-perfect objects. -/
theorem isStagePerfect_transition (h0DKT : RelativelyPerfectBaseChangeStable B S hS)
    {i j : D.LaterIndex} (h : i.1 ≤ j.1) (E : derivedModules B S hS (D.stageSource i))
    (hE : D.IsStagePerfect i E) :
    D.IsStagePerfect j (((smallEtaleDerivedPullbackData B S hS).pull
      (D.sourceTransition h)).obj E) :=
  h0DKT (D.stageStructure i) (D.targetTransition h) (D.sourceTransition h)
    (D.stageStructure j)
    (D.isPullback_sourceTransition h) (D.isFlat_stageStructure i)
    (D.isLocallyOfFinitePresentation_stageStructure i) (D.isFlat_stageStructure j)
    (D.isLocallyOfFinitePresentation_stageStructure j) E hE

/-- **Clause (2) of Stacks 0DKW, from Stacks 0DKT** (`h0DKT`, not yet proved here):
the comparison functors `Lfᵢ^*` carry `Yᵢ`-perfect objects to `Y`-perfect objects. -/
theorem isLimitPerfect_projection (h0DKT : RelativelyPerfectBaseChangeStable B S hS)
    (i : D.LaterIndex) (E : derivedModules B S hS (D.stageSource i))
    (hE : D.IsStagePerfect i E) :
    D.IsLimitPerfect (((smallEtaleDerivedPullbackData B S hS).pull
      (D.sourceProjection i)).obj E) :=
  h0DKT (D.stageStructure i) (D.targetProjection i) (D.sourceProjection i) D.limitStructure
    (D.isPullback_sourceProjection i) (D.isFlat_stageStructure i)
    (D.isLocallyOfFinitePresentation_stageStructure i) D.isFlat_limitStructure
    D.isLocallyOfFinitePresentation_limitStructure E hE

/-- **Fullness and faithfulness in Stacks 0DKW** (clauses (4) and (5)).  Internal, in progress:
in the source it is Stacks 0DKV (not yet proved here) for the situation reindexed at
the stage `i`, applied to two `Yᵢ`-perfect objects, which are pseudo-coherent and of locally
finite Tor dimension over `Yᵢ`.  It is stated for a situation whose limit is a limit of schemes
(`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`); without it faithfulness
fails. -/
def RelativelyPerfectFullyFaithful : Prop :=
  D.IsSchemeLimit →
  (∀ (i : D.LaterIndex) (E E' : derivedModules B S hS (D.stageSource i)),
      D.IsStagePerfect i E → D.IsStagePerfect i E' →
      ∀ φ : ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceProjection i)).obj E ⟶
          ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceProjection i)).obj E',
        ∃ (j : D.LaterIndex) (h : i.1 ≤ j.1)
          (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceTransition h)).obj E ⟶
            ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceTransition h)).obj E'),
          φ = Functor.conjHom (D.projectionComparison h) ψ) ∧
    (∀ (i : D.LaterIndex) (E E' : derivedModules B S hS (D.stageSource i)),
      D.IsStagePerfect i E → D.IsStagePerfect i E' →
      ∀ ψ ψ' : E ⟶ E',
        ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceProjection i)).map ψ =
            ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceProjection i)).map ψ' →
          ∃ (j : D.LaterIndex) (h : i.1 ≤ j.1),
            ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceTransition h)).map ψ =
              ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceTransition h)).map ψ')

/-- **Essential surjectivity in Stacks 0DKW** (clause (3)).  Internal, in progress: in the
source it is the induction of Stacks 08GP over the quasi-compact quasi-separated étale objects
of `Y₀` and then of `X₀`, whose glueing step is Stacks 08HB with an overlap isomorphism descended
by full faithfulness, and whose affine case is Stacks 0DI8 read through Stacks 0DKQ (not yet proved
here).  It is stated for a situation whose limit is a limit of schemes
(`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`), which is what the affine case
of the source's induction reads. -/
def RelativelyPerfectEssentiallySurjective : Prop :=
  D.IsSchemeLimit →
  ∀ E : derivedModules B S hS D.limitSource, D.IsLimitPerfect E →
    ∃ (i : D.LaterIndex) (Eᵢ : derivedModules B S hS (D.stageSource i)),
      D.IsStagePerfect i Eᵢ ∧
        Nonempty (((smallEtaleDerivedPullbackData B S hS).pull
          (D.sourceProjection i)).obj Eᵢ ≅ E)

/-- **Stacks 0DKW, from its pending inputs**: Stacks 0DKT (`h0DKT`, not yet proved here), fullness
and faithfulness (`hff`, from Stacks 0DKV, not yet proved here; internal
translation in progress) and essential surjectivity (`hes`, internal, in progress). -/
theorem relativelyPerfectColimit_of_held (h0DKT : RelativelyPerfectBaseChangeStable B S hS)
    (hff : D.RelativelyPerfectFullyFaithful) (hes : D.RelativelyPerfectEssentiallySurjective) :
    D.RelativelyPerfectColimit := fun hD =>
  ⟨fun h E hE => D.isStagePerfect_transition h0DKT h E hE,
    fun i E hE => D.isLimitPerfect_projection h0DKT i E hE, hes hD, (hff hD).1, (hff hD).2⟩

end AlgebraicGeometry.Space.RelativeDescentSituation

end
