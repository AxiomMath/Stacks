module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeLimitApproximationOfLimitBridges
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOverIntegersTerminal
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DominantChartLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DominantNoetherianApproximation
import all StacksFrontier.AlgebraicGeometry.Spaces.RelativeApproximation

/-!
# Relative approximation from Noetherian approximations of any size

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `Spec ℤ`, and let `X` and `Y` have
Noetherian approximations, by quasi-separated algebraic spaces of finite type over `Spec ℤ`
with affine transition morphisms, over directed index sets of any size. Then `f` has a relative
approximation, the conclusion of **Stacks 0GS3**, whose two component limits are the given ones.

## Main results

* `Space.exists_relativeApproximation_isLimit_fst_snd_of_hasNoetherianApproximation`: the
  relative approximation of `f` from two Noetherian approximations with no bound on the size of
  their index sets.

## Implementation notes

The argument is the alignment of the two approximations in the proof of Stacks 0GS3,
`AlgebraicGeometry.Space.hasRelativeApproximation_of_isQuasiCompactSpace`, run on the systems of
scheme-theoretic images of the projections of the two approximations. Their projections are
scheme-theoretically dominant, so their chart systems have limit bridges with no size condition,
which is what the limit criteria of Stacks 0CP4 need.

## References

* [Stacks Project, Tag 0GS3](https://stacks.math.columbia.edu/tag/0GS3)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] RelativeApproximation.preorder RelativeApproximation.nonempty
  RelativeApproximation.isDirected

/-! ### The alignment chain of the relative approximation

The stage systems and the alignment of two of them are those of
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeApproximation`, which need of a system only that
the limits of its base changes along affine points lie in the site; the names below are aliases
of them. -/

private alias BridgedStageSystem := StageSystem
private alias BridgedStageSystem.mk := StageSystem.mk
private alias BridgedStageSystem.I := StageSystem.I
private alias BridgedStageSystem.preorder := StageSystem.preorder
private alias BridgedStageSystem.nonempty := StageSystem.nonempty
private alias BridgedStageSystem.isDirected := StageSystem.isDirected
private alias BridgedStageSystem.diagram := StageSystem.diagram
private alias BridgedStageSystem.isAlgebraicSpace := StageSystem.isAlgebraicSpace
private alias BridgedStageSystem.isQuasiCompactSpace := StageSystem.isQuasiCompactSpace
private alias BridgedStageSystem.isAbsolutelyQuasiSeparated :=
  StageSystem.isAbsolutelyQuasiSeparated
private alias BridgedStageSystem.isAffineHom_map := StageSystem.isAffineHom_map
private alias BridgedStageSystem.isFiniteTypeOverIntegers := StageSystem.isFiniteTypeOverIntegers
private alias BridgedStageSystem.finitePresentation := StageSystem.finitePresentation
private alias BridgedStageSystem.π := StageSystem.π
private alias BridgedStageSystem.isLimit := StageSystem.isLimit
private alias exists_compatible_hom_of_bridges := exists_compatible_hom
private alias exists_eq_after_transition_of_bridges := exists_eq_after_transition
private alias BridgedCompatibleStage := CompatibleStage
private alias BridgedCompatibleStage.mk := CompatibleStage.mk
private alias BridgedCompatibleStage.source := CompatibleStage.source
private alias BridgedCompatibleStage.target := CompatibleStage.target
private alias BridgedCompatibleStage.hom := CompatibleStage.hom
private alias BridgedCompatibleStage.compatible := CompatibleStage.compatible
private alias BridgedCompatibleStage.Refines := CompatibleStage.Refines
private alias bridgedCompatibleStage_nonempty := compatibleStage_nonempty
private alias bridgedCompatibleStage_commonRefinement := compatibleStage_commonRefinement
private alias bridgedRefinesSourceMap := refinesSourceMap
private alias bridgedRefinesTargetMap := refinesTargetMap
private alias bridgedRefinesSquare := refinesSquare
private alias bridgedCompatibleDiagram := compatibleDiagram
private alias bridgedSourceProjection := compatibleSourceProjection
private alias bridgedTargetProjection := compatibleTargetProjection
private alias bridgedSourceProjection_initial := compatibleSourceProjection_initial
private alias bridgedTargetProjection_initial := compatibleTargetProjection_initial
private alias relativeApproximationOfBridgedStageSystems := relativeApproximationOfStageSystems

/-- A Noetherian approximation with scheme-theoretically dominant projections, of any size,
repackaged with the two consequences of the finite-type condition and with the limits in the
site of its base changes along affine points, which its chart systems' limit bridges along étale
charts supply with no size condition. -/
private noncomputable def bridgedStageSystemOfDominant (B : BigFppfSite.{u})
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X)
    (hdom : ∀ j, letI := A.preorder;
      schemeTheoreticImageSubfunctor B (⊤_ Scheme.{u}) hZ (A.π.app j) = ⊤) :
    StageSystem B hZ X :=
  letI := A.preorder
  letI := A.nonempty
  letI := A.isDirected
  letI : IsCofiltered (A.I)ᵒᵖ := A.isCofiltered_op
  have hqc (j : (A.I)ᵒᵖ) : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (A.diagram.obj j) :=
    isQuasiCompactSpace_of_isQuasiCompact_viewOverIntegers B hZ (A.isFiniteTypeOverIntegers j).2
  { I := A.I
    diagram := A.diagram
    isAlgebraicSpace := A.isAlgebraicSpace
    isQuasiCompactSpace := hqc
    isAbsolutelyQuasiSeparated := A.isAbsolutelyQuasiSeparated
    isAffineHom_map := A.isAffineHom_map
    isFiniteTypeOverIntegers := A.isFiniteTypeOverIntegers
    finitePresentation := fun j =>
      isLocallyOfFinitePresentation_terminal_of_isLocallyOfFiniteType_viewOverIntegers B hZ
        (A.isAlgebraicSpace j) (A.isFiniteTypeOverIntegers j).1
    π := A.π
    isLimit := A.isLimit
    siteContainsBaseChangeLimits := siteContainsBaseChangeLimits_of_hasChartLimitBridges B _ hZ hZ
      A.diagram (Cone.mk X A.π) A.isLimit (A.hasChartLimitBridges_of_dominant hX hdom)
      A.isAlgebraicSpace hqc A.isAbsolutelyQuasiSeparated A.isAffineHom_map hX }

section BridgedCompatible

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}

/-- **Stacks 0GS3 from two Noetherian approximations of any size, with the two component
limits.** Given Noetherian approximations of the source and of the target of `f`, with no bound
on the size of their index sets, `f` has a relative approximation whose limiting cone has
limiting images under the two projections of the arrow category.

The approximations are first replaced by the systems of scheme-theoretic images of their
projections, whose chart systems have limit bridges with no size condition; that is what the
limit criteria of Stacks 0CP4 need, and without it they fail for systems too large for the
site. -/
theorem exists_relativeApproximation_isLimit_fst_snd_of_hasNoetherianApproximation (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X) (hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y)
    (hXA : HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X)
    (hYA : HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ Y) :
    ∃ R : RelativeApproximation B hZ f,
      Nonempty (IsLimit ((Comma.fst (𝟭 _) (𝟭 _)).mapCone (Cone.mk (Arrow.mk f) R.π))) ∧
        Nonempty (IsLimit ((Comma.snd (𝟭 _) (𝟭 _)).mapCone (Cone.mk (Arrow.mk f) R.π))) := by
  classical
  obtain ⟨A, hA⟩ := exists_noetherianApproximation_dominant hX hXA
  obtain ⟨C, hC⟩ := exists_noetherianApproximation_dominant hY hYA
  let SX := bridgedStageSystemOfDominant B hZ hX A hA
  let SY := bridgedStageSystemOfDominant B hZ hY C hC
  let hne : Nonempty (CompatibleStage f SX SY) := compatibleStage_nonempty f hX SX SY
  let hdir : IsDirected (CompatibleStage f SX SY) (· ≤ ·) :=
    ⟨fun a b => compatibleStage_commonRefinement hX a b⟩
  let : (compatibleSourceProjection f SX SY).Initial :=
    compatibleSourceProjection_initial f hX SX SY
  let : (compatibleTargetProjection f SX SY).Initial :=
    compatibleTargetProjection_initial f hX SX SY
  exact ⟨relativeApproximationOfStageSystems f hX SX SY,
    ⟨(Functor.Initial.isLimitWhiskerEquiv (compatibleSourceProjection f SX SY)
      (Cone.mk X SX.π)).symm SX.isLimit⟩,
    ⟨(Functor.Initial.isLimitWhiskerEquiv (compatibleTargetProjection f SX SY)
      (Cone.mk Y SY.π)).symm SY.isLimit⟩⟩

end BridgedCompatible

end AlgebraicGeometry.Space

end
