module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.FormalArcs.PointBlowups
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.FormalArcs.PointBlowups

/-!
# Recursion for the stalk images along a sequence of point blowups

`PointBlowupSequence.stalkImage_zero` and `PointBlowupSequence.stalkImage_succ` describe
`PointBlowupSequence.stalkImage` by recursion on the stage.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace PrimeSpectrum

universe u

namespace AlgebraicGeometry

attribute [local instance] localStepMap_isLocal

/-- The image of an initial local function at the initial stage is the function itself: the
composite map to the initial scheme is the identity there. -/
public theorem PointBlowupSequence.stalkImage_zero (s : PointBlowupSequence.{u})
    (x : (s.scheme 0).presheaf.stalk (s.point 0)) : s.stalkImage 0 x = x := by
  rw [← initialToStage_apply]
  have hzero : initialToStage s 0 = RingHom.id (localRingAt s 0) := by
    ext z
    rw [initialToStage_apply]
    simp [PointBlowupSequence.stalkImage, PointBlowupSequence.toBase,
      Scheme.Hom.stalkMap_id]
    rfl
  rw [hzero]
  rfl

/-- The image of an initial local function at stage `n + 1` is the image of its value at stage
`n` under the stalk map of the transition morphism of the sequence. -/
public theorem PointBlowupSequence.stalkImage_succ (s : PointBlowupSequence.{u}) (n : ℕ)
    (x : (s.scheme 0).presheaf.stalk (s.point 0)) :
    s.stalkImage (n + 1) x =
      ((s.stepMap n).stalkMap (s.point (n + 1))).hom
        ((s.point_step n).symm ▸ s.stalkImage n x) := by
  rw [← localStepMap_stalkImage s x n, localStepMap]
  simp [RingEquiv.cast, eqRec_eq_cast]


end AlgebraicGeometry

end
