module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Thin

/-!
# Every functor out of a thin category preserves equalizers

In a thin category the two arrows of a parallel pair are equal, so the identity of the source is
an equalizer of them (`CategoryTheory.Limits.isLimitIdFork`). Any functor carries that equalizer
to the identity fork of the two equal image arrows, which is again an equalizer. So every functor
out of a thin category, for instance out of the category of opens of a topological space,
preserves equalizers.

## Main results

* `CategoryTheory.Limits.preservesLimitsOfShape_walkingParallelPair_of_isThin`: a functor out of a
  thin category preserves equalizers.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [Quiver.IsThin C]

/-- **Every functor out of a thin category preserves equalizers.** The two arrows of a parallel
pair in a thin category are equal, so the identity fork is an equalizer, and its image under any
functor is the identity fork of the two equal image arrows. -/
theorem preservesLimitsOfShape_walkingParallelPair_of_isThin (F : C ⥤ D) :
    PreservesLimitsOfShape WalkingParallelPair F where
  preservesLimit {K} := by
    have h : K.map WalkingParallelPairHom.left = K.map WalkingParallelPairHom.right :=
      Subsingleton.elim _ _
    have : PreservesLimit (parallelPair (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right)) F :=
      preservesLimit_of_preserves_limit_cone (isLimitIdFork h)
        ((isLimitMapConeForkEquiv F _).symm
          (Fork.IsLimit.mk _ (fun s ↦ s.ι) (fun s ↦ by simp)
            (fun s m hm ↦ by simpa using hm)))
    exact preservesLimit_of_iso_diagram F (diagramIsoParallelPair K).symm

end CategoryTheory.Limits
