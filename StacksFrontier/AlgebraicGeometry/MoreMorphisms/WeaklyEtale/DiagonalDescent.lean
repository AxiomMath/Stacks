module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Descent

/-!
# Descent of flatness of the relative diagonal

A morphism of schemes is *weakly étale* when both it and its relative diagonal are flat. This
file proves the descent step for the second condition: given `X ⟶ Y ⟶ Z` with `X ⟶ Y` flat and
surjective, flatness of the diagonal of `X ⟶ Z` implies flatness of the diagonal of `Y ⟶ Z`.
The relative diagonals are `CategoryTheory.Limits.pullback.diagonal`.

## Main results

* `AlgebraicGeometry.flat_diagonal_of_surjective_flat`: flatness of the relative diagonal descends
  along a surjective flat morphism.

## References

* [Stacks Project, Tag 094V](https://stacks.math.columbia.edu/tag/094V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Flatness of the relative diagonal descends along a surjective flat morphism. -/
@[stacks 094V]
theorem flat_diagonal_of_surjective_flat {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Surjective f]
    [Flat (pullback.diagonal (f ≫ g))] :
    Flat (pullback.diagonal g) := by
  let a : pullback (f ≫ g) (f ≫ g) ⟶ pullback g (f ≫ g) :=
    pullback.lift (pullback.fst (f ≫ g) (f ≫ g) ≫ f)
      (pullback.snd (f ≫ g) (f ≫ g)) (by
        simpa [Category.assoc] using pullback.condition (f := f ≫ g) (g := f ≫ g))
  let b : pullback g (f ≫ g) ⟶ pullback g g :=
    pullback.lift (pullback.fst g (f ≫ g))
      (pullback.snd g (f ≫ g) ≫ f) (by
        simpa [Category.assoc] using pullback.condition (f := g) (g := f ≫ g))
  have ha₁ : a ≫ pullback.fst g (f ≫ g) = pullback.fst (f ≫ g) (f ≫ g) ≫ f := by
    simp [a, pullback.lift_fst]
  have ha₂ : a ≫ pullback.snd g (f ≫ g) = pullback.snd (f ≫ g) (f ≫ g) := by
    simp [a, pullback.lift_snd]
  have hb₁ : b ≫ pullback.fst g g = pullback.fst g (f ≫ g) := by
    simp [b, pullback.lift_fst]
  have hb₂ : b ≫ pullback.snd g g = pullback.snd g (f ≫ g) ≫ f := by
    simp [b, pullback.lift_snd]
  let liftA := fun s : PullbackCone f (pullback.fst g (f ≫ g)) =>
    pullback.lift (f := f ≫ g) (g := f ≫ g) s.fst (s.snd ≫ pullback.snd g (f ≫ g))
      (by simp [reassoc_of% s.condition, pullback.condition])
  have liftA_fst (s : PullbackCone f (pullback.fst g (f ≫ g))) :
      liftA s ≫ pullback.fst (f ≫ g) (f ≫ g) = s.fst :=
    pullback.lift_fst _ _ _
  have liftA_snd (s : PullbackCone f (pullback.fst g (f ≫ g))) :
      liftA s ≫ pullback.snd (f ≫ g) (f ≫ g) = s.snd ≫ pullback.snd g (f ≫ g) :=
    pullback.lift_snd _ _ _
  have hlimA : IsLimit (PullbackCone.mk (pullback.fst (f ≫ g) (f ≫ g)) a ha₁.symm) :=
    PullbackCone.IsLimit.mk ha₁.symm liftA liftA_fst
      (by intro s; apply pullback.hom_ext
          · rw [Category.assoc, ha₁, ← Category.assoc, liftA_fst]; exact s.condition
          · simp [Category.assoc, ha₂, liftA_snd])
      (by intro s m hm₁ hm₂; apply pullback.hom_ext
          · simpa [liftA_fst] using hm₁
          · simpa [Category.assoc, ha₂, liftA_snd] using
              congrArg (fun k => k ≫ pullback.snd g (f ≫ g)) hm₂)
  have hsqA : IsPullback (pullback.fst (f ≫ g) (f ≫ g)) a f
      (pullback.fst g (f ≫ g)) := IsPullback.of_isLimit hlimA
  let liftB := fun s : PullbackCone f (pullback.snd g g) =>
    pullback.lift (f := g) (g := f ≫ g) (s.snd ≫ pullback.fst g g) s.fst
      (by simp [reassoc_of% s.condition, pullback.condition])
  have liftB_fst (s : PullbackCone f (pullback.snd g g)) :
      liftB s ≫ pullback.fst g (f ≫ g) = s.snd ≫ pullback.fst g g :=
    pullback.lift_fst _ _ _
  have liftB_snd (s : PullbackCone f (pullback.snd g g)) :
      liftB s ≫ pullback.snd g (f ≫ g) = s.fst :=
    pullback.lift_snd _ _ _
  have hlimB : IsLimit (PullbackCone.mk (pullback.snd g (f ≫ g)) b hb₂.symm) :=
    PullbackCone.IsLimit.mk hb₂.symm liftB liftB_snd
      (by intro s; apply pullback.hom_ext
          · simp [Category.assoc, hb₁, liftB_fst]
          · rw [Category.assoc, hb₂, ← Category.assoc, liftB_snd]; exact s.condition)
      (by intro s m hm₁ hm₂; apply pullback.hom_ext
          · simpa [Category.assoc, hb₁, liftB_fst] using
              congrArg (fun k => k ≫ pullback.fst g g) hm₂
          · simpa [liftB_snd] using hm₁)
  have hsqB : IsPullback (pullback.snd g (f ≫ g)) b f
      (pullback.snd g g) := IsPullback.of_isLimit hlimB
  have : Flat a := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqA inferInstance
  have : Flat b := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqB inferInstance
  have heq : pullback.diagonal (f ≫ g) ≫ a ≫ b = f ≫ pullback.diagonal g := by
    apply pullback.hom_ext
    · simp [Category.assoc, hb₁, ha₁]
    · simp only [Category.assoc, hb₂]
      rw [← Category.assoc a (pullback.snd g (f ≫ g)) f, ha₂]
      simp
  have : Flat (f ≫ pullback.diagonal g) := by
    rw [← heq]
    infer_instance
  exact flat_of_comp_of_surjective_flat f (pullback.diagonal g)

end AlgebraicGeometry

end
