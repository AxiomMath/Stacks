module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # The index categories of a functor are almost directed

Let `u : C ⥤ D` be a functor and `V : D` an object. If `C` has fibre products and equalizers and
`u` preserves them, then in the opposite of the comma category `StructuredArrow V u` every span
can be completed to a commutative square and every parallel pair can be coequalized.

## Main results

* `CategoryTheory.structuredArrow_op_span_and_parallelPair_completion`: `(StructuredArrow V u)ᵒᵖ`
  has the span completion and coequalizer properties.

## References

* [Stacks 00X4](https://stacks.math.columbia.edu/tag/00X4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- If `u` preserves pullbacks, every cospan `x ⟶ w ⟵ y` of structured arrows can be completed to a
commutative square. -/
private lemma structuredArrow_span_completion
    (u : C ⥤ D) [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (V : D) (w x y : StructuredArrow V u) (a : x ⟶ w) (b : y ⟶ w) :
    ∃ (z : StructuredArrow V u) (c : z ⟶ x) (d : z ⟶ y), c ≫ a = d ≫ b := by
  have hlim : IsLimit (PullbackCone.mk
      (u.map (Limits.pullback.fst a.right b.right))
      (u.map (Limits.pullback.snd a.right b.right))
      (by rw [← u.map_comp, ← u.map_comp, Limits.pullback.condition])) :=
    (PullbackCone.isLimitMapConeEquiv (Limits.pullback.cone a.right b.right) u)
      (isLimitOfPreserves u (Limits.pullback.isLimit a.right b.right))
  obtain ⟨φ, h₁, h₂⟩ := PullbackCone.IsLimit.lift' hlim x.hom y.hom
    (by rw [StructuredArrow.w a, StructuredArrow.w b])
  exact ⟨StructuredArrow.mk φ,
    StructuredArrow.homMk (Limits.pullback.fst a.right b.right) h₁,
    StructuredArrow.homMk (Limits.pullback.snd a.right b.right) h₂,
    StructuredArrow.hom_ext _ _ Limits.pullback.condition⟩

/-- If `u` preserves equalizers, every parallel pair `a b : y ⟶ x` of structured arrows is
equalized by some `c : z ⟶ y`. -/
private lemma structuredArrow_parallel_pair_completion
    (u : C ⥤ D) [HasEqualizers C] [PreservesLimitsOfShape WalkingParallelPair u]
    (V : D) (x y : StructuredArrow V u) (a b : y ⟶ x) :
    ∃ (z : StructuredArrow V u) (c : z ⟶ y), c ≫ a = c ≫ b := by
  have he : equalizer.ι a.right b.right ≫ a.right = equalizer.ι a.right b.right ≫ b.right :=
    equalizer.condition a.right b.right
  obtain ⟨φE, hφE⟩ := Fork.IsLimit.lift'
    (isLimitForkMapOfIsLimit u he (equalizerIsEqualizer a.right b.right)) y.hom
    (by rw [StructuredArrow.w a, StructuredArrow.w b])
  exact ⟨StructuredArrow.mk φE,
    StructuredArrow.homMk (equalizer.ι a.right b.right) (by simpa [Fork.ofι, Fork.ι] using hφE),
    StructuredArrow.hom_ext _ _ he⟩

/-- If `C` has fibre products and equalizers and `u : C ⥤ D` preserves them, then for every
`V : D`, in `(StructuredArrow V u)ᵒᵖ` every span can be completed to a commutative square and every
parallel pair can be coequalized. -/
@[stacks 00X4]
theorem structuredArrow_op_span_and_parallelPair_completion
    (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (V : D) :
    (∀ (w x y : (StructuredArrow V u)ᵒᵖ) (a : w ⟶ x) (b : w ⟶ y),
        ∃ (z : (StructuredArrow V u)ᵒᵖ) (c : x ⟶ z) (d : y ⟶ z),
          a ≫ c = b ≫ d) ∧
    (∀ (x y : (StructuredArrow V u)ᵒᵖ) (a b : x ⟶ y),
        ∃ (z : (StructuredArrow V u)ᵒᵖ) (c : y ⟶ z),
          a ≫ c = b ≫ c) := by
  refine ⟨fun w x y a b ↦ ?_, fun x y a b ↦ ?_⟩
  · obtain ⟨z, c, d, hcd⟩ :=
      structuredArrow_span_completion u V w.unop x.unop y.unop a.unop b.unop
    exact ⟨op z, c.op, d.op, Quiver.Hom.unop_inj (by simpa using hcd)⟩
  · obtain ⟨z, c, hc⟩ :=
      structuredArrow_parallel_pair_completion u V x.unop y.unop a.unop b.unop
    exact ⟨op z, c.op, Quiver.Hom.unop_inj (by simpa using hc)⟩

end CategoryTheory
