module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumTerm

/-!
# Extending a weighting by zero along a closed immersion

A weight `w : X → ℤ` on the source of a composite `j ≫ f` with `j : X ⟶ Z` a preimmersion
extends by zero to a weight on `Z`, and the extension has the same weighted fibre sum along
`f` as `w` has along `j ≫ f`: the extra points of `Z` carry weight zero, and the residue field
extension at a point of `X` is unchanged by `j`.

When `j` is a *closed* immersion the extension is again a weighting. The reason is that the
test diagrams of the weighting condition for `f` pull back to test diagrams for `j ≫ f`: the
base change of `j` along a test chart `h : U ⟶ Z` is a closed immersion, so it keeps the chart
finite over the base, and the comparison morphism into the pullback stays an open immersion
because it is itself a base change of the given one.

## Main results

* `AlgebraicGeometry.separableDegreeWeightedFiberSum_extend_of_isPreimmersion`: the weighted
  fibre sum of the extension by zero equals that of the composite.
* `AlgebraicGeometry.IsWeighting.extend_of_isClosedImmersion`: the extension by zero of a
  weighting along a closed immersion is a weighting.

## Implementation notes

The fibre sum identity is `finprod_emb_domain'` for the injective map `j`, together with
`AlgebraicGeometry.separableDegreeWeightedFiberTerm_comp_isPreimmersion` to identify the
summands at points in the image.

## References

* [Stacks Project, Tag 0F3A](https://stacks.math.columbia.edu/tag/0F3A)
* [Stacks Project, Tag 0F3B](https://stacks.math.columbia.edu/tag/0F3B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The weighted fibre sum of the extension by zero of a weight along a preimmersion is the
weighted fibre sum of the weight along the composite. -/
theorem separableDegreeWeightedFiberSum_extend_of_isPreimmersion
    {X Y Z : Scheme.{u}} (j : X ⟶ Z) [IsPreimmersion j] (f : Z ⟶ Y) (w : X → ℤ) :
    separableDegreeWeightedFiberSum f (Function.extend j w (0 : Z → ℤ)) =
      separableDegreeWeightedFiberSum (j ≫ f) w := by
  classical
  funext y
  set w' := Function.extend j w (0 : Z → ℤ) with hw'def
  have hw : w' ∘ j = w := funext (j.isEmbedding.injective.extend_apply w 0)
  rw [separableDegreeWeightedFiberSum_eq_finsum_term,
    separableDegreeWeightedFiberSum_eq_finsum_term,
    ← finsum_emb_domain' j.isEmbedding.injective
      (separableDegreeWeightedFiberTerm (j ≫ f) w y)]
  refine finsum_congr fun z ↦ ?_
  split_ifs with hz
  · calc separableDegreeWeightedFiberTerm f w' y z
        = separableDegreeWeightedFiberTerm f w' y (j (Classical.choose hz)) :=
          congrArg (separableDegreeWeightedFiberTerm f w' y) (Classical.choose_spec hz).symm
      _ = separableDegreeWeightedFiberTerm (j ≫ f) (w' ∘ j) y (Classical.choose hz) :=
          (separableDegreeWeightedFiberTerm_comp_isPreimmersion j f w' y _).symm
      _ = separableDegreeWeightedFiberTerm (j ≫ f) w y (Classical.choose hz) := by rw [hw]
  · have hwz : w' z = 0 := Function.extend_apply' w (0 : Z → ℤ) z hz
    by_cases hzy : f z = y
    · rw [separableDegreeWeightedFiberTerm_of_mem_fiber f w' hzy, hwz, zero_mul]
    · exact separableDegreeWeightedFiberTerm_of_notMem_fiber f w' hzy

/-- Restricting the extension by zero of a weight along a preimmersion to a scheme over the
target is the extension by zero of the restricted weight along the base change of the
preimmersion. -/
private lemma extend_comp_of_isPreimmersion
    {X Z U : Scheme.{u}} (j : X ⟶ Z) [IsPreimmersion j] (h : U ⟶ Z) (w : X → ℤ) :
    Function.extend j w (0 : Z → ℤ) ∘ h =
      Function.extend (pullback.snd j h) (w ∘ pullback.fst j h) (0 : U → ℤ) := by
  classical
  funext u
  by_cases hu : u ∈ Set.range (pullback.snd j h)
  · obtain ⟨x, rfl⟩ := hu
    have heq : h (pullback.snd j h x) = j (pullback.fst j h x) :=
      congrArg (fun k : pullback j h ⟶ Z ↦ k x) pullback.condition.symm
    simp only [Function.comp_apply, heq, j.isEmbedding.injective.extend_apply,
      (pullback.snd j h).isEmbedding.injective.extend_apply]
  · have hu' : h u ∉ Set.range j := by rwa [Scheme.Pullback.range_snd] at hu
    rw [Function.comp_apply, Function.extend_apply' _ _ _ hu',
      Function.extend_apply' _ _ _ hu]
    rfl

/-- The comparison morphism of a test diagram for `j ≫ f`, built from one for `f` by base
change along `j`, is itself a base change of the comparison morphism of the original diagram. -/
private lemma isPullback_lift_pullback_fst
    {X Z Y U V : Scheme.{u}} (j : X ⟶ Z) (f : Z ⟶ Y)
    (h : U ⟶ Z) (π : U ⟶ V) (g : V ⟶ Y) (comm : h ≫ f = π ≫ g)
    (comm' : pullback.fst j h ≫ (j ≫ f) = (pullback.snd j h ≫ π) ≫ g) :
    IsPullback (pullback.lift (pullback.fst j h) (pullback.snd j h ≫ π) comm')
      (pullback.snd j h)
      (pullback.map (j ≫ f) g f g j (𝟙 V) (𝟙 Y) (by simp) (by simp))
      (pullback.lift h π comm) := by
  have hs : IsPullback (pullback.fst (j ≫ f) g)
      (pullback.map (j ≫ f) g f g j (𝟙 V) (𝟙 Y) (by simp) (by simp)) j
      (pullback.fst f g) := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd f g) (v₂₂ := f) (h₃₁ := g)
    · simpa only [pullback.map, pullback.lift_snd, Category.comp_id] using
        IsPullback.of_hasPullback (j ≫ f) g
    · simp only [pullback.map, pullback.lift_fst]
    · exact IsPullback.of_hasPullback f g
  apply IsPullback.of_right (h₁₂ := pullback.fst (j ≫ f) g)
    (h₂₂ := pullback.fst f g) (v₁₃ := j)
  · simpa only [pullback.lift_fst] using IsPullback.of_hasPullback j h
  · apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd,
        Category.comp_id, pullback.lift_fst_assoc, pullback.condition]
  · exact hs

/-- **The extension by zero of a weighting along a closed immersion is a weighting.** -/
theorem IsWeighting.extend_of_isClosedImmersion
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsClosedImmersion j] {f : Z ⟶ Y} {w : X → ℤ}
    (hw : IsWeighting (j ≫ f) w) :
    IsWeighting f (Function.extend j w (0 : Z → ℤ)) := by
  intro U V h π g comm hg hU hπ
  have comm' : pullback.fst j h ≫ (j ≫ f) = (pullback.snd j h ≫ π) ≫ g := by
    rw [← Category.assoc, pullback.condition, Category.assoc, comm, Category.assoc]
  have hopen : IsOpenImmersion
      (pullback.lift (pullback.fst j h) (pullback.snd j h ≫ π) comm') :=
    MorphismProperty.of_isPullback
      (isPullback_lift_pullback_fst j f h π g comm comm').flip hU
  have := hπ
  have hfinite : IsFinite (pullback.snd j h ≫ π) := inferInstance
  have hconst := hw.isLocallyConstant (pullback.fst j h) (pullback.snd j h ≫ π) g comm'
    hg hopen hfinite
  rwa [extend_comp_of_isPreimmersion, separableDegreeWeightedFiberSum_extend_of_isPreimmersion]

end AlgebraicGeometry

end
