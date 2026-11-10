module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.ClosedPointsOfProductOverField

/-!
# Points over closed points in a base change to a one-point scheme

Let `K` be a field, `X` a scheme locally of finite type over `K` and `T ⟶ Spec K` a morphism from
a scheme with one point, for instance `Spec L` for a field extension `L/K`. A point of
`T ×_K X` whose image in `X` is closed is itself closed: the fibre of `T ×_K X ⟶ X` over a closed
point `x` is `T ×_K Spec κ(x)`, which is finite over the one-point scheme `T` because `κ(x)` is
finite over `K`, hence discrete, and it is a closed subscheme of `T ×_K X`.

The proof of [Stacks, Tag 0F1H] uses this when it replaces `K` by its separable closure: the
points of `(X ×_K Y)_{K^{sep}}` lying over closed points of `X ×_K Y` are closed.

## Main results

* `AlgebraicGeometry.isClosed_singleton_of_isClosed_singleton_snd` — the statement.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A point of a base change to a one-point scheme over a closed point is closed.** Let `K` be
a field, `sX : X ⟶ Spec K` locally of finite type and `φ : T ⟶ Spec K` a morphism from a scheme
with one point. A point `w` of `T ×_K X` whose image in `X` is closed is closed. -/
theorem isClosed_singleton_of_isClosed_singleton_snd {K : Type u} [Field K] {T X : Scheme.{u}}
    [Subsingleton T] (φ : T ⟶ Spec (.of K)) (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX]
    (w : ↥(pullback φ sX)) (hw : IsClosed ({pullback.snd φ sX w} : Set X)) :
    IsClosed ({w} : Set ↥(pullback φ sX)) := by
  let x := pullback.snd φ sX w
  let ix := X.fromSpecResidueField x
  have : IsClosedImmersion ix := isClosed_singleton_iff_isClosedImmersion.mp hw
  have : IsFinite (ix ≫ sX) := isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  let m : pullback φ (ix ≫ sX) ⟶ pullback φ sX :=
    pullback.map φ (ix ≫ sX) φ sX (𝟙 T) ix (𝟙 _) (by simp) (by simp)
  have hm : IsPullback (pullback.snd φ (ix ≫ sX)) m ix (pullback.snd φ sX) := by
    refine (IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback φ sX)).flip
    rw [show m ≫ pullback.fst φ sX = pullback.fst φ (ix ≫ sX) from
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)]
    exact IsPullback.of_hasPullback φ (ix ≫ sX)
  have : IsClosedImmersion m := MorphismProperty.of_isPullback hm ‹_›
  have : IsFinite (pullback.fst φ (ix ≫ sX)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback φ (ix ≫ sX)).flip
      (inferInstanceAs (IsFinite (ix ≫ sX)))
  obtain ⟨t, htw⟩ : w ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]
    refine ⟨⟨pullback.fst φ sX w, rfl⟩, ?_⟩
    change x ∈ Set.range ix
    rw [Scheme.range_fromSpecResidueField]
    rfl
  rw [← htw]
  simpa using m.isClosedEmbedding.isClosedMap _
    (isClosed_singleton_of_isFinite_of_subsingleton (pullback.fst φ (ix ≫ sX)) t)

end AlgebraicGeometry
