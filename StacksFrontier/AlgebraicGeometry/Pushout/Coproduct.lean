module

public import StacksFrontier.AlgebraicGeometry.Pushout.Gluing

/-!
# The coproduct covers a pushout

Let `i : Z ⟶ X` be a closed immersion and `j : Z ⟶ Y` an integral morphism satisfying the
fibrewise affineness condition of [Stacks Project, Tag 0ECI], so that the pushout `Y ⨿_Z X`
exists as a scheme.  The two canonical maps into the pushout jointly cover it, and both are
closed, so the induced morphism from the disjoint union `Y ⨿ X` to the pushout is surjective
and universally closed.

## Main definitions

* `AlgebraicGeometry.pushoutCoprodDesc` is the canonical morphism `Y ⨿ X ⟶ Y ⨿_Z X` out of the
  coproduct.

## Main results

* `AlgebraicGeometry.pushoutCoprodDesc_surjective`: the canonical morphism is surjective.
* `AlgebraicGeometry.pushoutCoprodDesc_universallyClosed`: it is universally closed.

## Implementation notes

Surjectivity is the only content, and it is proved by ruling out a point outside the union of
the two images.  That union is closed, since the map from `Y` is a closed immersion and the map
from `X` is integral and hence universally closed; so a point outside it has an affine open
neighbourhood `U` disjoint from both images.  Both `U`-sections of the two direct images then
vanish, and `AlgebraicGeometry.pushoutStructureSheaf_isPullback` exhibits `Γ(Y ⨿_Z X, U)` as a
fibre product of rings over them, forcing it to be subsingleton — impossible for a nonempty
affine open.

Surjectivity and universal closedness are stated separately, as instances, so that either can
be used directly by typeclass search.

## References

* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})

/-- The canonical morphism `Y ⨿ X ⟶ Y ⨿_Z X` from the coproduct of the two schemes to their
scheme-theoretic pushout. -/
noncomputable abbrev pushoutCoprodDesc : s.Y ⨿ s.X ⟶ pushoutScheme s :=
  coprod.desc (pushoutInr s) (pushoutInl s)

/-- The two canonical maps into the pushout jointly cover it: the union of their images is
everything. -/
private lemma range_pushoutInr_union_range_pushoutInl :
    Set.range (pushoutInr s) ∪ Set.range (pushoutInl s) = Set.univ := by
  by_contra h
  obtain ⟨p, hp⟩ : ∃ p : pushoutScheme s,
      p ∉ Set.range (pushoutInr s) ∪ Set.range (pushoutInl s) := by
    simpa [Set.eq_univ_iff_forall] using h
  let O : (pushoutScheme s).Opens :=
    ⟨(Set.range (pushoutInr s) ∪ Set.range (pushoutInl s))ᶜ,
      ((pushoutInr s).isClosedMap.isClosed_range.union
        (pushoutInl s).isClosedMap.isClosed_range).isOpen_compl⟩
  obtain ⟨_, ⟨U : (pushoutScheme s).Opens, hU, rfl⟩, hpU, hUO⟩ :=
    (pushoutScheme s).isBasis_affineOpens.exists_subset_of_mem_open (show p ∈ O from hp) O.2
  have hsub : ∀ {W : Scheme.{u}} (f : W ⟶ pushoutScheme s),
      Set.range f ⊆ Set.range (pushoutInr s) ∪ Set.range (pushoutInl s) →
        Subsingleton Γ(W, f ⁻¹ᵁ U) := fun f hf ↦ by
    have : f ⁻¹ᵁ U = ⊥ := by
      ext w
      exact ⟨fun hw ↦ (hUO hw) (hf ⟨w, rfl⟩), by simp⟩
    rw [this]
    infer_instance
  have := hsub (pushoutInr s) (Set.subset_union_left)
  have := hsub (pushoutInl s) (Set.subset_union_right)
  have : Subsingleton Γ(pushoutScheme s, U) := ⟨fun x y ↦ by
    apply PullbackCone.IsLimit.type_ext
      ((pushoutStructureSheaf_isPullback s U).map (forget CommRingCat)).isLimit <;>
      apply Subsingleton.elim⟩
  have : Nonempty U := ⟨⟨p, hpU⟩⟩
  exact not_nontrivial Γ(pushoutScheme s, U) inferInstance

/-- The canonical morphism from the coproduct of the two schemes to their pushout is
surjective. -/
instance pushoutCoprodDesc_surjective : Surjective (pushoutCoprodDesc s) := by
  refine ⟨fun p ↦ ?_⟩
  obtain ⟨y, rfl⟩ | ⟨x, rfl⟩ : p ∈ Set.range (pushoutInr s) ∪ Set.range (pushoutInl s) :=
    (range_pushoutInr_union_range_pushoutInl s).symm ▸ Set.mem_univ p
  · refine ⟨(coprod.inl : s.Y ⟶ s.Y ⨿ s.X) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, coprod.inl_desc]
  · refine ⟨(coprod.inr : s.X ⟶ s.Y ⨿ s.X) x, ?_⟩
    rw [← Scheme.Hom.comp_apply, coprod.inr_desc]

/-- The canonical morphism from the coproduct of the two schemes to their pushout is universally
closed. -/
instance pushoutCoprodDesc_universallyClosed :
    UniversallyClosed (pushoutCoprodDesc s) := inferInstance

end AlgebraicGeometry
