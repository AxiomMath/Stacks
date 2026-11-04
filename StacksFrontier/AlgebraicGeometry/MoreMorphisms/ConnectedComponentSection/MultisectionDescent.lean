module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.SectionedLocusBaseChange

/-!
# Invariance of the sectioned locus under the relation of a multisection

Let `f : X ⟶ Y` be a morphism, `g : Z ⟶ Y` a multisection with a lift `σ : Z ⟶ X`, and `X⁰`
the locus of fibrewise connected components of `X ×_Y Z ⟶ Z` met by the tautological section.
Descending `X⁰` along the first projection `X ×_Y Z ⟶ X` requires it to be invariant under the
canonical relation `(X ×_Y Z) ×_X (X ×_Y Z)`. This file proves that invariance over any locus
in the base on which the two tautological sections of the base change along `Z ×_Y Z ⟶ Y`
select the same fibrewise connected component.

## Main results

* `AlgebraicGeometry.ConnectedComponentSection.locus_compat_of_cross_agree` is that invariance.

## Implementation notes

The relation is compared with the base change along `Z ×_Y Z ⟶ Y` through
`AlgebraicGeometry.ConnectedComponentSection.exists_base_change_maps`, which presents the two
comparison maps by
their universal properties rather than as `CategoryTheory.Limits.pullback.map` applied to
specific commutativity proofs. The proof then only rewrites with hypotheses about opaque
morphisms, which keeps the rewrites from having to match proof terms inside a
`CategoryTheory.Limits.pullback.map`.

## References

* [Stacks Project, Tag 057I](https://stacks.math.columbia.edu/tag/057I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.ConnectedComponentSection

/-- Over a set `V` on which the two tautological sections of the base change of `f` along
`Z ×_Y Z ⟶ Y` select the same fibrewise connected component, the sectioned locus of
`X ×_Y Z ⟶ Z` is invariant under the canonical relation of `X ×_Y Z ⟶ X`. -/
theorem locus_compat_of_cross_agree {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) (σ : Z ⟶ X)
    (hσ : σ ≫ f = g)
    (hk₀ : (pullback.fst g g ≫ σ) ≫ f = pullback.fst g g ≫ g)
    (hk₁ : (pullback.snd g g ≫ σ) ≫ f = pullback.fst g g ≫ g)
    (V : Set Y)
    (hagree : ∀ a : ↥(pullback f (pullback.fst g g ≫ g)),
      (pullback.fst g g ≫ g) ((pullback.snd f (pullback.fst g g ≫ g)) a) ∈ V →
        (a ∈ (sectionedPullback f (pullback.fst g g ≫ g) (pullback.fst g g ≫ σ) hk₀).locus ↔
          a ∈ (sectionedPullback f (pullback.fst g g ≫ g) (pullback.snd g g ≫ σ) hk₁).locus))
    (r : ↥(pullback (pullback.fst f g) (pullback.fst f g)))
    (hr : (pullback.fst f g ≫ f)
      (pullback.fst (pullback.fst f g) (pullback.fst f g) r) ∈ V) :
    (pullback.fst (pullback.fst f g) (pullback.fst f g) r ∈
        (sectionedPullback f g σ hσ).locus ↔
      pullback.snd (pullback.fst f g) (pullback.fst f g) r ∈
        (sectionedPullback f g σ hσ).locus) := by
  obtain ⟨m₀, m₁, hm₀, hm₀', hm₁, hm₁', t, ht₀, ht₁⟩ := exists_base_change_maps f g
  have hbase₀ := sectionedPullback_locus_eq_preimage f g σ hσ (pullback.fst g g)
    (pullback.fst g g ≫ g) hk₀ m₀ hm₀ hm₀'
  have hbase₁ := sectionedPullback_locus_eq_preimage f g σ hσ (pullback.snd g g)
    (pullback.fst g g ≫ g) hk₁ m₁ hm₁ hm₁'
  have hmor : t ≫ (pullback.snd f (pullback.fst g g ≫ g) ≫ (pullback.fst g g ≫ g)) =
      pullback.fst (pullback.fst f g) (pullback.fst f g) ≫ (pullback.fst f g ≫ f) :=
    calc t ≫ (pullback.snd f (pullback.fst g g ≫ g) ≫ (pullback.fst g g ≫ g))
        = t ≫ (pullback.fst f (pullback.fst g g ≫ g) ≫ f) := by
          rw [pullback.condition (f := f) (g := pullback.fst g g ≫ g)]
      _ = t ≫ ((m₀ ≫ pullback.fst f g) ≫ f) := by rw [hm₀']
      _ = (t ≫ m₀) ≫ (pullback.fst f g ≫ f) := by simp only [Category.assoc]
      _ = pullback.fst (pullback.fst f g) (pullback.fst f g) ≫ (pullback.fst f g ≫ f) := by
          rw [ht₀]
  have hbasept : (pullback.fst g g ≫ g)
      ((pullback.snd f (pullback.fst g g ≫ g)) (t r)) ∈ V := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hmor, Scheme.Hom.comp_apply]
    exact hr
  have hpt₀ : m₀ (t r) = pullback.fst (pullback.fst f g) (pullback.fst f g) r := by
    rw [← Scheme.Hom.comp_apply, ht₀]
  have hpt₁ : m₁ (t r) = pullback.snd (pullback.fst f g) (pullback.fst f g) r := by
    rw [← Scheme.Hom.comp_apply, ht₁]
  rw [← hpt₀, ← hpt₁, ← Set.mem_preimage (f := m₀), ← Set.mem_preimage (f := m₁),
    ← hbase₀, ← hbase₁]
  exact hagree (t r) hbasept

end AlgebraicGeometry.ConnectedComponentSection

end
