module

public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# A quasi-compact scheme with a smooth surjective cover of finite type over `Y` is bounded by `Y`

Let `g : Z ⟶ A` be smooth and surjective with `A` quasi-compact, and `h : Z ⟶ Y` locally of
finite type. Then `size A ≤ 2 ^ 2 ^ size Y`: finitely many affine opens of `Z` already cover `A`
because `g` is open, their union is quasi-compact and locally of finite type over `Y`, hence of
size at most `size Y` by **Stacks 04T7**, and it covers `A` by a flat surjective morphism.

This bounds the ambient spaces of the smooth lifts of affine étale opens in the proof of
Stacks 0CJU uniformly, by the size of a chart of the target stack.

## Main results

* `AlgebraicGeometry.Scheme.size_le_of_smooth_surjective_of_locallyOfFiniteType`: the bound.
-/

@[expose] public section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry

/-- **A quasi-compact scheme with a smooth surjective cover locally of finite type over `Y` is
bounded by `Y`.** -/
theorem Scheme.size_le_of_smooth_surjective_of_locallyOfFiniteType {Z A Y : Scheme.{u}}
    (g : Z ⟶ A) (h : Z ⟶ Y) [Smooth g] [Surjective g] [LocallyOfFiniteType h]
    [CompactSpace A] : A.size ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ Y.size := by
  classical
  have hcover : ∀ a : A, ∃ U : Z.affineOpens, a ∈ g.base '' (U : Set Z) := by
    intro a
    obtain ⟨z, rfl⟩ := g.surjective a
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
    exact ⟨⟨U, hU⟩, z, hzU, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : Z.affineOpens => g.base '' (U : Set Z)) (fun U => g.isOpenMap _ U.1.isOpen)
    (fun a _ => Set.mem_iUnion.2 (hcover a))
  let V : Z.Opens := ⨆ U ∈ t, (U : Z.Opens)
  have hVc : IsCompact (V : Set Z) := by
    rw [show (V : Set Z) = ⋃ U ∈ t, (U : Set Z) by simp [V]]
    exact t.isCompact_biUnion fun U _ => U.2.isCompact
  have : CompactSpace V := isCompact_iff_compactSpace.1 hVc
  have : Surjective (V.ι ≫ g) := by
    refine ⟨fun a => ?_⟩
    obtain ⟨U, hUt, z, hz, rfl⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ a))
    have hzV : z ∈ V := by
      simp only [V, TopologicalSpace.Opens.mem_iSup]
      exact ⟨U, hUt, hz⟩
    exact ⟨⟨z, hzV⟩, rfl⟩
  exact (Scheme.size_le_two_pow_two_pow_size_of_flat_of_surjective (V.ι ≫ g)).trans
    (power_le_power_left two_ne_zero
      (power_le_power_left two_ne_zero (Scheme.size_le_of_locallyOfFiniteType (V.ι ≫ h))))

end AlgebraicGeometry
