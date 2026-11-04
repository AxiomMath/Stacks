module

public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport

/-!
# Unions, preimages and intersections of quasi-compact open subspaces

Let `X` be an algebraic space over a scheme `S`.  This file records three elementary facts about
quasi-compact open subspaces, read through the order isomorphism of Stacks 03BZ between open
subspaces of `X` and open subsets of `|X|` and through Stacks 03E4.

* The union of two open subspaces is an open subspace whose point set is the union of the two
  point sets; it is quasi-compact when both are.
* The point set of the preimage of an open subspace along a morphism is the preimage of its point
  set (Stacks 03H4, `AlgebraicGeometry.Space.range_pointsMap_preimage_ι` in
  `StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform`); the preimage of a quasi-compact open
  subspace along a quasi-compact morphism is quasi-compact (Stacks 0EMK).
* In particular, on a quasi-separated algebraic space the preimage in one quasi-compact open of
  another — their intersection — is quasi-compact.

## Main results

* `AlgebraicGeometry.Space.isCompact_range_of_isQuasiCompactSpace`
* `AlgebraicGeometry.Space.exists_openSubspace_range_eq_union`
* `AlgebraicGeometry.Space.isQuasiCompactSpace_preimage_of_isQuasiCompact`

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0EMK](https://stacks.math.columbia.edu/tag/0EMK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point set of a quasi-compact open subspace is a compact subset of the point space. -/
theorem isCompact_range_of_isQuasiCompactSpace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {G : Subfunctor X} (hG : IsOpenSubspace B S hS G)
    (hGqc : IsQuasiCompactSpace B S hS G.toFunctor) :
    IsCompact (Set.range (pointsMap B S hS G.toFunctor G.ι)) := by
  have := compactSpace_points_of_isQuasiCompactSpace B S hS hG.1 hGqc
  exact isCompact_range (continuous_pointsMap B S hS G.ι)

/-- **The union of two open subspaces.**  There is an open subspace containing both whose point
set is the union of their point sets. -/
theorem exists_openSubspace_range_eq_union {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {G₁ G₂ : Subfunctor X} (hG₁ : IsOpenSubspace B S hS G₁)
    (hG₂ : IsOpenSubspace B S hS G₂) :
    ∃ (G : Subfunctor X) (_hG : IsOpenSubspace B S hS G), G₁ ≤ G ∧ G₂ ≤ G ∧
      Set.range (pointsMap B S hS G.toFunctor G.ι) =
        Set.range (pointsMap B S hS G₁.toFunctor G₁.ι) ∪
          Set.range (pointsMap B S hS G₂.toFunctor G₂.ι) := by
  let e := openSubspacesOrderIso B S hS X hX
  let g : {G : Subfunctor X // IsOpenSubspace B S hS G} := e.symm (e ⟨G₁, hG₁⟩ ⊔ e ⟨G₂, hG₂⟩)
  have hge : e g = e ⟨G₁, hG₁⟩ ⊔ e ⟨G₂, hG₂⟩ := e.apply_symm_apply _
  refine ⟨g.1, g.2, ?_, ?_, ?_⟩
  · exact e.le_symm_apply (x := ⟨G₁, hG₁⟩) |>.2 le_sup_left
  · exact e.le_symm_apply (x := ⟨G₂, hG₂⟩) |>.2 le_sup_right
  · rw [← openSubspacesOrderIso_apply B S hS X hX g, hge]
    rfl

/-- **The preimage of a quasi-compact open subspace along a quasi-compact morphism is
quasi-compact.** -/
theorem isQuasiCompactSpace_preimage_of_isQuasiCompact {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : Y ⟶ X)
    (hf : IsQuasiCompact B S hS f) {G : Subfunctor X} (hG : IsOpenSubspace B S hS G)
    (hGqc : IsQuasiCompactSpace B S hS G.toFunctor) :
    IsQuasiCompactSpace B S hS (G.preimage f).toFunctor := by
  have hopen : IsOpen (Set.range (pointsMap B S hS G.toFunctor G.ι)) := by
    rw [← openSubspacesOrderIso_apply B S hS X hX ⟨G, hG⟩]
    exact (openSubspacesOrderIso B S hS X hX ⟨G, hG⟩).2
  refine isQuasiCompactSpace_of_isCompact_range B S hS hY
    (isOpenSubspace_preimage B S hS f G hX hY hG) ?_
  rw [range_pointsMap_preimage_ι]
  exact isQuasiCompactMap_pointsMap B S hS hY hX f hf hopen
    (isCompact_range_of_isQuasiCompactSpace B S hS hG hGqc)

end AlgebraicGeometry.Space

end
