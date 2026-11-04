module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology

/-!
# A quasi-compact morphism of algebraic spaces is quasi-compact on points

If `f : X ⟶ Y` is a quasi-compact morphism of algebraic spaces over a scheme `S`, then the
induced map `|f| : |X| → |Y|` of point spaces is quasi-compact: the preimage of every
quasi-compact open subset of `|Y|` is quasi-compact.

Quasi-compactness of a morphism is `AlgebraicGeometry.Space.IsQuasiCompact`: every base change of
`f` along a morphism from a quasi-compact algebraic space has quasi-compact source.
Quasi-compactness of a map of topological spaces is spelled out in the statement, as the preimage
condition itself. The point sets and their topology are `AlgebraicGeometry.Space.points` and
`AlgebraicGeometry.Space.pointTopology`.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactMap_pointsMap`: a quasi-compact morphism of algebraic
  spaces is quasi-compact on points.

## References

* [Stacks Project, Tag 0EMK](https://stacks.math.columbia.edu/tag/0EMK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A quasi-compact morphism `f : X ⟶ Y` of algebraic spaces over `S`
induces a quasi-compact map `|X| → |Y|` of point spaces: the preimage of a quasi-compact
open subset of `|Y|` is quasi-compact. -/
@[stacks 0EMK]
theorem isQuasiCompactMap_pointsMap {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsQuasiCompact B S hS f) :
    ∀ ⦃U : Set (points B S hS Y)⦄, IsOpen U → IsCompact U →
      IsCompact (pointsMap B S hS X f ⁻¹' U) := by
  intro U hUopen hUcompact
  obtain ⟨G, hG⟩ : ∃ G : {G : Subfunctor Y // IsOpenSubspace B S hS G},
      Set.range (pointsMap B S hS G.1.toFunctor G.1.ι) = U := by
    refine ⟨(openSubspacesOrderIso B S hS Y hY).symm ⟨U, hUopen⟩, ?_⟩
    rw [← openSubspacesOrderIso_apply B S hS Y hY, OrderIso.apply_symm_apply]
  have hGemb : Topology.IsOpenEmbedding (pointsMap B S hS G.1.toFunctor G.1.ι) :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (continuous_pointsMap B S hS G.1.ι)
      (pointsMap_injective_of_mono B S hS G.1.ι)
      (isOpenMap_pointsMap_of_isEtale B S hS G.1.ι G.2.1 hY
        (isEtale_ι_of_isOpenSubspace G.2))
  have hGcompact : CompactSpace (points B S hS G.1.toFunctor) := by
    rwa [← isCompact_univ_iff, hGemb.isCompact_iff, Set.image_univ, hG]
  have hGqc : IsQuasiCompactSpace B S hS G.1.toFunctor :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS G.1.toFunctor G.2.1).2 hGcompact
  have hPcompact : CompactSpace (points B S hS (pullback G.1.ι f)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS (pullback G.1.ι f)
      (isAlgebraicSpace_pullback B S hS G.1.ι f G.2.1 hX hY)).1
      (hf G.1.toFunctor G.2.1 hGqc G.1.ι)
  have hsq : IsPullback (pullback.fst G.1.ι f) (pullback.snd G.1.ι f) G.1.ι f :=
    IsPullback.of_hasPullback _ _
  have hrange : Set.range (pointsMap B S hS (pullback G.1.ι f) (pullback.snd G.1.ι f)) =
      pointsMap B S hS X f ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      rw [Set.mem_preimage, ← hG, ← pointsMap_comp_apply, ← hsq.w, pointsMap_comp_apply]
      exact Set.mem_range_self _
    · intro hx
      obtain ⟨y, hy⟩ : pointsMap B S hS X f x ∈
          Set.range (pointsMap B S hS G.1.toFunctor G.1.ι) := hG ▸ hx
      obtain ⟨w, -, hw⟩ := exists_point_of_isPullback_presheaf B S hS hsq y x hy
      exact ⟨w, hw⟩
  exact hrange ▸ isCompact_range (continuous_pointsMap B S hS (pullback.snd G.1.ι f))

end AlgebraicGeometry.Space

end
