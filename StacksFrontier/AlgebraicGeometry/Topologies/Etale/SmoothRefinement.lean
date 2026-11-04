module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.EtaleLocalSection

/-!
# Étale refinements of smooth coverings

Every smooth covering of a scheme is refined by an étale covering. So the étale coverings are
cofinal among the smooth ones, and the smooth topology on the category of schemes coincides with
the étale topology.

## Main results

* `AlgebraicGeometry.exists_etale_cover_refining_smooth_cover` is Tag 055V: an étale covering
  refining a given smooth covering.
* `AlgebraicGeometry.exists_affine_etale_refinement_of_smooth_cover` sharpens it: the refining
  étale covering may be taken to have affine members.

## Implementation notes

Coverings are `AlgebraicGeometry.Scheme.Cover` for the precoverage attached to the relevant
morphism property, and a refinement is a morphism of the underlying pre-zero-hypercovers, which
is the library's rendering of the source's notion of refinement (Tag 00VT, part (2)).

The refining covering is indexed by the points of the base: at each point Tag 055U produces an
étale neighbourhood admitting a morphism to the member of the smooth covering whose image
contains that point. Hence the refinement may always be taken indexed in the universe of the
points of the base, whatever the universe of the original index type.

## References

* [Stacks Project, Tag 055V](https://stacks.math.columbia.edu/tag/055V)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 055V.** Every smooth covering of a scheme is refined by an étale
covering. -/
@[stacks 055V]
public theorem exists_etale_cover_refining_smooth_cover {S : Scheme.{u}}
    (𝒰 : S.Cover.{v} (Scheme.precoverage (@Smooth.{u}))) :
    ∃ 𝒱 : S.Cover.{u} (Scheme.precoverage (@Etale.{u})),
      Nonempty (𝒱.toPreZeroHypercover.Hom 𝒰.toPreZeroHypercover) := by
  classical
  have hdata (s : S) : ∃ (W : EtaleNeighborhood S s) (i : 𝒰.I₀)
      (g : W.scheme ⟶ 𝒰.X i), g ≫ 𝒰.f i = W.toBase := by
    obtain ⟨i, hs⟩ := ((Scheme.presieve₀_mem_precoverage_iff (P := @Smooth.{u})
      𝒰.toPreZeroHypercover).mp 𝒰.mem₀).1 s
    have : Smooth (𝒰.f i) := 𝒰.map_prop i
    obtain ⟨W, g, hg⟩ := exists_etaleNeighborhood_lift_of_smooth (𝒰.f i) s hs
    exact ⟨W, i, g, hg⟩
  choose W i g hg using hdata
  let 𝒱 : S.Cover.{u} (Scheme.precoverage (@Etale.{u})) :=
    Scheme.Cover.mkOfCovers (ULift.{u} S) (fun j => (W j.down).scheme)
      (fun j => (W j.down).toBase) (fun s => ⟨⟨s⟩, (W s).point, (W s).map_point⟩)
      (fun j => (W j.down).etale_toBase)
  exact ⟨𝒱, ⟨⟨fun j => i j.down, fun j => g j.down, fun j => hg j.down⟩⟩⟩

/-- Every smooth covering of a scheme is refined by a jointly surjective family of étale
morphisms with **affine** sources: replace each member of the étale refinement of Tag 055V by
its affine open cover. -/
public theorem exists_affine_etale_refinement_of_smooth_cover {T : Scheme.{u}}
    (𝒰 : T.Cover.{v} (Scheme.precoverage (@Smooth.{u}))) :
    ∃ (J : Type u) (A : J → Scheme.{u}) (p : ∀ j, A j ⟶ T),
      (∀ j, IsAffine (A j)) ∧ (∀ j, Etale (p j)) ∧
        (∀ x : T, ∃ (j : J) (y : A j), (p j).base y = x) ∧
        ∀ j, ∃ (i : 𝒰.I₀) (h : A j ⟶ 𝒰.X i), h ≫ 𝒰.f i = p j := by
  obtain ⟨𝒱, ⟨H⟩⟩ := exists_etale_cover_refining_smooth_cover 𝒰
  refine ⟨(j : 𝒱.I₀) × (𝒱.X j).affineCover.I₀,
    fun q => (𝒱.X q.1).affineCover.X q.2,
    fun q => (𝒱.X q.1).affineCover.f q.2 ≫ 𝒱.f q.1,
    fun q => inferInstance, fun q => ?_, fun x => ?_, fun q => ?_⟩
  · have := 𝒱.map_prop q.1
    infer_instance
  · obtain ⟨j, y, hy⟩ := ((Scheme.presieve₀_mem_precoverage_iff (P := @Etale.{u})
      𝒱.toPreZeroHypercover).mp 𝒱.mem₀).1 x
    obtain ⟨k, z, hz⟩ := ((Scheme.presieve₀_mem_precoverage_iff (P := @IsOpenImmersion.{u})
      (𝒱.X j).affineCover.toPreZeroHypercover).mp (𝒱.X j).affineCover.mem₀).1 y
    exact ⟨⟨j, k⟩, z, by rw [Scheme.Hom.comp_apply, hz, hy]⟩
  · exact ⟨H.s₀ q.1, (𝒱.X q.1).affineCover.f q.2 ≫ H.h₀ q.1, by
      rw [Category.assoc, H.w₀]⟩

end AlgebraicGeometry

end
