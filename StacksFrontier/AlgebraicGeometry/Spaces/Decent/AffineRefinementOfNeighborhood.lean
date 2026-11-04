module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodCofiltered
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk

/-!
# Affine refinements of an elementary étale neighborhood

Every elementary étale neighborhood of a point of an algebraic space is refined by an *affine*
one, that is, one whose scheme is affine, and any two elementary étale neighborhoods of a point
are refined by a common affine one.

## Main results

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.exists_affine_refinement`: every
  elementary étale neighborhood is refined by an affine one.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.exists_affine_cone_objs`: any two
  elementary étale neighborhoods of a point are refined by a common affine one.

## References

* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0BGV](https://stacks.math.columbia.edu/tag/0BGV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X)

namespace ElementaryEtaleNeighborhood

/-- Every elementary étale neighborhood of a point of an algebraic space is refined by one
whose scheme is affine. -/
theorem exists_affine_refinement (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    ∃ (V : ElementaryEtaleNeighborhood B S hS X hX x) (_ : V ⟶ U),
      IsAffine V.scheme.left.1 := by
  obtain ⟨-, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    U.scheme.left.1.isBasis_affineOpens.exists_subset_of_mem_open
      (show U.point ∈ (⊤ : U.scheme.left.1.Opens) from trivial)
      (⊤ : U.scheme.left.1.Opens).2
  refine ⟨openRestrictionNeighborhood B S hS X hX x U W hxW,
    openRestrictionNeighborhoodHom B S hS X hX x U (le_top (a := W)) hxW trivial ≫
      openRestrictionNeighborhoodToOriginal B S hS X hX x U, hW⟩

/-- Any two elementary étale neighborhoods of a point of an algebraic space are refined by a
common elementary étale neighborhood whose scheme is affine. -/
@[stacks 0BGV "two neighbourhoods are refined by a common one whose scheme is affine"]
theorem exists_affine_cone_objs (U V : ElementaryEtaleNeighborhood B S hS X hX x) :
    ∃ (W : ElementaryEtaleNeighborhood B S hS X hX x) (_ : W ⟶ U) (_ : W ⟶ V),
      IsAffine W.scheme.left.1 := by
  obtain ⟨T, a, b, -⟩ := exists_cone_objs B S hS X hX x U V
  obtain ⟨W, c, hW⟩ := exists_affine_refinement B S hS X hX x T
  exact ⟨W, c ≫ a, c ≫ b, hW⟩

end ElementaryEtaleNeighborhood

end AlgebraicGeometry.Space

end
