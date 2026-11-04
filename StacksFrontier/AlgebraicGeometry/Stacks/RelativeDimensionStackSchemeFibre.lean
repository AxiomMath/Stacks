module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackRepresentable

/-!
# The relative dimension of Stacks 0DRL of a morphism of schemes of the site

Let `g : W ⟶ V` be a morphism of the big fppf category of `S`. Its two objects represent algebraic
spaces, hence algebraic stacks, and `g` induces a 1-morphism of those stacks. This file identifies
the relative dimension of Stacks 0DRL of that 1-morphism, at a point `w ∈ W`, with the Krull
dimension at `w` of the scheme theoretic fibre of the morphism of schemes underlying `g`.

## Main results

* `AlgebraicGeometry.Space.hasRelativeDimensionAt_yoneda_map_iff`: having relative dimension `d` in
  the sense of Stacks 04NM at a point of a represented algebraic space is the equation on the local
  dimension of the fibre of the underlying morphism of schemes.
* `AlgebraicGeometry.Stack.relativeDimensionAt_algebraicSpaceStackMap_yoneda_map_eq`: the relative
  dimension of Stacks 0DRG of the induced 1-morphism is that local fibre dimension.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_algebraicSpaceStackMap_yoneda_map_eq`: the
  relative dimension of Stacks 0DRL of the induced 1-morphism is that local fibre dimension, read
  in `EInt` through the embedding `AlgebraicGeometry.Stack.dimensionSubNat · 0` that the formula of
  Stacks 0AFN uses on a chart of relative dimension `0`.

## Implementation notes

The local Noetherianity hypotheses of the third result are not used; they appear only because
`AlgebraicGeometry.Stack.relativeStackDimensionAt` takes them as arguments.

## References

* [Stacks Project, Tag 04NL](https://stacks.math.columbia.edu/tag/04NL)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRH](https://stacks.math.columbia.edu/tag/0DRH)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRM](https://stacks.math.columbia.edu/tag/0DRM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Relative dimension at a point of a represented algebraic space is the local dimension of
the scheme theoretic fibre.** For a morphism `g : W ⟶ V` of the big fppf category of `S` and a
point `w` of the scheme underlying `W`, the morphism `yoneda.map g` of algebraic spaces has
relative dimension `d` of Stacks 04NM at `w` exactly when the fibre of the underlying morphism
of schemes has Krull dimension `d` at `w`. -/
theorem hasRelativeDimensionAt_yoneda_map_iff {W V : BigFppfOver B S hS} (g : W ⟶ V) (d : ℕ∞)
    (w : (BigFppfOver.toScheme B S hS).obj W) :
    HasRelativeDimensionAt d B S hS (yoneda.map g) ((pointsEquivScheme B S hS W).symm w) ↔
      topologicalKrullDimAt
          (((BigFppfOver.toScheme B S hS).map g).fiber
            ((BigFppfOver.toScheme B S hS).map g w))
          (((BigFppfOver.toScheme B S hS).map g).asFiber w) = (d : WithBot ℕ∞) := by
  have h := hasRelativeDimensionAt_pointsMap_iff B S hS d (yoneda.map g) W V
    (𝟙 (yoneda.obj W)) (𝟙 (yoneda.obj V)) g (presheaf_etale_id B S hS W)
    (presheaf_etale_id B S hS V) (by simp) w
  rwa [pointsMap_id, id_eq] at h

end Space

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a morphism `g : W ⟶ V` of the big fppf category of `S` whose induced 1-morphism of
algebraic stacks is locally of finite type, the relative dimension of Stacks 0DRG of that
1-morphism at a point `w` of the scheme underlying `W` is the Krull dimension at `w` of the fibre
of the underlying morphism of schemes. -/
theorem relativeDimensionAt_algebraicSpaceStackMap_yoneda_map_eq
    {W V : BigFppfOver B S hS} (g : W ⟶ V)
    (hg : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (algebraicSpaceStackMap.{u, w} B S hS (isAlgebraicSpace_yoneda B S hS W)
        (isAlgebraicSpace_yoneda B S hS V) (yoneda.map g)))
    (w : (BigFppfOver.toScheme B S hS).obj W) :
    relativeDimensionAt.{u, w} B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V))
        (algebraicSpaceStackMap.{u, w} B S hS (isAlgebraicSpace_yoneda B S hS W)
          (isAlgebraicSpace_yoneda B S hS V) (yoneda.map g)) hg
        ((Space.pointsEquivScheme B S hS W).symm w) =
      topologicalKrullDimAt
        (((BigFppfOver.toScheme B S hS).map g).fiber
          ((BigFppfOver.toScheme B S hS).map g w))
        (((BigFppfOver.toScheme B S hS).map g).asFiber w) := by
  obtain ⟨d, hd⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS (yoneda.obj W)
    (isAlgebraicSpace_yoneda B S hS W)
    (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)) _ hg
    ((Space.pointsEquivScheme B S hS W).symm w)
  rw [hd]
  refine ((Space.hasRelativeDimensionAt_yoneda_map_iff B S hS g (d : ℕ∞) w).1 ?_).symm
  exact (relativeDimensionAt_eq_iff_hasRelativeDimensionAt.{u, w} B S hS
    (isAlgebraicSpace_yoneda B S hS W) (isAlgebraicSpace_yoneda B S hS V) (yoneda.map g) hg
    ((Space.pointsEquivScheme B S hS W).symm w) (d : ℕ∞)).1 hd

/-- For a morphism `g : W ⟶ V` of the big fppf category of `S` whose induced 1-morphism of
algebraic stacks is locally of finite type, the relative dimension of Stacks 0DRL of that
1-morphism at a point `w` of the scheme underlying `W` is the Krull dimension at `w` of the fibre
of the underlying morphism of schemes, read in `EInt`. -/
theorem relativeStackDimensionAt_algebraicSpaceStackMap_yoneda_map_eq
    {W V : BigFppfOver B S hS} (g : W ⟶ V)
    (hg : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (algebraicSpaceStackMap.{u, w} B S hS (isAlgebraicSpace_yoneda B S hS W)
        (isAlgebraicSpace_yoneda B S hS V) (yoneda.map g)))
    (hW : IsLocallyNoetherianStack.{u, w} B S hS
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)))
    (hV : IsLocallyNoetherianStack.{u, w} B S hS
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)))
    (w : (BigFppfOver.toScheme B S hS).obj W) :
    relativeStackDimensionAt.{u, w} B S hS
        (algebraicSpaceStackMap.{u, w} B S hS (isAlgebraicSpace_yoneda B S hS W)
          (isAlgebraicSpace_yoneda B S hS V) (yoneda.map g)) hg hW hV
        (stackPointOfSpacePoint B S hS (yoneda.obj W)
          ((Space.pointsEquivScheme B S hS W).symm w)) =
      dimensionSubNat
        (topologicalKrullDimAt
          (((BigFppfOver.toScheme B S hS).map g).fiber
            ((BigFppfOver.toScheme B S hS).map g w))
          (((BigFppfOver.toScheme B S hS).map g).asFiber w)) 0 := by
  classical
  obtain ⟨p, q, hp, hq⟩ := exists_admissible_fieldFibreStackDimensionAt.{u, w} B S hS
    (algebraicSpaceStackMap.{u, w} B S hS (isAlgebraicSpace_yoneda B S hS W)
      (isAlgebraicSpace_yoneda B S hS V) (yoneda.map g))
    (stackPointOfSpacePoint B S hS (yoneda.obj W)
      ((Space.pointsEquivScheme B S hS W).symm w))
  rw [relativeStackDimensionAt_eq_fieldFibreStackDimensionAt_of_algebraicSpace.{u, w} B S hS
      (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W) _ _ hg hW hV _ p q hp hq,
    fieldFibreStackDimensionAt_eq_dimensionSubNat_relativeDimensionAt.{u, w} B S hS
      (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W) _ _ hg
      ((Space.pointsEquivScheme B S hS W).symm w) p q hp hq,
    relativeDimensionAt_algebraicSpaceStackMap_yoneda_map_eq.{u, w} B S hS g hg w]

end Stack

end AlgebraicGeometry

end
