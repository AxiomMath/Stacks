module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.GeometricallyUnibranch
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenFiltrationSeparatedNeighbourhoods

/-!
# Transporting the unibranch property along an isomorphism

Being geometrically unibranch at a point is carried along an isomorphism of algebraic spaces.
This is the degenerate case of descent along a flat morphism: an isomorphism is étale, an étale
morphism of algebraic spaces is flat, and flatness at a point is all that the descent statement
consumes.

## Main results

* `AlgebraicGeometry.Space.isGeometricallyUnibranchAt_of_isIso` — the property at a point is
  carried forward along an isomorphism.
* `AlgebraicGeometry.Space.isGeometricallyUnibranch_of_isIso` — the property at every point is
  carried forward along an isomorphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An isomorphism of algebraic spaces is flat at every point: it is étale, and an étale
morphism of algebraic spaces is flat. -/
public theorem isFlatAt_of_isIso (f : F ⟶ G) [IsIso f] (x : points B S hS F) :
    IsFlatAt B S hS f x :=
  (isFlat_iff_forall_isFlatAt B S hS f).mp
    (isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS f)) x

/-- If `F` is geometrically unibranch at `x` and `f : F ⟶ G` is an isomorphism of algebraic
spaces, then `G` is geometrically unibranch at the image of `x`. -/
public theorem isGeometricallyUnibranchAt_of_isIso (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) [IsIso f] (x : points B S hS F)
    (hx : IsGeometricallyUnibranchAt B S hS F x) :
    IsGeometricallyUnibranchAt B S hS G (pointsMap B S hS F f x) :=
  isGeometricallyUnibranchAt_of_isFlatAt B S hS hF hG f x (isFlatAt_of_isIso B S hS f x) hx

/-- A geometrically unibranch algebraic space is carried to a geometrically unibranch algebraic
space by an isomorphism. -/
public theorem isGeometricallyUnibranch_of_isIso (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) [IsIso f]
    (hx : IsGeometricallyUnibranch B S hS F) :
    IsGeometricallyUnibranch B S hS G := by
  intro y
  obtain ⟨x, hxy⟩ : ∃ x : points B S hS F, pointsMap B S hS F f x = y := by
    refine ⟨pointsMap B S hS G (inv f) y, ?_⟩
    have h := pointsMap_comp B S hS (F := G) (G := F) (H := G) (inv f) f
    simp only [IsIso.inv_hom_id, pointsMap_id] at h
    exact (congrFun h y).symm
  exact hxy ▸ isGeometricallyUnibranchAt_of_isIso B S hS hF hG f x (hx x)

end AlgebraicGeometry.Space

end
