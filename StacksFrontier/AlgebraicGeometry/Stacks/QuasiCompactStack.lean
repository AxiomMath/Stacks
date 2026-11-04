module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# Quasi-compact algebraic stacks

An algebraic stack is *quasi-compact* when its space of points, with its canonical topology, is a
compact space. Quasi-compactness passes along a surjection of algebraic stacks, and the algebraic
stack attached to a quasi-compact algebraic space is quasi-compact.

## Main definitions

* `AlgebraicGeometry.Stack.IsQuasiCompactStack`: quasi-compactness of an algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactStack_of_isSurjective`: the target of a surjective
  1-morphism out of a quasi-compact algebraic stack is quasi-compact.
* `AlgebraicGeometry.Stack.isQuasiCompactStack_fibredCategory`: the algebraic stack attached to
  a quasi-compact algebraic space is quasi-compact.
* `AlgebraicGeometry.Stack.pointsMap_surjective_of_basedEquivalence`: an equivalence of
  categories over the site is surjective on points.
* `AlgebraicGeometry.Stack.spacePointMap_eq_pointsMap_comp` and
  `AlgebraicGeometry.Stack.spacePointMap_surjective_iff_pointsMap_surjective`: the canonical map
  of a chart by an algebraic space, read through the category of elements of that space.

## References

* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic stack over `S` is *quasi-compact* when its space of points, with the topology
`pointTopology`, is a compact space. -/
@[stacks 04YB]
abbrev IsQuasiCompactStack
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (_h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) : Prop :=
  @CompactSpace (points B S hS 𝒳.val 𝒳.property) (pointTopology B S hS 𝒳)

/-- An equivalence of categories over the big fppf site of `S` is surjective on points. -/
theorem pointsMap_surjective_of_basedEquivalence
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (e : BasedCategory.Equivalence 𝒜.val 𝒞.val) :
    Function.Surjective
      (pointsMap B S hS 𝒜.val 𝒜.property 𝒞.property e.functor) :=
  (pointsEquivOfBasedEquivalence B S hS 𝒜.property 𝒞.property e).surjective

/-- The canonical map on points of a chart is the map on points of the chart composed with the
canonical map of the tautological chart. -/
theorem spacePointMap_eq_pointsMap_comp (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val) :
    spacePointMap B S hS F 𝒳 f =
      pointsMap B S hS (fibredCategory B S hS F).val (fibredCategory B S hS F).property
          𝒳.property f ∘
        spacePointMap B S hS F (fibredCategory B S hS F)
          (BasedFunctor.id (fibredCategory B S hS F).val) :=
  spacePointMap_comp B S hS F (fibredCategory B S hS F) 𝒳
    (BasedFunctor.id (fibredCategory B S hS F).val) f

/-- A chart by an algebraic space is surjective on points exactly when the 1-morphism out of its
category of elements is. -/
theorem spacePointMap_surjective_iff_pointsMap_surjective
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val) :
    Function.Surjective (spacePointMap B S hS F 𝒳 f) ↔
      Function.Surjective (pointsMap B S hS (fibredCategory B S hS F).val
        (fibredCategory B S hS F).property 𝒳.property f) := by
  rw [spacePointMap_eq_pointsMap_comp]
  exact ⟨fun h => h.of_comp, fun h => h.comp (spacePointMap_id_bijective B S hS F).2⟩

/-- The target of a surjective 1-morphism out of a quasi-compact algebraic stack is
quasi-compact. -/
theorem isQuasiCompactStack_of_isSurjective
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)
    (h𝒰 : IsQuasiCompactStack.{u, w} B S hS 𝒰.val 𝒰.property)
    (hf : IsSurjective B S hS f) :
    IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property :=
  let : TopologicalSpace (points B S hS 𝒰.val.val 𝒰.val.property) :=
    pointTopology B S hS 𝒰.val
  let : TopologicalSpace (points B S hS 𝒳.val.val 𝒳.val.property) :=
    pointTopology B S hS 𝒳.val
  let : CompactSpace (points B S hS 𝒰.val.val 𝒰.val.property) := h𝒰
  Function.Surjective.compactSpace
    (continuous_pointsMap B S hS 𝒰.val 𝒳.val f.hom.hom) hf

/-- The algebraic stack attached to a quasi-compact algebraic space is quasi-compact. -/
theorem isQuasiCompactStack_fibredCategory
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hFqc : Space.IsQuasiCompactSpace B S hS F)
    (h𝒰 : IsAlgebraicStack.{u, w} B S hS (fibredCategory B S hS F).val) :
    IsQuasiCompactStack.{u, w} B S hS (fibredCategory B S hS F) h𝒰 :=
  let : TopologicalSpace (Space.points B S hS F) := Space.pointTopology B S hS F
  let : TopologicalSpace
      (points B S hS (fibredCategory B S hS F).val (fibredCategory B S hS F).property) :=
    pointTopology B S hS (fibredCategory B S hS F)
  let : CompactSpace (Space.points B S hS F) :=
    (Space.isQuasiCompactSpace_iff_compactSpace_points B S hS F hF).1 hFqc
  Function.Surjective.compactSpace
    (continuous_spacePointMap B S hS F hF (fibredCategory B S hS F)
      (BasedFunctor.id (fibredCategory B S hS F).val))
    (spacePointMap_id_bijective B S hS F).2

end AlgebraicGeometry.Stack

end
