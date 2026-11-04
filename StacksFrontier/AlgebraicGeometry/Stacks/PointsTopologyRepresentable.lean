module

public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Basic

/-!
# The points of a stack represented by an algebraic space

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, and suppose
`𝒳` is represented by an algebraic space `F` over `S`, that is, suppose given an equivalence over
the site between `𝒳` and the category of elements of `F`. The inverse of that equivalence is a
chart of `𝒳` by `F` in the sense of `AlgebraicGeometry.Stack.SpaceChart`
(`AlgebraicGeometry.Stack.representingEquivalence`), and this file proves that the canonical map
on points of that chart is a **homeomorphism** from the topology of Tag 03BX on the points of `F`
to the topology of Tag 04XL on the points of `𝒳`: the point topology of a stack represented by an
algebraic space is the point topology of that space.

Continuity and bijectivity are formal. The content is **openness**, which is not an instance of
the openness clause of Tag 04XL (`AlgebraicGeometry.Stack.isOpenMap_spacePointMap`): that clause
asks the chart to be flat and locally of finite presentation on every represented base change,
whereas here the chart is an equivalence and no flatness hypothesis is available. Instead the
openness is proved directly from the definition of the topology as a supremum of coinduced
topologies: by `AlgebraicGeometry.Stack.isOpen_pointTopology_iff` it suffices to see that the
image of an open set has open preimage along *every* chart, and every chart of `𝒳` factors on
points through the representing chart (`AlgebraicGeometry.Stack.spacePointMap_factor`), because a
based functor between categories of elements of set-valued presheaves is a morphism of presheaves.
Since the representing chart is injective on points, the preimage of the image of an open set
along it is that set again, and the factorization reduces the question to continuity of the map on
points of a morphism of algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Stack.representingEquivalence`: the chart of `𝒳` by `F` attached to a
  representing equivalence.

## Main results

* `AlgebraicGeometry.Stack.bijective_spacePointMap_representing`: the canonical map on points of
  the representing chart is bijective.
* `AlgebraicGeometry.Stack.isOpenMap_spacePointMap_representing`: it is an open map.
* `AlgebraicGeometry.Stack.isHomeomorph_spacePointMap_representing`: it is a homeomorphism.
* `AlgebraicGeometry.Stack.spacePointMap_representing_naturality`: the representing charts of
  two represented stacks identify the map on points of a 1-morphism between them with the map on
  points of the induced morphism of representing presheaves.

## Implementation notes

`AlgebraicGeometry.Stack.pointsMap_basedFunctorId` and
`AlgebraicGeometry.Stack.representationMap_naturality` were `private` in
`StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology` when this file was written, and were
re-derived here from their own proofs. They are now public there and are used rather than copied;
`AlgebraicGeometry.Stack.spacePointMap_representing_naturality` below is one application of the
second.

`AlgebraicGeometry.Stack.representingEquivalence` is defeq to
`AlgebraicGeometry.Stack.representationMap` of that file, which is how the library's own
`representationMap_bijective` is proved; it is given a separate name here because the statements
below, and the characterization of universally closed representable 1-morphisms that uses them,
have to mention the chart as an equivalence rather than as a bare 1-morphism.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart attached to a representing equivalence -/

/-- The chart of `𝒳` by an algebraic space `F` representing it: the equivalence over the site
between the category of elements of `F` and `𝒳` obtained by inverting a representing equivalence.
Its forward 1-morphism is the chart, an object of `AlgebraicGeometry.Stack.SpaceChart`. -/
noncomputable def representingEquivalence (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    BasedCategory.Equivalence (fibredCategory B S hS F).val 𝒳.val :=
  ((StacksRepresentableCFG.EquivalenceOver.refl
    (fibredCategory B S hS F).val.p).trans e.symm).toBasedEquivalence

/-- The canonical map on points of a chart is the map on points of the underlying based functor
after the canonical map on points of the tautological chart. -/
private theorem spacePointMap_eq_pointsMap_comp_id (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (cf : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val) :
    spacePointMap B S hS F 𝒳 cf =
      pointsMap B S hS (fibredCategory B S hS F).val
          (fibredCategory B S hS F).property 𝒳.property cf ∘
        spacePointMap B S hS F (fibredCategory B S hS F)
          (BasedFunctor.id (fibredCategory B S hS F).val) := by
  rw [← spacePointMap_comp B S hS F (fibredCategory B S hS F) 𝒳
    (BasedFunctor.id (fibredCategory B S hS F).val) cf, BasedFunctor.id_comp]

/-- The canonical map on points of the chart of a representing equivalence factors as the
tautological chart of `F` followed by an equivalence, so it is bijective. -/
theorem bijective_spacePointMap_representing (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    Function.Bijective
      (spacePointMap B S hS F 𝒳 (representingEquivalence B S hS F 𝒳 e).functor) := by
  have hbij : Function.Bijective (pointsMap B S hS
      (fibredCategory B S hS F).val (fibredCategory B S hS F).property
      𝒳.property (representingEquivalence B S hS F 𝒳 e).functor) :=
    (pointsEquivOfBasedEquivalence B S hS (fibredCategory B S hS F).property 𝒳.property
      (representingEquivalence B S hS F 𝒳 e)).bijective
  rw [spacePointMap_eq_pointsMap_comp_id B S hS F 𝒳]
  exact hbij.comp (spacePointMap_id_bijective B S hS F)

/-- **The factorization.** Every chart of a category fibred in groupoids represented by an
algebraic space factors, on points, through the chart of a representing equivalence: a chart by
`G` is a based functor of categories of elements once it is composed with the inverse of the
representing equivalence, hence a morphism of presheaves `G ⟶ F`. -/
private theorem spacePointMap_factor (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (cf : (fibredCategory B S hS G).val ⥤ᵇ 𝒳.val) :
    spacePointMap B S hS G 𝒳 cf =
      spacePointMap B S hS F 𝒳 (representingEquivalence B S hS F 𝒳 e).functor ∘
        Space.pointsMap B S hS G
          (presheafMapOfBasedFunctor
            (cf.comp (representingEquivalence B S hS F 𝒳 e).inverse)) := by
  funext p
  have hF := spacePointMap_eq_pointsMap_comp_id B S hS F 𝒳
    (representingEquivalence B S hS F 𝒳 e).functor
  have hG := spacePointMap_eq_pointsMap_comp_id B S hS G 𝒳 cf
  refine (congrFun hG p).trans (Eq.symm ((congrFun hF _).trans ?_))
  refine ((congrArg (pointsMap B S hS (fibredCategory B S hS F).val
      (fibredCategory B S hS F).property 𝒳.property
      (representingEquivalence B S hS F 𝒳 e).functor)
    (spacePointMap_presheafMapOfBasedFunctor B S hS
      (cf.comp (representingEquivalence B S hS F 𝒳 e).inverse) p)).trans ?_)
  refine (congrArg (pointsMap B S hS (fibredCategory B S hS F).val
      (fibredCategory B S hS F).property 𝒳.property
      (representingEquivalence B S hS F 𝒳 e).functor)
    (pointsMap_comp B S hS (fibredCategory B S hS G).val
      (fibredCategory B S hS G).property 𝒳.property
      (fibredCategory B S hS F).property cf
      (representingEquivalence B S hS F 𝒳 e).inverse _).symm).trans ?_
  rw [pointsMap_comp, pointsMap_eq_of_basedNatTrans B S hS 𝒳.val
    𝒳.property 𝒳.property (representingEquivalence B S hS F 𝒳 e).counitIso.hom]
  exact pointsMap_basedFunctorId B S hS 𝒳.property _

/-- **Openness of the chart of a representing equivalence.** For a category fibred in groupoids
represented by an algebraic space `F`, the canonical map on points of the representing chart is an
open map from the topology of Tag 03BX on the points of `F` to the topology of Tag 04XL on the
points of the stack.

This is not an instance of the openness clause of Tag 04XL, which asks the chart to be flat and
locally of finite presentation on its represented base changes. It is proved from the definition
of the topology: the preimage of the image of an open set along an arbitrary chart is computed by
`AlgebraicGeometry.Stack.spacePointMap_factor` and
`AlgebraicGeometry.Stack.bijective_spacePointMap_representing`, and openness of it is continuity
of the map on points of a morphism of algebraic spaces. -/
theorem isOpenMap_spacePointMap_representing (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    @IsOpenMap _ _ (Space.pointTopology B S hS F) (pointTopology B S hS 𝒳)
      (spacePointMap B S hS F 𝒳 (representingEquivalence B S hS F 𝒳 e).functor) := by
  intro V hV
  refine (isOpen_pointTopology_iff B S hS 𝒳 _).2 fun c => ?_
  rw [spacePointMap_factor B S hS F c.1.1 𝒳 e c.2, Set.preimage_comp,
    Set.preimage_image_eq V (bijective_spacePointMap_representing B S hS F 𝒳 e).injective]
  have hc := Space.continuous_pointsMap B S hS
    (presheafMapOfBasedFunctor (c.2.comp (representingEquivalence B S hS F 𝒳 e).inverse))
  rw [continuous_def] at hc
  exact hc V hV

/-- **The point topology of a stack represented by an algebraic space is the point topology of
that space.** The canonical map on points of the chart of a representing equivalence is a
homeomorphism from the topology of Tag 03BX to the topology of Tag 04XL. -/
theorem isHomeomorph_spacePointMap_representing (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    @IsHomeomorph _ _ (Space.pointTopology B S hS F) (pointTopology B S hS 𝒳)
      (spacePointMap B S hS F 𝒳 (representingEquivalence B S hS F 𝒳 e).functor) :=
  @IsHomeomorph.mk _ _ (Space.pointTopology B S hS F) (pointTopology B S hS 𝒳) _
    (continuous_spacePointMap B S hS F hF 𝒳 _)
    (isOpenMap_spacePointMap_representing B S hS F 𝒳 e)
    (bijective_spacePointMap_representing B S hS F 𝒳 e)

/-- **Naturality of the canonical map in the chart.** The morphism of representing presheaves
induced by a 1-morphism of represented categories fibred in groupoids (Tag 04SW) acts on points
the way the 1-morphism does. This is `AlgebraicGeometry.Stack.representationMap_naturality` read
in the vocabulary of `AlgebraicGeometry.Stack.representingEquivalence`, the two charts being
definitionally equal. -/
theorem spacePointMap_representing_naturality
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (eX : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eY : StacksRepresentableCFG.EquivalenceOver 𝒴.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⟶ 𝒴) (x : Space.points B S hS F) :
    spacePointMap B S hS G 𝒴 (representingEquivalence B S hS G 𝒴 eY).functor
        (Space.pointsMap B S hS F (representingMap B S hS 𝒳 𝒴 F G eX eY f) x) =
      pointsMap B S hS 𝒳.val 𝒳.property 𝒴.property f.hom
        (spacePointMap B S hS F 𝒳 (representingEquivalence B S hS F 𝒳 eX).functor x) :=
  representationMap_naturality B S hS F G 𝒳 𝒴 eX eY f x

end AlgebraicGeometry.Stack

end
