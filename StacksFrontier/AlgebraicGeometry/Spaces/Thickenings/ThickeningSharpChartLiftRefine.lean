module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionExt
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison

/-!
# The morphism of charts attached to a comorphism through a thickening is compatible with
refinement

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`,
let `c : X ⟶ W`, and let `a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` be a morphism of sheaves of rings.
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartSchemeHom.lean` attaches
to `a`, an **affine** étale scheme chart `V` of `W` and an étale scheme chart `j` of `X` above
`X ×_W V` a morphism of schemes `V' ⟶ V`, where `V'` is the chart of `X` carried by `j`.

That assignment is a *single* morphism `a` read on a chart diagram, and this file proves that it
is **functorial in the diagram**: in the chart of `X` (an étale chart above the one `j` carries
gives the restriction of the morphism) and in the chart of `W` (a chart of `W` above `V`,
with the index base changed to it, gives the morphism followed by the chart morphism).

Both are naturality statements about the chart projections of a direct image, which are the
projections of a limit over the charts: `AlgebraicGeometry.Space.ranChartCone_π_comp` is the
cone condition and `AlgebraicGeometry.Space.ranChartCone_π_map` the compatibility with a
morphism of charts of `W`, and both hold at an arbitrary sheaf of sets.

This is what makes the chartwise morphisms produced by `a` **agree on a common refinement**, and
so glue: two affine chart diagrams over `c` with a common chart of `X` above both give one and
the same section of `W` over that chart as soon as the two index chart morphisms are induced by
one morphism into a third chart of `W`.

## Main results

* `AlgebraicGeometry.Space.directImageChartProjection_index_comp`: the chart projections of a
  direct image form a cone over the indices, at an arbitrary sheaf of sets.
* `AlgebraicGeometry.Space.directImageChartProjection_chart_map`: restricting a section of a
  direct image to a smaller chart of `W` and projecting is projecting at the base-changed index.
* `AlgebraicGeometry.Space.thickeningLiftChartAppTop_index_comp` and
  `AlgebraicGeometry.Space.thickeningLiftChartAppTop_chart_map`: the same two compatibilities
  for the map of regular functions attached to `a`.
* `AlgebraicGeometry.Space.thickeningLiftChartHom_index_comp` and
  `AlgebraicGeometry.Space.thickeningLiftChartHom_chart_map`: the same two for the attached
  morphism of schemes over an affine chart of `W`.
* `AlgebraicGeometry.Space.thickeningLiftChartSiteHom_index_comp` and
  `AlgebraicGeometry.Space.thickeningLiftChartSiteHom_chart_map`: the same two for the attached
  morphism of the big fppf category over `S`, the functor to schemes being faithful.
* `AlgebraicGeometry.Space.yoneda_map_thickeningLiftChartSiteHom_chart_map`: **the section of
  `W` over the chart of `X` does not depend on the chart of `W` the diagram passes through.**
* `AlgebraicGeometry.Space.yoneda_map_thickeningLiftChartSiteHom_index_comp`: **and it is
  compatible with restriction to a smaller chart of `X`.**

## Implementation notes

The index of the limit of chart sections is a `CategoryTheory.StructuredArrow`, and a morphism
`φ` of indices has for its `right` field a morphism of the charts of `X` *in the opposite
direction*; the two compatibilities are therefore stated with `φ.right` and with `m` for a
morphism `V₁ ⟶ V₂` of charts of `W`, and the base-changed index is the composite
`AlgebraicGeometry.Space.chartBaseChange` of `m` with the given index, which is the spelling
`AlgebraicGeometry.Space.chartBaseChangeMap_map` and
`AlgebraicGeometry.Space.chartProjection_map` use.

`AlgebraicGeometry.Space.thickeningLiftChartAppTop` is the value of `a` over the chart of `W`,
carried across the comparison of iterated direct images and projected to the chart of `X`, with
the unit of the thickening cancelled.  Each of those three factors is natural, the first two
being morphisms of sheaves and the third injective on the sections over a chart of a thickening
(`AlgebraicGeometry.Space.bijective_thickeningRingUnit_app`); so each compatibility is proved by
applying the unit and rewriting the three factors in turn.

The statements about morphisms of schemes are proved by `AlgebraicGeometry.ext_of_isAffine` from
the statements about maps of regular functions, the chart of `W` being affine; the statements
about morphisms of the site follow because the functor to schemes is faithful on the morphisms
over `S`.

**No `@[stacks]` attribute is placed.**  As in the files this one extends, what is proved is a
comparison internal to this development of two readings of [Stacks Project, Tag 03G8].

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), diagrams of charts.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this step is an
  input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### The chart projections of a direct image, at an arbitrary sheaf -/

/-- The chart projection of a direct image is the cone projection of the comparison with its
right Kan extension form. -/
private theorem directImageChartProjection_app_eq_ranChartCone_π (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (a : (smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj F) :
    (directImageChartProjection B S hS f V j).app F a =
      (ranChartCone B S hS X F.obj (chartBaseChange B S hS f V)).π.app j
        (((smallEtaleDirectImageRanIso B S hS f).hom.app F).hom.app (op V) a) :=
  (directImageChartProjection_app_apply B S hS f V j F a).trans
    (chartProjection_app_eq_ranChartCone_π B S hS f V j F _)

/-- **The chart projections of a direct image form a cone over the indices**: the projection to
a chart of `X` followed by restriction to a chart above it is the projection to the latter.

This is `AlgebraicGeometry.Space.chartProjection_naturality` for the direct image rather than
its right Kan extension form and at an arbitrary sheaf of sets, which is the generality the
chart reading of a comorphism through a thickening needs: the sheaf being projected there is the
iterated direct image `i_*(i^{-1}𝒪_X)`, not the structure sheaf. -/
theorem directImageChartProjection_index_comp (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    {j j' : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op}
    (φ : j ⟶ j') (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (a : (smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj F) :
    F.obj.map φ.right ((directImageChartProjection B S hS f V j).app F a) =
      (directImageChartProjection B S hS f V j').app F a := by
  rw [directImageChartProjection_app_eq_ranChartCone_π,
    directImageChartProjection_app_eq_ranChartCone_π]
  exact ranChartCone_π_comp B S hS X F.obj (chartBaseChange B S hS f V) φ _

/-- **Restricting a section of a direct image to a smaller chart of `Y` and projecting to a
chart of `X` is projecting at the base-changed index.**

This is `AlgebraicGeometry.Space.chartProjection_map` for the direct image rather than its right
Kan extension form and at an arbitrary sheaf of sets; the comparison of the two forms of the
direct image is a morphism of sheaves, so it commutes with the restriction. -/
theorem directImageChartProjection_chart_map (f : X ⟶ Y) {V₁ V₂ : SmallEtale B S hS Y.1}
    (m : V₁ ⟶ V₂)
    (j : StructuredArrow (op (chartBaseChange B S hS f V₁)) (comparisonFunctor B S hS X).op)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (a : (smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V₂)).obj F) :
    (directImageChartProjection B S hS f V₁ j).app F
        (((smallEtaleDirectImage B S hS f).obj F).obj.map m.op a) =
      (directImageChartProjection B S hS f V₂ (StructuredArrow.mk
        (((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map m)).op ≫ j.hom))).app F a := by
  have hnat := NatTrans.naturality_apply
    ((smallEtaleDirectImageRanIso B S hS f).hom.app F).hom m.op a
  refine ((directImageChartProjection_app_eq_ranChartCone_π B S hS f V₁ j F _).trans ?_).trans
    (directImageChartProjection_app_eq_ranChartCone_π B S hS f V₂
      (StructuredArrow.mk (((spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS Y).map m)).op ≫ j.hom)) F a).symm
  refine Eq.trans (congrArg _ hnat) ?_
  exact ranChartCone_π_map B S hS X F.obj
    ((spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS Y).map m)) j _

variable {W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-! ### The map of regular functions attached to a comorphism, under refinement -/

/-- **The map of regular functions attached to `a` over a chart of `X` above the one of a given
index is the restriction of the map attached at that index.**

The three factors of `AlgebraicGeometry.Space.thickeningLiftChartAppTop` — the value of `a`, the
comparison of iterated direct images, and the inverse of the unit of the thickening — are the
same at the two indices, and the chart projection at the smaller index is the restriction of the
one at the larger, by
`AlgebraicGeometry.Space.directImageChartProjection_index_comp`. -/
theorem thickeningLiftChartAppTop_index_comp (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    {j j' : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op}
    (φ : j ⟶ j')
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op V))) :
    thickeningLiftChartAppTop B S hS Z hZ c a V j' b =
      (structureRingSheaf B S hS X).obj.map φ.right
        (thickeningLiftChartAppTop B S hS Z hZ c a V j b) := by
  refine (bijective_thickeningRingUnit_app B S hS Z hZ j'.right).1 ?_
  refine (thickeningRingUnit_thickeningLiftChartAppTop B S hS Z hZ c a V j' b).trans ?_
  refine Eq.trans ?_ (ConcreteCategory.congr_hom
    ((thickeningRingUnit B S hS Z).hom.naturality φ.right)
    (thickeningLiftChartAppTop B S hS Z hZ c a V j b)).symm
  refine Eq.trans ?_ (congrArg
    (((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS X Z))).obj
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).obj.map φ.right)
    (thickeningRingUnit_thickeningLiftChartAppTop B S hS Z hZ c a V j b)).symm
  exact (directImageChartProjection_index_comp B S hS c V φ _ _).symm

/-- **The map of regular functions attached to `a` over a chart of `W` above `V` at the
base-changed index is the one attached over `V`, precomposed with restriction of regular
functions.**

The value of `a` and the comparison of iterated direct images are morphisms of sheaves on the
small étale site of `W`, so they commute with restriction from `V₂` to `V₁`; and restriction
followed by the chart projection over `V₁` is the chart projection over `V₂` at the base-changed
index, by `AlgebraicGeometry.Space.directImageChartProjection_chart_map`. -/
theorem thickeningLiftChartAppTop_chart_map (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {V₁ V₂ : SmallEtale B S hS W.1} (m : V₁ ⟶ V₂)
    (j : StructuredArrow (op (chartBaseChange B S hS c V₁)) (comparisonFunctor B S hS X).op)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op V₂))) :
    thickeningLiftChartAppTop B S hS Z hZ c a V₂ (StructuredArrow.mk
        (((spacesBaseChange B S hS c).functor.map
          ((comparisonFunctor B S hS W).map m)).op ≫ j.hom)) b =
      thickeningLiftChartAppTop B S hS Z hZ c a V₁ j
        ((structureRingSheaf B S hS W).obj.map m.op b) := by
  have h1 : a.hom.app (op V₁) ((structureRingSheaf B S hS W).obj.map m.op b) =
      (thickeningLiftRingSheaf B S hS Z c).obj.map m.op (a.hom.app (op V₂) b) :=
    ConcreteCategory.congr_hom (a.hom.naturality m.op) b
  have h2 : ∀ y : ToType ((thickeningLiftRingSheaf B S hS Z c).obj.obj (op V₂)),
      (pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
            (structureRingSheafInverseImage B S hS
              (subspaceInclusion B S hS X Z))).hom.app (op V₁)
          ((thickeningLiftRingSheaf B S hS Z c).obj.map m.op y) =
        (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
          (smallEtaleDirectImage B S hS c)
          ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z))).obj
            (structureRingSheafInverseImage B S hS
              (subspaceInclusion B S hS X Z)))).obj.map m.op
          ((pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
            (structureRingSheafInverseImage B S hS
              (subspaceInclusion B S hS X Z))).hom.app (op V₂) y) := fun y ↦
    ConcreteCategory.congr_hom
      ((pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
        (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z))).hom.naturality m.op) y
  refine (bijective_thickeningRingUnit_app B S hS Z hZ j.right).1 ?_
  refine (thickeningRingUnit_thickeningLiftChartAppTop B S hS Z hZ c a V₂
    (StructuredArrow.mk (((spacesBaseChange B S hS c).functor.map
      ((comparisonFunctor B S hS W).map m)).op ≫ j.hom)) b).trans ?_
  refine Eq.trans ?_ (thickeningRingUnit_thickeningLiftChartAppTop B S hS Z hZ c a V₁ j
    ((structureRingSheaf B S hS W).obj.map m.op b)).symm
  refine Eq.trans ?_ (congrArg ((directImageChartProjection B S hS c V₁ j).app
    ((sheafCompose (SmallEtale.topology B S hS X.1)
      (CategoryTheory.forget RingCat.{u})).obj
      ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS X Z))).obj
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))))
    ((congrArg ((pushforwardRingSheafCompInv B S hS (subspaceInclusion B S hS X Z) c
        (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z))).hom.app (op V₁)) h1).trans
      (h2 (a.hom.app (op V₂) b)))).symm
  exact (directImageChartProjection_chart_map B S hS c m j _ _).symm

/-! ### The morphism of schemes attached to a comorphism, under refinement -/

/-- **The morphism of charts attached to `a` at an index refined by a chart of `X` above it is
the morphism attached at the given index, precomposed with the morphism of charts.**  Both act
on regular functions as the map attached at the given index followed by restriction, by
`AlgebraicGeometry.Space.thickeningLiftChartAppTop_index_comp`, and a morphism into an affine
scheme is determined by its map of regular functions. -/
theorem thickeningLiftChartHom_index_comp (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    {j j' : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op}
    (φ : j ⟶ j')
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))] :
    thickeningLiftChartHom B S hS Z hZ c a V j' =
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map φ.right.unop) ≫
        thickeningLiftChartHom B S hS Z hZ c a V j :=
  AlgebraicGeometry.ext_of_isAffine (by
    rw [Scheme.Hom.comp_appTop, thickeningLiftChartHom_appTop, thickeningLiftChartHom_appTop]
    exact CommRingCat.hom_ext (RingHom.ext fun b ↦
      thickeningLiftChartAppTop_index_comp B S hS Z hZ c a V φ b))

/-- **The morphism of charts attached to `a` over a chart `V₁` of `W` above `V₂`, at the
base-changed index, is the morphism attached over `V₂` followed by the morphism of charts.**
Both act on regular functions as restriction from `V₂` to `V₁` followed by the map attached over
`V₁`, by `AlgebraicGeometry.Space.thickeningLiftChartAppTop_chart_map`, and a morphism into an
affine scheme is determined by its map of regular functions. -/
theorem thickeningLiftChartHom_chart_map (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {V₁ V₂ : SmallEtale B S hS W.1} (m : V₁ ⟶ V₂)
    (j : StructuredArrow (op (chartBaseChange B S hS c V₁)) (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V₁))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V₂))] :
    thickeningLiftChartHom B S hS Z hZ c a V₂ (StructuredArrow.mk
        (((spacesBaseChange B S hS c).functor.map
          ((comparisonFunctor B S hS W).map m)).op ≫ j.hom)) =
      thickeningLiftChartHom B S hS Z hZ c a V₁ j ≫
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS W.1).map m) :=
  AlgebraicGeometry.ext_of_isAffine (by
    rw [Scheme.Hom.comp_appTop, thickeningLiftChartHom_appTop, thickeningLiftChartHom_appTop]
    exact CommRingCat.hom_ext (RingHom.ext fun b ↦
      thickeningLiftChartAppTop_chart_map B S hS Z hZ c a m j b))

/-! ### The morphism of the site attached to a comorphism, under refinement -/

/-- **The morphism of the site attached to `a` at a refined index is the one at the given index,
precomposed with the morphism of charts.**  The functor to schemes is faithful on the morphisms
over `S`, and the two underlying morphisms of schemes agree by
`AlgebraicGeometry.Space.thickeningLiftChartHom_index_comp`. -/
theorem thickeningLiftChartSiteHom_index_comp (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    {j j' : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op}
    (φ : j ⟶ j')
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a V j)
    (ψ' : (SmallEtale.toOver B S hS X.1).obj j'.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V)
    (hψ' : (BigFppfOver.toScheme B S hS).map ψ' = thickeningLiftChartHom B S hS Z hZ c a V j') :
    ψ' = (SmallEtale.toOver B S hS X.1).map φ.right.unop ≫ ψ :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, hψ, hψ']
    exact thickeningLiftChartHom_index_comp B S hS Z hZ c a V φ)

/-- **The morphism of the site attached to `a` over a chart `V₁` of `W` above `V₂`, at the
base-changed index, is the one over `V₂` followed by the morphism of charts.**  The functor to
schemes is faithful on the morphisms over `S`, and the two underlying morphisms of schemes agree
by `AlgebraicGeometry.Space.thickeningLiftChartHom_chart_map`. -/
theorem thickeningLiftChartSiteHom_chart_map (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {V₁ V₂ : SmallEtale B S hS W.1} (m : V₁ ⟶ V₂)
    (j : StructuredArrow (op (chartBaseChange B S hS c V₁)) (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V₁))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V₂))]
    (ψ₁ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V₁)
    (hψ₁ : (BigFppfOver.toScheme B S hS).map ψ₁ = thickeningLiftChartHom B S hS Z hZ c a V₁ j)
    (ψ₂ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V₂)
    (hψ₂ : (BigFppfOver.toScheme B S hS).map ψ₂ =
      thickeningLiftChartHom B S hS Z hZ c a V₂ (StructuredArrow.mk
        (((spacesBaseChange B S hS c).functor.map
          ((comparisonFunctor B S hS W).map m)).op ≫ j.hom))) :
    ψ₂ = ψ₁ ≫ (SmallEtale.toOver B S hS W.1).map m :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, hψ₁, hψ₂]
    exact thickeningLiftChartHom_chart_map B S hS Z hZ c a m j)

/-- **The section of `W` over the chart of `X` attached to `a` and an affine chart diagram does
not depend on the chart of `W` the diagram passes through.**  Replacing the chart `V₂` of `W` by
a chart `V₁` above it, with the index base changed, replaces the morphism of charts by its
composite with `V₁ ⟶ V₂`, which is a morphism of charts of `W` and so composes with the
structure morphism of `V₂` to that of `V₁`. -/
theorem yoneda_map_thickeningLiftChartSiteHom_chart_map (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W) (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {V₁ V₂ : SmallEtale B S hS W.1} (m : V₁ ⟶ V₂)
    (j : StructuredArrow (op (chartBaseChange B S hS c V₁)) (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V₁))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V₂))]
    (ψ₁ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V₁)
    (hψ₁ : (BigFppfOver.toScheme B S hS).map ψ₁ = thickeningLiftChartHom B S hS Z hZ c a V₁ j)
    (ψ₂ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V₂)
    (hψ₂ : (BigFppfOver.toScheme B S hS).map ψ₂ =
      thickeningLiftChartHom B S hS Z hZ c a V₂ (StructuredArrow.mk
        (((spacesBaseChange B S hS c).functor.map
          ((comparisonFunctor B S hS W).map m)).op ≫ j.hom))) :
    yoneda.map ψ₂ ≫ V₂.1.hom = yoneda.map ψ₁ ≫ V₁.1.hom := by
  have hw : yoneda.map ((SmallEtale.toOver B S hS W.1).map m) ≫ V₂.1.hom = V₁.1.hom :=
    CostructuredArrow.w _
  rw [thickeningLiftChartSiteHom_chart_map B S hS Z hZ c a m j ψ₁ hψ₁ ψ₂ hψ₂,
    CategoryTheory.Functor.map_comp, Category.assoc, hw]

/-- **The section of `W` over the chart of `X` attached to `a` and an affine chart diagram is
compatible with restriction to a chart of `X` above it.** -/
theorem yoneda_map_thickeningLiftChartSiteHom_index_comp (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W) (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    {j j' : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op}
    (φ : j ⟶ j')
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a V j)
    (ψ' : (SmallEtale.toOver B S hS X.1).obj j'.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V)
    (hψ' : (BigFppfOver.toScheme B S hS).map ψ' = thickeningLiftChartHom B S hS Z hZ c a V j') :
    yoneda.map ψ' ≫ V.1.hom =
      yoneda.map ((SmallEtale.toOver B S hS X.1).map φ.right.unop) ≫ yoneda.map ψ ≫ V.1.hom := by
  rw [thickeningLiftChartSiteHom_index_comp B S hS Z hZ c a V φ ψ hψ ψ' hψ',
    CategoryTheory.Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Space

end
