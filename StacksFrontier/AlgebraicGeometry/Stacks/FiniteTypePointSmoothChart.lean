module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme

/-!
# Finite type points and smooth scheme charts (Stacks 06FX)

Stacks 06FX states that a point `x` of an algebraic stack `𝒳` over `S` satisfies two equivalent
conditions:

1. there is a 1-morphism `Spec k ⟶ 𝒳` which is locally of finite type and represents `x`;
2. there is a scheme `U`, a closed point `u ∈ U` and a smooth 1-morphism `φ : U ⟶ 𝒳` with
  `|φ|(u) = x`.

Condition (1) is `AlgebraicGeometry.Stack.IsFiniteTypePoint` of **Stacks 06FY**. This
file proves both implications.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth`: a smooth
  1-morphism of algebraic stacks over `S` is locally of finite type.
* `AlgebraicGeometry.Stack.isFiniteTypePoint_schemeStack_of_isClosed`: a point of the algebraic
  stack of a scheme `U` of the site whose point of `U` is closed is a finite type point.
* `AlgebraicGeometry.Stack.isFiniteTypePoint_of_exists_isClosed_smoothChart`: **Stacks 06FX**,
  condition (2) implies condition (1).
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_representingMap`: a 1-morphism of algebraic
  stacks over `S` which is locally of finite type induces a morphism locally of finite type on
  representing algebraic spaces.
* `AlgebraicGeometry.Stack.exists_isClosed_smoothChart_of_isFiniteTypePoint`: **Stacks 06FX**,
  condition (1) implies condition (2).

## Implementation notes

The point of `U` that a point of the algebraic stack of `U` names is read through
`AlgebraicGeometry.Stack.pointsHomeomorphScheme`, the identification of the point space of
Stacks 04XL of a represented algebraic stack with the topological space of the representing
scheme; this is the datum the statement of Stacks 06FX calls `u ∈ U`.

The implication reduces to the two statements before it. A point of the algebraic stack of `U`
lying over a closed point `u` is represented by the field-valued point whose arrow of the site is
`AlgebraicGeometry.Scheme.fromSpecResidueField` at `u`: that arrow is a closed immersion, hence
locally of finite type, and local finite type passes from the arrow to the 1-morphism it induces
through the relative property of **Stacks 03YK** and the equivalence of conditions (1) and (2) of
**Stacks 06FM**, since the induced 1-morphism is representable by algebraic spaces. The
1-morphism of the field-valued point is 2-isomorphic to that induced 1-morphism, by the 2-Yoneda
lemma (**Stacks 004B**) in the form `CategoryTheory.Functor.TwoYoneda.liftBased_overMap_iso`, and
local finite type is invariant under a 2-isomorphism. **Stacks 06G0** then carries the finite type
point along the smooth chart, which is locally of finite type because smoothness is the
existential smooth-diagram test of Stacks 06FM at smoothness of morphisms of algebraic spaces,
which implies local finite type by **Stacks 06MH**.

The converse implication is the source's argument. A surjective smooth scheme chart
`a : U ⟶ 𝒳` of **Stacks 026O** is base changed along the 1-morphism `Spec k ⟶ 𝒳` of a
field-valued representative of `x`; the apex of that 2-fibre product square (**Stacks 04T2**) is
representable by an algebraic space `R` (**Stacks 0300**), whose structural morphism to `U` is
locally of finite type by **Stacks 06FU** and whose structural morphism to `Spec k` is surjective
by **Stacks 04ZU**. So `R` is nonempty and **Stacks 06EK** gives a finite type point of it, whose
image in `U` is a finite type point by **Stacks 06EI** and hence, by **Stacks 06EF**, the image
of a closed point of a scheme étale over `U`. That scheme is the required chart: an étale
morphism is smooth and smooth 1-morphisms compose (**Stacks 075V**), and the 2-cell of the square
carries its closed point to `x` because the algebraic stack of the spectrum of a field has one
point.

The auxiliary `locallyOfFiniteType_fromSpecResidueField` repeats the first step of a `private`
declaration of `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType`, which is
not visible from here, and is `private` here too.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 06EF](https://stacks.math.columbia.edu/tag/06EF)
* [Stacks Project, Tag 06EI](https://stacks.math.columbia.edu/tag/06EI)
* [Stacks Project, Tag 06EK](https://stacks.math.columbia.edu/tag/06EK)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06FY](https://stacks.math.columbia.edu/tag/06FY)
* [Stacks Project, Tag 06G0](https://stacks.math.columbia.edu/tag/06G0)
* [Stacks Project, Tag 06MH](https://stacks.math.columbia.edu/tag/06MH)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Auxiliaries -/

/-- The morphism from the spectrum of the residue field at a closed point of a scheme is locally
of finite type: it is a closed immersion. -/
private theorem locallyOfFiniteType_fromSpecResidueField {Z : Scheme.{u}} {z : Z}
    (hz : IsClosed ({z} : Set Z)) : LocallyOfFiniteType (Z.fromSpecResidueField z) :=
  have : _root_.AlgebraicGeometry.IsClosedImmersion (Z.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz
  inferInstance

/-- A field-valued point of the presheaf represented by a scheme `U` of the site, read as a
field-valued point of the algebraic stack of `U`: its object is the arrow of the site that the
section names. -/
@[implicit_reducible] private def slicePoint (U : BigFppfOver B S hS)
    (q : Space.FieldValuedPoint B S hS (yoneda.obj U)) :
    FieldValuedPoint B S hS (schemeFibredCategory B S hS U).val where
  carrier := q.carrier
  field := q.field
  base := q.siteObject B S hS (yoneda.obj U)
  isSpec := Iso.refl _
  obj := Over.mk q.value
  «over» := rfl

private theorem fieldValuedPointSchemeArrow_slicePoint (U : BigFppfOver B S hS)
    (q : Space.FieldValuedPoint B S hS (yoneda.obj U)) :
    fieldValuedPointSchemeArrow B S hS (slicePoint B S hS U q) = q.value :=
  Category.id_comp q.value

/-- The morphism of schemes underlying the arrow of the site that the residue field
representative of a point of a scheme of the site names. -/
private theorem toScheme_map_fieldValuedPointSchemeArrow_slicePoint (U : BigFppfOver B S hS)
    (y : (BigFppfOver.toScheme B S hS).obj U) :
    (BigFppfOver.toScheme B S hS).map
        (fieldValuedPointSchemeArrow B S hS
          (slicePoint B S hS U (Space.schemePointRepresentative B S hS U y))) =
      ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField y := by
  rw [fieldValuedPointSchemeArrow_slicePoint, Space.toScheme_map_schemePointRepresentative_value]

private theorem toScheme_map_fieldValuedPointSchemeArrow_slicePoint_apply
    (U : BigFppfOver B S hS) (y : (BigFppfOver.toScheme B S hS).obj U)
    (w : (BigFppfOver.toScheme B S hS).obj
      (slicePoint B S hS U (Space.schemePointRepresentative B S hS U y)).base) :
    (BigFppfOver.toScheme B S hS).map
        (fieldValuedPointSchemeArrow B S hS
          (slicePoint B S hS U (Space.schemePointRepresentative B S hS U y))) w = y := by
  rw [toScheme_map_fieldValuedPointSchemeArrow_slicePoint]
  exact Scheme.fromSpecResidueField_apply _ _

/-! ### Smooth 1-morphisms are locally of finite type -/

/-- **A smooth 1-morphism of algebraic stacks over `S` is locally of finite type.** Smoothness
(**Stacks 075U**) is the existential smooth-diagram test of **Stacks 06FM** at smoothness of
morphisms of algebraic spaces, whose top horizontal morphism is then locally of finite type by
**Stacks 06MH**; local finite type of morphisms of algebraic spaces is smooth local on the
source-and-target, so Stacks 06FM upgrades that to the universal test, which is **Stacks 06FS**,
part (1). -/
theorem AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsSmooth B S hS f) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS f := by
  refine (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    𝒳.property 𝒴.property f.hom).2 ?_
  obtain ⟨U, V, hU, hV, a, b, h, hη, ha, hsurj, hb, hsm⟩ := hf
  exact ⟨U, V, hU, hV, a, b, h, hη, ha, hsurj, hb,
    Space.isLocallyOfFiniteType_of_isSmooth B S hS hsm⟩

/-! ### Finite type points of a represented algebraic stack -/

/-- **The 1-morphism of a field-valued point of a represented algebraic stack is locally of finite
type as soon as the arrow of the site it names is.**

The arrow induces a 1-morphism of represented algebraic stacks which is representable by algebraic
spaces, so the relative property of **Stacks 03YK** at local finite type holds for it and the
equivalence of conditions (1) and (2) of **Stacks 06FM** turns that into the universal
smooth-diagram test. The 1-morphism of the field-valued point is 2-isomorphic to it by the
2-Yoneda lemma, and local finite type is invariant under a 2-isomorphism. -/
theorem isLocallyOfFiniteType_fieldValuedPointStackMorphism_schemeStack
    (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (schemeFibredCategory B S hS U).val)
    (hp : Space.IsLocallyOfFiniteType B S hS
      (yoneda.map (fieldValuedPointSchemeArrow B S hS p))) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (fieldValuedPointStackMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS U) p) := by
  let _instbc : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S hS g.hom) :=
    Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  let _instlt : MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S hS g.hom)
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hrel := hasRelativeProperty_schemeFibredCategoryMap.{u, u} B S hS
    (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) =>
      Space.IsLocallyOfFiniteType B S hS g.hom)
    (fieldValuedPointSchemeArrow B S hS p) hp
  have hsome := hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
    (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
    (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS U)
    (schemeFibredCategoryMap B S hS (fieldValuedPointSchemeArrow B S hS p))
    (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS
      (fieldValuedPointSchemeArrow B S hS p))
    hrel
  have hevery : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (Bicategory.InducedBicategory.mkHom
        (schemeFibredCategoryMap B S hS (fieldValuedPointSchemeArrow B S hS p)) :
        schemeStack.{u, w} B S hS p.base ⟶ schemeStack.{u, w} B S hS U) :=
    (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS p.base)
      (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS U) _).2 hsome
  exact AlgebraicStacks.isLocallyOfFiniteType_of_twoIso B S hS
    (Bicategory.InducedBicategory.isoMk
      (CategoryTheory.Functor.TwoYoneda.liftBased_overMap_iso (V := U)
        (Functor.Fiber.mk (a := p.obj) p.over)
        (schemeFibredCategory B S hS U).isFiberedInGroupoids).symm)
    hevery

/-- **The point of `U` underlying the point of the algebraic stack of `U` represented by a
field-valued point** is the image, along the arrow of the site the field-valued point names, of
the point of the algebraic stack of its base named by the identity.

The 1-morphism of the field-valued point carries the identity point of the algebraic stack of its
base to the point it represents, and it is 2-isomorphic to the 1-morphism the arrow induces, whose
action on points is the action of the underlying morphism of schemes. -/
theorem pointsHomeomorphScheme_pointClass (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (schemeFibredCategory B S hS U).val) :
    pointsHomeomorphScheme B S hS U
        (pointClass B S hS (schemeFibredCategory B S hS U).val
          (schemeFibredCategory B S hS U).property p) =
      (BigFppfOver.toScheme B S hS).map (fieldValuedPointSchemeArrow B S hS p)
        (pointsHomeomorphScheme B S hS p.base
          (pointClass B S hS (schemeFibredCategory B S hS p.base).val
            (schemeFibredCategory B S hS p.base).property p.atBase)) := by
  calc pointsHomeomorphScheme B S hS U
        (pointClass B S hS (schemeFibredCategory B S hS U).val
          (schemeFibredCategory B S hS U).property p)
      = pointsHomeomorphScheme B S hS U
          (pointClass B S hS (schemeFibredCategory B S hS U).val
            (schemeFibredCategory B S hS U).property
            (fieldValuedPointMap B S hS (schemeFibredCategory B S hS p.base).val
              (fieldValuedPointMorphism B S hS (schemeFibredCategory B S hS U) p).hom
              p.atBase)) :=
        congrArg (fun y => pointsHomeomorphScheme B S hS U y)
          (pointClass_fieldValuedPointMap_atBase B S hS
            (schemeFibredCategory B S hS U) p).symm
    _ = pointsHomeomorphScheme B S hS U
          (pointClass B S hS (schemeFibredCategory B S hS U).val
            (schemeFibredCategory B S hS U).property
            (fieldValuedPointMap B S hS (schemeFibredCategory B S hS p.base).val
              (schemeFibredCategoryMap B S hS
                (fieldValuedPointSchemeArrow B S hS p)).hom p.atBase)) :=
        congrArg (fun y => pointsHomeomorphScheme B S hS U y)
          (pointClass_fieldValuedPointMap_eq_of_basedNatTrans B S hS
            (schemeFibredCategory B S hS p.base).val
            (schemeFibredCategory B S hS U).property
            (CategoryTheory.Functor.TwoYoneda.liftBased_overMap_iso (V := U)
              (Functor.Fiber.mk (a := p.obj) p.over)
              (schemeFibredCategory B S hS U).isFiberedInGroupoids).hom
            p.atBase)
    _ = (BigFppfOver.toScheme B S hS).map (fieldValuedPointSchemeArrow B S hS p)
          (pointsHomeomorphScheme B S hS p.base
            (pointClass B S hS (schemeFibredCategory B S hS p.base).val
              (schemeFibredCategory B S hS p.base).property p.atBase)) :=
        pointsHomeomorphScheme_naturality B S hS
          (fieldValuedPointSchemeArrow B S hS p)
          (pointClass B S hS (schemeFibredCategory B S hS p.base).val
            (schemeFibredCategory B S hS p.base).property p.atBase)

/-- **A point of the algebraic stack of a scheme `U` of the site lying over a closed point of `U`
is a finite type point.**

It is represented by the field-valued point of the residue field at that closed point, whose arrow
of the site is `AlgebraicGeometry.Scheme.fromSpecResidueField`; that arrow is a closed immersion,
hence locally of finite type, and so is the 1-morphism it determines. -/
theorem isFiniteTypePoint_schemeStack_of_isClosed (U : BigFppfOver B S hS)
    (z : points B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property)
    (hz : IsClosed ({pointsHomeomorphScheme B S hS U z} :
      Set ((BigFppfOver.toScheme B S hS).obj U))) :
    IsFiniteTypePoint.{u, w} B S hS (schemeStack.{u, w} B S hS U) z := by
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  refine ⟨slicePoint B S hS U
    (Space.schemePointRepresentative B S hS U (pointsHomeomorphScheme B S hS U z)), ?_, ?_⟩
  · exact (pointsHomeomorphScheme B S hS U).injective
      ((pointsHomeomorphScheme_pointClass B S hS U _).trans
        (toScheme_map_fieldValuedPointSchemeArrow_slicePoint_apply B S hS U _ _))
  · refine isLocallyOfFiniteType_fieldValuedPointStackMorphism_schemeStack.{u, w} B S hS U _ ?_
    rw [Space.isLocallyOfFiniteType_yoneda_map_iff,
      toScheme_map_fieldValuedPointSchemeArrow_slicePoint]
    exact locallyOfFiniteType_fromSpecResidueField hz

/-! ### Stacks 06FX -/

/-- **Stacks 06FX, condition (2) implies condition (1).** Let `x` be a point of an algebraic stack
`𝒳` over `S`. If there are a scheme `U` of the site, a closed point of `U`, and a smooth
1-morphism from the algebraic stack of `U` to `𝒳` carrying that point to `x`, then some
field-valued point representing `x` has a 1-morphism `Spec k ⟶ 𝒳` which is locally of finite
type, i.e. `x` is a finite type point in the sense of Stacks 06FY.

The point of `U` is the closed point, a smooth 1-morphism is locally of finite type, and
Stacks 06G0 carries finite type points along a 1-morphism locally of finite type. -/
@[stacks 06FX "condition (2) implies condition (1)"]
theorem isFiniteTypePoint_of_exists_isClosed_smoothChart
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (h : ∃ (U : BigFppfOver B S hS) (φ : schemeStack.{u, w} B S hS U ⟶ 𝒳)
        (z : points B S hS (schemeFibredCategory B S hS U).val
          (schemeFibredCategory B S hS U).property),
        AlgebraicStacks.IsSmooth B S hS φ ∧
          IsClosed ({pointsHomeomorphScheme B S hS U z} :
            Set ((BigFppfOver.toScheme B S hS).obj U)) ∧
          pointsMap B S hS (schemeFibredCategory B S hS U).val
            (schemeFibredCategory B S hS U).property 𝒳.val.property φ.hom.hom z = x) :
    IsFiniteTypePoint.{u, w} B S hS 𝒳 x := by
  obtain ⟨U, φ, z, hφ, hclosed, hzx⟩ := h
  have hmaps := mapsTo_finiteTypePoints.{u, w} B S hS φ
    (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS φ hφ)
    (isFiniteTypePoint_schemeStack_of_isClosed.{u, w} B S hS U z hclosed)
  rwa [hzx] at hmaps

/-- **A 1-morphism of algebraic stacks over `S` which is locally of finite type induces a morphism
locally of finite type on representing algebraic spaces.** This is the forward half of the third
assertion of **Stacks 06FM** at local finite type; Stacks 06FS, part (1) is stated over the
universal smooth-diagram criterion, which agrees with the existential one because local finite
type is smooth local on the source-and-target. -/
theorem isLocallyOfFiniteType_representingMap
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) :
    Space.IsLocallyOfFiniteType B S hS
      (representingMap B S hS 𝒳.val 𝒴.val F G eF eG f.hom) :=
  (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      𝒳.property 𝒴.property F G hF hG eF eG f.hom).mp
    ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      𝒳.property 𝒴.property f.hom).1 hf)

/-- **The algebraic stack of the spectrum of the field of a field-valued point has exactly the
point that the field-valued point names.** The scheme of the point's base is isomorphic to the
spectrum of a field, hence has at most one point, and so has the algebraic stack of that base
by **Stacks 04XL**. -/
private theorem eq_pointClass_atBase (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (y : points B S hS (schemeFibredCategory B S hS p.base).val
      (schemeFibredCategory B S hS p.base).property) :
    y = pointClass B S hS (schemeFibredCategory B S hS p.base).val
      (schemeFibredCategory B S hS p.base).property p.atBase :=
  have := subsingleton_points_schemeStack.{u, w} B S hS p.base
    (Scheme.homeoOfIso p.isSpec).injective.subsingleton
  Subsingleton.elim _ _

/-! ### Stacks 06FX, condition (1) implies condition (2) -/

/-- **The projection of a 2-fibre product square over a scheme chart and a field-valued point,
read on points.** Every point of an algebraic space representing the apex of such a square is
carried by the chart to the point of `𝒳` that the field-valued point names.

The 2-cell of the square identifies the two composites, and the other projection lands in the
algebraic stack of the spectrum of a field, which has only one point. No fibre-product property
is needed, only 2-commutativity. -/
private theorem pointsMap_representingMap_fst_eq
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (p : FieldValuedPoint B S hS 𝒳.val.val)
    (U₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳)
    (Q : Bicategory.TwoCommSq a (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p))
    (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eR : StacksRepresentableCFG.EquivalenceOver
      Q.pt.val.val.p (presheafOfCategories (R ⋙ typeToCat)).p)
    (v : Space.points B S hS R) :
    pointsMap B S hS (schemeFibredCategory B S hS U₀).val
        (schemeFibredCategory B S hS U₀).property 𝒳.val.property a.hom.hom
        (representedChartPointMap B S hS U₀
          (Space.pointsMap B S hS R
            (representingMap B S hS Q.pt.val (schemeStack.{u, w} B S hS U₀).val R
              (yoneda.obj U₀) eR (representedChart B S hS U₀) Q.fst.hom) v)) =
      pointClass B S hS 𝒳.val.val 𝒳.val.property p := by
  have hsq := Stack.pointsMap_eq_of_basedNatTrans B S hS Q.pt.val.val Q.pt.val.property
    𝒳.val.property Q.iso.hom.hom.hom
  calc pointsMap B S hS (schemeFibredCategory B S hS U₀).val
          (schemeFibredCategory B S hS U₀).property 𝒳.val.property a.hom.hom
          (representedChartPointMap B S hS U₀ (Space.pointsMap B S hS R _ v))
      = pointsMap B S hS (schemeFibredCategory B S hS U₀).val
          (schemeFibredCategory B S hS U₀).property 𝒳.val.property a.hom.hom
          (pointsMap B S hS Q.pt.val.val Q.pt.val.property
            (schemeFibredCategory B S hS U₀).property Q.fst.hom.hom
            (spacePointMap B S hS R Q.pt.val
              (representingEquivalence B S hS R Q.pt.val eR).functor v)) :=
        congrArg _ (spacePointMap_representing_naturality B S hS R (yoneda.obj U₀) Q.pt.val
          (schemeStack.{u, w} B S hS U₀).val eR (representedChart B S hS U₀) Q.fst.hom v)
    _ = pointsMap B S hS Q.pt.val.val Q.pt.val.property 𝒳.val.property (Q.fst ≫ a).hom.hom
          (spacePointMap B S hS R Q.pt.val
            (representingEquivalence B S hS R Q.pt.val eR).functor v) :=
        Stack.pointsMap_comp B S hS Q.pt.val.val Q.pt.val.property
          (schemeFibredCategory B S hS U₀).property 𝒳.val.property Q.fst.hom.hom a.hom.hom _
    _ = pointsMap B S hS Q.pt.val.val Q.pt.val.property 𝒳.val.property
          (Q.snd ≫ fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p).hom.hom
          (spacePointMap B S hS R Q.pt.val
            (representingEquivalence B S hS R Q.pt.val eR).functor v) := congrFun hsq _
    _ = pointsMap B S hS (schemeFibredCategory B S hS p.base).val
          (schemeFibredCategory B S hS p.base).property 𝒳.val.property
          (fieldValuedPointMorphism B S hS 𝒳.val p).hom
          (pointsMap B S hS Q.pt.val.val Q.pt.val.property
            (schemeFibredCategory B S hS p.base).property Q.snd.hom.hom
            (spacePointMap B S hS R Q.pt.val
              (representingEquivalence B S hS R Q.pt.val eR).functor v)) :=
        (Stack.pointsMap_comp B S hS Q.pt.val.val Q.pt.val.property
          (schemeFibredCategory B S hS p.base).property 𝒳.val.property Q.snd.hom.hom
          (fieldValuedPointMorphism B S hS 𝒳.val p).hom _).symm
    _ = pointsMap B S hS (schemeFibredCategory B S hS p.base).val
          (schemeFibredCategory B S hS p.base).property 𝒳.val.property
          (fieldValuedPointMorphism B S hS 𝒳.val p).hom
          (pointClass B S hS (schemeFibredCategory B S hS p.base).val
            (schemeFibredCategory B S hS p.base).property p.atBase) :=
        congrArg _ (eq_pointClass_atBase.{u, w} B S hS 𝒳 p _)
    _ = pointClass B S hS 𝒳.val.val 𝒳.val.property p :=
        pointClass_fieldValuedPointMap_atBase B S hS 𝒳.val p

/-- **The apex of the 2-fibre product square of a scheme chart and a field-valued point of an
algebraic stack over `S` is representable by an algebraic space.** This is **Stacks 0300**: the
1-morphism of the field-valued point is representable by algebraic spaces because the diagonal of
`𝒳` is, and the chart is representable by an algebraic space. -/
private theorem isRepresentableByAlgebraicSpace_pointFibreProduct
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (p : FieldValuedPoint B S hS 𝒳.val.val)
    (U₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS a
        (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p)).pt.val :=
  isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
    (schemeStack.{u, w} B S hS U₀).val (schemeStack.{u, w} B S hS p.base).val
    a.hom.hom (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p).hom.hom
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS p.base)
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p).hom)
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U₀)

/-- **The projection to the chart of a 2-fibre product square over a scheme chart and a
field-valued point locally of finite type is locally of finite type**, read on representing
algebraic spaces. The projection is locally of finite type by **Stacks 06FU**, and
**Stacks 06FM** reads that on the representing algebraic spaces. -/
private theorem isLocallyOfFiniteType_representingMap_fst
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (p : FieldValuedPoint B S hS 𝒳.val.val)
    (hplft : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p))
    (U₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳)
    (Q : Bicategory.TwoCommSq a (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p))
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hR : IsAlgebraicSpace B S hS R)
    (eR : StacksRepresentableCFG.EquivalenceOver
      Q.pt.val.val.p (presheafOfCategories (R ⋙ typeToCat)).p) :
    Space.IsLocallyOfFiniteType B S hS
      (representingMap B S hS Q.pt.val (schemeStack.{u, w} B S hS U₀).val R (yoneda.obj U₀)
        eR (representedChart B S hS U₀) Q.fst.hom) :=
  isLocallyOfFiniteType_representingMap.{u, w} B S hS (𝒳 := Q.pt)
    (𝒴 := schemeStack.{u, w} B S hS U₀) R (yoneda.obj U₀) hR
    (isAlgebraicSpace_yoneda B S hS U₀) eR (representedChart B S hS U₀) Q.fst
    (AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p) a Q hQ hplft)

/-- **An algebraic space representing the apex of a 2-fibre product square over a surjective
scheme chart and a field-valued point has a point.** The other projection of the square is
surjective by **Stacks 04ZU**, hence so is the morphism it induces on representing algebraic
spaces, and the spectrum of the point's field has a point. -/
private theorem nonempty_points_representingSpace
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (p : FieldValuedPoint B S hS 𝒳.val.val)
    (U₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳)
    (hasurj : IsSurjective B S hS a)
    (Q : Bicategory.TwoCommSq a (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p))
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eR : StacksRepresentableCFG.EquivalenceOver
      Q.pt.val.val.p (presheafOfCategories (R ⋙ typeToCat)).p) :
    Nonempty (Space.points B S hS R) :=
  ⟨(isSurjective_representingMap_of_isSurjective B S hS R (yoneda.obj p.base) eR
      (representedChart B S hS p.base) Q.snd
      (isSurjective_of_isTwoFibreProduct B S hS Q hQ hasurj)
    ((Space.schemePointRepresentative B S hS p.base
      ((Scheme.homeoOfIso p.isSpec).symm (IsLocalRing.closedPoint p.carrier))).class B S hS
        (yoneda.obj p.base))).choose⟩

/-- **The 2-fibre product of a smooth surjective scheme chart of an algebraic stack over `S` with
a locally-of-finite-type field-valued point of it**, read as an algebraic space over the chart:
the three preceding statements assembled at the canonical square of **Stacks 04T2**. -/
private theorem exists_representingSpace_pointFibreProduct
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (p : FieldValuedPoint B S hS 𝒳.val.val)
    (hplft : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p))
    (U₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳)
    (hasurj : IsSurjective B S hS a) :
    ∃ (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hR : IsAlgebraicSpace B S hS R)
      (r : R ⟶ yoneda.obj U₀),
      Space.IsLocallyOfFiniteType B S hS r ∧ Nonempty (Space.points B S hS R) ∧
        ∀ v : Space.points B S hS R,
          pointsMap B S hS (schemeFibredCategory B S hS U₀).val
              (schemeFibredCategory B S hS U₀).property 𝒳.val.property a.hom.hom
              (representedChartPointMap B S hS U₀ (Space.pointsMap B S hS R r v)) =
            pointClass B S hS 𝒳.val.val 𝒳.val.property p := by
  obtain ⟨R, hR, ⟨eR⟩⟩ := isRepresentableByAlgebraicSpace_pointFibreProduct.{u, w} B S hS 𝒳 p U₀ a
  exact ⟨R, hR, _,
    isLocallyOfFiniteType_representingMap_fst.{u, w} B S hS 𝒳 p hplft U₀ a _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a _) R hR eR,
    nonempty_points_representingSpace.{u, w} B S hS 𝒳 p U₀ a hasurj _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a _) R eR,
    pointsMap_representingMap_fst_eq.{u, w} B S hS 𝒳 p U₀ a _ R eR⟩

/-- **A finite type point of an algebraic stack lifts to a finite type point of any smooth
surjective scheme chart**, along the 2-fibre product with a locally-of-finite-type field-valued
point representing it. -/
private theorem exists_isFiniteTypePoint_over_chart
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (p : FieldValuedPoint B S hS 𝒳.val.val)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hpx : pointClass B S hS 𝒳.val.val 𝒳.val.property p = x)
    (hplft : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p))
    (U₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳)
    (hasurj : IsSurjective B S hS a) :
    ∃ y : Space.points B S hS (yoneda.obj U₀),
      Space.IsFiniteTypePoint B S hS (yoneda.obj U₀) y ∧
        pointsMap B S hS (schemeFibredCategory B S hS U₀).val
          (schemeFibredCategory B S hS U₀).property 𝒳.val.property a.hom.hom
          (representedChartPointMap B S hS U₀ y) = x := by
  obtain ⟨R, hR, r, hrlft, ⟨w₀⟩, hkey⟩ :=
    exists_representingSpace_pointFibreProduct.{u, w} B S hS 𝒳 p hplft U₀ a hasurj
  obtain ⟨v, -, hvft⟩ := Space.inter_finiteTypePoints_nonempty B S hS R hR
    (T := Set.univ) isClosed_univ.isLocallyClosed ⟨w₀, Set.mem_univ _⟩
  exact ⟨Space.pointsMap B S hS R r v,
    Space.mapsTo_finiteTypePoints B S hS r hR (isAlgebraicSpace_yoneda B S hS U₀) hrlft hvft,
    (hkey v).trans hpx⟩

/-- **A finite type point of an algebraic stack over `S` is the image of a finite type point of
a smooth surjective scheme chart.** The chart is
`AlgebraicGeometry.Stack.exists_smooth_surjective_schemeStack`, and the finite type point comes
from **Stacks 06EK** on the nonempty algebraic space of
`AlgebraicGeometry.Stack.exists_representingSpace_pointFibreProduct`, whose image in the chart is
a finite type point by **Stacks 06EI**. -/
private theorem exists_smoothChart_isFiniteTypePoint
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) :
    ∃ (U : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
      (y : Space.points B S hS (yoneda.obj U)),
      AlgebraicStacks.IsSmooth B S hS a ∧
        Space.IsFiniteTypePoint B S hS (yoneda.obj U) y ∧
          pointsMap B S hS (schemeFibredCategory B S hS U).val
            (schemeFibredCategory B S hS U).property 𝒳.val.property a.hom.hom
            (representedChartPointMap B S hS U y) = x := by
  obtain ⟨p, hpx, hplft⟩ := hx
  obtain ⟨U₀, a, hasm, hasurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  obtain ⟨y, hyft, hyx⟩ :=
    exists_isFiniteTypePoint_over_chart.{u, w} B S hS 𝒳 p x hpx hplft U₀ a hasurj
  exact ⟨U₀, a, y, hasm, hyft, hyx⟩

/-- The scheme morphism underlying an étale morphism of represented presheaves is étale. -/
private theorem etale_map_preimage_of_isEtale {U V : BigFppfOver B S hS}
    (ψ : yoneda.obj V ⟶ yoneda.obj U) (hψ : Space.IsEtale B S hS ψ) :
    Etale ((BigFppfOver.toScheme B S hS).map (yoneda.preimage ψ)) :=
  (Space.presheaf_yoneda_map_etale_iff B S hS (yoneda.preimage ψ)).1
    ((Space.isEtale_iff_presheaf_of_yoneda B S hS _).1 (by rwa [yoneda.map_preimage]))

/-- **A closed point of a scheme étale over a smooth chart gives a closed smooth chart.** The
composite of the étale morphism with the chart is smooth, and carries the closed point to `x`. -/
private theorem exists_isClosed_smoothChart_of_etaleChart
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (U₀ : BigFppfOver B S hS)
    (a : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳) (hasm : AlgebraicStacks.IsSmooth B S hS a)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) (y : Space.points B S hS (yoneda.obj U₀))
    (hyx : pointsMap B S hS (schemeFibredCategory B S hS U₀).val
      (schemeFibredCategory B S hS U₀).property 𝒳.val.property a.hom.hom
      (representedChartPointMap B S hS U₀ y) = x)
    {V : BigFppfOver B S hS} (ψ : yoneda.obj V ⟶ yoneda.obj U₀)
    (t : Space.FieldValuedPoint B S hS (yoneda.obj V)) (hψ : Space.IsEtale B S hS ψ)
    (hclosed : IsClosed ({Space.schemePoint B S hS V t} :
      Set ((BigFppfOver.toScheme B S hS).obj V)))
    (hψy : Space.pointsMap B S hS (yoneda.obj V) ψ (t.class B S hS (yoneda.obj V)) = y) :
    ∃ (φ : schemeStack.{u, w} B S hS V ⟶ 𝒳)
      (z : points B S hS (schemeFibredCategory B S hS V).val
        (schemeFibredCategory B S hS V).property),
      AlgebraicStacks.IsSmooth B S hS φ ∧
        IsClosed ({pointsHomeomorphScheme B S hS V z} :
          Set ((BigFppfOver.toScheme B S hS).obj V)) ∧
        pointsMap B S hS (schemeFibredCategory B S hS V).val
          (schemeFibredCategory B S hS V).property 𝒳.val.property φ.hom.hom z = x := by
  have := etale_map_preimage_of_isEtale B S hS ψ hψ
  refine ⟨schemeStackMap.{u, w} B S hS (yoneda.preimage ψ) ≫ a,
    representedChartPointMap B S hS V (t.class B S hS (yoneda.obj V)),
    AlgebraicStacks.isSmooth_comp B S hS _ _
      (isSmooth_schemeStackMap.{u, w} B S hS (yoneda.preimage ψ) inferInstance) hasm, ?_, ?_⟩
  · rw [pointsHomeomorphScheme_representedChartPointMap]
    exact hclosed
  · calc pointsMap B S hS (schemeFibredCategory B S hS V).val
            (schemeFibredCategory B S hS V).property 𝒳.val.property
            (schemeStackMap.{u, w} B S hS (yoneda.preimage ψ) ≫ a).hom.hom
            (representedChartPointMap B S hS V (t.class B S hS (yoneda.obj V)))
        = pointsMap B S hS (schemeFibredCategory B S hS U₀).val
            (schemeFibredCategory B S hS U₀).property 𝒳.val.property a.hom.hom
            (pointsMap B S hS (schemeFibredCategory B S hS V).val
              (schemeFibredCategory B S hS V).property
              (schemeFibredCategory B S hS U₀).property
              (schemeFibredCategoryMap B S hS (yoneda.preimage ψ)).hom
              (representedChartPointMap B S hS V (t.class B S hS (yoneda.obj V)))) :=
          (Stack.pointsMap_comp B S hS (schemeFibredCategory B S hS V).val
            (schemeFibredCategory B S hS V).property
            (schemeFibredCategory B S hS U₀).property 𝒳.val.property
            (schemeFibredCategoryMap B S hS (yoneda.preimage ψ)).hom a.hom.hom _).symm
      _ = pointsMap B S hS (schemeFibredCategory B S hS U₀).val
            (schemeFibredCategory B S hS U₀).property 𝒳.val.property a.hom.hom
            (representedChartPointMap B S hS U₀ y) :=
          congrArg _ ((representedChartPointMap_naturality B S hS (yoneda.preimage ψ)
            (t.class B S hS (yoneda.obj V))).trans
            (congrArg (representedChartPointMap B S hS U₀)
              (by rw [← yoneda.map_preimage ψ] at hψy; exact hψy)))
      _ = x := hyx

/-- **Stacks 06FX, condition (1) implies condition (2).** A finite type point `x` of an algebraic
stack `𝒳` over `S` (Stacks 06FY) is the image of a closed point of a scheme of the site carrying
a smooth 1-morphism to `𝒳`.

A smooth surjective scheme chart `a : U ⟶ 𝒳` has a finite type point above `x`, and by
**Stacks 06EF** such a point is the image of a closed point of a scheme `V` étale over `U`. An
étale morphism of schemes is smooth, so the composite `V ⟶ U ⟶ 𝒳` is smooth by **Stacks 075V**,
and it carries that closed point to `x`. -/
@[stacks 06FX "condition (1) implies condition (2)"]
theorem exists_isClosed_smoothChart_of_isFiniteTypePoint
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) :
    ∃ (U : BigFppfOver B S hS) (φ : schemeStack.{u, w} B S hS U ⟶ 𝒳)
      (z : points B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property),
      AlgebraicStacks.IsSmooth B S hS φ ∧
        IsClosed ({pointsHomeomorphScheme B S hS U z} :
          Set ((BigFppfOver.toScheme B S hS).obj U)) ∧
        pointsMap B S hS (schemeFibredCategory B S hS U).val
          (schemeFibredCategory B S hS U).property 𝒳.val.property φ.hom.hom z = x := by
  obtain ⟨U₀, a, y, hasm, hyft, hyx⟩ :=
    exists_smoothChart_isFiniteTypePoint.{u, w} B S hS 𝒳 x hx
  obtain ⟨V, ψ, t, hψ, hclosed, hψy⟩ :=
    (Space.isFiniteTypePoint_iff_exists_isClosed_etaleChart B S hS (yoneda.obj U₀)
      (isAlgebraicSpace_yoneda B S hS U₀) y).1 hyft
  exact ⟨V, exists_isClosed_smoothChart_of_etaleChart.{u, w} B S hS 𝒳 U₀ a hasm x y hyx ψ t hψ
    hclosed hψy⟩

/-- **Stacks 06FX, condition (1) implies condition (2), with the chart no larger than a given
smooth surjective chart.** Let `a : U₀ ⟶ 𝒳` be a smooth surjective 1-morphism out of a scheme of
the site. Then a finite type point `x` of `𝒳` is the image of a closed point of a scheme `U` of
the site carrying a smooth 1-morphism to `𝒳` whose **size is at most that of `U₀`** and whose
underlying scheme is **affine**.

The proof of `AlgebraicGeometry.Stack.exists_isClosed_smoothChart_of_isFiniteTypePoint` run at
the given chart rather than at one chosen for the occasion, and with the affine form of
**Stacks 06EH** (`AlgebraicGeometry.Space.isFiniteTypePoint_iff_exists_isAffine_isClosed_etaleChart`)
in place of the general one: the chart it produces is then an **affine** scheme étale over `U₀`,
so it is quasi-compact and locally of finite type over `U₀`, and **Stacks 04T7**
(`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType`) bounds its size by that of `U₀`. The
affineness is recorded in the conclusion as well: the chart construction of **Stacks 06N3** reads
its slicing sequence in the global functions of the chart, and on an affine chart it may do so
with no shrinking, by
`AlgebraicGeometry.exists_global_isRegular_ofList_eq_maximalIdeal_stalk_of_unramifiedAt`.

This is the form the chart construction of **Stacks 06MF** needs: the charts it cuts out of these
are indexed by the finite type points of `𝒳`, a set which need not be below the cofinality of the
site's size cutoff, so their coproduct lies in the site by
`AlgebraicGeometry.BigFppfSite.contains_sigma_of_forall_size_le` and that asks for a bound on
their sizes which is *uniform in the point*. -/
@[stacks 06FX "condition (1) implies condition (2), with the chart's size bounded by that of a \
given smooth surjective chart"]
theorem exists_isClosed_smoothChart_size_le_of_isFiniteTypePoint
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (U₀ : BigFppfOver B S hS)
    (a : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳)
    (hasm : AlgebraicStacks.IsSmooth B S hS a) (hasurj : IsSurjective B S hS a)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) :
    ∃ (U : BigFppfOver B S hS) (φ : schemeStack.{u, w} B S hS U ⟶ 𝒳)
      (z : points B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property),
      AlgebraicStacks.IsSmooth B S hS φ ∧
        IsClosed ({pointsHomeomorphScheme B S hS U z} :
          Set ((BigFppfOver.toScheme B S hS).obj U)) ∧
        pointsMap B S hS (schemeFibredCategory B S hS U).val
          (schemeFibredCategory B S hS U).property 𝒳.val.property φ.hom.hom z = x ∧
        ((BigFppfOver.toScheme B S hS).obj U).size ≤
          ((BigFppfOver.toScheme B S hS).obj U₀).size ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj U) := by
  obtain ⟨p, hpx, hplft⟩ := hx
  obtain ⟨y, hyft, hyx⟩ :=
    exists_isFiniteTypePoint_over_chart.{u, w} B S hS 𝒳 p x hpx hplft U₀ a hasurj
  obtain ⟨V, ψ, t, hVaff, hψ, hclosed, hψy⟩ :=
    (Space.isFiniteTypePoint_iff_exists_isAffine_isClosed_etaleChart B S hS (yoneda.obj U₀)
      (isAlgebraicSpace_yoneda B S hS U₀) y).1 hyft
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hVaff
  have := etale_map_preimage_of_isEtale B S hS ψ hψ
  obtain ⟨φ, z, hφ, hz, hzx⟩ :=
    exists_isClosed_smoothChart_of_etaleChart.{u, w} B S hS 𝒳 U₀ a hasm x y hyx ψ t hψ hclosed hψy
  exact ⟨V, φ, z, hφ, hz, hzx,
    Scheme.size_le_of_locallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage ψ)), hVaff⟩



end AlgebraicGeometry.Stack

end
