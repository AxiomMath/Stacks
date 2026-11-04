module

public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureChartCompactFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureChartExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.JointlyFaithful
public import StacksFrontier.CategoryTheory.TwoFibreProduct.PrecomposeLegs
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The relation of an affine chart as a 2-fibre product on the represented object

Let `f : U ⟶ 𝒳` be a 1-morphism from the algebraic stack of an object of the site to an algebraic
stack over `S`, and let the self-intersection `ℛ = U ×_{f, 𝒳, f} U` of **Stacks 04T4** be
represented by an object `V` of the site. This file records that the square

    V ⟶ U
    ↓     ↓
    U ⟶ 𝒳

whose apex is the algebraic stack of `V` *on the nose* and whose two legs are the 1-morphisms of
the source and target morphisms `s, t : V ⟶ U` of the groupoid of Stacks 04T4 (4), is a 2-fibre
product of `(f, f)`.

This is the shape in which a quotient chart's relation data is usable as the outer square of a
pasting: the inner square of a chart fibre is a fibre product *in the site* along `t`
(`AlgebraicGeometry.Stack.isPullback_sitePullback`), so it is a square over a cospan whose legs
are `AlgebraicGeometry.Stack.schemeFibredCategoryMap`s, and a square whose apex is the canonical
2-fibre product `ℛ` cannot be glued to it.

## Main definitions

* `AlgebraicGeometry.Stack.SelfIntersection.chartHom`: the forward 1-morphism of the representing
  equivalence of the algebraic stack of an object of the site.
* `AlgebraicGeometry.Stack.SelfIntersection.relationChart`: the comparison 1-morphism from the
  algebraic stack of the representing object of `ℛ` to `ℛ`.
* `AlgebraicGeometry.Stack.SelfIntersection.relationSquareRepresented`: the square above.

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.isTwoFibreProduct_relationSquareRepresented`: it is a
  2-fibre product of `(f, f)`.
* `AlgebraicGeometry.Stack.SelfIntersection.representingMap_relationSquareRepresented_fst` and
  `..._snd`: its two legs induce the source and the target morphism of Stacks 04T4 (4).

## Implementation notes

The square is `CategoryTheory.Bicategory.TwoCommSq.precompose` of the canonical one along that
comparison, so `CategoryTheory.Bicategory.TwoCommSq.PreHom.ofPrecompose` is the pre-morphism of
squares with no 2-cell computation of its own.

The comparison `h_V ⟶ ℛ` is the forward 1-morphism of the representing equivalence of `h_V`
followed by the backward 1-morphism of the given representation of `ℛ`
(`AlgebraicGeometry.Stack.equivalenceOverInvMap`). Both are equivalences of underlying
categories, so `CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to` carries
terminality of the canonical square across it; and both induce the identity morphism of
representing presheaves — for the backward one that is
`AlgebraicGeometry.Stack.representingMap_equivalenceOverInvMap`, and for the forward one it
follows because the two compose to the *identity* 1-morphism, the unit of
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver` being the identity.

The legs of the square are read off the *swapped* canonical square, because the first projection
`pr₀` of `ℛ` induces the **target** morphism of the groupoid
(`AlgebraicGeometry.Stack.SelfIntersection.representingMap_relationSquare_fst`) while a pasting
against the fibre of `t` needs the target on the second leg.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.SelfIntersection

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The representation of the algebraic stack of the chart as an algebraic space over `S`. -/
noncomputable abbrev chartSpace (U : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩

/-! ### The forward 1-morphism of a representing chart -/

/-- The forward 1-morphism of the representing equivalence of the algebraic stack of an object of
the site: the slice over `V`, read as the category of elements of the presheaf `h_V`. It is the
inverse of `AlgebraicGeometry.Stack.equivalenceOverInvMap` at
`AlgebraicGeometry.Stack.representedChart`, on the nose. -/
noncomputable def chartHom (V : BigFppfOver B S hS) :
    schemeFibredCategory B S hS V ⟶ fibredCategory B S hS (yoneda.obj V) :=
  (CatFiberedInGroupoids.homEquivBasedFunctor _ _).symm
    ⟨(representedChart B S hS V).hom.functor, (representedChart B S hS V).hom.w⟩

/-- `AlgebraicGeometry.Stack.SelfIntersection.chartHom` followed by the backward 1-morphism of the
same representing equivalence is the identity: the unit of
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver` is the identity 2-cell. -/
theorem chartHom_comp_equivalenceOverInvMap (V : BigFppfOver B S hS) :
    chartHom V ≫ equivalenceOverInvMap B S hS (yoneda.obj V) (representedChart B S hS V) =
      𝟙 (schemeFibredCategory B S hS V) := rfl

/-- **The forward 1-morphism of a representing chart induces the identity.** Read through the
given comparison on the source and the identity comparison on the target, the morphism of
representing presheaves of **Stacks 04SW** induced by
`AlgebraicGeometry.Stack.SelfIntersection.chartHom` is the identity of `h_V`: it is a one-sided
inverse of `AlgebraicGeometry.Stack.equivalenceOverInvMap`, which induces the identity. -/
theorem representingMap_chartHom (V : BigFppfOver B S hS) :
    representingMap B S hS (schemeFibredCategory B S hS V)
        (fibredCategory B S hS (yoneda.obj V)) (yoneda.obj V) (yoneda.obj V)
        (representedChart B S hS V) (StacksRepresentableCFG.EquivalenceOver.refl _)
        (chartHom V) = 𝟙 (yoneda.obj V) := by
  have h := representingMap_comp B S hS (𝒜 := schemeFibredCategory B S hS V)
    (ℬ := fibredCategory B S hS (yoneda.obj V)) (𝒞 := schemeFibredCategory B S hS V)
    (yoneda.obj V) (yoneda.obj V) (yoneda.obj V)
    (representedChart B S hS V) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (representedChart B S hS V) (chartHom V)
    (equivalenceOverInvMap B S hS (yoneda.obj V) (representedChart B S hS V))
  rw [chartHom_comp_equivalenceOverInvMap, representingMap_id,
    representingMap_equivalenceOverInvMap, Category.comp_id] at h
  exact h.symm

/-! ### The relation square on the represented object -/

section Square

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {U V : BigFppfOver B S hS}
  (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom.hom).val.p
    (presheafOfCategories ((chartSpace V).obj ⋙ typeToCat)).p)

/-- The canonical 2-fibre product square of the cospan `(f, f)` with its two legs exchanged, so
that the first leg induces the **source** and the second the **target** morphism of the groupoid
of Stacks 04T4 (4). -/
noncomputable abbrev relationSquareSwapped : Bicategory.TwoCommSq f.hom f.hom :=
  (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom f.hom).swap

/-- **The comparison of the algebraic stack of the representing object of the self-intersection
with the self-intersection itself.** The forward 1-morphism of the representing equivalence of
`h_V` followed by the backward 1-morphism of the given representation of `ℛ`. -/
noncomputable def relationChart :
    schemeFibredCategory B S hS V ⟶
      relation B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom.hom :=
  chartHom V ≫ equivalenceOverInvMap B S hS (yoneda.obj V) eR

/-- `AlgebraicGeometry.Stack.SelfIntersection.relationChart` induces the identity morphism of
representing presheaves. -/
theorem representingMap_relationChart :
    representingMap B S hS (schemeFibredCategory B S hS V)
        (relation B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom.hom)
        (yoneda.obj V) (yoneda.obj V) (representedChart B S hS V) eR (relationChart f eR) =
      𝟙 (yoneda.obj V) := by
  have h := representingMap_comp B S hS (𝒜 := schemeFibredCategory B S hS V)
    (ℬ := fibredCategory B S hS (yoneda.obj V))
    (𝒞 := relation B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom.hom)
    (yoneda.obj V) (yoneda.obj V) (yoneda.obj V)
    (representedChart B S hS V) (StacksRepresentableCFG.EquivalenceOver.refl _) eR
    (chartHom V) (equivalenceOverInvMap B S hS (yoneda.obj V) eR)
  rw [representingMap_chartHom, representingMap_equivalenceOverInvMap, Category.id_comp] at h
  rw [show relationChart f eR =
    chartHom V ≫ equivalenceOverInvMap B S hS (yoneda.obj V) eR from rfl]
  exact h

/-- `AlgebraicGeometry.Stack.SelfIntersection.relationChart` is an equivalence of underlying
categories: it is a composite of the two 1-morphisms of representing equivalences. -/
theorem isEquivalence_relationChart : (relationChart f eR).hom.toFunctor.IsEquivalence := by
  show ((representedChart B S hS V).hom.functor ⋙ eR.inv.functor).IsEquivalence
  have := (representedChart B S hS V).isEquivalence_hom_functor
  have := eR.isEquivalence_inv_functor
  infer_instance

/-- **The relation of an affine chart as a square whose apex is a represented algebraic stack.**
The algebraic stack of the object `V` representing `ℛ = U ×_𝒳 U`, with the two legs obtained from
the projections of the swapped canonical 2-fibre product square by precomposition with
`AlgebraicGeometry.Stack.SelfIntersection.relationChart`. -/
noncomputable abbrev relationSquareRepresented : Bicategory.TwoCommSq f.hom f.hom :=
  (relationSquareSwapped f).precompose (relationChart f eR)

/-- **The relation square on the represented object is a 2-fibre product (Stacks 003Q).** The
comparison with the canonical square is an equivalence of underlying categories, and terminality
transports across it. -/
noncomputable def isTwoFibreProduct_relationSquareRepresented :
    Bicategory.IsTwoFibreProduct (relationSquareRepresented f eR) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom f.hom))
    (Bicategory.TwoCommSq.PreHom.ofPrecompose (relationSquareSwapped f) (relationChart f eR))
    (isEquivalence_relationChart f eR)

/-- Precomposing a 1-morphism out of `ℛ` with `relationChart` does not change the induced morphism
of representing presheaves. -/
private theorem representingMap_relationChart_comp
    (g : relation B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom.hom ⟶
      schemeFibredCategory B S hS U) :
    representingMap B S hS (schemeFibredCategory B S hS V) (schemeFibredCategory B S hS U)
        (yoneda.obj V) (yoneda.obj U) (representedChart B S hS V) (representedChart B S hS U)
        (relationChart f eR ≫ g) =
      representingMap B S hS _ (schemeFibredCategory B S hS U) (yoneda.obj V) (yoneda.obj U) eR
        (representedChart B S hS U) g := by
  have h := representingMap_comp B S hS (𝒜 := schemeFibredCategory B S hS V)
    (ℬ := relation B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom.hom)
    (𝒞 := schemeFibredCategory B S hS U)
    (yoneda.obj V) (yoneda.obj V) (yoneda.obj U)
    (representedChart B S hS V) eR (representedChart B S hS U) (relationChart f eR) g
  rw [representingMap_relationChart, Category.id_comp] at h
  exact h

/-- The first leg of the relation square on the represented object induces the **source**
morphism of the groupoid of Stacks 04T4 (4). -/
theorem representingMap_relationSquareRepresented_fst :
    representingMap B S hS (schemeFibredCategory B S hS V) (schemeFibredCategory B S hS U)
        (yoneda.obj V) (yoneda.obj U) (representedChart B S hS V) (representedChart B S hS U)
        (relationSquareRepresented f eR).fst =
      relationSourceMap (U := chartSpace U) (R := chartSpace V) (representedChart B S hS U) eR :=
  (representingMap_relationChart_comp f eR _).trans rfl

/-- The second leg of the relation square on the represented object induces the **target**
morphism of the groupoid of Stacks 04T4 (4). -/
theorem representingMap_relationSquareRepresented_snd :
    representingMap B S hS (schemeFibredCategory B S hS V) (schemeFibredCategory B S hS U)
        (yoneda.obj V) (yoneda.obj U) (representedChart B S hS V) (representedChart B S hS U)
        (relationSquareRepresented f eR).snd =
      relationTargetMap (U := chartSpace U) (R := chartSpace V) (representedChart B S hS U) eR :=
  (representingMap_relationChart_comp f eR _).trans rfl

/-! ### The relation square with the groupoid's own source and target as legs -/

section Pinned

variable {s t : V ⟶ U}
  (hs : yoneda.map s = relationSourceMap (U := chartSpace U) (R := chartSpace V)
    (representedChart B S hS U) eR)
  (ht : yoneda.map t = relationTargetMap (U := chartSpace U) (R := chartSpace V)
    (representedChart B S hS U) eR)

/-- **The source morphism of the groupoid induces the first leg of the relation square.** Both
1-morphisms of represented algebraic stacks induce the morphism `s` of representing presheaves, so
the uniqueness clause of **Stacks 04SW** supplies a unique 2-isomorphism between them. -/
noncomputable def relationSquareLegIsoFst :
    schemeFibredCategoryMap B S hS s ≅ (relationSquareRepresented f eR).fst :=
  (nonempty_unique_twoIso_of_representingMap_eq B S hS (schemeFibredCategory B S hS V)
    (schemeFibredCategory B S hS U) (yoneda.obj V) (yoneda.obj U)
    (representedChart B S hS V) (representedChart B S hS U)
    (f := schemeFibredCategoryMap B S hS s) (g := (relationSquareRepresented f eR).fst)
    (by rw [representingMap_schemeFibredCategoryMap,
      representingMap_relationSquareRepresented_fst, hs])).some.default

/-- **The target morphism of the groupoid induces the second leg of the relation square.** -/
noncomputable def relationSquareLegIsoSnd :
    schemeFibredCategoryMap B S hS t ≅ (relationSquareRepresented f eR).snd :=
  (nonempty_unique_twoIso_of_representingMap_eq B S hS (schemeFibredCategory B S hS V)
    (schemeFibredCategory B S hS U) (yoneda.obj V) (yoneda.obj U)
    (representedChart B S hS V) (representedChart B S hS U)
    (f := schemeFibredCategoryMap B S hS t) (g := (relationSquareRepresented f eR).snd)
    (by rw [representingMap_schemeFibredCategoryMap,
      representingMap_relationSquareRepresented_snd, ht])).some.default

/-- **The relation of an affine chart as a 2-fibre product whose legs are the source and the
target of the groupoid of Stacks 04T4 (4).** The apex is the algebraic stack of the representing
object `V` and the two legs are the 1-morphisms of represented algebraic stacks induced by `s` and
`t` *on the nose*, which is what a pasting against a fibre product in the site requires. -/
noncomputable abbrev relationSquarePinned : Bicategory.TwoCommSq f.hom f.hom :=
  (relationSquareSwapped f).precomposeLegs (relationChart f eR)
    (schemeFibredCategoryMap B S hS s) (schemeFibredCategoryMap B S hS t)
    (relationSquareLegIsoFst f eR hs) (relationSquareLegIsoSnd f eR ht)

/-- **The pinned relation square is a 2-fibre product (Stacks 003Q).** -/
noncomputable def isTwoFibreProduct_relationSquarePinned :
    Bicategory.IsTwoFibreProduct (relationSquarePinned f eR hs ht) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom f.hom))
    (Bicategory.TwoCommSq.PreHom.ofPrecomposeLegs (relationSquareSwapped f) (relationChart f eR)
      (schemeFibredCategoryMap B S hS s) (schemeFibredCategoryMap B S hS t)
      (relationSquareLegIsoFst f eR hs) (relationSquareLegIsoSnd f eR ht))
    (isEquivalence_relationChart f eR)

end Pinned

end Square

end AlgebraicGeometry.Stack.SelfIntersection

/-! ### The residue field point of a point of a chart -/

namespace AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (K : ChartGroupoid B S hS 𝒳)
  (z : Space.points B S hS (yoneda.obj K.U))

/-- **The residue field point of the object scheme of a quotient chart at a point of its object
space**, as a field-valued point of the algebraic stack of that object scheme: its base is
`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.residuePointObj` and the object it
names is `...residuePointMap`. -/
noncomputable def residueFieldValuedPoint :
    FieldValuedPoint B S hS (schemeFibredCategory B S hS K.U).val where
  carrier := ((BigFppfOver.toScheme B S hS).obj K.U).residueField
    (Space.pointsToScheme B S hS K.U z)
  base := residuePointObj K z
  isSpec := Iso.refl _
  obj := Over.mk (residuePointMap K z)
  «over» := rfl

/-- The arrow of the site named by
`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.residueFieldValuedPoint` is the
residue field point itself. -/
theorem fieldValuedPointSchemeArrow_residueFieldValuedPoint :
    fieldValuedPointSchemeArrow B S hS (residueFieldValuedPoint K z) = residuePointMap K z :=
  Category.id_comp _

/-- **The residue field point of a point of the object space represents that point.** Under the
identification of the points of the algebraic stack of the object scheme with the points of that
scheme (**Stacks 04XL**), the class of
`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.residueFieldValuedPoint` is the point
of the object space that it was built from.

The class is read on the underlying scheme by
`AlgebraicGeometry.Stack.pointsHomeomorphScheme_pointClass`, where the arrow of the site is
`AlgebraicGeometry.Scheme.fromSpecResidueField` and so sends every point of the field spectrum to
the given one. -/
theorem pointClass_residueFieldValuedPoint :
    pointClass B S hS (schemeFibredCategory B S hS K.U).val
        (schemeFibredCategory B S hS K.U).property (residueFieldValuedPoint K z) =
      representedChartPointMap B S hS K.U z := by
  let := pointTopology B S hS (schemeFibredCategory B S hS K.U)
  refine (pointsHomeomorphScheme B S hS K.U).injective ?_
  rw [pointsHomeomorphScheme_pointClass, pointsHomeomorphScheme_representedChartPointMap,
    fieldValuedPointSchemeArrow_residueFieldValuedPoint]
  exact Scheme.fromSpecResidueField_apply _ _

/-- **The residue field point of a point of the object space determines the first leg of the
chart fibre's inner square.** The 1-morphism of represented algebraic stacks induced by the
residue field point of the site is 2-isomorphic to the 1-morphism that
`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.residueFieldValuedPoint` determines by
2-Yoneda (**Stacks 004B**). -/
noncomputable def residuePointMapIso :
    schemeFibredCategoryMap B S hS (residuePointMap K z) ≅
      fieldValuedPointMorphism B S hS (schemeFibredCategory B S hS K.U)
        (residueFieldValuedPoint K z) := by
  refine Bicategory.InducedBicategory.isoMk ?_
  rw [show residuePointMap K z =
    fieldValuedPointSchemeArrow B S hS (residueFieldValuedPoint K z) from
      (fieldValuedPointSchemeArrow_residueFieldValuedPoint K z).symm]
  exact (CategoryTheory.Functor.TwoYoneda.liftBased_overMap_iso (V := K.U)
    (Functor.Fiber.mk (a := (residueFieldValuedPoint K z).obj)
      (residueFieldValuedPoint K z).over)
    (schemeFibredCategory B S hS K.U).isFiberedInGroupoids).symm

end AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid


/-! ### The quotient chart on points, at a given point of the object space -/

namespace AlgebraicGeometry.Stack.SelfIntersection

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The tautological point map of a represented algebraic stack, read through the forward
1-morphism of its representing chart.** The point of the category of elements of `h_U` named by a
point of `h_U` is the image under
`AlgebraicGeometry.Stack.SelfIntersection.chartHom` of the point of the algebraic stack of `U`
that `AlgebraicGeometry.Stack.representedChartPointMap` names.

This is `AlgebraicGeometry.Stack.spacePointMap_representing_naturality` at the 1-morphism
`AlgebraicGeometry.Stack.SelfIntersection.chartHom`, whose morphism of representing presheaves is
the identity. -/
theorem spacePointMap_id_eq_pointsMap_chartHom (U : BigFppfOver B S hS)
    (z : Space.points B S hS (yoneda.obj U)) :
    spacePointMap B S hS (yoneda.obj U) (fibredCategory B S hS (yoneda.obj U))
        (BasedFunctor.id _) z =
      pointsMap B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property
        (fibredCategory B S hS (yoneda.obj U)).property (chartHom U).hom
        (representedChartPointMap B S hS U z) := by
  have h := spacePointMap_representing_naturality B S hS (yoneda.obj U) (yoneda.obj U)
    (schemeFibredCategory B S hS U) (fibredCategory B S hS (yoneda.obj U))
    (representedChart B S hS U) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (chartHom U) z
  rw [representingMap_chartHom] at h
  rw [show Space.pointsMap B S hS (yoneda.obj U) (𝟙 (yoneda.obj U)) z = z from
    congrFun (Space.pointsMap_id B S hS (F := yoneda.obj U)) z] at h
  exact h

/-- **The quotient chart of a surjective chart, on points, at a given point of the object
space.** This is `AlgebraicGeometry.Stack.EtaleLocalStructure.pointsMap_chart_point` with the
point of the object space given rather than produced: the 1-morphism from the small model of the
quotient stack carries the point attached to `z` to the image under the chart of the point of
`|U|` that `z` names.

The proof is that of `...pointsMap_chart_point` with its choice of `z` replaced by
`AlgebraicGeometry.Stack.SelfIntersection.spacePointMap_id_eq_pointsMap_chartHom`, which
identifies the tautological point of the category of elements of `h_U` with the image of
`AlgebraicGeometry.Stack.representedChartPointMap` — the presentation's chosen equivalence of the
object fibration being `AlgebraicGeometry.Stack.representedChart` itself
(`AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionPresentation`), so that the
presentation's comparison is `AlgebraicGeometry.Stack.SelfIntersection.chartHom`. The universally
quantified form is what a consumer needs when the point of the object space is prescribed by the
rest of the construction, as it is for the fibre of the groupoid's target map over it. -/
theorem pointsMap_chart_representedChartPointMap {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {U V : BigFppfOver B S hS} (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (relation B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val f.hom.hom).val.p
      (presheafOfCategories ((chartSpace V).obj ⋙ typeToCat)).p)
    {s t : V ⟶ U}
    {c' : Deformation.composableArrows (yoneda.obj U) (yoneda.obj V) (yoneda.map s) (yoneda.map t) ⟶
      yoneda.obj V}
    {hG' : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
      ((yoneda.map t).app T) fun p => c'.app T p)}
    (φP : GroupoidInAlgebraicSpaces.Hom (Space.representedRealization s t c' hG')
      (selfIntersectionPresentation (U := chartSpace U) (R := chartSpace V)
        (representedChart B S hS U) eR 𝒳.property).groupoid)
    (hφobj : φP.toGroupoidHom.mapObjects = 𝟙 (yoneda.obj U))
    (alg : IsAlgebraicStack.{u, w} B S hS (quotientStack (Space.representedRealization s t c' hG')))
    (algP : IsAlgebraicStack.{u, w} B S hS (quotientStack
      (selfIntersectionPresentation (U := chartSpace U) (R := chartSpace V)
        (representedChart B S hS U) eR 𝒳.property).groupoid))
    (z : Space.points B S hS (yoneda.obj U)) :
    AlgebraicStacks.pointsMap B S hS
        (smallQuotientStackMap.{u, w} φP alg algP ≫ smallQuotientStackLift.{u, w}
          (selfIntersectionPresentation (U := chartSpace U) (R := chartSpace V)
            (representedChart B S hS U) eR 𝒳.property).groupoid algP
          (selfIntersectionPresentation (U := chartSpace U) (R := chartSpace V)
            (representedChart B S hS U) eR 𝒳.property).canonicalMap)
        (smallQuotientStackPoint _ alg z) =
      AlgebraicStacks.pointsMap B S hS f (representedChartPointMap B S hS U z) := by
  set p := representedChartPointMap B S hS U z with hp
  let P := selfIntersectionPresentation (U := chartSpace U) (R := chartSpace V)
    (representedChart B S hS U) eR 𝒳.property
  let can := smallQuotientStackLift.{u, w} P.groupoid algP P.canonicalMap
  let eUb : (schemeStack.{u, w} B S hS U).val.val ⥤ᵇ
      (fibredCategory B S hS (yoneda.obj U)).val :=
    ⟨P.sourcePresentation.hom.functor, P.sourcePresentation.hom.w⟩
  set y := pointsMap B S hS _ (schemeStack.{u, w} B S hS U).val.property
    (fibredCategory B S hS (yoneda.obj U)).property eUb p with hy
  have hz : spacePointMap B S hS (yoneda.obj U) (fibredCategory B S hS (yoneda.obj U))
      (BasedFunctor.id _) z = y := by
    rw [hy, hp]
    exact spacePointMap_id_eq_pointsMap_chartHom U z
  let X : (quotientStack P.groupoid) ⥤ᵇ 𝒳.val.val := P.canonicalMap
  let η : BasedNatTrans (eUb.comp (BasedFunctor.comp (quotientStackProjection P.groupoid) X))
      f.hom.hom :=
    { toNatTrans := P.extends_f.1.hom
      isHomLift' := fun a => P.extends_f.2 a }
  have hR : AlgebraicStacks.pointsMap B S hS f p =
      pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
        (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property
        (BasedFunctor.comp (quotientStackProjection P.groupoid) X) y := by
    rw [hy]
    show pointsMap B S hS _ _ _ f.hom.hom p = _
    rw [← pointsMap_eq_of_basedNatTrans B S hS _ _ _ η, ← pointsMap_comp]
  have hL := pointsMap_smallQuotientStackLift_point.{u, w} P.groupoid algP P.canonicalMap
    (Space.pointsMap B S hS _ φP.toGroupoidHom.mapObjects z)
  have hid : Space.pointsMap B S hS
      (Space.representedRealization s t c' hG').toGroupoidInFunctors.objects
      φP.toGroupoidHom.mapObjects z = z := by
    rw [hφobj]
    exact congrFun (Space.pointsMap_id B S hS (F := yoneda.obj U)) z
  refine (congrFun (AlgebraicStacks.pointsMap_comp B S hS
    (smallQuotientStackMap.{u, w} φP alg algP) can) _).trans ?_
  rw [Function.comp_apply, pointsMap_smallQuotientStackMap_point.{u, w} φP alg algP z, hR, ← hz]
  exact hL.trans (congrArg (fun w => pointsMap B S hS _ _ _
    (BasedFunctor.comp (quotientStackProjection P.groupoid) X)
    (spacePointMap B S hS _ _ (BasedFunctor.id _) w)) hid)

end AlgebraicGeometry.Stack.SelfIntersection


/-! ### The quotient chart of a surjective chart, with its relation square -/

namespace AlgebraicGeometry.Stack.EtaleLocalStructure

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The quotient chart of a surjective chart, together with the presentation of its arrow
scheme as a 2-fibre product.** This is
`AlgebraicGeometry.Stack.EtaleLocalStructure.exists_chartGroupoid_of_isSurjective` with the chart
`U ⟶ 𝒴` and the representation `eR` of the self-intersection `U ×_𝒴 U` by the chart's arrow scheme
returned as part of the existential, and with three extra conclusions: the square with apex the
algebraic stack of the chart's arrow scheme `V` and legs the 1-morphisms induced by the source and
target `s, t : V ⟶ U` is a 2-fibre product of the cospan `(U ⟶ 𝒴, U ⟶ 𝒴)`; `K.s` and `K.t` are
the source and target morphisms of **Stacks 04T4 (4)** read through `eR`; and the 1-morphism out of
the small model of the quotient stack acts on a *prescribed* point of the object space as the chart
does.

Returning the chart rather than taking it from the context is what lets `eR` be stated for `K.U`:
the quotient chart is built from a representation of the self-intersection of the chart, and a
`ChartGroupoid` carries no equation identifying its object scheme with any object of the site
fixed in advance.

Neither conclusion can be recovered from
`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid` alone: the structure records `V`, `s`
and `t` but no 2-fibre-product property of them, and the only general statement of that kind in
the tree (**Stacks 04M9**,
`AlgebraicGeometry.Space.QuotientAtlas.isTwoFibreProduct_arrowSelfSquare`) lives in the lifted
2-category `CategoryTheory.CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}`, from which there is no
transport to `AlgebraicGeometry.Stack.AlgebraicStacks.{u, w}`. The proof is therefore
`...exists_chartGroupoid_of_isSurjective` re-run with the representation `eR` of the relation and
the two identities `yoneda.map s = s`, `yoneda.map t = t` of **Stacks 04T4 (4)** *retained* rather
than discarded, which is what
`AlgebraicGeometry.Stack.SelfIntersection.isTwoFibreProduct_relationSquarePinned` consumes; the
duplicated part is the assembly of the structure's fields, which has no content of its own.

The point conclusion is universally quantified over the point of the object space, where
`...exists_chartGroupoid_of_isSurjective` produces one point for each point of `|U|`: the fibre of
the groupoid's target map is formed at a *given* point of the object space, so the quasi-compact
field-valued representative has to be compared at that same point. It is
`AlgebraicGeometry.Stack.SelfIntersection.pointsMap_chart_representedChartPointMap`. -/
theorem exists_chartGroupoid_relationSquare_of_isSurjective {𝒴 : AlgebraicStacks.{u, w} B S hS}
    {U : BigFppfOver B S hS} (g : schemeStack.{u, w} B S hS U ⟶ 𝒴)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hsurj : IsSurjective B S hS g) (hflat : AlgebraicStacks.IsFlat B S hS g)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (hlqf : IsLocallyQuasiFinite B S hS g.hom) (hQ : IsQuasiDMOver B S hS 𝒴)
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒴.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒴).hom)) :
    ∃ (K : ChartGroupoid B S hS 𝒴) (chart : schemeStack.{u, w} B S hS K.U ⟶ 𝒴)
      (eR : StacksRepresentableCFG.EquivalenceOver
        (SelfIntersection.relation B S hS (schemeStack.{u, w} B S hS K.U).val 𝒴.val
          chart.hom.hom).val.p
        (presheafOfCategories ((SelfIntersection.chartSpace K.V).obj ⋙ typeToCat)).p)
      (γ : schemeFibredCategoryMap B S hS K.s ≫ chart.hom ≅
        schemeFibredCategoryMap B S hS K.t ≫ chart.hom)
      (_hsq : Bicategory.IsTwoFibreProduct
        (⟨schemeFibredCategory B S hS K.V, schemeFibredCategoryMap B S hS K.s,
            schemeFibredCategoryMap B S hS K.t, γ⟩ :
          Bicategory.TwoCommSq chart.hom chart.hom)),
      IsSurjective B S hS chart ∧
      yoneda.map K.s = SelfIntersection.relationSourceMap
          (U := SelfIntersection.chartSpace K.U) (R := SelfIntersection.chartSpace K.V)
          (representedChart B S hS K.U) eR ∧
      yoneda.map K.t = SelfIntersection.relationTargetMap
          (U := SelfIntersection.chartSpace K.U) (R := SelfIntersection.chartSpace K.V)
          (representedChart B S hS K.U) eR ∧
      ∀ z : Space.points B S hS (yoneda.obj K.U),
        AlgebraicStacks.pointsMap B S hS K.map (K.point z) =
          AlgebraicStacks.pointsMap B S hS chart (representedChartPointMap B S hS K.U z) := by
  classical
  obtain ⟨V, ⟨eR₀⟩⟩ := exists_representation_relation g hQ hΔ
  let Uₛ : AlgebraicSpaces B S hS := SelfIntersection.chartSpace U
  let Rₛ : AlgebraicSpaces B S hS := SelfIntersection.chartSpace V
  let eU : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS U).val.val.p
      (presheafOfCategories (Uₛ.obj ⋙ typeToCat)).p := representedChart B S hS U
  let eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeStack.{u, w} B S hS U).val 𝒴.val g.hom.hom).val.p
      (presheafOfCategories (Rₛ.obj ⋙ typeToCat)).p := eR₀
  have hrep := isRepresentableByAlgebraicSpaces_schemeStack_hom B S hS g
  have hflatP := (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) (schemeStack.{u, w} B S hS U).property
    𝒴.property g.hom hrep).1 hflat
  have hlfpP := (hasPropertyOnEverySmoothDiagram_iff_relative.{u, u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    (schemeStack.{u, w} B S hS U).property 𝒴.property g.hom hrep).1 hlfp
  have hsurjP := (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS g hrep).1 hsurj
  obtain ⟨E⟩ := SelfIntersection.nonempty_isEquivalenceOver_canonicalMap eU eR 𝒴.property
    (fun T y hy G hG he => ⟨hsurjP T y hy G hG he, hflatP T y hy G hG he,
      hlfpP T y hy G hG he⟩)
  let P := SelfIntersection.selfIntersectionPresentation eU eR 𝒴.property
  obtain ⟨s, t, c', hG', hs, ht, φ, hφobj, hφfull, hφfaith⟩ :=
    exists_representedRealizationHom B S hS (SelfIntersection.relationSourceMap eU eR)
      (SelfIntersection.relationTargetMap eU eR)
      (SelfIntersection.compositionLaw eU eR (SelfIntersection.isFiberedInSetoids_source eU))
      (SelfIntersection.nonempty_pointwiseGroupoid eU eR
        (SelfIntersection.isFiberedInSetoids_source eU))
  obtain ⟨hsFl, htFl⟩ := SelfIntersection.isFlat_relationSource_and_relationTarget B S hS
    (schemeStack.{u, w} B S hS U).val 𝒴.val g.hom Uₛ Rₛ eU eR hrep hflatP
  obtain ⟨hsL, htL⟩ :=
    SelfIntersection.isLocallyOfFinitePresentation_relationSource_and_relationTarget B S hS
      (schemeStack.{u, w} B S hS U).val 𝒴.val g.hom Uₛ Rₛ eU eR hrep hlfpP
  have : (Space.locallyQuasiFiniteProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hsQ := SelfIntersection.prop_relationSource B S hS (schemeStack.{u, w} B S hS U).val 𝒴.val
    g.hom Uₛ Rₛ eU eR (Space.locallyQuasiFiniteProperty B S hS) hrep hlqf
  have hsSep := isSeparated_source_pointGroupoid g Rₛ eR hU hΔ
  have htSep := isSeparated_target_pointGroupoid g Rₛ eR hU hΔ
  change Space.IsFlat B S hS (SelfIntersection.relationSourceMap eU eR) at hsFl
  change Space.IsFlat B S hS (SelfIntersection.relationTargetMap eU eR) at htFl
  change Space.IsLocallyOfFinitePresentation B S hS (SelfIntersection.relationSourceMap eU eR)
    at hsL
  change Space.IsLocallyOfFinitePresentation B S hS (SelfIntersection.relationTargetMap eU eR)
    at htL
  change Space.IsLocallyQuasiFinite B S hS (SelfIntersection.relationSourceMap eU eR) at hsQ
  change Space.IsSeparated B S hS (SelfIntersection.relationSourceMap eU eR) at hsSep
  change Space.IsSeparated B S hS (SelfIntersection.relationTargetMap eU eR) at htSep
  have hPflat_s := hsFl
  have hPflat_t := htFl
  have hPlfp_s := hsL
  have hPlfp_t := htL
  rw [← hs] at hsFl hsL hsQ hsSep
  rw [← ht] at htFl htL htSep
  have flat_s := (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    Flat.isEtaleLocalOnSourceAndTarget s).1 hsFl
  have flat_t := (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    Flat.isEtaleLocalOnSourceAndTarget t).1 htFl
  have lfp_s := (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget s).1 hsL
  have lfp_t := (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget t).1 htL
  obtain ⟨lft_s, lqf_s⟩ := (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    isEtaleLocalOnSourceAndTarget_locallyOfFiniteType_inf_locallyQuasiFinite s).1 hsQ
  have lft_t : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map t) := by
    have := lfp_t
    infer_instance
  have sep_s := (Space.isSeparated_yoneda_map_iff B S hS s).1 hsSep
  have sep_t := (Space.isSeparated_yoneda_map_iff B S hS t).1 htSep
  have : Flat (Space.representedGroupoidScheme s t c' hG').source.left := flat_s
  have : Flat (Space.representedGroupoidScheme s t c' hG').target.left := flat_t
  have : LocallyOfFinitePresentation (Space.representedGroupoidScheme s t c' hG').source.left :=
    lfp_s
  have : LocallyOfFinitePresentation (Space.representedGroupoidScheme s t c' hG').target.left :=
    lfp_t
  have alg : IsAlgebraicStack.{u, w} B S hS
      (quotientStack (Space.representedRealization s t c' hG')) :=
    Stacks.Groupoids.GroupoidScheme.isAlgebraicStack_quotientStack_realization.{u, w} B hS _ _ _
  have algP : IsAlgebraicStack.{u, w} B S hS (quotientStack P.groupoid) :=
    isAlgebraicStack_quotientStack_of_flat P.groupoid hPflat_s hPflat_t hPlfp_s hPlfp_t
  let φP : GroupoidInAlgebraicSpaces.Hom (Space.representedRealization s t c' hG') P.groupoid := φ
  have hrep₃ := isRepresentableByAlgebraicSpaces_quotientStackMap_of_faithful.{u, w} φP alg algP
    (faithful_quotientStackMap_of_evaluation_faithful φP hφfaith)
  have hobjFlat : Space.IsFlat B S hS φP.toGroupoidHom.mapObjects := by
    rw [hφobj, ← yoneda.map_id]
    exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Flat.isEtaleLocalOnSourceAndTarget (𝟙 U)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have hobjLfp : Space.IsLocallyOfFinitePresentation B S hS φP.toGroupoidHom.mapObjects := by
    rw [hφobj, ← yoneda.map_id]
    exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget (𝟙 U)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have het₃ := isRelativelyEtale_smallQuotientStackMap.{u, w} φP alg algP hrep₃
    (hasRelativeProperty_etale_quotientStackMap_of_full_of_faithful φP hφfull hφfaith
      hobjFlat hobjLfp hPflat_s hPlfp_s hrep₃)
  have hcan : P.canonicalMap.toFunctor.IsEquivalence :=
    (CategoryTheory.Equivalence.mk P.canonicalMap.toFunctor E.inv E.unitIso.symm
      E.counitIso).isEquivalence_functor
  let can := smallQuotientStackLift.{u, w} P.groupoid algP P.canonicalMap
  have hcanEq := isEquivalence_smallQuotientStackLift.{u, w} P.groupoid algP P.canonicalMap
  obtain ⟨hFF⟩ := nonempty_fullyFaithful_smallQuotientStackMap.{u, w} φP alg algP
    (nonempty_fullyFaithful_quotientStackMap B S hS φP hφfull hφfaith)
  have hFFmap : (CatFiberedInGroupoids.homFunctor
      (smallQuotientStackMap.{u, w} φP alg algP ≫ can).hom).FullyFaithful :=
    hFF.comp (Functor.FullyFaithful.ofFullyFaithful (CatFiberedInGroupoids.homFunctor can.hom))
  exact ⟨{
      U := U
      V := V
      s := s
      t := t
      c := c'
      hG := hG'
      isAffine_U := hU
      flat_s := flat_s
      lfp_s := lfp_s
      flat_t := flat_t
      lfp_t := lfp_t
      separated_s := sep_s
      separated_t := sep_t
      lft_s := lft_s
      lft_t := lft_t
      lqf_s := lqf_s
      alg := alg
      map := smallQuotientStackMap.{u, w} φP alg algP ≫ can
      etale := isRelativelyEtale_comp_of_isEquivalence B S hS _ can.hom hcanEq het₃
      full := hFFmap.full
      faithful := hFFmap.faithful }, g, eR,
    (SelfIntersection.relationSquarePinned g eR hs ht).iso,
    SelfIntersection.isTwoFibreProduct_relationSquarePinned g eR hs ht, hsurj, hs, ht,
    SelfIntersection.pointsMap_chart_representedChartPointMap g eR φP hφobj alg algP⟩

end AlgebraicGeometry.Stack.EtaleLocalStructure

end
