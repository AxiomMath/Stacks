module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion

/-!
# Lifting a valuation ring through a flat morphism of algebraic stacks (Stacks 0DN5)

Let `f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic stacks over `S` and let `Spec A ⟶ 𝒴` be a
1-morphism with `A` a valuation ring. If the closed point of `Spec A` is carried to a point of
`|𝒴|` lying in the image of `|𝒳| ⟶ |𝒴|`, then there are an extension of valuation rings
`A ⟶ A'` and a 1-morphism `Spec A' ⟶ 𝒳` making the square

```text
Spec A' ⟶ 𝒳
   |         |
   v         v
Spec A  ⟶ 𝒴
```

2-commute.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_valuationRing_extension_lift_of_isFlat`:
  **Stacks 0DN5**.

## Implementation notes

The spectrum of the valuation ring enters as an object `V` of the big fppf site together with an
isomorphism `e` of its underlying scheme with `Spec A`, and as an algebraic stack through
`AlgebraicGeometry.Stack.schemeStack`; the valuation-ring extension is
`AlgebraicGeometry.ValuationRing.IsExtension` of **Stacks 0ASG**. The closed point of `Spec A` is
presented by a field-valued point `p` of the algebraic space `V` represents whose underlying
scheme point is the closed point, which is the interface of the flat lifting statement for
algebraic spaces, **Stacks 089F**. The point of `|𝒴|` it determines is read off through
`AlgebraicGeometry.Stack.spacePointMap`, the canonical map of **Stacks 04XL** from the points of
an algebraic space to the points of a stack charted by it.

The proof is the source's. Base change along `Spec A ⟶ 𝒴` keeps the morphism flat (**Stacks
06PY**), and **Stacks 04XH** puts a point of the base change over the closed point, so one may
assume the target is `Spec A`. A smooth surjective chart of the base change by a scheme `U`
(**Stacks 04YF**, in the form
`AlgebraicGeometry.Stack.exists_smooth_surjective_schemeStack`) is again flat over `Spec A`, by
**Stacks 075U** against **Stacks 04TA** and composition of flat 1-morphisms (**Stacks 06PX**).
Source and target of that composite are representable by the algebraic spaces `U` and `V`
represent, so **Stacks 06FM** reads it as a flat morphism `h_U ⟶ h_V` of algebraic spaces, and
Stacks 089F applies to it. The chosen point of the chart is produced by surjectivity of the
chart on points, transported to a point of the representing algebraic space by
`AlgebraicGeometry.Stack.bijective_spacePointMap_representing`; that its image is the class of
`p` follows from injectivity of the same comparison at `V`, together with
`AlgebraicGeometry.Stack.spacePointMap_representing_naturality`.

The lift that Stacks 089F returns is a morphism of representable presheaves, hence `yoneda.map`
of a morphism of the site, and the 2-commutativity of the resulting square is assembled from the
comparison 2-cell of the 2-fibre product square and two applications of the uniqueness clause of
**Stacks 04SW**: a 1-morphism between algebraic stacks of schemes of the site is 2-isomorphic to
the one induced by a morphism of the site as soon as the two have the same representing map
(`AlgebraicGeometry.Stack.nonempty_unique_twoIso_of_representingMap_eq`).

## References

* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 089F](https://stacks.math.columbia.edu/tag/089F)
* [Stacks Project, Tag 0ASG](https://stacks.math.columbia.edu/tag/0ASG)
* [Stacks Project, Tag 0DN5](https://stacks.math.columbia.edu/tag/0DN5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The uniqueness clause of Stacks 04SW for the algebraic stacks of two schemes of the site.**
A 1-morphism `Φ` between the categories fibred in groupoids of two objects `U`, `V` of the big
fppf site of `S` whose representing map is `yoneda.map k`, for a morphism `k : U ⟶ V` of the
site, is 2-isomorphic to the 1-morphism induced by `k`. -/
private theorem nonempty_twoIso_schemeFibredCategoryMap {U V : BigFppfOver B S hS}
    (Φ : schemeFibredCategory B S hS U ⟶ schemeFibredCategory B S hS V) (k : U ⟶ V)
    (h : representingMap B S hS (schemeFibredCategory B S hS U)
      (schemeFibredCategory B S hS V) (yoneda.obj U) (yoneda.obj V)
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (PresheafOfCategories.sliceElementsEquivalenceOver V) Φ = yoneda.map k) :
    Nonempty (Φ ≅ schemeFibredCategoryMap B S hS k) := by
  obtain ⟨hu⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS
    (schemeFibredCategory B S hS U) (schemeFibredCategory B S hS V)
    (yoneda.obj U) (yoneda.obj V)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (PresheafOfCategories.sliceElementsEquivalenceOver V)
    (h.trans (representingMap_schemeFibredCategoryMap B S hS k).symm)
  exact ⟨hu.default⟩

/-- **Stacks 0DN5.** Let `f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic stacks over `S` and let
`g : Spec A ⟶ 𝒴` be a 1-morphism out of the spectrum of a valuation ring `A`, presented as an
object `V` of the big fppf site of `S` with an isomorphism `e` of its underlying scheme with
`Spec A`. If the closed point of `Spec A` — presented by a field-valued point `p` of the
algebraic space `V` represents — is carried by `g` to a point of `|𝒴|` in the image of
`|𝒳| ⟶ |𝒴|`, then there are an extension of valuation rings `ι : A ⟶ A'`, an object `V'` of the
site with an isomorphism `e'` of its underlying scheme with `Spec A'` over `Spec ι`, and a
1-morphism `Spec A' ⟶ 𝒳` whose composite with `f` is 2-isomorphic to `Spec A' ⟶ Spec A ⟶ 𝒴`. -/
@[stacks 0DN5]
theorem exists_valuationRing_extension_lift_of_isFlat
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsFlat B S hS f)
    (V : BigFppfOver B S hS)
    (e : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of A))
    (g : schemeStack.{u, w} B S hS V ⟶ 𝒴)
    (p : Space.FieldValuedPoint B S hS (yoneda.obj V))
    (hp : e.hom ((BigFppfOver.toScheme B S hS).map p.value
      (IsLocalRing.closedPoint p.carrier)) = IsLocalRing.closedPoint A)
    (himage : ∃ x : points B S hS 𝒳, pointsMap B S hS f x =
      pointsMap B S hS g (spacePointMap B S hS (yoneda.obj V)
        (schemeFibredCategory B S hS V) (schemeRepChart B S hS V)
        (p.class B S hS (yoneda.obj V)))) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : ValuationRing A') (ι : A →+* A'),
      ValuationRing.IsExtension ι ∧
      ∃ (V' : BigFppfOver B S hS)
        (e' : (BigFppfOver.toScheme B S hS).obj V' ≅ Spec (.of A'))
        (j : V' ⟶ V) (lift : schemeStack.{u, w} B S hS V' ⟶ 𝒳),
        (BigFppfOver.toScheme B S hS).map j ≫ e.hom =
            e'.hom ≫ Spec.map (CommRingCat.ofHom ι) ∧
          Nonempty (lift ≫ f ≅ schemeStackMap.{u, w} B S hS j ≫ g) := by
  classical
  obtain ⟨x, hx⟩ := himage
  set pV := spacePointMap B S hS (yoneda.obj V) (schemeFibredCategory B S hS V)
    (schemeRepChart B S hS V) (p.class B S hS (yoneda.obj V)) with hpV
  -- Base change along `Spec A ⟶ 𝒴`, and a point of the base change over the closed point.
  set P := twoFibreProductSquareAlgebraicStacks B S hS g f with hPdef
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f
  have hflatP : IsFlat B S hS P.fst := isFlat_baseChange B S hS f g P hP hf
  obtain ⟨z, hzP, -⟩ := exists_point_of_isTwoFibreProduct B S hS P hP pV x hx.symm
  -- A smooth surjective chart of the base change by a scheme of the site.
  obtain ⟨U, atlas, hatlasSmooth, hatlasSurj⟩ :=
    exists_smooth_surjective_schemeStack.{u, w} B S hS P.pt
  have hflatChart : IsFlat B S hS (atlas ≫ P.fst) :=
    isFlat_comp B S hS atlas P.fst (isFlat_of_isSmooth B S hS atlas hatlasSmooth) hflatP
  -- The chart, read as a morphism of the representing algebraic spaces.
  set chartMap := representingMap B S hS (schemeFibredCategory B S hS U)
    (schemeFibredCategory B S hS V) (yoneda.obj U) (yoneda.obj V)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (PresheafOfCategories.sliceElementsEquivalenceOver V) (atlas ≫ P.fst).hom with hchartMap
  have hflatSpace : Space.IsFlat B S hS chartMap :=
    (hasPropertyOnSomeSmoothDiagram_iff_represented B S hS
      (fun _ _ k => Space.IsFlat B S hS k) (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
      (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS U)
      (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS V) (yoneda.obj U) (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (PresheafOfCategories.sliceElementsEquivalenceOver V)
      (atlas ≫ P.fst).hom).1
      ((isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS (atlas ≫ P.fst)).1 hflatChart)
  -- A point of the representing algebraic space of the chart over the closed point.
  obtain ⟨zU, hzU⟩ := hatlasSurj z
  obtain ⟨y, hy⟩ := (bijective_spacePointMap_representing B S hS (yoneda.obj U)
    (schemeFibredCategory B S hS U)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)).surjective zU
  have hyV : Space.pointsMap B S hS (yoneda.obj U) chartMap y = p.class B S hS (yoneda.obj V) := by
    refine (bijective_spacePointMap_representing B S hS (yoneda.obj V)
      (schemeFibredCategory B S hS V)
      (PresheafOfCategories.sliceElementsEquivalenceOver V)).injective ?_
    have hnat : spacePointMap B S hS (yoneda.obj V) (schemeFibredCategory B S hS V)
          (schemeRepChart B S hS V) (Space.pointsMap B S hS (yoneda.obj U) chartMap y) =
        pointsMap B S hS (atlas ≫ P.fst)
          (spacePointMap B S hS (yoneda.obj U) (schemeFibredCategory B S hS U)
            (schemeRepChart B S hS U) y) :=
      spacePointMap_representing_naturality B S hS (yoneda.obj U) (yoneda.obj V)
        (schemeFibredCategory B S hS U) (schemeFibredCategory B S hS V)
        (PresheafOfCategories.sliceElementsEquivalenceOver U)
        (PresheafOfCategories.sliceElementsEquivalenceOver V) (atlas ≫ P.fst).hom y
    rw [hnat, hy, pointsMap_comp, Function.comp_apply, hzU, hzP]
  -- The lifting statement for algebraic spaces.
  obtain ⟨A', hring, hdomain, hvaluation, ι, hι, V', e', j, lift₀, hj, hlift⟩ :=
    Space.exists_valuationRing_extension_lift_of_isFlat (B := B) (S := S) (hS := hS) A
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
      chartMap hflatSpace V e (𝟙 (yoneda.obj V)) p hp
      ⟨y, hyV.trans (congrFun (Space.pointsMap_id B S hS (yoneda.obj V)) _).symm⟩
  -- The lift, read as a morphism of the site.
  set l := yoneda.preimage lift₀ with hldef
  set chartArrow := yoneda.preimage chartMap with hchartArrow
  have hl : yoneda.map l = lift₀ := yoneda.map_preimage lift₀
  have hc : yoneda.map chartArrow = chartMap := yoneda.map_preimage chartMap
  have hlj : l ≫ chartArrow = j := by
    refine yoneda.map_injective ?_
    rw [yoneda.map_comp, hl, hc, hlift]
    exact Category.comp_id _
  -- The two comparison 2-cells.
  obtain ⟨ηchart⟩ := nonempty_twoIso_schemeFibredCategoryMap B S hS
    (atlas ≫ P.fst).hom chartArrow (hchartMap ▸ hc.symm)
  obtain ⟨ηcomp⟩ := nonempty_twoIso_schemeFibredCategoryMap B S hS
    (schemeFibredCategoryMap B S hS l ≫ schemeFibredCategoryMap B S hS chartArrow) j (by
      rw [representingMap_comp (𝒜 := schemeFibredCategory B S hS V')
        (ℬ := schemeFibredCategory B S hS U) (𝒞 := schemeFibredCategory B S hS V) B S hS
        (yoneda.obj V') (yoneda.obj U) (yoneda.obj V)
        (PresheafOfCategories.sliceElementsEquivalenceOver V')
        (PresheafOfCategories.sliceElementsEquivalenceOver U)
        (PresheafOfCategories.sliceElementsEquivalenceOver V),
        representingMap_schemeFibredCategoryMap, representingMap_schemeFibredCategoryMap,
        ← yoneda.map_comp, hlj])
  refine ⟨A', hring, hdomain, hvaluation, ι, hι, V', e', j,
    (schemeStackMap.{u, w} B S hS l ≫ atlas) ≫ P.snd, hj, ?_⟩
  have hchartIso : atlas ≫ P.fst ≅ schemeStackMap.{u, w} B S hS chartArrow :=
    Bicategory.InducedBicategory.isoMk ηchart
  have hcompIso :
      schemeStackMap.{u, w} B S hS l ≫ schemeStackMap.{u, w} B S hS chartArrow ≅
        schemeStackMap.{u, w} B S hS j :=
    Bicategory.InducedBicategory.isoMk ηcomp
  have hfstIso : (schemeStackMap.{u, w} B S hS l ≫ atlas) ≫ P.fst ≅
      schemeStackMap.{u, w} B S hS j :=
    Bicategory.associator (schemeStackMap.{u, w} B S hS l) atlas P.fst ≪≫
      Bicategory.whiskerLeftIso (schemeStackMap.{u, w} B S hS l) hchartIso ≪≫ hcompIso
  exact ⟨Bicategory.associator (schemeStackMap.{u, w} B S hS l ≫ atlas) P.snd f ≪≫
    Bicategory.whiskerLeftIso (schemeStackMap.{u, w} B S hS l ≫ atlas) P.iso.symm ≪≫
    (Bicategory.associator (schemeStackMap.{u, w} B S hS l ≫ atlas) P.fst g).symm ≪≫
    Bicategory.whiskerRightIso hfstIso g⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
