module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestriction

/-!
# Zariski opens of an étale chart along a morphism of charts

Let `F` be a presheaf on the big fppf site of `S` and let `g : V ⟶ U` be a morphism of étale
charts of `F`, with underlying morphism of schemes `chartSchemeMap g : chartScheme V ⟶
chartScheme U`.  For a Zariski open `O` of the larger chart scheme, its preimage
`chartSchemeMap g ⁻¹ᵁ O` is a Zariski open of the smaller one, and the restriction of
`chartSchemeMap g` to those opens is again a morphism of étale charts of `F`.

That assignment is what makes `AlgebraicGeometry.Space.openChartFunctor`, and with it the
restriction of a module to a chart, functorial in the chart as well as in the open: it is a
natural transformation from the preimage functor followed by the open charts of the smaller
chart to the open charts of the larger one.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeMap` names the morphism of schemes underlying a morphism
  of étale charts.
* `AlgebraicGeometry.Space.openSubSchemeHomOfRestrict`,
  `AlgebraicGeometry.Space.openSubHomOfRestrict`: the restriction of a morphism of the big
  fppf site to an open of the target and its preimage, read in `Sch_κ` and in the big fppf
  category over `S`.
* `AlgebraicGeometry.Space.openChartRestrict` is the induced morphism of étale charts
  `openChart V (chartSchemeMap g ⁻¹ᵁ O) ⟶ openChart U O`.
* `AlgebraicGeometry.Space.openChartRestrictNatTrans` assembles it into a natural
  transformation `Opens.map (chartSchemeMap g).base ⋙ openChartFunctor V ⟶ openChartFunctor U`.

## Main results

* `AlgebraicGeometry.Space.openSubHomOfRestrict_comp_openSubHom`: the restriction is a
  morphism over the ambient objects, which is `AlgebraicGeometry.morphismRestrict_ι`.
* `AlgebraicGeometry.Space.openChartRestrict_comp_openChartInclusion`: the triangle of the
  induced morphism of charts over the inclusions of the opens.
* `AlgebraicGeometry.Space.openChartRestrict_openChartHomOfLE`: naturality in the open.

## Implementation notes

The morphism of schemes is `AlgebraicGeometry.morphismRestrict`, written `f ∣_ O`, and every
compatibility proved here reduces, after cancelling the monomorphism `O.ι`, to
`AlgebraicGeometry.morphismRestrict_ι`.  Nothing uses that the charts are étale: the whole file
is about the open subobjects of an object of the big fppf site and the triangle over `F`, and
the étale hypothesis enters only through the ambient category
`AlgebraicGeometry.Space.SmallEtale`.

The naturality statement is phrased with `CategoryTheory.Functor.op`-free data — a natural
transformation of functors out of `(chartScheme U).Opens` — so that it can be whiskered on
either side when it is applied to presheaves of modules.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

variable {B S hS F} in
/-- The morphism of schemes underlying a morphism of étale charts of `F`. -/
abbrev chartSchemeMap {U V : SmallEtale B S hS F} (g : V ⟶ U) :
    chartScheme V ⟶ chartScheme U :=
  (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map g)

variable {B S hS F} in
/-- The triangle of a morphism of étale charts over `F`. -/
theorem yoneda_map_toOver_map_comp_hom {U V : SmallEtale B S hS F} (g : V ⟶ U) :
    yoneda.map ((SmallEtale.toOver B S hS F).map g) ≫ U.obj.hom = V.obj.hom :=
  ((SmallEtale.inclusion B S hS F).map g).w

/-! ### Restricting a morphism of the site to an open and its preimage -/

variable {B S hS F} in
/-- The morphism of `Sch_κ` underlying `AlgebraicGeometry.Space.openSubHomOfRestrict`: the
restriction of a morphism to an open of its target and the preimage of that open. -/
noncomputable def openSubSchemeHomOfRestrict {A A' : BigFppfOver B S hS} (σ : A' ⟶ A)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    (openSub A' ((BigFppfOver.toScheme B S hS).map σ ⁻¹ᵁ O)).left ⟶ (openSub A O).left :=
  ObjectProperty.homMk ((BigFppfOver.toScheme B S hS).map σ ∣_ O)

variable {B S hS F} in
/-- The underlying morphism of schemes of
`AlgebraicGeometry.Space.openSubSchemeHomOfRestrict` is the restricted morphism. -/
theorem inclusion_map_openSubSchemeHomOfRestrict {A A' : BigFppfOver B S hS} (σ : A' ⟶ A)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    B.inclusion.map (openSubSchemeHomOfRestrict σ O) =
      (BigFppfOver.toScheme B S hS).map σ ∣_ O :=
  rfl

variable {B S hS F} in
/-- `AlgebraicGeometry.Space.openSubSchemeHomOfRestrict` followed by the inclusion of the open
is the inclusion of its preimage followed by the morphism. -/
theorem openSubSchemeHomOfRestrict_comp_left {A A' : BigFppfOver B S hS} (σ : A' ⟶ A)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    openSubSchemeHomOfRestrict σ O ≫ (openSubHom A O).left =
      (openSubHom A' ((BigFppfOver.toScheme B S hS).map σ ⁻¹ᵁ O)).left ≫ σ.left := by
  apply B.inclusion.map_injective
  rw [B.inclusion.map_comp, B.inclusion.map_comp,
    inclusion_map_openSubSchemeHomOfRestrict]
  change _ ≫ (BigFppfOver.toScheme B S hS).map (openSubHom A O) =
    (BigFppfOver.toScheme B S hS).map
        (openSubHom A' ((BigFppfOver.toScheme B S hS).map σ ⁻¹ᵁ O)) ≫
      (BigFppfOver.toScheme B S hS).map σ
  rw [toScheme_map_openSubHom, toScheme_map_openSubHom]
  exact morphismRestrict_ι _ O

variable {B S hS F} in
/-- The restriction of a morphism of the big fppf category over `S` to an open of its target
and the preimage of that open. -/
noncomputable def openSubHomOfRestrict {A A' : BigFppfOver B S hS} (σ : A' ⟶ A)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    openSub A' ((BigFppfOver.toScheme B S hS).map σ ⁻¹ᵁ O) ⟶ openSub A O :=
  Over.homMk (openSubSchemeHomOfRestrict σ O) (by
    change openSubSchemeHomOfRestrict σ O ≫ (openSubHom A O).left ≫ A.hom =
      (openSubHom A' ((BigFppfOver.toScheme B S hS).map σ ⁻¹ᵁ O)).left ≫ A'.hom
    rw [← Category.assoc, openSubSchemeHomOfRestrict_comp_left, Category.assoc,
      Over.w σ])

variable {B S hS F} in
/-- `AlgebraicGeometry.Space.openSubHomOfRestrict` is a morphism over the two ambient
objects. -/
theorem openSubHomOfRestrict_comp_openSubHom {A A' : BigFppfOver B S hS} (σ : A' ⟶ A)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    openSubHomOfRestrict σ O ≫ openSubHom A O =
      openSubHom A' ((BigFppfOver.toScheme B S hS).map σ ⁻¹ᵁ O) ≫ σ :=
  Over.OverMorphism.ext (openSubSchemeHomOfRestrict_comp_left σ O)

/-! ### Restricting a morphism of étale charts to an open and its preimage -/

/-- The morphism of étale charts of `F` induced by a morphism of charts `g : V ⟶ U` and a
Zariski open `O` of the larger chart scheme: it restricts `chartSchemeMap g` to `O` and its
preimage. -/
noncomputable def openChartRestrict {U V : SmallEtale B S hS F} (g : V ⟶ U)
    (O : (chartScheme U).Opens) :
    openChart B S hS F V (chartSchemeMap g ⁻¹ᵁ O) ⟶ openChart B S hS F U O :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (openSubHomOfRestrict ((SmallEtale.toOver B S hS F).map g) O) (by
      change yoneda.map (openSubHomOfRestrict ((SmallEtale.toOver B S hS F).map g) O) ≫
          yoneda.map (openSubHom ((SmallEtale.toOver B S hS F).obj U) O) ≫ U.obj.hom =
          yoneda.map (openSubHom ((SmallEtale.toOver B S hS F).obj V)
            (chartSchemeMap g ⁻¹ᵁ O)) ≫ V.obj.hom
      rw [← yoneda_map_toOver_map_comp_hom g, ← Category.assoc, ← Category.assoc,
        ← yoneda.map_comp, ← yoneda.map_comp,
        openSubHomOfRestrict_comp_openSubHom ((SmallEtale.toOver B S hS F).map g) O]))

/-- The restriction of a morphism of charts to an open and its preimage is compatible with the
inclusions of those opens into the two charts. -/
theorem openChartRestrict_comp_openChartInclusion {U V : SmallEtale B S hS F} (g : V ⟶ U)
    (O : (chartScheme U).Opens) :
    openChartRestrict B S hS F g O ≫ openChartInclusion B S hS F U O =
      openChartInclusion B S hS F V (chartSchemeMap g ⁻¹ᵁ O) ≫ g :=
  ObjectProperty.hom_ext _ <| CostructuredArrow.hom_ext _ _ <|
    openSubHomOfRestrict_comp_openSubHom ((SmallEtale.toOver B S hS F).map g) O

/-- Naturality of `AlgebraicGeometry.Space.openChartRestrict` in the open. -/
theorem openChartRestrict_naturality {U V : SmallEtale B S hS F} (g : V ⟶ U)
    {O O' : (chartScheme U).Opens} (i : O ⟶ O') :
    (openChartFunctor B S hS F V).map ((Opens.map (chartSchemeMap g).base).map i) ≫
        openChartRestrict B S hS F g O' =
      openChartRestrict B S hS F g O ≫ (openChartFunctor B S hS F U).map i := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  change (chartScheme V).homOfLE ((Opens.map (chartSchemeMap g).base).map i).le ≫
      (chartSchemeMap g ∣_ O') =
    (chartSchemeMap g ∣_ O) ≫ (chartScheme U).homOfLE i.le
  rw [← cancel_mono O'.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
    Scheme.homOfLE_ι, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

/-- `AlgebraicGeometry.Space.openChartRestrict` as a natural transformation: the Zariski opens
of the smaller chart scheme obtained as preimages, read as étale charts of `F`, map naturally
to the Zariski opens of the larger one. -/
noncomputable def openChartRestrictNatTrans {U V : SmallEtale B S hS F} (g : V ⟶ U) :
    Opens.map (chartSchemeMap g).base ⋙ openChartFunctor B S hS F V ⟶
      openChartFunctor B S hS F U where
  app O := openChartRestrict B S hS F g O
  naturality {_O _O'} i := openChartRestrict_naturality B S hS F g i

end AlgebraicGeometry.Space

end
