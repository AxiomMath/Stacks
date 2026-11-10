module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteSmoothEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite

/-!
# Étale charts after enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B` and let
`X` be an algebraic space over `S` for `B`, with inverse image `X'` on the enlarged site
(`AlgebraicGeometry.changeBigSite`). An étale chart `φ : h_U ⟶ X` of `X` with `U` an object of
the smaller site transports to an étale chart `h_{i U} ⟶ X'` of `X'` with the *same* scheme:
its Yoneda transpose is the transport of the section `φ` along the bijection
`X(U) ≃ X'(i U)` of `AlgebraicGeometry.changeBigSiteSectionEquiv`. This defines a functor
between the small étale sites, which is fully faithful.

## Main definitions

* `AlgebraicGeometry.SiteEnlargement.chartHom`: the transported chart `h_{i U} ⟶ X'`.
* `AlgebraicGeometry.SiteEnlargement.chartTransport`: the functor
  `X_étale ⥤ X'_étale` it defines.
* `AlgebraicGeometry.SiteEnlargement.chartTransportToOverIso`: the functor lies over the
  localized inclusion of big fppf sites.

## Main results

* `AlgebraicGeometry.SiteEnlargement.chartHom_eq`: the transported chart is the inverse image of
  the chart, read through the identification `h_{i U} ≅ f⁻¹h_U` of Stacks 03FP, part (1).
* `AlgebraicGeometry.SiteEnlargement.isEtaleChart_chartHom`: it is an étale chart, by the
  persistence of étaleness under enlarging the big fppf site.
* `AlgebraicGeometry.SiteEnlargement.chartTransportFullyFaithful`: the functor is fully
  faithful.

## Implementation notes

The chart is defined through the bijection on sections rather than as the composite of
`AlgebraicGeometry.changeBigSiteYonedaIso` with the inverse image of the chart: the bijection on
sections is natural in the test object (`AlgebraicGeometry.changeBigSiteSectionEquiv_restrict`),
which is exactly the compatibility a morphism of charts needs, whereas the composite form is the
one in which étaleness is visible. `chartHom_eq` identifies the two.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SiteEnlargement

open Space

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The localized inclusion of big fppf sites is full, as an instance at `τ = fppf`. -/
local instance : (inclusionOver h S hS).Full := inclusionOver_full (τ := .fppf) h S hS

/-- The localized inclusion of big fppf sites is faithful, as an instance at `τ = fppf`. -/
local instance : (inclusionOver h S hS).Faithful := inclusionOver_faithful (τ := .fppf) h S hS

/-- The transported chart: the morphism `h_{i U} ⟶ X'` whose Yoneda transpose is the transport
of the chart `φ : h_U ⟶ X` along the bijection `X(U) ≃ X'(i U)`. -/
def chartHom {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X.obj) :
    yoneda.obj ((inclusionOver h S hS).obj U) ⟶ ((changeBigSite B B' h S hS).obj X).obj :=
  yonedaEquiv.symm (changeBigSiteSectionEquiv B B' h S hS X U (yonedaEquiv φ))

/-- The Yoneda transpose of the transported chart is the transported section. -/
theorem yonedaEquiv_chartHom {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X.obj) :
    yonedaEquiv (chartHom B B' h S hS X φ) =
      changeBigSiteSectionEquiv B B' h S hS X U (yonedaEquiv φ) :=
  yonedaEquiv.apply_symm_apply _

/-- Transport of charts commutes with precomposition by a morphism of the smaller site. -/
theorem chartHom_comp {U V : BigFppfOver B S hS} (g : U ⟶ V) (φ : yoneda.obj V ⟶ X.obj) :
    chartHom B B' h S hS X (yoneda.map g ≫ φ) =
      yoneda.map ((inclusionOver h S hS).map g) ≫ chartHom B B' h S hS X φ :=
  (congrArg (fun x => yonedaEquiv.symm (changeBigSiteSectionEquiv B B' h S hS X U x))
      (yonedaEquiv_naturality φ g).symm).trans
    ((congrArg yonedaEquiv.symm (changeBigSiteSectionEquiv_restrict B B' h S hS X g
      (yonedaEquiv φ))).trans
      (yonedaEquiv_symm_naturality_left _ _ _).symm)

/-- Transport of charts commutes with postcomposition by a morphism of algebraic spaces. -/
theorem chartHom_map {Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {U : BigFppfOver B S hS}
    (φ : yoneda.obj U ⟶ X.obj) :
    chartHom B B' h S hS Y (φ ≫ f.hom) =
      chartHom B B' h S hS X φ ≫ ((changeBigSite B B' h S hS).map f).hom :=
  (congrArg yonedaEquiv.symm (changeBigSiteSectionEquiv_map B B' h S hS f U
      (yonedaEquiv φ))).trans
    (yonedaEquiv_symm_naturality_right _ _ _).symm

/-- Transport of charts is injective. -/
theorem chartHom_injective {U : BigFppfOver B S hS} {φ ψ : yoneda.obj U ⟶ X.obj}
    (e : chartHom B B' h S hS X φ = chartHom B B' h S hS X ψ) : φ = ψ :=
  yonedaEquiv.injective ((changeBigSiteSectionEquiv B B' h S hS X U).injective
    (yonedaEquiv.symm.injective e))

/-- **The transported chart is the inverse image of the chart**, read through the canonical
identification `h_{i U} ≅ f⁻¹h_U` of Stacks 03FP, part (1). -/
theorem chartHom_eq {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X.obj) :
    chartHom B B' h S hS X φ =
      (changeBigSiteYonedaIso B B' h S hS U).hom ≫
        ((changeBigSite B B' h S hS).map
          (ObjectProperty.homMk φ : (schemeSpaceFunctor B S hS).obj U ⟶ X)).hom := by
  have e := chartHom_map B B' h S hS ((schemeSpaceFunctor B S hS).obj U)
    (ObjectProperty.homMk φ : (schemeSpaceFunctor B S hS).obj U ⟶ X) (𝟙 (yoneda.obj U))
  refine (Eq.trans ?_ e).trans ?_
  · exact congrArg (chartHom B B' h S hS X) (Category.id_comp φ).symm
  · exact congrArg (· ≫ ((changeBigSite B B' h S hS).map
      (ObjectProperty.homMk φ : (schemeSpaceFunctor B S hS).obj U ⟶ X)).hom) rfl

/-- **A transported étale chart is an étale chart**, because étaleness of a morphism of
algebraic spaces persists under enlarging the big fppf site. -/
theorem isEtaleChart_chartHom {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X.obj)
    (hφ : IsEtaleChart B S hS X.obj (CostructuredArrow.mk φ)) :
    IsEtaleChart B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj
      (CostructuredArrow.mk (chartHom B B' h S hS X φ)) := by
  change MorphismProperty.presheaf _ (chartHom B B' h S hS X φ)
  refine (isEtale_iff_presheaf_of_yoneda B' S (largerContains h hS) _).mp ?_
  refine (chartHom_eq B B' h S hS X φ).symm ▸ ?_
  refine isEtale_comp _ _ _ (@isEtale_of_isIso _ _ _ _ _ _ (Iso.isIso_hom _)) ?_
  exact changeBigSite_isEtale B B' h S hS _ ((isEtale_iff_presheaf_of_yoneda B S hS φ).mpr hφ)

/-- The transport of an étale chart, as an object of the small étale site of `X'`. -/
def chartTransportObj (U : Space.SmallEtale B S hS X.obj) :
    Space.SmallEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj :=
  ⟨CostructuredArrow.mk (chartHom B B' h S hS X U.obj.hom),
    isEtaleChart_chartHom B B' h S hS X U.obj.hom U.property⟩

/-- **The transport of étale charts**, as a functor from the small étale site of `X` to that
of its inverse image `X'`: a chart `h_U ⟶ X` goes to the transported chart `h_{i U} ⟶ X'` and
a morphism of charts to the same morphism of schemes. -/
def chartTransport :
    Space.SmallEtale B S hS X.obj ⥤
      Space.SmallEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj where
  obj := chartTransportObj B B' h S hS X
  map {U V} g := ObjectProperty.homMk (CostructuredArrow.homMk
    ((inclusionOver h S hS).map g.hom.left) (by
      change yoneda.map _ ≫ chartHom B B' h S hS X V.obj.hom = chartHom B B' h S hS X U.obj.hom
      rw [← chartHom_comp]
      exact congrArg (chartHom B B' h S hS X) (CostructuredArrow.w g.hom)))
  map_id U := by
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    exact (inclusionOver h S hS).map_id _
  map_comp f g := by
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    exact (inclusionOver h S hS).map_comp _ _

/-- The scheme of a transported chart is the image of the scheme of the chart under the
localized inclusion of big fppf sites. -/
@[simp]
theorem chartTransport_obj_left (U : Space.SmallEtale B S hS X.obj) :
    ((chartTransport B B' h S hS X).obj U).obj.left = (inclusionOver h S hS).obj U.obj.left :=
  rfl

/-- The morphism to `X'` of a transported chart is the transported chart `chartHom`. -/
@[simp]
theorem chartTransport_obj_hom (U : Space.SmallEtale B S hS X.obj) :
    ((chartTransport B B' h S hS X).obj U).obj.hom = chartHom B B' h S hS X U.obj.hom :=
  rfl

/-- The transport of a morphism of charts is the image of its morphism of schemes under the
localized inclusion of big fppf sites. -/
@[simp]
theorem chartTransport_map_left {U V : Space.SmallEtale B S hS X.obj} (g : U ⟶ V) :
    ((chartTransport B B' h S hS X).map g).hom.left = (inclusionOver h S hS).map g.hom.left :=
  rfl

/-- **The transport of étale charts lies over the localized inclusion of big fppf sites.** -/
def chartTransportToOverIso :
    Space.SmallEtale.toOver B S hS X.obj ⋙ inclusionOver h S hS ≅
      chartTransport B B' h S hS X ⋙
        Space.SmallEtale.toOver B' S (largerContains h hS)
          ((changeBigSite B B' h S hS).obj X).obj :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The transport of étale charts is fully faithful.** Faithfulness is that of the localized
inclusion of big fppf sites; for fullness, the preimage of a morphism of transported charts is
its preimage along the localized inclusion, and it is a morphism of charts because transport of
charts is injective. -/
def chartTransportFullyFaithful : (chartTransport B B' h S hS X).FullyFaithful where
  preimage {U V} k := ObjectProperty.homMk (CostructuredArrow.homMk
    ((inclusionOver h S hS).preimage k.hom.left) (by
      apply chartHom_injective B B' h S hS X
      refine (chartHom_comp B B' h S hS X _ _).trans ?_
      refine Eq.trans ?_ (CostructuredArrow.w k.hom)
      exact congrArg (fun m => yoneda.map m ≫ chartHom B B' h S hS X V.obj.hom)
        ((inclusionOver h S hS).map_preimage k.hom.left)))
  map_preimage k := by
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    exact (inclusionOver h S hS).map_preimage k.hom.left
  preimage_map {U V} g := by
    refine ObjectProperty.hom_ext (P := IsEtaleChart B S hS X.obj)
      (CostructuredArrow.hom_ext _ _ ?_)
    exact (inclusionOver h S hS).preimage_map g.hom.left

/-- The transport of étale charts is full. -/
instance : (chartTransport B B' h S hS X).Full :=
  (chartTransportFullyFaithful B B' h S hS X).full

/-- The transport of étale charts is faithful. -/
instance : (chartTransport B B' h S hS X).Faithful :=
  (chartTransportFullyFaithful B B' h S hS X).faithful

end AlgebraicGeometry.SiteEnlargement

end
