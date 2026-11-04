module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionEnlargedThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartSchemeHom

/-!
# Presentations after enlarging the big fppf site

An étale presentation `R ⇉ U ⟶ X` of an algebraic space on a big fppf site `B` transports to an
étale presentation of its inverse image `X'` on a containing site `B'`, on the same schemes `U` and
`R` with the same two projections, and with the transported atlas. The two presenting charts of
the transported presentation are the transports of the two presenting charts.

## Main definitions

* `AlgebraicGeometry.SiteEnlargement.transportPresentation`: the transported presentation.
* `AlgebraicGeometry.SiteEnlargement.transportChartedPresentation`: the same for a morphism.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SiteEnlargement

open Space Space.SquareZeroExtension

variable {B B' : BigFppfSite.{u}} (h : IsContained (τ := .fppf) B B') {S : Scheme.{u}}
  {hS : B.Contains S}

/-- The canonical comparison `h_{i T} ≅ f⁻¹h_T` is natural in `T`. -/
theorem changeBigSiteYonedaHom_naturality {R U : BigFppfOver B S hS} (t : R ⟶ U) :
    yoneda.map ((inclusionOver h S hS).map t) ≫ changeBigSiteYonedaHom B B' h S hS U =
      changeBigSiteYonedaHom B B' h S hS R ≫
        ((changeBigSite B B' h S hS).map ((schemeSpaceFunctor B S hS).map t)).hom := by
  have h₁ := chartHom_comp B B' h S hS ((schemeSpaceFunctor B S hS).obj U) t (𝟙 (yoneda.obj U))
  have h₂ := chartHom_map B B' h S hS ((schemeSpaceFunctor B S hS).obj R)
    ((schemeSpaceFunctor B S hS).map t) (𝟙 (yoneda.obj R))
  refine h₁.symm.trans (Eq.trans ?_ h₂)
  exact congrArg (chartHom B B' h S hS ((schemeSpaceFunctor B S hS).obj U))
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The transported atlas has the same kernel pair**: the image of the relation scheme of a
presentation, with the images of the two projections, is the fibre product of the transported
atlas with itself. The inverse image along the inclusion of big fppf sites is left exact
(`AlgebraicGeometry.inclusionOver_preservesFiniteLimits_sheafPullback`) and carries `h_T` to
`h_{i T}` naturally in `T`. -/
theorem isPullback_chartHom {X : AlgebraicSpaces B S hS} (P : Presentation B S hS X.1 X.2) :
    IsPullback (yoneda.map ((inclusionOver h S hS).map P.target))
      (yoneda.map ((inclusionOver h S hS).map P.source))
      (chartHom B B' h S hS X P.toSpace) (chartHom B B' h S hS X P.toSpace) := by
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S (largerContains h hS)
  let i := inclusionOver h S hS
  let : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let : J.Subcanonical := subcanonical_overTopology B S hS
  let L := i.sheafPullback (Type u) J K
  let : PreservesFiniteLimits L := inclusionOver_preservesFiniteLimits_sheafPullback B B' h S hS
  let A : Sheaf J (Type u) := ⟨X.obj, X.property.isSheaf⟩
  let qS : J.yoneda.obj P.U ⟶ A := ⟨P.toSpace⟩
  have hRS : IsPullback (J.yoneda.map P.target) (J.yoneda.map P.source) qS qS :=
    IsPullback.of_map_of_faithful (F := sheafToPresheaf J (Type u)) P.isPullback
  have H := (hRS.map L).map (sheafToPresheaf K (Type u))
  have hnat : ∀ {R U : BigFppfOver B S hS} (t : R ⟶ U),
      ((sheafToPresheaf K (Type u)).map (L.map (J.yoneda.map t))) ≫
          (changeBigSiteYonedaIso B B' h S hS U).symm.hom =
        (changeBigSiteYonedaIso B B' h S hS R).symm.hom ≫ yoneda.map (i.map t) := fun t =>
    (Iso.comp_inv_eq _).mpr ((Category.assoc _ _ _).trans
      ((congrArg ((changeBigSiteYonedaIso B B' h S hS _).inv ≫ ·)
        (changeBigSiteYonedaHom_naturality h t)).trans
        (Iso.inv_hom_id_assoc (changeBigSiteYonedaIso B B' h S hS _) _))).symm
  have H' := isPullback_of_iso_comp_inv H (changeBigSiteYonedaIso B B' h S hS P.R).symm
    (changeBigSiteYonedaIso B B' h S hS P.U).symm (changeBigSiteYonedaIso B B' h S hS P.U).symm
    (hnat P.target) (hnat P.source)
  have he := chartHom_eq B B' h S hS X P.toSpace
  rw [he]
  exact H'

variable (hS' : B'.Contains S)

/-- **The transported presentation**: the same presenting scheme and relation scheme, read in the
larger site, with the transported atlas. -/
def transportPresentation {X : AlgebraicSpaces B S hS} (P : Presentation B S hS X.1 X.2) :
    Presentation B' S hS' ((changeBigSite B B' h S hS).obj X).1
      ((changeBigSite B B' h S hS).obj X).2 where
  U := (inclusionOver h S hS).obj P.U
  R := (inclusionOver h S hS).obj P.R
  target := (inclusionOver h S hS).map P.target
  source := (inclusionOver h S hS).map P.source
  isEtaleEquivalenceRelation := P.isEtaleEquivalenceRelation
  toSpace := chartHom B B' h S hS X P.toSpace
  surjective := presheaf_surjective_of_isLocallySurjective B' S hS'
    (isEtaleChart_chartHom B B' h S hS X P.toSpace P.etale).rep
    (isLocallySurjective_chartHom B B' h S hS X P.toSpace P.surjective P.etale)
  etale := isEtaleChart_chartHom B B' h S hS X P.toSpace P.etale
  isPullback := isPullback_chartHom h P

/-- **The transported charted presentation** of the inverse image of a morphism. -/
def transportChartedPresentation {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (C : ChartedPresentation B S hS f) :
    ChartedPresentation B' S hS' ((changeBigSite B B' h S hS).map f) where
  P := transportPresentation h hS' C.P
  Q := transportPresentation h hS' C.Q
  α := (inclusionOver h S hS).map C.α
  comm := (chartHom_map B B' h S hS X f C.P.toSpace).symm.trans
    ((congrArg (chartHom B B' h S hS Y) C.comm).trans (chartHom_comp B B' h S hS Y C.α C.Q.toSpace))

/-- The presenting chart of the transported presentation is the transported presenting chart. -/
def presentationChartTransportIso {X : AlgebraicSpaces B S hS} (P : Presentation B S hS X.1 X.2) :
    presentationChart (transportPresentation h hS' P) ≅
      (chartTransport B B' h S hS X).obj (presentationChart P) :=
  Iso.refl _

/-- The relation chart of the transported presentation is the transported relation chart. -/
def presentationRelationChartTransportIso {X : AlgebraicSpaces B S hS}
    (P : Presentation B S hS X.1 X.2) :
    presentationRelationChart (transportPresentation h hS' P) ≅
      (chartTransport B B' h S hS X).obj (presentationRelationChart P) :=
  ObjectProperty.isoMk _ (CostructuredArrow.isoMk (Iso.refl _)
    ((Category.id_comp _).trans (chartHom_comp B B' h S hS X P.source P.toSpace)))

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
  (C : ChartedPresentation B S hS f)

/-- **The enlarged site contains the thickened presenting chart of the transported presentation**
as soon as it contains the thickened presenting chart of the given one. -/
theorem contains_chartThickening_transportPresentationChart
    (hcU : B'.Contains (chartThickening B S hS E (presentationChart C.P))) :
    B'.Contains (chartThickening B' S hS' (transportExtension h hS' E)
      (presentationChart (transportChartedPresentation h hS' C).P)) :=
  lt_of_eq_of_lt
    (Scheme.size_congr ((chartThickeningFunctor B' S hS' (transportExtension h hS' E)).mapIso
      (presentationChartTransportIso h hS' C.P)))
    (contains_chartThickening_transport h hS' E (presentationChart C.P) hcU)

/-- **The enlarged site contains the thickened relation chart of the transported presentation**
as soon as it contains the thickened relation chart of the given one. -/
theorem contains_chartThickening_transportPresentationRelationChart
    (hcR : B'.Contains (chartThickening B S hS E (presentationRelationChart C.P))) :
    B'.Contains (chartThickening B' S hS' (transportExtension h hS' E)
      (presentationRelationChart (transportChartedPresentation h hS' C).P)) :=
  lt_of_eq_of_lt
    (Scheme.size_congr ((chartThickeningFunctor B' S hS' (transportExtension h hS' E)).mapIso
      (presentationRelationChartTransportIso h hS' C.P)))
    (contains_chartThickening_transport h hS' E (presentationRelationChart C.P) hcR)

end AlgebraicGeometry.SiteEnlargement

end
