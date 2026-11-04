module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SiteEnlargementExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartScheme

/-!
# Thickened charts after enlarging the big fppf site

The transport of étale charts to an enlarged big fppf site keeps the scheme of a chart, and the
transported square-zero extension restricts to the given one along it. Hence the thickening of a
chart for the given extension and the thickening of the transported chart for the transported
extension are isomorphic schemes, and in particular have the same size: a site containing the
first is a site containing the second.

## Main results

* `AlgebraicGeometry.SiteEnlargement.chartThickeningTransportIso`: the comparison of thickened
  charts.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SiteEnlargement

open Space Space.SquareZeroExtension Functor

variable {B B' : BigFppfSite.{u}} (h : IsContained (τ := .fppf) B B') {S : Scheme.{u}}
  {hS : B.Contains S} (hS' : B'.Contains S) {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  (E : SquareZeroExtension B S hS f)

/-- The inclusion of big fppf sites is full and faithful on the inclusion of an open subscheme,
both for `B` and for `B'`. -/
private theorem map_preimage_opens_ι (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    B'.inclusion.map (B'.inclusion.preimage (show B'.inclusion.obj ⟨(O : Scheme),
      lt_of_le_of_lt (Scheme.size_coe_opens_le _ O) ((inclusionOver h S hS).obj A).left.property⟩ ⟶
        B'.inclusion.obj ((inclusionOver h S hS).obj A).left from O.ι)) = O.ι ∧
    B.inclusion.map (B.inclusion.preimage (show B.inclusion.obj ⟨(O : Scheme),
      lt_of_le_of_lt (Scheme.size_coe_opens_le _ O) A.left.property⟩ ⟶
        B.inclusion.obj A.left from O.ι)) = O.ι :=
  ⟨B'.inclusion.map_preimage _, B.inclusion.map_preimage _⟩

/-- The structure morphism of the open subobject, on an open `O`, of the image of `A` in the
enlarged site is the structure morphism of the image of the open subobject of `A` on `O`. -/
theorem openSub_hom_transport (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    Over.hom (openSub ((inclusionOver h S hS).obj A) O) =
      ((inclusionOver h S hS).obj (openSub A O)).hom := by
  obtain ⟨e₁, e₂⟩ := map_preimage_opens_ι h A O
  apply ObjectProperty.hom_ext
  dsimp [openSub]
  exact (congrArg (· ≫ _) e₁).trans (congrArg (· ≫ A.hom.hom) e₂).symm

/-- The inclusion of big fppf sites carries the open subobject of an object to the open subobject
of its image, on the same open subscheme. -/
def openSubTransportIso (A : BigFppfOver B S hS) (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    (inclusionOver h S hS).obj (openSub A O) ≅
      openSub ((inclusionOver h S hS).obj A) O :=
  Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (openSub_hom_transport h A O))

/-- The isomorphism `openSubTransportIso` followed by the inclusion of the open subobject of the
image of `A` is the image of the inclusion of the open subobject of `A`. -/
theorem openSubTransportIso_hom_comp (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    (openSubTransportIso h A O).hom ≫ openSubHom ((inclusionOver h S hS).obj A) O =
      (inclusionOver h S hS).map (openSubHom A O) := by
  obtain ⟨e₁, e₂⟩ := map_preimage_opens_ι h A O
  ext1
  apply ObjectProperty.hom_ext
  exact (Category.id_comp _).trans (e₁.trans e₂.symm)

/-- The transport of the chart of a Zariski open of an étale chart is the chart of the same open
of the transported chart. -/
def chartTransportOpenChartIso (V : Space.SmallEtale B S hS X.1) (O : (chartScheme V).Opens) :
    (chartTransport B B' h S hS X).obj (openChart B S hS X.1 V O) ≅
      openChart B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).1
        ((chartTransport B B' h S hS X).obj V) O :=
  ObjectProperty.isoMk _ (CostructuredArrow.isoMk (openSubTransportIso h _ O) (by
    change yoneda.map _ ≫ yoneda.map _ ≫ chartHom B B' h S hS X V.obj.hom =
      chartHom B B' h S hS X (yoneda.map _ ≫ V.obj.hom)
    refine Eq.trans ?_ (chartHom_comp B B' h S hS X _ _).symm
    refine (yoneda.map_comp_assoc _ _ _).symm.trans ?_
    exact congrArg (fun m => yoneda.map m ≫ chartHom B B' h S hS X V.obj.hom)
      (openSubTransportIso_hom_comp h _ O)))

/-- The comparison of open charts, natural in the open. -/
def chartTransportOpenChartFunctorIso (V : Space.SmallEtale B S hS X.1) :
    openChartFunctor B S hS X.1 V ⋙ chartTransport B B' h S hS X ≅
      openChartFunctor B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).1
        ((chartTransport B B' h S hS X).obj V) :=
  NatIso.ofComponents (chartTransportOpenChartIso h V) fun _ => by
    ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The restricted extension sheaves of a chart and of its transport agree**: the Zariski
restriction of the transported extension to the transported chart is that of the given extension
to the chart, on the same scheme. -/
def chartZariskiSheafTransportIso (V : Space.SmallEtale B S hS X.1) :
    chartZariskiSheaf B' S hS' (transportExtension h hS' E) ((chartTransport B B' h S hS X).obj V) ≅
      chartZariskiSheaf B S hS E V :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (isoWhiskerRight (NatIso.op (chartTransportOpenChartFunctorIso h V))
        (transportExtension h hS' E).A.obj ≪≫
      isoWhiskerLeft (openChartFunctor B S hS X.1 V).op
        ((sheafToPresheaf _ _).mapIso (transportAIso h hS' E)))

/-- **The thickened chart of a transported chart is the thickened chart**, for the transported
extension: the two schemes have the same points and isomorphic structure sheaves. -/
def chartThickeningTransportIso (V : Space.SmallEtale B S hS X.1) :
    chartThickening B' S hS' (transportExtension h hS' E) ((chartTransport B B' h S hS X).obj V) ≅
      chartThickening B S hS E V :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
    (LocallyRingedSpace.isoOfSheafedSpaceIso (SheafedSpace.isoMk
      (PresheafedSpace.isoOfComponents (Iso.refl _)
        ((sheafToPresheaf _ _).mapIso (chartZariskiSheafTransportIso h hS' E V)))))

/-- **A site containing a thickened chart contains the thickened transported chart.** -/
theorem contains_chartThickening_transport (V : Space.SmallEtale B S hS X.1)
    (hc : B'.Contains (chartThickening B S hS E V)) :
    B'.Contains (chartThickening B' S hS' (transportExtension h hS' E)
      ((chartTransport B B' h S hS X).obj V)) :=
  lt_of_eq_of_lt (Scheme.size_congr (chartThickeningTransportIso h hS' E V)) hc

end AlgebraicGeometry.SiteEnlargement

end
