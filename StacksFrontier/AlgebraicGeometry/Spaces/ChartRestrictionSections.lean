module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.TensorQuasicoherent

/-!
# The sections of the restriction of a module to an étale chart, and its quasi-coherence

`AlgebraicGeometry.Space.restrictToChart` restricts an `𝒪_X`-module to the Zariski site of the
scheme of an étale chart `A` of an algebraic space `X` by sheafifying the presheaf
`AlgebraicGeometry.Space.chartRestrictionPresheaf`, whose sections over a Zariski open `V` are
the sections of the module over the étale chart `V` cuts out. This file shows that this presheaf
is already a sheaf, computes the sections of the restriction, and proves that the restriction of
a quasi-coherent module is quasi-coherent.

The inclusion `AlgebraicGeometry.Space.chartOpens` of the Zariski opens of the chart into the
small étale site of `X` is, on the nose, the composite

  `Opens(T) ⥤ T_étale ⥤ (chart space)_étale ⥤ X_étale/A ⥤ X_étale`

of the inclusion of the small Zariski site of the chart's scheme `T`, of the comparison of the
small étale site of `T` with that of the algebraic space it represents, of the comparison of
Stacks 04M0, and of the slice projection. The restriction of a sheaf along that composite is
therefore a sheaf, and the change of scalars along which the restriction extends scalars is, on
the nose, the structure map of the morphism of ringed sites `(T_étale, 𝒪) → (T_Zar, 𝒪_T)`. So
the presheaf being sheafified is already the restriction, along the inclusion of the small
Zariski site, of a module on the small étale site of `T`.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeSmallEtaleModule` is the restriction of an `𝒪_X`-module to
  the small étale site of the chart's scheme, with the universe of its sections raised as
  `AlgebraicGeometry.Space.restrictToChart` raises it.
* `AlgebraicGeometry.Space.chartRestrictionSheaf` is its restriction along the inclusion of the
  small Zariski site of the chart's scheme, an `AlgebraicGeometry.Scheme.Modules` whose
  underlying presheaf of modules is `AlgebraicGeometry.Space.chartRestrictionPresheaf` **on the
  nose**.
* `AlgebraicGeometry.Space.chartOpensHom` is the inclusion of the chart cut out by a Zariski open
  of the chart's scheme into the chart itself, and
  `AlgebraicGeometry.Space.chartOpensTopHom` is its value at the open `⊤`.
* `AlgebraicGeometry.Space.moduleChartSections` reads the sections of an `𝒪_X`-module over an
  étale chart as a module over the global functions on the chart's scheme.
* `AlgebraicGeometry.Space.chartRestrictionSheafTopEquiv` identifies the sections of an
  `𝒪_X`-module over an étale chart with the sections of its chart restriction over `⊤`.

## Main results

* `AlgebraicGeometry.Space.chartRestrictionSheaf_val`: the presheaf which
  `AlgebraicGeometry.Space.restrictToChart` sheafifies is the underlying presheaf of a sheaf of
  modules, by `rfl`.
* `AlgebraicGeometry.Space.restrictToChartIsoChartRestrictionSheaf`: **the restriction of an
  `𝒪_X`-module to an étale chart is that sheaf**, with no hypothesis on the module.
* `AlgebraicGeometry.Space.chartRestrictionSheaf_obj`: **the sections of the restriction over a
  Zariski open `V` of the chart's scheme are the sections of the module over the étale chart `V`
  cuts out**, with the universe of the sections raised.
* `AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`: **the restriction of a
  quasi-coherent `𝒪_X`-module to an étale chart is quasi-coherent** on the Zariski site of the
  chart's scheme.
* `AlgebraicGeometry.Space.isIso_chartOpensTopHom` and
  `AlgebraicGeometry.Space.structureRingSheaf_map_chartOpensTopHom`: the chart cut out by the
  whole of the chart's scheme is the chart itself, and the change of scalars at the open `⊤` is
  the structure sheaf applied to that identification.

## References

* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-! ### The chart restriction before sheafification is already a sheaf -/

/-- The restriction of an `𝒪_X`-module to the small étale site of the scheme of an étale chart
`A` of `X`: the comparison of Stacks 04M0 at the chart followed by the comparison of the small
étale site of the chart's scheme with that of the algebraic space it represents, applied to the
module with the universe of its sections raised as `AlgebraicGeometry.Space.restrictToChart`
raises it. -/
noncomputable def chartSchemeSmallEtaleModule (M : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) :
    SheafOfModules.{u} (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)) :=
  (representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS X A)).inverse.obj
    (chartSmallEtaleRestriction B S hS X
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} M) A)

/-- **The restriction of an `𝒪_X`-module to an étale scheme chart, with no sheafification.**  It
is the restriction of `AlgebraicGeometry.Space.chartSchemeSmallEtaleModule` along the inclusion
of the small Zariski site of the chart's scheme into its small étale site. -/
noncomputable def chartRestrictionSheaf (M : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) : (chartScheme A).Modules :=
  (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
    (chartSchemeSmallEtaleModule B S hS X M A)

/-- **The presheaf that `AlgebraicGeometry.Space.restrictToChart` sheafifies is the underlying
presheaf of `AlgebraicGeometry.Space.chartRestrictionSheaf`**, on the nose: the two index
functors agree, and so do the two changes of scalars. -/
theorem chartRestrictionSheaf_val (M : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) :
    (chartRestrictionSheaf B S hS X M A).val = chartRestrictionPresheaf B S hS X.2 M A :=
  rfl

/-- **The restriction of an `𝒪_X`-module to an étale scheme chart is
`AlgebraicGeometry.Space.chartRestrictionSheaf`.** The presheaf of its sections over the Zariski
opens of the chart is already a sheaf, and the isomorphism is the counit of the sheafification
adjunction of presheaves of modules at that sheaf. -/
noncomputable def restrictToChartIsoChartRestrictionSheaf (M : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) :
    restrictToChart B S hS X.2 M A ≅ chartRestrictionSheaf B S hS X M A := by
  letI : HasSheafify (Opens.grothendieckTopology (chartScheme A)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  letI : (Opens.grothendieckTopology (chartScheme A)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  refine Iso.trans (eqToIso (congrArg
    (PresheafOfModules.sheafification (J := Opens.grothendieckTopology (chartScheme A))
      (𝟙 (chartScheme A).ringCatSheaf.obj)).obj
    (chartRestrictionSheaf_val B S hS X M A).symm)) (@asIso _ _ _ _
      (Stacks.SheafOfModules.EpiMono.counitApp (chartRestrictionSheaf B S hS X M A))
      (Stacks.SheafOfModules.EpiMono.isIsoCounitApp _))

/-! ### The sections -/

/-- **The sections of the chart restriction over a Zariski open of the chart's scheme are the
sections of the module over the étale chart that open cuts out**, with the universe of the
sections raised. -/
theorem chartRestrictionSheaf_obj (M : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens) :
    ((chartRestrictionSheaf B S hS X M A).val.obj (op V) : Type u) =
      ULift.{u} (M.val.obj (op ((chartOpens B S hS A).obj V)) : Type u) :=
  rfl

/-- The inclusion of the étale chart cut out by a Zariski open of the chart's scheme into the
chart itself. Its underlying morphism of chart schemes is the inclusion of the open. -/
noncomputable def chartOpensHom (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) :
    (chartOpens B S hS A).obj V ⟶ A :=
  ObjectProperty.homMk (CostructuredArrow.homMk (chartOpenOverι B S hS A V) rfl)

/-- The inclusion of the étale chart cut out by the whole of the chart's scheme into the chart
itself.  This is `AlgebraicGeometry.Space.chartOpensHom` at the open `⊤`. -/
noncomputable def chartOpensTopHom (A : SmallEtale B S hS X.1) :
    (chartOpens B S hS A).obj ⊤ ⟶ A :=
  chartOpensHom B S hS X A ⊤

/-- The chart cut out by the whole of the chart's scheme, as an object of the slice of the small
étale site of `X` at the chart. -/
noncomputable abbrev chartOverOfTop (A : SmallEtale B S hS X.1) : Over A :=
  (SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor.obj
    ((representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A)).inverse.obj
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property ⊤))

/-- `AlgebraicGeometry.Space.chartOpensTopHom` is the isomorphism of
`AlgebraicGeometry.Space.openChartOfComparisonTopIso`: both are morphisms into the final object
of the slice of the small étale site of `X` at the chart, hence equal. -/
theorem openChartOfComparisonTopIso_hom (A : SmallEtale B S hS X.1) :
    (openChartOfComparisonTopIso B S hS X A).hom = chartOpensTopHom B S hS X A :=
  congrArg (Over.forget A).map
    (Over.mkIdTerminal.hom_ext _
      (Over.homMk (U := chartOverOfTop B S hS X A) (V := Over.mk (𝟙 A))
        (chartOpensTopHom B S hS X A) (Category.comp_id _)))

/-- The chart cut out by the whole of the chart's scheme is the chart itself. -/
instance isIso_chartOpensTopHom (A : SmallEtale B S hS X.1) :
    IsIso (chartOpensTopHom B S hS X A) := by
  rw [← openChartOfComparisonTopIso_hom B S hS X A]
  exact Iso.isIso_hom _

/-- **The change of scalars of the chart restriction at the open `⊤` is the structure sheaf of
`X` applied to `AlgebraicGeometry.Space.chartOpensTopHom`**, on the nose. -/
theorem structureRingSheaf_map_chartOpensTopHom (A : SmallEtale B S hS X.1) :
    (structureRingSheaf B S hS X).obj.map (chartOpensTopHom B S hS X A).op =
      (chartRestrictionRingHom B S hS X.2 A).app (op ⊤) :=
  rfl

/-- **The sections of an `𝒪_X`-module over an étale scheme chart are a module over the global
functions on the chart's scheme**, which are the sections of `𝒪_X` over the chart. -/
instance moduleChartSections (M : Modules.{u, u} B S hS X.1 X.2) (A : SmallEtale B S hS X.1) :
    Module Γ(chartScheme A, ⊤) (M.val.obj (op A)) :=
  (M.val.obj (op A)).isModule

/-- **The sections of an `𝒪_X`-module over an étale scheme chart are the sections of its chart
restriction over the whole of the chart's scheme**, linearly over the global functions on that
scheme. The map is the restriction of `M` along `AlgebraicGeometry.Space.chartOpensTopHom`, an
isomorphism, followed by the universe lift. -/
noncomputable def chartRestrictionSheafTopEquiv (M : Modules.{u, u} B S hS X.1 X.2)
    (A : SmallEtale B S hS X.1) :
    (M.val.obj (op A) : Type u) ≃ₗ[Γ(chartScheme A, ⊤)]
      (Γ(chartRestrictionSheaf B S hS X M A, ⊤) : Type u) :=
  { (M.val.presheaf.mapIso
        (asIso (chartOpensTopHom B S hS X A)).op).addCommGroupIsoToAddEquiv.trans
      AddEquiv.ulift.symm with
    map_smul' := fun c m =>
      congrArg ULift.up (M.val.map_smul (chartOpensTopHom B S hS X A).op c m) }

/-! ### Quasi-coherence -/

/-- The restriction of a quasi-coherent `𝒪_X`-module to the small étale site of the chart's
scheme is quasi-coherent there. -/
theorem isQuasicoherentOnSite_chartSchemeSmallEtaleModule (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) :
    (chartSchemeSmallEtaleModule B S hS X M A).IsQuasicoherentOnSite := by
  have hlift : (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} M).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      (SheafOfModules.uliftForPresentationSelfIso.{u + 1, u, u, u} M).symm hM
  exact (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS
    (chartFppfObject B S hS X A) (chartSchemeSmallEtaleModule B S hS X M A)).1
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((representedSmallEtaleModuleEquivalence B S hS
        (chartFppfObject B S hS X A)).counitIso.app _).symm
      (isQuasicoherentOnSite_chartSmallEtaleRestriction B S hS X _ hlift A))

/-- **The chart restriction of a quasi-coherent `𝒪_X`-module is quasi-coherent** on the Zariski
site of the chart's scheme. -/
theorem isQuasicoherent_chartRestrictionSheaf (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) :
    SheafOfModules.IsQuasicoherent (chartRestrictionSheaf B S hS X M A) :=
  _root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule
    (associatedBigEtaleSite B) (chartScheme A) (chartFppfObject B S hS X A).left.property
    (chartSchemeSmallEtaleModule B S hS X M A)
    (isQuasicoherentOnSite_chartSchemeSmallEtaleModule B S hS X M hM A)

/-- **The restriction of a quasi-coherent `𝒪_X`-module to an étale scheme chart is
quasi-coherent** on the Zariski site of the chart's scheme. -/
theorem isQuasicoherent_restrictToChart (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) :
    SheafOfModules.IsQuasicoherent (restrictToChart B S hS X.2 M A) :=
  (SheafOfModules.isQuasicoherent (chartScheme A).ringCatSheaf).prop_of_iso
    (restrictToChartIsoChartRestrictionSheaf B S hS X M A).symm
    (isQuasicoherent_chartRestrictionSheaf B S hS X M hM A)

end AlgebraicGeometry.Space

end
