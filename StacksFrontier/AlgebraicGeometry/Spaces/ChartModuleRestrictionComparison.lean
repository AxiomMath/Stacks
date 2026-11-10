module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction

/-!
# Comparing the restrictions of a module to two étale charts

Let `F` be an algebraic space over a scheme `S` of a big fppf site, let `M` be an
`𝒪_F`-module and let `g : V ⟶ U` be a morphism of étale charts of `F`.  Restricting `M` to
the two chart schemes gives Zariski modules `M|_U` and `M|_V`
(`AlgebraicGeometry.Space.restrictToChartScheme`), and this file constructs the canonical
comparison between them over the morphism of schemes `chartSchemeMap g : chartScheme V ⟶
chartScheme U`:

* in the direct-image direction, a morphism `M|_U ⟶ (chartSchemeMap g)_* M|_V`;
* equivalently, in the inverse-image direction, a morphism
  `(chartSchemeMap g)^* M|_U ⟶ M|_V`.

This is the functoriality of the chart restriction *in the chart*; functoriality in the module
is `AlgebraicGeometry.Space.restrictToChartSchemeFunctor`.

## Main definitions

* `AlgebraicGeometry.Space.chartRestrictionRingComparison` is the change-of-scalars map that
  the comparison is semilinear along: the structure sheaf of the larger chart scheme maps to
  the global functions on the preimages of its opens in the smaller chart.
* `AlgebraicGeometry.Space.chartRestrictionPresheafComparison` is the comparison before
  sheafification.
* `AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison` is the comparison
  `M|_U ⟶ (chartSchemeMap g)_* M|_V`, and
  `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` its inverse-image form
  `(chartSchemeMap g)^* M|_U ⟶ M|_V`.

## Main results

* `AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict`: on an open
  `O` of the target, the identification of `Γ(Y, O)` with the global functions on the open
  subscheme `O` carries the pullback along `f` to the pullback along `f ∣_ O`.  This is the
  one piece of scheme geometry the comparison needs.
* `AlgebraicGeometry.Space.chartRestrictionRingComparison_eq`: the change-of-scalars map of
  the comparison factors through the one of the larger chart, along the restriction of the
  chart morphism to the opens.  This is what makes the comparison semilinear.
* `AlgebraicGeometry.Space.chartRestrictionPresheafComparison_naturality`: naturality of the
  comparison in the module, before sheafification.

## Implementation notes

The comparison is *not* claimed to be an isomorphism, and it is not one for a general
`𝒪_F`-module: the restriction to a chart scheme is a Zariski-sheafified restriction of
sections, and it is cartesian along étale morphisms of charts exactly for the quasi-coherent
modules — that is the cartesianness of Descent, Proposition 03DX together with the
identification of the chart restriction with an inverse image, Stacks 03LY.  It is **not**
Stacks 03M0, which is the characterisation of quasi-coherence itself; see also the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/AlgebraSheafChartCartesian.lean`.  The
identification of the slice of the small étale site at a chart with the small étale site of the
chart (Stacks 04M0) which transporting those conditions needs is recorded as missing in the
implementation notes of `StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentEtaleChart.lean`.
For a Zariski open
`O` of `chartScheme U` and the chart morphism `openChartInclusion U O`, the comparison *is*
the restriction of `M|_U` to `O`; no statement to that effect is made here either, since it
needs the identification of the inverse image along an open immersion with the restriction.

The construction has three steps.  Before sheafification the restriction to a chart is a
`CategoryTheory.PresheafOfModules.pushforward` of the sections of `M` along
`AlgebraicGeometry.Space.openChartFunctor`, so the comparison of the two presheaves is the
map on sections induced by `AlgebraicGeometry.Space.openChartRestrictNatTrans`; it is built
with `CategoryTheory.PresheafOfModules.homMk`, which asks only for the underlying map of
abelian presheaves and its semilinearity, so no change-of-scalars isomorphism intervenes.
Composing two pushforwards is a pushforward along the composite *on the nose*
(`CategoryTheory.PresheafOfModules.pushforwardComp` is `CategoryTheory.Iso.refl`), which is
how the target of that map is read as the pushforward of the restriction to the smaller
chart.  Finally the sheafification adjunction turns the presheaf map into the asserted map of
sheaves, and the inverse-image form is the transpose along
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`.

Naturality in the module is proved before sheafification, where it is the naturality of the
map on sections; the comparison itself is the transpose of a composite of a natural
transformation with the unit of the sheafification adjunction, so it is natural in the module
as well, but stating that after sheafification asks for the two adjunction transposes to be
recognized through `AlgebraicGeometry.Space.restrictToChartScheme`, whose definition hides the
sheafification functor behind its instance arguments, and no such statement is made here.

The semilinearity is the only non-formal input and it reduces to
`AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict`, proved with
the `AlgebraicGeometry.Scheme.Hom.appLE` calculus: both sides are the same `appLE` of the
chart morphism, between the same two opens.  It is stated and used as an equality of
natural transformations of presheaves of rings rather than transported into the data of the
comparison, so that no `CategoryTheory.eqToHom` occurs in any definition here.

The module universe is the universe `u` of the schemes.  As the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModule.lean` record, `restrictToChartScheme` raises
an arbitrary module universe `m` to `max u m`, and at `m > u` the restriction no longer lands
in `AlgebraicGeometry.Scheme.Modules` of the chart, which is what
`AlgebraicGeometry.Scheme.Modules.pushforward` and
`AlgebraicGeometry.Scheme.Modules.pullback` consume; so `m = u` is the only universe at which
the comparison can be stated at all.

The two sheafification instances for the Zariski site of each chart are restated from its
essential smallness exactly as in `AlgebraicGeometry.Space.restrictToChartScheme`; both
classes are propositions, so which term is used is immaterial.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Restricting a morphism of schemes to an open `O` of its target and the preimage of that
open is, on global sections, the map on sections over `O` read through the identification of
`Γ(Y, O)` with the global functions on the open subscheme `O`. -/
theorem Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (O : Y.Opens) :
    (Scheme.restrictFunctorΓ (X := Y)).inv.app (Opposite.op O) ≫ Scheme.Γ.map (f ∣_ O).op =
      f.app O ≫ (Scheme.restrictFunctorΓ (X := X)).inv.app (Opposite.op (f ⁻¹ᵁ O)) := by
  simp only [Scheme.restrictFunctorΓ_inv_app, Scheme.Γ_map_op, morphismRestrict_appTop]
  simp only [Scheme.Hom.app_eq_appLE]
  exact ((Scheme.Hom.map_appLE_assoc f _ _ _).trans (Scheme.Hom.appLE_map f _ _)).trans
    (Scheme.Hom.appLE_map f _ _).symm

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### The change of scalars of the comparison -/

/-- The change-of-scalars map the comparison of the two chart restrictions is semilinear
along: the structure sheaf of the larger chart scheme maps to the global functions on the
preimages of its opens, read as étale charts of `F`.

It is the sheaf map of `AlgebraicGeometry.Space.chartSchemeMap` followed by the
change-of-scalars map of the smaller chart. -/
noncomputable def chartRestrictionRingComparison {U V : SmallEtale B S hS F} (g : V ⟶ U) :
    (chartScheme U).ringCatSheaf.obj ⟶
      (Opens.map (chartSchemeMap g).base ⋙ openChartFunctor B S hS F V).op ⋙
        (structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat) :=
  (chartSchemeMap g).toRingCatSheafHom.hom ≫ Functor.whiskerLeft
    (Opens.map (chartSchemeMap g).base).op (chartSchemeRestrictionRingHom B S hS F V)

/-- The change of scalars of the comparison factors through the one of the larger chart, along
the restriction of the chart morphism to the opens.

This is `AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict`, read
on the small étale site. -/
theorem chartRestrictionRingComparison_eq {U V : SmallEtale B S hS F} (g : V ⟶ U) :
    chartRestrictionRingComparison B S hS F g =
      chartSchemeRestrictionRingHom B S hS F U ≫
        Functor.whiskerRight (NatTrans.op (openChartRestrictNatTrans B S hS F g))
          (structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat) := by
  refine NatTrans.ext (funext fun ⟨O⟩ => ?_)
  exact congrArg (forget₂ CommRingCat.{u} RingCat.{u}).map
    (Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict (chartSchemeMap g) O).symm

/-! ### The comparison before sheafification -/

/-- The comparison of the two chart restrictions before sheafification: on a Zariski open `O`
of the larger chart scheme it is the map on sections of `M` induced by the morphism of étale
charts `AlgebraicGeometry.Space.openChartRestrict`.

Its target is the pushforward along `AlgebraicGeometry.Space.chartSchemeMap` of the
restriction to the smaller chart, because composing two pushforwards of presheaves of modules
is the pushforward along the composite change of scalars on the nose. -/
noncomputable def chartRestrictionPresheafComparison {U V : SmallEtale B S hS F} (g : V ⟶ U)
    (N : PresheafOfModules.{u}
      (structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F U)).obj N ⟶
      (PresheafOfModules.pushforward (chartSchemeMap g).toRingCatSheafHom.hom).obj
        ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F V)).obj N) :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (NatTrans.op (openChartRestrictNatTrans B S hS F g)) N.presheaf)
    (fun O r m => (N.map_smul _ _ _).trans
      (congrArg (fun s => s • N.map ((openChartRestrictNatTrans B S hS F g).app O.unop).op m)
        (congrArg (fun z => RingCat.Hom.hom (NatTrans.app z O) r)
          (chartRestrictionRingComparison_eq B S hS F g).symm)))

/-- The comparison before sheafification is natural in the presheaf of modules. -/
theorem chartRestrictionPresheafComparison_naturality {U V : SmallEtale B S hS F} (g : V ⟶ U)
    {N N' : PresheafOfModules.{u}
      (structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat)} (φ : N ⟶ N') :
    chartRestrictionPresheafComparison B S hS F g N ≫
        (PresheafOfModules.pushforward (chartSchemeMap g).toRingCatSheafHom.hom).map
          ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F V)).map φ) =
      (PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F U)).map φ ≫
        chartRestrictionPresheafComparison B S hS F g N' := by
  refine PresheafOfModules.hom_ext (fun O => ?_)
  ext x
  exact PresheafOfModules.naturality_apply φ
    ((openChartRestrictNatTrans B S hS F g).app O.unop).op x

/-! ### The comparison -/

variable (hF : IsAlgebraicSpace B S hS F)

/-- **Chart functoriality of the restriction of a module to an étale chart.** For a morphism
`g : V ⟶ U` of étale charts of `F`, the restriction of `M` to the larger chart maps to the
direct image along `chartSchemeMap g` of its restriction to the smaller one. -/
noncomputable def restrictToChartSchemePushforwardComparison (M : Modules.{u, u} B S hS F hF)
    {U V : SmallEtale B S hS F} (g : V ⟶ U) :
    restrictToChartScheme B S hS F hF M U ⟶
      (Scheme.Modules.pushforward (chartSchemeMap g)).obj
        (restrictToChartScheme B S hS F hF M V) := by
  letI : HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  letI : (Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  letI : HasSheafify (Opens.grothendieckTopology (chartScheme V)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  letI : (Opens.grothendieckTopology (chartScheme V)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  exact (PresheafOfModules.sheafificationHomEquiv
      (P := (PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F U)).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} M).val)
      (F := (Scheme.Modules.pushforward (chartSchemeMap g)).obj
        (restrictToChartScheme B S hS F hF M V))
      (𝟙 (chartScheme U).ringCatSheaf.obj)).symm
    (chartRestrictionPresheafComparison B S hS F g _ ≫
      (PresheafOfModules.pushforward (chartSchemeMap g).toRingCatSheafHom.hom).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (chartScheme V).ringCatSheaf.obj)).unit.app _))

/-- **Chart functoriality of the restriction of a module to an étale chart, inverse-image
form.** For a morphism `g : V ⟶ U` of étale charts of `F`, the inverse image along
`chartSchemeMap g` of the restriction of `M` to the larger chart maps to its restriction to
the smaller one.

This is the transpose of
`AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison` along
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`. -/
noncomputable def restrictToChartSchemePullbackComparison (M : Modules.{u, u} B S hS F hF)
    {U V : SmallEtale B S hS F} (g : V ⟶ U) :
    (Scheme.Modules.pullback (chartSchemeMap g)).obj
        (restrictToChartScheme B S hS F hF M U) ⟶
      restrictToChartScheme B S hS F hF M V :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (chartSchemeMap g)).homEquiv _ _).symm
    (restrictToChartSchemePushforwardComparison B S hS F hF M g)

end AlgebraicGeometry.Space

end
