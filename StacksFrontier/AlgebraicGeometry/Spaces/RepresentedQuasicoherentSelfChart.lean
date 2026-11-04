module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction

/-!
# The Zariski restriction to the self chart inverts the represented transport

Let `U` be an object of the big fppf site over `S` with underlying scheme `T`, and let `M` be a
quasi-coherent `AlgebraicGeometry.Scheme.Modules` on `T`.  Descent, Proposition 03DX (2) followed
by the comparison of the small étale site of `T` with the small étale site of the algebraic space
`yoneda.obj U` — that is, `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence` —
carries `M` to a quasi-coherent `𝒪`-module on the small étale site of `yoneda.obj U`.  Restricting
that module back to the Zariski site of `T` along the identity chart
`AlgebraicGeometry.Space.selfChart` recovers `M`.

## Main results

* `AlgebraicGeometry.Space.restrictToChartSelfChartIsoRestrictModule`: the restriction of an
  `𝒪`-module on `yoneda.obj U` to the self chart is the right adjoint
  `AlgebraicGeometry.SmallEtale.restrictModule` of the associated-module functor, applied to the
  module read on the small étale site of `T`.
* `AlgebraicGeometry.Space.restrictToChart_selfChart_representedQuasicoherentIso`: **the Zariski
  restriction to the self chart of the transport of a quasi-coherent module on `T` is isomorphic
  to the module one started from.**

## Implementation notes

Everything about the *self* chart is definitional and nothing new had to be proved about it: the
chart's object of the big fppf site is `U` on the nose, so `AlgebraicGeometry.Space.selfChart` and
`AlgebraicGeometry.Space.idEtaleChart` are the same term up to proof irrelevance, and the
transported module is, by `rfl`, the image under
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` of
`AlgebraicGeometry.SmallEtale.associatedModule` applied to `M`.  The three inputs are therefore all
available and general:

* `AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme`, which identifies the two
  readings of the chart restriction;
* `AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso`, which identifies the restriction
  to the identity chart with `AlgebraicGeometry.SmallEtale.restrictModule` of the module read on
  the small étale site of `T`;
* `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`, Stacks 0GN7 on the small étale site of a
  scheme, which makes the unit of the associated-module adjunction an isomorphism at `M`.

The composite is the inverse of that unit, transported across the unit isomorphism of the
comparison equivalence of the two small étale sites.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The restriction of an `𝒪`-module on `yoneda.obj U` to the self chart is the right adjoint
of the associated-module functor of Stacks 03DU**, applied to the module read on the small étale
site of the scheme underlying `U`.

The self chart is `AlgebraicGeometry.Space.idEtaleChart` up to proof irrelevance, so this is
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso` read through the comparison
`AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme` of the two readings of the
chart restriction. -/
noncomputable def restrictToChartSelfChartIsoRestrictModule
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)) :
    restrictToChart B S hS (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) N
        (selfChart B S hS U) ≅
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N) :=
  restrictToChartIsoRestrictToChartScheme B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) N (selfChart B S hS U) ≪≫
    restrictToChartSchemeIdEtaleChartIso B S hS U N

/-- The transport of a quasi-coherent `AlgebraicGeometry.Scheme.Modules` on the scheme underlying
`U` to the small étale site of `yoneda.obj U` is, on the nose, its associated module read across
the comparison of the two small étale sites. -/
theorem representedQuasicoherentSchemeEquivalence_functor_obj_obj
    (M : SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf)
    (hM : SheafOfModules.IsQuasicoherent M) :
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨M, hM⟩).obj =
      (representedSmallEtaleModuleEquivalence B S hS U).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M) :=
  rfl

/-- **The Zariski restriction to the self chart inverts the represented transport of a
quasi-coherent module.**  Let `U` be an object of the big fppf site over `S` and let `M` be a
quasi-coherent `AlgebraicGeometry.Scheme.Modules` on the scheme underlying `U`.  Transport `M` to
a quasi-coherent `𝒪`-module on the small étale site of the represented algebraic space
`yoneda.obj U` by Descent, Proposition 03DX (2) and the comparison of the two small étale sites,
and restrict the result to the Zariski site of the scheme underlying `U` along the identity chart:
the outcome is isomorphic to `M`.

The restriction to the self chart is the right adjoint of the associated-module functor applied to
the module read on the small étale site of the scheme
(`AlgebraicGeometry.Space.restrictToChartSelfChartIsoRestrictModule`), the comparison of the two
small étale sites is undone by its own unit, and what is left is the unit of the associated-module
adjunction at `M`, an isomorphism by Stacks 0GN7
(`AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`) since `M` is quasi-coherent. -/
noncomputable def restrictToChart_selfChart_representedQuasicoherentIso
    (M : SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf)
    (hM : SheafOfModules.IsQuasicoherent M) :
    restrictToChart B S hS (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨M, hM⟩).obj
        (selfChart B S hS U)
      ≅ M :=
  have := _root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⟨M, hM⟩
  restrictToChartSelfChartIsoRestrictModule B S hS U _ ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS U).unitIso.app
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M)).symm ≪≫
    (asIso ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
      U.left.property).unit.app M)).symm

/-- `AlgebraicGeometry.Space.restrictToChart_selfChart_representedQuasicoherentIso` in the
`AlgebraicGeometry.Space.representedZariskiRestriction` phrasing: **the comparison of the modules
of a represented algebraic space with the modules of the representing scheme undoes the transport
of a quasi-coherent module.**  The two statements are the same by definition, the comparison being
the restriction to the self chart. -/
noncomputable def representedZariskiRestriction_representedQuasicoherentIso
    (M : SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf)
    (hM : SheafOfModules.IsQuasicoherent M) :
    representedZariskiRestriction B S hS U
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨M, hM⟩).obj
      ≅ M :=
  restrictToChart_selfChart_representedQuasicoherentIso B S hS U M hM

end AlgebraicGeometry.Space

end
