module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSemilinear

/-!
# The sections of the chart restriction, at the consumers' spelling

`AlgebraicGeometry.Space.chartSectionsLinearEquiv` identifies the sections over a Zariski open
`W` of the chart's scheme of the *three-pushforward* spelling of the chart restriction — the
`AlgebraicGeometry.SmallEtale.restrictModule` of
`AlgebraicGeometry.Space.chartSchemeEtaleModule` — with the sections of `M` over the étale chart
which `W` cuts out.  What the consumers of the chart restriction actually hold is
`AlgebraicGeometry.Space.chartSchemeModule`, which is that spelling only up to the isomorphism
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule`.

This file composes the two, so that the sections of `AlgebraicGeometry.Space.chartSchemeModule`
itself over `W` are the sections of `M` over
`AlgebraicGeometry.Space.openChartOfComparison … W`, linearly over the functions on `W`.  At
`W = ⊤` and an affine chart this is the change of coordinates under which a statement of
commutative algebra about the sections of `M` over an affine étale chart becomes a statement
about the global sections of the chart restriction on the chart's scheme — the form in which
`Stacks.Algebraization.sectionsTop_bijective` and
`AlgebraicGeometry.Space.smallEtaleInternalHomAffineChartHomEquiv` deliver it.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv` — **the sections of the chart
  restriction of `M` over a Zariski open of the chart's scheme are the sections of `M` over the
  étale chart which that open cuts out.**

## Implementation notes

The component of `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` at `W` is turned
into a linear equivalence by assembling it into a `CategoryTheory.Iso` in `ModuleCat` by hand:
`(f ≫ g).val.app W` is `f.val.app W ≫ g.val.app W` and `(𝟙 _).val.app W` is `𝟙 _`, both by
`rfl`, so the two triangles are `congrArg` of the triangles of the isomorphism and nothing more.
The `congrArg` is written with no type ascription on its lambda: ascribing `_ ⟶ _` leaves the
two objects as metavariables and the field projection `k.val` then has no constant head.

No `@[stacks]` attribute is carried: both halves are identifications proved elsewhere and this is their
composite.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The sections of the chart restriction over a Zariski open of the chart's scheme are the
sections of the module over the étale chart which that open cuts out**, linearly over the
functions on the open, the scalars on the target being restricted along
`AlgebraicGeometry.Space.chartSectionsRingHom`.

This is `AlgebraicGeometry.Space.chartSectionsLinearEquiv` preceded by the component at `W` of
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule`, which is what carries the consumers'
spelling of the chart restriction to the three-pushforward spelling the former is stated at. -/
noncomputable def chartSchemeModuleSectionsLinearEquiv (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens) :
    (chartSchemeModule B S hS X M hM A).val.obj (op W)
      ≃ₗ[(chartScheme A).ringCatSheaf.obj.obj (op W)]
        (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A W)).obj
          (M.val.obj (op (openChartOfComparison B S hS X A W))) :=
  LinearEquiv.trans
    (Iso.toLinearEquiv
      { hom := (chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom.val.app (op W)
        inv := (chartSchemeModuleIsoRestrictModule B S hS X M hM A).inv.val.app (op W)
        hom_inv_id := congrArg (fun k => k.val.app (op W))
          (chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom_inv_id
        inv_hom_id := congrArg (fun k => k.val.app (op W))
          (chartSchemeModuleIsoRestrictModule B S hS X M hM A).inv_hom_id })
    (chartSectionsLinearEquiv B S hS X M hM A W)

end AlgebraicGeometry.Space

end
