module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiIdealSubmodule

/-!
# The Zariski restriction of a sheaf of ideals is the chart restriction of modules

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`N ⊆ 𝒪_X` be a sheaf of ideals on the small étale site of `X` and let `A` be an étale scheme
chart of `X`. Two objects on the small Zariski site of the chart's scheme are built from `N`:

* `AlgebraicGeometry.Space.chartZariskiIdealSheaf`, the restriction read as a submodule of
  `𝒪_A`: its ideal of sections over a Zariski open `W` is the ideal of sections of `N` over the
  étale chart which `W` cuts out, pulled back along the comparison of scalars
  `AlgebraicGeometry.Space.chartSectionsRingHom`; and
* `AlgebraicGeometry.Space.chartPush` of `N`, the restriction read as a direct image of sheaves
  of modules: its sections over `W` are the sections of `N` over that same étale chart, with
  scalars restricted along the same comparison.

This file shows that the comparison of scalars induces an isomorphism of sheaves of modules
between them.

## Main definitions

* `AlgebraicGeometry.Space.openChartSectionsRingEquiv`: the comparison of scalars, bundled as a
  ring isomorphism. Its inverse is `AlgebraicGeometry.Space.openChartTopRingHom`.
* `AlgebraicGeometry.Space.chartZariskiIdealSectionsIso`: the comparison on sections over one
  Zariski open, as an isomorphism of `Γ(A, W)`-modules.
* `AlgebraicGeometry.Space.chartZariskiIdealSheafToChartPush`: the morphism of presheaves of
  modules from the Zariski restriction read as a submodule to the chart restriction read as a
  direct image.
* `AlgebraicGeometry.Space.chartZariskiIdealSheafPresheafIsoChartPush` and
  `AlgebraicGeometry.Space.chartZariskiIdealSheafIsoChartPush`: the isomorphism, at the level
  of presheaves of modules and of sheaves of modules.

## Main results

* `AlgebraicGeometry.Space.chartZariskiIdealSheafToChartPush_app_apply` and
  `AlgebraicGeometry.Space.chartZariskiIdealSheafIsoChartPush_hom_val_app_apply`: the morphism and
  the isomorphism act on a section as the comparison of scalars does.
* `AlgebraicGeometry.Space.chartZariskiIdealSheafIsoChartPush_inv_val_app_apply`: the inverse acts
  as `AlgebraicGeometry.Space.openChartTopRingHom`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The comparison of scalars, as a ring isomorphism -/

/-- The comparison of scalars `AlgebraicGeometry.Space.chartSectionsRingHom` of the chart
sections identification, bundled as a ring isomorphism with inverse
`AlgebraicGeometry.Space.openChartTopRingHom`. -/
noncomputable def openChartSectionsRingEquiv (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens) :
    Γ(chartScheme A, W) ≃+*
      (structureRingSheaf B S hS X).obj.obj (op (openChartOfComparison B S hS X A W)) :=
  RingEquiv.ofRingHom (chartSectionsRingHom B S hS X A W) (openChartTopRingHom B S hS X A W)
    (RingHom.ext (chartSectionsRingHom_openChartTopRingHom B S hS X A W))
    (RingHom.ext (openChartTopRingHom_chartSectionsRingHom B S hS X A W))

/-! ### The comparison on sections over one Zariski open -/

variable (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)

/-- The isomorphism of `Γ(A, W)`-modules between the sections of
`AlgebraicGeometry.Space.chartZariskiIdealSheaf` over a Zariski open `W` of the chart's scheme
and the sections of `AlgebraicGeometry.Space.chartPush` of `N` over `W`, given by the comparison
of scalars restricted to the two ideals of sections. -/
noncomputable def chartZariskiIdealSectionsIso (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens) :
    (chartZariskiIdealSheaf B S hS X N A).toSheafOfModules.val.obj (op W) ≅
      (chartPush B S hS X N.toSheafOfModules A).val.obj (op W) where
  hom := ModuleCat.ofHom
    (X := (chartZariskiIdealSheaf B S hS X N A).toSheafOfModules.val.obj (op W))
    (Y := (chartPush B S hS X N.toSheafOfModules A).val.obj (op W))
    { toFun := fun r =>
        ⟨chartSectionsRingHom B S hS X A W r.1,
          (mem_openChartIdeal_iff_chartSectionsRingHom_mem B S hS X N A W r.1).1 r.2⟩
      map_add' := fun r r' => Subtype.ext (map_add (chartSectionsRingHom B S hS X A W) r.1 r'.1)
      map_smul' := fun c r => Subtype.ext (map_mul (chartSectionsRingHom B S hS X A W) c r.1) }
  inv := ModuleCat.ofHom
    (X := (chartPush B S hS X N.toSheafOfModules A).val.obj (op W))
    (Y := (chartZariskiIdealSheaf B S hS X N A).toSheafOfModules.val.obj (op W))
    { toFun := fun y =>
        ⟨openChartTopRingHom B S hS X A W y.1,
          (mem_openChartIdeal_iff_chartSectionsRingHom_mem B S hS X N A W _).2
            (((chartSectionsRingHom_openChartTopRingHom B S hS X A W y.1).symm ▸ y.2 :
              chartSectionsRingHom B S hS X A W (openChartTopRingHom B S hS X A W y.1) ∈
                N.obj (op (openChartOfComparison B S hS X A W))))⟩
      map_add' := fun y y' => Subtype.ext (map_add (openChartTopRingHom B S hS X A W) y.1 y'.1)
      map_smul' := fun c y =>
        Subtype.ext
          ((map_mul (openChartTopRingHom B S hS X A W)
              (chartSectionsRingHom B S hS X A W c) y.1).trans
            (congrArg (fun z => z * openChartTopRingHom B S hS X A W y.1)
              (openChartTopRingHom_chartSectionsRingHom B S hS X A W c))) }
  hom_inv_id :=
    ModuleCat.hom_ext (LinearMap.ext fun r =>
      Subtype.ext (openChartTopRingHom_chartSectionsRingHom B S hS X A W r.1))
  inv_hom_id :=
    ModuleCat.hom_ext (LinearMap.ext fun y =>
      Subtype.ext (chartSectionsRingHom_openChartTopRingHom B S hS X A W y.1))

/-- The comparison on sections acts as the comparison of scalars. -/
theorem chartZariskiIdealSectionsIso_hom_apply (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens)
    (r : (chartZariskiIdealSheaf B S hS X N A).toSheafOfModules.val.obj (op W)) :
    ((chartZariskiIdealSectionsIso B S hS X N A W).hom r).1 =
      chartSectionsRingHom B S hS X A W r.1 := rfl

/-- The inverse of the comparison on sections acts as
`AlgebraicGeometry.Space.openChartTopRingHom`. -/
theorem chartZariskiIdealSectionsIso_inv_apply (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens)
    (y : (chartPush B S hS X N.toSheafOfModules A).val.obj (op W)) :
    ((chartZariskiIdealSectionsIso B S hS X N A W).inv y).1 =
      openChartTopRingHom B S hS X A W y.1 := rfl

/-! ### The morphism and the isomorphism of modules -/

/-- The morphism of presheaves of modules from the Zariski restriction of a sheaf of ideals,
read as a submodule of `𝒪_A`, to the chart restriction of that sheaf of ideals, read as a direct
image. Its component over a Zariski open `W` is
`AlgebraicGeometry.Space.chartZariskiIdealSectionsIso`. -/
noncomputable def chartZariskiIdealSheafToChartPush (A : SmallEtale B S hS X.1) :
    (chartZariskiIdealSheaf B S hS X N A).toSheafOfModules.val ⟶
      (chartPush B S hS X N.toSheafOfModules A).val where
  app W := (chartZariskiIdealSectionsIso B S hS X N A W.unop).hom
  naturality f :=
    ModuleCat.hom_ext (LinearMap.ext fun r =>
      Subtype.ext (chartSectionsRingHom_restrict B S hS X A f.unop r.1))

/-- The morphism acts on a section as the comparison of scalars. -/
theorem chartZariskiIdealSheafToChartPush_app_apply (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens)
    (r : (chartZariskiIdealSheaf B S hS X N A).toSheafOfModules.val.obj (op W)) :
    (((chartZariskiIdealSheafToChartPush B S hS X N A).app (op W)) r).1 =
      chartSectionsRingHom B S hS X A W r.1 := rfl

/-- The isomorphism of presheaves of modules on the small Zariski site of the chart's scheme
between the Zariski restriction of a sheaf of ideals of `𝒪_X`, read as a submodule of `𝒪_A`, and
the chart restriction of that sheaf of ideals, read as a direct image. -/
noncomputable def chartZariskiIdealSheafPresheafIsoChartPush (A : SmallEtale B S hS X.1) :
    (chartZariskiIdealSheaf B S hS X N A).toSheafOfModules.val ≅
      (chartPush B S hS X N.toSheafOfModules A).val :=
  PresheafOfModules.isoMk (fun W => chartZariskiIdealSectionsIso B S hS X N A W.unop)
    fun {_ _} f =>
      ModuleCat.hom_ext (LinearMap.ext fun r =>
        Subtype.ext (chartSectionsRingHom_restrict B S hS X A f.unop r.1))

/-- The isomorphism of sheaves of modules on the small Zariski site of the chart's scheme
between the Zariski restriction of a sheaf of ideals of `𝒪_X`, read as a submodule of `𝒪_A`, and
the chart restriction of that sheaf of ideals, read as a direct image. -/
noncomputable def chartZariskiIdealSheafIsoChartPush (A : SmallEtale B S hS X.1) :
    (chartZariskiIdealSheaf B S hS X N A).toSheafOfModules ≅
      (chartPush B S hS X N.toSheafOfModules A :
        SheafOfModules.{u} (chartScheme A).ringCatSheaf) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (chartZariskiIdealSheafPresheafIsoChartPush B S hS X N A)

/-- The isomorphism of sheaves of modules acts on a section as the comparison of scalars. -/
theorem chartZariskiIdealSheafIsoChartPush_hom_val_app_apply (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens)
    (r : (chartZariskiIdealSheaf B S hS X N A).toSheafOfModules.val.obj (op W)) :
    (((chartZariskiIdealSheafIsoChartPush B S hS X N A).hom.val.app (op W)) r).1 =
      chartSectionsRingHom B S hS X A W r.1 := rfl

/-- The inverse of the isomorphism of sheaves of modules acts on a section as
`AlgebraicGeometry.Space.openChartTopRingHom`. -/
theorem chartZariskiIdealSheafIsoChartPush_inv_val_app_apply (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens)
    (y : (chartPush B S hS X N.toSheafOfModules A).val.obj (op W)) :
    (((chartZariskiIdealSheafIsoChartPush B S hS X N A).inv.val.app (op W)) y).1 =
      openChartTopRingHom B S hS X A W y.1 := rfl

end AlgebraicGeometry.Space

end
