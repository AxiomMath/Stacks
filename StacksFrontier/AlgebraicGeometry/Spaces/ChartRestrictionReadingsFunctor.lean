module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PushforwardIndexIso
public import StacksFrontier.AlgebraicGeometry.RelativeSpecFinish.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadings

/-!
# The two readings of the chart restriction are one

`AlgebraicGeometry.Space.restrictToChart` and `AlgebraicGeometry.Space.restrictToChartScheme`
restrict an `𝒪_X`-module to an étale scheme chart along the two index functors
`AlgebraicGeometry.Space.chartOpens` and `AlgebraicGeometry.Space.openChartFunctor`.  Those
functors read a Zariski open of the chart as an étale chart of `X` through
`CategoryTheory.ObjectProperty.homMk` and through `CategoryTheory.Functor.preimage`
respectively, which is the discrepancy `AlgebraicGeometry.Space.homMk_opens_ι_eq_preimage`
removes.  This file carries that equality up to the two functors and hence to the two
restrictions, so that a property proved of either reading holds of the other.

## Main results

* `AlgebraicGeometry.Space.chartOpens_obj_eq_openChart`: the two readings of a Zariski open of
  a chart as an étale chart of `X` agree.
* `AlgebraicGeometry.Space.chartOpens_eq_openChartFunctor`: **the two index functors agree.**
* `AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme`: **the two restrictions are
  isomorphic.**
* `AlgebraicGeometry.Space.isQuasicoherent_restrictToChart_iff`: consequently the two are
  quasi-coherent together.

## Implementation notes

The equality of the two functors is `CategoryTheory.Functor.ext` over
`AlgebraicGeometry.Space.chartOpens_obj_eq_openChart`; its morphism obligation is a morphism of
the small étale site between objects of a full subcategory of a costructured-arrow category, so
it is settled by the extensionality lemmas of those two layers and then by uniqueness of a
morphism of the big fppf category over `S` lying over a given morphism of schemes.

The remaining data of the two restrictions already agree: the change-of-scalars maps coincide
by `AlgebraicGeometry.Space.chartRestrictionRingHom_eq`, because the structure sheaf of the
small étale site sees only the underlying scheme of a chart, and the universe lift and the
Zariski sheafification are shared.  Only the index functor distinguished them, and it no longer
does.

The isomorphism is therefore `Stacks.PresheafOfModules.pushforwardIsoOfIndexIso` at
`CategoryTheory.eqToIso` of that equality, evaluated at the universe-lifted sections and carried
through the Zariski sheafification.  Its compatibility hypothesis is discharged *whole*, by
`Stacks.PresheafOfModules.comp_whiskerRight_eqToIso_inv`: the two change-of-scalars maps are one
map, and asking instead for the equality of a single component of them makes the elaborator
compare the structure sheaf of the small étale site with the global functions on a chart's
scheme at that component, which does not terminate within the heartbeat limit even though the
two presheaves of rings are definitionally equal as whole terms.

The four `letI`s of the construction are those of
`AlgebraicGeometry.Space.chartRestrictionPresheaf` and
`AlgebraicGeometry.Space.restrictToChart`: the two categories of presheaves of modules, which
instance search does not find at these universes, and the sheafification data of the Zariski
site of the chart.  `CategoryTheory.Iso.app` is applied to the first two explicitly for the
same reason.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The two readings of a Zariski open of an étale scheme chart as an étale chart of `X` agree:
the one of `AlgebraicGeometry.Space.chartOpens` and the one of
`AlgebraicGeometry.Space.openChart`. -/
theorem chartOpens_obj_eq_openChart (U : SmallEtale B S hS X)
    (O : (etaleChartScheme B S hS U).Opens) :
    (chartOpens B S hS U).obj O = openChart B S hS X U O :=
  Stacks.CategoryTheory.fullSubcategory_eq_of_obj_eq
    (congrArg (fun g => CostructuredArrow.mk
        (yoneda.map (Over.homMk (V := (SmallEtale.toOver B S hS X).obj U)
          (U := Over.mk (g ≫ ((SmallEtale.toOver B S hS X).obj U).hom)) g (w := rfl)) ≫
            U.obj.hom))
      (homMk_opens_ι_eq_preimage B S hS ((SmallEtale.toOver B S hS X).obj U) O))

/-- The scheme underlying an étale chart of `X`, functorially in the chart. -/
noncomputable abbrev chartSchemeForget : SmallEtale B S hS X ⥤ Scheme.{u} :=
  SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS

/-- `AlgebraicGeometry.Space.chartOpens_obj_eq_openChart` with the right-hand side read through
`AlgebraicGeometry.Space.openChartFunctor`, which is the form the equality of the two functors
is stated over. -/
theorem chartOpens_obj_eq_openChartFunctor_obj (U : SmallEtale B S hS X)
    (O : (etaleChartScheme B S hS U).Opens) :
    (chartOpens B S hS U).obj O = (openChartFunctor B S hS X U).obj O :=
  chartOpens_obj_eq_openChart B S hS U O

/-- The two index functors of the chart restriction agree. -/
theorem chartOpens_eq_openChartFunctor (U : SmallEtale B S hS X) :
    chartOpens B S hS U = openChartFunctor B S hS X U :=
  CategoryTheory.Functor.ext (chartOpens_obj_eq_openChartFunctor_obj B S hS U) (fun O O' i => by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change (chartSchemeForget B S hS (X := X)).map ((chartOpens B S hS U).map i) =
      (chartSchemeForget B S hS (X := X)).map
        (eqToHom (chartOpens_obj_eq_openChartFunctor_obj B S hS U O) ≫
          (openChartFunctor B S hS X U).map i ≫
            eqToHom (chartOpens_obj_eq_openChartFunctor_obj B S hS U O').symm)
    simp only [Functor.map_comp, eqToHom_map]
    rfl)

/-- The two change-of-scalars maps of the chart restriction are compatible with the comparison
of index functors that `AlgebraicGeometry.Space.chartOpens_eq_openChartFunctor` induces.

This is the hypothesis of `Stacks.PresheafOfModules.pushforwardIsoOfIndexIso`.  It holds because
the two maps are literally the same map, by
`AlgebraicGeometry.Space.chartRestrictionRingHom_eq`, and the comparison of index functors
attached to an equality of functors is an identity. -/
theorem chartRestrictionRingHom_comp_whiskerRight (U : SmallEtale B S hS X) :
    chartRestrictionRingHom B S hS hX U ≫
        Functor.whiskerRight
          (NatIso.op (eqToIso (chartOpens_eq_openChartFunctor B S hS U))).inv
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).obj =
      chartSchemeRestrictionRingHom B S hS X U :=
  Stacks.PresheafOfModules.comp_whiskerRight_eqToIso_inv
    (chartOpens_eq_openChartFunctor B S hS U)
    (heq_of_eq (chartRestrictionRingHom_eq B S hS hX U))

/-- **The two readings of the chart restriction of an `𝒪_X`-module are isomorphic.**
`AlgebraicGeometry.Space.restrictToChart` and `AlgebraicGeometry.Space.restrictToChartScheme`
differ only in the index functor along which the sections are restricted, and
`AlgebraicGeometry.Space.chartOpens_eq_openChartFunctor` says the two index functors are
equal. -/
noncomputable def restrictToChartIsoRestrictToChartScheme (G : Modules.{u, m} B S hS X hX)
    (U : SmallEtale B S hS X) :
    restrictToChart B S hS hX G U ≅ restrictToChartScheme B S hS X hX G U := by
  letI catSpaceModules : Category (PresheafOfModules.{max u m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).obj) :=
    inferInstance
  letI catChartModules : Category (PresheafOfModules.{max u m}
      (etaleChartScheme B S hS U).ringCatSheaf.obj) := inferInstance
  letI : HasSheafify (Opens.grothendieckTopology (etaleChartScheme B S hS U))
      AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u m} _ _
  letI : (Opens.grothendieckTopology (etaleChartScheme B S hS U)).WEqualsLocallyBijective
      AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u m} _
  exact (PresheafOfModules.sheafification.{max u m}
      (𝟙 (etaleChartScheme B S hS U).ringCatSheaf.obj)).mapIso
    (@Iso.app _ catSpaceModules _ catChartModules _ _
      (Stacks.PresheafOfModules.pushforwardIsoOfIndexIso.{max u m}
        (eqToIso (chartOpens_eq_openChartFunctor B S hS U))
        (chartRestrictionRingHom_comp_whiskerRight B S hS hX U))
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u} G).val)

/-- The two readings of the chart restriction are quasi-coherent together: quasi-coherence is
closed under isomorphism, and `AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme`
is the isomorphism.

Both readings are modules on the Zariski site of the chart's scheme, so this is quasi-coherence
in the sense of `CategoryTheory.SheafOfModules.IsQuasicoherent`, which fixes the universe of the
sections at that of the schemes. -/
theorem isQuasicoherent_restrictToChart_iff (G : Modules.{u, u} B S hS X hX)
    (U : SmallEtale B S hS X) :
    (restrictToChart B S hS hX G U).IsQuasicoherent ↔
      (restrictToChartScheme B S hS X hX G U).IsQuasicoherent := by
  let : HasSheafify (Opens.grothendieckTopology (etaleChartScheme B S hS U))
      AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  let : (Opens.grothendieckTopology (etaleChartScheme B S hS U)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  exact ObjectProperty.prop_iff_of_iso _
    (restrictToChartIsoRestrictToChartScheme B S hS hX G U)

end AlgebraicGeometry.Space

end
