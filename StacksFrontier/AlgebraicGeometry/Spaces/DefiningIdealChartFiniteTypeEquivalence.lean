module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafDataComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealChartFiniteGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSchemeDescent

/-!
# Finite type of the defining ideal sheaf is finite generation on one chart

For a closed subspace `Z ⊆ X` of an algebraic space, finite generation of the chart ideal of `𝓘_Z`
over the affine opens of one surjective étale scheme chart implies that `𝓘_Z` is of finite type as
a module on the small étale site of `X`. With the converse,
`AlgebraicGeometry.Space.fg_ideal_ker_rep_snd_of_isFiniteTypeOnSite`, this is the étale-locality
of finite type for a defining ideal sheaf used in Stacks 084Q.

All declarations below are in the namespace `AlgebraicGeometry.Space`.

## Main results

* `moduleFinite_sections_chartRestrictionSheaf_definingIdealSheaf_of_fg`: finite generation of the
  chart ideals makes the sections of the chart restriction a finite module over the functions on
  each affine open.
* `isFiniteType_chartSchemeModule_definingIdealSheaf_of_fg`: hence the chart restriction, read on
  the Zariski site of the chart's scheme, is of finite type.
* `isFiniteTypeOnSite_definingIdealSheaf_of_fg_chartIdeal_of_isSurjective`: finite type of `𝓘_Z`
  from finite generation on one surjective chart.
* `isFiniteTypeOnSite_definingIdealSheaf_iff_fg_ideal_ker_rep_snd_of_isSurjective`: on a surjective
  chart, finite type of `𝓘_Z` is equivalent to finite generation of the kernel ideals of the base
  change `Z ×_X A ⟶ A`.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- **Finite generation of the chart ideals makes the sections of the chart restriction of the
defining ideal sheaf a finite module.** If the chart ideal of `𝓘_Z` is finitely generated over
every affine open of the étale chart `A`, then for every affine open `V` of `A` the sections of the
chart restriction of `𝓘_Z` over `V` form a finite `Γ(A, V)`-module. -/
theorem moduleFinite_sections_chartRestrictionSheaf_definingIdealSheaf_of_fg
    (A : SmallEtale B S hS X.1)
    (hfg : ∀ W : (chartScheme A).affineOpens,
      (chartIdeal B S hS X (definingIdealSheaf B S hS X Z)
        ((chartOpens B S hS A).obj W.1)).FG)
    (V : (chartScheme A).affineOpens) :
    Module.Finite Γ(chartScheme A, V.1)
      Γ(chartRestrictionSheaf B S hS X
        (definingIdealSheaf B S hS X Z).toSheafOfModules A, V.1) := by
  have hfin : Module.Finite (chartRing B S hS X.1 X.2 ((chartOpens B S hS A).obj V.1))
      ↥(chartIdeal B S hS X (definingIdealSheaf B S hS X Z)
        ((chartOpens B S hS A).obj V.1)) :=
    Module.Finite.iff_fg.mpr (hfg V)
  let : Module (Γ(↑(V.1), ⊤) : Type u)
      ((definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj
        (op ((chartOpens B S hS A).obj V.1)) : Type u) :=
    moduleChartSections B S hS X (definingIdealSheaf B S hS X Z).toSheafOfModules
      ((chartOpens B S hS A).obj V.1)
  have : Module.Finite (Γ(↑(V.1), ⊤) : Type u)
      ((definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj
        (op ((chartOpens B S hS A).obj V.1)) : Type u) := hfin
  refine Module.Finite.of_surjective
    (f := ({ toFun := fun m => ULift.up m
             map_add' := fun _ _ => rfl
             map_smul' := fun r m => congrArg ULift.up (congrArg (fun y => y • m)
               (ConcreteCategory.congr_hom V.1.topIso.hom_inv_id r).symm) } :
      ((definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj
          (op ((chartOpens B S hS A).obj V.1)) : Type u) →ₛₗ[(V.1.topIso.hom).hom]
        (Γ(chartRestrictionSheaf B S hS X
          (definingIdealSheaf B S hS X Z).toSheafOfModules A, V.1) : Type u))) ?_
  exact fun y => ⟨y.down, rfl⟩

/-- **The chart restriction of the defining ideal sheaf is of finite type on the Zariski site of
the chart's scheme**, as soon as the chart ideals over the affine opens of that chart are finitely
generated. -/
theorem isFiniteType_chartSchemeModule_definingIdealSheaf_of_fg
    (A : SmallEtale B S hS X.1)
    (hfg : ∀ W : (chartScheme A).affineOpens,
      (chartIdeal B S hS X (definingIdealSheaf B S hS X Z)
        ((chartOpens B S hS A).obj W.1)).FG) :
    SheafOfModules.IsFiniteType (chartSchemeModule B S hS X
      (definingIdealSheaf B S hS X Z).toSheafOfModules
      (isQuasicoherentOnSite_definingIdealSheaf B S hS X Z) A) := by
  have : (chartRestrictionSheaf B S hS X
      (definingIdealSheaf B S hS X Z).toSheafOfModules A).IsQuasicoherent :=
    isQuasicoherent_chartRestrictionSheaf B S hS X _
      (isQuasicoherentOnSite_definingIdealSheaf B S hS X Z) A
  have : (chartRestrictionSheaf B S hS X
      (definingIdealSheaf B S hS X Z).toSheafOfModules A).IsFiniteType :=
    Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_of_forall_moduleFinite_sections _
      (moduleFinite_sections_chartRestrictionSheaf_definingIdealSheaf_of_fg B S hS X Z A hfg)
  have : (restrictToChart B S hS X.2
      (definingIdealSheaf B S hS X Z).toSheafOfModules A).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso
      (restrictToChartIsoChartRestrictionSheaf B S hS X _ A).symm
  exact Stacks.SheafOfModules.isFiniteType_of_iso
    (restrictToChartIsoChartSchemeModule B S hS X _
      (isQuasicoherentOnSite_definingIdealSheaf B S hS X Z) A)

/-- **Finite type of the defining ideal sheaf from finite generation on one surjective chart.**
If the chart ideal of `𝓘_Z` is finitely generated over every affine open of one étale scheme chart
whose structure morphism is surjective on points, then `𝓘_Z` is of finite type on the small étale
site of `X`. -/
theorem isFiniteTypeOnSite_definingIdealSheaf_of_fg_chartIdeal_of_isSurjective
    (A : SmallEtale B S hS X.1) (hsurj : IsSurjective B S hS A.1.hom)
    (hfg : ∀ W : (chartScheme A).affineOpens,
      (chartIdeal B S hS X (definingIdealSheaf B S hS X Z)
        ((chartOpens B S hS A).obj W.1)).FG) :
    SheafOfModules.IsFiniteTypeOnSite
      (definingIdealSheaf B S hS X Z).toSheafOfModules :=
  isFiniteTypeOnSite_of_isFiniteType_chartSchemeModule_of_isSurjective B S hS X _
    (isQuasicoherentOnSite_definingIdealSheaf B S hS X Z) A hsurj
    (isFiniteType_chartSchemeModule_definingIdealSheaf_of_fg B S hS X Z A hfg)

/-- Finite generation passes from the ideal cut out on a Zariski open of the chart's scheme to the
chart ideal at the étale chart that open cuts out. -/
theorem fg_chartIdeal_openChart_of_fg_openChartIdeal
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens)
    (h : (openChartIdeal B S hS X N A W).FG) :
    (chartIdeal B S hS X N (openChart B S hS X.1 A W)).FG := by
  have hfgmap : (Ideal.map (W.topIso.inv).hom (openChartIdeal B S hS X N A W)).FG :=
    Ideal.FG.map h _
  rwa [show Ideal.map (W.topIso.inv).hom (openChartIdeal B S hS X N A W)
      = chartIdeal B S hS X N (openChart B S hS X.1 A W) from
    Stacks.Ideal.map_map_of_leftInverse (openChartTopRingHom B S hS X A W) (W.topIso.inv).hom
      (fun x => ConcreteCategory.congr_hom W.topIso.hom_inv_id x) _] at hfgmap

/-- **Finite type of `𝓘_Z` from finite generation on one surjective chart**, with the chart ideal
in the spelling Stacks 084Q uses — the kernel of pullback of regular functions along the base
change `Z ×_X A ⟶ A`. -/
theorem isFiniteTypeOnSite_definingIdealSheaf_of_fg_ideal_ker_rep_snd_of_isSurjective
    (A : SmallEtale B S hS X.1) (hsurj : IsSurjective B S hS A.1.hom)
    (hfg : ∀ W : (chartScheme A).affineOpens,
      (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).ker.ideal W).FG) :
    SheafOfModules.IsFiniteTypeOnSite
      (definingIdealSheaf B S hS X Z).toSheafOfModules := by
  refine isFiniteTypeOnSite_definingIdealSheaf_of_fg_chartIdeal_of_isSurjective
    B S hS X Z A hsurj (fun W => ?_)
  rw [chartOpens_obj_eq_openChart]
  refine fg_chartIdeal_openChart_of_fg_openChartIdeal B S hS X _ A W.1 ?_
  have hW := hfg W
  rwa [ker_rep_snd_eq_idealSheafDataOfChart B S hS X Z A] at hW

/-- **Finite type of the defining ideal sheaf is finite generation of the chart ideal on one
surjective étale scheme chart.** For a surjective étale chart `A`, the defining ideal sheaf `𝓘_Z`
is of finite type on the small étale site of `X` if and only if, over every affine open `W` of `A`,
the kernel of pullback of regular functions along the base change `Z ×_X A ⟶ A` is finitely
generated. -/
theorem isFiniteTypeOnSite_definingIdealSheaf_iff_fg_ideal_ker_rep_snd_of_isSurjective
    (A : SmallEtale B S hS X.1) (hsurj : IsSurjective B S hS A.1.hom) :
    SheafOfModules.IsFiniteTypeOnSite
        (definingIdealSheaf B S hS X Z).toSheafOfModules ↔
      ∀ W : (chartScheme A).affineOpens,
        (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).ker.ideal W).FG :=
  ⟨fun hft W => fg_ideal_ker_rep_snd_of_isFiniteTypeOnSite B S hS X Z hft A W,
    isFiniteTypeOnSite_definingIdealSheaf_of_fg_ideal_ker_rep_snd_of_isSurjective
      B S hS X Z A hsurj⟩

end AlgebraicGeometry.Space

end
