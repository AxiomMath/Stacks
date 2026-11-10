module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExceptionalTwistChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartHomEquivComponent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealPowerFactorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSeparator
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjGlueing

/-!
# The pullback of the ideal sheaf of a closed subspace to an étale scheme chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `Z ⊆ X` be a
closed subspace with defining ideal sheaf `𝓘_Z ⊆ 𝒪_X` (Stacks 03MB) and let `φ : U ⟶ X` be an
étale morphism from a scheme, read as a morphism of algebraic spaces.  The base change
`Z ×_X U ⟶ U` is a closed immersion of schemes, and its ideal sheaf `ker(𝒪_U ⟶ (Z ×_X U)_* 𝒪)`
is the pullback of `𝓘_Z`, at the level of modules:

`φ^* 𝓘_Z ≅ (ker(𝒪_U ⟶ 𝒪_{Z ×_X U}))^a`,

where `(-)^a` is the associated module on the small étale site of the representable algebraic
space `U` (Stacks 03DU).  For the étale atlas `P_U ⟶ X'` of the blowing up `b : X' ⟶ X` of an
algebraic space along `Z` (Stacks 085Q) and the exceptional divisor `E = b⁻¹(Z)`, the pullback of
`𝓘_E` to the chart is therefore the module associated with the ideal sheaf of `E ×_{X'} P_U`.

## Main definitions

* `AlgebraicGeometry.Space.chartPushUnitIso`: the chart restriction of `𝒪_X` to an étale scheme
  chart is the structure sheaf of the chart's scheme.
* `AlgebraicGeometry.Space.chartPushDefiningIdealIso`: **the chart restriction of `𝓘_Z` is the
  ideal sheaf of the base change `Z ×_X A ⟶ A`**, on the Zariski site of the chart's scheme.
* `AlgebraicGeometry.Space.representedAssociatedChartSchemeModuleIso`: the associated module of
  the chart restriction of a quasi-coherent `𝒪_X`-module is its pullback along the chart.
* `AlgebraicGeometry.Space.modulePullbackChartToSpaceDefiningIdealIso`: **the pullback of `𝓘_Z`
  along an étale scheme chart is the associated module of the ideal sheaf of the base change.**
* `AlgebraicGeometry.Space.modulePullbackPresentationAtlasDefiningIdealIso`: the same along the
  atlas of a presentation, with the associated module read through
  `AlgebraicGeometry.Space.presentationObjectsFunctor`.
* `AlgebraicGeometry.Space.modulePullbackBlowUpAtlasExceptionalIdealIso`: the case of the
  exceptional divisor of the blowing up of an algebraic space, along the atlas `P_U ⟶ X'`.

## Main results

* `AlgebraicGeometry.Space.app_eq_zero_iff_chartSectionsRingHom_mem_definingIdealAt`: **the
  sectionwise statement.**  Over a Zariski open `V` of the chart's scheme, a function lies in the
  kernel of pullback along `Z ×_X A ⟶ A` exactly when, read on the étale chart that `V` cuts out,
  it lies in the defining ideal of `Z` there.
* `AlgebraicGeometry.Space.bijective_chartSectionsRingHom`: the scalar map of the chart sections
  identification is bijective.

## Implementation notes

The chart restriction is taken in its direct-image spelling `AlgebraicGeometry.Space.chartPush`,
whose sections over a Zariski open `V` are, on the nose, the sections of the module over the
étale chart which `V` cuts out; `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush` connects
it with the chart restriction `AlgebraicGeometry.Space.chartSchemeModule` of Stacks 03DX (2),
whose associated module is the pullback along the chart.

## References

* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- Pulling back a function on an open `U` along the restriction `f ∣_ U` kills it exactly when
`f.app U` does, the function being read on `U` as a scheme through
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
theorem morphismRestrict_appTop_topIso_inv_eq_zero_iff {Y T : Scheme.{u}} (f : Y ⟶ T)
    (U : T.Opens) (s : Γ(T, U)) :
    (f ∣_ U).appTop (U.topIso.inv s) = 0 ↔ f.app U s = 0 := by
  have h := resLE_appTop_comp_topIso_hom f (V := U) (le_refl (f ⁻¹ᵁ U))
  rw [Scheme.Hom.resLE_eq_morphismRestrict, ← Scheme.Hom.app_eq_appLE] at h
  have h' := ConcreteCategory.congr_hom h (U.topIso.inv s)
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] at h'
  rw [← h']
  exact (map_eq_zero_iff (f ⁻¹ᵁ U).topIso.hom.hom
    (ConcreteCategory.bijective_of_isIso (f ⁻¹ᵁ U).topIso.hom).1).symm

/-- The same, for any morphism identified with `f ∣_ U` by an isomorphism of its source. -/
theorem appTop_topIso_inv_eq_zero_iff_of_iso {P Y T : Scheme.{u}} (f : Y ⟶ T) (U : T.Opens)
    (h : P ⟶ U.toScheme) (e : P ≅ f ⁻¹ᵁ U) (he : e.hom ≫ (f ∣_ U) = h) (s : Γ(T, U)) :
    h.appTop (U.topIso.inv s) = 0 ↔ f.app U s = 0 := by
  subst he
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
  exact (map_eq_zero_iff e.hom.appTop.hom
    (ConcreteCategory.bijective_of_isIso e.hom.appTop).1).trans
    (morphismRestrict_appTop_topIso_inv_eq_zero_iff f U s)

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

section Chart

variable (A : SmallEtale B S hS X.1)

/-- **The scalar map of the chart sections identification is bijective.**  Its inverse is the
comparison `AlgebraicGeometry.Scheme.Opens.topIso` read as
`AlgebraicGeometry.Space.openChartTopRingHom`. -/
theorem bijective_chartSectionsRingHom (V : (chartScheme A).Opens) :
    Function.Bijective (chartSectionsRingHom B S hS X A V) :=
  Function.bijective_iff_has_inverse.2 ⟨openChartTopRingHom B S hS X A V,
    openChartTopRingHom_chartSectionsRingHom B S hS X A V,
    chartSectionsRingHom_openChartTopRingHom B S hS X A V⟩

/-- The comparison of the structure sheaf of the chart's scheme with the chart restriction of
`𝒪_X`: the unit map of the direct image along the composite comparison functor of the chart. -/
abbrev chartPushUnitMap :
    SheafOfModules.unit (chartScheme A).ringCatSheaf ⟶
      chartPush B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)) A :=
  SheafOfModules.unitToPushforwardObjUnit (chartComparisonRingMap B S hS X A)

/-- The comparison `AlgebraicGeometry.Space.chartPushUnitMap` is an isomorphism. -/
theorem isIso_chartPushUnitMap : IsIso (chartPushUnitMap B S hS X A) :=
  Stacks.SheafOfModules.isIso_of_bijective_val_app _ fun V =>
    bijective_chartSectionsRingHom B S hS X A V.unop

/-- **The chart restriction of `𝒪_X` is the structure sheaf of the chart's scheme.** -/
def chartPushUnitIso :
    SheafOfModules.unit (chartScheme A).ringCatSheaf ≅
      chartPush B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)) A :=
  @asIso _ _ _ _ (chartPushUnitMap B S hS X A) (isIso_chartPushUnitMap B S hS X A)

variable (Z : ClosedSubspaces B S hS X.1)

/-- **The ideal sheaf of the base change of a closed subspace to a chart, sectionwise.**  Let `A`
be an étale scheme chart of `X` and `V` a Zariski open of its scheme.  A function `s` on `V` is
killed by pullback along the closed immersion `Z ×_X A ⟶ A` exactly when its image under the
chart sections identification `AlgebraicGeometry.Space.chartSectionsRingHom` lies in the defining
ideal of `Z` at the étale chart cut out by `V`. -/
theorem app_eq_zero_iff_chartSectionsRingHom_mem_definingIdealAt
    (V : (chartScheme A).Opens) (s : Γ(chartScheme A, V)) :
    ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).app V s = 0 ↔
      chartSectionsRingHom B S hS X A V s ∈
        definingIdealAt B S hS X Z (op (openChartOfComparison B S hS X A V)) := by
  set f := (BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom) with hf
  have hC : yoneda.map ((SmallEtale.toOver B S hS X.1).map
      (openChartOfComparisonOver B S hS X A V).hom) ≫ A.1.hom =
        (openChartOfComparison B S hS X A V).1.hom :=
    CostructuredArrow.w (openChartOfComparisonOver B S hS X A V).hom.hom
  obtain ⟨l, hsq⟩ := exists_isPullback_snd_comp B S hS Z.2.2.rep A.1.hom
    ((SmallEtale.toOver B S hS X.1).map (openChartOfComparisonOver B S hS X A V).hom)
    (openChartOfComparison B S hS X A V).1.hom hC
  have hsq' : IsPullback ((BigFppfOver.toScheme B S hS).map l)
      ((BigFppfOver.toScheme B S hS).map
        (Z.2.2.rep.snd (openChartOfComparison B S hS X A V).1.hom)) f V.ι := hsq
  let e := hsq'.isoIsPullback _ _ (isPullback_morphismRestrict f V).flip
  have he : e.hom ≫ (f ∣_ V) = (BigFppfOver.toScheme B S hS).map
      (Z.2.2.rep.snd (openChartOfComparison B S hS X A V).1.hom) :=
    hsq'.isoIsPullback_hom_snd _ _ _
  have htop : V.topIso.hom (chartSectionsRingHom B S hS X A V s) = s :=
    openChartTopRingHom_chartSectionsRingHom B S hS X A V s
  have hs : chartSectionsRingHom B S hS X A V s = V.topIso.inv s :=
    (ConcreteCategory.bijective_of_isIso V.topIso.hom).1
      (htop.trans (Iso.inv_hom_id_apply V.topIso s).symm)
  rw [definingIdealAt_eq_ker]
  change _ ↔ ((BigFppfOver.toScheme B S hS).map
    (Z.2.2.rep.snd (openChartOfComparison B S hS X A V).1.hom)).appTop
      (chartSectionsRingHom B S hS X A V s) = 0
  rw [hs]
  exact (appTop_topIso_inv_eq_zero_iff_of_iso f V _ e he s).symm

/-- The inverse of `AlgebraicGeometry.Space.chartPushUnitIso` is
`AlgebraicGeometry.Space.openChartTopRingHom` on sections. -/
theorem chartPushUnitIso_inv_val_app (V : (chartScheme A).Opens)
    (y : (chartPush B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)) A).val.obj
      (op V)) :
    (chartPushUnitIso B S hS X A).inv.val.app (op V) y =
      openChartTopRingHom B S hS X A V y := by
  have h : (chartPushUnitIso B S hS X A).inv.val.app (op V)
      ((chartPushUnitIso B S hS X A).hom.val.app (op V)
        (openChartTopRingHom B S hS X A V y)) = openChartTopRingHom B S hS X A V y :=
    congrArg (fun φ => φ.val.app (op V) (openChartTopRingHom B S hS X A V y))
      (chartPushUnitIso B S hS X A).hom_inv_id
  have hy : (chartPushUnitIso B S hS X A).hom.val.app (op V)
      (openChartTopRingHom B S hS X A V y) = y :=
    chartSectionsRingHom_openChartTopRingHom B S hS X A V y
  exact (congrArg ((chartPushUnitIso B S hS X A).inv.val.app (op V)) hy).symm.trans h

/-- The chart restriction of the inclusion `𝓘_Z ⟶ 𝒪_X`, followed by the identification of the
chart restriction of `𝒪_X` with the structure sheaf of the chart's scheme. -/
def chartPushDefiningIdealι :
    chartPush B S hS X (definingIdealSheaf B S hS X Z).toSheafOfModules A ⟶
      SheafOfModules.unit (chartScheme A).ringCatSheaf :=
  (SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).map
      (definingIdealSheaf B S hS X Z).ι ≫ (chartPushUnitIso B S hS X A).inv

/-- On sections, `AlgebraicGeometry.Space.chartPushDefiningIdealι` is the inclusion of the
defining ideal followed by `AlgebraicGeometry.Space.openChartTopRingHom`. -/
theorem chartPushDefiningIdealι_val_app (V : (chartScheme A).Opens)
    (x : (chartPush B S hS X (definingIdealSheaf B S hS X Z).toSheafOfModules A).val.obj
      (op V)) :
    (chartPushDefiningIdealι B S hS X A Z).val.app (op V) x =
      openChartTopRingHom B S hS X A V
        ((definingIdealSheaf B S hS X Z).ι.val.app (op (openChartOfComparison B S hS X A V)) x) :=
  chartPushUnitIso_inv_val_app B S hS X A V
    ((definingIdealSheaf B S hS X Z).ι.val.app (op (openChartOfComparison B S hS X A V)) x)

/-- The ideal sheaf of the closed immersion `Z ×_X A ⟶ A`, as the sectionwise kernel of
`𝒪_A ⟶ (Z ×_X A)_* 𝒪`, a submodule of the structure sheaf of the chart's scheme. -/
abbrev chartBaseChangeIdealSubmodule :
    (SheafOfModules.unit (chartScheme A).ringCatSheaf).Submodule :=
  Stacks.Algebraization.kernelSubmodule (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom ((BigFppfOver.toScheme B S hS).map
      (Z.2.2.rep.snd A.1.hom)).toLRSHom.toShHom))

/-- Membership in `AlgebraicGeometry.Space.chartBaseChangeIdealSubmodule` over an open `V` is
being killed by pullback along `Z ×_X A ⟶ A` over `V`. -/
theorem mem_chartBaseChangeIdealSubmodule_iff (V : (chartScheme A).Opens)
    (r : (SheafOfModules.unit (chartScheme A).ringCatSheaf).val.obj (op V)) :
    r ∈ (chartBaseChangeIdealSubmodule B S hS X A Z).obj (op V) ↔
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).app V r = 0 :=
  (Iff.of_eq (congrArg (fun P => r ∈ P)
    (Stacks.Algebraization.kernelSubmodule_toSubmodule_obj _ (op V)))).trans LinearMap.mem_ker

/-- Over `V`, the function `openChartTopRingHom x` is killed by pullback along `Z ×_X A ⟶ A` exactly
when `x` lies in the defining ideal of `Z` at the étale chart cut out by `V`. -/
private theorem app_openChartTopRingHom_eq_zero_iff (V : (chartScheme A).Opens)
    (x : chartRing B S hS X.1 X.2 (openChartOfComparison B S hS X A V)) :
    ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).app V
        (openChartTopRingHom B S hS X A V x) = 0 ↔
      x ∈ definingIdealAt B S hS X Z (op (openChartOfComparison B S hS X A V)) := by
  refine (app_eq_zero_iff_chartSectionsRingHom_mem_definingIdealAt B S hS X A Z V _).trans ?_
  rw [chartSectionsRingHom_openChartTopRingHom B S hS X A V x]
  exact Iff.rfl

/-- The chart restriction of `𝓘_Z` lands in the ideal sheaf of the base change. -/
theorem chartPushDefiningIdealι_mem (V : ((chartScheme A).Opens)ᵒᵖ)
    (x : (chartPush B S hS X (definingIdealSheaf B S hS X Z).toSheafOfModules A).val.obj V) :
    (chartPushDefiningIdealι B S hS X A Z).val.app V x ∈
      (chartBaseChangeIdealSubmodule B S hS X A Z).obj V := by
  obtain ⟨V⟩ := V
  refine (mem_chartBaseChangeIdealSubmodule_iff B S hS X A Z V _).2 ?_
  rw [chartPushDefiningIdealι_val_app]
  exact (app_openChartTopRingHom_eq_zero_iff B S hS X A Z V _).2
    (x : (definingIdealSheaf B S hS X Z).obj _).2

/-- The chart restriction of `𝓘_Z`, factored through the ideal sheaf of the base change
`Z ×_X A ⟶ A`. -/
def chartPushDefiningIdealFactor :
    chartPush B S hS X (definingIdealSheaf B S hS X Z).toSheafOfModules A ⟶
      (chartBaseChangeIdealSubmodule B S hS X A Z).toSheafOfModules :=
  SheafOfModules.Submodule.factorThru _ (chartPushDefiningIdealι B S hS X A Z)
    (chartPushDefiningIdealι_mem B S hS X A Z)

/-- The factorization `AlgebraicGeometry.Space.chartPushDefiningIdealFactor` is bijective on
sections. -/
theorem bijective_chartPushDefiningIdealFactor_val_app (V : ((chartScheme A).Opens)ᵒᵖ) :
    Function.Bijective ((chartPushDefiningIdealFactor B S hS X A Z).val.app V) := by
  obtain ⟨V⟩ := V
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · have h1 := congrArg Subtype.val hab
    change (chartPushDefiningIdealι B S hS X A Z).val.app (op V) a =
      (chartPushDefiningIdealι B S hS X A Z).val.app (op V) b at h1
    have h1' := (chartPushDefiningIdealι_val_app B S hS X A Z V a).symm.trans
      (h1.trans (chartPushDefiningIdealι_val_app B S hS X A Z V b))
    have h2 := (ConcreteCategory.bijective_of_isIso V.topIso.hom).1 h1'
    exact (Subtype.val_injective h2 :)
  · have hy := (mem_chartBaseChangeIdealSubmodule_iff B S hS X A Z V y.1).1 y.2
    replace hy := (app_eq_zero_iff_chartSectionsRingHom_mem_definingIdealAt B S hS X A Z V
      y.1).1 hy
    refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
    change (chartPushDefiningIdealι B S hS X A Z).val.app (op V) ⟨_, hy⟩ = y.1
    exact (chartPushDefiningIdealι_val_app B S hS X A Z V ⟨_, hy⟩).trans
      (openChartTopRingHom_chartSectionsRingHom B S hS X A V y.1)

/-- The factorization `AlgebraicGeometry.Space.chartPushDefiningIdealFactor` is an
isomorphism. -/
instance isIso_chartPushDefiningIdealFactor :
    IsIso (chartPushDefiningIdealFactor B S hS X A Z) :=
  Stacks.SheafOfModules.isIso_of_bijective_val_app _
    (bijective_chartPushDefiningIdealFactor_val_app B S hS X A Z)

/-- **The chart restriction of the ideal sheaf of a closed subspace is the ideal sheaf of its base
change.**  For an étale scheme chart `A` of `X` and a closed subspace `Z ⊆ X`, the chart
restriction of `𝓘_Z` to the Zariski site of the chart's scheme is the ideal sheaf
`ker(𝒪_A ⟶ (Z ×_X A)_* 𝒪)` of the closed immersion `Z ×_X A ⟶ A`. -/
def chartPushDefiningIdealIso :
    chartPush B S hS X (definingIdealSheaf B S hS X Z).toSheafOfModules A ≅
      Stacks.ClosedImmersion.idealSheaf
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).toLRSHom.toShHom :=
  asIso (chartPushDefiningIdealFactor B S hS X A Z) ≪≫
    Stacks.Algebraization.kernelSubmoduleIso _

/-- **The associated module of the chart restriction of a quasi-coherent `𝒪_X`-module is its
pullback along the chart.**  This is the counit of Stacks 03DX (2) at the chart's scheme, the
reindexing along the comparison of the two small étale sites of the chart, and Equation 03LW for
the structure morphism of the chart. -/
def representedAssociatedChartSchemeModuleIso
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hM : M.IsQuasicoherentOnSite) :
    (representedAssociatedModuleFunctor B S hS (chartFppfObject B S hS X A)).obj
        (chartSchemeModule B S hS X M hM A) ≅
      (modulePullback B S hS (chartToSpace B S hS X A)).obj M :=
  (representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS X A)).functor.mapIso
      (associatedModuleChartSchemeModuleIso B S hS X M hM A) ≪≫
    representedSmallEtaleChartSchemeEtaleModuleIso B S hS X M hM A ≪≫
    chartSmallEtaleRestrictionFunctorObjIso X M A ≪≫
    ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X A)
      (isEtale_chartToSpace B S hS X A)).app M).symm

/-- **The pullback of the ideal sheaf of a closed subspace along an étale scheme chart is the
associated module of the ideal sheaf of the base change.**  For an étale scheme chart `A` of `X`
and a closed subspace `Z ⊆ X`, the pullback of `𝓘_Z` along `A ⟶ X` is the module on the small
étale site of the representable algebraic space `A` associated with the ideal sheaf of the closed
immersion `Z ×_X A ⟶ A`. -/
def modulePullbackChartToSpaceDefiningIdealIso :
    (modulePullback B S hS (chartToSpace B S hS X A)).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules ≅
      (representedAssociatedModuleFunctor B S hS (chartFppfObject B S hS X A)).obj
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).toLRSHom.toShHom) :=
  (representedAssociatedChartSchemeModuleIso B S hS X A _
      (isQuasicoherentOnSite_definingIdealSheaf B S hS X Z)).symm ≪≫
    (representedAssociatedModuleFunctor B S hS (chartFppfObject B S hS X A)).mapIso
      (chartSchemeModuleIsoChartPush B S hS X _
          (isQuasicoherentOnSite_definingIdealSheaf B S hS X Z) A ≪≫
        chartPushDefiningIdealIso B S hS X A Z)

end Chart

/-- **The pullback of the ideal sheaf of a closed subspace along the atlas of a presentation.**
For a presentation `X = U/R` and a closed subspace `Z ⊆ X`, the pullback of `𝓘_Z` along the atlas
`U ⟶ X` is the module associated, by `AlgebraicGeometry.Space.presentationObjectsFunctor`, with
the ideal sheaf of the closed immersion `Z ×_X U ⟶ U`. -/
def modulePullbackPresentationAtlasDefiningIdealIso (Z : ClosedSubspaces B S hS X.1)
    (P : Presentation B S hS X.1 X.2) :
    (modulePullback B S hS (presentationAtlas P)).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules ≅
      (presentationObjectsFunctor P).obj
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd P.toSpace)).toLRSHom.toShHom) :=
  modulePullbackChartToSpaceDefiningIdealIso B S hS X (presentationChart P) Z

section Blowup

variable {B S hS} {X} [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (Z : ClosedSubspaces B S hS X.obj) (P : Presentation B S hS X.obj X.property)
  (hcU : B.Contains (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR)))

/-- **The pullback of the ideal sheaf of the exceptional divisor to the étale atlas of the
blowup.**
Let `b : X' ⟶ X` be the blowing up of an algebraic space along a closed subspace `Z` (Stacks
085Q), with exceptional divisor `E = b⁻¹(Z)`, and let `P_U ⟶ X'` be the atlas of its presentation
by `P_R ⇉ P_U`.  The pullback of `𝓘_E` along the atlas is the module associated with the ideal
sheaf of the closed immersion `E ×_{X'} P_U ⟶ P_U`, whose sheaf of ideals is
`ℐ|_U · 𝒪_{P_U}` by `AlgebraicGeometry.Space.ker_rep_snd_chart_exceptionalDivisor`. -/
def modulePullbackBlowUpAtlasExceptionalIdealIso :
    (modulePullback B S hS (presentationAtlas
        (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
          P hcU hcR heq).presentationRelativeProj)).obj
        (definingIdealSheaf B S hS (blowUpAlong Z P hcU hcR heq)
          (exceptionalDivisor Z P hcU hcR heq)).toSheafOfModules ≅
      (presentationObjectsFunctor
          (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
            P hcU hcR heq).presentationRelativeProj).obj
        (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map
            ((exceptionalDivisor Z P hcU hcR heq).2.2.rep.snd
              (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
                P hcU hcR heq).chart)).toLRSHom.toShHom) :=
  modulePullbackPresentationAtlasDefiningIdealIso B S hS (blowUpAlong Z P hcU hcR heq)
    (exceptionalDivisor Z P hcU hcR heq)
    (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
      P hcU hcR heq).presentationRelativeProj

end Blowup

end AlgebraicGeometry.Space
