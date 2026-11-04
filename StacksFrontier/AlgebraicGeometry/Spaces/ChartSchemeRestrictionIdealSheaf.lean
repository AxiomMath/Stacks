module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafKer
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Basis
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian

/-!
# The restriction of a sheaf of ideals to the scheme of an étale chart

Let `X` be an algebraic space over a scheme `S`, let `𝓝 ⊆ 𝒪_X` be a sheaf of ideals on the small
étale site of `X` whose sections over affine charts are compatible with restriction, and let `A`
be an étale scheme chart of `X`. The ideals of sections of `𝓝` over the affine opens of the
scheme of `A` form a sheaf of ideals `𝓝_A` on that scheme
(`AlgebraicGeometry.Space.idealSheafDataOfChart`). The restriction of the `𝒪_X`-module `𝓝` to the
scheme of `A` is the ideal sheaf of `𝓝_A`, as an `𝒪_A`-module:

`𝓝|_A ≅ 𝓘_{V(𝓝_A)}`.

## Main definitions

* `AlgebraicGeometry.Space.chartRestrictionIdealToUnit`: the restriction of `𝓝` to the chart,
  mapped into the structure sheaf of the chart's scheme.
* `AlgebraicGeometry.Space.chartIdealToNegativeTwist`: its lift to the ideal sheaf of `V(𝓝_A)`.
* `AlgebraicGeometry.Space.restrictToChartSchemeIsoNegativeTwist`: the isomorphism
  `𝓝|_A ≅ 𝓘_{V(𝓝_A)}`.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X : AlgebraicSpaces B S hS)
  (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
  (hN : IsCartesianOnAffineCharts N.toSheafOfModules) (A : SmallEtale B S hS X.1)

section

attribute [local instance] isContinuous_openChartFunctor

/-- The canonical map from the structure sheaf of the chart to the direct image of the
structure sheaf of `X`; it is pullback of regular functions along the opens of the chart. -/
abbrev chartUnitToPushforward :
    SheafOfModules.unit (chartScheme A).ringCatSheaf ⟶
      (SheafOfModules.pushforward.{u} (chartSchemeRestrictionSheafHom B S hS X.2 A)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  SheafOfModules.unitToPushforwardObjUnit (chartSchemeRestrictionSheafHom B S hS X.2 A)

/-- On sections over a Zariski open `W`, `AlgebraicGeometry.Space.chartUnitToPushforward` is the
comparison `Γ(A, W) ≅ Γ(W, ⊤)`. -/
theorem chartUnitToPushforward_val_app (W : (chartScheme A).Opens)
    (r : Γ(chartScheme A, W)) :
    (chartUnitToPushforward X A).val.app (op W) r =
      (W.topIso.inv.hom r : Γ(W.toScheme, ⊤)) := rfl

/-- The comparison of the structure sheaf of the chart with the direct image of `𝒪_X` is an
isomorphism: on every Zariski open it is the isomorphism `Γ(A, W) ≅ Γ(W, ⊤)`. -/
instance isIso_chartUnitToPushforward : IsIso (chartUnitToPushforward X A) := by
  have h : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      (chartUnitToPushforward X A)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro W
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ConcreteCategory.bijective_of_isIso
      (Scheme.Opens.topIso (X := chartScheme A) W.unop).inv
  exact isIso_of_reflects_iso _ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)

/-- The inverse of `AlgebraicGeometry.Space.chartUnitToPushforward` is, on sections, the
comparison `Γ(W, ⊤) ≅ Γ(A, W)`. -/
theorem inv_chartUnitToPushforward_val_app (W : (chartScheme A).Opens)
    (x : Γ(W.toScheme, ⊤)) :
    (inv (chartUnitToPushforward X A)).val.app (op W) x = W.topIso.hom.hom x := by
  have h : (chartUnitToPushforward X A).val.app (op W)
      ((inv (chartUnitToPushforward X A)).val.app (op W) x) = x :=
    congrArg (fun g => g.val.app (op W) x) (IsIso.inv_hom_id (chartUnitToPushforward X A))
  replace h : W.topIso.inv.hom ((inv (chartUnitToPushforward X A)).val.app (op W) x) = x := h
  exact ((ConcreteCategory.congr_hom W.topIso.inv_hom_id _).symm).trans
    (congrArg W.topIso.hom.hom h)

/-- The restriction of a sheaf of ideals of `𝒪_X` to the scheme of a chart, mapped into the
structure sheaf of that scheme. -/
def chartRestrictionIdealToUnit :
    (SheafOfModules.pushforward.{u} (chartSchemeRestrictionSheafHom B S hS X.2 A)).obj
        N.toSheafOfModules ⟶ SheafOfModules.unit (chartScheme A).ringCatSheaf :=
  (SheafOfModules.pushforward.{u} (chartSchemeRestrictionSheafHom B S hS X.2 A)).map N.ι ≫
    inv (chartUnitToPushforward X A)

/-- On sections over a Zariski open `W`, `AlgebraicGeometry.Space.chartRestrictionIdealToUnit`
sends a section of `𝓝` over the chart `W` cuts out to the corresponding function on `W`. -/
theorem chartRestrictionIdealToUnit_val_app (W : (chartScheme A).Opens)
    (a : N.obj (op (openChart B S hS X.1 A W))) :
    (chartRestrictionIdealToUnit X N A).val.app (op W) a = openChartTopRingHom B S hS X A W a.1 :=
  inv_chartUnitToPushforward_val_app X A W a.1

/-- `AlgebraicGeometry.Space.chartRestrictionIdealToUnit` is injective on sections. -/
theorem injective_chartRestrictionIdealToUnit_val_app (W : (chartScheme A).Opens) :
    Function.Injective ((chartRestrictionIdealToUnit X N A).val.app (op W)) := by
  intro a b h
  have h' : openChartTopRingHom B S hS X A W a.1 = openChartTopRingHom B S hS X A W b.1 :=
    (chartRestrictionIdealToUnit_val_app X N A W a).symm.trans
      (h.trans (chartRestrictionIdealToUnit_val_app X N A W b))
  exact Subtype.ext ((Scheme.Opens.topIso (X := chartScheme A) W).commRingCatIsoToRingEquiv
    |>.injective h')

/-- Over an affine open the image of `AlgebraicGeometry.Space.chartRestrictionIdealToUnit` lies in
the ideal of the chart sheaf of ideals. -/
theorem chartRestrictionIdealToUnit_val_app_mem (W : (chartScheme A).affineOpens)
    (a : N.obj (op (openChart B S hS X.1 A W.1))) :
    (show Γ(chartScheme A, W.1) from (chartRestrictionIdealToUnit X N A).val.app (op W.1) a) ∈
      (idealSheafDataOfChart B S hS X N hN A).ideal W := by
  rw [ideal_idealSheafDataOfChart]
  exact (chartRestrictionIdealToUnit_val_app X N A W.1 a).symm ▸ Ideal.mem_map_of_mem _ a.2

/-- The restriction of the sheaf of ideals to the chart, as a module over the structure sheaf of
the chart's scheme read as a ringed space. -/
abbrev chartIdealPushforward :
    SheafOfModules.{u} (structureSheafRing (chartScheme A).toRingedSpace) :=
  (SheafOfModules.pushforward.{u} (chartSchemeRestrictionSheafHom B S hS X.2 A)).obj
    N.toSheafOfModules

/-- `AlgebraicGeometry.Space.chartRestrictionIdealToUnit`, read over the structure sheaf of the
chart's scheme as a ringed space. -/
abbrev chartRestrictionIdealToUnitRingedSpace : chartIdealPushforward X N A ⟶
    SheafOfModules.unit (structureSheafRing (chartScheme A).toRingedSpace) :=
  chartRestrictionIdealToUnit X N A

/-- `AlgebraicGeometry.Space.chartRestrictionIdealToUnit` is killed by the map of structure sheaves
of the closed subscheme cut out by the chart sheaf of ideals. -/
theorem chartRestrictionIdealToUnit_comp_structureSheafModuleHom :
    chartRestrictionIdealToUnitRingedSpace X N A ≫ structureSheafModuleHom
      (idealSheafDataOfChart B S hS X N hN A).subschemeι.toLRSHom.toShHom = 0 := by
  refine Stacks.AlgebraicGeometry.ModuleHomGlue.hom_ext_of_isBasis
    (B := fun W : (chartScheme A).affineOpens => W.1)
    (by simpa using (chartScheme A).isBasis_affineOpens) fun W a => ?_
  have hmem := chartRestrictionIdealToUnit_val_app_mem X N hN A W a
  rw [← Stacks.ClosedImmersion.range_idealSheafι_val_app_subschemeι] at hmem
  exact (Stacks.ClosedImmersion.mem_range_idealSheafι_val_app_iff _ W.1 _).mp hmem

/-- The lift of `AlgebraicGeometry.Space.chartRestrictionIdealToUnit` to the ideal sheaf of the
subscheme cut out by the chart sheaf of ideals, a kernel. -/
def chartIdealToNegativeTwist : chartIdealPushforward X N A ⟶
    Stacks.Divisors.negativeTwist' (idealSheafDataOfChart B S hS X N hN A) :=
  kernel.lift _ (chartRestrictionIdealToUnitRingedSpace X N A)
    (chartRestrictionIdealToUnit_comp_structureSheafModuleHom X N hN A)

/-- `AlgebraicGeometry.Space.chartIdealToNegativeTwist` lifts
`AlgebraicGeometry.Space.chartRestrictionIdealToUnit`. -/
theorem chartIdealToNegativeTwist_comp_idealSheafι :
    chartIdealToNegativeTwist X N hN A ≫ Stacks.ClosedImmersion.idealSheafι
      (idealSheafDataOfChart B S hS X N hN A).subschemeι.toLRSHom.toShHom =
      chartRestrictionIdealToUnitRingedSpace X N A :=
  kernel.lift_ι _ _ _

/-- `AlgebraicGeometry.Space.chartIdealToNegativeTwist` is an isomorphism: over every affine open
both sides are the ideal of the chart sheaf of ideals there. -/
instance isIso_chartIdealToNegativeTwist : IsIso (chartIdealToNegativeTwist X N hN A) := by
  set K := idealSheafDataOfChart B S hS X N hN A
  set j := K.subschemeι.toLRSHom.toShHom
  have hcomp : ∀ (W : (chartScheme A).Opens) (a : N.obj (op (openChart B S hS X.1 A W))),
      (Stacks.ClosedImmersion.idealSheafι j).val.app (op W)
        ((chartIdealToNegativeTwist X N hN A).val.app (op W) a) =
        (chartRestrictionIdealToUnit X N A).val.app (op W) a := fun W a =>
    congrArg (fun f => f.val.app (op W) a) (chartIdealToNegativeTwist_comp_idealSheafι X N hN A)
  refine Scheme.Modules.isIso_of_isIso_app_affineOpens _ fun W =>
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b h => ?_, fun y => ?_⟩
  · exact injective_chartRestrictionIdealToUnit_val_app X N A W.1
      ((hcomp W.1 a).symm.trans ((congrArg _ h).trans (hcomp W.1 b)))
  · have hy : (show Γ(chartScheme A, W.1) from
        (Stacks.ClosedImmersion.idealSheafι j).val.app (op W.1) y) ∈ K.ideal W := by
      rw [← Stacks.ClosedImmersion.range_idealSheafι_val_app_subschemeι]
      exact ⟨y, rfl⟩
    rw [ideal_idealSheafDataOfChart] at hy
    obtain ⟨a, ha, hay⟩ := (Ideal.mem_map_iff_of_surjective _
      (Scheme.Opens.topIso (X := chartScheme A) W.1).commRingCatIsoToRingEquiv.surjective).mp hy
    exact ⟨⟨a, ha⟩, Stacks.ClosedImmersion.injective_idealSheafι_val_app j W.1
      ((hcomp W.1 ⟨a, ha⟩).trans
        ((chartRestrictionIdealToUnit_val_app X N A W.1 ⟨a, ha⟩).trans hay))⟩

/-- **The restriction of a sheaf of ideals to the scheme of an étale chart is the ideal sheaf of
the chart sheaf of ideals.** For a sheaf of ideals `𝓝 ⊆ 𝒪_X` cartesian on affine charts and an
étale chart `A` of `X`, the restriction of `𝓝` to the scheme of `A` is isomorphic to the ideal
sheaf `𝓘_{V(𝓝_A)}` of the sheaf of ideals `𝓝_A = AlgebraicGeometry.Space.idealSheafDataOfChart`
that `𝓝` induces on that scheme. -/
def restrictToChartSchemeIsoNegativeTwist :
    restrictToChartScheme B S hS X.1 X.2 N.toSheafOfModules A ≅
      Stacks.Divisors.negativeTwist' (idealSheafDataOfChart B S hS X N hN A) :=
  restrictToChartSchemeIsoPushforward B S hS X.2 A N.toSheafOfModules ≪≫
    @asIso _ _ _ _ (chartIdealToNegativeTwist X N hN A) (isIso_chartIdealToNegativeTwist X N hN A)

end

end AlgebraicGeometry.Space

end
