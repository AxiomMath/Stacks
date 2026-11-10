module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyBaseChangeFromDerived
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverPointVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageVanishingOnCoveringChart
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections

/-!
# `Rf_*𝒪_X` has no cohomology above degree one over a one-point base

Let `f : X ⟶ S` be a family of curves (Stacks 0D4Z) whose base `S` is an affine, locally
Noetherian scheme with one point, for instance the spectrum of a field. Then the higher direct
images `R^q f_*𝒪_X` vanish for `q ≥ 2`, that is, `Rf_*𝒪_X` lies in `D^{≤ 1}`.

The total space is a scheme, Noetherian of dimension at most one
(`AlgebraicGeometry.CurveFamily.exists_isTerminal_chart_of_subsingleton`), so its cohomology
stops in degree one (Cohomology, Proposition 02UZ); the base is affine and its identity chart
covers its small étale site, so the vanishing of `H^q(X, 𝓜)` is the vanishing of `R^q f_*𝓜`
(`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_coveringChart`).

This is the input "`H^i(X_s, 𝒪_{X_s}) = 0` for `i ≥ 2`" of the proof of Stacks 0E1J, in the form
that is read off the base change isomorphism of Stacks 0CTM, part (1), at the fibres.

## Main results

* `AlgebraicGeometry.CurveFamily.hasDerivedStructureSheafPushforwardIsLEOne_of_subsingleton`.

## Implementation notes

No declaration here carries a `stacks` attribute: it is a step of the proof of Stacks 0E1J.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

variable (Y : CurveFamily B hZ)
  [hY : Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj Y.base)]
  [hAff : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Y.base)]
  [hNoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj Y.base)]

include hY hAff hNoeth in
/-- The structure morphism of a family of curves over an affine locally Noetherian one-point base
is relatively representable: its source is a scheme. -/
theorem relativelyRepresentable_toBase_of_subsingleton :
    yoneda.relativelyRepresentable Y.toBase.hom := by
  have := Y.isRepresentable_total_of_subsingleton
  let e : yoneda.obj Y.total.obj.reprX ≅ Y.total.obj := Y.total.obj.reprW
  let q : Y.total.obj.reprX ⟶ Y.base := yoneda.preimage (e.hom ≫ Y.toBase.hom)
  have hq : Y.toBase.hom = e.inv ≫ yoneda.map q := by simp [q]
  rw [hq]
  exact (MorphismProperty.cancel_left_of_respectsIso _ e.inv _).2
    (Space.relativelyRepresentable_yoneda_map B integerBase hZ q)

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis on the chart schemes of `Space.smallBaseChange` is deep
include hY hAff hNoeth in
/-- **The chart of the total space over the identity chart of the base is a Noetherian scheme of
dimension at most one.** Its structure map to the total space is an isomorphism, so it is
isomorphic to the terminal chart of `exists_isTerminal_chart_of_subsingleton`. -/
theorem noetherianSpace_and_dim_le_chartScheme_smallBaseChange_idEtaleChart
    (hp : yoneda.relativelyRepresentable Y.toBase.hom) :
    NoetherianSpace (Space.chartScheme ((Space.smallBaseChange B integerBase hZ Y.toBase hp).obj
        (Space.idEtaleChart B integerBase hZ Y.base))) ∧
      topologicalKrullDim (Space.chartScheme ((Space.smallBaseChange B integerBase hZ Y.toBase
        hp).obj (Space.idEtaleChart B integerBase hZ Y.base))) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨A, ⟨hA⟩, hN, hdim⟩ := Y.exists_isTerminal_chart_of_subsingleton
  set W := (Space.smallBaseChange B integerBase hZ Y.toBase hp).obj
    (Space.idEtaleChart B integerBase hZ Y.base)
  have hW : IsIso W.obj.hom := by
    have sq := hp.isPullback (𝟙 (yoneda.obj Y.base))
    exact sq.isIso_fst_of_isIso (inst := IsIso.id _)
  have hWt : IsTerminal W := IsTerminal.ofUniqueHom
    (fun A' => ObjectProperty.homMk (CostructuredArrow.homMk
      (yoneda.preimage (A'.obj.hom ≫ inv W.obj.hom)) (by simp)))
    (fun A' m => ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
      (yoneda.map_injective (by
        have hw := CostructuredArrow.w m.hom
        change _ = yoneda.map (yoneda.preimage (A'.obj.hom ≫ inv W.obj.hom))
        rw [Functor.map_preimage, ← hw]
        simp))))
  let i : W ≅ A := hWt.uniqueUpToIso hA
  let φ : Space.chartScheme W ≃ₜ Space.chartScheme A :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso ((BigFppfOver.toScheme B integerBase hZ).mapIso
      ((ObjectProperty.ι _ ⋙ CostructuredArrow.proj _ _).mapIso i)))
  refine ⟨φ.isClosedEmbedding.noetherianSpace, ?_⟩
  rwa [← IsHomeomorph.topologicalKrullDim_eq _ φ.isHomeomorph] at hdim

include hY hAff hNoeth in
/-- **`Rf_*𝒪_X ∈ D^{≤ 1}` for a family of curves over an affine locally Noetherian one-point
base**: `R^q f_*𝒪_X = 0` for `q ≥ 2`. -/
theorem hasDerivedStructureSheafPushforwardIsLEOne_of_subsingleton :
    Y.HasDerivedStructureSheafPushforwardIsLEOne := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ Y.total))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ
      (schemeSpace Y.base)))
  have := Space.hasInjectiveResolutions_modules B integerBase hZ Y.total.1 Y.total.2
  have hp := Y.relativelyRepresentable_toBase_of_subsingleton
  rw [HasDerivedStructureSheafPushforwardIsLEOne, DerivedCategory.isLE_iff]
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, (q : ℤ) = n := ⟨n.toNat, by omega⟩
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      ((Space.smallEtaleDerivedModulePushforwardIso B integerBase hZ Y.toBase).app _) ≪≫
    Space.homologyDerivedModulePushforwardSingleIso B integerBase hZ Y.toBase
      (Space.structureSheafModule B integerBase hZ Y.total) 0 q q (by simp))
  let U := Space.idEtaleChart B integerBase hZ Y.base
  have hUt : IsTerminal U := Space.isTerminalIdEtaleChart B integerBase hZ Y.base
  have hUaff : Space.IsAffineChart B integerBase hZ (yoneda.obj Y.base) U := hAff
  have hU : (Space.SmallEtale.topology B integerBase hZ (yoneda.obj Y.base)).CoversTop
      (fun _ : Unit => U) := fun V =>
    (Space.SmallEtale.topology B integerBase hZ (yoneda.obj Y.base)).superset_covering
      (fun _ _ _ => ⟨(), ⟨hUt.from _⟩⟩)
      ((Space.SmallEtale.topology B integerBase hZ (yoneda.obj Y.base)).top_mem V)
  have : (Space.structureSheafModule B integerBase hZ Y.total).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_unit _
  refine Space.isZero_rightDerived_modulePushforward_of_coveringChart B integerBase hZ Y.toBase hp
    Y.proper.2.1.2 (Space.isQuasiSeparated_of_isSeparated B integerBase hZ Y.proper.1) U hUaff hU
    _ q ?_
  set W := (Space.smallBaseChange B integerBase hZ Y.toBase hp).obj U
  set C := Space.chartSpace B integerBase hZ Y.total W
  obtain ⟨hN, hdim⟩ := Y.noetherianSpace_and_dim_le_chartScheme_smallBaseChange_idEtaleChart hp
  exact @Space.isZero_rightDerived_globalSectionsFunctor_of_isTerminal_of_dim_le B integerBase hZ C
    _ (Space.isTerminalIdEtaleChart B integerBase hZ _) hN _
    (Space.isQuasicoherentOnSite_etaleModulePullback B integerBase hZ _ _ _ inferInstance)
    1 q hdim (by omega)

end CurveFamily

end AlgebraicGeometry

end
