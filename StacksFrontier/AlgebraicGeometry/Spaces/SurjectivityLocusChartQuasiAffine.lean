module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeTensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeSectionMap
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.AmpleQuasiAffineCover.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleEventualGeneration.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndQuasiAffineStability

/-!
# The surjectivity locus of a section of a tensor power, on a scheme chart with ample base change

Let `Z` be an algebraic space over a scheme `S` of a big fppf site, `𝓛` an invertible
`𝒪_Z`-module and `σ` a global section of `𝓛^{⊗ n}`, `n ≥ 1`. The map `𝒪_Z ⟶ 𝓛^{⊗ n}` named by `σ`
has an open surjectivity locus `V_σ ⊆ Z`. For a scheme point `w : h_U ⟶ Z` at which the base change
of `𝓛` to `U` is ample, the base change `V_σ ×_Z h_U` is represented by the open subscheme of `U`
on which the pullback of `σ` does not vanish, and that open subscheme is quasi-affine (Stacks
01PX applied to the ample base change).

## Main results

* `AlgebraicGeometry.Space.range_pullback_eq_of_forall_exists_factor_iff`: the image of the
  scheme representing the base change of an open subspace to a scheme point is the open
  characterising the factorisations through it.
* `AlgebraicGeometry.Space.range_eq_and_isQuasiAffine_pullback_surjectivityLocus`: the image in
  `U` of the scheme representing `V_σ ×_Z h_U` is the complement of the support of the cokernel
  of the chart map, and that scheme is quasi-affine.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.TensorPowers (natTensorPow)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

/-- **A scheme point factoring through an open subspace has image the factorisation locus.**
For an open subspace `V` of an algebraic space `X` and a scheme point `w : h_U ⟶ X`, let `W` be the
scheme representing `V ×_X h_U`. If an open `O` of `U` is such that a morphism `r : U' ⟶ U` of the
site has `h_r ≫ w` factoring through `V` exactly when the image of `r` lies in `O`, then the image
of `W` in `U` is `O`. -/
theorem range_pullback_eq_of_forall_exists_factor_iff {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V : Subfunctor X} (hV : IsOpenSubspace B S hS V) {U : BigFppfOver B S hS}
    (w : yoneda.obj U ⟶ X) (O : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (h : ∀ {U' : BigFppfOver B S hS} (r : U' ⟶ U),
      (∃ k : yoneda.obj U' ⟶ V.toFunctor, k ≫ V.ι = yoneda.map r ≫ w) ↔
        Set.range ((BigFppfOver.toScheme B S hS).map r) ⊆ O) :
    Set.range ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd w)) = O := by
  refine le_antisymm ((h _).mp ⟨hV.2.rep.fst w, (hV.2.rep.isPullback w).w⟩) fun x hx => ?_
  have hι : Set.range ((BigFppfOver.toScheme B S hS).map (openSiteObjectHom B S hS U O)) =
      (O : Set ((BigFppfOver.toScheme B S hS).obj U)) :=
    (congrArg (fun f : (BigFppfOver.toScheme B S hS).obj (openSiteObject B S hS U O) ⟶
        (BigFppfOver.toScheme B S hS).obj U => Set.range ⇑f)
            (map_openSiteObjectHom B S hS U O)).trans
      (Scheme.Opens.range_ι O)
  obtain ⟨k, hk⟩ := (h (openSiteObjectHom B S hS U O)).mpr hι.le
  have hfac : openSiteObjectHom B S hS U O = yoneda.preimage ((hV.2.rep.isPullback w).lift k
      (yoneda.map (openSiteObjectHom B S hS U O)) hk) ≫ hV.2.rep.snd w :=
    yoneda.map_injective (by rw [Functor.map_comp, Functor.map_preimage, IsPullback.lift_snd])
  obtain ⟨y, rfl⟩ := hι.symm ▸ hx
  rw [hfac, Functor.map_comp]
  exact ⟨_, rfl⟩

/-- The structure sheaf of `U` is isomorphic to the module on `U` corresponding to the pullback of
the unit module along a scheme point `w : h_U ⟶ Z`. -/
def unitModuleIsoChartSchemeSource {Z : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (w : yoneda.obj U ⟶ Z.1) :
    Stacks.Ample.unitModule ((BigFppfOver.toScheme B S hS).obj U) ≅
      chartSchemeSource (𝓖 := SheafOfModules.unit _)
        (h𝓖 := SheafOfModules.isQuasicoherentOnSite_unit _) w :=
  chartSchemeUnitIso U ≪≫ (ObjectProperty.ι _).mapIso
    ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.mapIso
      (ObjectProperty.isoMk _ (X := chartUnitQcoh U)
        (Y := @chartPullbackQcoh B S hS Z U w (SheafOfModules.unit _)
          (SheafOfModules.isQuasicoherentOnSite_unit _))
        (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
          (smallEtaleRingedToposModulesHom B S hS (chartSpaceMap w)))))

/-- The module on `U` corresponding to the pullback of `𝓛^{⊗ n}` along a scheme point at which
the base change of `𝓛` is invertible is invertible. -/
theorem isInvertibleModule_chartSchemeTarget_natTensorPow {Z : AlgebraicSpaces B S hS}
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (structureSheaf B S hS Z.1 Z.2).obj (structureRingPresheaf_isSheaf B S hS Z.1 Z.2)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible (structureSheaf B S hS Z.1 Z.2).obj
      (structureRingPresheaf_isSheaf B S hS Z.1 Z.2) L]
    {U : BigFppfOver B S hS} (w : yoneda.obj U ⟶ Z.1)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj
      (structureRingPresheaf_isSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
      ((modulePullback B S hS (chartSpaceMap w)).obj L)]
    [Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U w)] (n : ℕ) :
    Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (chartSchemeTarget (𝓕 := natTensorPow (C := SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (structureSheaf B S hS Z.1 Z.2).obj (structureRingPresheaf_isSheaf B S hS Z.1 Z.2))) L n)
            (h𝓕 := isQuasicoherentOnSite_natTensorPow_of_isInvertible L n) w) := by
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (natTensorPow (C := SheafOfModules.{u}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (chartScheme (idEtaleChart B S hS U)).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (chartScheme
            (idEtaleChart B S hS U)))))
        (baseChangeModule B S hS L U w) n) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule _ (baseChangeModule B S hS L U w) (n : ℤ)
  exact Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _
    (natTensorPowIsoChartSchemeTarget L w n)

/-- **The base change of the surjectivity locus of a section to a scheme chart with ample base
change is quasi-affine.** Let `𝓛` be an invertible module on an algebraic space `Z`, `σ` a global
section of `𝓛^{⊗ n}` with `n ≥ 1`, and `w : h_U ⟶ Z` a scheme point at which the base change of
`𝓛` to `U` is ample. Then the scheme representing the base change to `U` of the surjectivity
locus of the map `𝒪_Z ⟶ 𝓛^{⊗ n}` named by `σ` is quasi-affine.

That scheme is the open subscheme of `U` complementary to the support of the cokernel of the chart
map (`AlgebraicGeometry.Space.range_pullback_eq_of_forall_exists_factor_iff` with
`AlgebraicGeometry.Space.exists_factor_surjectivityLocus_iff_range_subset`), which is the
nonvanishing locus of a section of the `n`th tensor power of the ample base change
(`Stacks.CokernelSupport.compl_supp_cokernel_eq_nonvanishingLocus`), and such a locus is
quasi-affine (`Stacks.AmpleQuasiAffineCover.isQuasiAffine_nonvanishingOpen_of_isAmple`). -/
theorem range_eq_and_isQuasiAffine_pullback_surjectivityLocus {Z : AlgebraicSpaces B S hS}
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (structureSheaf B S hS Z.1 Z.2).obj (structureRingPresheaf_isSheaf B S hS Z.1 Z.2)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible (structureSheaf B S hS Z.1 Z.2).obj
      (structureRingPresheaf_isSheaf B S hS Z.1 Z.2) L]
    {U : BigFppfOver B S hS} (w : yoneda.obj U ⟶ Z.1)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj
      (structureRingPresheaf_isSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
      ((modulePullback B S hS (chartSpaceMap w)).obj L)]
    [Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U w)]
    (hamp : Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U w))
    {n : ℕ} (hn : 1 ≤ n) (σ : (natTensorPow (C := SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (structureSheaf B S hS Z.1 Z.2).obj (structureRingPresheaf_isSheaf B S hS Z.1 Z.2))) L
            n).sections)
    (hV : IsOpenSubspace B S hS (surjectivityLocus (𝓖 := SheafOfModules.unit _)
      (𝓕 := natTensorPow (C := SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (structureSheaf B S hS Z.1 Z.2).obj (structureRingPresheaf_isSheaf B S hS Z.1 Z.2))) L n)
            ((SheafOfModules.unitHomEquiv _).symm σ))) :
    Set.range ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd w)) =
        (_root_.SheafOfModules.supp (cokernel (chartPullbackSchemeMap
          (h𝓖 := SheafOfModules.isQuasicoherentOnSite_unit _)
          (h𝓕 := isQuasicoherentOnSite_natTensorPow_of_isInvertible L n)
          ((SheafOfModules.unitHomEquiv (natTensorPow (C := SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (structureSheaf B S hS Z.1 Z.2).obj (structureRingPresheaf_isSheaf B S hS Z.1 Z.2))) L
            n)).symm σ) w)))ᶜ ∧
      Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj (hV.2.rep.pullback w)) := by
  have hFq := isQuasicoherentOnSite_natTensorPow_of_isInvertible L n
  have := isInvertibleModule_chartSchemeTarget_natTensorPow L w n
  have : (chartSchemeTarget (𝓕 := natTensorPow (C := SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (structureSheaf B S hS Z.1 Z.2).obj (structureRingPresheaf_isSheaf B S hS Z.1 Z.2))) L n)
            (h𝓕 := hFq) w).IsFiniteType :=
    Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule _
  let c := unitModuleIsoChartSchemeSource (Z := Z) w
  let φ := chartPullbackSchemeMap (h𝓖 := SheafOfModules.isQuasicoherentOnSite_unit _) (h𝓕 := hFq)
    ((SheafOfModules.unitHomEquiv (natTensorPow (C := SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (structureSheaf B S hS Z.1 Z.2).obj (structureRingPresheaf_isSheaf B S hS Z.1 Z.2))) L
            n)).symm σ) w
  let θ' : (chartSchemeTarget (𝓕 := natTensorPow (C := SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (structureSheaf B S hS Z.1 Z.2).obj (structureRingPresheaf_isSheaf B S hS Z.1 Z.2))) L n)
            (h𝓕 := hFq) w :
        ((BigFppfOver.toScheme B S hS).obj U).Modules) ≅
      Stacks.Ample.tensorPowModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U w) (n : ℤ) := (natTensorPowIsoChartSchemeTarget L w n).symm
  let s := φ.app ⊤ (c.hom.app ⊤
    (show Γ(Stacks.Ample.unitModule ((BigFppfOver.toScheme B S hS).obj U), ⊤) from
      (1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))))
  let O := Stacks.NonvanishingOpen.nonvanishingOpen ((BigFppfOver.toScheme B S hS).obj U)
    (Stacks.Ample.tensorPowModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U w) (n : ℤ)) (θ'.hom.app ⊤ s)
  have hOset : (_root_.SheafOfModules.supp (cokernel φ))ᶜ =
      (O : Set ((BigFppfOver.toScheme B S hS).obj U)) :=
    (Stacks.CokernelSupport.compl_supp_cokernel_eq_nonvanishingLocus c φ).trans
      (Stacks.CokernelSupport.nonvanishingLocus_iso_app θ' s).symm
  have hrange := range_pullback_eq_of_forall_exists_factor_iff hV w O (fun r =>
    (exists_factor_surjectivityLocus_iff_range_subset (h𝓖 :=
        SheafOfModules.isQuasicoherentOnSite_unit _)
      (h𝓕 := hFq) ((SheafOfModules.unitHomEquiv _).symm σ) w
        (isFiniteTypeOnSite_natTensorPow L n) r).trans
      (iff_of_eq (congrArg (fun A => Set.range ⇑((BigFppfOver.toScheme B S hS).map r) ⊆ A)
        hOset)))
  have : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd w)) :=
    hV.2.property_snd w
  have : (O : Scheme).IsQuasiAffine :=
    Stacks.AmpleQuasiAffineCover.isQuasiAffine_nonvanishingOpen_of_isAmple
      (baseChangeModule B S hS L U w) hamp hn _
  exact ⟨hrange.trans hOset.symm, Scheme.IsQuasiAffine.of_iso
    (_root_.AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq ((BigFppfOver.toScheme B S hS).map
        (hV.2.rep.snd w)) O.ι
      (hrange.trans (Scheme.Opens.range_ι O).symm))⟩

end AlgebraicGeometry.Space

end
