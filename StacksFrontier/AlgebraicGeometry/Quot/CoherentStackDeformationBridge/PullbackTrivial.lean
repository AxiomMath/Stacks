module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackQuotientSquare
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.DifferenceExt
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackNaturality

/-!
# The trivial lift has class zero on `X_T`

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB) and `h : T ⟶ T'` a first order
thickening with a retraction `r`. The extension `0 ⟶ I ⊗ 𝒢 ⟶ r^*𝒢 ⟶ i_*𝒢 ⟶ 0` attached to the
trivial lift `r^*𝒢` splits after the direct image along the retraction `ρ = X_r`: the unit
`𝒢 ⟶ ρ_*ρ^*𝒢` is a section, the reduction of `r^*𝒢` read through it being the reduction of `ξ`
as a lift of itself (`ThickeningLift.unit_comp_map_pullback_toThickened` for `h ≫ r = 𝟙`), an
isomorphism. So the class on `X_T` of the trivial lift is zero.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtClass_trivial`.

## References

* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe e u

-- at default priority, `HasExt (SheafOfModules _)` gets stuck on a universe constraint
attribute [local instance 5000] SheafOfModules.instAbelian

-- TC for `(smallEtaleRingedTopos X).J.HasSheafCompose (forget RingCat)` exceeds
-- 1000 heartbeats below priority 10000
attribute [local instance 10000]
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- **`ξ` as a lift of itself has an invertible reduction**: the unit of the inverse image along
`X_{𝟙}`, which is isomorphic to the identity (`CoherentSituation.idComparison`), followed by the
direct image of the identity law. -/
theorem isIso_identityThickeningLift_toThickened (ξ : CoherentObject D) :
    IsIso ((identityThickeningLift ξ).toThickened (𝟙 ξ.T)) := by
  have : (modulePullback B S hS (D.relativeSquareSituation.relativeMap (𝟙 ξ.T))).Full :=
    Functor.Full.of_iso (D.idComparison (modulePushforwardCoherence B S hS) ξ.T).symm
  have : (modulePullback B S hS (D.relativeSquareSituation.relativeMap (𝟙 ξ.T))).Faithful :=
    Functor.Faithful.of_iso (D.idComparison (modulePushforwardCoherence B S hS) ξ.T).symm
  have : IsIso ((identityThickeningLift ξ).fibre) := (identityThickeningLift ξ).isIso_fibre
  have h :=
    (identityThickeningLift ξ).toThickened_comp_pushforwardModulesIsoModulePushforward_hom_app
  have hR : IsIso ((modulePullbackAdjunction B S hS
      (D.relativeSquareSituation.relativeMap (𝟙 ξ.T))).unit.app (identityThickeningLift ξ).F ≫
        (modulePushforward B S hS (D.relativeSquareSituation.relativeMap (𝟙 ξ.T))).map
          (identityThickeningLift ξ).fibre) := inferInstance
  rw [← h] at hR
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ ((pushforwardModulesIsoModulePushforward B S hS
    (D.relativeSquareSituation.relativeMap (𝟙 ξ.T))).hom.app ξ.F)
    (Iso.isIso_hom ((pushforwardModulesIsoModulePushforward B S hS
      (D.relativeSquareSituation.relativeMap (𝟙 ξ.T))).app ξ.F)) hR


variable {ξ : CoherentObject D} {T' : SchemesOver D.Y} (h : ξ.T ⟶ T') (r : T' ⟶ ξ.T)
  (hr : h ≫ r = 𝟙 ξ.T)

/-- **The reduction of the trivial lift, read on `X_T` through the unit of `ρ^* ⊣ ρ_*`, is
invertible**: through the comparison of Stacks 03LU it is the reduction of `ξ` as a lift of
itself (`ThickeningLift.unit_comp_map_pullback_toThickened` for `h ≫ r = 𝟙`). -/
theorem isIso_unit_comp_map_trivialThickeningLift_toThickened :
    IsIso ((smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap r)).pullbackAdjPushforwardModulesViaComparison.unit.app
        (identityThickeningLift ξ).F ≫
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map
        (((identityThickeningLift ξ).pullback r hr).toThickened h)) := by
  have hQ := (identityThickeningLift ξ).unit_comp_map_pullback_toThickened r hr
  have := isIso_identityThickeningLift_toThickened ξ
  have : IsIso ((pushforwardModulesCompAt B S hS (D.relativeSquareSituation.relativeMap h)
      (D.relativeSquareSituation.relativeMap r)).hom.app ξ.F ≫
      eqToHom (congrArg (fun x : D.relativeSquareSituation.space ξ.T ⟶
          D.relativeSquareSituation.space ξ.T =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj ξ.F)
        (relativeMap_comp_of_comp_eq r hr))) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom ((pushforwardModulesCompAt B S hS
      (D.relativeSquareSituation.relativeMap h) (D.relativeSquareSituation.relativeMap r)).app ξ.F))
      (Iso.isIso_hom (eqToIso (congrArg (fun x : D.relativeSquareSituation.space ξ.T ⟶
          D.relativeSquareSituation.space ξ.T =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj ξ.F)
        (relativeMap_comp_of_comp_eq r hr))))
  exact IsIso.of_isIso_fac_right ((Category.assoc _ _ _).trans hQ)


variable (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hfl : IsFlat B S hS (D.projection T').hom)
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]

omit [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))] in
/-- The reduction of the extension attached to a lift is the reduction of the lift. -/
theorem thickeningLiftExtension_g (L : D.ThickeningLift ξ h) :
    (thickeningLiftExtension h hh L).g = L.toThickened h :=
  rfl

omit [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))] in
/-- **The extension attached to the trivial lift splits after the direct image along the
retraction**, so its class read on `X_T` vanishes. -/
theorem retractionExt_thickeningLiftExtensionClass_trivial :
    retractionExt h r hr hh (thickeningLiftExtensionClass h hh hfl
      ((identityThickeningLift ξ).pullback r hr)) = 0 := by
  have := preservesFiniteLimits_retraction_pushforwardModules (D := D) r
  have := preservesFiniteColimits_retraction_pushforwardModules h r hr hh
  have hv := isIso_unit_comp_map_trivialThickeningLift_toThickened h r hr
  unfold retractionExt
  refine (Abelian.Ext.mapExactFunctor_extClass _ _).trans ?_
  refine Stacks.Homology.extClass_eq_zero_of_comp_g_eq_id _
    (@inv _ _ _ _ ((smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap r)).pullbackAdjPushforwardModulesViaComparison.unit.app
        (identityThickeningLift ξ).F ≫
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map
        (((identityThickeningLift ξ).pullback r hr).toThickened h)) hv ≫
      (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap r)).pullbackAdjPushforwardModulesViaComparison.unit.app
        (identityThickeningLift ξ).F) ?_
  refine (congrArg (_ ≫ (smallEtaleRingedToposHom B S hS
    (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map ·)
    (thickeningLiftExtension_g h hh ((identityThickeningLift ξ).pullback r hr))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact @IsIso.inv_hom_id _ _ _ _ _ hv

omit [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))] in
/-- **The trivial lift has class zero on `X_T`.** -/
theorem thickeningLiftExtClass_trivial :
    thickeningLiftExtClass h r hr hh hfl (trivialThickeningLift h r hr) = 0 := by
  unfold thickeningLiftExtClass trivialThickeningLift
  rw [retractionExt_thickeningLiftExtensionClass_trivial h r hr hh hfl]
  exact Stacks.Homology.extConj_zero _ _ 1

end AlgebraicGeometry.Space.CoherentSituation

end
