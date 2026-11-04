module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.Pullback
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.ThickeningMorphismComparison

/-!
# The reduction map of a lift and of its pullback

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB) and `L = (𝒢', (X_h)^*𝒢' ≅ 𝒢)` a lift
of `ξ` across `h : T ⟶ T'`. Its reduction `𝒢' ⟶ (X_h)_*𝒢` is the map adjoint to the comparison.
For `g : T'₂ ⟶ T'` under `T` the pulled back lift `(X_g)^*𝒢'` has the reduction
`(X_g)^*𝒢' ⟶ (X_{h₂})_*𝒢`, and the two are related through the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` and
the comparison `(X_g)_*(X_{h₂})_* ≅ (X_h)_*` of Stacks 03LU. This is the square of reductions in
the map of extensions comparing the deformation classes of `L` and of its pullback.

## Main results

All in the namespace `AlgebraicGeometry.Space.CoherentSituation`:

* `ThickeningLift.toThickened_comp_pushforwardModulesIsoModulePushforward`: the reduction of a
  lift, read through the identification of the two direct images, is the map adjoint to its
  comparison.
* `ThickeningLift.reduction_pullback`: the reduction of a lift through the reduction of its
  pullback.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}

/-- The comparison `topos pullback ⟶ modulePullback` along `X_h` is the identity. -/
theorem relativeMapPullbackIso_inv_app (h : ξ.T ⟶ T')
    (M : Modules.{u, u} B S hS (D.space T').1 (D.space T').2) :
    (D.relativeMapPullbackIso h).inv.app M = 𝟙 _ :=
  rfl

/-- **The reduction of a lift is the map adjoint to its comparison**, read through the
identification of the two direct images of modules along `X_h`. -/
theorem ThickeningLift.toThickened_comp_pushforwardModulesIsoModulePushforward
    (L : D.ThickeningLift ξ h) :
    L.toThickened h ≫
        (pushforwardModulesIsoModulePushforward B S hS
          (D.relativeSquareSituation.relativeMap h)).hom.app (objectToposModule ξ) =
      (modulePullbackAdjunction B S hS (D.relativeSquareSituation.relativeMap h)).unit.app L.F ≫
        (modulePushforward B S hS (D.relativeSquareSituation.relativeMap h)).map L.toposFibre := by
  have hσ := (pushforwardModulesIsoModulePushforward B S hS
    (D.relativeSquareSituation.relativeMap h)).hom.naturality L.toposFibre
  have hu := viaComparison_unit_app_comp_pushforwardModulesIsoModulePushforward
    (D.relativeSquareSituation.relativeMap h) L.F
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hσ).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hu)))

/-- The comparison of a lift, read through `topos pullback = modulePullback`, is its comparison. -/
theorem ThickeningLift.toposFibre_eq_fibre (L : D.ThickeningLift ξ h) : L.toposFibre = L.fibre :=
  (congrArg (· ≫ L.fibre) (relativeMapPullbackIso_inv_app h L.F)).trans (Category.id_comp _)

/-- The reduction of a lift, with its comparison read in the spelling of the inverse image along
`X_h`. -/
theorem ThickeningLift.toThickened_eq_fibre (L : D.ThickeningLift ξ h) :
    L.toThickened h =
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap
            h)).pullbackAdjPushforwardModulesViaComparison.unit.app
          L.F ≫
        (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h)).pushforwardModules.map
          L.fibre :=
  congrArg (fun φ => _ ≫ (smallEtaleRingedToposHom B S hS
    (D.relativeSquareSituation.relativeMap h)).pushforwardModules.map φ) L.toposFibre_eq_fibre

/-- The comparison of Stacks 03LU for `X_{h₂} ≫ X_g = X_h`, followed by the comparison of the
pulled back lift, is the comparison of the lift. -/
theorem ThickeningLift.modulePullbackTriangle_hom_app_comp_pullback_fibre (g : T'₂ ⟶ T')
    (hg : h₂ ≫ g = h) (L : D.ThickeningLift ξ h) :
    (modulePullbackTriangle B S hS (relativeMap_comp_of_comp_eq g hg)).hom.app L.F ≫
      (L.pullback g hg).fibre = L.fibre :=
  Iso.hom_inv_id_app_assoc (modulePullbackTriangle B S hS (relativeMap_comp_of_comp_eq g hg)) L.F
    L.fibre

/-- **The cocycle condition for the comparisons of a lift and of its pullback**: the comparison
`(X_h)^*𝒢' ≅ 𝒢` of a lift is the comparison of Stacks 03LU for `X_{h₂} ≫ X_g = X_h` followed by
the comparison `(X_{h₂})^*(X_g)^*𝒢' ≅ 𝒢` of the pulled back lift. -/
theorem ThickeningLift.fibre_eq_triangle (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    (L : D.ThickeningLift ξ h) :
    L.fibre = (modulePullbackTriangle B S hS (relativeMap_comp_of_comp_eq g hg)).hom.app L.F ≫
      (modulePullback B S hS (D.relativeSquareSituation.relativeMap h₂)).map
        (𝟙 ((modulePullback B S hS (D.relativeSquareSituation.relativeMap g)).obj L.F)) ≫
      (L.pullback g hg).fibre := by
  rw [CategoryTheory.Functor.map_id]
  exact (L.modulePullbackTriangle_hom_app_comp_pullback_fibre g hg).symm.trans
    (congrArg (_ ≫ ·) (Category.id_comp _).symm)

/-- **The reduction of a lift through the reduction of its pullback**: for `h₂ ≫ g = h`, the map
`𝒢' ⟶ (X_h)_*𝒢` adjoint to the comparison of `L` is the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`, followed by
the direct image of the map adjoint to the comparison of the pulled back lift and the comparison
`(X_g)_*(X_{h₂})_* ≅ (X_h)_*` of Stacks 03LU. -/
theorem ThickeningLift.reduction_pullback (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    (L : D.ThickeningLift ξ h) :
    (modulePullbackAdjunction B S hS (D.relativeSquareSituation.relativeMap h)).unit.app L.F ≫
        (modulePushforward B S hS (D.relativeSquareSituation.relativeMap h)).map L.fibre =
      (modulePullbackAdjunction B S hS (D.relativeSquareSituation.relativeMap g)).unit.app L.F ≫
        (modulePushforward B S hS (D.relativeSquareSituation.relativeMap g)).map
          ((modulePullbackAdjunction B S hS (D.relativeSquareSituation.relativeMap h₂)).unit.app
              (L.pullback g hg).F ≫
            (modulePushforward B S hS (D.relativeSquareSituation.relativeMap h₂)).map
              (L.pullback g hg).fibre) ≫
        (modulePushforwardCompIso B S hS (D.relativeSquareSituation.relativeMap h₂)
            (D.relativeSquareSituation.relativeMap g) ≪≫
          eqToIso (congrArg (modulePushforward B S hS) (relativeMap_comp_of_comp_eq g hg))).hom.app
          ξ.F := by
  have h₀ := modulePullbackAdjunction_unit_map_of_triangle
    (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
    (relativeMap_comp_of_comp_eq g hg) (F₁ := L.F) (F₂ := (L.pullback g hg).F) (F₀ := ξ.F)
    (Iso.refl _) (asIso (L.pullback g hg).fibre) (asIso L.fibre) (L.fibre_eq_triangle g hg)
  refine h₀.trans ?_
  exact congrArg (fun φ => (modulePullbackAdjunction B S hS
      (D.relativeSquareSituation.relativeMap g)).unit.app L.F ≫
    (modulePushforward B S hS (D.relativeSquareSituation.relativeMap g)).map φ ≫
    (modulePushforwardCompIso B S hS (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap g) ≪≫
      eqToIso (congrArg (modulePushforward B S hS) (relativeMap_comp_of_comp_eq g hg))).hom.app
      ξ.F) (Category.id_comp _)

end AlgebraicGeometry.Space.CoherentSituation

end
