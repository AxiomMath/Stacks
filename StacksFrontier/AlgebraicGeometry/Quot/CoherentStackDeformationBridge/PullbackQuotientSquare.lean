module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseDerivedCoherence

/-!
# The reduction of a pulled back lift, on small étale ringed topoi

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `L` a lift of `ξ` across
`h : T ⟶ T'` and `g : T'₂ ⟶ T'` a morphism under `T`, `h₂ ≫ g = h`. The reduction
`𝒢' ⟶ (X_h)_*𝒢` of `L` is the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` followed by the direct image of the
reduction of the pulled back lift and the comparison `(X_g)_*(X_{h₂})_* ≅ (X_h)_*` of
Stacks 03LU. This file states it for the morphisms of small étale ringed topoi, the spelling in
which the extensions attached to lifts are written
(`AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.toThickened`).

## Main results

* `AlgebraicGeometry.Space.pushforwardModulesCompAt_hom_app_comp_eqToHom`: the comparison of
  Stacks 03LU for the morphisms of small étale ringed topoi, read through the identification
  with the direct images of modules.
* `AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.toThickened_eq_unit_comp_pullback`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits


universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The sheaves of rings of the small étale ringed topos of an algebraic space compose with the
forgetful functor to sets (instance search reaches this only slowly through
`AlgebraicGeometry.Space.smallEtaleRingedTopos`). -/
theorem smallEtaleRingedTopos_hasSheafCompose_forget_ringCat (X : AlgebraicSpaces B S hS) :
    (smallEtaleRingedTopos B S hS X).J.HasSheafCompose (forget RingCat.{u}) :=
  inferInstanceAs ((SmallEtale.topology B S hS X.1).HasSheafCompose (forget RingCat.{u}))

/-- The sheaves of commutative rings of the small étale ringed topos of an algebraic space are
sheaves of rings (instance search reaches this only slowly through
`AlgebraicGeometry.Space.smallEtaleRingedTopos`). -/
theorem smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat (X : AlgebraicSpaces B S hS) :
    (smallEtaleRingedTopos B S hS X).J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
  inferInstanceAs ((SmallEtale.topology B S hS X.1).HasSheafCompose
    (forget₂ CommRingCat.{u} RingCat.{u}))

-- Below priority 10000, the instance search for
-- `(smallEtaleRingedTopos X).J.HasSheafCompose (forget RingCat)` exceeds 1000 heartbeats.
attribute [local instance 10000] smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat

/-- **The comparison of Stacks 03LU for the morphisms of small étale ringed topoi is the one for
the direct images of modules**, read through the identifications
`AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward` of the two direct images, for
a morphism `k` equal to the composite. -/
theorem pushforwardModulesCompAt_hom_app_comp_eqToHom {X₀ X₂ X₁ : AlgebraicSpaces B S hS}
    (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁) {k : X₀ ⟶ X₁} (e : a ≫ b = k)
    (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    (pushforwardModulesCompAt B S hS a b).hom.app M ≫
        eqToHom (congrArg (fun x : X₀ ⟶ X₁ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) e) ≫
        (pushforwardModulesIsoModulePushforward B S hS k).hom.app M =
      (pushforwardModulesIsoModulePushforward B S hS b).hom.app
          ((smallEtaleRingedToposHom B S hS a).pushforwardModules.obj M) ≫
        (modulePushforward B S hS b).map
          ((pushforwardModulesIsoModulePushforward B S hS a).hom.app M) ≫
        (modulePushforwardCompIso B S hS a b ≪≫
          eqToIso (congrArg (modulePushforward B S hS) e)).hom.app M := by
  subst e
  have h₁ : (modulePushforwardCompIso B S hS a b ≪≫
      eqToIso (congrArg (modulePushforward B S hS) (rfl : a ≫ b = a ≫ b))).hom.app M =
      (modulePushforward B S hS b).map
          ((pushforwardModulesIsoModulePushforward B S hS a).inv.app M) ≫
        (pushforwardModulesIsoModulePushforward B S hS b).inv.app
          ((smallEtaleRingedToposHom B S hS a).pushforwardModules.obj M) ≫
        (pushforwardModulesCompAt B S hS a b).hom.app M ≫
        (pushforwardModulesIsoModulePushforward B S hS (a ≫ b)).hom.app M :=
    (Category.comp_id _).trans (NatTrans.congr_app
      (congrArg Iso.hom (modulePushforwardCompIso_eq_pushforwardModulesCompAt B a b)) M)
  rw [h₁]
  exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans
    ((Iso.hom_inv_id_assoc ((pushforwardModulesIsoModulePushforward B S hS b).app _) _).symm.trans
      (congrArg (_ ≫ ·) (Iso.hom_inv_id_map_assoc
        ((pushforwardModulesIsoModulePushforward B S hS a).app M) _ _).symm))

/-- **The map adjoint to `φ : f^*M ⟶ N`, on small étale ringed topoi, read through the
identification of the two direct images**, is the map adjoint to `φ` for `f^* ⊣ f_*`. -/
theorem unit_comp_map_comp_pushforwardModulesIsoModulePushforward {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {M : Modules.{u, u} B S hS Y.1 Y.2} {N : Modules.{u, u} B S hS X.1 X.2}
    (φ : (modulePullback B S hS f).obj M ⟶ N) :
    ((smallEtaleRingedToposHom B S hS f).pullbackAdjPushforwardModulesViaComparison.unit.app M ≫
      (smallEtaleRingedToposHom B S hS f).pushforwardModules.map φ) ≫
      (pushforwardModulesIsoModulePushforward B S hS f).hom.app N =
    (modulePullbackAdjunction B S hS f).unit.app M ≫ (modulePushforward B S hS f).map φ :=
  transport_comp_map (pushforwardModulesIsoModulePushforward B S hS f) _ _ φ
    (viaComparison_unit_app_comp_pushforwardModulesIsoModulePushforward f M)

/-- The unit of the small étale ringed topoi followed by a direct image and by the
identification of the two direct images, through the unit of `f^* ⊣ f_*`. -/
theorem unit_comp_map_comp_pushforwardModulesIsoModulePushforward_assoc
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {M : Modules.{u, u} B S hS Y.1 Y.2}
    {N : Modules.{u, u} B S hS X.1 X.2} {W : Modules.{u, u} B S hS Y.1 Y.2}
    (φ : (modulePullback B S hS f).obj M ⟶ N) (ψ : (modulePushforward B S hS f).obj N ⟶ W) :
    (smallEtaleRingedToposHom B S hS f).pullbackAdjPushforwardModulesViaComparison.unit.app M ≫
      (smallEtaleRingedToposHom B S hS f).pushforwardModules.map φ ≫
      (pushforwardModulesIsoModulePushforward B S hS f).hom.app N ≫ ψ =
    (modulePullbackAdjunction B S hS f).unit.app M ≫ (modulePushforward B S hS f).map φ ≫ ψ :=
  (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ψ) (unit_comp_map_comp_pushforwardModulesIsoModulePushforward f φ)).trans
      (Category.assoc _ _ _)))

/-- The first half of `AlgebraicGeometry.Space.unit_comp_map_unit_comp_pushforwardModulesCompAt`:
the topos-side composite, read through the identification along `k`, in terms of the units of
`f^* ⊣ f_*`. -/
theorem unit_comp_map_comp_pushforwardModulesCompAt_comp {X₀ X₂ X₁ : AlgebraicSpaces B S hS}
    (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁) {k : X₀ ⟶ X₁} (e : a ≫ b = k)
    {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2} {F₀ : Modules.{u, u} B S hS X₀.1 X₀.2}
    (Y : (modulePullback B S hS b).obj F₁ ⟶
      (smallEtaleRingedToposHom B S hS a).pushforwardModules.obj F₀) :
    (smallEtaleRingedToposHom B S hS b).pullbackAdjPushforwardModulesViaComparison.unit.app F₁ ≫
      (smallEtaleRingedToposHom B S hS b).pushforwardModules.map Y ≫
      (pushforwardModulesCompAt B S hS a b).hom.app F₀ ≫
      eqToHom (congrArg (fun x : X₀ ⟶ X₁ =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj F₀) e) ≫
        (pushforwardModulesIsoModulePushforward B S hS k).hom.app F₀ =
      (modulePullbackAdjunction B S hS b).unit.app F₁ ≫ (modulePushforward B S hS b).map Y ≫
        (modulePushforward B S hS b).map
          ((pushforwardModulesIsoModulePushforward B S hS a).hom.app F₀) ≫
        (modulePushforwardCompIso B S hS a b ≪≫
          eqToIso (congrArg (modulePushforward B S hS) e)).hom.app F₀ :=
  (congrArg (_ ≫ _ ≫ ·) (pushforwardModulesCompAt_hom_app_comp_eqToHom a b e F₀)).trans
    (unit_comp_map_comp_pushforwardModulesIsoModulePushforward_assoc b Y _)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}

/-- The reduction of a lift, read through the identification of the two direct images along
`X_h`, as a morphism of `𝒪_{X_{T'}}`-modules. -/
theorem ThickeningLift.toThickened_comp_pushforwardModulesIsoModulePushforward_hom_app
    (L : D.ThickeningLift ξ h) :
    (L.toThickened h ≫ (pushforwardModulesIsoModulePushforward B S hS
        (D.relativeSquareSituation.relativeMap h)).hom.app (objectToposModule ξ) :
      L.F ⟶ (modulePushforward B S hS (D.relativeSquareSituation.relativeMap h)).obj ξ.F) =
      (modulePullbackAdjunction B S hS (D.relativeSquareSituation.relativeMap h)).unit.app L.F ≫
        (modulePushforward B S hS (D.relativeSquareSituation.relativeMap h)).map L.fibre :=
  L.toThickened_comp_pushforwardModulesIsoModulePushforward.trans
    (congrArg (fun φ => _ ≫ (modulePushforward B S hS
      (D.relativeSquareSituation.relativeMap h)).map φ) L.toposFibre_eq_fibre)


/-- The direct image along `X_g` of the reduction of the pulled back lift, read through the
identification of the two direct images along `X_{h₂}`. -/
theorem ThickeningLift.modulePushforward_map_pullback_toThickened (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    (L : D.ThickeningLift ξ h) :
    (modulePushforward B S hS (D.relativeSquareSituation.relativeMap g)).map
        ((L.pullback g hg).toThickened h₂ :
          (modulePullback B S hS (D.relativeSquareSituation.relativeMap g)).obj L.F ⟶
            (smallEtaleRingedToposHom B S hS
              (D.relativeSquareSituation.relativeMap h₂)).pushforwardModules.obj ξ.F) ≫
      (modulePushforward B S hS (D.relativeSquareSituation.relativeMap g)).map
        ((pushforwardModulesIsoModulePushforward B S hS
          (D.relativeSquareSituation.relativeMap h₂)).hom.app ξ.F) =
      (modulePushforward B S hS (D.relativeSquareSituation.relativeMap g)).map
        ((modulePullbackAdjunction B S hS (D.relativeSquareSituation.relativeMap h₂)).unit.app
            (L.pullback g hg).F ≫
          (modulePushforward B S hS (D.relativeSquareSituation.relativeMap h₂)).map
            (L.pullback g hg).fibre) :=
  (Functor.map_comp _ _ _).symm.trans (congrArg (modulePushforward B S hS
    (D.relativeSquareSituation.relativeMap g)).map
    (L.pullback g hg).toThickened_comp_pushforwardModulesIsoModulePushforward_hom_app)

/-- `AlgebraicGeometry.Space.unit_comp_map_comp_pushforwardModulesCompAt_comp` for the reduction
of the pulled back lift. -/
theorem ThickeningLift.unit_comp_map_pullback_toThickened_comp (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    (L : D.ThickeningLift ξ h) :
    type_of% (unit_comp_map_comp_pushforwardModulesCompAt_comp
      (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.relativeMap g) (relativeMap_comp_of_comp_eq g hg) (F₁ := L.F)
      (F₀ := ξ.F) ((L.pullback g hg).toThickened h₂)) :=
  unit_comp_map_comp_pushforwardModulesCompAt_comp (D.relativeSquareSituation.relativeMap h₂)
    (D.relativeSquareSituation.relativeMap g) (relativeMap_comp_of_comp_eq g hg) (F₁ := L.F)
    (F₀ := ξ.F) ((L.pullback g hg).toThickened h₂)


/-- The reduction of a lift through the reduction of its pullback, read through the
identification of the two direct images along `X_h`. -/
theorem ThickeningLift.unit_comp_map_pullback_toThickened_comp_eq (g : T'₂ ⟶ T')
    (hg : h₂ ≫ g = h) (L : D.ThickeningLift ξ h) :
    (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap g)).pullbackAdjPushforwardModulesViaComparison.unit.app
        L.F ≫
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.map
        ((L.pullback g hg).toThickened h₂) ≫
      (pushforwardModulesCompAt B S hS (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap g)).hom.app ξ.F ≫
      eqToHom (congrArg (fun x : D.relativeSquareSituation.space ξ.T ⟶
          D.relativeSquareSituation.space T' =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj ξ.F)
        (relativeMap_comp_of_comp_eq g hg)) ≫
      (pushforwardModulesIsoModulePushforward B S hS
        (D.relativeSquareSituation.relativeMap h)).hom.app ξ.F =
    (modulePullbackAdjunction B S hS (D.relativeSquareSituation.relativeMap h)).unit.app L.F ≫
      (modulePushforward B S hS (D.relativeSquareSituation.relativeMap h)).map L.fibre := by
  refine (L.unit_comp_map_pullback_toThickened_comp g hg).trans ?_
  refine Eq.trans ?_ (L.reduction_pullback g hg).symm
  refine congrArg (_ ≫ ·) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine congrArg (· ≫ _) ?_
  exact L.modulePushforward_map_pullback_toThickened g hg

/-- **The reduction of a lift through the reduction of its pullback**, on small étale ringed
topoi: for `h₂ ≫ g = h`, the reduction `𝒢' ⟶ (X_h)_*𝒢` of `L` is the unit
`𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`, followed by the direct image of the reduction of the pulled back lift and
the comparison `(X_g)_*(X_{h₂})_* ≅ (X_h)_*` of Stacks 03LU
(`AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.reduction_pullback`, read through the
identification of the two direct images). -/
theorem ThickeningLift.unit_comp_map_pullback_toThickened (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    (L : D.ThickeningLift ξ h) :
    (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap g)).pullbackAdjPushforwardModulesViaComparison.unit.app
        L.F ≫
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.map
        ((L.pullback g hg).toThickened h₂) ≫
      (pushforwardModulesCompAt B S hS (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap g)).hom.app ξ.F ≫
      eqToHom (congrArg (fun x : D.relativeSquareSituation.space ξ.T ⟶
          D.relativeSquareSituation.space T' =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj ξ.F)
        (relativeMap_comp_of_comp_eq g hg)) =
    L.toThickened h := by
  refine (Iso.cancel_iso_hom_right _ _ ((pushforwardModulesIsoModulePushforward B S hS
    (D.relativeSquareSituation.relativeMap h)).app ξ.F)).1 ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (congrArg (_ ≫ _ ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (L.unit_comp_map_pullback_toThickened_comp_eq g hg).trans ?_
  exact L.toThickened_comp_pushforwardModulesIsoModulePushforward_hom_app.symm
  /-
    ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (L.modulePushforward_map_pullback_toThickened g hg)).trans
        (L.reduction_pullback g hg).symm))))
  -/

end AlgebraicGeometry.Space.CoherentSituation

end
