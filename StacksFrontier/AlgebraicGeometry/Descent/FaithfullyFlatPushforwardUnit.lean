module

public import StacksFrontier.AlgebraicGeometry.Descent.CounitFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.FlatBaseChange
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Descent of `𝒪 = f_*𝒪` and of `R^n f_*𝒪 = 0` along a faithfully flat base change

Let
```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```
be a cartesian square of schemes with `g` flat and surjective and `f` quasi-compact and
quasi-separated. This file proves that the conditions `𝒪_S ≅ f_*𝒪_X` (the canonical map is an
isomorphism) and `R^n f_*𝒪_X = 0` descend from `f'` to `f`.

Both follow from flat base change (Stacks 02KH) together with the fact that a morphism of modules
whose pullback along a flat surjective morphism is invertible is invertible: on stalks the
pullback is a faithfully flat base change.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_pullback_map_of_surjective`: pullback along a
  flat surjective morphism reflects isomorphisms of modules.
* `AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_pullback_of_surjective`: and zero objects.
* `AlgebraicGeometry.Scheme.Modules.isIso_unitToPushforwardUnit_of_isPullback`: `𝒪 = f_*𝒪`
  descends.
* `AlgebraicGeometry.Scheme.Modules.isZero_rightDerived_unit_of_isPullback`: `R^n f_*𝒪 = 0`
  descends.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] HasDerivedCategory.standard

/-- **Pullback along a flat surjective morphism reflects isomorphisms of modules.** On the stalk
at `g y` the pullback is the base change along the faithfully flat local homomorphism
`𝒪_{X, g y} ⟶ 𝒪_{Y, y}`. -/
theorem isIso_of_isIso_pullback_map_of_surjective {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g]
    (hg : Function.Surjective g.base) {F G : X.Modules} (φ : F ⟶ G)
    (h : IsIso ((Scheme.Modules.pullback g).map φ)) : IsIso φ := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  have hst : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ.val)) := fun x => by
    obtain ⟨y, rfl⟩ := hg x
    exact VectorBundleCodimensionOne.isIso_stalk_of_isIso_pullback_map g φ h y
  let ψ := (SheafOfModules.toSheaf X.ringCatSheaf).map φ
  have : ∀ x : U, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.val).map ψ.1) :=
    fun x => hst x.val
  have h1 : IsIso (ψ.1.app (op U)) := TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso ψ U
  rwa [ConcreteCategory.isIso_iff_bijective] at h1 ⊢

/-- **Pullback along a flat surjective morphism reflects zero modules.** -/
theorem isZero_of_isZero_pullback_of_surjective {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g]
    (hg : Function.Surjective g.base) (M : X.Modules)
    (h : IsZero ((Scheme.Modules.pullback g).obj M)) : IsZero M := by
  obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := X.Modules)
  have hz : IsZero ((Scheme.Modules.pullback g).obj Z) := Functor.map_isZero _ hZ
  have : IsIso ((Scheme.Modules.pullback g).map (hZ.to_ M)) := by
    rw [hz.eq_of_src ((Scheme.Modules.pullback g).map (hZ.to_ M)) (hz.iso h).hom]
    infer_instance
  have : IsIso (hZ.to_ M) := isIso_of_isIso_pullback_map_of_surjective g hg _ this
  exact hZ.of_iso (asIso (hZ.to_ M)).symm

/-- Pushforward of sheaves of modules along a scheme morphism is a right adjoint. -/
private instance isRightAdjoint_pushforward_toRingCatSheafHom {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
  (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint

/-- The comparison `g^*𝒪_X ⟶ 𝒪_Y` is an isomorphism. -/
private theorem isIso_pullbackObjUnitToUnit {X Y : Scheme.{u}} (g : Y ⟶ X) :
    IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom :
      (Scheme.Modules.pullback g).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
        SheafOfModules.unit Y.ringCatSheaf) := by
  have : (Opens.map g.base).Final := Stacks.Topology.final_opensMap _
  exact SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _

/-- The canonical map `𝒪_S ⟶ f_*𝒪_X` is the unit of `f^* ⊣ f_*` at `𝒪_S`, followed by the
pushforward of the identification `f^*𝒪_S ≅ 𝒪_X`. -/
theorem isIso_unitToPushforwardUnit_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    IsIso (Scheme.Modules.unitToPushforwardUnit f) ↔
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit S.ringCatSheaf)) := by
  let O : S.Modules := SheafOfModules.unit S.ringCatSheaf
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let q : (Scheme.Modules.pullback f).obj O ⟶ OX :=
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  have heq : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app O ≫
      (Scheme.Modules.pushforward f).map q = Scheme.Modules.unitToPushforwardUnit f :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _)
  have : IsIso q := isIso_pullbackObjUnitToUnit f
  constructor
  · intro ht
    have hc : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app O ≫
        (Scheme.Modules.pushforward f).map q) := by
      rw [heq]
      exact ht
    exact IsIso.of_isIso_comp_right _ ((Scheme.Modules.pushforward f).map q)
  · intro hu
    have hu' : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app O) := hu
    rw [← heq]
    exact IsIso.comp_isIso' hu' (Functor.map_isIso _ q)

section BaseChange

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- **`𝒪 = f_*𝒪` descends along a flat surjective base change.** -/
theorem isIso_unitToPushforwardUnit_of_isPullback (H : IsPullback g' f' f g) [Flat g]
    (hg : Function.Surjective g.base) [QuasiCompact f] [QuasiSeparated f]
    (h : IsIso (Scheme.Modules.unitToPushforwardUnit f')) :
    IsIso (Scheme.Modules.unitToPushforwardUnit f) := by
  rw [isIso_unitToPushforwardUnit_iff] at h ⊢
  let O : S.Modules := SheafOfModules.unit S.ringCatSheaf
  have hO : O.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit S
  have : ((Scheme.Modules.pullback f).obj O).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ f.toLRSHom.toShHom O hO
  have hbc := Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
    H ((Scheme.Modules.pullback f).obj O)
  have key := Stacks.Modules.map_unit_comp_baseChangeNatTrans_app H.w O
  let q : (Scheme.Modules.pullback g).obj O ⟶ SheafOfModules.unit S'.ringCatSheaf :=
    SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom
  have : IsIso q := isIso_pullbackObjUnitToUnit g
  have hu : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
      ((Scheme.Modules.pullback g).obj O)) :=
    (NatTrans.isIso_app_iff_of_iso (Scheme.Modules.pullbackPushforwardAdjunction f').unit
      (asIso q)).mpr h
  have : IsIso ((Scheme.Modules.pullback g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app O) ≫
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H.w).app
        ((Scheme.Modules.pullback f).obj O)) := by
    rw [key]
    infer_instance
  exact isIso_of_isIso_pullback_map_of_surjective g hg _ (IsIso.of_isIso_comp_right _
    ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H.w).app
      ((Scheme.Modules.pullback f).obj O)))

/-- **`R^n f_*𝒪 = 0` descends along a flat surjective base change.** -/
theorem isZero_rightDerived_unit_of_isPullback (H : IsPullback g' f' f g) [Flat g]
    (hg : Function.Surjective g.base) [QuasiCompact f] [QuasiSeparated f] (n : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward f').rightDerived n).obj
      (SheafOfModules.unit X'.ringCatSheaf))) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj
      (SheafOfModules.unit X.ringCatSheaf)) := by
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hO : OX.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  have : Flat g' := MorphismProperty.of_isPullback H.flip inferInstance
  let OX' : X'.Modules := SheafOfModules.unit X'.ringCatSheaf
  let q : (Scheme.Modules.pullback g').obj OX ⟶ OX' :=
    SheafOfModules.pullbackObjUnitToUnit g'.toRingCatSheafHom
  have : IsIso q := isIso_pullbackObjUnitToUnit g'
  let e : (Scheme.Modules.pullback g').obj OX ≅ OX' := asIso q
  have h' : IsZero (((RingedSpaceModuleAdjunction.modulePushforward
      f'.toLRSHom.toShHom).rightDerivedPlus (n : ℤ)).obj
        ((RingedSpaceModuleAdjunction.modulePullback g'.toLRSHom.toShHom).obj OX)) :=
    (h.of_iso ((Stacks.DerivedIndexing.rightDerivedIso _ n).app _).symm).of_iso
      (((RingedSpaceModuleAdjunction.modulePushforward
        f'.toLRSHom.toShHom).rightDerivedPlus (n : ℤ)).mapIso e)
  have h2 := h'.of_iso
    (Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeIso H OX (n : ℤ))
  exact (isZero_of_isZero_pullback_of_surjective g hg _ h2).of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso _ n).app _)

end BaseChange

end AlgebraicGeometry.Scheme.Modules

end
