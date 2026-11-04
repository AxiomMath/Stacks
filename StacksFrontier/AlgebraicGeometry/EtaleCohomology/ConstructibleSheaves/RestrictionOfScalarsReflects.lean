module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.RestrictionOfScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsAlongSurjection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.OfStrictTower

/-!
# Restriction of scalars along a surjection reflects constructibility

Let `f : R →+* S` be a surjective homomorphism of Noetherian rings. For a sheaf `F` of
`S`-modules on the small étale site of a scheme, if `F` read as a sheaf of `R`-modules is
constructible, then `F` is constructible. For `ℤ_ℓ → ℤ/ℓⁿ⁺¹ℤ` this gives the descent of
constructibility from `ℤ_ℓ` to `ℤ/ℓⁿ⁺¹ℤ` for the levels of a strict ℓ-adic tower.

## Main definitions

* `CategoryTheory.extendScalarsSheafRestrictScalarsSheafIso`: for `f` surjective, extending the
  scalars of a sheaf of `S`-modules read over `R` gives it back.
* `Stacks.EtaleCohomology.strictTowerLevelRestrictScalarsIso`: level `n` of the ℓ-adic sheaf of a
  strict tower, read over `ℤ_ℓ`, is `Hₙ`.

## Main results

* `CategoryTheory.ModuleCat.restrictScalars_full_of_surjective`: restriction of scalars along a
  surjective ring homomorphism is full.
* `Stacks.EtaleCohomology.isConstructibleModuleSheaf_of_restrictScalars`: restriction of scalars
  along a surjection of Noetherian rings reflects constructibility.
* `Stacks.EtaleCohomology.isConstructibleModuleSheaf_strictTowerLevel`: a level of a strict ℓ-adic
  tower which is constructible over `ℤ_ℓ` is constructible over `ℤ/ℓⁿ⁺¹ℤ`.

## References

* [Stacks Project, Tag 0GKB](https://stacks.math.columbia.edu/tag/0GKB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u w r s v c

namespace CategoryTheory

/-- Restriction of scalars along a surjective ring homomorphism is full: an `R`-linear map
between `S`-modules is `S`-linear. -/
theorem ModuleCat.restrictScalars_full_of_surjective {R : Type r} {S : Type s} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) : (ModuleCat.restrictScalars.{v} f).Full where
  map_surjective {M N} g := ⟨ModuleCat.ofHom
    { toFun := g.hom
      map_add' := g.hom.map_add
      map_smul' := fun a x => by
        obtain ⟨b, rfl⟩ := hf a
        exact g.hom.map_smul b x }, rfl⟩

/-- For `f : R →+* S` surjective, extending the scalars of a sheaf of `S`-modules read over `R`
gives it back. -/
def extendScalarsSheafRestrictScalarsSheafIso {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) {R : Type r} {S : Type s} [CommRing R] [CommRing S]
    [HasWeakSheafify J (ModuleCat.{max r s w} S)] (f : R →+* S) (hf : Function.Surjective f)
    (F : Sheaf J (ModuleCat.{max r s w} S)) :
    (extendScalarsSheaf.{w} J R S f).obj ((restrictScalarsSheaf.{w} J f).obj F) ≅ F :=
  haveI := ModuleCat.restrictScalars_full_of_surjective.{r, s, max r s w} f hf
  (presheafToSheaf J (ModuleCat.{max r s w} S)).mapIso
      (Functor.isoWhiskerLeft F.obj
          (asIso (ModuleCat.extendRestrictScalarsAdj.{max r s w} f).counit) ≪≫
        Functor.rightUnitor F.obj) ≪≫
    (sheafificationIso F).symm

end CategoryTheory

namespace Stacks.EtaleCohomology

/-- Restriction of scalars along a surjection of Noetherian rings reflects constructibility of
sheaves of modules on the small étale site. -/
theorem isConstructibleModuleSheaf_of_restrictScalars
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type r) (S : Type s) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] (f : R →+* S) (hf : Function.Surjective f)
    [HasWeakSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.{max r s w} S)]
    [∀ (A T : B.Scheme) (g : T ⟶ A),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{max r s w} R)
        (SmallEtale.topology B A.1 A.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{max r s w} R)]
    [∀ (A T : B.Scheme) (g : T ⟶ A),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{max r s w} S)
        (SmallEtale.topology B A.1 A.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{max r s w} S)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max r s w} S))
    (hF : IsConstructibleModuleSheaf B X R
      ((restrictScalarsSheaf.{w} (SmallEtale.topology B X.1 X.property) f).obj F)) :
    IsConstructibleModuleSheaf B X S F :=
  AlgebraicGeometry.isConstructibleModuleSheaf_congr B S X
    (extendScalarsSheafRestrictScalarsSheafIso.{w} _ f hf F)
    (isConstructibleModuleSheaf_extendScalars.{u, w} B X R S f _ hF)

section StrictTower

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

/-- The sections of level `n` of the ℓ-adic sheaf of a strict tower, read over `ℤ_ℓ`, are those of
`Hₙ`: the two `ℤ_ℓ`-module structures on a group killed by `ℓⁿ⁺¹` agree. -/
def strictTowerLevelRestrictScalarsHomApp (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1)
    (hH : IsStrict H ℓ) (n : ℕ) (U : (SmallEtale B X.1 X.property)ᵒᵖ) :
    ((restrictScalarsSheaf.{u + 1} (SmallEtale.topology B X.1 X.property)
        (PadicInt.toZModPow (p := ℓ) (n + 1))).obj (strictTowerLevel H hH n)).obj.obj U ⟶
      ((etaleModulesToSmallEtale.{u, 0} B X ℤ_[ℓ]).obj (towerObj H n)).obj.obj U :=
  letI : Module ℤ_[ℓ] (((restrictScalarsSheaf.{u + 1} (SmallEtale.topology B X.1 X.property)
      (PadicInt.toZModPow (p := ℓ) (n + 1))).obj (strictTowerLevel H hH n)).obj.obj U) :=
    ModuleCat.isModule _
  ModuleCat.ofHom (R := ℤ_[ℓ])
    (X := ((restrictScalarsSheaf.{u + 1} (SmallEtale.topology B X.1 X.property)
        (PadicInt.toZModPow (p := ℓ) (n + 1))).obj (strictTowerLevel H hH n)).obj.obj U)
    (Y := ((etaleModulesToSmallEtale.{u, 0} B X ℤ_[ℓ]).obj (towerObj H n)).obj.obj U)
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => by
        have hx : ℓ ^ (n + 1) • x = 0 :=
          padicForget_nsmul_eq_zero B X ℓ (hH.annihilated n) U x
        rw [RingHom.id_apply, padicInt_smul_eq_val_nsmul (n + 1) a x hx]
        exact (padicInt_smul_eq_val_nsmul (M := ((etaleModulesToSmallEtale.{u, 0} B X ℤ_[ℓ]).obj
          (towerObj H n)).obj.obj U) (n + 1) a x hx).symm }

/-- The inverse of `Stacks.EtaleCohomology.strictTowerLevelRestrictScalarsHomApp`. -/
def strictTowerLevelRestrictScalarsInvApp (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1)
    (hH : IsStrict H ℓ) (n : ℕ) (U : (SmallEtale B X.1 X.property)ᵒᵖ) :
    ((etaleModulesToSmallEtale.{u, 0} B X ℤ_[ℓ]).obj (towerObj H n)).obj.obj U ⟶
      ((restrictScalarsSheaf.{u + 1} (SmallEtale.topology B X.1 X.property)
        (PadicInt.toZModPow (p := ℓ) (n + 1))).obj (strictTowerLevel H hH n)).obj.obj U :=
  letI : Module ℤ_[ℓ] (((restrictScalarsSheaf.{u + 1} (SmallEtale.topology B X.1 X.property)
      (PadicInt.toZModPow (p := ℓ) (n + 1))).obj (strictTowerLevel H hH n)).obj.obj U) :=
    ModuleCat.isModule _
  ModuleCat.ofHom (R := ℤ_[ℓ])
    (X := ((etaleModulesToSmallEtale.{u, 0} B X ℤ_[ℓ]).obj (towerObj H n)).obj.obj U)
    (Y := ((restrictScalarsSheaf.{u + 1} (SmallEtale.topology B X.1 X.property)
        (PadicInt.toZModPow (p := ℓ) (n + 1))).obj (strictTowerLevel H hH n)).obj.obj U)
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => by
        have hx : ℓ ^ (n + 1) • x = 0 :=
          padicForget_nsmul_eq_zero B X ℓ (hH.annihilated n) U x
        rw [RingHom.id_apply, padicInt_smul_eq_val_nsmul (n + 1) a x hx]
        exact (padicInt_smul_eq_val_nsmul (M := ((restrictScalarsSheaf.{u + 1}
          (SmallEtale.topology B X.1 X.property) (PadicInt.toZModPow (p := ℓ) (n + 1))).obj
            (strictTowerLevel H hH n)).obj.obj U) (n + 1) a x hx).symm }

/-- Level `n` of the ℓ-adic sheaf of a strict tower, read over `ℤ_ℓ`, is `Hₙ` on the small
étale site. -/
def strictTowerLevelRestrictScalarsIso (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1)
    (hH : IsStrict H ℓ) (n : ℕ) :
    (restrictScalarsSheaf.{u + 1} (SmallEtale.topology B X.1 X.property)
        (PadicInt.toZModPow (p := ℓ) (n + 1))).obj (strictTowerLevel H hH n) ≅
      (etaleModulesToSmallEtale.{u, 0} B X ℤ_[ℓ]).obj (towerObj H n) where
  hom := ⟨{ app U := strictTowerLevelRestrictScalarsHomApp H hH n U
            naturality _ _ _ := rfl }⟩
  inv := ⟨{ app U := strictTowerLevelRestrictScalarsInvApp H hH n U
            naturality _ _ _ := rfl }⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

omit [AlgebraicGeometry.IsNoetherian X.1] in
/-- Descent of constructibility from `ℤ_ℓ` to `ℤ/ℓⁿ⁺¹ℤ`: a level `Hₙ` of a strict ℓ-adic
tower which is constructible as a sheaf of `ℤ_ℓ`-modules is constructible as a sheaf of
`ℤ/ℓⁿ⁺¹ℤ`-modules. -/
theorem isConstructibleModuleSheaf_strictTowerLevel (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1)
    (hH : IsStrict H ℓ) (n : ℕ)
    (hc : IsBigSiteConstructibleEtaleModule.{u, 0} B X ℤ_[ℓ] (towerObj H n)) :
    IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) (strictTowerLevel H hH n) := by
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X ℤ_[ℓ]
  exact isConstructibleModuleSheaf_of_restrictScalars.{u, u + 1} B X ℤ_[ℓ] (ZMod (ℓ ^ (n + 1)))
    (PadicInt.toZModPow (n + 1)) (ZMod.ringHom_surjective _) _
    (AlgebraicGeometry.isConstructibleModuleSheaf_congr B ℤ_[ℓ] X
      (strictTowerLevelRestrictScalarsIso H hH n).symm hc)

end StrictTower

end Stacks.EtaleCohomology
