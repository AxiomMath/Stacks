module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedPullbackMateUnit

/-!
# Changing the structure sheaf of the source along an isomorphism

Let `u : (D, K) ⥤ (C, J)` be a continuous functor, `e : O₁ ≅ O₂` an isomorphism of sheaves of
commutative rings on `C` and `φ₁ : O_D ⟶ u_*O₁`, `φ₂ = φ₁ ≫ u_*(e)` two structure maps. The two
morphisms of ringed topoi `(Sh(C), O_i) ⟶ (Sh(D), O_D)` have the same unit up to the equivalence
`Mod(O₂) ≌ Mod(O₁)` of restriction of scalars along `e`: the unit `G ⟶ f_{1,*}f_1^*G` is
invertible exactly when `G ⟶ f_{2,*}f_2^*G` is.

## Main definitions

* `AlgebraicGeometry.RingedToposSiteHom.restrictScalarsEquivalenceRingedToposSiteHomRingIso`:
  restriction of scalars along an isomorphism of sheaves of rings, as an equivalence given by
  `SheafOfModules.pushforward` along the identity functor.

## Main results

* `AlgebraicGeometry.RingedToposSiteHom.isIso_unit_app_iff_of_ringIso_ringedToposSiteHomRingIso`:
  the unit of the first morphism is invertible at `G` exactly when that of the second is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedToposSiteHom

section Equivalence

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) {R₁ R₂ : Sheaf J RingCat.{u}}
  (e : R₁ ≅ R₂)

/-- **Restriction of scalars along an isomorphism of sheaves of rings is an equivalence**:
`Mod(R₁) ≌ Mod(R₂)` with functor the pushforward along the identity functor and `e.inv`,
inverse the one along `e.hom`. -/
def restrictScalarsEquivalenceRingedToposSiteHomRingIso :
    SheafOfModules.{u} R₁ ≌ SheafOfModules.{u} R₂ :=
  CategoryTheory.Equivalence.mk (SheafOfModules.pushforward.{u} (F := 𝟭 C) (R := R₁) e.inv)
    (SheafOfModules.pushforward.{u} (F := 𝟭 C) (R := R₂) e.hom)
    ((SheafOfModules.pushforwardComp.{u} (F := 𝟭 C) (G := 𝟭 C) (R := R₂) (R' := R₁)
      e.hom e.inv ≪≫
      SheafOfModules.pushforwardCongr.{u} (e.hom_inv_id) ≪≫
        SheafOfModules.pushforwardId.{u} R₁).symm)
    (SheafOfModules.pushforwardComp.{u} (F := 𝟭 C) (G := 𝟭 C) (R := R₁) (R' := R₂)
      e.inv e.hom ≪≫
      SheafOfModules.pushforwardCongr.{u} (e.inv_hom_id) ≪≫
        SheafOfModules.pushforwardId.{u} R₂)

end Equivalence

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O₁ O₂ : Sheaf J CommRingCat.{u}} (e : O₁ ≅ O₂) {Y : RingedTopos.{u, u, u}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (v : Y.C ⥤ C) [v.IsContinuous Y.J J]
  (φ₁ : Y.O ⟶ (v.sheafPushforwardContinuous CommRingCat.{u} Y.J J).obj O₁)
  (φ₂ : Y.O ⟶ (v.sheafPushforwardContinuous CommRingCat.{u} Y.J J).obj O₂)
  (h : φ₂ = φ₁ ≫ (v.sheafPushforwardContinuous CommRingCat.{u} Y.J J).map e.hom)

/-- The morphism of ringed topoi `(Sh(C), O) ⟶ Y` of `v` with the structure map `φ`. -/
abbrev ofStructureMapRingedToposSiteHomRingIso (O : Sheaf J CommRingCat.{u})
    (φ : Y.O ⟶ (v.sheafPushforwardContinuous CommRingCat.{u} Y.J J).obj O) :
    RingedToposSiteHom ⟨C, J, O⟩ Y where
  u := v
  fSharp := φ

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
include h in
/-- The structure maps on sheaves of rings differ by `e`. -/
theorem fSharpRing_ofStructureMap_ringedToposSiteHomRingIso :
    (ofStructureMapRingedToposSiteHomRingIso v O₂ φ₂).fSharpRing =
      (ofStructureMapRingedToposSiteHomRingIso v O₁ φ₁).fSharpRing ≫
      (v.sheafPushforwardContinuous RingCat.{u} Y.J J).map
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map e.hom) := by
  subst h
  rfl

/-- The direct image along the second morphism is restriction of scalars along `e` followed by
the direct image along the first. -/
def pushforwardTopos_ofStructureMap_iso_ringedToposSiteHomRingIso :
    (ofStructureMapRingedToposSiteHomRingIso v O₂ φ₂).pushforwardTopos ≅
      SheafOfModules.pushforward.{u} (F := 𝟭 C)
          (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O₂)
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map e.hom) ⋙
        (ofStructureMapRingedToposSiteHomRingIso v O₁ φ₁).pushforwardTopos :=
  SheafOfModules.pushforwardCongr.{u}
      (fSharpRing_ofStructureMap_ringedToposSiteHomRingIso e v φ₁ φ₂ h) ≪≫
    (SheafOfModules.pushforwardComp.{u} (G := 𝟭 C)
      (R' := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O₂)
      (ofStructureMapRingedToposSiteHomRingIso v O₁ φ₁).fSharpRing
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map e.hom)).symm

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
include e h in
/-- **Changing the structure sheaf of the source along an isomorphism does not change where the
unit is invertible**: for `φ₂ = φ₁ ≫ v_*(e)`, the unit of `f_1^* ⊣ f_{1,*}` is invertible at `G`
exactly when that of `f_2^* ⊣ f_{2,*}` is. -/
theorem isIso_unit_app_iff_of_ringIso_ringedToposSiteHomRingIso
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    IsIso ((ofStructureMapRingedToposSiteHomRingIso v O₁ φ₁).pullbackPushforwardAdjunctionTopos
        |>.unit.app G) ↔
      IsIso ((ofStructureMapRingedToposSiteHomRingIso v O₂ φ₂).pullbackPushforwardAdjunctionTopos
        |>.unit.app G) := by
  let eqv := restrictScalarsEquivalenceRingedToposSiteHomRingIso J
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).mapIso e)
  have hc := Adjunction.isIso_unit_app_iff_of_iso_right
    ((ofStructureMapRingedToposSiteHomRingIso v O₁ φ₁).pullbackPushforwardAdjunctionTopos.comp
      eqv.toAdjunction)
    (ofStructureMapRingedToposSiteHomRingIso v O₂ φ₂).pullbackPushforwardAdjunctionTopos
    (pushforwardTopos_ofStructureMap_iso_ringedToposSiteHomRingIso e v φ₁ φ₂ h).symm G
  rw [show ((ofStructureMapRingedToposSiteHomRingIso v O₁ φ₁).pullbackPushforwardAdjunctionTopos
      |>.comp eqv.toAdjunction).unit.app G = _ from Adjunction.comp_unit_app _ _ G] at hc
  have : IsIso (eqv.toAdjunction.unit.app
      ((ofStructureMapRingedToposSiteHomRingIso v O₁ φ₁).pullbackTopos.obj G)) :=
    Iso.isIso_hom (eqv.unitIso.app _)
  rw [← hc]
  have : IsIso ((ofStructureMapRingedToposSiteHomRingIso v O₁ φ₁).pushforwardTopos.map
      (eqv.toAdjunction.unit.app
        ((ofStructureMapRingedToposSiteHomRingIso v O₁ φ₁).pullbackTopos.obj G))) :=
    Iso.isIso_hom
      ((ofStructureMapRingedToposSiteHomRingIso v O₁ φ₁).pushforwardTopos.mapIso
        (eqv.unitIso.app _))
  exact (isIso_comp_right_iff _ _).symm

end AlgebraicGeometry.RingedToposSiteHom
