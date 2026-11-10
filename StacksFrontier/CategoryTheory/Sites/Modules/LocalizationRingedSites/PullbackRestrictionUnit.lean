module

public import
  StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackRestrictionSections

/-!
# The native localization comparison inverts the extension-of-scalars unit

For the four-field localization morphism, the comparison with restriction is a transpose.
Reading that transpose on underlying sheaves shows that the comparison is a right inverse
of the extension-of-scalars unit. The proof keeps the two underlying-sheaf functors fixed,
and does the categorical reassociation at arbitrary morphisms.

No claim about Stacks 0GN2 or about the two-field comparison is made here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
  Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.ToposPullback

/-- An identity-on-sections retyping of a unit does not change its triangle identity. -/
theorem unit_retyping_triangle {D : Type*} [Category* D] {P B : D}
    {a a' : P ⟶ B} {t : B ⟶ B} {v w : B ⟶ P} {r : P ⟶ P}
    (ha : a' = a ≫ t) (ht : t = 𝟙 B) (h : a' ≫ v = r)
    (hr : r = 𝟙 P) (hv : v = w) : a ≫ w = 𝟙 P := by
  rw [ht, Category.comp_id] at ha
  rw [← ha, ← hv, h, hr]

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(X.J.over U).HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(X.J.over U).HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- The retyping formula for the localization unit, read on underlying sheaves. -/
theorem map_localizationExtendRestrictAdjunction_unit_app
    (M : SheafOfModules.{u} (commRingSheaf (X.over U).ringedTopos.J
      (inverseImageStructureCommRing (X.localizationMorphism U))
      (Stacks.SheafOfModules.isSheaf_inverseImageStructureCommRing
        (X.localizationMorphism U)))) :
    (localizationModuleForgetInverse X U).map
      ((X.localizationExtendRestrictAdjunction U).unit.app M) =
    (localizationModuleForgetInverse X U).map
      ((Stacks.SheafOfModules.pullbackExtendAdj (X.localizationMorphism U)).unit.app M) ≫
    (localizationModuleForgetInverse X U).map
      ((eqToIso (X.localizationRestrictScalars_eq U)).hom.app
        ((X.localizationExtendScalars U).obj M)) :=
  (congrArg (localizationModuleForgetInverse X U).map
    (X.localizationExtendRestrictAdjunction_unit_app U M)).trans
      ((localizationModuleForgetInverse X U).map_comp _ _)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The unit of Stacks 03CZ for the localization morphism of the modules development, on
underlying sheaves of sets, followed by the comparison of Stacks 04IX for that same morphism, is
the identity: the comparison is the inverse transpose of the inverse-image identification of
Stacks 03D2, which is the identity on sections.

This is the assembly of
`unit_comp_restrictScalars_map_localizationPullbackIsoRestriction`,
`localizationExtendRestrictAdjunction_unit_app`,
`moduleSheafFunctor_map_localizationRestrictScalars_eq_hom_app` and
`moduleSheafFunctor_map_restrictionModuleIso_hom_app`. -/
theorem map_unit_comp_localizationPullbackIsoRestriction
    (Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (localizationModuleForgetInverse X U).map
        ((Stacks.SheafOfModules.pullbackExtendAdj (X.localizationMorphism U)).unit.app
          ((inverseImageModules (X.localizationMorphism U).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.ringedTopos.O)).obj Z)) ≫
      (localizationModuleForgetTarget X U).map
        ((X.localizationPullbackIsoRestriction U).hom.app Z) = 𝟙 _ := by
  have hret := X.moduleSheafFunctor_map_localizationRestrictScalars_eq_hom_app U
    ((X.localizationExtendScalars U).obj
      ((inverseImageModules (X.localizationMorphism U).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.ringedTopos.O)).obj Z))
  have hu := X.map_localizationExtendRestrictAdjunction_unit_app U
    ((inverseImageModules (X.localizationMorphism U).toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.ringedTopos.O)).obj Z)
  have hm := ((localizationModuleForgetInverse X U).map_comp _ _).symm.trans
    (congrArg (localizationModuleForgetInverse X U).map
      (X.unit_comp_restrictScalars_map_localizationPullbackIsoRestriction U Z))
  have hv := moduleSheafFunctor_map_restrictScalars_map (X.overInverseImageRingIso U).hom
    ((X.localizationPullbackIsoRestriction U).hom.app Z)
  exact unit_retyping_triangle hu hret hm
    (X.moduleSheafFunctor_map_restrictionModuleIso_hom_app U Z) hv

end AlgebraicGeometry.RingedSite

end
