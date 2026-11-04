module

public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import StacksFrontier.Deformation.ToposThickening.DerivedReductionData

/-!
# Derived base change along a composite of morphisms of sheaves of rings

Let `g : O ⟶ O'` and `f' : O' ⟶ O₀` be morphisms of sheaves of commutative rings on a site, and
`f = g ≫ f'`. Restriction of scalars along `f` is restriction along `f'` followed by restriction
along `g`, already on modules and so on derived categories, where restriction of scalars needs no
deriving. By uniqueness of left adjoints, derived base change along `g` followed by derived base
change along `f'` is derived base change along `f`:

`(- ⊗^L_O O') ⊗^L_{O'} O₀ ≅ - ⊗^L_O O₀`.

This is the identification of the two derived base changes of a lift in the proof of Stacks
0DLL: there `O = O₀[V]` and `O' = O₀[W]` are the structure sheaves of `X_V` and `X_W` on the
small étale site of the special fibre `X₀`, `g` is induced by a linear map `V ⟶ W`, and `f`, `f'`
are the reductions to `X₀`.

The identification is defined through the adjunctions, not through resolutions, so it is
compatible with them by construction:
`Deformation.ComplexLift.derivedAdjunction_homEquiv_derivedExtensionOfScalarsCompIso` writes the
adjunction transpose along `f` as the transpose along `f'` followed by the transpose along `g`.
This is what makes base change of lifts along `g` compatible with the obstruction classes of
Stacks 0DIY, which are adjunction transposes.

## Main definitions

* `Deformation.ComplexLift.restrictScalarsCompIsoOf`: restriction of scalars along `f'` and then
  along `g` is restriction along `f`, on sheaves of modules.
* `Deformation.ComplexLift.restrictionOnDerivedCompIso`: the same on derived categories.
* `Deformation.ComplexLift.derivedExtensionOfScalarsCompIso`: derived base change along `g` and
  then along `f'` is derived base change along `f`.

## Main results

* `Deformation.ComplexLift.commShift_restrictionOnDerivedCompIso_hom`: the identification of the
  derived restrictions commutes with the shift.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe d d' d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O' O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀} {f' : O' ⟶ O₀} (g : O ⟶ O')
  (hg : g ≫ f' = f)

include hg in
/-- **Restriction of scalars along a composite**: restricting along `f'` and then along `g` is
restricting along `f = g ≫ f'`. Both sides have the same underlying presheaves of abelian groups,
and the identification is the identity on them. -/
def restrictScalarsCompIsoOf :
    SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f') ⋙
        SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g) ≅
      SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f) := by
  subst hg
  exact NatIso.ofComponents (fun M =>
    { hom := ⟨PresheafOfModules.homMk (𝟙 M.val.presheaf) (fun _ _ _ => rfl)⟩
      inv := ⟨PresheafOfModules.homMk (𝟙 M.val.presheaf) (fun _ _ _ => rfl)⟩
      hom_inv_id := rfl
      inv_hom_id := rfl }) (fun _ => rfl)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The component at `M` of `restrictScalarsCompIsoOf` is the identity on sections. -/
theorem restrictScalarsCompIsoOf_hom_app_val_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) (U : Cᵒᵖ)
    (x : M.val.obj U) :
    ((restrictScalarsCompIsoOf g hg).hom.app M).val.app U x = x := by
  subst hg
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The component at `M` of the inverse of `restrictScalarsCompIsoOf` is the identity on
sections. -/
theorem restrictScalarsCompIsoOf_inv_app_val_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) (U : Cᵒᵖ)
    (x : M.val.obj U) :
    ((restrictScalarsCompIsoOf g hg).inv.app M).val.app U x = x := by
  subst hg
  rfl

/-- The composite of the adjunctions along `g` and along `f'`, read with restriction along `f`
as right adjoint. -/
def extendRestrictAdjunctionComp :
    extensionOfScalars g ⋙ extensionOfScalars f' ⊣
      SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f) :=
  ((extendRestrictAdjunction g).comp (extendRestrictAdjunction f')).ofNatIsoRight
    (restrictScalarsCompIsoOf g hg)

/-- **Extension of scalars along a composite**, on sheaves of modules: extension along `g` and
then along `f'` is extension along `f = g ≫ f'`, by uniqueness of left adjoints. -/
def extensionOfScalarsCompIso :
    extensionOfScalars g ⋙ extensionOfScalars f' ≅ extensionOfScalars f :=
  (extendRestrictAdjunctionComp g hg).leftAdjointUniq (extendRestrictAdjunction f)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The unit along `f`, followed by the comparison of the extensions of scalars, is the unit
along `g` followed by the unit along `f'`. -/
theorem extendRestrictAdjunction_unit_comp_extensionOfScalarsCompIso_inv
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (extendRestrictAdjunction f).unit.app M ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).map
          ((extensionOfScalarsCompIso g hg).inv.app M) =
      (extendRestrictAdjunction g).unit.app M ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).map
          ((extendRestrictAdjunction f').unit.app ((extensionOfScalars g).obj M)) ≫
        (restrictScalarsCompIsoOf g hg).hom.app _ := by
  rw [show (extensionOfScalarsCompIso g hg).inv.app M =
    ((extendRestrictAdjunction f).leftAdjointUniq (extendRestrictAdjunctionComp g hg)).hom.app M
    from rfl, Adjunction.unit_leftAdjointUniq_hom_app]
  simp [extendRestrictAdjunctionComp, Adjunction.comp_unit_app]

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- The composite of the two derived restrictions of scalars, precomposed with the localization,
is degreewise restriction along `f'` and `g`, followed by the localization. -/
def restrictionOnDerivedCompFactors :
    DerivedCategory.Q ⋙ (restrictionOnDerived.{d', d₀} f' ⋙ restrictionOnDerived.{d, d'} g) ≅
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f')).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f')).mapDerivedCategoryFactors
      (restrictionOnDerived.{d, d'} g) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors

/-- The composite of the degreewise restrictions along `f'` and `g` is degreewise restriction
along `f`. -/
def restrictScalarsCompMapHomologicalComplexIso :
    (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f')).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Q : _ ⥤ DerivedCategory (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf O))) ≅
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g hg) (ComplexShape.up ℤ))
      DerivedCategory.Q

/-- The composite of the two derived restrictions lifts the composite of the degreewise
restrictions through the localization. -/
instance liftingRestrictionOnDerivedComp :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
        (ComplexShape.up ℤ))
      ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f')).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (restrictionOnDerived.{d', d₀} f' ⋙ restrictionOnDerived.{d, d'} g) :=
  ⟨restrictionOnDerivedCompFactors.{d, d', d₀} g⟩

/-- Derived restriction along `f` lifts degreewise restriction along `f`. -/
instance liftingRestrictionOnDerived :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
        (ComplexShape.up ℤ))
      ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (restrictionOnDerived.{d, d₀} f) :=
  ⟨(SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactors⟩

/-- **Derived restriction of scalars along a composite**: derived restriction along `f'` and then
along `g` is derived restriction along `f = g ≫ f'`. Both lift degreewise restriction along `f`
through the localization, so this is the lift of the identity. -/
def restrictionOnDerivedCompIso :
    restrictionOnDerived.{d', d₀} f' ⋙ restrictionOnDerived.{d, d'} g ≅
      restrictionOnDerived.{d, d₀} f :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ)) _ _ _ _ (restrictScalarsCompMapHomologicalComplexIso.{d} g hg)

/-- The composite of the two derived adjunctions, along `g` and then along `f'`, read with
derived restriction along `f` as right adjoint. -/
def derivedAdjunctionComp :
    derivedExtensionOfScalars.{d, d'} g ⋙ derivedExtensionOfScalars.{d', d₀} f' ⊣
      restrictionOnDerived.{d, d₀} f :=
  ((derivedAdjunction.{d, d'} g).comp (derivedAdjunction.{d', d₀} f')).ofNatIsoRight
    (restrictionOnDerivedCompIso.{d, d', d₀} g hg)

/-- **Derived base change along a composite**: derived base change along `g` followed by derived
base change along `f'` is derived base change along `f = g ≫ f'`, by uniqueness of left
adjoints of derived restriction of scalars along `f`. -/
def derivedExtensionOfScalarsCompIso :
    derivedExtensionOfScalars.{d, d'} g ⋙ derivedExtensionOfScalars.{d', d₀} f' ≅
      derivedExtensionOfScalars.{d, d₀} f :=
  (derivedAdjunctionComp.{d, d', d₀} g hg).leftAdjointUniq (derivedAdjunction.{d, d₀} f)

/-- **The transpose along `f` is the transpose along `f'` followed by the transpose along `g`**,
through `Deformation.ComplexLift.derivedExtensionOfScalarsCompIso` and
`Deformation.ComplexLift.restrictionOnDerivedCompIso`. -/
theorem derivedAdjunction_homEquiv_derivedExtensionOfScalarsCompIso
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))
    (x : (derivedExtensionOfScalars.{d', d₀} f').obj
      ((derivedExtensionOfScalars.{d, d'} g).obj K) ⟶ Y) :
    (derivedAdjunction.{d, d₀} f).homEquiv K Y
        ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app K ≫ x) =
      (derivedAdjunction.{d, d'} g).homEquiv K _ ((derivedAdjunction.{d', d₀} f').homEquiv _ Y x) ≫
        (restrictionOnDerivedCompIso.{d, d', d₀} g hg).hom.app Y := by
  rw [show (derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app K =
    ((derivedAdjunction.{d, d₀} f).leftAdjointUniq
      (derivedAdjunctionComp.{d, d', d₀} g hg)).hom.app K from rfl]
  rw [Adjunction.homEquiv_apply, Functor.map_comp, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app]
  have hn := (restrictionOnDerivedCompIso.{d, d', d₀} g hg).hom.naturality x
  simp only [Functor.comp_map] at hn
  simp [derivedAdjunctionComp, Adjunction.homEquiv_unit, Adjunction.comp_unit_app, hn]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The identification of the two derived restrictions, at the localization of a complex. -/
theorem restrictionOnDerivedCompIso_hom_app_Q
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ) :
    (restrictionOnDerivedCompIso.{d, d', d₀} g hg).hom.app (DerivedCategory.Q.obj K) =
      (restrictionOnDerivedCompFactors.{d, d', d₀} g).hom.app K ≫
        (restrictScalarsCompMapHomologicalComplexIso.{d} g hg).hom.app K ≫
        (SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f)).mapDerivedCategoryFactors.inv.app K :=
  Localization.liftNatTrans_app _ _ _ _ _ _ _ K

/-- The identification of the composite of the degreewise restrictions with degreewise
restriction along `f` commutes with the shift of cochain complexes. -/
instance commShift_mapHomologicalComplexCompIso_restrictScalarsCompIsoOf :
    NatTrans.CommShift (Functor.mapHomologicalComplexCompIso
      (restrictScalarsCompIsoOf g hg) (ComplexShape.up ℤ)).hom ℤ := ⟨fun a => by
  ext K n
  simp [Functor.mapHomologicalComplexCompIso, Functor.commShiftIso_comp_hom_app]⟩

/-- **Derived restriction along a composite commutes with the shift**: the identification of
derived restriction along `f'` and then along `g` with derived restriction along `f` is
compatible with the commutations of the three functors with the shift. -/
instance commShift_restrictionOnDerivedCompIso_hom :
    NatTrans.CommShift (restrictionOnDerivedCompIso.{d, d', d₀} g hg).hom ℤ := by
  refine NatTrans.commShift_of_whiskerLeft DerivedCategory.Q _ ?_
  have h : Functor.whiskerLeft DerivedCategory.Q
        (restrictionOnDerivedCompIso.{d, d', d₀} g hg).hom =
      (restrictionOnDerivedCompFactors.{d, d', d₀} g).hom ≫
        (restrictScalarsCompMapHomologicalComplexIso.{d} g hg).hom ≫
        (SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f)).mapDerivedCategoryFactors.inv := by
    ext K
    exact restrictionOnDerivedCompIso_hom_app_Q.{d, d', d₀} g hg K
  rw [h]
  unfold restrictionOnDerivedCompFactors restrictScalarsCompMapHomologicalComplexIso
    restrictionOnDerived
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom]
  infer_instance

end Deformation.ComplexLift

end
