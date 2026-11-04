module

public import StacksFrontier.Deformation.ToposThickening.DerivedExtensionOfScalarsComp

/-!
# Associativity of derived base change along composites

Let `g₁ : O ⟶ O'`, `g₂ : O' ⟶ O''`, `g₃ : O'' ⟶ O₀` be morphisms of sheaves of commutative rings
on a site. The identifications `Deformation.ComplexLift.derivedExtensionOfScalarsCompIso` of
derived base change along a composite with the composite of derived base changes satisfy the
associativity (pentagon) coherence
(`Deformation.ComplexLift.derivedExtensionOfScalarsCompIso_assoc`): the two identifications of
`((- ⊗^L O') ⊗^L O'') ⊗^L O₀` with `- ⊗^L O₀` agree. It follows by adjunction from the same
coherence for derived restriction of scalars
(`Deformation.ComplexLift.restrictionOnDerivedCompIso_assoc`), which holds on complexes because
the identifications of restrictions of scalars are identities on the underlying presheaves.

In the proof of Stacks 0DLL this makes the reference lifts `s^* K₀` over `O₀[V]`, `s` the section
of `O₀[V] ⟶ O₀`, compatible with base change along `O₀[V] ⟶ O₀[W]`.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe d d' d'' d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O' O'' O₀ : Sheaf J CommRingCat.{u}} (g₁ : O ⟶ O') (g₂ : O' ⟶ O'') (g₃ : O'' ⟶ O₀)
  {f₁₂ : O ⟶ O''} {f₂₃ : O' ⟶ O₀} {f : O ⟶ O₀} (h₁₂ : g₁ ≫ g₂ = f₁₂) (h₂₃ : g₂ ≫ g₃ = f₂₃)
  (h : f₁₂ ≫ g₃ = f) (h' : g₁ ≫ f₂₃ = f)

/-- **Associativity of the identifications of restrictions of scalars, on complexes**: both
composites are the identity on the underlying presheaves. -/
theorem restrictScalarsCompIsoOf_mapHomologicalComplex_assoc
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ) :
    (Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g₁ h₁₂)
          (ComplexShape.up ℤ)).hom.app
        (((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g₃)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≫
      (Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf f₁₂ h)
          (ComplexShape.up ℤ)).hom.app M =
    ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g₁)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g₂ h₂₃)
          (ComplexShape.up ℤ)).hom.app M) ≫
      (Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g₁ h')
          (ComplexShape.up ℤ)).hom.app M := by
  ext n U x
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact (congrArg _ (restrictScalarsCompIsoOf_hom_app_val_app g₁ h₁₂ _ U x)).trans
    ((restrictScalarsCompIsoOf_hom_app_val_app f₁₂ h _ U x).trans
      ((restrictScalarsCompIsoOf_hom_app_val_app g₁ h' _ U x).symm.trans
        (congrArg _ (restrictScalarsCompIsoOf_hom_app_val_app g₂ h₂₃ _ U x).symm)))

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d''} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O''))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasDerivedCategory.{d''} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O''))] in
/-- The composite comparison `restrictionOnDerivedCompFactors` at a complex. -/
theorem restrictionOnDerivedCompFactors_hom_app_mapDerivedCategory {f' : O' ⟶ O₀} (g : O ⟶ O')
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ) :
    (restrictionOnDerivedCompFactors.{d, d', d₀} (f' := f') g).hom.app M =
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategory.map
          ((SheafOfModules.restrictScalars.{u}
            (ringSheafMapOf J f')).mapDerivedCategoryFactors.hom.app M) ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.hom.app
          (((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f')).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) := by
  simp only [restrictionOnDerivedCompFactors, restrictionOnDerived]
  simp

/-- **Associativity of the identifications of derived restrictions of scalars**, as natural
transformations. -/
theorem restrictionOnDerivedCompIso_assoc_natTrans :
    Functor.whiskerLeft (restrictionOnDerived.{d'', d₀} g₃)
        (restrictionOnDerivedCompIso.{d, d', d''} g₁ h₁₂).hom ≫
      (restrictionOnDerivedCompIso.{d, d'', d₀} f₁₂ h).hom =
    (Functor.associator (restrictionOnDerived.{d'', d₀} g₃) (restrictionOnDerived.{d', d''} g₂)
        (restrictionOnDerived.{d, d'} g₁)).inv ≫
      Functor.whiskerRight (restrictionOnDerivedCompIso.{d', d'', d₀} g₂ h₂₃).hom
        (restrictionOnDerived.{d, d'} g₁) ≫
      (restrictionOnDerivedCompIso.{d, d', d₀} g₁ h').hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ)) (fun M => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp]
  rw [restrictionOnDerivedCompIso_hom_app_Q, restrictionOnDerivedCompIso_hom_app_Q,
    restrictionOnDerivedCompIso_hom_app_Q]
  have n1 := (restrictionOnDerivedCompIso.{d, d', d''} g₁ h₁₂).hom.naturality
    ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g₃)).mapDerivedCategoryFactors.hom.app M)
  simp only [Functor.comp_obj] at n1
  rw [restrictionOnDerivedCompIso_hom_app_Q] at n1
  simp only [restrictionOnDerivedCompFactors_hom_app_mapDerivedCategory,
    restrictScalarsCompMapHomologicalComplexIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp] at n1 ⊢
  simp only [restrictionOnDerived, Functor.comp_map, Functor.comp_obj] at n1 ⊢
  simp only [Category.assoc] at n1 ⊢
  rw [← reassoc_of% n1, Iso.inv_hom_id_app_assoc]
  have n3 : (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g₁)).mapDerivedCategory.map
        ((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f₂₃)).mapDerivedCategoryFactors.inv.app M) ≫
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g₁)).mapDerivedCategory.map
        ((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f₂₃)).mapDerivedCategoryFactors.hom.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have n2 := (SheafOfModules.restrictScalars.{u}
      (ringSheafMapOf J g₁)).mapDerivedCategoryFactors.hom.naturality
    ((Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g₂ h₂₃)
      (ComplexShape.up ℤ)).hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at n2
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% n3, reassoc_of% n2, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    restrictScalarsCompIsoOf_mapHomologicalComplex_assoc g₁ g₂ g₃ h₁₂ h₂₃ h h' M]
  simp only [Functor.map_comp, Category.assoc]

/-- **Associativity of the identifications of derived restrictions of scalars.** -/
theorem restrictionOnDerivedCompIso_assoc
    (Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))) :
    (restrictionOnDerivedCompIso.{d, d', d''} g₁ h₁₂).hom.app
        ((restrictionOnDerived.{d'', d₀} g₃).obj Y) ≫
      (restrictionOnDerivedCompIso.{d, d'', d₀} f₁₂ h).hom.app Y =
    (restrictionOnDerived.{d, d'} g₁).map
        ((restrictionOnDerivedCompIso.{d', d'', d₀} g₂ h₂₃).hom.app Y) ≫
      (restrictionOnDerivedCompIso.{d, d', d₀} g₁ h').hom.app Y := by
  have := congrArg (fun τ => τ.app Y)
    (restrictionOnDerivedCompIso_assoc_natTrans.{d, d', d''} g₁ g₂ g₃ h₁₂ h₂₃ h h')
  simpa using this

/-- **Associativity of the identifications of derived base changes along composites**: the two
identifications of `((K ⊗^L O') ⊗^L O'') ⊗^L O₀` with `K ⊗^L O₀` agree. -/
theorem derivedExtensionOfScalarsCompIso_assoc
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))) :
    (derivedExtensionOfScalars.{d'', d₀} g₃).map
        ((derivedExtensionOfScalarsCompIso.{d, d', d''} g₁ h₁₂).hom.app K) ≫
      (derivedExtensionOfScalarsCompIso.{d, d'', d₀} f₁₂ h).hom.app K =
    (derivedExtensionOfScalarsCompIso.{d', d'', d₀} g₂ h₂₃).hom.app
        ((derivedExtensionOfScalars.{d, d'} g₁).obj K) ≫
      (derivedExtensionOfScalarsCompIso.{d, d', d₀} g₁ h').hom.app K := by
  have key : (derivedExtensionOfScalarsCompIso.{d, d'', d₀} f₁₂ h).inv.app K ≫
        (derivedExtensionOfScalars.{d'', d₀} g₃).map
          ((derivedExtensionOfScalarsCompIso.{d, d', d''} g₁ h₁₂).inv.app K) =
      (derivedExtensionOfScalarsCompIso.{d, d', d₀} g₁ h').inv.app K ≫
        (derivedExtensionOfScalarsCompIso.{d', d'', d₀} g₂ h₂₃).inv.app
          ((derivedExtensionOfScalars.{d, d'} g₁).obj K) := by
    apply ((derivedAdjunction.{d, d₀} f).homEquiv _ _).injective
    rw [derivedAdjunction_homEquiv_derivedExtensionOfScalarsCompIso,
      derivedAdjunction_homEquiv_derivedExtensionOfScalarsCompIso,
      ← Category.comp_id ((derivedExtensionOfScalars.{d'', d₀} g₃).map _),
      Adjunction.homEquiv_naturality_left,
      derivedAdjunction_homEquiv_derivedExtensionOfScalarsCompIso,
      ← Category.comp_id ((derivedExtensionOfScalarsCompIso.{d', d'', d₀} g₂ h₂₃).inv.app _),
      derivedAdjunction_homEquiv_derivedExtensionOfScalarsCompIso,
      Adjunction.homEquiv_naturality_right, Category.assoc, Category.assoc,
      restrictionOnDerivedCompIso_assoc.{d, d', d'', d₀} g₁ g₂ g₃ h₁₂ h₂₃ h h']
    rfl
  have e := ((Iso.inv_eq_inv
    ((derivedExtensionOfScalars.{d'', d₀} g₃).mapIso
        ((derivedExtensionOfScalarsCompIso.{d, d', d''} g₁ h₁₂).app K) ≪≫
      (derivedExtensionOfScalarsCompIso.{d, d'', d₀} f₁₂ h).app K)
    ((derivedExtensionOfScalarsCompIso.{d', d'', d₀} g₂ h₂₃).app
        ((derivedExtensionOfScalars.{d, d'} g₁).obj K) ≪≫
      (derivedExtensionOfScalarsCompIso.{d, d', d₀} g₁ h').app K)).1 (by simpa using key))
  simpa using e

end Deformation.ComplexLift

end
