module

public import StacksFrontier.Deformation.ToposThickening.DerivedExtensionOfScalarsComp
public import StacksFrontier.Deformation.ToposThickening.SquareZeroReductionTriangle

/-!
# Derived base change along a composite, read on complexes

Let `g : O ⟶ O'` and `f' : O' ⟶ O₀` be morphisms of sheaves of commutative rings on a site, and
`f = g ≫ f'`. The identification
`Deformation.ComplexLift.derivedExtensionOfScalarsCompIso` of derived base change along `g` and
then along `f'` with derived base change along `f` is defined through the derived adjunctions.
This file computes it on a complex `M` of `O`-modules: through the comparisons of the three
derived base changes with degreewise extension of scalars, it is the degreewise identification
`Deformation.ComplexLift.extensionOfScalarsCompIso` of extension of scalars along `g` and then
along `f'` with extension of scalars along `f`.

This is the input that makes the base change of lifts along `O₀[V] ⟶ O₀[W]` in the proof of
Stacks 0DLL computable by resolutions: every comparison met there is a left derived natural
transformation, so its value is determined on complexes.

Nothing here is registered.

## Main results

* `Deformation.ComplexLift.derivedExtensionOfScalarsCompIso_hom_app_comp_counit`: the
  identification of the derived base changes, followed by the comparison along `f`, is the
  comparison along `g` pushed along `f'`, the comparison along `f'`, and the degreewise
  identification of the extensions of scalars.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
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

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The unit along `f` is the unit along `g`, followed by the unit along `f'` restricted along
`g`, the identification of the extensions of scalars and the identification of the
restrictions of scalars. -/
theorem extendRestrictAdjunction_unit_app_eq
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (extendRestrictAdjunction f).unit.app M =
      (extendRestrictAdjunction g).unit.app M ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).map
          ((extendRestrictAdjunction f').unit.app ((extensionOfScalars g).obj M) ≫
            (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f')).map
              ((extensionOfScalarsCompIso g hg).hom.app M)) ≫
        (restrictScalarsCompIsoOf g hg).hom.app ((extensionOfScalars f).obj M) := by
  have h := extendRestrictAdjunction_unit_comp_extensionOfScalarsCompIso_inv g hg M
  have hn := (restrictScalarsCompIsoOf g hg).hom.naturality
    ((extensionOfScalarsCompIso g hg).hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [Functor.map_comp, Category.assoc, hn, ← reassoc_of% h, ← Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

/-- Four commuting squares, the first three of whose horizontal sides lie in the image of a
functor `G` and whose vertical sides lie in the image of a functor `F`, compose: the abstract
shape of the computation of a transpose along a composite, stated with the objects abstract so
that the different spellings of the same object meet only when it is applied. -/
theorem comp_map_chain_eq {D E D' : Type*} [Category D] [Category E] [Category D']
    (F : E ⥤ D) (G : D' ⥤ D) {X₆ : D} {Z₁ Z₂ Z₃ Z₄ Z₅ : D'} {W₀ W₁ W₂ W₃ W₄ : E}
    (x : F.obj W₀ ⟶ G.obj Z₁) (s₁ : Z₁ ⟶ Z₂) (s₂ : Z₂ ⟶ Z₃) (s₃ : Z₃ ⟶ Z₄) (s₄ : Z₄ ⟶ Z₅)
    (r₅ : G.obj Z₅ ⟶ X₆) (c₀ : W₀ ⟶ W₁) (c₁ : W₁ ⟶ W₂) (c₂ : W₂ ⟶ W₃) (c₃ : W₃ ⟶ W₄)
    (w : W₀ ⟶ W₄) (p₁ : F.obj W₁ ⟶ G.obj Z₂) (p₂ : F.obj W₂ ⟶ G.obj Z₃)
    (p₃ : F.obj W₃ ⟶ G.obj Z₄) (p₄ : F.obj W₄ ⟶ X₆)
    (ha : x ≫ G.map s₁ = F.map c₀ ≫ p₁) (hb : p₁ ≫ G.map s₂ = F.map c₁ ≫ p₂)
    (hc : p₂ ≫ G.map s₃ = F.map c₂ ≫ p₃) (hd : p₃ ≫ G.map s₄ ≫ r₅ = F.map c₃ ≫ p₄)
    (he : w = c₀ ≫ c₁ ≫ c₂ ≫ c₃) :
    x ≫ G.map (s₁ ≫ s₂ ≫ s₃ ≫ s₄) ≫ r₅ = F.map w ≫ p₄ := by
  subst he
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc, hd]

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- **Derived base change along a composite, read on complexes.** At the localization of a
complex `M` of `O`-modules, the identification of derived base change along `g` and then along
`f'` with derived base change along `f`, followed by the comparison of derived base change
along `f` with degreewise extension of scalars, is the comparison along `g` pushed along `f'`,
the comparison along `f'` at `O' ⊗_O M`, and the degreewise identification of extension of
scalars along `g` and then along `f'` with extension of scalars along `f`. -/
theorem derivedExtensionOfScalarsCompIso_hom_app_comp_counit
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    (derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).hom.app (DerivedCategory.Q.obj M) ≫
        (derivedExtensionOfScalarsCounit.{d, d₀} f).app M =
      (derivedExtensionOfScalars.{d', d₀} f').map
          ((derivedExtensionOfScalarsCounit.{d, d'} g).app M) ≫
        (derivedExtensionOfScalarsCounit.{d', d₀} f').app
          ((extensionOfScalarsCochainComplex J g).obj M) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (extensionOfScalarsCompIso g hg) (ComplexShape.up ℤ)).hom.app M) := by
  -- the transposes along `f'`, along `g` and along `f`, computed on complexes
  have hA := derivedAdjunction_unit_app_comp_counit.{d', d₀} f'
    ((extensionOfScalarsCochainComplex J g).obj M)
  have hG := derivedAdjunction_unit_app_comp_counit.{d, d'} g M
  have hF := derivedAdjunction_unit_app_comp_counit.{d, d₀} f M
  have hB : ((SheafOfModules.restrictScalars.{u}
      (ringSheafMapOf J f')).mapDerivedCategoryFactors).inv.app
        ((extensionOfScalarsCochainComplex J f').obj
          ((extensionOfScalarsCochainComplex J g).obj M)) ≫
      (restrictionOnDerived.{d', d₀} f').map (DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (extensionOfScalarsCompIso g hg)
          (ComplexShape.up ℤ)).hom.app M)) =
      DerivedCategory.Q.map (((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f')).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (extensionOfScalarsCompIso g hg)
            (ComplexShape.up ℤ)).hom.app M)) ≫
        ((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f')).mapDerivedCategoryFactors).inv.app
          ((extensionOfScalarsCochainComplex J f).obj M) :=
    (((SheafOfModules.restrictScalars.{u}
      (ringSheafMapOf J f')).mapDerivedCategoryFactors).inv.naturality
      ((Functor.mapHomologicalComplexCompIso (extensionOfScalarsCompIso g hg)
          (ComplexShape.up ℤ)).hom.app M)).symm
  have e1 : (derivedAdjunction.{d', d₀} f').homEquiv _ _
      ((derivedExtensionOfScalarsCounit.{d', d₀} f').app
          ((extensionOfScalarsCochainComplex J g).obj M) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (extensionOfScalarsCompIso g hg) (ComplexShape.up ℤ)).hom.app M)) =
      DerivedCategory.Q.map (reductionMapComplex (f := f')
          ((extensionOfScalarsCochainComplex J g).obj M)) ≫
        DerivedCategory.Q.map (((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f')).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (extensionOfScalarsCompIso g hg)
            (ComplexShape.up ℤ)).hom.app M)) ≫
        ((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f')).mapDerivedCategoryFactors).inv.app
          ((extensionOfScalarsCochainComplex J f).obj M) := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, hA]
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (DerivedCategory.Q.map (reductionMapComplex (f := f')
      ((extensionOfScalarsCochainComplex J g).obj M)) ≫ ·) hB
  have hDa : ((SheafOfModules.restrictScalars.{u}
      (ringSheafMapOf J g)).mapDerivedCategoryFactors).inv.app
        ((extensionOfScalarsCochainComplex J g).obj M) ≫
      (restrictionOnDerived.{d, d'} g).map (DerivedCategory.Q.map (reductionMapComplex (f := f')
          ((extensionOfScalarsCochainComplex J g).obj M))) =
      DerivedCategory.Q.map (((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (reductionMapComplex (f := f') ((extensionOfScalarsCochainComplex J g).obj M))) ≫
        ((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J g)).mapDerivedCategoryFactors).inv.app
          (((reductionPart f').mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((extensionOfScalarsCochainComplex J g).obj M)) :=
    (((SheafOfModules.restrictScalars.{u}
      (ringSheafMapOf J g)).mapDerivedCategoryFactors).inv.naturality
      (reductionMapComplex (f := f') ((extensionOfScalarsCochainComplex J g).obj M))).symm
  have hDb : ((SheafOfModules.restrictScalars.{u}
      (ringSheafMapOf J g)).mapDerivedCategoryFactors).inv.app
        (((reductionPart f').mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((extensionOfScalarsCochainComplex J g).obj M)) ≫
      (restrictionOnDerived.{d, d'} g).map
        (DerivedCategory.Q.map (((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f')).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (extensionOfScalarsCompIso g hg)
            (ComplexShape.up ℤ)).hom.app M))) =
      DerivedCategory.Q.map (((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J g)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f')).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (extensionOfScalarsCompIso g hg)
            (ComplexShape.up ℤ)).hom.app M))) ≫
        ((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J g)).mapDerivedCategoryFactors).inv.app
          (((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((extensionOfScalarsCochainComplex J f).obj M)) :=
    (((SheafOfModules.restrictScalars.{u}
      (ringSheafMapOf J g)).mapDerivedCategoryFactors).inv.naturality
      (((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f')).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (extensionOfScalarsCompIso g hg)
            (ComplexShape.up ℤ)).hom.app M))).symm
  have hE : ((SheafOfModules.restrictScalars.{u}
      (ringSheafMapOf J g)).mapDerivedCategoryFactors).inv.app
        (((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((extensionOfScalarsCochainComplex J f).obj M)) ≫
      (restrictionOnDerived.{d, d'} g).map
        (((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f')).mapDerivedCategoryFactors).inv.app
          ((extensionOfScalarsCochainComplex J f).obj M)) ≫
      (restrictionOnDerivedCompIso.{d, d', d₀} g hg).hom.app
        (DerivedCategory.Q.obj ((extensionOfScalarsCochainComplex J f).obj M)) =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g hg)
          (ComplexShape.up ℤ)).hom.app ((extensionOfScalarsCochainComplex J f).obj M)) ≫
        ((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f)).mapDerivedCategoryFactors).inv.app
          ((extensionOfScalarsCochainComplex J f).obj M) := by
    rw [restrictionOnDerivedCompIso_hom_app_Q]
    simp [restrictionOnDerivedCompFactors, restrictScalarsCompMapHomologicalComplexIso,
      restrictionOnDerived]
  have hC : reductionMapComplex (f := f) M = reductionMapComplex (f := g) M ≫
      ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (reductionMapComplex (f := f') ((extensionOfScalarsCochainComplex J g).obj M)) ≫
      ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (((SheafOfModules.restrictScalars.{u}
          (ringSheafMapOf J f')).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (extensionOfScalarsCompIso g hg)
            (ComplexShape.up ℤ)).hom.app M)) ≫
      (Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g hg)
          (ComplexShape.up ℤ)).hom.app ((extensionOfScalarsCochainComplex J f).obj M) := by
    refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
    exact extendRestrictAdjunction_unit_app_eq g hg (M.X n)
  have hR := comp_map_chain_eq DerivedCategory.Q (restrictionOnDerived.{d, d'} g)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG hDa hDb hE hC
  have key : (derivedAdjunction.{d, d₀} f).homEquiv _ _
        ((derivedExtensionOfScalarsCounit.{d, d₀} f).app M) =
      (derivedAdjunction.{d, d₀} f).homEquiv _ _
        ((derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app (DerivedCategory.Q.obj M) ≫
          (derivedExtensionOfScalars.{d', d₀} f').map
            ((derivedExtensionOfScalarsCounit.{d, d'} g).app M) ≫
          (derivedExtensionOfScalarsCounit.{d', d₀} f').app
            ((extensionOfScalarsCochainComplex J g).obj M) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
            (extensionOfScalarsCompIso g hg) (ComplexShape.up ℤ)).hom.app M)) := by
    rw [derivedAdjunction_homEquiv_derivedExtensionOfScalarsCompIso,
      Adjunction.homEquiv_naturality_left]
    simp only [Functor.comp_obj]
    rw [e1]
    refine (Adjunction.homEquiv_unit _ _ _ _).trans (hF.trans ?_)
    rw [Adjunction.homEquiv_unit]
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact hR.symm
  have := ((derivedAdjunction.{d, d₀} f).homEquiv _ _).injective key
  rw [this]
  exact Iso.hom_inv_id_app_assoc _ _ _

end Deformation.ComplexLift

end
