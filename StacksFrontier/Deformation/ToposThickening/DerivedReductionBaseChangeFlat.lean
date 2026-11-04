module

public import StacksFrontier.Deformation.ToposThickening.DerivedExtensionOfScalarsComp
public import StacksFrontier.Deformation.ToposThickening.DerivedLiftBaseChange
public import StacksFrontier.Deformation.ToposThickening.IdealPartInclBaseChange
public import StacksFrontier.Deformation.ToposThickening.SquareZeroReductionTriangle

/-!
# Base change of the reduction triangle along a morphism of square-zero thickenings

(module docstring to be completed)

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe d d' d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O' O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀} {f' : O' ⟶ O₀} (g : O ⟶ O')
  (hg : g ≫ f' = f)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- A functor carries `b ≫ e.inv ≫ e.hom` to the image of `b`. -/
theorem comp_inv_hom_map_eq {D E : Type*} [Category D] [Category E] (G : D ⥤ E) {X Y Z : D}
    (b : X ⟶ Z) (e : Y ≅ Z) : G.map (b ≫ e.inv) ≫ G.map e.hom = G.map b := by
  rw [← Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- A functor carries a relation `a ≫ b ≫ c = a' ≫ d` to the relation of the images. -/
theorem map_comp_comp_eq_of_eq {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {X Y Y' Z W : D} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (a' : X ⟶ Y') (d : Y' ⟶ W)
    (h : a ≫ b ≫ c = a' ≫ d) : F.map a ≫ F.map b ≫ F.map c = F.map a' ≫ F.map d := by
  simp only [← F.map_comp, h]

/-- A chain of morphisms collapses through four given relations. The objects are abstract, so
that different spellings of the same object of a derived category meet only when the lemma is
applied. -/
theorem comp_chain_five_eq {D : Type*} [Category D] {A B₁ B₂ B₃ B₄ B₅ B₆ E C₁ C₂ : D}
    (a : A ⟶ B₁) (i : B₁ ⟶ B₂) (x₁ : B₂ ⟶ B₃) (x₂ : B₃ ⟶ B₄) (h : B₄ ⟶ B₅) (q : B₅ ⟶ B₆)
    (j : B₆ ⟶ E) (y : B₂ ⟶ B₄) (r : B₁ ⟶ B₅) (a' : A ⟶ C₁) (i' : C₁ ⟶ C₂) (z : C₂ ⟶ E)
    (s : C₁ ⟶ B₆) (h₁ : x₁ ≫ x₂ = y) (h₂ : i ≫ y ≫ h = r) (h₃ : i' ≫ z = s ≫ j)
    (h₄ : a ≫ r ≫ q = a' ≫ s) :
    (a ≫ i) ≫ x₁ ≫ x₂ ≫ h ≫ q ≫ j = (a' ≫ i') ≫ z := by
  rw [reassoc_of% h₁, Category.assoc, reassoc_of% h₂, reassoc_of% h₄, Category.assoc, h₃]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The terms of the degreewise extension of scalars of a complex. -/
theorem extensionOfScalarsCochainComplex_obj_X {O₁ O₂ : Sheaf J CommRingCat.{u}} (h : O₁ ⟶ O₂)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) ℤ)
    (n : ℤ) :
    ((extensionOfScalarsCochainComplex J h).obj P).X n = (extensionOfScalars h).obj (P.X n) :=
  rfl

/-- Extension of scalars along `f = g ≫ f'` of a complex is extension along `g` and then along
`f'`, degreewise: `Deformation.ComplexLift.extensionOfScalarsCompIso` in each degree. -/
def extensionOfScalarsCompComplexIso
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    (extensionOfScalarsCochainComplex J f).obj P ≅
      (extensionOfScalarsCochainComplex J f').obj ((extensionOfScalarsCochainComplex J g).obj P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((extensionOfScalarsCompIso g hg).app (P.X n)).symm)
    (fun i j _ => ((extensionOfScalarsCompIso g hg).inv.naturality (P.d i j)).symm)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))] in
/-- In degree `n`, the forward map of `extensionOfScalarsCompComplexIso` is the inverse of
`extensionOfScalarsCompIso` at `P.X n`. -/
@[simp]
theorem extensionOfScalarsCompComplexIso_hom_f
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (n : ℤ) :
    (extensionOfScalarsCompComplexIso g hg P).hom.f n =
      (extensionOfScalarsCompIso g hg).inv.app (P.X n) := rfl

/-- **The comparison of the derived base changes, on a complex.** At the localization of a
complex `P` of `O`-modules, the identification `(- ⊗^L_O O') ⊗^L_{O'} O₀ ≅ - ⊗^L_O O₀` of
`Deformation.ComplexLift.derivedExtensionOfScalarsCompIso` is, through the comparisons of the
derived base changes with degreewise extension of scalars, the degreewise identification
`O₀ ⊗_O P ≅ O₀ ⊗_{O'} (O' ⊗_O P)`. -/
theorem derivedExtensionOfScalarsCompIso_inv_app_Q
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    (derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).inv.app (DerivedCategory.Q.obj P) ≫
        (derivedExtensionOfScalars.{d', d₀} f').map
          ((derivedExtensionOfScalarsCounit.{d, d'} g).app P) ≫
        (derivedExtensionOfScalarsCounit.{d', d₀} f').app
          ((extensionOfScalarsCochainComplex J g).obj P) =
      (derivedExtensionOfScalarsCounit.{d, d₀} f).app P ≫
        DerivedCategory.Q.map (extensionOfScalarsCompComplexIso g hg P).hom := by
  apply ((derivedAdjunction.{d, d₀} f).homEquiv _ _).injective
  rw [derivedAdjunction_homEquiv_derivedExtensionOfScalarsCompIso,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_comp]
  have hf := derivedAdjunction_unit_app_comp_counit.{d, d₀} f P
  have hf' := derivedAdjunction_unit_app_comp_counit.{d', d₀} f'
    ((extensionOfScalarsCochainComplex J g).obj P)
  have hg' := derivedAdjunction_unit_app_comp_counit.{d, d'} g P
  have hcx : reductionMapComplex (f := g) P ≫
      ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (reductionMapComplex (f := f')
          ((extensionOfScalarsCochainComplex J g).obj P)) ≫
      (Functor.mapHomologicalComplexCompIso (restrictScalarsCompIsoOf g hg)
        (ComplexShape.up ℤ)).hom.app ((extensionOfScalarsCochainComplex J f').obj
          ((extensionOfScalarsCochainComplex J g).obj P)) =
      reductionMapComplex (f := f) P ≫
        ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (extensionOfScalarsCompComplexIso g hg P).hom := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    have h := extendRestrictAdjunction_unit_comp_extensionOfScalarsCompIso_inv g hg (P.X n)
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso] at h ⊢
    exact h.symm
  dsimp only [Functor.comp_obj]
  rw [restrictionOnDerivedCompIso_hom_app_Q, Functor.map_comp, reassoc_of% hf, hg',
    ← Functor.map_comp (restrictionOnDerived g), hf']
  dsimp only [restrictionOnDerivedCompFactors, restrictScalarsCompMapHomologicalComplexIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  unfold restrictionOnDerived
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Category.assoc]
  have h1 := comp_inv_hom_map_eq
    (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategory
    (DerivedCategory.Q.map (reductionMapComplex (f := f')
      ((extensionOfScalarsCochainComplex J g).obj P)))
    ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f')).mapDerivedCategoryFactors.app
      ((extensionOfScalarsCochainComplex J f').obj ((extensionOfScalarsCochainComplex J g).obj P)))
  have h2 :
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.inv.app
        ((extensionOfScalarsCochainComplex J g).obj P) ≫
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategory.map
        (DerivedCategory.Q.map (reductionMapComplex (f := f')
          ((extensionOfScalarsCochainComplex J g).obj P))) ≫
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapDerivedCategoryFactors.hom.app
        _ =
      DerivedCategory.Q.map
        (((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (reductionMapComplex (f := f')
            ((extensionOfScalarsCochainComplex J g).obj P))) := by
    rw [Functor.mapDerivedCategoryFactors_hom_naturality, Iso.inv_hom_id_app_assoc]
  have h3 :=
    (SheafOfModules.restrictScalars (ringSheafMapOf J f)).mapDerivedCategoryFactors.inv.naturality
      (extensionOfScalarsCompComplexIso g hg P).hom
  dsimp only [Functor.comp_map] at h3
  refine comp_chain_five_eq _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3.symm ?_
  exact map_comp_comp_eq_of_eq DerivedCategory.Q _ _ _ _ _ hcx

/-! ### The base change of the reduction sequence -/

section Sequence

variable {I₀ I₀' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)} (u₀ : I₀ ⟶ I₀')

/-- The base change of the ideal part, `((O₀ ⊗_O M) ⊗ I₀)|_O ⟶ ((O₀ ⊗_{O'} (O' ⊗_O M)) ⊗ I₀')|_O`:
the comparison of the extensions of scalars, tensored with `u₀`, read over `O`. -/
def idealPartBaseChange :
    idealPart f I₀ ⟶ extensionOfScalars g ⋙ idealPart f' I₀' ⋙
      SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g) :=
  Functor.whiskerRight (extensionOfScalarsCompIso g hg).inv
      (tensorRight O₀ I₀ ⋙ SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)) ≫
    Functor.whiskerLeft (extensionOfScalars g ⋙ extensionOfScalars f')
      (Functor.whiskerRight
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O₀).flip.map u₀)
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f))) ≫
    Functor.whiskerLeft (extensionOfScalars g ⋙ extensionOfScalars f' ⋙ tensorRight O₀ I₀')
      (restrictScalarsCompIsoOf g hg).inv

/-- The base change of the reduction, `(O₀ ⊗_O M)|_O ⟶ (O₀ ⊗_{O'} (O' ⊗_O M))|_O`. -/
def reductionPartBaseChange :
    reductionPart f ⟶ extensionOfScalars g ⋙ reductionPart f' ⋙
      SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g) :=
  Functor.whiskerRight (extensionOfScalarsCompIso g hg).inv
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)) ≫
    Functor.whiskerLeft (extensionOfScalars g ⋙ extensionOfScalars f')
      (restrictScalarsCompIsoOf g hg).inv

/-- The base change of the ideal part, degreewise on a complex. -/
def idealPartBaseChangeComplex
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    ((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((idealPart f' I₀').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((extensionOfScalarsCochainComplex J g).obj P)) where
  f n := (idealPartBaseChange g hg u₀).app (P.X n)
  comm' i j _ := ((idealPartBaseChange g hg u₀).naturality (P.d i j)).symm

/-- The base change of the reduction, degreewise on a complex. -/
def reductionPartBaseChangeComplex
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    ((reductionPart f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((reductionPart f').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((extensionOfScalarsCochainComplex J g).obj P)) where
  f n := (reductionPartBaseChange g hg).app (P.X n)
  comm' i j _ := ((reductionPartBaseChange g hg).naturality (P.d i j)).symm

/-- The unit `P ⟶ (O' ⊗_O P)|_O` of extension of scalars along `g`, degreewise on a complex. -/
def extensionUnitComplex
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    P ⟶ ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochainComplex J g).obj P) where
  f n := (extendRestrictAdjunction g).unit.app (P.X n)
  comm' i j _ := ((extendRestrictAdjunction g).unit.naturality (P.d i j)).symm

variable (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f) = 0)
  (ι' : restrictIdeal f' I₀' ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
  (hι' : ι' ≫
    Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f') = 0)
  (hu : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J g) =
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).map u₀ ≫
        (restrictScalarsCompIsoOf g hg).inv.app I₀' ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).map ι')

omit [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))] in
include hu in
/-- The base change of the ideal part is compatible with the inclusions of the ideal parts and
the unit along `g`: `Deformation.ComplexLift.idealPartIncl_app_comp_unit`, read with
`Deformation.ComplexLift.idealPartBaseChange`. -/
theorem idealPartBaseChange_app_comp_idealPartIncl
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (idealPartBaseChange g hg u₀).app M ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).map
          ((idealPartIncl f' ι').app ((extensionOfScalars g).obj M)) =
      (idealPartIncl f ι).app M ≫ (extendRestrictAdjunction g).unit.app M := by
  rw [idealPartIncl_app_comp_unit g hg ι ι' u₀ hu M]
  simp only [idealPartBaseChange, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_map, Functor.map_comp, Category.assoc]
  rfl

omit [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))] in
include hu in
/-- The base change of the ideal part is compatible with the inclusions of the ideal parts and
the unit along `g`, degreewise on a complex. -/
theorem idealPartBaseChangeComplex_comp_idealPartInclComplex
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    idealPartBaseChangeComplex g hg u₀ P ≫
        ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (idealPartInclComplex ι' ((extensionOfScalarsCochainComplex J g).obj P)) =
      idealPartInclComplex ι P ≫ extensionUnitComplex g P :=
  by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have key := idealPartBaseChange_app_comp_idealPartIncl g hg u₀ ι ι' hu (P.X n)
  dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_obj_X, idealPartBaseChangeComplex, idealPartInclComplex,
    extensionUnitComplex, extensionOfScalarsCochainComplex_obj_X, Functor.comp_obj] at key ⊢
  convert key using 1

include hu in
/-- **The base change of the reduction sequence.** For a complex `P` of `O`-modules, the
reduction sequence of `P` along `f` maps to the restriction to `O` of the reduction sequence of
`O' ⊗_O P` along `f'`: by the unit `P ⟶ (O' ⊗_O P)|_O` in the middle, and by the base changes of
the reduction and of the ideal part on the outside. -/
def reductionSequenceBaseChange
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    reductionSequence ι hι P ⟶
      (reductionSequence ι' hι' ((extensionOfScalarsCochainComplex J g).obj P)).map
        ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).mapHomologicalComplex
          (ComplexShape.up ℤ)) where
  τ₁ := idealPartBaseChangeComplex g hg u₀ P
  τ₂ := extensionUnitComplex g P
  τ₃ := reductionPartBaseChangeComplex g hg P
  comm₁₂ := idealPartBaseChangeComplex_comp_idealPartInclComplex g hg u₀ ι ι' hu P
  comm₂₃ := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    have h := extendRestrictAdjunction_unit_comp_extensionOfScalarsCompIso_inv g hg (P.X n)
    have h' : (extendRestrictAdjunction g).unit.app (P.X n) ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).map
          ((extendRestrictAdjunction f').unit.app ((extensionOfScalars g).obj (P.X n))) =
        (extendRestrictAdjunction f).unit.app (P.X n) ≫
          (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).map
            ((extensionOfScalarsCompIso g hg).inv.app (P.X n)) ≫
          (restrictScalarsCompIsoOf g hg).inv.app _ := by
      rw [reassoc_of% h]
      simp
    exact h'

end Sequence

end Deformation.ComplexLift

end
