module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerivedNaturality
public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorExtendHomotopyHomology

/-! # The object-level comparison `Hⁿ(RF(M[0])) ≅ RⁿF(M)` is the natural one

`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso` identifies the degree-`n` cohomology of
a right derived functor applied to an object placed in degree `0` with the classical right
derived functor, object by object, from the chosen injective resolution.
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` is a natural isomorphism
between the same two functors, read off the same chosen resolution. This file proves that the
former is the component of the latter, so that the object-level comparison is natural.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

universe v u vB uB wD wE

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wD} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wE} B]
  (F : A ⥤ B) [F.Additive]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

/-- Three isomorphisms followed by their inverses in the reverse order compose to the identity. -/
private lemma comp_three_inv {C : Type*} [Category* C] {X Y Z W : C} (a : X ≅ Y) (b : Y ≅ Z)
    (c : Z ≅ W) : (a.hom ≫ b.hom ≫ c.hom) ≫ c.inv ≫ b.inv ≫ a.inv = 𝟙 X := by
  simp

/-- Reassociating a four-fold composite and rewriting its last two factors. -/
private lemma comp_three_comp_of_eq {C : Type*} [Category* C] {X Y Z W V V' : C} (x : X ⟶ Y)
    (y : Y ⟶ Z) (z : Z ⟶ W) (w : W ⟶ V) (v : Z ⟶ V') (t : V' ⟶ V) (h : z ≫ w = v ≫ t) :
    (x ≫ y ≫ z) ≫ w = x ≫ y ≫ v ≫ t := by
  simp only [Category.assoc, h]

/-- A composite through two isomorphisms and back, with a retraction in the middle. -/
private lemma eq_comp_iso_iso_comp {C : Type*} [Category* C] {X Y Z W V : C} (a : X ⟶ Y)
    (b : Y ≅ Z) (c : W ≅ Z) (d : Y ⟶ X) (e : X ⟶ V) (h : a ≫ d = 𝟙 X) :
    e = (a ≫ b.hom ≫ c.inv) ≫ c.hom ≫ b.inv ≫ d ≫ e := by
  simp [reassoc_of% h]

/-- Two functors applied in succession to an identity morphism give an identity. -/
private lemma map_map_eq_id {C D E : Type*} [Category* C] [Category* D] [Category* E] (G : C ⥤ D)
    (H : D ⥤ E) {X : C} (f : X ⟶ X) (hf : f = 𝟙 X) : H.map (G.map f) = 𝟙 _ := by
  simp [hf]

/-- An equality of composites assembled from equalities of their factors. -/
private lemma tail_assemble {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (o : X₀ ⟶ X₀) (q : X₀ ⟶ X₁) (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (x : X₃ ⟶ X₆) (m₁ m : X₂ ⟶ X₄)
    (e : X₄ ≅ X₅) (i : X₆ ≅ X₅) (j : X₅ ⟶ X₆) (h : X₀ ⟶ X₃) (ho : o = 𝟙 X₀)
    (hh : h = q ≫ f ≫ g) (ht : g ≫ x = m ≫ e.hom ≫ j) (hm : m₁ = m) (hi : i.inv = j) :
    o ≫ q ≫ f ≫ m₁ ≫ (e ≪≫ i.symm).hom = h ≫ x := by
  subst ho hh hm hi
  simp [ht]

/-- The component of a whiskered composite followed by a third isomorphism. -/
private lemma isoWhiskerLeft_trans_trans_hom_app {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (G : C ⥤ D) {H₁ H₂ H₃ : D ⥤ E} {K : C ⥤ E} (I₁ : H₁ ≅ H₂) (I₂ : H₂ ≅ H₃)
    (I₃ : G ⋙ H₃ ≅ K) (M : C) :
    (G.isoWhiskerLeft (I₁ ≪≫ I₂) ≪≫ I₃).hom.app M =
      I₁.hom.app (G.obj M) ≫ I₂.hom.app (G.obj M) ≫ I₃.hom.app M := by
  simp

/-- A composite ending in a composite of two isomorphisms. -/
private lemma comp_comp_trans_hom {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ≅ X₃) (d : X₃ ≅ X₄) (r : X₁ ⟶ X₄) (hr : r = b ≫ c.hom ≫ d.hom) :
    a ≫ b ≫ (c ≪≫ d).hom = a ≫ r := by
  simp [hr]

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- The component at `M` of the inverse of `Stacks.DerivedIndexing.rightDerivedIsoRes F n` is the
inverse of `Stacks.DerivedIndexing.extendMapHomologyIso F I n`, where `I` is the chosen injective
resolution of `M`. -/
theorem rightDerivedIsoRes_inv_app_eq (M : A) (n : ℕ) :
    (Stacks.DerivedIndexing.rightDerivedIsoRes F n).inv.app M =
      (Stacks.DerivedIndexing.extendMapHomologyIso F (injectiveResolution M).cocomplex n).inv := by
  rw [← Iso.app_inv]
  exact congrArg Iso.inv (Iso.ext (Stacks.DerivedIndexing.rightDerivedIsoRes_hom_app_eq F M n))

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] in
/-- The two comparisons of `F` applied degreewise to an extension by zero with the extension by
zero of `F` applied degreewise agree. -/
theorem mapHomologicalComplexExtendNatIso_hom_eq (K : CochainComplex A ℕ) :
    (mapHomologicalComplexExtendNatIso F K).hom =
      (Stacks.DerivedIndexing.mapExtendIso F ComplexShape.embeddingUpNat K).inv := by
  ext i
  by_cases hi : 0 ≤ i
  · have h : ComplexShape.embeddingUpNat.f i.toNat = i := by
      simpa using Int.toNat_of_nonneg hi
    rw [Stacks.DerivedIndexing.mapExtendIso_inv_f_eq F ComplexShape.embeddingUpNat K h]
    simp [mapHomologicalComplexExtendNatIso, hi]
  · exact (F.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat i
      (by intro n; simp; omega))).eq_of_src _ _

omit [EnoughInjectives A] in
/-- The component at `M` of `DerivedCategory.singleFunctorIsoCompQh A 0` is the inverse of
`DerivedCategory.quotientCompQhIso A` at the complex `M` placed in degree `0`. -/
theorem singleFunctorIsoCompQh_hom_app (M : A) :
    (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app M =
      (DerivedCategory.quotientCompQhIso A).inv.app ((CochainComplex.singleFunctor A 0).obj M) := by
  simp only [DerivedCategory.singleFunctorIsoCompQh, DerivedCategory.singleFunctorsPostcompQhIso,
    SingleFunctors.postcompIsoOfIso, SingleFunctors.postcompPostcompIso, SingleFunctors.isoMk,
    Functor.mapIso_hom]
  exact Category.comp_id _

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] in
/-- **`extendMapHomologyIso` at a complex**, written on complexes: the homotopy-category
comparison, `extendHomologyIso` inverted, the homology of the comparison of the two extensions,
and the homotopy-category comparison inverted. -/
theorem extendMapHomologyIso_hom_eq (K : CochainComplex A ℕ) (n : ℕ) :
    (Stacks.DerivedIndexing.extendMapHomologyIso F K n).hom =
      (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendHomologyIso
            ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).inv ≫
        (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)).map
          (Stacks.DerivedIndexing.mapExtendIso F ComplexShape.embeddingUpNat K).hom ≫
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (n : ℤ)).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (K.extend ComplexShape.embeddingUpNat)) := by
  let E := Stacks.DerivedIndexing.extendHomotopyHomologyNatIso (A := B)
    ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))
  let Z := (F.mapHomotopyCategory (ComplexShape.up ℕ)).obj
    ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj K)
  let FK := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let φ := (Stacks.DerivedIndexing.mapExtendIso F ComplexShape.embeddingUpNat K).hom
  let Hh := HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)
  let HhF := HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (n : ℤ)
  let HhFN := HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) n
  let eh := FK.extendHomologyIso ComplexShape.embeddingUpNat
    (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))
  have hE : E.hom.app Z = HhF.hom.app (FK.extend ComplexShape.embeddingUpNat) ≫ eh.hom ≫
      HhFN.inv.app FK :=
    Stacks.DerivedIndexing.extendHomotopyHomologyNatIso_hom_app_quotient
      ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ)) FK
  have hEinv : E.inv.app Z = HhFN.hom.app FK ≫ eh.inv ≫
      HhF.inv.app (FK.extend ComplexShape.embeddingUpNat) := by
    refine Iso.inv_ext (f := E.app Z) ((congrArg (· ≫ _) hE).trans ?_)
    exact comp_three_inv (HhF.app (FK.extend ComplexShape.embeddingUpNat)) eh (HhFN.app FK).symm
  refine (Stacks.DerivedIndexing.extendMapHomologyIso_hom F K n).trans
    ((congrArg (· ≫ Hh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map φ))
      hEinv).trans ?_)
  exact comp_three_comp_of_eq _ _ _ _ _ _ (HhF.inv.naturality φ).symm

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] in
/-- `extendMapHomologyIso`, inverted, after the homotopy-category comparison. -/
theorem homologyFunctorFactors_inv_comp_extendMapHomologyIso_inv (K : CochainComplex A ℕ)
    (n : ℕ) :
    (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (n : ℤ)).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (K.extend ComplexShape.embeddingUpNat)) ≫
        (Stacks.DerivedIndexing.extendMapHomologyIso F K n).inv =
      (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)).map
          (Stacks.DerivedIndexing.mapExtendIso F ComplexShape.embeddingUpNat K).inv ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendHomologyIso
            ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).hom ≫
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) n).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) := by
  refine (Iso.comp_inv_eq (α := Stacks.DerivedIndexing.extendMapHomologyIso F K n)).2 ?_
  rw [extendMapHomologyIso_hom_eq]
  refine eq_comp_iso_iso_comp _ _ ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ)
    n).app ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) _ _ ?_
  rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

omit [HasDerivedCategory A] in
/-- The comparisons after the unit of the derived functor, in the object-level construction and
in the natural one, agree. -/
theorem homologyTotalRightDerivedSingleIso_tail (M : A) (n : ℕ) :
    (DerivedCategory.homologyFunctor B (n : ℤ)).map (DerivedCategory.Qh.map
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
          (injectiveResolution M).cochainComplex)) ≫
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
        ((DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (injectiveResolution M).cochainComplex)) ≫
      (DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (injectiveResolution M).cochainComplex) ≫
      ((HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)).mapIso
          (mapHomologicalComplexExtendNatIso F (injectiveResolution M).cocomplex)).hom ≫
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution M).cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (by rfl) ≪≫
        ((injectiveResolution M).isoRightDerivedObj F n).symm).hom =
    (DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (Stacks.DerivedIndexing.resH.obj M)) ≫
      (Stacks.DerivedIndexing.extendMapHomologyIso F (injectiveResolution M).cocomplex n).inv := by
  have h0 : (DerivedCategory.homologyFunctor B (n : ℤ)).map (DerivedCategory.Qh.map
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
        (injectiveResolution M).cochainComplex)) = 𝟙 _ :=
    map_map_eq_id _ _ _ rfl
  exact tail_assemble _ _ _ _ _ _ _ _ _ _ _ h0
    (DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj (C := B)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (injectiveResolution M).cochainComplex)
      (n : ℤ))
    (homologyFunctorFactors_inv_comp_extendMapHomologyIso_inv F (injectiveResolution M).cocomplex n)
    (congrArg (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)).map
      (mapHomologicalComplexExtendNatIso_hom_eq F (injectiveResolution M).cocomplex))
    (Stacks.DerivedIndexing.isoRightDerivedObj_injectiveResolution_inv F M n)

/-- The isomorphism `homologyTotalRightDerivedSingleIso F RF α hres M n` is the component at `M`
of the natural isomorphism `singleCompDerivedCompHomologyIsoRightDerived F RF α hres n`. -/
theorem homologyTotalRightDerivedSingleIso_eq (M : A) (n : ℕ) :
    homologyTotalRightDerivedSingleIso F RF α hres M n =
      (singleCompDerivedCompHomologyIsoRightDerived F RF α hres n).app M := by
  have : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
      (injectiveResolution M).cochainComplex)) := isIso_unit_app_resH_obj F RF α hres M
  ext
  rw [Iso.app_hom, singleCompDerivedCompHomologyIsoRightDerived_hom_app,
    rightDerivedIsoRes_inv_app_eq]
  unfold homologyTotalRightDerivedSingleIso
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom, asIso_inv, Iso.app_hom]
  have h₁ : (DerivedCategory.singleFunctorIsoCompQ A 0).hom.app M ≫
        DerivedCategory.Q.map (injectiveResolution M).ι' ≫
          ((DerivedCategory.quotientCompQhIso A).app (injectiveResolution M).cochainComplex).inv =
      singleIsoResCompQh.hom.app M := by
    have hq := (DerivedCategory.quotientCompQhIso A).inv.naturality (injectiveResolution M).ι'
    dsimp only [Functor.comp_map] at hq
    have hs : (singleIsoResCompQh (A := A)).hom.app M =
        (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app M ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            (injectiveResolution M).ι') := rfl
    rw [hs, singleFunctorIsoCompQh_hom_app]
    exact (Category.id_comp _).trans hq
  have h₂ : (resCompUnitIso F RF α hres).inv.app M =
      inv (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (injectiveResolution M).cochainComplex)) := by
    simp only [Functor.comp_obj, resCompUnitIso, asIso_inv, NatIso.isIso_inv_app,
      Functor.whiskerLeft_app]
    rfl
  rw [h₁, h₂]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun t => _ ≫ _ ≫ t) (homologyTotalRightDerivedSingleIso_tail F M n)

/-- The isomorphism `homologyTotalRightDerivedSingleShiftIso F RF α hres M a m n hn` is the
component at `M` of the natural isomorphism
`singleShiftCompDerivedCompHomologyIsoRightDerived F RF α hres a m n hn`. -/
theorem homologyTotalRightDerivedSingleShiftIso_eq (M : A) (a m : ℤ) (n : ℕ) (hn : m - a = n) :
    letI := Functor.IsRightDerivedFunctor.commShift RF α
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
    homologyTotalRightDerivedSingleShiftIso F RF α hres M a m n hn =
      (singleShiftCompDerivedCompHomologyIsoRightDerived F RF α hres a m n hn).app M := by
  let := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  unfold homologyTotalRightDerivedSingleShiftIso
  rw [homologyTotalRightDerivedSingleIso_eq]
  ext
  dsimp only [Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
    singleShiftCompDerivedCompHomologyIsoRightDerived, NatIso.trans_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.comp_map]
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  exact comp_comp_trans_hom _ _ _ _ _ (isoWhiskerLeft_trans_trans_hom_app _ _ _ _ M)

end Stacks.DerivedFunctor
