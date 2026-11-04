module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingDerivedEquivalence

/-!
# Total derived functors along exact equivalences of abelian categories

Let `e : A₁ ≌ A₂` be an equivalence of abelian categories, so that `e` induces an equivalence
`K(A₁) ≌ K(A₂)` of homotopy categories and an equivalence `D(A₁) ≌ D(A₂)` of derived categories.
Let `F₁ : K(A₁) ⥤ T₁` and `F₂ : K(A₂) ⥤ T₂` be functors having total left derived functors
`LF₁`, `LF₂` along the quasi-isomorphisms, and let `κ : T₁ ⥤ T₂` be a right adjoint with
`F₁ ⋙ κ ≅ e ⋙ F₂`.  Then `LF₁ ⋙ κ ≅ e ⋙ LF₂`: both sides are left derived functors of
`F₁ ⋙ κ`.  Dually for total right derived functors, with `κ` a left adjoint.

## Main definitions

* `CategoryTheory.Functor.totalLeftDerivedCompIsoOfEquivalence`: `LF₁ ⋙ κ ≅ e ⋙ LF₂`.
* `CategoryTheory.Functor.totalRightDerivedCompIsoOfEquivalence`: `RF₁ ⋙ κ ≅ e ⋙ RF₂`.

## Main results

* `CategoryTheory.Functor.isEquivalence_mapHomotopyCategory`: an additive equivalence induces an
  equivalence of homotopy categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A₁ A₂ : Type*} [Category* A₁] [Category* A₂] [Abelian A₁] [Abelian A₂]

/-- **An additive equivalence induces an equivalence of homotopy categories.** -/
theorem isEquivalence_mapHomotopyCategory {ι : Type*} (c : ComplexShape ι) (G : A₁ ⥤ A₂)
    [G.Additive] [G.IsEquivalence] : (G.mapHomotopyCategory c).IsEquivalence where
  essSurj := ⟨fun K => ⟨⟨(G.asEquivalence.inverse.mapHomologicalComplex c).obj K.as⟩,
    ⟨(HomotopyCategory.quotient A₂ c).mapIso
      ((G.asEquivalence.mapHomologicalComplex c).counitIso.app K.as)⟩⟩⟩

variable [HasDerivedCategory A₁] [HasDerivedCategory A₂] (G : A₁ ⥤ A₂) [hG : G.Additive]
  [G.IsEquivalence]

/-- The localizer morphism of the quasi-isomorphisms of homotopy categories induced by an
additive equivalence. -/
abbrev mapHomotopyCategoryQuasiIsoLocalizerMorphism :
    LocalizerMorphism (HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso A₂ (ComplexShape.up ℤ)) where
  functor := G.mapHomotopyCategory (ComplexShape.up ℤ)
  map K L f hf := by
    obtain ⟨g, rfl⟩ :=
      (HomotopyCategory.quotient A₁ (ComplexShape.up ℤ)).map_surjective (X := K.as) (Y := L.as) f
    change HomotopyCategory.quasiIso A₂ (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient A₂ (ComplexShape.up ℤ)).map
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map g))
    refine (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ?_
    have : QuasiIso g := (HomotopyCategory.quotient_map_mem_quasiIso_iff g).1 hf
    exact HomologicalComplex.quasiIso_map_of_preservesHomology _ _

/-- The functor of homotopy categories induced by an additive equivalence is an equivalence. -/
instance : (G.mapHomotopyCategoryQuasiIsoLocalizerMorphism).functor.IsEquivalence :=
  isEquivalence_mapHomotopyCategory _ G

/-- The functor of derived categories induced by an additive equivalence is an equivalence. -/
instance : G.mapDerivedCategory.IsEquivalence :=
  haveI : G.asEquivalence.functor.Additive := ‹G.Additive›
  Stacks.DerivedCategory.mapDerivedCategory_isEquivalence G.asEquivalence

/-- The localizer morphism of quasi-isomorphisms induced by an additive equivalence is a
localized equivalence. -/
instance : (G.mapHomotopyCategoryQuasiIsoLocalizerMorphism).IsLocalizedEquivalence :=
  have : CatCommSq (G.mapHomotopyCategoryQuasiIsoLocalizerMorphism).functor DerivedCategory.Qh
      DerivedCategory.Qh G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactorsh.symm⟩
  LocalizerMorphism.IsLocalizedEquivalence.mk' _ DerivedCategory.Qh DerivedCategory.Qh
    G.mapDerivedCategory

variable {T₁ T₂ : Type*} [Category* T₁] [Category* T₂]
  (F₁ : HomotopyCategory A₁ (ComplexShape.up ℤ) ⥤ T₁)
  (F₂ : HomotopyCategory A₂ (ComplexShape.up ℤ) ⥤ T₂) (κ : T₁ ⥤ T₂)
  (τ : F₁ ⋙ κ ≅ G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ F₂)

section Left

variable [F₁.HasLeftDerivedFunctor (HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ))]
  [F₂.HasLeftDerivedFunctor (HomotopyCategory.quasiIso A₂ (ComplexShape.up ℤ))]
  [κ.IsRightAdjoint]

/-- **Total left derived functors along an additive equivalence**: if `F₁ ⋙ κ ≅ G ⋙ F₂` for
a right adjoint `κ` and an additive equivalence `G`, then `LF₁ ⋙ κ ≅ G ⋙ LF₂`. -/
def totalLeftDerivedCompIsoOfEquivalence :
    F₁.totalLeftDerived DerivedCategory.Qh (HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ)) ⋙
        κ ≅
      G.mapDerivedCategory ⋙
        F₂.totalLeftDerived DerivedCategory.Qh (HomotopyCategory.quasiIso A₂ (ComplexShape.up ℤ)) :=
  let W₁ := HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ)
  let W₂ := HomotopyCategory.quasiIso A₂ (ComplexShape.up ℤ)
  let Φ := G.mapHomotopyCategoryQuasiIsoLocalizerMorphism
  let iso : Φ.functor ⋙ DerivedCategory.Qh ≅ DerivedCategory.Qh ⋙ G.mapDerivedCategory :=
    G.mapDerivedCategoryFactorsh.symm
  let α₂ := F₂.totalLeftDerivedCounit DerivedCategory.Qh W₂
  let α : DerivedCategory.Qh ⋙ (G.mapDerivedCategory ⋙ F₂.totalLeftDerived DerivedCategory.Qh W₂)
      ⟶ Φ.functor ⋙ F₂ :=
    whiskerLeft DerivedCategory.Qh (Iso.refl _).inv ≫ (associator _ _ _).inv ≫
      whiskerRight iso.inv _ ≫ (associator _ _ _).hom ≫ whiskerLeft Φ.functor α₂ ≫
        (Iso.refl _).hom
  have : (G.mapDerivedCategory ⋙ F₂.totalLeftDerived DerivedCategory.Qh W₂).IsLeftDerivedFunctor
      α W₁ :=
    (Φ.isLeftDerivedFunctor_iff_precomp DerivedCategory.Qh DerivedCategory.Qh
      G.mapDerivedCategory iso α α₂ (Iso.refl _) (Iso.refl _) rfl).1 inferInstance
  leftDerivedNatIso _ _
    ((associator _ _ _).inv ≫ whiskerRight (F₁.totalLeftDerivedCounit DerivedCategory.Qh W₁) κ)
    α W₁ τ

end Left

section Right

variable [F₁.HasRightDerivedFunctor (HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ))]
  [F₂.HasRightDerivedFunctor (HomotopyCategory.quasiIso A₂ (ComplexShape.up ℤ))]
  [κ.IsLeftAdjoint]

/-- **Total right derived functors along an additive equivalence**: if `F₁ ⋙ κ ≅ G ⋙ F₂` for
a left adjoint `κ` and an additive equivalence `G`, then `RF₁ ⋙ κ ≅ G ⋙ RF₂`. -/
def totalRightDerivedCompIsoOfEquivalence :
    F₁.totalRightDerived DerivedCategory.Qh (HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ)) ⋙
        κ ≅
      G.mapDerivedCategory ⋙
        F₂.totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso A₂ (ComplexShape.up ℤ)) :=
  let W₁ := HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ)
  let W₂ := HomotopyCategory.quasiIso A₂ (ComplexShape.up ℤ)
  let Φ := G.mapHomotopyCategoryQuasiIsoLocalizerMorphism
  let iso : Φ.functor ⋙ DerivedCategory.Qh ≅ DerivedCategory.Qh ⋙ G.mapDerivedCategory :=
    G.mapDerivedCategoryFactorsh.symm
  let α₂ := F₂.totalRightDerivedUnit DerivedCategory.Qh W₂
  let α : Φ.functor ⋙ F₂ ⟶
      DerivedCategory.Qh ⋙ (G.mapDerivedCategory ⋙ F₂.totalRightDerived DerivedCategory.Qh W₂) :=
    (Iso.refl _).inv ≫ whiskerLeft Φ.functor α₂ ≫ (associator _ _ _).inv ≫
      whiskerRight iso.hom _ ≫ (associator _ _ _).hom ≫
        whiskerLeft DerivedCategory.Qh (Iso.refl _).hom
  have : (G.mapDerivedCategory ⋙ F₂.totalRightDerived DerivedCategory.Qh W₂).IsRightDerivedFunctor
      α W₁ :=
    (Φ.isRightDerivedFunctor_iff_precomp DerivedCategory.Qh DerivedCategory.Qh
      G.mapDerivedCategory iso α α₂ (Iso.refl _) (Iso.refl _) rfl).1 inferInstance
  rightDerivedNatIso _ _
    (whiskerRight (F₁.totalRightDerivedUnit DerivedCategory.Qh W₁) κ ≫ (associator _ _ _).hom)
    α W₁ τ

end Right

section Underived

variable {B₁ B₂ : Type*} [Category* B₁] [Category* B₂] [Abelian B₁] [Abelian B₂]
  [HasDerivedCategory B₁] [HasDerivedCategory B₂]
  (P₁ : A₁ ⥤ B₁) (P₂ : A₂ ⥤ B₂) [hP₁ : P₁.Additive] [hP₂ : P₂.Additive]
  (H : B₁ ⥤ B₂) [hH : H.Additive] [hHl : PreservesFiniteLimits H] [hHc : PreservesFiniteColimits H]
  (τm : P₁ ⋙ H ≅ G ⋙ P₂)

/-- An isomorphism `P₁ ⋙ H ≅ G ⋙ P₂` of additive functors of abelian categories, with `H` exact,
induces `(P₁ ⋙ Qh) ⋙ H ≅ G ⋙ (P₂ ⋙ Qh)` on homotopy categories. -/
def mapHomotopyCategoryQhCompIso :
    (P₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ H.mapDerivedCategory ≅
      G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (P₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
  associator _ _ _ ≪≫ isoWhiskerLeft _ H.mapDerivedCategoryFactorsh ≪≫
    (associator _ _ _).symm ≪≫
    isoWhiskerRight (mapHomotopyCategoryCompIso (Iso.refl (P₁ ⋙ H)) (ComplexShape.up ℤ) ≪≫
      { hom := NatTrans.mapHomotopyCategory τm.hom (ComplexShape.up ℤ)
        inv := NatTrans.mapHomotopyCategory τm.inv (ComplexShape.up ℤ)
        hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
        inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp } ≪≫
      (mapHomotopyCategoryCompIso (Iso.refl (G ⋙ P₂)) (ComplexShape.up ℤ)).symm) _ ≪≫
    associator _ _ _

variable [hHe : H.IsEquivalence]

/-- **Total left derived functors of underived functors along additive equivalences**: if
`P₁ ⋙ H ≅ G ⋙ P₂` with `G`, `H` additive equivalences, then `LP₁ ⋙ H ≅ G ⋙ LP₂`. -/
def totalLeftDerivedMapHomotopyCompIsoOfEquivalence
    [hL₁ : (P₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ))]
    [hL₂ : (P₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A₂ (ComplexShape.up ℤ))] :
    (P₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerived
        DerivedCategory.Qh (HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ)) ⋙
        H.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙
        (P₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerived
          DerivedCategory.Qh (HomotopyCategory.quasiIso A₂ (ComplexShape.up ℤ)) :=
  totalLeftDerivedCompIsoOfEquivalence G _ _ H.mapDerivedCategory
    (mapHomotopyCategoryQhCompIso G P₁ P₂ H τm)

/-- **Total right derived functors of underived functors along additive equivalences**: if
`P₁ ⋙ H ≅ G ⋙ P₂` with `G`, `H` additive equivalences, then `RP₁ ⋙ H ≅ G ⋙ RP₂`. -/
def totalRightDerivedMapHomotopyCompIsoOfEquivalence
    [(P₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ))]
    [(P₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A₂ (ComplexShape.up ℤ))] :
    (P₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
        DerivedCategory.Qh (HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ)) ⋙
        H.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙
        (P₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
          DerivedCategory.Qh (HomotopyCategory.quasiIso A₂ (ComplexShape.up ℤ)) :=
  totalRightDerivedCompIsoOfEquivalence G _ _ H.mapDerivedCategory
    (mapHomotopyCategoryQhCompIso G P₁ P₂ H τm)

end Underived

end CategoryTheory.Functor

end
