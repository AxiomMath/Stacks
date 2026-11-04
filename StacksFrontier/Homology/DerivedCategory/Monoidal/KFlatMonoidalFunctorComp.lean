module

public import StacksFrontier.CategoryTheory.Monoidal.NatTransIsMonoidal
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatMonoidalFunctor
public import StacksFrontier.Homology.MapHomologicalComplexMonoidalComp

/-!
# Composition isomorphisms of derived functors computed on K-flat complexes are monoidal

Let `F : A₁ ⥤ A₂`, `G : A₂ ⥤ A₃`, `H : A₁ ⥤ A₃` be additive monoidal functors between monoidal
abelian categories as in `CochainComplex.KFlatMonoidal.derivedFunctorMonoidal`, preserving
K-flatness, and let `γ : F ⋙ G ≅ H` be a monoidal isomorphism. Then the induced isomorphisms on
homotopy categories and on K-flat objects are monoidal, and a transformation `Φ_F ⋙ Φ_G ⟶ Φ_H`
of functors on derived categories computed on K-flat objects by `F`, `G`, `H`, which on K-flat
objects is induced by `γ`, is monoidal for the structures `derivedFunctorMonoidal`.

## Main results

* `CategoryTheory.ObjectProperty.isMonoidal_lift_comp` — a transformation of lifts to full
  monoidal subcategories is monoidal when the underlying one is.
* `CochainComplex.KFlatMonoidal.isMonoidal_mapHomotopyCategoryCompIso_hom`
* `CochainComplex.KFlatMonoidal.kFlatLiftCompIso` and its monoidality
* `CochainComplex.KFlatMonoidal.isMonoidal_derivedFunctorMonoidal_comp`
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatBifunctor

namespace CategoryTheory.ObjectProperty

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C₃]
  (P₁ : ObjectProperty C₁) (P₂ : ObjectProperty C₂) (P₃ : ObjectProperty C₃)
  [P₁.IsMonoidal] [P₂.IsMonoidal] [P₃.IsMonoidal]

omit [MonoidalCategory C₃] [P₁.IsMonoidal] in
/-- The unit of the lift of a monoidal functor to a full monoidal subcategory is that of the
functor. -/
lemma lift_ε_hom (F : C₁ ⥤ C₂) [F.Monoidal] (h : ∀ X, P₂ (F.obj X)) :
    (Functor.LaxMonoidal.ε (P₂.lift F h)).hom = Functor.LaxMonoidal.ε F :=
  rfl

/-- **A transformation between lifts to full monoidal subcategories is monoidal when the
underlying transformation is.** -/
theorem isMonoidal_lift_comp {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {H : C₁ ⥤ C₃} [F.Monoidal]
    [G.Monoidal] [H.Monoidal] (hF : ∀ X : P₁.FullSubcategory, P₂ (F.obj X.obj))
    (hG : ∀ X : P₂.FullSubcategory, P₃ (G.obj X.obj))
    (hH : ∀ X : P₁.FullSubcategory, P₃ (H.obj X.obj)) (τ : F ⋙ G ⟶ H) [NatTrans.IsMonoidal τ]
    (σ : P₂.lift (P₁.ι ⋙ F) hF ⋙ P₃.lift (P₂.ι ⋙ G) hG ⟶ P₃.lift (P₁.ι ⋙ H) hH)
    (hσ : ∀ X, (σ.app X).hom = τ.app X.obj) :
    NatTrans.IsMonoidal σ where
  unit := by
    apply ObjectProperty.hom_ext
    have h := NatTrans.IsMonoidal.unit (τ := τ)
    simp only [Functor.LaxMonoidal.comp_ε, Functor.comp_obj, Category.assoc] at h
    simp only [Functor.LaxMonoidal.comp_ε, FullSubcategory.comp_hom, hσ, lift_ε_hom,
      lift_map, homMk_hom, ι_ε, Functor.map_id, Category.comp_id, Category.assoc, ι_map,
      Functor.comp_map]
    exact h
  tensor X Y := by
    apply ObjectProperty.hom_ext
    have h := NatTrans.IsMonoidal.tensor (τ := τ) X.obj Y.obj
    simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj, Category.assoc] at h
    have ht : (σ.app X ⊗ₘ σ.app Y).hom = (σ.app X).hom ⊗ₘ (σ.app Y).hom := rfl
    simp only [Functor.LaxMonoidal.comp_μ, FullSubcategory.comp_hom, hσ, lift_mu_hom,
      lift_map, homMk_hom, ι_μ, Functor.map_id, Category.comp_id, Category.assoc, ι_map,
      Functor.comp_map, ht]
    exact h

end CategoryTheory.ObjectProperty

namespace CochainComplex.KFlatMonoidal

/-- A composite with identities, one of them the image of an identity. Applied by unification
where the identities are identities only after unfolding. -/
private lemma comp_id_eq_map_id_comp {C D : Type*} [Category C] [Category D] (Φ : C ⥤ D)
    {X : C} {Z : D} {u w : Φ.obj X ⟶ Z} (h : u = w) :
    u ≫ 𝟙 Z = Φ.map (𝟙 X) ≫ 𝟙 (Φ.obj X) ≫ w := by
  subst h
  simp

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

attribute [local instance] homotopyMonoidal

variable
  {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁] [MonoidalCategory A₁]
  [(curriedTensor A₁).Additive] [∀ X : A₁, ((curriedTensor A₁).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ A₁, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A₁, PreservesColimit (Functor.empty.{0} A₁) ((curriedTensor A₁).obj X₁)]
  [∀ X₂ : A₁, PreservesColimit (Functor.empty.{0} A₁) ((curriedTensor A₁).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A₁, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A₁, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A₁, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Abelian A₂] [MonoidalCategory A₂]
  [(curriedTensor A₂).Additive] [∀ X : A₂, ((curriedTensor A₂).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ A₂, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A₂, PreservesColimit (Functor.empty.{0} A₂) ((curriedTensor A₂).obj X₁)]
  [∀ X₂ : A₂, PreservesColimit (Functor.empty.{0} A₂) ((curriedTensor A₂).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A₂, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A₂, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A₂, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {A₃ : Type u₃} [Category.{v₃} A₃] [Abelian A₃] [MonoidalCategory A₃]
  [(curriedTensor A₃).Additive] [∀ X : A₃, ((curriedTensor A₃).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ A₃, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A₃, PreservesColimit (Functor.empty.{0} A₃) ((curriedTensor A₃).obj X₁)]
  [∀ X₂ : A₃, PreservesColimit (Functor.empty.{0} A₃) ((curriedTensor A₃).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A₃, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A₃, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A₃, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {F : A₁ ⥤ A₂} {G : A₂ ⥤ A₃} {H : A₁ ⥤ A₃} [F.Additive] [G.Additive] [H.Additive]
  [F.Monoidal] [G.Monoidal] [H.Monoidal]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n})) F]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n})) G]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n})) H]

/-- **The composition isomorphism on homotopy categories induced by a monoidal isomorphism
`F ⋙ G ≅ H` is monoidal**, for the structures `mapHomotopyCategoryMonoidal`. -/
theorem isMonoidal_mapHomotopyCategoryCompIso_hom (γ : F ⋙ G ≅ H) [NatTrans.IsMonoidal γ.hom] :
    letI := mapHomotopyCategoryMonoidal F
    letI := mapHomotopyCategoryMonoidal G
    letI := mapHomotopyCategoryMonoidal H
    NatTrans.IsMonoidal (Functor.mapHomotopyCategoryCompIso γ (ComplexShape.up ℤ)).hom := by
  let := mapHomotopyCategoryLifting F
  let := mapHomotopyCategoryLifting G
  let := mapHomotopyCategoryLifting H
  let := mapHomotopyCategoryMonoidal F
  let := mapHomotopyCategoryMonoidal G
  let := mapHomotopyCategoryMonoidal H
  have := Localization.essSurj
    (Localization.Monoidal.toMonoidalCategory (HomotopyCategory.quotient A₁ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A₁ (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit A₁)))
    (HomologicalComplex.homotopyEquivalences A₁ (ComplexShape.up ℤ))
  let : F.mapHomotopyCategoryLocalized.Monoidal := mapHomotopyCategoryMonoidal F
  let : G.mapHomotopyCategoryLocalized.Monoidal := mapHomotopyCategoryMonoidal G
  let : H.mapHomotopyCategoryLocalized.Monoidal := mapHomotopyCategoryMonoidal H
  exact NatTrans.IsMonoidal.of_comp_lifting (Localization.Monoidal.toMonoidalCategory
      (HomotopyCategory.quotient A₁ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A₁ (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit A₁)))
    (Localization.Lifting.iso (Localization.Monoidal.toMonoidalCategory
        (HomotopyCategory.quotient A₁ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A₁ (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit A₁)))
      (HomologicalComplex.homotopyEquivalences A₁ (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ (Localization.Monoidal.toMonoidalCategory
          (HomotopyCategory.quotient A₂ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A₂ (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit A₂))))
      F.mapHomotopyCategoryLocalized)
    (Localization.Lifting.iso (Localization.Monoidal.toMonoidalCategory
        (HomotopyCategory.quotient A₂ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A₂ (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit A₂)))
      (HomologicalComplex.homotopyEquivalences A₂ (ComplexShape.up ℤ))
      (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ (Localization.Monoidal.toMonoidalCategory
          (HomotopyCategory.quotient A₃ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A₃ (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit A₃))))
      G.mapHomotopyCategoryLocalized)
    (Localization.Lifting.iso (Localization.Monoidal.toMonoidalCategory
        (HomotopyCategory.quotient A₁ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A₁ (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit A₁)))
      (HomologicalComplex.homotopyEquivalences A₁ (ComplexShape.up ℤ))
      (H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ (Localization.Monoidal.toMonoidalCategory
          (HomotopyCategory.quotient A₃ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A₃ (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit A₃))))
      H.mapHomotopyCategoryLocalized)
    (Functor.mapHomologicalComplexCompIso γ (ComplexShape.up ℤ)).hom
    (Functor.mapHomotopyCategoryCompIso γ (ComplexShape.up ℤ)).hom (fun K ↦ by
      exact comp_id_eq_map_id_comp G.mapHomotopyCategoryLocalized rfl)

section KFlat

variable (hF : ∀ K : CochainComplex A₁ ℤ,
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A₁) K →
      _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A₂)
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hG : ∀ K : CochainComplex A₂ ℤ,
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A₂) K →
      _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A₃)
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hH : ∀ K : CochainComplex A₁ ℤ,
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A₁) K →
      _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A₃)
        ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))

/-- The composition isomorphism `kFlatLift F ⋙ kFlatLift G ≅ kFlatLift H` on K-flat objects of
the homotopy categories induced by `γ : F ⋙ G ≅ H`. -/
def kFlatLiftCompIso (γ : F ⋙ G ≅ H) :
    kFlatLift F hF ⋙ kFlatLift G hG ≅ kFlatLift H hH :=
  NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _
      ((Functor.mapHomotopyCategoryCompIso γ (ComplexShape.up ℤ)).app X.obj))
    (fun f ↦ ObjectProperty.hom_ext _
      ((Functor.mapHomotopyCategoryCompIso γ (ComplexShape.up ℤ)).hom.naturality f.hom))

omit [∀ X₁ : A₁, PreservesColimit (Functor.empty.{0} A₁) ((curriedTensor A₁).obj X₁)]
  [∀ X₂ : A₁, PreservesColimit (Functor.empty.{0} A₁) ((curriedTensor A₁).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A₁, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A₁, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A₁, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : A₂, PreservesColimit (Functor.empty.{0} A₂) ((curriedTensor A₂).obj X₁)]
  [∀ X₂ : A₂, PreservesColimit (Functor.empty.{0} A₂) ((curriedTensor A₂).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A₂, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A₂, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A₂, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : A₃, PreservesColimit (Functor.empty.{0} A₃) ((curriedTensor A₃).obj X₁)]
  [∀ X₂ : A₃, PreservesColimit (Functor.empty.{0} A₃) ((curriedTensor A₃).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A₃, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A₃, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A₃, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [F.Monoidal] [G.Monoidal] [H.Monoidal]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n})) F]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n})) G]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n})) H] in
/-- The component of `kFlatLiftCompIso` at a K-flat object `X` is the component of
`Functor.mapHomotopyCategoryCompIso γ` at the underlying object of `X`. -/
@[simp]
lemma kFlatLiftCompIso_hom_app_hom (γ : F ⋙ G ≅ H)
    (X : (kFlatObjects (curriedTensor A₁)).FullSubcategory) :
    ((kFlatLiftCompIso hF hG hH γ).hom.app X).hom =
      (Functor.mapHomotopyCategoryCompIso γ (ComplexShape.up ℤ)).hom.app X.obj :=
  rfl

/-- **The composition isomorphism on K-flat objects is monoidal**, for the structures
`kFlatLiftMonoidal`. -/
theorem isMonoidal_kFlatLiftCompIso_hom (γ : F ⋙ G ≅ H) [NatTrans.IsMonoidal γ.hom] :
    letI := kFlatLiftMonoidal F hF
    letI := kFlatLiftMonoidal G hG
    letI := kFlatLiftMonoidal H hH
    NatTrans.IsMonoidal (kFlatLiftCompIso hF hG hH γ).hom :=
  let := mapHomotopyCategoryMonoidal F
  let := mapHomotopyCategoryMonoidal G
  let := mapHomotopyCategoryMonoidal H
  have := isMonoidal_mapHomotopyCategoryCompIso_hom γ
  ObjectProperty.isMonoidal_lift_comp _ _ _ _ _ _
    (Functor.mapHomotopyCategoryCompIso γ (ComplexShape.up ℤ)).hom _ (fun _ ↦ rfl)

variable [BraidedCategory (CochainComplex A₁ ℤ)] [BraidedCategory (CochainComplex A₂ ℤ)]
  [BraidedCategory (CochainComplex A₃ ℤ)]
  [HasDerivedCategory.{w₁} A₁] [HasDerivedCategory.{w₂} A₂] [HasDerivedCategory.{w₃} A₃]
  (hres₁ : ∀ K : CochainComplex A₁ ℤ, ∃ (P : CochainComplex A₁ ℤ) (f : P ⟶ K),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A₁) P ∧ QuasiIso f)
  (hres₂ : ∀ K : CochainComplex A₂ ℤ, ∃ (P : CochainComplex A₂ ℤ) (f : P ⟶ K),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A₂) P ∧ QuasiIso f)
  (hres₃ : ∀ K : CochainComplex A₃ ℤ, ∃ (P : CochainComplex A₃ ℤ) (f : P ⟶ K),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A₃) P ∧ QuasiIso f)
  (ΦF : DerivedCategory A₁ ⥤ DerivedCategory A₂) (ΦG : DerivedCategory A₂ ⥤ DerivedCategory A₃)
  (ΦH : DerivedCategory A₁ ⥤ DerivedCategory A₃)
  (eF : kFlatQ (curriedTensor A₁) ⋙ ΦF ≅ kFlatLift F hF ⋙ kFlatQ (curriedTensor A₂))
  (eG : kFlatQ (curriedTensor A₂) ⋙ ΦG ≅ kFlatLift G hG ⋙ kFlatQ (curriedTensor A₃))
  (eH : kFlatQ (curriedTensor A₁) ⋙ ΦH ≅ kFlatLift H hH ⋙ kFlatQ (curriedTensor A₃))

/-- **Pseudofunctoriality of `derivedFunctorMonoidal`.** A transformation `c : Φ_F ⋙ Φ_G ⟶ Φ_H`
of functors on derived categories computed on K-flat objects by `F`, `G`, `H`, which on K-flat
objects is the composition isomorphism induced by a monoidal `γ : F ⋙ G ≅ H`, is monoidal for
the structures `derivedFunctorMonoidal`. -/
theorem isMonoidal_derivedFunctorMonoidal_comp (γ : F ⋙ G ≅ H) [NatTrans.IsMonoidal γ.hom]
    (c : ΦF ⋙ ΦG ⟶ ΦH)
    (hc : ∀ X, c.app ((kFlatQ (curriedTensor A₁)).obj X) ≫ eH.hom.app X =
      ΦG.map (eF.hom.app X) ≫ eG.hom.app ((kFlatLift F hF).obj X) ≫
        (kFlatQ (curriedTensor A₃)).map ((kFlatLiftCompIso hF hG hH γ).hom.app X)) :
    letI := derivedMonoidal A₁ hres₁
    letI := derivedMonoidal A₂ hres₂
    letI := derivedMonoidal A₃ hres₃
    letI := derivedFunctorMonoidal F hF hres₁ hres₂ ΦF eF
    letI := derivedFunctorMonoidal G hG hres₂ hres₃ ΦG eG
    letI := derivedFunctorMonoidal H hH hres₁ hres₃ ΦH eH
    NatTrans.IsMonoidal c := by
  let := kFlatQ_isLocalization (curriedTensor A₁) hres₁
  let := kFlatQ_isLocalization (curriedTensor A₂) hres₂
  let := kFlatQ_isLocalization (curriedTensor A₃) hres₃
  let := kFlatLiftMonoidal F hF
  let := kFlatLiftMonoidal G hG
  let := kFlatLiftMonoidal H hH
  let := derivedFunctorLifting F hF hres₁ hres₂ ΦF eF
  let := derivedFunctorLifting G hG hres₂ hres₃ ΦG eG
  let := derivedFunctorLifting H hH hres₁ hres₃ ΦH eH
  let : (derivedFunctorLocalized hres₁ hres₂ ΦF).Monoidal :=
    derivedFunctorMonoidal F hF hres₁ hres₂ ΦF eF
  let : (derivedFunctorLocalized hres₂ hres₃ ΦG).Monoidal :=
    derivedFunctorMonoidal G hG hres₂ hres₃ ΦG eG
  let : (derivedFunctorLocalized hres₁ hres₃ ΦH).Monoidal :=
    derivedFunctorMonoidal H hH hres₁ hres₃ ΦH eH
  have := isMonoidal_kFlatLiftCompIso_hom hF hG hH γ
  have := Localization.essSurj (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A₁))
      (kFlatQuasiIso (curriedTensor A₁)) (Iso.refl ((kFlatQ (curriedTensor A₁)).obj (𝟙_ _))))
    (kFlatQuasiIso (curriedTensor A₁))
  exact NatTrans.IsMonoidal.of_comp_lifting (Localization.Monoidal.toMonoidalCategory (kFlatQ
      (curriedTensor A₁))
      (kFlatQuasiIso (curriedTensor A₁)) (Iso.refl ((kFlatQ (curriedTensor A₁)).obj (𝟙_ _))))
    (Localization.Lifting.iso (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A₁))
      (kFlatQuasiIso (curriedTensor A₁)) (Iso.refl ((kFlatQ (curriedTensor A₁)).obj (𝟙_ _))))
      (kFlatQuasiIso (curriedTensor A₁)) (kFlatLift F hF ⋙
          (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A₂))
      (kFlatQuasiIso (curriedTensor A₂)) (Iso.refl ((kFlatQ (curriedTensor A₂)).obj (𝟙_ _)))))
      (derivedFunctorLocalized hres₁ hres₂ ΦF))
    (Localization.Lifting.iso (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A₂))
      (kFlatQuasiIso (curriedTensor A₂)) (Iso.refl ((kFlatQ (curriedTensor A₂)).obj (𝟙_ _))))
      (kFlatQuasiIso (curriedTensor A₂)) (kFlatLift G hG ⋙
          (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A₃))
      (kFlatQuasiIso (curriedTensor A₃)) (Iso.refl ((kFlatQ (curriedTensor A₃)).obj (𝟙_ _)))))
      (derivedFunctorLocalized hres₂ hres₃ ΦG))
    (Localization.Lifting.iso (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A₁))
      (kFlatQuasiIso (curriedTensor A₁)) (Iso.refl ((kFlatQ (curriedTensor A₁)).obj (𝟙_ _))))
      (kFlatQuasiIso (curriedTensor A₁)) (kFlatLift H hH ⋙
          (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A₃))
      (kFlatQuasiIso (curriedTensor A₃)) (Iso.refl ((kFlatQ (curriedTensor A₃)).obj (𝟙_ _)))))
      (derivedFunctorLocalized hres₁ hres₃ ΦH))
    (kFlatLiftCompIso hF hG hH γ).hom c hc

end KFlat

end CochainComplex.KFlatMonoidal


end
