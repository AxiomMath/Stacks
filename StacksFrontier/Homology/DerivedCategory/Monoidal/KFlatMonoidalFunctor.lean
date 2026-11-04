module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure
public import StacksFrontier.Homology.DerivedCategory.Monoidal.MapDerivedCategoryMonoidal

/-!
# Monoidal functors on derived categories from functors preserving K-flatness

Let `A` and `B` be monoidal abelian categories satisfying the hypotheses of
`CochainComplex.KFlatMonoidal.derivedMonoidal`, so that `K(A)`, `K(B)`, `D(A)` and `D(B)` are
monoidal, and let `F : A ⥤ B` be an additive monoidal functor preserving the coproducts occurring
in total complexes. Then:

* `F.mapHomotopyCategory : K(A) ⥤ K(B)` is monoidal;
* if `F` sends K-flat complexes to K-flat complexes, its restriction to the K-flat objects of the
  homotopy categories is monoidal;
* any functor `Φ : D(A) ⥤ D(B)` which on K-flat objects is computed by `F` — that is, with an
  isomorphism `kFlatQ ⋙ Φ ≅ (F on K-flat objects) ⋙ kFlatQ` — is monoidal.

## Main definitions

* `CochainComplex.KFlatMonoidal.mapHomotopyCategoryMonoidal`: the monoidal structure on
  `F.mapHomotopyCategory`.
* `CochainComplex.KFlatMonoidal.kFlatLift`: the restriction of `F.mapHomotopyCategory` to the
  K-flat objects.
* `CochainComplex.KFlatMonoidal.kFlatLiftMonoidal`: the monoidal structure on `kFlatLift`.
* `CochainComplex.KFlatMonoidal.derivedFunctorMonoidal`: the monoidal structure on a functor
  `Φ : D(A) ⥤ D(B)` computed on K-flat objects by `F`.

## Main results

* `CochainComplex.KFlatMonoidal.derivedFunctorMonoidal_ε`: the unit of
  `derivedFunctorMonoidal`.
* `CochainComplex.KFlatMonoidal.derivedFunctorMonoidal_μ`: the tensorator of
  `derivedFunctorMonoidal` on the images of K-flat objects.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatBifunctor

universe w w' v₁ v₂ u₁ u₂

namespace CochainComplex.KFlatMonoidal

attribute [local instance] homotopyMonoidal

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [MonoidalCategory B]
  [(curriedTensor B).Additive] [∀ X : B, ((curriedTensor B).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ B, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X₁)]
  [∀ X₂ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ B, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (F : A ⥤ B) [F.Additive] [F.Monoidal]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹'
      {n})) F]

/-! ### The homotopy categories -/

/-- The lifting of `F.mapHomotopyCategory` along the homotopy localization given by
`Functor.mapHomotopyCategoryFactors`. -/
@[instance_reducible]
def mapHomotopyCategoryLifting :
    Localization.Lifting
      (Localization.Monoidal.toMonoidalCategory (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
        (Iso.refl (homotopyUnit A)))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Localization.Monoidal.toMonoidalCategory
          (HomotopyCategory.quotient B (ComplexShape.up ℤ))
          (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
          (Iso.refl (homotopyUnit B)))
      F.mapHomotopyCategoryLocalized :=
  ⟨F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)⟩

/-- **`F.mapHomotopyCategory : K(A) ⥤ K(B)` is monoidal**, for
`CochainComplex.KFlatMonoidal.homotopyMonoidal` on both sides: it lifts along the homotopy
localization to the monoidal functor `F.mapHomologicalComplex` followed by the localization. -/
@[instance_reducible]
def mapHomotopyCategoryMonoidal : (F.mapHomotopyCategory (ComplexShape.up ℤ)).Monoidal :=
  letI := mapHomotopyCategoryLifting F
  (Localization.Monoidal.functorMonoidalOfComp
    (Localization.Monoidal.toMonoidalCategory (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit A)))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    F.mapHomotopyCategoryLocalized
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      Localization.Monoidal.toMonoidalCategory
        (HomotopyCategory.quotient B (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
        (Iso.refl (homotopyUnit B))) : F.mapHomotopyCategoryLocalized.Monoidal)

/-- The unit of a functor between localized monoidal categories which lifts a composite of a
monoidal functor with a localization. -/
private lemma functorMonoidalOfComp_ε_toMonoidalCategory
    {C C₂ D₁ D₂ : Type*} [Category C] [Category C₂] [Category D₁] [Category D₂]
    [MonoidalCategory C] [MonoidalCategory C₂]
    (L₁ : C ⥤ D₁) (W₁ : MorphismProperty C) [W₁.IsMonoidal] [L₁.IsLocalization W₁]
    (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [W₂.IsMonoidal] [L₂.IsLocalization W₂]
    (P : C ⥤ C₂) [P.Monoidal]
    (Φ : LocalizedMonoidal L₁ W₁ (Iso.refl (L₁.obj (𝟙_ C))) ⥤
      LocalizedMonoidal L₂ W₂ (Iso.refl (L₂.obj (𝟙_ C₂))))
    [Localization.Lifting (Localization.Monoidal.toMonoidalCategory L₁ W₁ (Iso.refl _)) W₁
      (P ⋙ Localization.Monoidal.toMonoidalCategory L₂ W₂ (Iso.refl _)) Φ] :
    letI := Localization.Monoidal.functorMonoidalOfComp
      (Localization.Monoidal.toMonoidalCategory L₁ W₁ (Iso.refl _)) W₁ Φ
      (P ⋙ Localization.Monoidal.toMonoidalCategory L₂ W₂ (Iso.refl _))
    Functor.LaxMonoidal.ε Φ = L₂.map (Functor.LaxMonoidal.ε P) ≫
      (Localization.Lifting.iso (Localization.Monoidal.toMonoidalCategory L₁ W₁ (Iso.refl _)) W₁
        (P ⋙ Localization.Monoidal.toMonoidalCategory L₂ W₂ (Iso.refl _)) Φ).inv.app (𝟙_ C) := by
  refine (Localization.Monoidal.functorMonoidalOfComp_ε _ _ _ _).trans ?_
  rw [Functor.LaxMonoidal.comp_ε, Category.assoc]
  change 𝟙 _ ≫ _ ≫ _ ≫ Φ.map (𝟙 _) = _
  simp only [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- The tensorator of a functor between localized monoidal categories which lifts a composite of a
monoidal functor with a localization. -/
private lemma functorMonoidalOfComp_μ_toMonoidalCategory
    {C C₂ D₁ D₂ : Type*} [Category C] [Category C₂] [Category D₁] [Category D₂]
    [MonoidalCategory C] [MonoidalCategory C₂]
    (L₁ : C ⥤ D₁) (W₁ : MorphismProperty C) [W₁.IsMonoidal] [L₁.IsLocalization W₁]
    (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [W₂.IsMonoidal] [L₂.IsLocalization W₂]
    (P : C ⥤ C₂) [P.Monoidal]
    (Φ : LocalizedMonoidal L₁ W₁ (Iso.refl (L₁.obj (𝟙_ C))) ⥤
      LocalizedMonoidal L₂ W₂ (Iso.refl (L₂.obj (𝟙_ C₂))))
    [Localization.Lifting (Localization.Monoidal.toMonoidalCategory L₁ W₁ (Iso.refl _)) W₁
      (P ⋙ Localization.Monoidal.toMonoidalCategory L₂ W₂ (Iso.refl _)) Φ] (X Y : C) :
    letI := Localization.Monoidal.functorMonoidalOfComp
      (Localization.Monoidal.toMonoidalCategory L₁ W₁ (Iso.refl _)) W₁ Φ
      (P ⋙ Localization.Monoidal.toMonoidalCategory L₂ W₂ (Iso.refl _))
    letI e := Localization.Lifting.iso
      (Localization.Monoidal.toMonoidalCategory L₁ W₁ (Iso.refl _)) W₁
      (P ⋙ Localization.Monoidal.toMonoidalCategory L₂ W₂ (Iso.refl _)) Φ
    Functor.LaxMonoidal.μ Φ (L₁.obj X) (L₁.obj Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫
        (Localization.Monoidal.μ L₂ W₂ (Iso.refl _) (P.obj X) (P.obj Y)).hom ≫
        L₂.map (Functor.LaxMonoidal.μ P X Y) ≫ e.inv.app (X ⊗ Y) ≫
        Φ.map (Localization.Monoidal.μ L₁ W₁ (Iso.refl _) X Y).inv := by
  refine (Localization.Monoidal.functorMonoidalOfComp_μ
    (Localization.Monoidal.toMonoidalCategory L₁ W₁ (Iso.refl _)) W₁ Φ
    (P ⋙ Localization.Monoidal.toMonoidalCategory L₂ W₂ (Iso.refl _)) X Y).trans ?_
  rw [Functor.LaxMonoidal.comp_μ, Category.assoc]
  rfl

/-- The unit of `mapHomotopyCategoryMonoidal`: the image of the unit of `F.mapHomologicalComplex`,
through `Functor.mapHomotopyCategoryFactors`. -/
lemma mapHomotopyCategoryMonoidal_ε :
    @Functor.LaxMonoidal.ε _ _ _ _ _ _ (F.mapHomotopyCategory (ComplexShape.up ℤ))
        (mapHomotopyCategoryMonoidal F).toLaxMonoidal =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          (Functor.LaxMonoidal.ε (F.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
        (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app (𝟙_ (CochainComplex A ℤ)) := by
  let := mapHomotopyCategoryLifting F
  exact functorMonoidalOfComp_ε_toMonoidalCategory
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ)) F.mapHomotopyCategoryLocalized

/-- The tensorator of `mapHomotopyCategoryMonoidal` at the images of two complexes: the
tensorator of `F.mapHomologicalComplex`, conjugated by `homotopyMu` and
`Functor.mapHomotopyCategoryFactors`. -/
lemma mapHomotopyCategoryMonoidal_μ (K L : CochainComplex A ℤ) :
    @Functor.LaxMonoidal.μ _ _ _ _ _ _ (F.mapHomotopyCategory (ComplexShape.up ℤ))
        (mapHomotopyCategoryMonoidal F).toLaxMonoidal
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) =
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K ⊗ₘ
          (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app L) ≫
        (homotopyMu B ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).hom ≫
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          (Functor.LaxMonoidal.μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L) ≫
        (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app (K ⊗ L) ≫
        (F.mapHomotopyCategory (ComplexShape.up ℤ)).map (homotopyMu A K L).inv := by
  let := mapHomotopyCategoryLifting F
  exact functorMonoidalOfComp_μ_toMonoidalCategory
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ)) F.mapHomotopyCategoryLocalized K L

/-! ### The K-flat objects -/

variable (hF : ∀ K : CochainComplex A ℤ,
  _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K →
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor B)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))

/-- `F.mapHomotopyCategory`, restricted to the K-flat objects of the two homotopy categories. -/
def kFlatLift :
    (kFlatObjects (curriedTensor A)).FullSubcategory ⥤
      (kFlatObjects (curriedTensor B)).FullSubcategory :=
  (kFlatObjects (curriedTensor B)).lift
    ((kFlatObjects (curriedTensor A)).ι ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ))
    (fun X ↦ hF X.obj.as X.property)

/-- **The restriction of `F.mapHomotopyCategory` to the K-flat objects is monoidal**, the K-flat
objects being full monoidal subcategories on both sides. -/
@[instance_reducible]
def kFlatLiftMonoidal : (kFlatLift F hF).Monoidal :=
  letI := mapHomotopyCategoryMonoidal F
  ObjectProperty.liftMonoidal _ _ _

/-! ### The derived categories -/

variable [BraidedCategory (CochainComplex A ℤ)] [BraidedCategory (CochainComplex B ℤ)]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (hresA : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)
  (hresB : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor B) P ∧ QuasiIso f)
  (Φ : DerivedCategory A ⥤ DerivedCategory B)
  (e : kFlatQ (curriedTensor A) ⋙ Φ ≅ kFlatLift F hF ⋙ kFlatQ (curriedTensor B))

/-- `Φ`, retyped between the type synonyms carrying the localized monoidal structures of the two
derived categories. -/
abbrev derivedFunctorLocalized : DerivedLocalized A hresA ⥤ DerivedLocalized B hresB := Φ

/-- The lifting of `Φ` along the K-flat localization given by `e`. -/
@[instance_reducible]
def derivedFunctorLifting :
    letI := kFlatQ_isLocalization (curriedTensor A) hresA
    letI := kFlatQ_isLocalization (curriedTensor B) hresB
    Localization.Lifting
      (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
        (kFlatQuasiIso (curriedTensor A))
        (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))))
      (kFlatQuasiIso (curriedTensor A))
      (kFlatLift F hF ⋙
        Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor B))
          (kFlatQuasiIso (curriedTensor B))
          (Iso.refl ((kFlatQ (curriedTensor B)).obj (𝟙_ _))))
      (derivedFunctorLocalized hresA hresB Φ) :=
  ⟨e⟩

/-- **A functor `Φ : D(A) ⥤ D(B)` computed on K-flat objects by `F` is monoidal**, for
`CochainComplex.KFlatMonoidal.derivedMonoidal` on both sides. It is
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` applied to the K-flat localization,
with the lifting `e` to the monoidal functor `kFlatLift F hF` followed by the localization. -/
@[instance_reducible]
def derivedFunctorMonoidal :
    letI := derivedMonoidal A hresA
    letI := derivedMonoidal B hresB
    Φ.Monoidal :=
  letI := kFlatQ_isLocalization (curriedTensor A) hresA
  letI := kFlatQ_isLocalization (curriedTensor B) hresB
  letI := kFlatLiftMonoidal F hF
  letI := derivedFunctorLifting F hF hresA hresB Φ e
  (Localization.Monoidal.functorMonoidalOfComp
    (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
      (kFlatQuasiIso (curriedTensor A))
      (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))))
    (kFlatQuasiIso (curriedTensor A))
    (derivedFunctorLocalized hresA hresB Φ)
    (kFlatLift F hF ⋙
      Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor B))
        (kFlatQuasiIso (curriedTensor B))
        (Iso.refl ((kFlatQ (curriedTensor B)).obj (𝟙_ _)))) :
      (derivedFunctorLocalized hresA hresB Φ).Monoidal)

omit [MonoidalCategory A] [MonoidalCategory B] [(curriedTensor A).Additive]
  [∀ X : A, ((curriedTensor A).obj X).Additive] [(curriedTensor B).Additive]
  [∀ X : B, ((curriedTensor B).obj X).Additive] [Abelian A] [Abelian B] [F.Additive] [F.Monoidal]
  [∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ X₂ : GradedObject ℤ B, GradedObject.HasTensor X₁ X₂] in
/-- Composing with the image of an identity morphism does nothing. -/
private lemma comp_map_id {C₁ C₂ : Type*} [Category C₁] [Category C₂] (G : C₁ ⥤ C₂)
    {X : C₂} {W : C₁} (a : X ⟶ G.obj W) : a ≫ G.map (𝟙 W) = a := by
  simp

/-- The unit of `derivedFunctorMonoidal`: the image in `D(B)` of the unit of
`F.mapHomotopyCategory`, followed by `e⁻¹` at the unit. -/
lemma derivedFunctorMonoidal_ε :
    @Functor.LaxMonoidal.ε _ _ (derivedMonoidal A hresA) _ _ (derivedMonoidal B hresB) Φ
        (derivedFunctorMonoidal F hF hresA hresB Φ e).toLaxMonoidal =
      DerivedCategory.Qh.map
          (@Functor.LaxMonoidal.ε _ _ _ _ _ _ (F.mapHomotopyCategory (ComplexShape.up ℤ))
            (mapHomotopyCategoryMonoidal F).toLaxMonoidal) ≫
        e.inv.app (𝟙_ (kFlatObjects (curriedTensor A)).FullSubcategory) := by
  let := kFlatQ_isLocalization (curriedTensor A) hresA
  let := kFlatQ_isLocalization (curriedTensor B) hresB
  let := kFlatLiftMonoidal F hF
  let := derivedFunctorLifting F hF hresA hresB Φ e
  have h₃ : (Functor.LaxMonoidal.ε (kFlatLift F hF)).hom =
      @Functor.LaxMonoidal.ε _ _ _ _ _ _ (F.mapHomotopyCategory (ComplexShape.up ℤ))
          (mapHomotopyCategoryMonoidal F).toLaxMonoidal ≫
        (F.mapHomotopyCategory (ComplexShape.up ℤ)).map (𝟙 _) := rfl
  have h₄ : (kFlatQ (curriedTensor B)).map (Functor.LaxMonoidal.ε (kFlatLift F hF)) =
      DerivedCategory.Qh.map
        (@Functor.LaxMonoidal.ε _ _ _ _ _ _ (F.mapHomotopyCategory (ComplexShape.up ℤ))
          (mapHomotopyCategoryMonoidal F).toLaxMonoidal) := by
    change DerivedCategory.Qh.map (Functor.LaxMonoidal.ε (kFlatLift F hF)).hom = _
    rw [h₃, comp_map_id]
    rfl
  exact (functorMonoidalOfComp_ε_toMonoidalCategory _ _ _ _ (kFlatLift F hF)
    (derivedFunctorLocalized hresA hresB Φ)).trans (congrArg (· ≫ _) h₄)

/-- The tensorator of `derivedFunctorMonoidal` at the images of two K-flat objects: the tensorator
of `kFlatLift F hF`, conjugated by `e` and by the tensorators `Localization.Monoidal.μ` of the two
K-flat localizations. -/
lemma derivedFunctorMonoidal_μ (X Y : (kFlatObjects (curriedTensor A)).FullSubcategory) :
    letI := kFlatQ_isLocalization (curriedTensor A) hresA
    letI := kFlatQ_isLocalization (curriedTensor B) hresB
    letI := derivedMonoidal A hresA
    letI := derivedMonoidal B hresB
    letI := derivedFunctorMonoidal F hF hresA hresB Φ e
    letI := kFlatLiftMonoidal F hF
    Functor.LaxMonoidal.μ Φ ((kFlatQ (curriedTensor A)).obj X) ((kFlatQ (curriedTensor A)).obj Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫
        (Localization.Monoidal.μ (kFlatQ (curriedTensor B)) (kFlatQuasiIso (curriedTensor B))
          (Iso.refl ((kFlatQ (curriedTensor B)).obj (𝟙_ _)))
          ((kFlatLift F hF).obj X) ((kFlatLift F hF).obj Y)).hom ≫
        (kFlatQ (curriedTensor B)).map (Functor.LaxMonoidal.μ (kFlatLift F hF) X Y) ≫
        e.inv.app (X ⊗ Y) ≫
        Φ.map (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
          (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))) X Y).inv := by
  let := kFlatQ_isLocalization (curriedTensor A) hresA
  let := kFlatQ_isLocalization (curriedTensor B) hresB
  let := kFlatLiftMonoidal F hF
  let := derivedFunctorLifting F hF hresA hresB Φ e
  exact functorMonoidalOfComp_μ_toMonoidalCategory _ _ _ _ (kFlatLift F hF)
    (derivedFunctorLocalized hresA hresB Φ) X Y

end CochainComplex.KFlatMonoidal

end
