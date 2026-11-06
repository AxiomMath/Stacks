module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedBifunctorOnModels
public import StacksFrontier.Homology.DerivedCategory.Monoidal.MapDerivedCategoryMonoidal

/-!
# The tensorator of `F.mapDerivedCategory` on K-flat complexes

Let `F : A ⥤ B` be an additive, exact, monoidal functor between monoidal abelian categories
which carries K-flat complexes to K-flat complexes, so that `F.mapDerivedCategory` is monoidal
for the derived tensor products (`CategoryTheory.Functor.mapDerivedCategoryMonoidal`). That
structure is produced by two descents along localizations, so nothing about it is visible at
a particular pair of objects. This file computes its tensorator at the image of a pair of
K-flat complexes `K` and `L`: it is the tensorator of `F` applied termwise to the total tensor
complex, read through the identifications `QK ⊗ QL ≅ Q(K ⊗ L)` of
`CochainComplex.KFlatMonoidal.derivedTensorIso` on either side and the identification
`F.mapDerivedCategory (Q K) ≅ Q (F K)` of `CategoryTheory.Functor.mapDerivedCategoryFactors`.

## Main results

* `CategoryTheory.Functor.mapHomotopyCategoryMonoidal_μ_quotient`: the tensorator of
  `F.mapHomotopyCategory` at the image of a pair of complexes.
* `CategoryTheory.Functor.mapDerivedCategoryMonoidal_μ_Q`: the tensorator of
  `F.mapDerivedCategory` at the image of a pair of K-flat complexes.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatMonoidal CochainComplex.KFlatBifunctor

universe w w' v₁ u₁ v₂ u₂

namespace CategoryTheory

/-- Removing two identities from a composite. Applied as a term, so that the unifier rather than
the rewriter matches the objects, which `rw` cannot do across the type synonyms carrying the
localized monoidal structures. -/
private lemma comp_map_comp_id_comp_id {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {a b e : D} {p q : C} (x : a ⟶ b) (y : b ⟶ G.obj p) (m : p ⟶ q) (z : G.obj q ⟶ e) :
    x ≫ (y ≫ G.map (m ≫ 𝟙 q)) ≫ z ≫ 𝟙 e = x ≫ y ≫ G.map m ≫ z := by
  simp

/-- Removing a trailing identity image from a composite, applied as a term; see
`comp_map_comp_id_comp_id`. -/
private lemma comp_comp_map_id {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {a b : D} {p : C} (x : a ⟶ b) (y : b ⟶ G.obj p) : x ≫ y ≫ G.map (𝟙 p) = x ≫ y := by
  simp

/-- Cancelling the image of an isomorphism against the image of its inverse, applied as a term;
see `comp_map_comp_id_comp_id`. -/
private lemma comp_comp_map_inv_comp_map_hom {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {a b : D} {p q : C} (x : a ⟶ b) (y : b ⟶ G.obj q) (i : p ≅ q) :
    (x ≫ y ≫ G.map i.inv) ≫ G.map i.hom = x ≫ y := by
  simp [← Functor.map_comp]

/-- The final reassembly in `CategoryTheory.Functor.mapDerivedCategoryMonoidal_μ_Q`, applied as
a term; see `comp_map_comp_id_comp_id`. -/
private lemma tensor_comp_assemble {D : Type*} [Category D] [MonoidalCategory D]
    {P₁ P₂ R₁ R₂ S₁ S₂ T T₂ U U' V W Z Y Y₂ : D}
    (a₁ : P₁ ⟶ R₁) (b₁ : R₁ ⟶ S₁) (a₂ : P₂ ⟶ R₂) (b₂ : R₂ ⟶ S₂) (m : S₁ ⊗ S₂ ⟶ T)
    (g : T ⟶ U) (e : U ⟶ V) (ph : V ⟶ W) (pq : W ⟶ Z) (φ : Z ⟶ Y) (X : U ⟶ U')
    (e' : U' ⟶ W) (q'' : U' ⟶ Y) (hb : T ⟶ T₂) (hqμ : T₂ ⟶ U') (q' : T₂ ⟶ Y₂) (Qμ : Y₂ ⟶ Y)
    (hnat : X ≫ e' = e ≫ ph) (hB : e' ≫ pq ≫ φ = q'') (hμ : g ≫ X = hb ≫ hqμ)
    (hq : hqμ ≫ q'' = q' ≫ Qμ) :
    (a₁ ≫ b₁ ⊗ₘ a₂ ≫ b₂) ≫ (m ≫ g ≫ e) ≫ ph ≫ pq ≫ φ =
      (a₁ ⊗ₘ a₂) ≫ ((b₁ ⊗ₘ b₂) ≫ m ≫ hb ≫ q') ≫ Qμ := by
  simp only [← tensorHom_comp_tensorHom, Category.assoc]
  rw [← reassoc_of% hnat, hB, reassoc_of% hμ, hq]

/-- Moving isomorphisms across an equation, applied as a term; see
`comp_map_comp_id_comp_id`. -/
private lemma inv_comp_hom_comp_of_inv_comp_hom {C : Type*} [Category C] {P₁ P₂ P₃ P₄ : C}
    (i : P₂ ≅ P₁) (e : P₂ ≅ P₃) (φ : P₁ ⟶ P₄) (j : P₃ ≅ P₄) (h : i.inv ≫ e.hom = φ ≫ j.inv) :
    e.inv ≫ i.hom ≫ φ = j.hom := by
  rw [← cancel_epi e.hom, Iso.hom_inv_id_assoc, ← cancel_epi i.inv, Iso.inv_hom_id_assoc,
    reassoc_of% h, Iso.inv_hom_id, Category.comp_id]

attribute [local instance] homotopyMonoidal homotopyBraided

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [MonoidalCategory B]
  [(curriedTensor B).Additive] [∀ X : B, ((curriedTensor B).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ B), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X₁)]
  [∀ X₂ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ B, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (F : A ⥤ B) [F.Additive] [F.Monoidal]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) F]

/-- **The tensorator of `F.mapHomotopyCategory` at the image of a pair of complexes** is the
tensorator of `F` applied termwise, read through the comparisons `homotopyMu` of the two
homotopy categories. -/
theorem Functor.mapHomotopyCategoryMonoidal_μ_quotient (K L : CochainComplex A ℤ) :
    letI := Functor.mapHomotopyCategoryMonoidal F
    Functor.LaxMonoidal.μ (F.mapHomotopyCategory (ComplexShape.up ℤ))
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) =
      (homotopyMu B ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).hom ≫
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          (Functor.LaxMonoidal.μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L) ≫
        (F.mapHomotopyCategory (ComplexShape.up ℤ)).map (homotopyMu A K L).inv := by
  let := Functor.mapHomotopyCategoryLifting F
  have h := Localization.Monoidal.functorMonoidalOfComp_μ
    (Localization.Monoidal.toMonoidalCategory (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit A)))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (Functor.mapHomotopyCategoryLocalized F)
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      Localization.Monoidal.toMonoidalCategory
        (HomotopyCategory.quotient B (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
        (Iso.refl (homotopyUnit B))) K L
  have e : ∀ X : CochainComplex A ℤ,
      (Functor.mapHomotopyCategoryLifting F).iso.hom.app X = 𝟙 _ := fun _ => rfl
  have e' : ∀ X : CochainComplex A ℤ,
      (Functor.mapHomotopyCategoryLifting F).iso.inv.app X = 𝟙 _ := fun _ => rfl
  rw [e K, e L, e' (K ⊗ L), Functor.LaxMonoidal.comp_μ] at h
  refine h.trans ?_
  refine (congrArg (· ≫ _) (id_tensorHom_id _ _)).trans ?_
  refine (Category.id_comp _).trans ?_
  refine (congrArg (fun t => _ ≫ t) (Category.id_comp _)).trans ?_
  exact Category.assoc _ _ _

section Derived

variable [BraidedCategory (CochainComplex A ℤ)] [BraidedCategory (CochainComplex B ℤ)]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (hF : ∀ K : CochainComplex A ℤ, KFlat (curriedTensor A) K →
    KFlat (curriedTensor B) ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hresA : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)
  (hresB : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
    KFlat (curriedTensor B) P ∧ QuasiIso f)

include hF in
/-- **The tensorator of `F.mapDerivedCategory` at the image of a pair of K-flat objects of the
homotopy category**, composed with the comparison of the source with the image of the total
tensor complex: it is the comparison of the target, followed by the tensorator of `F` applied
termwise. -/
theorem Functor.mapDerivedCategoryMonoidal_μ_Qh {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    letI := derivedMonoidal A hresA
    letI := derivedMonoidal B hresB
    letI := Functor.mapDerivedCategoryMonoidal F hF hresA hresB
    letI := Functor.mapHomotopyCategoryMonoidal F
    Functor.LaxMonoidal.μ F.mapDerivedCategory
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) ≫
      F.mapDerivedCategory.map (derivedMu A hresA hK hL) =
      (F.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⊗ₘ
        F.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) ≫
        derivedMu B hresB (hF K hK) (hF L hL) ≫
        DerivedCategory.Qh.map (Functor.LaxMonoidal.μ (F.mapHomotopyCategory (ComplexShape.up ℤ))
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) ≫
        F.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⊗
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) := by
  let := kFlatQ_isLocalization (curriedTensor A) hresA
  let := kFlatQ_isLocalization (curriedTensor B) hresB
  let := Functor.kFlatLiftMonoidal F hF
  let := Functor.mapDerivedCategoryLifting F hF hresA hresB
  let := derivedMonoidal A hresA
  let := derivedMonoidal B hresB
  let := Functor.mapDerivedCategoryMonoidal F hF hresA hresB
  let := Functor.mapHomotopyCategoryMonoidal F
  have h := Localization.Monoidal.functorMonoidalOfComp_μ
    (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
      (kFlatQuasiIso (curriedTensor A))
      (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))))
    (kFlatQuasiIso (curriedTensor A))
    (Functor.mapDerivedCategoryLocalized F hresA hresB)
    (Functor.kFlatLift F hF ⋙
      Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor B))
        (kFlatQuasiIso (curriedTensor B))
        (Iso.refl ((kFlatQ (curriedTensor B)).obj (𝟙_ _))))
    (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩ :
      (kFlatObjects (curriedTensor A)).FullSubcategory)
    (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩ :
      (kFlatObjects (curriedTensor A)).FullSubcategory)
  rw [Functor.LaxMonoidal.comp_μ] at h
  let δA : DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⊗
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⊗
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) :=
    (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
      (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))
      ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩
      ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩).inv
  have hδ : δA ≫ derivedMu A hresA hK hL = 𝟙 _ :=
    (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
      (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))
      ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩
      ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩).inv_hom_id
  have h' : Functor.LaxMonoidal.μ F.mapDerivedCategory
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) =
      (F.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⊗ₘ
        F.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) ≫
        (derivedMu B hresB (hF K hK) (hF L hL) ≫
          DerivedCategory.Qh.map (Functor.LaxMonoidal.μ (F.mapHomotopyCategory (ComplexShape.up ℤ))
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) ≫
            (F.mapHomotopyCategory (ComplexShape.up ℤ)).map (𝟙 _))) ≫
        F.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⊗
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) ≫
        F.mapDerivedCategory.map δA := h
  rw [h']
  simp only [Category.assoc, ← Functor.map_comp, hδ, Functor.map_id]
  refine Eq.trans ?_ (comp_map_comp_id_comp_id (DerivedCategory.Qh (C := B)) _ _ _ _)
  simp only [Category.assoc]

omit [BraidedCategory (CochainComplex A ℤ)] [BraidedCategory (CochainComplex B ℤ)]
  [F.Monoidal] [MonoidalCategory A] [MonoidalCategory B]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [(curriedTensor B).Additive] [∀ X : B, ((curriedTensor B).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ B), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X₁)]
  [∀ X₂ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ B, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) F] in
/-- The two factorizations of `F.mapDerivedCategory`, through `Q` and through `Qh`, at a
complex. -/
@[reassoc]
lemma Functor.map_quotientCompQhIso_inv_comp_mapDerivedCategoryFactorsh_hom
    (K : CochainComplex A ℤ) :
    F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).inv.app K) ≫
        F.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K ≫
        (DerivedCategory.quotientCompQhIso B).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, Category.id_comp]
  exact comp_comp_map_id _ _ _

omit [BraidedCategory (CochainComplex A ℤ)] [BraidedCategory (CochainComplex B ℤ)]
  [F.Monoidal] [MonoidalCategory A] [MonoidalCategory B]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [(curriedTensor B).Additive] [∀ X : B, ((curriedTensor B).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ B), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X₁)]
  [∀ X₂ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ B, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) F] in
/-- The two factorizations of `F.mapDerivedCategory`, through `Q` and through `Qh`, at a
complex, inverted. -/
@[reassoc]
lemma Functor.mapDerivedCategoryFactorsh_inv_comp_map_quotientCompQhIso_hom
    (K : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
        F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app K) ≫
          F.mapDerivedCategoryFactors.hom.app K =
      (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  inv_comp_hom_comp_of_inv_comp_hom
    (F.mapDerivedCategory.mapIso ((DerivedCategory.quotientCompQhIso A).app K))
    (F.mapDerivedCategoryFactorsh.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))
    (F.mapDerivedCategoryFactors.hom.app K)
    ((DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (Functor.map_quotientCompQhIso_inv_comp_mapDerivedCategoryFactorsh_hom F K)

include hF in
/-- **The tensorator of `F.mapDerivedCategory` at the image of a pair of K-flat complexes.**
Read through the comparisons `QK ⊗ QL ≅ Q(K ⊗ L)` of `derivedTensorIso` on either side and the
identification `F.mapDerivedCategory (Q K) ≅ Q (F K)`, it is the image of the tensorator of `F`
applied termwise. -/
theorem Functor.mapDerivedCategoryMonoidal_μ_Q {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    letI := derivedMonoidal A hresA
    letI := derivedMonoidal B hresB
    letI := Functor.mapDerivedCategoryMonoidal F hF hresA hresB
    Functor.LaxMonoidal.μ F.mapDerivedCategory (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) ≫
      F.mapDerivedCategory.map (derivedTensorIso A hresA hK hL).hom ≫
      F.mapDerivedCategoryFactors.hom.app (K ⊗ L) =
      (F.mapDerivedCategoryFactors.hom.app K ⊗ₘ F.mapDerivedCategoryFactors.hom.app L) ≫
        (derivedTensorIso B hresB (hF K hK) (hF L hL)).hom ≫
        DerivedCategory.Q.map
          (Functor.LaxMonoidal.μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L) := by
  let := derivedMonoidal A hresA
  let := derivedMonoidal B hresB
  let := Functor.mapDerivedCategoryMonoidal F hF hresA hresB
  let := Functor.mapHomotopyCategoryMonoidal F
  have hQh := Functor.mapDerivedCategoryMonoidal_μ_Qh F hF hresA hresB hK hL
  have hH := Functor.mapHomotopyCategoryMonoidal_μ_quotient F K L
  have hB := Functor.mapDerivedCategoryFactorsh_inv_comp_map_quotientCompQhIso_hom F (K ⊗ L)
  rw [derivedTensorIso_hom_eq, derivedTensorIso_hom_eq, Functor.map_comp, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_assoc, reassoc_of% hQh, tensorHom_comp_tensorHom_assoc,
    Iso.app_inv, Iso.app_inv,
    Functor.map_quotientCompQhIso_inv_comp_mapDerivedCategoryFactorsh_hom,
    Functor.map_quotientCompQhIso_inv_comp_mapDerivedCategoryFactorsh_hom]
  have hnat : DerivedCategory.Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
        (homotopyMu A K L).hom) ≫
      F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (K ⊗ L)) =
      F.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⊗
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) ≫
      F.mapDerivedCategory.map (DerivedCategory.Qh.map (homotopyMu A K L).hom) :=
    F.mapDerivedCategoryFactorsh.inv.naturality (homotopyMu A K L).hom
  have hμ : DerivedCategory.Qh.map
      (Functor.LaxMonoidal.μ (F.mapHomotopyCategory (ComplexShape.up ℤ))
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) ≫
      DerivedCategory.Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
        (homotopyMu A K L).hom) =
      DerivedCategory.Qh.map (homotopyMu B ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).hom ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          (Functor.LaxMonoidal.μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L)) := by
    rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp, hH]
    exact congrArg _ (comp_comp_map_inv_comp_map_hom _ _ _ _)
  have hq := (DerivedCategory.quotientCompQhIso B).hom.naturality
    (Functor.LaxMonoidal.μ (F.mapHomologicalComplex (ComplexShape.up ℤ)) K L)
  refine Eq.trans ?_ (tensor_comp_assemble _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnat hB hμ hq)
  simp only [Category.assoc]
  rfl

end Derived

end CategoryTheory

end
