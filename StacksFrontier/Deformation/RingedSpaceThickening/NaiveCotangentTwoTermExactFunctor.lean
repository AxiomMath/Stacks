module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryExtOne
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClassVanishing

/-!
# The class of a conormal homomorphism under an exact functor

Let `F : C ⥤ D` be an exact functor of abelian categories. The class in `Ext¹` of a homomorphism
`δ : X₀ ⟶ M` out of the degree `-1` term of a two-term complex `double d` — the form in which the
class of a square-zero extension is read off a presentation (**Stacks 0GQ0**) — is carried by
`F` to the class of `F δ`, compatibly with maps of two-term complexes and with comparisons that
become invertible in the derived category.

## Main results

* `CategoryTheory.Functor.Q_map_comp_mapExtOne_conormalExtClass`: the image under `F` of the class
  of `δ₁`, read through comparisons `c₁`, `c₂` and maps `ψ`, `φ` of complexes, is the class of `δ₂`
  as soon as `ψ` in degree `-1` followed by `F δ₁` is `δ₂`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open ComplexShape (upIntRelNegOneZero)
open AlgebraicGeometry.RingedSpaceThickening

namespace CategoryTheory.Functor

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- A map out of the degree `-1` term of `double d` composes to zero with the incoming
differentials. -/
private theorem double_d_comp_doubleXIso₀_hom_comp_eq_zero {A : Type*} [Category A] [Abelian A]
    {X₀ X₁ G : A} (d : X₀ ⟶ X₁) (f : X₀ ⟶ G) : ∀ i : ℤ, (ComplexShape.up ℤ).Rel i (-1) →
      (double d upIntRelNegOneZero).d i (-1) ≫ ((doubleXIso₀ d upIntRelNegOneZero).hom ≫ f) =
        0 :=
  fun i hi => (isZero_double_X d upIntRelNegOneZero i
    (by rw [ComplexShape.up_Rel] at hi; omega)
    (by rw [ComplexShape.up_Rel] at hi; omega)).eq_of_src _ _

/-- **The image under an exact functor of the class of a conormal homomorphism.** Let
`d₁ : X₀ ⟶ X₁` in `C` and `d₂ : Y₀ ⟶ Y₁` in `D` define two-term complexes with comparisons
`c₁ : double d₁ ⟶ N₁`, `c₂ : double d₂ ⟶ N₂` invertible in the derived categories, and let
`ψ : double d₂ ⟶ F (double d₁)` and `φ : N₂ ⟶ F N₁` be chain maps with `c₂ ≫ φ = ψ ≫ F c₁`. If
`ψ` in degree `-1` followed by `F δ₁` is `δ₂`, then `φ` carries the image of the class of `δ₁` to
the class of `δ₂`. -/
theorem Q_map_comp_mapExtOne_conormalExtClass {X₀ X₁ : C} (d₁ : X₀ ⟶ X₁) {Y₀ Y₁ : D}
    (d₂ : Y₀ ⟶ Y₁) {N₁ : CochainComplex C ℤ} {N₂ : CochainComplex D ℤ}
    (c₁ : double d₁ upIntRelNegOneZero ⟶ N₁) (c₂ : double d₂ upIntRelNegOneZero ⟶ N₂)
    (hc₁ : IsIso (DerivedCategory.Q.map c₁)) (hc₂ : IsIso (DerivedCategory.Q.map c₂))
    (ψ : double d₂ upIntRelNegOneZero ⟶
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (double d₁ upIntRelNegOneZero))
    (φ : N₂ ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N₁)
    (hφ : c₂ ≫ φ = ψ ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map c₁)
    {M : C} (δ₁ : X₀ ⟶ M) (δ₂ : Y₀ ⟶ F.obj M)
    (h₁ : (double d₁ upIntRelNegOneZero).X (-1) = X₀)
    (h₂ : (double d₂ upIntRelNegOneZero).X (-1) = Y₀)
    (hδ' : ψ.f (-1) ≫ F.map (eqToHom h₁ ≫ δ₁) = eqToHom h₂ ≫ δ₂) :
    DerivedCategory.Q.map φ ≫ F.mapExtOne (CategoryTheory.inv (DerivedCategory.Q.map c₁) ≫
        (NaiveCotangentTwoTerm.ofDoubleNegOne d₁).conormalExtClass M δ₁) =
      CategoryTheory.inv (DerivedCategory.Q.map c₂) ≫
        (NaiveCotangentTwoTerm.ofDoubleNegOne d₂).conormalExtClass (F.obj M) δ₂ := by
  have hδ : ψ.f (-1) ≫ F.map ((doubleXIso₀ d₁ upIntRelNegOneZero).hom ≫ δ₁) =
      (doubleXIso₀ d₂ upIntRelNegOneZero).hom ≫ δ₂ := hδ'
  have hf₁ := double_d_comp_doubleXIso₀_hom_comp_eq_zero d₁ δ₁
  have hf₂ := double_d_comp_doubleXIso₀_hom_comp_eq_zero d₂ δ₂
  have e₁ := neg_eq_iff_eq_neg.1 (NaiveCotangentTwoTerm.Q_map_mkHomToSingle_comp d₁ M δ₁ hf₁).symm
  have e₂ := neg_eq_iff_eq_neg.1
    (NaiveCotangentTwoTerm.Q_map_mkHomToSingle_comp d₂ (F.obj M) δ₂ hf₂).symm
  refine (congrArg (fun z => DerivedCategory.Q.map φ ≫ F.mapExtOne
    (CategoryTheory.inv (DerivedCategory.Q.map c₁) ≫ z)) e₁).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => CategoryTheory.inv (DerivedCategory.Q.map c₂) ≫ z) e₂).symm
  rw [Preadditive.comp_neg, Preadditive.comp_neg, mapExtOne_neg, Preadditive.comp_neg,
    mapExtOne_inv_Q_map_comp, mapExtOne_Q_map_shiftIso]
  congr 1
  have hchain : ψ ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (mkHomToSingle ((doubleXIso₀ d₁ upIntRelNegOneZero).hom ≫ δ₁) hf₁) ≫
        (singleMapHomologicalComplex F (ComplexShape.up ℤ) (-1)).hom.app M =
      mkHomToSingle ((doubleXIso₀ d₂ upIntRelNegOneZero).hom ≫ δ₂) hf₂ := by
    apply HomologicalComplex.to_single_hom_ext
    simp only [comp_f, Functor.mapHomologicalComplex_map_f, mkHomToSingle_f,
      singleMapHomologicalComplex_hom_app_self, Functor.map_comp, Category.assoc]
    simp only [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
    rw [reassoc_of% hδ]
  have := F.isIso_Q_map_mapHomologicalComplex_map c₁
  have hQ : DerivedCategory.Q.map φ ≫ CategoryTheory.inv (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map c₁)) =
      CategoryTheory.inv (DerivedCategory.Q.map c₂) ≫ DerivedCategory.Q.map ψ := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← Functor.map_comp, hφ, Functor.map_comp,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, hQ, Category.assoc, ← Category.assoc (DerivedCategory.Q.map ψ),
    ← Functor.map_comp, hchain]


/-- **The image under an exact functor of the class of a conormal homomorphism, contravariant
form.** Let `d₁ : X₀ ⟶ X₁` in `C` and `d₂ : Y₀ ⟶ Y₁` in `D` define two-term complexes with
comparisons `c₁ : double d₁ ⟶ N₁`, `c₂ : double d₂ ⟶ N₂` invertible in the derived categories, and
let `ψ : F (double d₁) ⟶ double d₂` and `φ : F N₁ ⟶ N₂` be chain maps with
`F c₁ ≫ φ = ψ ≫ c₂`. If `F δ₁` followed by `κ : F M ⟶ M'` is `ψ` in degree `-1` followed by `δ₂`,
then the class of `δ₂` pulled back along `φ` is the image under `F` of the class of `δ₁` pushed
forward along `κ`. -/
theorem Q_map_comp_conormalExtClass_eq_mapExtOne_comp {X₀ X₁ : C} (d₁ : X₀ ⟶ X₁) {Y₀ Y₁ : D}
    (d₂ : Y₀ ⟶ Y₁) {N₁ : CochainComplex C ℤ} {N₂ : CochainComplex D ℤ}
    (c₁ : double d₁ upIntRelNegOneZero ⟶ N₁) (c₂ : double d₂ upIntRelNegOneZero ⟶ N₂)
    (hc₁ : IsIso (DerivedCategory.Q.map c₁)) (hc₂ : IsIso (DerivedCategory.Q.map c₂))
    (ψ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (double d₁ upIntRelNegOneZero) ⟶
      double d₂ upIntRelNegOneZero)
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N₁ ⟶ N₂)
    (hφ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).map c₁ ≫ φ = ψ ≫ c₂)
    {M : C} {M' : D} (κ : F.obj M ⟶ M') (δ₁ : X₀ ⟶ M) (δ₂ : Y₀ ⟶ M')
    (h₁ : (double d₁ upIntRelNegOneZero).X (-1) = X₀)
    (h₂ : (double d₂ upIntRelNegOneZero).X (-1) = Y₀)
    (hδ' : F.map (eqToHom h₁ ≫ δ₁) ≫ κ = ψ.f (-1) ≫ eqToHom h₂ ≫ δ₂) :
    DerivedCategory.Q.map φ ≫ CategoryTheory.inv (DerivedCategory.Q.map c₂) ≫
        (NaiveCotangentTwoTerm.ofDoubleNegOne d₂).conormalExtClass M' δ₂ =
      F.mapExtOne (CategoryTheory.inv (DerivedCategory.Q.map c₁) ≫
          (NaiveCotangentTwoTerm.ofDoubleNegOne d₁).conormalExtClass M δ₁) ≫
        ((DerivedCategory.singleFunctor D 0).map κ)⟦(1 : ℤ)⟧' := by
  have hδ : F.map ((doubleXIso₀ d₁ upIntRelNegOneZero).hom ≫ δ₁) ≫ κ =
      ψ.f (-1) ≫ (doubleXIso₀ d₂ upIntRelNegOneZero).hom ≫ δ₂ := hδ'
  have hf₁ := double_d_comp_doubleXIso₀_hom_comp_eq_zero d₁ δ₁
  have hf₂ := double_d_comp_doubleXIso₀_hom_comp_eq_zero d₂ δ₂
  have e₁ := neg_eq_iff_eq_neg.1 (NaiveCotangentTwoTerm.Q_map_mkHomToSingle_comp d₁ M δ₁ hf₁).symm
  have e₂ := neg_eq_iff_eq_neg.1
    (NaiveCotangentTwoTerm.Q_map_mkHomToSingle_comp d₂ M' δ₂ hf₂).symm
  refine (congrArg (fun z => DerivedCategory.Q.map φ ≫
    CategoryTheory.inv (DerivedCategory.Q.map c₂) ≫ z) e₂).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => F.mapExtOne
    (CategoryTheory.inv (DerivedCategory.Q.map c₁) ≫ z) ≫
      ((DerivedCategory.singleFunctor D 0).map κ)⟦(1 : ℤ)⟧') e₁).symm
  rw [Preadditive.comp_neg, Preadditive.comp_neg, Preadditive.comp_neg, mapExtOne_neg,
    Preadditive.neg_comp, mapExtOne_inv_Q_map_comp, mapExtOne_Q_map_shiftIso]
  congr 1
  have hnat :=
    ((DerivedCategory.singleFunctors D).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.naturality κ
  have hchain : (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (mkHomToSingle ((doubleXIso₀ d₁ upIntRelNegOneZero).hom ≫ δ₁) hf₁) ≫
        (singleMapHomologicalComplex F (ComplexShape.up ℤ) (-1)).hom.app M ≫
          (HomologicalComplex.single D (ComplexShape.up ℤ) (-1)).map κ =
      ψ ≫ mkHomToSingle ((doubleXIso₀ d₂ upIntRelNegOneZero).hom ≫ δ₂) hf₂ := by
    apply HomologicalComplex.to_single_hom_ext
    simp only [comp_f, Functor.mapHomologicalComplex_map_f, mkHomToSingle_f,
      singleMapHomologicalComplex_hom_app_self, Functor.map_comp, Category.assoc,
      HomologicalComplex.single_map_f_self]
    simp only [← F.map_comp_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, F.map_id,
      Category.id_comp]
    rw [reassoc_of% hδ]
  have := F.isIso_Q_map_mapHomologicalComplex_map c₁
  have hQ : CategoryTheory.inv (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map c₁)) ≫ DerivedCategory.Q.map ψ =
      DerivedCategory.Q.map φ ≫ CategoryTheory.inv (DerivedCategory.Q.map c₂) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← Functor.map_comp, hφ, Functor.map_comp,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hnat' : ((DerivedCategory.singleFunctors D).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app
        (F.obj M) ≫ ((DerivedCategory.singleFunctor D 0).map κ)⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map ((HomologicalComplex.single D (ComplexShape.up ℤ) (-1)).map κ) ≫
        ((DerivedCategory.singleFunctors D).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app M' :=
    hnat.symm
  rw [← reassoc_of% hQ, ← Functor.map_comp_assoc, ← hchain, Category.assoc, Category.assoc, hnat']
  simp only [Functor.map_comp, Category.assoc]

/-- Cancelling the transport isomorphisms around a composite with the image of a functor. -/
theorem eqToHom_comp_comp_map_eqToHom_comp_map {C' D' : Type*} [Category C'] [Category D']
    (F' : C' ⥤ D') {Z W : D'} {X X' M : C'} (hZ : Z = W) (P : W ⟶ F'.obj X) (h : X = X')
    (h' : X' = X) (δ : X ⟶ M) (δ₂ : W ⟶ F'.obj M) (hP : P ≫ F'.map δ = δ₂) :
    (eqToHom hZ ≫ P ≫ F'.map (eqToHom h)) ≫ F'.map (eqToHom h' ≫ δ) = eqToHom hZ ≫ δ₂ := by
  subst h'
  simp [← hP]

end CategoryTheory.Functor
