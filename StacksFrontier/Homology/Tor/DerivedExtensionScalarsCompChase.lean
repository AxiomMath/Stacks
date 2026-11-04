module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp

/-!
# Composition laws for comparisons with derived extension of scalars

Diagram chases behind composition laws of maps built from the comparison of derived with
degreewise extension of scalars: uniqueness of maps into a left derived functor moved across an
isomorphism, the composition law of the comparison along two ring homomorphisms followed by
identifications of complexes, the complex-level form of a degreewise composition law of
extension-of-scalars comparisons, and the identifications of the derived image of a complex
under an exact functor with the image of the complex.

## Main results

* `CategoryTheory.Functor.leftDerived_ext_comp_inv_app`
* `CochainComplex.DerivedExtensionScalars.comparison_comp_chase`
* `CochainComplex.DerivedExtensionScalars.mapHomologicalComplex_comp_inv_app_eq`
* `CategoryTheory.Functor.mapDerivedCategoryFactors_inv_app_comp_map`
* `Functor.mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso_hom_app_quotient_obj`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace CategoryTheory.Functor

/-- Uniqueness of maps into a left derived functor, moved across an isomorphism, tested on the
objects in the image of a functor surjective on objects. -/
theorem leftDerived_ext_comp_inv_app {C₀ C D H : Type*} [Category* C₀] [Category* C] [Category* D]
    [Category* H] {L : C ⥤ D} {W : MorphismProperty C} [L.IsLocalization W] {F : C ⥤ H}
    {LF : D ⥤ H} (α : L ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α W] {G M : D ⥤ H} (γ₁ : G ⟶ LF)
    (γ₂ : G ⟶ M) (θ : M ≅ LF) (q : C₀ ⥤ C) (hq : ∀ K, ∃ P, q.obj P = K)
    (h : ∀ P, γ₁.app (L.obj (q.obj P)) ≫ α.app (q.obj P) =
      γ₂.app (L.obj (q.obj P)) ≫ θ.hom.app (L.obj (q.obj P)) ≫ α.app (q.obj P))
    (K : D) : γ₁.app K ≫ θ.inv.app K = γ₂.app K := by
  have h' : ∀ K, γ₁.app (L.obj K) ≫ α.app K = γ₂.app (L.obj K) ≫ θ.hom.app (L.obj K) ≫ α.app K :=
    fun K => by
      obtain ⟨P, rfl⟩ := hq K
      exact h P
  have : γ₁ = γ₂ ≫ θ.hom := LF.leftDerived_ext α W G γ₁ (γ₂ ≫ θ.hom)
    (NatTrans.ext (funext fun K => by simpa using h' K))
  rw [this, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end CategoryTheory.Functor

/-- A diagram chase in a category: the shape of the composition law of the derived pullback-stalk
comparison on the image of the homotopy category. -/
theorem _root_.CategoryTheory.comp_chase_of_eq {E : Type*} [Category* E]
    {A B₁ B₂ B₃ M N Z C₁ C₂ D₁ : E} (lhs : A ⟶ Z) (Γ : A ⟶ M) (θ : M ⟶ N) (α : N ⟶ Z)
    (m₁ : A ⟶ B₁) (m₂ : B₁ ⟶ B₂) (m₃ : B₂ ⟶ B₃) (m₄ : B₃ ⟶ M)
    (hΓ : Γ = m₁ ≫ m₂ ≫ m₃ ≫ m₄)
    (n₁ : M ⟶ C₁) (n₂ : C₁ ⟶ C₂) (n₃ : C₂ ⟶ Z) (hθα : θ ≫ α = n₁ ≫ n₂ ≫ n₃)
    (p₁ : B₃ ⟶ D₁) (p₂ : D₁ ⟶ C₁) (hn : m₄ ≫ n₁ = p₁ ≫ p₂)
    (h₂ : B₂ ⟶ D₁) (hh₂ : m₃ ≫ p₁ = h₂) (h₁ : D₁ ⟶ C₂) (hh₁ : p₂ ≫ n₂ = h₁)
    (hL : lhs = m₁ ≫ m₂ ≫ h₂ ≫ h₁ ≫ n₃) :
    lhs = Γ ≫ θ ≫ α := by
  rw [hL, hΓ, hθα, ← hh₂, ← hh₁]
  simp only [Category.assoc]
  rw [reassoc_of% hn]

namespace CategoryTheory

/-- Moving isomorphisms across an equation of composites. -/
theorem comp_eq_of_comp_inv_eq {C : Type*} [Category* C] {A A' B D E : C} (a : A ⟶ B)
    (c : B ⟶ D) (h : D ⟶ E) (i : E ⟶ D) (t : A' ⟶ A) (t' : A ⟶ A') (c' : A' ⟶ E)
    (hT : a ≫ c ≫ h = t' ≫ c') (ht : t ≫ t' = 𝟙 _) (hi : h ≫ i = 𝟙 _) :
    t ≫ a ≫ c = c' ≫ i := by
  have : t ≫ a ≫ c = t ≫ (a ≫ c ≫ h) ≫ i := by simp [hi]
  rw [this, hT, ← Category.assoc, ← Category.assoc, ht, Category.id_comp]

/-- A diagram chase in a category: the shape of the composition law of the comparison of derived
with degreewise extension of scalars. -/
theorem comp_chase_of_eq₂ {C : Type*} [Category* C] {A₀ A₁ A₂ B₁ B₂ B₃ B₄ B₅ M₁ M₂ M₃ Z : C}
    (x : A₀ ⟶ A₁) (y : A₁ ⟶ A₂) (c : A₂ ⟶ M₁) (k : M₁ ⟶ M₂) (l : M₂ ⟶ M₃) (r : M₃ ⟶ Z)
    (t : A₀ ⟶ B₁) (a₁ : B₁ ⟶ B₂) (a₂ : B₂ ⟶ B₃) (a₃ : B₃ ⟶ B₄) (a₄ : B₄ ⟶ B₅) (i : B₅ ⟶ B₅)
    (c₁ : B₅ ⟶ M₃) (t' : A₁ ⟶ B₂) (t'' : A₂ ⟶ B₃) (c₁' : B₄ ⟶ M₂)
    (hi : i = 𝟙 _) (hn₁ : t ≫ a₁ = x ≫ t') (hn₂ : t' ≫ a₂ = y ≫ t'')
    (hT : t'' ≫ a₃ ≫ c₁' = c ≫ k) (hc : a₄ ≫ c₁ = c₁' ≫ l) :
    x ≫ y ≫ c ≫ k ≫ l ≫ r = t ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ i ≫ c₁ ≫ r := by
  rw [hi, Category.id_comp, reassoc_of% hc, reassoc_of% hn₁, reassoc_of% hn₂, reassoc_of% hT]

end CategoryTheory

namespace CochainComplex.DerivedExtensionScalars

/-- The composition law of the comparison of derived with degreewise extension of scalars,
followed by identifications of complexes: the chase behind the composition law of the derived
pullback-stalk comparison. -/
theorem comparison_comp_chase {R₀ R' R'' : CommRingCat.{u}}
    {𝒜₀ 𝒜' : Type*} {cat₀ : Category 𝒜₀} {cat' : Category 𝒜'} {pre₀ : Preadditive 𝒜₀}
    {pre' : Preadditive 𝒜'}
    (F₀ : 𝒜₀ ⥤ ModuleCat.{u} R₀) {hF₀ : F₀.Additive} (F' : 𝒜' ⥤ ModuleCat.{u} R')
    {hF' : F'.Additive} (P : CochainComplex 𝒜₀ ℤ) (P' : CochainComplex 𝒜' ℤ)
    (ρ₂ σ₂ : R₀ →+* R') (ρ₁ σ₁ : R' →+* R'') (ρ₁₂ σ₁₂ : R₀ →+* R'')
    (h₂ : ρ₂ = σ₂) (h₁ : ρ₁ = σ₁) (h₁₂ : ρ₁₂ = σ₁₂) (hρ : ρ₁₂ = ρ₁.comp ρ₂)
    (hσ : σ₁₂ = σ₁.comp σ₂)
    (c₂ : (totalDerivedExtensionScalars.{u, u, u} ρ₂).functor.obj (DerivedCategory.Q.obj
        ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶
      DerivedCategory.Q.obj (((ModuleCat.extendScalars ρ₂).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
    (hc₂ : c₂ = (totalDerivedExtensionScalars.{u, u, u} ρ₂).comparison.app
      ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (c₁ : (totalDerivedExtensionScalars.{u, u, u} ρ₁).functor.obj (DerivedCategory.Q.obj
        ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P')) ⟶
      DerivedCategory.Q.obj (((ModuleCat.extendScalars ρ₁).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P')))
    (hc₁ : c₁ = (totalDerivedExtensionScalars.{u, u, u} ρ₁).comparison.app
      ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P'))
    (c₁₂ : (totalDerivedExtensionScalars.{u, u, u} ρ₁₂).functor.obj (DerivedCategory.Q.obj
        ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶
      DerivedCategory.Q.obj (((ModuleCat.extendScalars ρ₁₂).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
    (hc₁₂ : c₁₂ = (totalDerivedExtensionScalars.{u, u, u} ρ₁₂).comparison.app
      ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    {E₀ E₀' : DerivedCategory (ModuleCat.{u} R₀)} (x₀ : E₀ ⟶ E₀')
    (y₀ : E₀' ⟶ DerivedCategory.Q.obj ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (π₂ : ((ModuleCat.extendScalars σ₂).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
        (F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P')
    {E₂ E₂' E₂'' : DerivedCategory (ModuleCat.{u} R')}
    (u₂ : DerivedCategory.Q.obj ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P') ⟶ E₂)
    (v₂ : E₂ ⟶ E₂') (w₂ : E₂' ⟶ E₂'') (x' : E₂'' ⟶ E₂)
    (y' : E₂ ⟶ DerivedCategory.Q.obj ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P'))
    (hab : u₂ ≫ v₂ ≫ w₂ ≫ x' ≫ y' = 𝟙 _)
    {S'' S₁₂ : CochainComplex (ModuleCat.{u} R'') ℤ}
    (π₁ : ((ModuleCat.extendScalars σ₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P') ⟶ S'')
    (π₁₂ : ((ModuleCat.extendScalars σ₁₂).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶ S₁₂) (ψ : S'' ⟶ S₁₂)
    (hπ : π₁₂ = eqToHom (congrArg (fun χ => ((ModuleCat.extendScalars χ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) hσ) ≫
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp σ₂ σ₁)
        (ComplexShape.up ℤ)).hom.app ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
      ((ModuleCat.extendScalars σ₁).mapHomologicalComplex (ComplexShape.up ℤ)).map π₂ ≫ π₁ ≫ ψ)
    {E₁ E₁' E₁'' E₁₂ E₁₂' E₁₂'' : DerivedCategory (ModuleCat.{u} R'')}
    (u₁ : DerivedCategory.Q.obj S'' ⟶ E₁) (v₁ : E₁ ⟶ E₁') (w₁ : E₁' ⟶ E₁'') (ω : E₁'' ⟶ E₁₂'')
    (u₁₂ : DerivedCategory.Q.obj S₁₂ ⟶ E₁₂) (v₁₂ : E₁₂ ⟶ E₁₂') (w₁₂ : E₁₂' ⟶ E₁₂'')
    (hω : u₁ ≫ v₁ ≫ w₁ ≫ ω = DerivedCategory.Q.map ψ ≫ u₁₂ ≫ v₁₂ ≫ w₁₂) :
    ((totalDerivedExtensionScalars.{u, u, u} ρ₁₂).functor.map x₀ ≫
        (totalDerivedExtensionScalars.{u, u, u} ρ₁₂).functor.map y₀) ≫
        c₁₂ ≫ ((eqToIso (congrArg (fun φ => F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q) h₁₂)).hom.app P ≫ DerivedCategory.Q.map π₁₂ ≫ u₁₂ ≫ v₁₂ ≫ w₁₂ :
          DerivedCategory.Q.obj (((ModuleCat.extendScalars ρ₁₂).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶ _) =
      eqToHom (congrArg (fun φ => (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj E₀) hρ) ≫
        (totalDerivedExtensionScalarsComp.{u, u} ρ₂ ρ₁).inv.app E₀ ≫
        (totalDerivedExtensionScalars.{u, u, u} ρ₁).functor.map
          (((totalDerivedExtensionScalars.{u, u, u} ρ₂).functor.map x₀ ≫
            (totalDerivedExtensionScalars.{u, u, u} ρ₂).functor.map y₀) ≫
            c₂ ≫ ((eqToIso (congrArg (fun φ => F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q) h₂)).hom.app P ≫ DerivedCategory.Q.map π₂ ≫ u₂ ≫ v₂ ≫ w₂ :
          DerivedCategory.Q.obj (((ModuleCat.extendScalars ρ₂).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶ _)) ≫
        (((totalDerivedExtensionScalars.{u, u, u} ρ₁).functor.map x' ≫
          (totalDerivedExtensionScalars.{u, u, u} ρ₁).functor.map y') ≫
          c₁ ≫ ((eqToIso (congrArg (fun φ => F'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q) h₁)).hom.app P' ≫ DerivedCategory.Q.map π₁ ≫ u₁ ≫ v₁ ≫ w₁ :
          DerivedCategory.Q.obj (((ModuleCat.extendScalars ρ₁).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P')) ⟶
              _)) ≫ ω := by
  subst h₂ h₁ h₁₂ hρ
  simp only [Category.assoc]
  have hT := totalDerivedExtensionScalarsComp_comparison.{u, u} ρ₂ ρ₁
    ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  have hc := (totalDerivedExtensionScalars.{u, u, u} ρ₁).comparison.naturality π₂
  rw [← hc₂, ← hc₁₂] at hT
  rw [← hc₁] at hc
  have hab' := congrArg (totalDerivedExtensionScalars.{u, u, u} ρ₁).functor.map hab
  simp only [Functor.map_comp] at hab'
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Functor.comp_obj, eqToHom_refl,
    Category.id_comp, Category.assoc, Functor.map_comp, hω, hπ,
    reassoc_of% hab'] at hc ⊢
  exact CategoryTheory.comp_chase_of_eq₂ _ _ _
    ((extensionOfScalarsComplexComp ρ₂ ρ₁).hom.app
      ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) _ _ _ _ _ _ _ _ _
    ((totalDerivedExtensionScalarsComp.{u, u} ρ₂ ρ₁).inv.app E₀')
    ((totalDerivedExtensionScalarsComp.{u, u} ρ₂ ρ₁).inv.app _)
    ((totalDerivedExtensionScalars.{u, u, u} ρ₁).comparison.app
        (((ModuleCat.extendScalars ρ₂).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
    (CategoryTheory.Functor.map_id _ _)
    ((totalDerivedExtensionScalarsComp.{u, u} ρ₂ ρ₁).inv.naturality x₀).symm
    ((totalDerivedExtensionScalarsComp.{u, u} ρ₂ ρ₁).inv.naturality y₀).symm
    (CategoryTheory.comp_eq_of_comp_inv_eq _ _ _ _ _ _ _ hT (Iso.inv_hom_id_app _ _)
      (Iso.inv_hom_id_app _ _)) hc

end CochainComplex.DerivedExtensionScalars

namespace CochainComplex.DerivedExtensionScalars

/-- A degreewise composition law for the extension-of-scalars comparisons of three functors to
modules gives the composition law of the induced comparisons of complexes. -/
theorem mapHomologicalComplex_comp_inv_app_eq {R₀ R' R'' : CommRingCat.{u}}
    {𝒜 𝒜' 𝒜'' : Type*} {cat : Category 𝒜} {cat' : Category 𝒜'} {cat'' : Category 𝒜''}
    {pre : Preadditive 𝒜} {pre' : Preadditive 𝒜'} {pre'' : Preadditive 𝒜''}
    (p₂ : 𝒜 ⥤ 𝒜') (p₁ : 𝒜' ⥤ 𝒜'') (p₁₂' p₁₂ : 𝒜 ⥤ 𝒜'') [p₂.Additive] [p₁.Additive]
    [p₁₂'.Additive] [p₁₂.Additive]
    (F₀ : 𝒜 ⥤ ModuleCat.{u} R₀) (F' : 𝒜' ⥤ ModuleCat.{u} R') (F'' : 𝒜'' ⥤ ModuleCat.{u} R'')
    [F₀.Additive] [F'.Additive] [F''.Additive]
    (σ₂ : R₀ →+* R') (σ₁ : R' →+* R'') (σ₁₂ : R₀ →+* R'') (hσ : σ₁₂ = σ₁.comp σ₂)
    (s₂ : p₂ ⋙ F' ≅ F₀ ⋙ ModuleCat.extendScalars σ₂)
    (s₁ : p₁ ⋙ F'' ≅ F' ⋙ ModuleCat.extendScalars σ₁)
    (s₁₂ : p₁₂ ⋙ F'' ≅ F₀ ⋙ ModuleCat.extendScalars σ₁₂)
    (e₁ : p₂ ⋙ p₁ ≅ p₁₂') (e₂ : p₁₂' ≅ p₁₂)
    (hP1 : ∀ M, s₁₂.inv.app M =
      eqToHom (congrArg (fun χ => (ModuleCat.extendScalars χ).obj (F₀.obj M)) hσ) ≫
        (ModuleCat.extendScalarsComp σ₂ σ₁).hom.app _ ≫
        (ModuleCat.extendScalars σ₁).map (s₂.inv.app M) ≫ s₁.inv.app (p₂.obj M) ≫
        F''.map ((e₁ ≪≫ e₂).hom.app M))
    (ρ₂ : p₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F'.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars σ₂).mapHomologicalComplex (ComplexShape.up ℤ))
    (hρ₂ : ρ₂ = Functor.mapHomologicalComplexCompIso s₂ (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F₀ ⋙ ModuleCat.extendScalars σ₂))
        (ComplexShape.up ℤ)).symm)
    (ρ₁ : p₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F''.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars σ₁).mapHomologicalComplex (ComplexShape.up ℤ))
    (hρ₁ : ρ₁ = Functor.mapHomologicalComplexCompIso s₁ (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F' ⋙ ModuleCat.extendScalars σ₁))
        (ComplexShape.up ℤ)).symm)
    (ρ₁₂ : p₁₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F''.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars σ₁₂).mapHomologicalComplex (ComplexShape.up ℤ))
    (hρ₁₂ : ρ₁₂ = Functor.mapHomologicalComplexCompIso s₁₂ (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F₀ ⋙ ModuleCat.extendScalars σ₁₂))
        (ComplexShape.up ℤ)).symm)
    (P : CochainComplex 𝒜 ℤ) :
    ρ₁₂.inv.app P = eqToHom (congrArg (fun χ => ((ModuleCat.extendScalars χ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) hσ) ≫
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp σ₂ σ₁)
        (ComplexShape.up ℤ)).hom.app ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
      ((ModuleCat.extendScalars σ₁).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (ρ₂.inv.app P) ≫ ρ₁.inv.app ((p₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
      (F''.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso e₁ (ComplexShape.up ℤ)).hom.app P ≫
          (NatTrans.mapHomologicalComplex e₂.hom (ComplexShape.up ℤ)).app P) := by
  subst hσ hρ₂ hρ₁ hρ₁₂
  ext n : 1
  simp only [eqToHom_refl, Category.id_comp, HomologicalComplex.comp_f,
    NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, NatTrans.mapHomologicalComplex_app_f, hP1,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.map_comp,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_hom, NatTrans.id_app,
    Category.assoc, Functor.comp_obj, Category.id_comp]
  simp

end CochainComplex.DerivedExtensionScalars

namespace CategoryTheory.Functor


/-- A composite of two functors sends an identity, given as any morphism equal to it, to an
identity. -/
theorem map_map_eq_id {C D E : Type*} [Category* C] [Category* D] [Category* E] (F : C ⥤ D)
    (G : D ⥤ E) {X : C} (i : X ⟶ X) (hi : i = 𝟙 X) : G.map (F.map i) = 𝟙 _ := by
  subst hi
  simp



/-- Replacing the outer factors of a composite by equal morphisms. -/
theorem comp_comp_congr {C : Type*} [Category* C] {W X Y Z : C} {a a' : W ⟶ X} (c : X ⟶ Y)
    {b b' : Y ⟶ Z} (ha : a = a') (hb : b = b') : a ≫ c ≫ b = a' ≫ c ≫ b' := by
  subst ha hb
  rfl

/-- Replacing two factors of a composite by equal morphisms. -/
theorem comp_map_comp_congr {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B M Z : D} {X Y : C} (a : A ⟶ B) (b : B ⟶ F.obj X) {m m' : X ⟶ Y} (hm : m = m')
    {n n' : F.obj Y ⟶ M} (hn : n = n') (c : M ⟶ Z) :
    a ≫ b ≫ F.map m ≫ n ≫ c = a ≫ b ≫ F.map m' ≫ n' ≫ c := by
  subst hm hn
  rfl

/-- The isomorphism on homotopy categories induced by `F ⋙ G ≅ H` followed by the one induced by
`H ≅ H'`, at the class of a complex: the class of the composite map of complexes. -/
theorem mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso_hom_app_quotient_obj
    {A B C : Type*} {catA : Category A} {catB : Category B} {catC : Category C}
    {preA : Preadditive A} {preB : Preadditive B} {preC : Preadditive C} {F : A ⥤ B} {G : B ⥤ C}
    {H H' : A ⥤ C} {hF : F.Additive} {hG : G.Additive} {hH : H.Additive} {hH' : H'.Additive}
    (e₁ : F ⋙ G ≅ H) (e₂ : H ≅ H') (K : CochainComplex A ℤ) :
    (Functor.mapHomotopyCategoryCompIso e₁ (ComplexShape.up ℤ) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso e₂ (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso e₁ (ComplexShape.up ℤ)).hom.app K ≫
          (NatTrans.mapHomologicalComplex e₂.hom (ComplexShape.up ℤ)).app K) :=
  ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _).symm

/-- The identification of the derived image of a complex with the image of the complex, followed
by its inverse through an identity. -/
theorem mapDerivedCategoryFactors_inv_app_comp_cancel {𝒜' ℬ : Type*}
    {cat : Category 𝒜'} {catB : Category ℬ} {ab : Abelian 𝒜'} {abB : Abelian ℬ}
    {hd : HasDerivedCategory 𝒜'} {hdB : HasDerivedCategory ℬ}
    (F : 𝒜' ⥤ ℬ) {hF : F.Additive} {hl : PreservesFiniteLimits F} {hc : PreservesFiniteColimits F}
    (M : CochainComplex 𝒜' ℤ)
    (w : F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) ⟶
      F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M))) (hw : w = 𝟙 _) :
    F.mapDerivedCategoryFactors.inv.app M ≫
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso 𝒜').inv.app M) ≫ (w ≫
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso 𝒜').hom.app M) ≫
      F.mapDerivedCategoryFactors.hom.app M : F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) ⟶ _) = 𝟙 _ := by
  subst hw
  rw [Category.id_comp, ← F.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]

/-- Naturality of the inverse identification of the derived image of a complex with the image of
the complex, along a morphism of the homotopy category induced by a morphism of complexes. -/
theorem mapDerivedCategoryFactors_inv_app_comp_quotient_map {𝒜'' ℬ : Type*}
    {cat : Category 𝒜''} {catB : Category ℬ} {ab : Abelian 𝒜''} {abB : Abelian ℬ}
    {hd : HasDerivedCategory 𝒜''} {hdB : HasDerivedCategory ℬ}
    (F : 𝒜'' ⥤ ℬ) {hF : F.Additive} {hl : PreservesFiniteLimits F} {hc : PreservesFiniteColimits F}
    (M N : CochainComplex 𝒜'' ℤ) (Ψ : M ⟶ N)
    (w₁ : F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) ⟶
      F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M))) (hw₁ : w₁ = 𝟙 _)
    (w₁₂ : F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ⟶
      F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N))) (hw₁₂ : w₁₂ = 𝟙 _)
    (π : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M ⟶
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)
    (hπ : π = (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map Ψ) :
    F.mapDerivedCategoryFactors.inv.app M ≫
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso 𝒜'').inv.app M) ≫ (w₁ ≫
      F.mapDerivedCategory.map (DerivedCategory.Qh.map π) :
        F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) ⟶ _) =
    DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map Ψ) ≫
      F.mapDerivedCategoryFactors.inv.app N ≫
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso 𝒜'').inv.app N) ≫
        (w₁₂ : F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ⟶
          F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N))) := by
  subst hw₁ hw₁₂ hπ
  dsimp only [Functor.comp_obj]
  rw [Category.id_comp, Category.comp_id, ← F.mapDerivedCategory.map_comp,
    ← DerivedCategory.quotientCompQhIso_inv_naturality, F.mapDerivedCategory.map_comp]
  have := F.mapDerivedCategoryFactors.inv.naturality Ψ
  dsimp only [Functor.comp_obj, Functor.comp_map] at this
  rw [reassoc_of% this]

/-- Naturality of the inverse identification of the derived image of a complex with the image of
the complex, along the isomorphism of homotopy categories induced by `p₂ ⋙ p₁ ≅ p₁₂' ≅ p₁₂`. -/
theorem mapDerivedCategoryFactors_inv_app_comp_map {𝒜 𝒜' 𝒜'' ℬ : Type*}
    {cat : Category 𝒜} {cat' : Category 𝒜'} {cat'' : Category 𝒜''} {catB : Category ℬ}
    {pre : Preadditive 𝒜} {pre' : Preadditive 𝒜'} {ab : Abelian 𝒜''} {abB : Abelian ℬ}
    {hd : HasDerivedCategory 𝒜''} {hdB : HasDerivedCategory ℬ}
    (p₂ : 𝒜 ⥤ 𝒜') (p₁ : 𝒜' ⥤ 𝒜'') (p₁₂' p₁₂ : 𝒜 ⥤ 𝒜'') [hp₂ : p₂.Additive] [hp₁ : p₁.Additive]
    [hp₁₂' : p₁₂'.Additive] [hp₁₂ : p₁₂.Additive]
    (F : 𝒜'' ⥤ ℬ) {hF : F.Additive} {hl : PreservesFiniteLimits F} {hc : PreservesFiniteColimits F}
    (e₁ : p₂ ⋙ p₁ ≅ p₁₂') (e₂ : p₁₂' ≅ p₁₂) (P : CochainComplex 𝒜 ℤ)
    (w₁ : F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ((p₁.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((p₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) ⟶
      F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ((p₁.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((p₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))))
    (hw₁ : w₁ = 𝟙 _)
    (w₁₂ : F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((p₁₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ⟶
      F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((p₁₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))))
    (hw₁₂ : w₁₂ = 𝟙 _) :
    F.mapDerivedCategoryFactors.inv.app ((p₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((p₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso 𝒜'').inv.app
        ((p₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((p₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫ (w₁ ≫
      F.mapDerivedCategory.map (DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso e₁ (ComplexShape.up ℤ) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso e₂ (ComplexShape.up ℤ)).hom.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) :
        F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ((p₁.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((p₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) ⟶ _) =
    DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso e₁ (ComplexShape.up ℤ)).hom.app P ≫
          (NatTrans.mapHomologicalComplex e₂.hom (ComplexShape.up ℤ)).app P)) ≫
      F.mapDerivedCategoryFactors.inv.app ((p₁₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso 𝒜'').inv.app
        ((p₁₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫ w₁₂ := by
  rw [mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso_hom_app_quotient_obj]
  exact mapDerivedCategoryFactors_inv_app_comp_quotient_map F _ _ _ w₁ hw₁ w₁₂ hw₁₂ _ rfl

end CategoryTheory.Functor
