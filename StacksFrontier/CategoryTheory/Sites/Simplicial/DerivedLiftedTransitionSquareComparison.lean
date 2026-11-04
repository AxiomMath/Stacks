module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedLiftedTransitionLeg

/-!
# The derived image of a transition square, through a total left derived functor

Let `Rn : T ⥤ A`, `Rm : T ⥤ B` and `Tf : T ⥤ T` be exact functors, let `P : A ⥤ B` be an additive
functor which need not be exact, and let `τ : Rn ⋙ P ⟶ Rm`, `adj : Rn ⟶ Tf ⋙ Rn` and
`chain : Rm ⟶ Tf ⋙ Rm` be transformations satisfying the square

  `P(adj_M) ≫ τ_{Tf M} = τ_M ≫ chain_M`.

Given any functor `LP : D(A) ⥤ D(B)` with a comparison `cmp : Qh ⋙ LP ⟶ K(P) ⋙ Qh` — for instance
the total left derived functor of `P` with its canonical comparison — the transition
`Rn^D ⋙ LP ⟶ Rm^D` lifted from `τ` along the localization of the homotopy category satisfies the
derived square. `CategoryTheory.liftedTransition_square` is the special case of an exact `P`,
read through an identification of `LP` with the derived functor of `P`; here no such
identification, and no invertibility of `cmp`, is needed.

## Main results

* `CategoryTheory.mapHomotopyCategoryTransition_square`: the square on homotopy categories.
* `CategoryTheory.derivedCompIso_refl_hom_app_Qh`: the compositor of derived functors of exact
  functors, on the image of the localization of the homotopy category.
* `CategoryTheory.liftedTransition_square_of_comparison`: the transition lifted from `τ` satisfies
  the derived square.

## References

* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {T : Type u₁} {A : Type u₂} {B : Type u₃}
  [Category.{v₁} T] [Category.{v₂} A] [Category.{v₃} B]
  [Abelian T] [Abelian A] [Abelian B]
  (Tf : T ⥤ T) (Rn : T ⥤ A) (Rm : T ⥤ B) (P : A ⥤ B)
  [Tf.Additive] [Rn.Additive] [Rm.Additive] [P.Additive]

/-- **A transition square on homotopy categories.** The square
`P(adj_M) ≫ τ_{Tf M} = τ_M ≫ chain_M` of additive functors, applied degreewise, holds on the
homotopy category of complexes. -/
theorem mapHomotopyCategoryTransition_square
    (adj : Rn ⟶ Tf ⋙ Rn) (τ : Rn ⋙ P ⟶ Rm) (chain : Rm ⟶ Tf ⋙ Rm)
    (hsq : ∀ M : T, P.map (adj.app M) ≫ τ.app (Tf.obj M) = τ.app M ≫ chain.app M)
    (X : HomotopyCategory T (ComplexShape.up ℤ)) :
    (P.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomotopyCategory adj (ComplexShape.up ℤ)).app X) ≫
        (mapHomotopyCategoryTransition (ComplexShape.up ℤ) Rn P Rm τ).app
          ((Tf.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) =
      (mapHomotopyCategoryTransition (ComplexShape.up ℤ) Rn P Rm τ).app X ≫
        (NatTrans.mapHomotopyCategory chain (ComplexShape.up ℤ)).app X := by
  rw [mapHomotopyCategoryTransition_app, mapHomotopyCategoryTransition_app]
  exact (Functor.map_comp _ _ _).symm.trans ((congrArg (HomotopyCategory.quotient B
    (ComplexShape.up ℤ)).map (HomologicalComplex.hom_ext _ _ fun i => hsq (X.as.X i))).trans
      (Functor.map_comp _ _ _))

/-- Cancelling three factors against their inverses, over abstract morphisms. -/
private theorem comp_three_inv {C : Type*} [Category C] {X₀ X₁ X₂ X₃ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (c' : X₃ ⟶ X₂) (b' : X₂ ⟶ X₁) (a' : X₁ ⟶ X₀)
    (ha : a ≫ a' = 𝟙 _) (hb : b ≫ b' = 𝟙 _) (hc : c ≫ c' = 𝟙 _) :
    (a ≫ b ≫ c) ≫ c' ≫ b' ≫ a' = 𝟙 _ := by
  simp only [Category.assoc, reassoc_of% hc, reassoc_of% hb, ha]

/-- An identity between two composites through a functor `L`, from relations among the factors.
-/
private theorem square_chase {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {c₀ c₁ c₂ c₃ c₄ c₅ : C} {e₀ e₄ e₅ e₆ f₁ f₂ g₁ g₂ : D}
    (nF : c₀ ⟶ c₁) (qa : c₁ ⟶ c₂) (eTi : c₂ ⟶ c₃) (eT : c₃ ⟶ c₂) (y : c₄ ⟶ c₂) (y' : c₂ ⟶ c₄)
    (z : c₄ ⟶ c₅) (dT₀ : L.obj c₀ ⟶ e₀) (dT₁ : L.obj c₅ ⟶ e₅) (dT₂ : L.obj c₄ ⟶ e₄)
    (w : e₄ ⟶ e₅) (cmp' : L.obj c₂ ⟶ f₁) (qt' : f₁ ⟶ f₂) (ei' : f₂ ⟶ e₄)
    (cmp : L.obj c₁ ⟶ g₁) (qP : g₁ ⟶ f₁) (qt : g₁ ⟶ g₂) (qc : g₂ ⟶ f₂) (ei : g₂ ⟶ e₀)
    (eh : e₀ ⟶ g₂) (eTi' : f₂ ⟶ e₆) (eT' : e₆ ⟶ f₂)
    (hT : eTi ≫ eT = 𝟙 _) (hT' : eTi' ≫ eT' = 𝟙 _) (h₁ : L.map z ≫ dT₁ = dT₂ ≫ w)
    (h₂ : dT₂ = L.map y ≫ cmp' ≫ qt' ≫ ei') (h₃ : y' ≫ y = 𝟙 _)
    (h₄ : L.map qa ≫ cmp' = cmp ≫ qP) (h₅ : qP ≫ qt' = qt ≫ qc)
    (h₀ : dT₀ = L.map nF ≫ cmp ≫ qt ≫ ei) (h₆ : ei ≫ eh = 𝟙 _) :
    L.map ((nF ≫ qa ≫ eTi) ≫ eT ≫ y' ≫ z) ≫ dT₁ =
      dT₀ ≫ (eh ≫ qc ≫ eTi') ≫ eT' ≫ ei' ≫ w := by
  subst h₀ h₂
  simp only [Functor.map_comp, Category.assoc, reassoc_of% hT, reassoc_of% hT', h₁,
    reassoc_of% h₆]
  rw [← L.map_comp_assoc y' y, h₃, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% h₄, reassoc_of% h₅]

variable [HasDerivedCategory T] [HasDerivedCategory A] [HasDerivedCategory B]
  [PreservesFiniteLimits Tf] [PreservesFiniteColimits Tf]
  [PreservesFiniteLimits Rn] [PreservesFiniteColimits Rn]
  [PreservesFiniteLimits Rm] [PreservesFiniteColimits Rm]

/-- The compositor of derived functors of exact functors, on the image of the localization of
the homotopy category. -/
theorem derivedCompIso_refl_hom_app_Qh {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    (derivedCompIso F G (F ⋙ G) (Iso.refl _)).hom.app (DerivedCategory.Qh.obj X) =
      (F ⋙ G).mapDerivedCategoryFactorsh.hom.app X ≫
        G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.inv.app X) := by
  refine (cancel_epi ((derivedCompIso F G (F ⋙ G) (Iso.refl _)).inv.app
    (DerivedCategory.Qh.obj X))).1 ?_
  rw [Iso.inv_hom_id_app, derivedCompIso_refl_inv_eq,
    Stacks.DerivedFunctor.mapDerivedCategoryCompIso_hom_app_Qh]
  exact (comp_three_inv _ _ _ _ _ _
    ((G.mapDerivedCategory.map_comp _ _).symm.trans
      ((congrArg G.mapDerivedCategory.map (Iso.hom_inv_id_app F.mapDerivedCategoryFactorsh X)).trans
        (CategoryTheory.Functor.map_id _ _)))
    (Iso.hom_inv_id_app G.mapDerivedCategoryFactorsh
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj X))
    (Iso.inv_hom_id_app (F ⋙ G).mapDerivedCategoryFactorsh X)).symm

/-- **The derived image of a transition square, through a total left derived functor.** Let
`τ : Rn ⋙ P ⟶ Rm` be a transition, with `Rn`, `Rm` and `Tf` exact and `P` only additive, and let
`adj : Rn ⟶ Tf ⋙ Rn` and `chain : Rm ⟶ Tf ⋙ Rm` satisfy the square
`P(adj_M) ≫ τ_{Tf M} = τ_M ≫ chain_M`. For any functor `LP : D(A) ⥤ D(B)` with a comparison
`cmp : Qh ⋙ LP ⟶ K(P) ⋙ Qh`, the transition `dT : Rn^D ⋙ LP ⟶ Rm^D` lifted from `τ` satisfies the
same square one level up. -/
theorem liftedTransition_square_of_comparison
    (adj : Rn ⟶ Tf ⋙ Rn) (τ : Rn ⋙ P ⟶ Rm) (chain : Rm ⟶ Tf ⋙ Rm)
    (hsq : ∀ M : T, P.map (adj.app M) ≫ τ.app (Tf.obj M) = τ.app M ≫ chain.app M)
    {LP : DerivedCategory A ⥤ DerivedCategory B}
    (cmp : DerivedCategory.Qh ⋙ LP ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (dT : Rn.mapDerivedCategory ⋙ LP ⟶ Rm.mapDerivedCategory)
    (hdT : dT = liftedTransition Rn.mapDerivedCategoryFactorsh cmp Rm.mapDerivedCategoryFactorsh
      (mapHomotopyCategoryTransition (ComplexShape.up ℤ) Rn P Rm τ)
      (HomotopyCategory.quasiIso T (ComplexShape.up ℤ)))
    (K : DerivedCategory T) :
    LP.map ((derivedNatTrans Rn (Tf ⋙ Rn) adj).app K ≫
          (derivedCompIso Tf Rn (Tf ⋙ Rn) (Iso.refl _)).hom.app K) ≫
        dT.app (Tf.mapDerivedCategory.obj K) =
      dT.app K ≫ (derivedNatTrans Rm (Tf ⋙ Rm) chain).app K ≫
        (derivedCompIso Tf Rm (Tf ⋙ Rm) (Iso.refl _)).hom.app K := by
  have key : Functor.whiskerRight (derivedNatTrans Rn (Tf ⋙ Rn) adj ≫
        (derivedCompIso Tf Rn (Tf ⋙ Rn) (Iso.refl _)).hom) LP ≫
      Functor.whiskerLeft Tf.mapDerivedCategory dT =
      dT ≫ derivedNatTrans Rm (Tf ⋙ Rm) chain ≫
        (derivedCompIso Tf Rm (Tf ⋙ Rm) (Iso.refl _)).hom := by
    refine Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso T (ComplexShape.up ℤ)) fun X => ?_
    have hnat := dT.naturality (Tf.mapDerivedCategoryFactorsh.inv.app X)
    have hcmp := cmp.naturality ((NatTrans.mapHomotopyCategory adj (ComplexShape.up ℤ)).app X)
    have hhsq := (DerivedCategory.Qh.map_comp _ _).symm.trans ((congrArg DerivedCategory.Qh.map
      (mapHomotopyCategoryTransition_square Tf Rn Rm P adj τ chain hsq X)).trans
        (DerivedCategory.Qh.map_comp _ _))
    simp only [Functor.comp_map] at hnat hcmp
    subst hdT
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [derivedNatTrans_app_Qh, derivedNatTrans_app_Qh, derivedCompIso_refl_hom_app_Qh,
      derivedCompIso_refl_hom_app_Qh]
    exact square_chase LP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _) hnat
      (liftedTransition_app_q _ _ _ _ _ _) (Iso.inv_hom_id_app _ _) hcmp hhsq
      (liftedTransition_app_q _ _ _ _ _ _) (Iso.inv_hom_id_app _ _)
  exact congr_app key K

end CategoryTheory

end
