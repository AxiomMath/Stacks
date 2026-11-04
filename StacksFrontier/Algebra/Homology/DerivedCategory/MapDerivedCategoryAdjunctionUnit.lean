module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# The unit of a degreewise derived adjunction, read on the homotopy category

Let `adj : F ⊣ G` be an adjunction of exact additive functors between abelian categories with
derived categories, and let `CategoryTheory.Adjunction.mapDerivedCategory` be the induced
adjunction `D(F) ⊣ D(G)` on unbounded derived categories. Its unit at the image under
`DerivedCategory.Q` of a complex is `CategoryTheory.mapDerivedCategoryAdjunction_unit_app_Q`.
This file computes its unit at the image under `DerivedCategory.Qh` of an object of the homotopy
category, in the form of the factorization `CategoryTheory.Adjunction.derivedη_fac_app` of the
unit of a derived adjunction in the sense of Maltsiniotis. It also shows that an adjunction whose
left adjoint composed with its right adjoint is a left derived functor is determined by such a
factorization of its unit.

## Main results

* `CategoryTheory.mapDerivedCategoryAdjunction_unit_app_Qh`: the unit of
  `CategoryTheory.Adjunction.mapDerivedCategory adj` at the image of an object of the homotopy
  category, read through the comparisons `CategoryTheory.Functor.mapDerivedCategoryFactorsh`, is
  the unit of the adjunction on homotopy categories.
* `CategoryTheory.Adjunction.eq_of_unit_comp_eq`: two adjunctions between the same pair of
  functors whose units agree after the comparison of a left derived functor are equal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Adjunction

/-! ### Uniqueness of an adjunction from the factorization of its unit -/

section Uniqueness

variable {C₁ : Type u₁} [Category.{v₁} C₁] {D₁ : Type u₂} [Category.{v₂} D₁]
  {C₂ : Type u₃} [Category.{v₃} C₂] {D₂ : Type u₄} [Category.{v₄} D₂]
  {L₁ : C₁ ⥤ D₁} {G' : D₁ ⥤ D₂} {F' : D₂ ⥤ D₁} {G : C₁ ⥤ C₂} {L₂ : C₂ ⥤ D₂}

/-- **Two adjunctions between the same pair of functors whose units agree after the comparison of
a left derived functor are equal.** -/
theorem eq_of_unit_comp_eq (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
    (α : L₁ ⋙ G' ⟶ G ⋙ L₂)
    [(G' ⋙ F').IsLeftDerivedFunctor
      ((Functor.associator L₁ G' F').inv ≫ Functor.whiskerRight α F') W₁]
    (adj₁ adj₂ : G' ⊣ F')
    (h : ∀ X : C₁, adj₁.unit.app (L₁.obj X) ≫ F'.map (α.app X) =
      adj₂.unit.app (L₁.obj X) ≫ F'.map (α.app X)) :
    adj₁ = adj₂ := by
  refine Adjunction.ext ((G' ⋙ F').leftDerived_ext
    ((Functor.associator L₁ G' F').inv ≫ Functor.whiskerRight α F') W₁ (𝟭 D₁)
    adj₁.unit adj₂.unit ?_)
  ext X
  simpa using h X

end Uniqueness

/-! ### Reversing a transport of an adjunction along two natural isomorphisms -/

section Transport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **Transporting an adjunction along two natural isomorphisms is reversed by transporting it
back along their inverses.** -/
theorem ofNatIsoLeft_ofNatIsoRight_symm {F F' : C ⥤ D} {G G' : D ⥤ C} (adj : F ⊣ G)
    (adj' : F' ⊣ G') (e : F ≅ F') (f : G' ≅ G)
    (h : adj = (adj'.ofNatIsoLeft e.symm).ofNatIsoRight f) :
    (adj.ofNatIsoLeft e).ofNatIsoRight f.symm = adj' := by
  subst h
  refine Adjunction.ext ?_
  ext Z
  simp

end Transport

/-! ### Two identities between composites of morphisms -/

section Chase

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]

/-- Given functors `Ψ : 𝒞 ⥤ 𝒟` and `Φ : 𝒟 ⥤ 𝒞`, a square
`v ≫ Φ.map (Ψ.map t) = t ≫ u ≫ b ≫ Φ.map a'` and left inverses `a` of `a'` and `e` of `e'`, the
composites `v ≫ Φ.map (Ψ.map t ≫ a ≫ c)` and `(t ≫ u ≫ e') ≫ e ≫ b ≫ Φ.map c` are equal. -/
theorem unitChase (Ψ : 𝒞 ⥤ 𝒟) (Φ : 𝒟 ⥤ 𝒞) {X Y N N' : 𝒞} {M W : 𝒟}
    (t : X ⟶ Y) (v : X ⟶ Φ.obj (Ψ.obj X)) (u : Y ⟶ N) (b : N ⟶ Φ.obj M)
    (a : Ψ.obj Y ⟶ M) (a' : M ⟶ Ψ.obj Y) (c : M ⟶ W) (e : N' ⟶ N) (e' : N ⟶ N')
    (hv : v ≫ Φ.map (Ψ.map t) = t ≫ u ≫ b ≫ Φ.map a')
    (ha : a' ≫ a = 𝟙 M) (he : e' ≫ e = 𝟙 N) :
    v ≫ Φ.map (Ψ.map t ≫ a ≫ c) = (t ≫ u ≫ e') ≫ e ≫ b ≫ Φ.map c := by
  rw [Φ.map_comp, Φ.map_comp, ← Category.assoc v, hv]
  simp only [Category.assoc]
  rw [← Category.assoc (Φ.map a') (Φ.map a), ← Φ.map_comp, ha, Φ.map_id, Category.id_comp,
    ← Category.assoc e' e, he, Category.id_comp]

/-- Given a natural transformation `r : Φ ⟶ Φ'`, morphisms with `Φ.map l' ≫ Φ.map l = 𝟙 _` and a
square `u ≫ Φ.map f = w ≫ s`, the composites `u ≫ Φ.map l' ≫ r.app V' ≫ Φ'.map (l ≫ f)` and
`w ≫ s ≫ r.app W` are equal. -/
theorem comparisonChase {Φ Φ' : 𝒟 ⥤ 𝒞} (r : Φ ⟶ Φ') {Z N : 𝒞} {V V' W : 𝒟}
    (u : Z ⟶ Φ.obj V) (l : V' ⟶ V) (l' : V ⟶ V') (f : V ⟶ W) (w : Z ⟶ N) (s : N ⟶ Φ.obj W)
    (hl : Φ.map l' ≫ Φ.map l = 𝟙 (Φ.obj V)) (hu : u ≫ Φ.map f = w ≫ s) :
    u ≫ Φ.map l' ≫ r.app V' ≫ Φ'.map (l ≫ f) = w ≫ s ≫ r.app W := by
  have h₁ : r.app V' ≫ Φ'.map l ≫ Φ'.map f = Φ.map l ≫ r.app V ≫ Φ'.map f := by
    rw [← Category.assoc, ← r.naturality l, Category.assoc]
  rw [Φ'.map_comp, h₁, (r.naturality f).symm, ← Category.assoc (Φ.map l') (Φ.map l), hl,
    Category.id_comp, ← Category.assoc u, hu, Category.assoc]

end Chase

end CategoryTheory.Adjunction

namespace CategoryTheory

/-! ### The unit of `Adjunction.mapDerivedCategory` on the homotopy category -/

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- `CategoryTheory.mapDerivedCategoryAdjunction_unit_app_Qh` at the quotient of a cochain
complex `K`. -/
private theorem mapDerivedCategoryAdjunction_unit_app_Qh_quotient_obj (adj : F ⊣ G)
    (K : CochainComplex A ℤ) :
    adj.mapDerivedCategory.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).unit.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        G.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
  have hunit : DerivedCategory.Qh.map
        ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).unit.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app K)) := rfl
  have hv : adj.mapDerivedCategory.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        G.mapDerivedCategory.map
          (F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app K)) =
      (DerivedCategory.quotientCompQhIso A).hom.app K ≫
        DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app K) ≫
          G.mapDerivedCategoryFactors.inv.app
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
            G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
    rw [← mapDerivedCategoryAdjunction_unit_app_Q adj K]
    exact (adj.mapDerivedCategory.unit.naturality
      ((DerivedCategory.quotientCompQhIso A).hom.app K)).symm
  rw [← Functor.mapDerivedCategoryFactorsh_hom_app_quotient_obj F K, hunit,
    Functor.Qh_map_quotient_map,
    ← Functor.mapDerivedCategoryFactorsh_inv_app_quotient_obj G
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)]
  exact Adjunction.unitChase F.mapDerivedCategory G.mapDerivedCategory _ _ _ _ _ _ _ _ _ hv
    (F.mapDerivedCategoryFactors.inv_hom_id_app K)
    ((DerivedCategory.quotientCompQhIso A).inv_hom_id_app _)

/-- **The unit of the degreewise derived adjunction, at the image of an object of the homotopy
category.** For an adjunction `adj : F ⊣ G` of exact additive functors, the unit of
`CategoryTheory.Adjunction.mapDerivedCategory adj`, read through the comparisons
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the two derived functors, is the unit of
the adjunction `K(F) ⊣ K(G)` on homotopy categories. -/
theorem mapDerivedCategoryAdjunction_unit_app_Qh (adj : F ⊣ G)
    (M : HomotopyCategory A (ComplexShape.up ℤ)) :
    adj.mapDerivedCategory.unit.app (DerivedCategory.Qh.obj M) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app M) =
      DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).unit.app M) ≫
        G.mapDerivedCategoryFactorsh.inv.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) :=
  mapDerivedCategoryAdjunction_unit_app_Qh_quotient_obj adj M.as

end

end CategoryTheory

end
