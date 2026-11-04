module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackTensorModels
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparisonAssociator
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedAssociatorComparison
public import StacksFrontier.CategoryTheory.Monoidal.ReseatComparison

/-!
# Tag 079U at the derived tensor product of the internal hom is monoidal

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  The comparison of Tag 079U,
`Lh^*(K ⊗^L L) ≅ Lh^*K ⊗^L Lh^*L`, carries the associativity constraint of Tag 0FPT on `D(𝒪_Y)`
to the one on `D(𝒪_X)`.  This file proves it at the derived tensor product the derived internal
hom is stated at, `Stacks.Cohomology.DerivedInternalHomPullback.pullbackTensorIso`, from the
statement at the derived tensor product of Tag 079U itself: both derived tensor products are
re-seatings of one monoidal structure on `D(𝒪_Z)`, the comparison `tensorBridge` of the two is
the comparison of the two re-seatings, and so it carries one associativity constraint to the
other.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.tensorBridge_hom_app_eq`: `tensorBridge` is the
  comparison of the two re-seatings.
* `Stacks.Cohomology.DerivedInternalHomPullback.pullbackTensorIso_associator`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomPullback

/-! ### Transport of the associativity axiom along comparisons of bifunctors -/

section Abstract

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂] (P : D₁ ⥤ D₂)
  {Ta₁ Tb₁ : D₁ × D₁ ⥤ D₁} {Ta₂ Tb₂ : D₂ × D₂ ⥤ D₂}
  (β₁ : Ta₁ ≅ Tb₁) (β₂ : Ta₂ ≅ Tb₂) (ma : Ta₁ ⋙ P ≅ P.prod P ⋙ Ta₂)
  (aa₁ : ∀ A B C : D₁, Ta₁.obj (Ta₁.obj (A, B), C) ⟶ Ta₁.obj (A, Ta₁.obj (B, C)))
  (ab₁ : ∀ A B C : D₁, Tb₁.obj (Tb₁.obj (A, B), C) ⟶ Tb₁.obj (A, Tb₁.obj (B, C)))
  (aa₂ : ∀ A B C : D₂, Ta₂.obj (Ta₂.obj (A, B), C) ⟶ Ta₂.obj (A, Ta₂.obj (B, C)))
  (ab₂ : ∀ A B C : D₂, Tb₂.obj (Tb₂.obj (A, B), C) ⟶ Tb₂.obj (A, Tb₂.obj (B, C)))

/-- Naturality of a transformation of bifunctors in its first variable. -/
@[reassoc]
private theorem nat_left {C D : Type*} [Category C] [Category D] {F G : C × C ⥤ D} (τ : F ⟶ G)
    {A A' : C} (f : A ⟶ A') (B : C) :
    τ.app (A, B) ≫ G.map (f ×ₘ 𝟙 B) = F.map (f ×ₘ 𝟙 B) ≫ τ.app (A', B) :=
  (τ.naturality (f ×ₘ 𝟙 B)).symm

/-- Naturality of a transformation of bifunctors in its second variable. -/
@[reassoc]
private theorem nat_right {C D : Type*} [Category C] [Category D] {F G : C × C ⥤ D}
    (τ : F ⟶ G) (A : C) {B B' : C} (g : B ⟶ B') :
    τ.app (A, B) ≫ G.map (𝟙 A ×ₘ g) = F.map (𝟙 A ×ₘ g) ≫ τ.app (A, B') :=
  (τ.naturality (𝟙 A ×ₘ g)).symm

/-- A threefold composite in the first variable of a bifunctor splits. -/
private theorem map_comp₃_left {C D : Type*} [Category C] [Category D] (F : C × C ⥤ D)
    {A₀ A₁ A₂ A₃ : C} (x : A₀ ⟶ A₁) (y : A₁ ⟶ A₂) (z : A₂ ⟶ A₃) (B : C) :
    F.map ((x ≫ y ≫ z) ×ₘ 𝟙 B) = F.map (x ×ₘ 𝟙 B) ≫ F.map (y ×ₘ 𝟙 B) ≫ F.map (z ×ₘ 𝟙 B) := by
  rw [← F.map_comp, ← F.map_comp, prod_comp, prod_comp, Category.comp_id, Category.comp_id]

/-- A threefold composite in the second variable of a bifunctor splits. -/
private theorem map_comp₃_right {C D : Type*} [Category C] [Category D] (F : C × C ⥤ D)
    (A : C) {B₀ B₁ B₂ B₃ : C} (x : B₀ ⟶ B₁) (y : B₁ ⟶ B₂) (z : B₂ ⟶ B₃) :
    F.map (𝟙 A ×ₘ (x ≫ y ≫ z)) = F.map (𝟙 A ×ₘ x) ≫ F.map (𝟙 A ×ₘ y) ≫ F.map (𝟙 A ×ₘ z) := by
  rw [← F.map_comp, ← F.map_comp, prod_comp, prod_comp, Category.comp_id, Category.comp_id]

/-- The monoidality comparison is natural in its first variable. -/
@[reassoc]
private theorem ma_left {A A' : D₁} (f : A ⟶ A') (B : D₁) :
    ma.hom.app (A, B) ≫ Ta₂.map (P.map f ×ₘ 𝟙 (P.obj B)) =
      P.map (Ta₁.map (f ×ₘ 𝟙 B)) ≫ ma.hom.app (A', B) := by
  simpa using nat_left ma.hom f B

/-- The monoidality comparison is natural in its second variable. -/
@[reassoc]
private theorem ma_right (A : D₁) {B B' : D₁} (g : B ⟶ B') :
    ma.hom.app (A, B) ≫ Ta₂.map (𝟙 (P.obj A) ×ₘ P.map g) =
      P.map (Ta₁.map (𝟙 A ×ₘ g)) ≫ ma.hom.app (A, B') := by
  simpa using nat_right ma.hom A g

/-- Inverting a square of isomorphisms. -/
private theorem conj_inv {C : Type*} [Category C] {S S' T T' : C} (u : S ⟶ S') (v : T ⟶ T')
    [IsIso u] [IsIso v] (a : S ⟶ T) (b : S' ⟶ T') (h : u ≫ b = a ≫ v) :
    inv u ≫ a = b ≫ inv v := by
  rw [IsIso.eq_comp_inv, Category.assoc, ← h, IsIso.inv_hom_id_assoc]

/-- **The associativity axiom of a monoidality comparison transports along comparisons of the
bifunctors.**  If `β₁`, `β₂` carry the associativity morphisms `aa` to `ab` on each side and `ma`
satisfies the associativity axiom for `aa`, then the conjugate `mb` of `ma` by `β₁` and `β₂`
satisfies it for `ab`. -/
theorem associator_of_conj (mb : Tb₁ ⋙ P ≅ P.prod P ⋙ Tb₂)
    (hmb : ∀ A B : D₁, mb.hom.app (A, B) =
      P.map (β₁.inv.app (A, B)) ≫ ma.hom.app (A, B) ≫ β₂.hom.app (P.obj A, P.obj B))
    (hconj₁ : ∀ A B C : D₁,
      β₁.inv.app (Tb₁.obj (A, B), C) ≫ Ta₁.map (β₁.inv.app (A, B) ×ₘ 𝟙 C) ≫ aa₁ A B C =
        ab₁ A B C ≫ β₁.inv.app (A, Tb₁.obj (B, C)) ≫ Ta₁.map (𝟙 A ×ₘ β₁.inv.app (B, C)))
    (hconj₂ : ∀ A B C : D₂,
      β₂.hom.app (Ta₂.obj (A, B), C) ≫ Tb₂.map (β₂.hom.app (A, B) ×ₘ 𝟙 C) ≫ ab₂ A B C =
        aa₂ A B C ≫ β₂.hom.app (A, Ta₂.obj (B, C)) ≫ Tb₂.map (𝟙 A ×ₘ β₂.hom.app (B, C)))
    (hassoc : ∀ A B C : D₁,
      ma.hom.app (Ta₁.obj (A, B), C) ≫ Ta₂.map (ma.hom.app (A, B) ×ₘ 𝟙 (P.obj C)) ≫
          aa₂ (P.obj A) (P.obj B) (P.obj C) =
        P.map (aa₁ A B C) ≫ ma.hom.app (A, Ta₁.obj (B, C)) ≫
          Ta₂.map (𝟙 (P.obj A) ×ₘ ma.hom.app (B, C)))
    (A B C : D₁) :
    mb.hom.app (Tb₁.obj (A, B), C) ≫ Tb₂.map (mb.hom.app (A, B) ×ₘ 𝟙 (P.obj C)) ≫
        ab₂ (P.obj A) (P.obj B) (P.obj C) =
      P.map (ab₁ A B C) ≫ mb.hom.app (A, Tb₁.obj (B, C)) ≫
        Tb₂.map (𝟙 (P.obj A) ×ₘ mb.hom.app (B, C)) := by
  have h₁ : P.map (β₁.inv.app (Tb₁.obj (A, B), C)) ≫ P.map (Ta₁.map (β₁.inv.app (A, B) ×ₘ 𝟙 C)) ≫
      P.map (aa₁ A B C) = P.map (ab₁ A B C) ≫ P.map (β₁.inv.app (A, Tb₁.obj (B, C))) ≫
        P.map (Ta₁.map (𝟙 A ×ₘ β₁.inv.app (B, C))) := by
    simp only [← P.map_comp]
    rw [hconj₁ A B C]
  rw [hmb, hmb, hmb, hmb, map_comp₃_left, map_comp₃_right]
  simp only [Category.assoc]
  dsimp only [Functor.comp_obj, Functor.prod_obj]
  rw [nat_left_assoc β₂.hom, nat_left_assoc β₂.hom, hconj₂, ma_left_assoc P ma,
    reassoc_of% (hassoc A B C), nat_right_assoc β₂.hom, nat_right_assoc β₂.hom,
    ma_right_assoc P ma, reassoc_of% h₁]

/-- **An associativity square for a comparison of bifunctors, read backwards.** -/
theorem associator_conj_inv {C : Type*} [Category C] {Ta Tb : C × C ⥤ C} (β : Ta ≅ Tb)
    (aa : ∀ A B C' : C, Ta.obj (Ta.obj (A, B), C') ⟶ Ta.obj (A, Ta.obj (B, C')))
    (ab : ∀ A B C' : C, Tb.obj (Tb.obj (A, B), C') ⟶ Tb.obj (A, Tb.obj (B, C')))
    (hconj : ∀ A B C' : C,
      β.hom.app (Ta.obj (A, B), C') ≫ Tb.map (β.hom.app (A, B) ×ₘ 𝟙 C') ≫ ab A B C' =
        aa A B C' ≫ β.hom.app (A, Ta.obj (B, C')) ≫ Tb.map (𝟙 A ×ₘ β.hom.app (B, C')))
    (A B C' : C) :
    β.inv.app (Tb.obj (A, B), C') ≫ Ta.map (β.inv.app (A, B) ×ₘ 𝟙 C') ≫ aa A B C' =
      ab A B C' ≫ β.inv.app (A, Tb.obj (B, C')) ≫ Ta.map (𝟙 A ×ₘ β.inv.app (B, C')) := by
  let U := β.app (Ta.obj (A, B), C') ≪≫ Tb.mapIso (Iso.prod (β.app (A, B)) (Iso.refl C'))
  let V := β.app (A, Ta.obj (B, C')) ≪≫ Tb.mapIso (Iso.prod (Iso.refl A) (β.app (B, C')))
  have hU : U.inv = β.inv.app (Tb.obj (A, B), C') ≫ Ta.map (β.inv.app (A, B) ×ₘ 𝟙 C') :=
    (nat_left β.inv (β.inv.app (A, B)) C').symm
  have hV : V.inv = β.inv.app (A, Tb.obj (B, C')) ≫ Ta.map (𝟙 A ×ₘ β.inv.app (B, C')) :=
    (nat_right β.inv A (β.inv.app (B, C'))).symm
  have h := conj_inv U.hom V.hom (aa A B C') (ab A B C') (by
    simpa only [U, V, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
      Category.assoc] using hconj A B C')
  rw [IsIso.Iso.inv_hom, IsIso.Iso.inv_hom, hU, hV] at h
  rw [← Category.assoc, h]

end Abstract

/-! ### The comparison of the two derived tensor products is the comparison of two re-seatings -/

section Bridge

universe u

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedPullbackTensor in
attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes
  liftMonoidal CochainComplex.symmetricCategory

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  StacksDraft.KFlat.modulePullback Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

variable (Z : AlgebraicGeometry.RingedSpace.{u, u})

/-- Two isomorphisms out of one object, followed by morphisms with a common composite. -/
private theorem comp_inv_eq_of_comp {C : Type*} [Category C] {P A₁ A₂ T : C} (r₁ : P ≅ A₁)
    (r₂ : P ≅ A₂) (a : A₁ ⟶ T) (b : A₂ ≅ T) (D : P ⟶ T) (h₁ : r₁.hom ≫ a = D)
    (h₂ : r₂.hom ≫ b.hom = D) : a ≫ b.inv = r₁.inv ≫ r₂.hom := by
  rw [← cancel_epi r₁.hom, reassoc_of% h₁, ← h₂, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.hom_inv_id_assoc]

/-- Generic: two isomorphisms out of one object with a common composite, read on uncurried
re-seating comparisons. -/
private theorem uncurry_comp_inv_eq {C : Type*} [Category C] {T₀ T₁ T₂ : C ⥤ C ⥤ C}
    (e₁ : T₀ ≅ T₁) (e₂ : T₀ ≅ T₂) (X Y : C) {T : C} (a : (T₁.obj X).obj Y ⟶ T)
    (b : (T₂.obj X).obj Y ≅ T) (D : (T₀.obj X).obj Y ⟶ T)
    (h₁ : ((e₁.app X).app Y).hom ≫ a = D) (h₂ : ((e₂.app X).app Y).hom ≫ b.hom = D) :
    a ≫ b.inv = (Functor.uncurry.map (e₁.inv ≫ e₂.hom)).app (X, Y) :=
  comp_inv_eq_of_comp ((e₁.app X).app Y) ((e₂.app X).app Y) a b D h₁ h₂

private theorem reseat_comp_internalHomComparison
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z L) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.sheaf
    ((Iso.app (C := Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Z.sheaf)
        (D := Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Z.sheaf ⥤
          Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Z.sheaf)
        (Stacks.SheafOfModules.derivedTensorMonoidalIso Z.sheaf)
        (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L)).hom ≫
      ((internalHomTensorProduct Z).comparison K L hK hL).hom =
      (CochainComplex.KFlatMonoidal.derivedTensorIso
        (Stacks.SheafOfModules.DerivedMonoidal.Mod Z.sheaf) _ hK hL).hom :=
  Stacks.SheafOfModules.reseatIso_comp_derivedTensorComparisonHom Z.sheaf K L hK hL

/-- **`tensorBridge` is the comparison of the two re-seatings of the monoidal structure of
Tag 0FPT**, on the derived tensor product of Tag 079U and on the one of the internal hom. -/
theorem tensorBridge_hom_eq :
    (tensorBridge Z).hom = Functor.uncurry.map
      ((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Z.sheaf).inv ≫
        (Stacks.SheafOfModules.derivedTensorMonoidalIso Z.sheaf).hom) := by
  refine Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat Z _ _ fun K L hK hL => ?_
  rw [tensorBridge_hom_app_of_kFlat Z K L hK hL, tensorBridgeModel_eq]
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.sheaf
  have h₁ : (reseatIso (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Z.sheaf)
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
      ((pullbackTensorProduct Z).comparison K L hK hL).hom =
      (CochainComplex.KFlatMonoidal.derivedTensorIso
        (Stacks.SheafOfModules.DerivedMonoidal.Mod Z.sheaf) _ hK hL).hom :=
    Stacks.SheafOfModules.DerivedMonoidal.reseatIso_comp_canonicalComparisonHom Z.sheaf K L hK hL
  exact uncurry_comp_inv_eq _ _ _ _ _ ((internalHomTensorProduct Z).comparison K L hK hL) _ h₁
    (reseat_comp_internalHomComparison Z K L hK hL)

/-- The inverse of `tensorBridge` is the comparison of the two re-seatings taken the other way. -/
theorem tensorBridge_inv_app_eq
    (A B : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (tensorBridge Z).inv.app (A, B) =
      ((Stacks.SheafOfModules.derivedTensorMonoidalIso Z.sheaf).inv.app A).app B ≫
        ((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Z.sheaf).hom.app A).app
          B := by
  rw [← cancel_epi ((tensorBridge Z).hom.app (A, B)), Iso.hom_inv_id_app, tensorBridge_hom_eq]
  simp

end Bridge

section BridgeAssociator

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

/-- **An associativity square for a comparison of two re-seatings, read on the uncurried
bifunctors.**  Stated over an arbitrary category, so that it is applied by unification. -/
private theorem uncurry_associator {C : Type*} [Category C] {T₀ T₁ T₂ : C ⥤ C ⥤ C}
    (e₁ : T₀ ≅ T₁) (e₂ : T₀ ≅ T₂)
    (a₁ : ∀ X Y Z : C, (T₁.obj ((T₁.obj X).obj Y)).obj Z ⟶ (T₁.obj X).obj ((T₁.obj Y).obj Z))
    (a₂ : ∀ X Y Z : C, (T₂.obj ((T₂.obj X).obj Y)).obj Z ⟶ (T₂.obj X).obj ((T₂.obj Y).obj Z))
    (X Y Z : C)
    (h : (((e₁.app ((T₁.obj X).obj Y)).app Z).inv ≫ ((e₂.app ((T₁.obj X).obj Y)).app Z).hom) ≫
        (T₂.map (((e₁.app X).app Y).inv ≫ ((e₂.app X).app Y).hom)).app Z ≫ a₂ X Y Z =
      a₁ X Y Z ≫ (((e₁.app X).app ((T₁.obj Y).obj Z)).inv ≫
          ((e₂.app X).app ((T₁.obj Y).obj Z)).hom) ≫
        (T₂.obj X).map (((e₁.app Y).app Z).inv ≫ ((e₂.app Y).app Z).hom)) :
    (Functor.uncurry.map (e₁.inv ≫ e₂.hom)).app ((Functor.uncurry.obj T₁).obj (X, Y), Z) ≫
        (Functor.uncurry.obj T₂).map
          ((Functor.uncurry.map (e₁.inv ≫ e₂.hom)).app (X, Y) ×ₘ 𝟙 Z) ≫ a₂ X Y Z =
      a₁ X Y Z ≫
        (Functor.uncurry.map (e₁.inv ≫ e₂.hom)).app (X, (Functor.uncurry.obj T₁).obj (Y, Z)) ≫
        (Functor.uncurry.obj T₂).map
          (𝟙 X ×ₘ (Functor.uncurry.map (e₁.inv ≫ e₂.hom)).app (Y, Z)) := by
  simpa [Functor.uncurry] using h

/-- **The associativity square of two re-seatings, read on the uncurried bifunctors**, for the
associativity constraints of the two re-seated structures. -/
private theorem uncurry_reseat_associator {C : Type*} [Category C] [MonoidalCategory C]
    {T₁ T₂ : C ⥤ C ⥤ C} (e₁ : curriedTensor C ≅ T₁) (e₂ : curriedTensor C ≅ T₂)
    {U₁ U₂ : C} (ε₁ : 𝟙_ C ≅ U₁) (ε₂ : 𝟙_ C ≅ U₂) (X Y Z : C) :
    (Functor.uncurry.map (e₁.inv ≫ e₂.hom)).app ((Functor.uncurry.obj T₁).obj (X, Y), Z) ≫
        (Functor.uncurry.obj T₂).map
          ((Functor.uncurry.map (e₁.inv ≫ e₂.hom)).app (X, Y) ×ₘ 𝟙 Z) ≫
          (@MonoidalCategoryStruct.associator C _ (reseat e₂ ε₂).toMonoidalCategoryStruct
            X Y Z).hom =
      (@MonoidalCategoryStruct.associator C _ (reseat e₁ ε₁).toMonoidalCategoryStruct
          X Y Z).hom ≫
        (Functor.uncurry.map (e₁.inv ≫ e₂.hom)).app (X, (Functor.uncurry.obj T₁).obj (Y, Z)) ≫
          (Functor.uncurry.obj T₂).map
            (𝟙 X ×ₘ (Functor.uncurry.map (e₁.inv ≫ e₂.hom)).app (Y, Z)) :=
  uncurry_associator e₁ e₂
    (fun X Y Z => (@MonoidalCategoryStruct.associator C _
      (reseat e₁ ε₁).toMonoidalCategoryStruct X Y Z).hom)
    (fun X Y Z => (@MonoidalCategoryStruct.associator C _
      (reseat e₂ ε₂).toMonoidalCategoryStruct X Y Z).hom) X Y Z
    (reseatComparison_associator e₁ e₂ ε₁ ε₂ X Y Z)

/-- `uncurry_reseat_associator` for a transformation `β` and families `a₁`, `a₂` given as equal
to the uncurried comparison of the two re-seatings and to their associativity constraints. -/
private theorem associator_of_reseat {C : Type*} [Category C] [MonoidalCategory C]
    {T₁ T₂ : C ⥤ C ⥤ C} (e₁ : curriedTensor C ≅ T₁) (e₂ : curriedTensor C ≅ T₂)
    {U₁ U₂ : C} (ε₁ : 𝟙_ C ≅ U₁) (ε₂ : 𝟙_ C ≅ U₂)
    (β : Functor.uncurry.obj T₁ ⟶ Functor.uncurry.obj T₂)
    (hβ : β = Functor.uncurry.map (e₁.inv ≫ e₂.hom))
    (a₁ : ∀ X Y Z : C, (T₁.obj ((T₁.obj X).obj Y)).obj Z ⟶ (T₁.obj X).obj ((T₁.obj Y).obj Z))
    (a₂ : ∀ X Y Z : C, (T₂.obj ((T₂.obj X).obj Y)).obj Z ⟶ (T₂.obj X).obj ((T₂.obj Y).obj Z))
    (ha₁ : ∀ X Y Z : C, a₁ X Y Z =
      (@MonoidalCategoryStruct.associator C _ (reseat e₁ ε₁).toMonoidalCategoryStruct
        X Y Z).hom)
    (ha₂ : ∀ X Y Z : C, a₂ X Y Z =
      (@MonoidalCategoryStruct.associator C _ (reseat e₂ ε₂).toMonoidalCategoryStruct
        X Y Z).hom)
    (X Y Z : C) :
    β.app ((Functor.uncurry.obj T₁).obj (X, Y), Z) ≫
        (Functor.uncurry.obj T₂).map (β.app (X, Y) ×ₘ 𝟙 Z) ≫ a₂ X Y Z =
      a₁ X Y Z ≫ β.app (X, (Functor.uncurry.obj T₁).obj (Y, Z)) ≫
        (Functor.uncurry.obj T₂).map (𝟙 X ×ₘ β.app (Y, Z)) := by
  subst hβ
  rw [ha₁, ha₂]
  exact uncurry_reseat_associator e₁ e₂ ε₁ ε₂ X Y Z

variable (Z : AlgebraicGeometry.RingedSpace.{u, u})

/-- The associativity constraint of Tag 0FPT at the derived tensor product of the internal hom
is the one of the re-seating along `Stacks.SheafOfModules.derivedTensorMonoidalIso`. -/
private theorem derivedAssociatorHom_eq_reseat
    (A B C : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A B C =
      (@MonoidalCategoryStruct.associator
        (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Z.sheaf) _
        (@reseat _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.sheaf) _ _
          (Stacks.SheafOfModules.derivedTensorMonoidalIso Z.sheaf)
          (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Z.sheaf)).toMonoidalCategoryStruct
        A B C).hom :=
  rfl

/-- The associativity constraint of Tag 0FPT at the derived tensor product of Tag 079U is the one
of the re-seating along `Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso`. -/
private theorem canonicalAssociatorHom_eq_reseat
    (A B C : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom Z.sheaf A B C =
      (@MonoidalCategoryStruct.associator
        (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Z.sheaf) _
        (@reseat _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.sheaf) _ _
          (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Z.sheaf)
          (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Z.sheaf)).toMonoidalCategoryStruct
        A B C).hom :=
  rfl

/-- **`tensorBridge` carries the associativity constraint of Tag 0FPT at the derived tensor
product of Tag 079U to the one at the derived tensor product of the internal hom.** -/
theorem tensorBridge_associator
    (A B C : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (tensorBridge Z).hom.app ((pullbackTensorUncurried Z).obj (A, B), C) ≫
        (internalHomTensorUncurried Z).map ((tensorBridge Z).hom.app (A, B) ×ₘ 𝟙 C) ≫
          Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A B C =
      Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom Z.sheaf A B C ≫
        (tensorBridge Z).hom.app (A, (pullbackTensorUncurried Z).obj (B, C)) ≫
          (internalHomTensorUncurried Z).map (𝟙 A ×ₘ (tensorBridge Z).hom.app (B, C)) := by
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.sheaf
  exact associator_of_reseat (T₁ := (pullbackTensorProduct Z).tensor)
    (T₂ := (internalHomTensorProduct Z).tensor)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Z.sheaf)
    (Stacks.SheafOfModules.derivedTensorMonoidalIso Z.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Z.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Z.sheaf)
    (tensorBridge Z).hom (tensorBridge_hom_eq Z)
    (fun A B C => Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom Z.sheaf A B C)
    (fun A B C => Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A B C)
    (canonicalAssociatorHom_eq_reseat Z) (derivedAssociatorHom_eq_reseat Z) A B C

/-- `tensorBridge`, taken backwards, carries the associativity constraint at the derived tensor
product of the internal hom to the one at the derived tensor product of Tag 079U. -/
theorem tensorBridge_inv_associator
    (A B C : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)) :
    (tensorBridge Z).inv.app ((internalHomTensorUncurried Z).obj (A, B), C) ≫
        (pullbackTensorUncurried Z).map ((tensorBridge Z).inv.app (A, B) ×ₘ 𝟙 C) ≫
          Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom Z.sheaf A B C =
      Stacks.SheafOfModules.derivedAssociatorHom Z.sheaf A B C ≫
        (tensorBridge Z).inv.app (A, (internalHomTensorUncurried Z).obj (B, C)) ≫
          (pullbackTensorUncurried Z).map (𝟙 A ×ₘ (tensorBridge Z).inv.app (B, C)) :=
  associator_conj_inv (tensorBridge Z) _ _
    (tensorBridge_associator Z) A B C

end BridgeAssociator

/-! ### Tag 079U at the derived tensor product of the internal hom is associative -/

section Pullback

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (h : X ⟶ Y)

/-- **The comparison of Tag 079U at the derived tensor product of the internal hom carries the
associativity constraint of Tag 0FPT on `D(𝒪_Y)` to the one on `D(𝒪_X)`.** -/
theorem pullbackTensorIso_associator
    (A B C : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (pullbackTensorIso h).hom.app ((internalHomTensorUncurried Y).obj (A, B), C) ≫
        (internalHomTensorUncurried X).map
          ((pullbackTensorIso h).hom.app (A, B) ×ₘ 𝟙 ((derivedPullbackFunctor h).obj C)) ≫
          Stacks.SheafOfModules.derivedAssociatorHom X.sheaf ((derivedPullbackFunctor h).obj A)
            ((derivedPullbackFunctor h).obj B) ((derivedPullbackFunctor h).obj C) =
      (derivedPullbackFunctor h).map (Stacks.SheafOfModules.derivedAssociatorHom Y.sheaf A B C) ≫
        (pullbackTensorIso h).hom.app (A, (internalHomTensorUncurried Y).obj (B, C)) ≫
          (internalHomTensorUncurried X).map
            (𝟙 ((derivedPullbackFunctor h).obj A) ×ₘ (pullbackTensorIso h).hom.app (B, C)) :=
  associator_of_conj (derivedPullbackFunctor h) (tensorBridge Y) (tensorBridge X)
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso h)
    (fun A B C => Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom Y.sheaf A B C)
    (fun A B C => Stacks.SheafOfModules.derivedAssociatorHom Y.sheaf A B C)
    (fun A B C => Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociatorHom X.sheaf A B C)
    (fun A B C => Stacks.SheafOfModules.derivedAssociatorHom X.sheaf A B C)
    (pullbackTensorIso h) (fun _ _ => rfl) (tensorBridge_inv_associator Y)
    (tensorBridge_associator X)
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_associator h) A B C

end Pullback

end Stacks.Cohomology.DerivedInternalHomPullback

end
