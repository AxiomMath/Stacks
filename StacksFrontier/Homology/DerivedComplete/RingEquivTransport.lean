module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedCategory.ModelComparison
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness

/-!
# Transporting derived completeness along ring isomorphisms and changes of model

Let `e : R ≃+* R'` be an isomorphism of commutative rings, possibly living in different
universes, and fix a universe `w` for modules. Restriction of scalars along `e.symm` is an
equivalence `ModuleCat.{w} R ≌ ModuleCat.{w} R'`, and it induces an equivalence of derived
categories `D(R) ≌ D(R')` for any two chosen models of these derived categories. This file shows
that this equivalence carries the objects of `D(R)` which are derived complete with respect to an
ideal `I` exactly onto the objects of `D(R')` which are derived complete with respect to the
transported ideal `e(I)`, and hence restricts to an equivalence of the full subcategories of
derived complete objects.

The same is proved for a change of model of the derived category of an `R`-linear abelian
category: the comparison equivalence `StacksDraft.DerivedModel.modelEquiv h₁ h₂` between two
chosen derived categories restricts to an equivalence of their derived complete objects.

Finally, for a nilpotent ideal every object is derived complete, so the full subcategory of
derived complete objects is equivalent to the whole category.

## Main definitions

* `Stacks.DerivedCompleteTransport.derivedCompleteEquivalence`: an equivalence of linear
  categories which is semilinear along a ring isomorphism `σ` restricts to an equivalence between
  the objects derived complete for `I` and those derived complete for `σ(I)`.
* `Stacks.DerivedCompleteTransport.derivedEquivalenceOfRingEquiv`: the equivalence
  `D(ModuleCat.{w} R) ≌ D(ModuleCat.{w} R')` induced by restriction of scalars along `e.symm`,
  for arbitrary models.
* `Stacks.DerivedCompleteTransport.derivedCompleteEquivalenceOfRingEquiv`: its restriction to
  derived complete objects.
* `Stacks.DerivedCompleteTransport.derivedCompleteModelEquivalence`: the restriction of the
  model comparison to derived complete objects.
* `Stacks.DerivedCompleteTransport.derivedCompleteEquivalenceOfIsNilpotent`: for a nilpotent
  ideal, the derived complete objects form the whole category.

## Main results

* `Stacks.DerivedCompleteTransport.isDerivedCompleteAt_iff_obj`: a fully faithful additive
  functor preserving countable products, which carries the action of `a` to the action of `b`,
  carries `T(K, a) = 0` to `T(F K, b) = 0` and back.
* `Stacks.DerivedCompleteTransport.isDerivedComplete_iff_derivedEquivalenceOfRingEquiv`:
  `K` is derived complete for `I` iff its image in `D(R')` is derived complete for `e(I)`.
* `Stacks.DerivedCompleteTransport.isDerivedComplete_iff_modelEquiv`: derived completeness does
  not depend on the model of the derived category.
* `Stacks.DerivedCompleteTransport.isDerivedComplete_of_isNilpotent`: for a nilpotent ideal every
  object is derived complete.
* `Stacks.DerivedCompleteTransport.hasProductsOfShape_nat_derivedCategory_moduleCat`: the derived
  category of `ModuleCat.{w} R` has countable products for every ring universe, module universe
  and model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w₁ w₂ u u'

namespace Stacks.DerivedCompleteTransport

/-! ### Transport along a semilinear equivalence -/

section Abstract

variable {A B : Type*} [CommRing A] [CommRing B]
  {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [Linear A C] [Linear B D] [HasProductsOfShape ℕ C] [HasProductsOfShape ℕ D]

/-- Let `F` be a fully faithful additive functor preserving the countable power `∏ₙ K`, which
carries the action of `a` on `K` to the action of `b` on `F K`. Then `T(F K, b) = 0` if and only
if `T(K, a) = 0`. -/
theorem isDerivedCompleteAt_iff_obj (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] {K : C}
    [PreservesLimit (Discrete.functor fun _ : ℕ => K) F] {a : A} {b : B}
    (h : F.map (a • 𝟙 K) = b • 𝟙 (F.obj K)) :
    IsDerivedCompleteAt K a ↔ IsDerivedCompleteAt (F.obj K) b := by
  rw [isDerivedCompleteAt_iff_isIso, isDerivedCompleteAt_iff_isIso]
  let c := piComparison F (fun _ : ℕ ↦ K)
  have hc : c ≫ oneSubSmulShift (F.obj K) b = F.map (oneSubSmulShift K a) ≫ c := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    have key : F.map (a • Pi.π (fun _ : ℕ ↦ K) (n + 1)) =
        b • F.map (Pi.π (fun _ : ℕ ↦ K) (n + 1)) := by
      have : a • Pi.π (fun _ : ℕ ↦ K) (n + 1) = Pi.π (fun _ : ℕ ↦ K) (n + 1) ≫ (a • 𝟙 K) := by
        rw [Linear.comp_smul, Category.comp_id]
      rw [this, F.map_comp, h, Linear.comp_smul, Category.comp_id]
    rw [Category.assoc, oneSubSmulShift_π, Preadditive.comp_sub, Linear.comp_smul,
      piComparison_comp_π, piComparison_comp_π, Category.assoc, piComparison_comp_π,
      ← F.map_comp, oneSubSmulShift_π, F.map_sub, key]
  rw [← isIso_comp_left_iff c (oneSubSmulShift (F.obj K) b), hc, isIso_comp_right_iff]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ isIso_of_fully_faithful F _⟩

/-- An equivalence `E` of linear categories which is semilinear along a ring isomorphism
`σ : A ≃+* B` carries the objects derived complete for `I` exactly to the objects derived
complete for `σ(I)`. -/
theorem isDerivedComplete_iff_functor_obj (E : C ≌ D) [E.functor.Additive] (σ : A ≃+* B)
    (hσ : ∀ (K : C) (a : A), E.functor.map (a • 𝟙 K) = σ a • 𝟙 (E.functor.obj K))
    (I : Ideal A) (K : C) :
    IsDerivedComplete I K ↔ IsDerivedComplete (I.map σ) (E.functor.obj K) := by
  refine ⟨fun h b hb ↦ ?_, fun h a ha ↦
    (isDerivedCompleteAt_iff_obj E.functor (hσ K a)).2 (h _ (Ideal.mem_map_of_mem σ ha))⟩
  obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_of_equiv σ b).1 hb
  exact (isDerivedCompleteAt_iff_obj E.functor (hσ K a)).1 (h a ha)

/-- An equivalence `E` of `A`-linear categories carries the objects derived complete for `I`
exactly to the objects derived complete for `I`. -/
theorem isDerivedComplete_iff_functor_obj_of_linear {D : Type*} [Category D] [Preadditive D]
    [Linear A D] [HasProductsOfShape ℕ D] (E : C ≌ D) [E.functor.Additive]
    (hE : ∀ (K : C) (a : A), E.functor.map (a • 𝟙 K) = a • 𝟙 (E.functor.obj K))
    (I : Ideal A) (K : C) :
    IsDerivedComplete I K ↔ IsDerivedComplete I (E.functor.obj K) :=
  forall₂_congr fun a _ ↦ isDerivedCompleteAt_iff_obj E.functor (hE K a)

/-- Derived completeness for an ideal is a property closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_isDerivedComplete (I : Ideal A) :
    ObjectProperty.IsClosedUnderIsomorphisms (fun K : C => IsDerivedComplete I K) :=
  ⟨fun e h ↦ DerivedCompleteRecurrence.isDerivedComplete_of_iso e h⟩

/-- An equivalence of linear categories which is semilinear along a ring isomorphism
`σ : A ≃+* B` restricts to an equivalence between the full subcategory of objects derived
complete for `I` and the full subcategory of objects derived complete for `σ(I)`. -/
def derivedCompleteEquivalence (E : C ≌ D) [E.functor.Additive] (σ : A ≃+* B)
    (hσ : ∀ (K : C) (a : A), E.functor.map (a • 𝟙 K) = σ a • 𝟙 (E.functor.obj K))
    (I : Ideal A) :
    ObjectProperty.FullSubcategory (fun K : C => IsDerivedComplete I K) ≌
      ObjectProperty.FullSubcategory (fun K : D => IsDerivedComplete (I.map σ) K) :=
  E.congrFullSubcategory
    (funext fun K ↦ propext (isDerivedComplete_iff_functor_obj E σ hσ I K).symm)

/-- The functor of `derivedCompleteEquivalence E σ hσ I` is computed by `E.functor`. -/
@[simp]
theorem derivedCompleteEquivalence_functor_obj_obj (E : C ≌ D) [E.functor.Additive]
    (σ : A ≃+* B)
    (hσ : ∀ (K : C) (a : A), E.functor.map (a • 𝟙 K) = σ a • 𝟙 (E.functor.obj K))
    (I : Ideal A) (X : ObjectProperty.FullSubcategory (fun K : C => IsDerivedComplete I K)) :
    ((derivedCompleteEquivalence E σ hσ I).functor.obj X).obj = E.functor.obj X.obj :=
  rfl

/-- The inverse of `derivedCompleteEquivalence E σ hσ I` is computed by `E.inverse`. -/
@[simp]
theorem derivedCompleteEquivalence_inverse_obj_obj (E : C ≌ D) [E.functor.Additive]
    (σ : A ≃+* B)
    (hσ : ∀ (K : C) (a : A), E.functor.map (a • 𝟙 K) = σ a • 𝟙 (E.functor.obj K))
    (I : Ideal A)
    (Y : ObjectProperty.FullSubcategory (fun K : D => IsDerivedComplete (I.map σ) K)) :
    ((derivedCompleteEquivalence E σ hσ I).inverse.obj Y).obj = E.inverse.obj Y.obj :=
  rfl

/-- An equivalence of `A`-linear categories restricts to an equivalence between the full
subcategories of objects derived complete for `I`. -/
def derivedCompleteEquivalenceOfLinear {D : Type*} [Category D] [Preadditive D]
    [Linear A D] [HasProductsOfShape ℕ D] (E : C ≌ D) [E.functor.Additive]
    (hE : ∀ (K : C) (a : A), E.functor.map (a • 𝟙 K) = a • 𝟙 (E.functor.obj K))
    (I : Ideal A) :
    ObjectProperty.FullSubcategory (fun K : C => IsDerivedComplete I K) ≌
      ObjectProperty.FullSubcategory (fun K : D => IsDerivedComplete I K) :=
  E.congrFullSubcategory
    (funext fun K ↦ propext (isDerivedComplete_iff_functor_obj_of_linear E hE I K).symm)

/-- The functor of `derivedCompleteEquivalenceOfLinear E hE I` is computed by `E.functor`. -/
@[simp]
theorem derivedCompleteEquivalenceOfLinear_functor_obj_obj {D : Type*} [Category D]
    [Preadditive D] [Linear A D] [HasProductsOfShape ℕ D] (E : C ≌ D) [E.functor.Additive]
    (hE : ∀ (K : C) (a : A), E.functor.map (a • 𝟙 K) = a • 𝟙 (E.functor.obj K))
    (I : Ideal A) (X : ObjectProperty.FullSubcategory (fun K : C => IsDerivedComplete I K)) :
    ((derivedCompleteEquivalenceOfLinear E hE I).functor.obj X).obj = E.functor.obj X.obj :=
  rfl

end Abstract

/-! ### Scalars through a localization -/

section Localization

variable {A B : Type*} [CommRing A] [CommRing B]
  {C₀ C₀' D₁ D₂ : Type*} [Category C₀] [Category C₀'] [Category D₁] [Category D₂]
  [Preadditive C₀] [Preadditive C₀'] [Preadditive D₁] [Preadditive D₂]
  [Linear A C₀] [Linear B C₀'] [Linear A D₁] [Linear B D₂]

/-- Let `Q₁ : C₀ ⥤ D₁` be essentially surjective and `A`-linear, `Q₂ : C₀' ⥤ D₂` be `B`-linear
and `α : Q₁ ⋙ F ≅ G ⋙ Q₂`. If `G` carries the action of `a` to the action of `b`, so does `F`. -/
theorem map_smul_id_of_compIso (Q₁ : C₀ ⥤ D₁) [Q₁.Linear A] [Q₁.EssSurj] (Q₂ : C₀' ⥤ D₂)
    [Q₂.Linear B] (G : C₀ ⥤ C₀') (F : D₁ ⥤ D₂) (α : Q₁ ⋙ F ≅ G ⋙ Q₂) (a : A) (b : B)
    (hG : ∀ X : C₀, G.map (a • 𝟙 X) = b • 𝟙 (G.obj X)) (K : D₁) :
    F.map (a • 𝟙 K) = b • 𝟙 (F.obj K) := by
  let X := Q₁.objPreimage K
  let i : Q₁.obj X ≅ K := Q₁.objObjPreimageIso K
  have h1 : a • 𝟙 K = i.inv ≫ (a • 𝟙 (Q₁.obj X)) ≫ i.hom := by
    rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.inv_hom_id]
  have h2 : F.map (a • 𝟙 (Q₁.obj X)) = b • 𝟙 (F.obj (Q₁.obj X)) := by
    have nat := α.hom.naturality (a • 𝟙 X)
    simp only [Functor.comp_map, hG, Functor.Linear.map_smul, CategoryTheory.Functor.map_id] at nat
    rw [← cancel_mono (α.hom.app X), Linear.smul_comp, Category.id_comp, nat]
    simp
  rw [h1, F.map_comp, F.map_comp, h2, Linear.smul_comp, Category.id_comp, Linear.comp_smul,
    ← F.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

end Localization

/-! ### Countable products in `D(ModuleCat.{w} R)` -/

/-- The derived category of `ModuleCat.{w} R` has countable products, for every ring universe,
every module universe and every model of the derived category. -/
instance hasProductsOfShape_nat_derivedCategory_moduleCat (R : Type u) [Ring R]
    [HasDerivedCategory.{w₁} (ModuleCat.{w} R)] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{w} R)) :=
  Stacks.DerivedProducts.hasProductsOfShape_nat

/-! ### Ring isomorphisms -/

section RingEquiv

variable {R : Type u} [CommRing R] {R' : Type u'} [CommRing R'] (e : R ≃+* R')

/-- Restriction of scalars along `e.symm` carries the action of `a` to the action of `e a`. -/
theorem restrictScalars_symm_map_smul_id (M : ModuleCat.{w} R) (a : R) :
    (ModuleCat.restrictScalars.{w} e.symm.toRingHom).map (a • 𝟙 M) =
      e a • 𝟙 ((ModuleCat.restrictScalars.{w} e.symm.toRingHom).obj M) := by
  ext x
  show a • x = e.symm.toRingHom (e a) • x
  simp

/-- Restriction of scalars along `e.symm`, applied degreewise to cochain complexes, carries the
action of `a` to the action of `e a`. -/
theorem restrictScalars_symm_mapHomologicalComplex_map_smul_id
    (X : CochainComplex (ModuleCat.{w} R) ℤ) (a : R) :
    ((ModuleCat.restrictScalars.{w} e.symm.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (a • 𝟙 X) =
      e a • 𝟙 (((ModuleCat.restrictScalars.{w} e.symm.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X) := by
  ext n : 1
  exact restrictScalars_symm_map_smul_id e (X.X n) a

/-- The functor of `ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm` is restriction of
scalars along `e.symm`. -/
theorem restrictScalarsEquivalenceOfRingEquiv_symm_functor :
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor =
      ModuleCat.restrictScalars.{w} e.symm.toRingHom :=
  rfl

variable [HasDerivedCategory.{w₁} (ModuleCat.{w} R)] [HasDerivedCategory.{w₂} (ModuleCat.{w} R')]

/-- **The equivalence `D(R) ≌ D(R')` induced by a ring isomorphism `e : R ≃+* R'`**, for modules
in a fixed universe `w` and arbitrary models of the two derived categories: it is induced by the
exact equivalence `ModuleCat.{w} R ≌ ModuleCat.{w} R'` given by restriction of scalars along
`e.symm`. -/
def derivedEquivalenceOfRingEquiv :
    DerivedCategory (ModuleCat.{w} R) ≌ DerivedCategory (ModuleCat.{w} R') :=
  have := Stacks.Injectives.mapDerivedCategory_isEquivalence
    (ModuleCat.restrictScalars.{w} e.symm.toRingHom)
  (ModuleCat.restrictScalars.{w} e.symm.toRingHom).mapDerivedCategory.asEquivalence

/-- The functor of `derivedEquivalenceOfRingEquiv e` is the functor induced on derived
categories by restriction of scalars along `e.symm`. -/
theorem derivedEquivalenceOfRingEquiv_functor :
    (derivedEquivalenceOfRingEquiv.{w} e).functor =
      (ModuleCat.restrictScalars.{w} e.symm.toRingHom).mapDerivedCategory :=
  rfl

/-- `derivedEquivalenceOfRingEquiv e` commutes with the localization functors `Q`: on the
image of a complex it is the image of the complex with scalars restricted degreewise. -/
def derivedEquivalenceOfRingEquivCompQIso :
    DerivedCategory.Q ⋙ (derivedEquivalenceOfRingEquiv.{w} e).functor ≅
      (ModuleCat.restrictScalars.{w} e.symm.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (ModuleCat.restrictScalars.{w} e.symm.toRingHom).mapDerivedCategoryFactors

/-- The functor of `derivedEquivalenceOfRingEquiv e` is additive. -/
instance derivedEquivalenceOfRingEquiv_functor_additive :
    (derivedEquivalenceOfRingEquiv.{w} e).functor.Additive :=
  inferInstanceAs (ModuleCat.restrictScalars.{w} e.symm.toRingHom).mapDerivedCategory.Additive

/-- `derivedEquivalenceOfRingEquiv e` carries the action of `a` to the action of `e a`. -/
theorem derivedEquivalenceOfRingEquiv_map_smul_id (K : DerivedCategory (ModuleCat.{w} R))
    (a : R) :
    (derivedEquivalenceOfRingEquiv.{w} e).functor.map (a • 𝟙 K) =
      e a • 𝟙 ((derivedEquivalenceOfRingEquiv.{w} e).functor.obj K) :=
  map_smul_id_of_compIso DerivedCategory.Q DerivedCategory.Q _ _
    (derivedEquivalenceOfRingEquivCompQIso e) a (e a)
    (fun X ↦ restrictScalars_symm_mapHomologicalComplex_map_smul_id e X a) K

variable [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{w} R))]
  [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{w} R'))]

/-- **Derived completeness along a ring isomorphism.** An object `K` of `D(R)` is derived
complete with respect to `I` if and only if its image in `D(R')` under the equivalence induced by
`e : R ≃+* R'` is derived complete with respect to `e(I)`. -/
theorem isDerivedComplete_iff_derivedEquivalenceOfRingEquiv (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{w} R)) :
    IsDerivedComplete I K ↔
      IsDerivedComplete (I.map e) ((derivedEquivalenceOfRingEquiv.{w} e).functor.obj K) :=
  isDerivedComplete_iff_functor_obj _ e (derivedEquivalenceOfRingEquiv_map_smul_id e) I K

/-- **The equivalence `D_comp(R, I) ≌ D_comp(R', e(I))`** of the full subcategories of derived
complete objects induced by a ring isomorphism `e : R ≃+* R'`. -/
def derivedCompleteEquivalenceOfRingEquiv (I : Ideal R) :
    ObjectProperty.FullSubcategory
        (fun K : DerivedCategory (ModuleCat.{w} R) => IsDerivedComplete I K) ≌
      ObjectProperty.FullSubcategory
        (fun K : DerivedCategory (ModuleCat.{w} R') => IsDerivedComplete (I.map e) K) :=
  derivedCompleteEquivalence (derivedEquivalenceOfRingEquiv.{w} e) e
    (derivedEquivalenceOfRingEquiv_map_smul_id e) I

/-- The functor of `derivedCompleteEquivalenceOfRingEquiv e I` is computed by the functor induced
on derived categories by restriction of scalars along `e.symm`. -/
@[simp]
theorem derivedCompleteEquivalenceOfRingEquiv_functor_obj_obj (I : Ideal R)
    (X : ObjectProperty.FullSubcategory
      (fun K : DerivedCategory (ModuleCat.{w} R) => IsDerivedComplete I K)) :
    ((derivedCompleteEquivalenceOfRingEquiv e I).functor.obj X).obj =
      (ModuleCat.restrictScalars.{w} e.symm.toRingHom).mapDerivedCategory.obj X.obj :=
  rfl

end RingEquiv

/-! ### Change of model -/

section Model

variable {R : Type u} [CommRing R] {C : Type*} [Category C] [Abelian C] [Linear R C]

/-- The comparison equivalence between two models of the derived category of an `R`-linear
abelian category is `R`-linear on the actions of scalars. -/
theorem modelEquiv_map_smul_id (h₁ : HasDerivedCategory.{w₁} C) (h₂ : HasDerivedCategory.{w₂} C)
    (K : @DerivedCategory C _ _ h₁) (a : R) :
    (StacksDraft.DerivedModel.modelEquiv h₁ h₂).functor.map (a • 𝟙 K) =
      a • 𝟙 ((StacksDraft.DerivedModel.modelEquiv h₁ h₂).functor.obj K) := by
  let := h₁
  let := h₂
  exact map_smul_id_of_compIso (@DerivedCategory.Q C _ _ h₁) (@DerivedCategory.Q C _ _ h₂)
    (𝟭 _) _ (StacksDraft.DerivedModel.modelCompQIso h₁ h₂ ≪≫ (Functor.leftUnitor _).symm) a a
    (fun _ ↦ rfl) K

/-- **Derived completeness does not depend on the model of the derived category.** -/
theorem isDerivedComplete_iff_modelEquiv (h₁ : HasDerivedCategory.{w₁} C)
    (h₂ : HasDerivedCategory.{w₂} C) [HasProductsOfShape ℕ (@DerivedCategory C _ _ h₁)]
    [HasProductsOfShape ℕ (@DerivedCategory C _ _ h₂)] (I : Ideal R)
    (K : @DerivedCategory C _ _ h₁) :
    IsDerivedComplete I K ↔
      IsDerivedComplete I ((StacksDraft.DerivedModel.modelEquiv h₁ h₂).functor.obj K) :=
  have := StacksDraft.DerivedModel.modelEquiv_functor_additive h₁ h₂
  isDerivedComplete_iff_functor_obj_of_linear _ (modelEquiv_map_smul_id h₁ h₂) I K

/-- **The equivalence of derived complete objects between two models of the derived
category**, restricting the comparison equivalence `StacksDraft.DerivedModel.modelEquiv h₁ h₂`. -/
def derivedCompleteModelEquivalence (h₁ : HasDerivedCategory.{w₁} C)
    (h₂ : HasDerivedCategory.{w₂} C) [HasProductsOfShape ℕ (@DerivedCategory C _ _ h₁)]
    [HasProductsOfShape ℕ (@DerivedCategory C _ _ h₂)] (I : Ideal R) :
    ObjectProperty.FullSubcategory
        (fun K : @DerivedCategory C _ _ h₁ => IsDerivedComplete I K) ≌
      ObjectProperty.FullSubcategory
        (fun K : @DerivedCategory C _ _ h₂ => IsDerivedComplete I K) :=
  have := StacksDraft.DerivedModel.modelEquiv_functor_additive h₁ h₂
  derivedCompleteEquivalenceOfLinear (StacksDraft.DerivedModel.modelEquiv h₁ h₂)
    (modelEquiv_map_smul_id h₁ h₂) I

/-- The functor of `derivedCompleteModelEquivalence h₁ h₂ I` is the model comparison. -/
@[simp]
theorem derivedCompleteModelEquivalence_functor_obj_obj (h₁ : HasDerivedCategory.{w₁} C)
    (h₂ : HasDerivedCategory.{w₂} C) [HasProductsOfShape ℕ (@DerivedCategory C _ _ h₁)]
    [HasProductsOfShape ℕ (@DerivedCategory C _ _ h₂)] (I : Ideal R)
    (X : ObjectProperty.FullSubcategory
      (fun K : @DerivedCategory C _ _ h₁ => IsDerivedComplete I K)) :
    ((derivedCompleteModelEquivalence h₁ h₂ I).functor.obj X).obj =
      (StacksDraft.DerivedModel.modelEquiv h₁ h₂).functor.obj X.obj :=
  rfl

end Model

/-! ### Nilpotent ideals -/

section Nilpotent

variable {A : Type*} [CommRing A] {C : Type*} [Category C] [Preadditive C] [Linear A C]
  [HasProductsOfShape ℕ C]

/-- If `I` is nilpotent, then every object is derived complete with respect to `I`. -/
theorem isDerivedComplete_of_isNilpotent {I : Ideal A} (hI : IsNilpotent I) (K : C) :
    IsDerivedComplete I K := by
  obtain ⟨n, hn⟩ := hI
  intro f hf
  apply isDerivedCompleteAt_of_isNilpotent
  have hfn : f ^ n ∈ I ^ n := Ideal.pow_mem_pow hf n
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hfn
  exact ⟨n, by rw [smul_pow, one_pow, hfn, zero_smul]⟩

/-- If `I` is nilpotent, the full subcategory of objects derived complete with respect to `I` is
the whole category: its inclusion is an equivalence. -/
def derivedCompleteEquivalenceOfIsNilpotent {I : Ideal A} (hI : IsNilpotent I) :
    ObjectProperty.FullSubcategory (fun K : C => IsDerivedComplete I K) ≌ C :=
  (ObjectProperty.fullSubcategoryCongr (P' := ⊤)
    (funext fun K ↦ propext ⟨fun _ ↦ trivial,
      fun _ ↦ isDerivedComplete_of_isNilpotent hI K⟩)).trans
    (ObjectProperty.topEquivalence C)

/-- The equivalence `derivedCompleteEquivalenceOfIsNilpotent` is the inclusion. -/
@[simp]
theorem derivedCompleteEquivalenceOfIsNilpotent_functor_obj {I : Ideal A} (hI : IsNilpotent I)
    (X : ObjectProperty.FullSubcategory (fun K : C => IsDerivedComplete I K)) :
    (derivedCompleteEquivalenceOfIsNilpotent hI).functor.obj X = X.obj :=
  rfl

/-- If `I` is nilpotent, the inclusion of the derived complete objects is an equivalence. -/
theorem isEquivalence_ι_of_isNilpotent {I : Ideal A} (hI : IsNilpotent I) :
    (ObjectProperty.ι (fun K : C => IsDerivedComplete I K)).IsEquivalence :=
  (derivedCompleteEquivalenceOfIsNilpotent hI).isEquivalence_functor

end Nilpotent

end Stacks.DerivedCompleteTransport

end
