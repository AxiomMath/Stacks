module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition

/-!
# Composites of exact functors on derived categories, over the homotopy category

Let `r₂ : M₂ ⥤ M₁`, `r₁ : M₁ ⥤ M₀` and `r : M₂ ⥤ M₀` be exact functors of abelian categories and
`e : r₂ ⋙ r₁ ≅ r`. The induced functors on derived categories satisfy
`r̄₂ ⋙ r̄₁ ≅ r̄`; this file builds that isomorphism as a lift along the localization
`DerivedCategory.Qh` of the homotopy category, so that its value at the image of an object of the
homotopy category is the composite of the factorizations through `Qh` and of the action of `e`
on homotopy categories. It then restricts it to bounded below derived categories, and shows that
the restricted transformation satisfies the compatibility hypothesis of
`CategoryTheory.Functor.derivedSquareMap_comp` for `ρ₀ = e.hom`.

## Main definitions

* `CategoryTheory.Functor.mapDerivedCategoryCompIsoh`: the isomorphism `r̄₂ ⋙ r̄₁ ≅ r̄` on
  unbounded derived categories.
* `CategoryTheory.Functor.mapDerivedCategoryPlusCompIsoh`: the same on bounded below derived
  categories.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryCompIsoh_hom_app_Qh`: its value on the image of the
  homotopy category.
* `CategoryTheory.Functor.mapDerivedCategoryPlusCompIsoh_compatible`: the compatibility
  hypothesis of `CategoryTheory.Functor.derivedSquareMap_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {M₀ : Type*} [Category* M₀] [Abelian M₀] [HasDerivedCategory M₀]
  {M₁ : Type*} [Category* M₁] [Abelian M₁] [HasDerivedCategory M₁]
  {M₂ : Type*} [Category* M₂] [Abelian M₂] [HasDerivedCategory M₂]
  {r₁ : M₁ ⥤ M₀} {r₂ : M₂ ⥤ M₁} {r : M₂ ⥤ M₀} [r₁.Additive] [r₂.Additive] [r.Additive]
  [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁]
  [PreservesFiniteLimits r₂] [PreservesFiniteColimits r₂]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]

/-- The action on homotopy categories of an isomorphism `e : F ⋙ G ≅ H` is, componentwise, the
action of `e.hom`. -/
theorem mapHomotopyCategoryCompIso_hom_app_eq {A B C : Type*} [Category* A] [Preadditive A]
    [Category* B] [Preadditive B] [Category* C] [Preadditive C] {F : A ⥤ B} {G : B ⥤ C}
    {H : A ⥤ C} [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    (J : HomotopyCategory A (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J =
      (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app J := by
  rcases J with ⟨K⟩
  rfl

/-- The composite `r̄₂ ⋙ r̄₁` lifts `r₂ ⋙ r₁` along `DerivedCategory.Qh`. -/
def mapDerivedCategoryCompFactorsh (r₂ : M₂ ⥤ M₁) (r₁ : M₁ ⥤ M₀) [r₁.Additive] [r₂.Additive]
    [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁]
    [PreservesFiniteLimits r₂] [PreservesFiniteColimits r₂] :
    DerivedCategory.Qh ⋙ r₂.mapDerivedCategory ⋙ r₁.mapDerivedCategory ≅
      (r₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ r₁.mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
        DerivedCategory.Qh :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight r₂.mapDerivedCategoryFactorsh _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ r₁.mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm

/-- The value of `mapDerivedCategoryCompFactorsh`. -/
theorem mapDerivedCategoryCompFactorsh_hom_app (r₂ : M₂ ⥤ M₁) (r₁ : M₁ ⥤ M₀) [r₁.Additive]
    [r₂.Additive] [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁]
    [PreservesFiniteLimits r₂] [PreservesFiniteColimits r₂]
    (J : HomotopyCategory M₂ (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompFactorsh r₂ r₁).hom.app J =
      r₁.mapDerivedCategory.map (r₂.mapDerivedCategoryFactorsh.hom.app J) ≫
        r₁.mapDerivedCategoryFactorsh.hom.app ((r₂.mapHomotopyCategory _).obj J) := by
  simp [mapDerivedCategoryCompFactorsh]

/-- `mapDerivedCategoryCompFactorsh` as a lifting. It is not an instance, so that it does not
compete with other liftings of the composite. -/
abbrev mapDerivedCategoryCompLiftingh (r₂ : M₂ ⥤ M₁) (r₁ : M₁ ⥤ M₀) [r₁.Additive]
    [r₂.Additive] [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁]
    [PreservesFiniteLimits r₂] [PreservesFiniteColimits r₂] :
    Localization.Lifting DerivedCategory.Qh (HomotopyCategory.quasiIso M₂ (ComplexShape.up ℤ))
      ((r₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        r₁.mapHomotopyCategory (ComplexShape.up ℤ)) ⋙ DerivedCategory.Qh)
      (r₂.mapDerivedCategory ⋙ r₁.mapDerivedCategory) :=
  ⟨mapDerivedCategoryCompFactorsh r₂ r₁⟩

/-- **`r̄₂ ⋙ r̄₁ ≅ r̄`** for `e : r₂ ⋙ r₁ ≅ r`, as a lift along `DerivedCategory.Qh` of the
action of `e` on homotopy categories. -/
def mapDerivedCategoryCompIsoh (e : r₂ ⋙ r₁ ≅ r) :
    r₂.mapDerivedCategory ⋙ r₁.mapDerivedCategory ≅ r.mapDerivedCategory :=
  letI := mapDerivedCategoryCompLiftingh r₂ r₁
  Localization.liftNatIso DerivedCategory.Qh (HomotopyCategory.quasiIso M₂ (ComplexShape.up ℤ))
    ((r₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ r₁.mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
      DerivedCategory.Qh)
    (r.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) _ _
    (isoWhiskerRight (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- The value of `mapDerivedCategoryCompIsoh` at the image of an object of the homotopy
category. -/
theorem mapDerivedCategoryCompIsoh_hom_app_Qh (e : r₂ ⋙ r₁ ≅ r)
    (J : HomotopyCategory M₂ (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompIsoh e).hom.app (DerivedCategory.Qh.obj J) =
      r₁.mapDerivedCategory.map (r₂.mapDerivedCategoryFactorsh.hom.app J) ≫
        r₁.mapDerivedCategoryFactorsh.hom.app ((r₂.mapHomotopyCategory _).obj J) ≫
          DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J) ≫
            r.mapDerivedCategoryFactorsh.inv.app J := by
  let := mapDerivedCategoryCompLiftingh r₂ r₁
  rw [mapDerivedCategoryCompIsoh, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  show (mapDerivedCategoryCompFactorsh r₂ r₁).hom.app J ≫
    DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J) ≫
      r.mapDerivedCategoryFactorsh.inv.app J = _
  rw [mapDerivedCategoryCompFactorsh_hom_app, Category.assoc]

/-- **`r̄₂ ⋙ r̄₁ ≅ r̄` on bounded below derived categories**: `mapDerivedCategoryCompIsoh`
restricted along the fully faithful inclusion. -/
def mapDerivedCategoryPlusCompIsoh (e : r₂ ⋙ r₁ ≅ r) :
    r₂.mapDerivedCategoryPlus ⋙ r₁.mapDerivedCategoryPlus ≅ r.mapDerivedCategoryPlus :=
  (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryCompIsoh e))

/-- The inclusion of the bounded below subcategory carries `mapDerivedCategoryPlusCompIsoh` to
`mapDerivedCategoryCompIsoh`. -/
theorem ι_map_mapDerivedCategoryPlusCompIsoh_hom_app (e : r₂ ⋙ r₁ ≅ r)
    (K : DerivedCategory.Plus M₂) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusCompIsoh e).hom.app K) =
      (mapDerivedCategoryCompIsoh e).hom.app (DerivedCategory.Plus.ι.obj K) := by
  have h : Functor.whiskerRight (mapDerivedCategoryPlusCompIsoh e).hom DerivedCategory.Plus.ι =
      (Functor.isoWhiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryCompIsoh e)).hom :=
    (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).map_preimage _
  exact congr_app h K

/-- **The compatibility hypothesis of `CategoryTheory.Functor.derivedSquareMap_comp`** for the
transformation `mapDerivedCategoryPlusCompIsoh e` and the underived `e.hom`. -/
theorem mapDerivedCategoryPlusCompIsoh_compatible (e : r₂ ⋙ r₁ ≅ r)
    (L : HomotopyCategory.Plus M₂) :
    r₁.mapDerivedCategoryPlusFactorsh.inv.app (r₂.mapHomotopyCategoryPlus.obj L) ≫
        r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.inv.app L) ≫
          (mapDerivedCategoryPlusCompIsoh e).hom.app (DerivedCategory.Plus.Qh.obj L) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans e.hom).app L) ≫
        r.mapDerivedCategoryPlusFactorsh.inv.app L := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp]
  rw [ι_map_mapDerivedCategoryPlusCompIsoh_hom_app]
  show r₁.mapDerivedCategoryFactorsh.inv.app ((r₂.mapHomotopyCategory _).obj L.obj) ≫
      r₁.mapDerivedCategory.map (r₂.mapDerivedCategoryFactorsh.inv.app L.obj) ≫
        (mapDerivedCategoryCompIsoh e).hom.app (DerivedCategory.Qh.obj L.obj) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app L.obj) ≫
      r.mapDerivedCategoryFactorsh.inv.app L.obj
  refine Eq.trans (?_ : _ = DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app L.obj) ≫
        r.mapDerivedCategoryFactorsh.inv.app L.obj) ?_
  · rw [mapDerivedCategoryCompIsoh_hom_app_Qh]
    simp
  · exact congrArg (· ≫ r.mapDerivedCategoryFactorsh.inv.app L.obj)
      (congrArg DerivedCategory.Qh.map (mapHomotopyCategoryCompIso_hom_app_eq e L.obj))

end CategoryTheory.Functor
