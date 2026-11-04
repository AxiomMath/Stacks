module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.ConstantAdicQuotientTower
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Linear
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Products
public import StacksFrontier.Homology.DerivedComplete

/-!
# The tower of derived reductions of a complex of sheaves of modules

Let `(C, J)` be a site, `Λ` a commutative ring and `I ⊆ Λ` an ideal. For an object `K` of the
derived category `D(C, Λ)` of sheaves of `Λ`-modules, the derived reductions
`K ⊗_Λ^L \underline{Λ/Iⁿ}` form an inverse system indexed by `n`, whose transition maps are
induced by the reductions `Λ/Iⁿ⁺¹ → Λ/Iⁿ`, and the maps `K → K ⊗_Λ^L \underline{Λ/Iⁿ}` induced
by `Λ → Λ/Iⁿ` are compatible with them. Every term of the tower is derived complete with respect
to `I`: multiplication by `f ∈ I` is nilpotent on it, since `fⁿ` kills `Λ/Iⁿ` and the derived
tensor product is `Λ`-linear.

## Main definitions

* `Stacks.ModuleSheaf.quotientPowerTower`: the tower `n ↦ \underline{Λ/Iⁿ}` in `D(C, Λ)`.
* `Stacks.ModuleSheaf.unitToQuotientPowerTower`: the maps from the unit object induced by
  `Λ → Λ/Iⁿ`.
* `Stacks.ModuleSheaf.derivedReductionTower`: the tower `n ↦ K ⊗_Λ^L \underline{Λ/Iⁿ}`.
* `Stacks.ModuleSheaf.derivedReductionMap`: the maps `K → K ⊗_Λ^L \underline{Λ/Iⁿ}`.
* `Stacks.ModuleSheaf.derivedReductionTowerFunctor`, `Stacks.ModuleSheaf.derivedReductionNatTrans`:
  the tower and the maps to it, functorially in `K`.

## Main results

* `Stacks.ModuleSheaf.isDerivedComplete_derivedReductionTower_obj`: every term of the tower is
  derived complete with respect to `I`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe t w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
  CochainComplex.braidedCategory derivedMonoidal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}]

variable {J Λ} in
/-- The constant sheaf functor is `Λ`-linear. -/
theorem constantSheaf_map_smul {M N : ModuleCat.{w} Λ} (a : Λ) (g : M ⟶ N) :
    (constantSheaf J (ModuleCat.{w} Λ)).map (a • g) =
      a • (constantSheaf J (ModuleCat.{w} Λ)).map g := by
  show (presheafToSheaf J _).map ((Functor.const _).map (a • g)) =
    a • (presheafToSheaf J _).map ((Functor.const _).map g)
  rw [← Functor.map_smul]
  rfl

/-- The unit sheaf of `Λ`-modules is the constant sheaf `\underline{Λ}`. -/
def tensorUnitIsoConstantSheaf :
    𝟙_ (Sheaf J (ModuleCat.{w} Λ)) ≅ (constantSheaf J (ModuleCat.{w} Λ)).obj (ModuleCat.of Λ Λ) :=
  Iso.refl _

variable [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))] (I : Ideal Λ)

/-- The tower `n ↦ \underline{Λ/Iⁿ}` of constant sheaves placed in degree zero, in `D(C, Λ)`. -/
abbrev quotientPowerTower : ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) :=
  constantAdicQuotientTower J Λ I (ModuleCat.of Λ Λ) ⋙ DerivedCategory.singleFunctor _ 0

/-- The unit of the derived tensor product of `D(C, Λ)` is `\underline{Λ}` in degree zero. -/
def derivedTensorUnitIso :
    𝟙_ (DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf J (ModuleCat.{w} Λ)).obj (ModuleCat.of Λ Λ)) :=
  CochainComplex.KFlatMonoidal.derivedUnitIso _ (exists_kFlat_quasiIso (J := J) (Λ := Λ)) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ _ 0).symm.app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (tensorUnitIsoConstantSheaf J Λ)

/-- The maps `𝟙 ≅ \underline{Λ} → \underline{Λ/Iⁿ}` from the unit object of `D(C, Λ)` to the
tower of quotients. -/
def unitToQuotientPowerTower :
    (Functor.const ℕᵒᵖ).obj (𝟙_ (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))) ⟶
      quotientPowerTower J Λ I :=
  (Functor.const ℕᵒᵖ).map (derivedTensorUnitIso J Λ).hom ≫
    (Functor.constComp ℕᵒᵖ _ (DerivedCategory.singleFunctor _ 0)).inv ≫
      Functor.whiskerRight (constantAdicQuotientCone J Λ I (ModuleCat.of Λ Λ))
        (DerivedCategory.singleFunctor _ 0)

/-- **The tower of derived reductions** `n ↦ K ⊗_Λ^L \underline{Λ/Iⁿ}` of an object `K` of
`D(C, Λ)`, with the transition maps induced by the reductions `Λ/Iⁿ⁺¹ → Λ/Iⁿ`. -/
abbrev derivedReductionTower (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) :=
  quotientPowerTower J Λ I ⋙ tensorLeft K

/-- The maps `K ≅ K ⊗_Λ^L \underline{Λ} → K ⊗_Λ^L \underline{Λ/Iⁿ}` induced by the reductions
`Λ → Λ/Iⁿ`, a map from the constant tower `K` to the tower of derived reductions. -/
def derivedReductionMap (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    (Functor.const ℕᵒᵖ).obj K ⟶ derivedReductionTower J Λ I K :=
  (Functor.const ℕᵒᵖ).map (ρ_ K).inv ≫
    (Functor.constComp ℕᵒᵖ _ (tensorLeft K)).inv ≫
      Functor.whiskerRight (unitToQuotientPowerTower J Λ I) (tensorLeft K)

/-- The `n`-th component of `derivedReductionMap` is the inverse right unitor of `K` followed by
`K` tensored with the `n`-th component of `unitToQuotientPowerTower`. -/
theorem derivedReductionMap_app (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (n : ℕᵒᵖ) :
    (derivedReductionMap J Λ I K).app n =
      (ρ_ K).inv ≫ K ◁ (unitToQuotientPowerTower J Λ I).app n := by
  simp [derivedReductionMap]

/-- The tower of derived reductions, as a functor of the object being reduced. -/
abbrev derivedReductionTowerFunctor :
    DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) ⥤
      ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) :=
  curriedTensor _ ⋙ (Functor.whiskeringLeft ℕᵒᵖ _ _).obj (quotientPowerTower J Λ I)

/-- The functor `derivedReductionTowerFunctor` sends `K` to its tower of derived reductions. -/
@[simp]
theorem derivedReductionTowerFunctor_obj (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    (derivedReductionTowerFunctor J Λ I).obj K = derivedReductionTower J Λ I K :=
  rfl

/-- The maps `K → K ⊗_Λ^L \underline{Λ/Iⁿ}` are natural in `K`. -/
theorem derivedReductionMap_naturality {K K' : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))}
    (g : K ⟶ K') (n : ℕᵒᵖ) :
    g ≫ (derivedReductionMap J Λ I K').app n =
      (derivedReductionMap J Λ I K).app n ≫ g ▷ (quotientPowerTower J Λ I).obj n := by
  rw [derivedReductionMap_app, derivedReductionMap_app, Category.assoc, whisker_exchange,
    rightUnitor_inv_naturality_assoc]

/-- The maps `K → K ⊗_Λ^L \underline{Λ/Iⁿ}`, as a natural transformation from the constant
towers to the towers of derived reductions. -/
def derivedReductionNatTrans : Functor.const ℕᵒᵖ ⟶ derivedReductionTowerFunctor J Λ I where
  app K := derivedReductionMap J Λ I K
  naturality K K' g := by
    ext n
    exact derivedReductionMap_naturality J Λ I g n

/-- Multiplication by `f ∈ I` on the constant sheaf `\underline{Λ/Iⁿ}` placed in degree zero has
`n`-th power zero. -/
theorem pow_smul_id_quotientPowerTower_obj {f : Λ} (hf : f ∈ I) (n : ℕ) :
    f ^ n • 𝟙 ((quotientPowerTower J Λ I).obj (Opposite.op n)) = 0 := by
  have h : f ^ n • 𝟙 ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem Λ I
      (ModuleCat.of Λ Λ)).obj (Opposite.op n)) = 0 := by
    ext x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show (Submodule.Quotient.mk (f ^ n • y) : Λ ⧸ (I ^ n • ⊤ : Submodule Λ Λ)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hf n) Submodule.mem_top
  show f ^ n • 𝟙 ((DerivedCategory.singleFunctor _ 0).obj ((constantSheaf J _).obj _)) = 0
  rw [← (DerivedCategory.singleFunctor _ 0).map_id, ← (constantSheaf J _).map_id,
    ← Functor.map_smul, ← constantSheaf_map_smul, h, Functor.map_zero, Functor.map_zero]

/-- **Every term of the tower of derived reductions is derived complete** with respect to `I`:
multiplication by `f ∈ I` on `K ⊗_Λ^L \underline{Λ/Iⁿ}` has `n`-th power zero. -/
theorem isDerivedComplete_derivedReductionTower_obj
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (n : ℕᵒᵖ) :
    IsDerivedComplete I ((derivedReductionTower J Λ I K).obj n) := by
  intro f hf
  refine isDerivedCompleteAt_of_isNilpotent ⟨n.unop, ?_⟩
  rw [smul_id_pow]
  show f ^ n.unop • 𝟙 (K ⊗ (quotientPowerTower J Λ I).obj (Opposite.op n.unop)) = 0
  rw [← derived_whiskerLeft_smul_id, pow_smul_id_quotientPowerTower_obj J Λ I hf,
    ← zero_smul Λ (𝟙 ((quotientPowerTower J Λ I).obj (Opposite.op n.unop))),
    derived_whiskerLeft_smul_id, zero_smul]

end Stacks.ModuleSheaf
