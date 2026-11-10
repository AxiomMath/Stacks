module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.CompletedBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.SuccUniverseCoefficients
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleCompletedBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleDerivedTensorInvariance

/-!
# The completed base change map is an isomorphism modulo `I`

For a commutative square of schemes and a derived complete `K ∈ D(X_proét, Λ)`, the completed
base change map `Lg^*_comp Rf_* K ⟶ Rf'_* L(g')^*_comp K` is invertible as soon as the uncompleted
base change map is invertible at `K ⊗^L_Λ P`, where `P` is a bounded complex of finitely generated
projective `Λ`-modules representing `Λ/I`.

## Main results

* `AlgebraicGeometry.ProEtale.isIso_proetaleCompletedBaseChangeMap_of_isIso_baseChange`: the
  completed base change map at `K` is invertible once the base change map is
  invertible at `K ⊗^L_Λ P`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasSheafify_proEt_moduleCat_succ
  isGrothendieckAbelian_proetaleModuleSheaf_succ

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Countable products are exact in the category of `Λ`-modules. -/
local instance : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u + 1} Λ) :=
  moduleCat_hasExactLimitsOfShape_discrete.{u + 1} Λ ℕ

/-- The derived category of `Λ`-modules has countable products. -/
local instance : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u + 1} Λ)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

/-- A bounded above complex of projective modules is K-flat for the tensor product with
pro-étale sheaves of `Λ`-modules. -/
theorem isKFlat_proEt_of_projective (X : Scheme.{u}) (P : CochainComplex (ModuleCat.{u + 1} Λ) ℤ)
    (b : ℤ) [P.IsStrictlyLE b] [∀ q, Module.Projective Λ (P.X q)] :
    Stacks.DerivedTensor.IsKFlat (Stacks.ConstantModuleTensor.sheafTensor
      (Scheme.ProEt.topology X) Λ) P :=
  ⟨fun K hK => Stacks.ConstantModuleTensor.kFlat_of_isStrictlyLE_of_flat _ Λ P b K hK⟩

variable [IsNoetherianRing Λ] (I : Ideal Λ)

section BaseChange

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (w : f' ≫ g = g' ≫ f)

/-- **The completed base change map is an isomorphism once the base change map is one modulo
`I`**: if, for a K-injective complex `K'` representing `K`, the base change map is invertible at
`K' ⊗_Λ P` for a bounded complex `P` of finitely generated projective modules representing
`Λ/I`, then the completed base change map at `K` is invertible. -/
theorem isIso_proetaleCompletedBaseChangeMap_of_isIso_baseChange
    (K : ProetaleDerivedCategory Λ X)
    (P : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (a b : ℤ) [P.IsStrictlyLE b] [P.IsStrictlyGE a]
    [∀ q, Module.Finite Λ (P.X q)] [∀ q, Module.Projective Λ (P.X q)]
    (eP : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj (ModuleCat.of Λ (Λ ⧸ I)) ≅
      DerivedCategory.Q.obj P)
    (K' : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ)
    (hK' : K'.IsKInjective)
    (eK : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K') ≅ K)
    (hβ : IsIso ((proetaleModuleDerivedBaseChange.{u, u + 1, 0} f g f' g' w).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        ((Stacks.DerivedTensor.totRight (Stacks.ConstantModuleTensor.sheafTensor
          (Scheme.ProEt.topology X) Λ) P).obj K'))))) :
    IsIso (proetaleCompletedBaseChangeMap Λ I f g f' g' w K) := by
  have := isKFlat_proEt_of_projective Λ X' P b
  have := isKFlat_proEt_of_projective Λ Y' P b
  have hI : I.FG := IsNoetherian.noetherian I
  refine Stacks.ConstantModuleTensor.isIso_of_isIso_derivedTensor_map_baseChange
    (proetaleModuleDirectImage.{u, u + 1, 0} (Λ := Λ) f)
    (proetaleModuleInverseImage.{u, u + 1, 0} g Λ) (proetaleModuleInverseImage.{u, u + 1, 0} g' Λ)
    (proetaleModuleDirectImage.{u, u + 1, 0} (Λ := Λ) f')
    (proetaleModuleBaseChange.{u, u + 1, 0} f g f' g' w)
    (proetaleModuleDerivedDirectImage.{u, u + 1, 0} f)
    (proetaleModuleDerivedDirectImageUnit.{u, u + 1, 0} f)
    (proetaleModuleDerivedDirectImage.{u, u + 1, 0} f')
    (proetaleModuleDerivedDirectImageUnit.{u, u + 1, 0} f')
    I hI (proetaleCompletionAdjunction Λ I X') (proetaleCompletionAdjunction Λ I Y') P a b eP K
    (proetaleCompletedBaseChangeMap Λ I f g f' g' w K)
    (proetaleDerivedCompletionUnit_comp_proetaleCompletedBaseChangeMap Λ I f g f' g' w K)
    (isDerivedComplete_proetaleModuleDerivedDirectImage Λ I f'
      (isDerivedComplete_proetaleDerivedCompletion Λ I X' _)) ?_
  have hR3 := Stacks.ConstantModuleTensor.isIso_derivedTensor_map_baseChange_iff
    (proetaleModuleDirectImage.{u, u + 1, 0} (Λ := Λ) f)
    (proetaleModuleInverseImage.{u, u + 1, 0} g Λ) (proetaleModuleInverseImage.{u, u + 1, 0} g' Λ)
    (proetaleModuleDirectImage.{u, u + 1, 0} (Λ := Λ) f')
    (proetaleModuleBaseChange.{u, u + 1, 0} f g f' g' w)
    (proetaleModuleDerivedDirectImage.{u, u + 1, 0} f)
    (proetaleModuleDerivedDirectImageUnit.{u, u + 1, 0} f)
    (proetaleModuleDerivedDirectImage.{u, u + 1, 0} f')
    (proetaleModuleDerivedDirectImageUnit.{u, u + 1, 0} f')
    P a b K' hK'
  have hnat := (proetaleModuleDerivedBaseChange.{u, u + 1, 0} f g f' g' w).naturality eK.hom
  change IsIso ((Stacks.DerivedTensor.derivedTensor (Stacks.ConstantModuleTensor.sheafTensor
    (Scheme.ProEt.topology Y') Λ) P).map
      ((proetaleModuleDerivedBaseChange.{u, u + 1, 0} f g f' g' w).app K))
  rw [← isIso_comp_left_iff ((Stacks.DerivedTensor.derivedTensor
    (Stacks.ConstantModuleTensor.sheafTensor (Scheme.ProEt.topology Y') Λ) P).map
      ((proetaleModuleDerivedDirectImage.{u, u + 1, 0} f ⋙
        proetaleModuleDerivedInverseImage.{u, u + 1, 0} g).map eK.hom)), ← Functor.map_comp, hnat,
    Functor.map_comp, isIso_comp_right_iff]
  exact hR3.2 hβ

end BaseChange

end AlgebraicGeometry.ProEtale
