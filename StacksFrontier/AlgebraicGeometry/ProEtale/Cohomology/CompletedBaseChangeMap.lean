module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ModuleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.SuccUniverseCoefficients
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ModuleComparisonWithEtale
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleDerivedTensor
public import StacksFrontier.Homology.DerivedComplete.TriangulatedReflection
public import StacksFrontier.Homology.DerivedComplete.LinearFunctor
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts
public import StacksFrontier.Homology.Injectives.Spaltenstein.Enlargement
public import StacksFrontier.RingTheory.LocalCohomology.ArtinianOverLocalRing
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic

/-!
# The completed base change map on pro-étale sites

Let `Λ` be a Noetherian ring and `I ⊆ Λ` an ideal. On the unbounded derived category
`D(X_proét, Λ)` of pro-étale sheaves of `Λ`-modules of a scheme `X` this file sets up:
countable products, derived completeness along `I` (Stacks 091S), derived completion (the left
adjoint of the inclusion of the derived complete objects, Stacks 099F), the completed pullback
`Lg^*_comp = (g⁻¹ -)^∧`, the derived reductions `K ⊗^L_Λ Λ/Iⁿ`, and the completed base change
map `Lg^*_comp Rf_* K ⟶ Rf'_* L(g')^*_comp K` of a commutative square of schemes, which is the
unique map out of the completion compatible with the uncompleted base change map.

## Main definitions

* `AlgebraicGeometry.ProEtale.proetaleDerivedCompletion`: derived completion along `I`.
* `AlgebraicGeometry.ProEtale.proetaleCompletedInverseImage`: `Lg^*_comp`.
* `AlgebraicGeometry.ProEtale.proetaleDerivedReduction`: `K ↦ K ⊗^L_Λ Λ/Iⁿ`.
* `AlgebraicGeometry.ProEtale.proetaleCompletedBaseChangeMap`: the completed base change map.

## Implementation notes

The coefficient ring and the sections of the sheaves live in one universe `u + 1` above that of
the schemes, which is where the tensor products of `Λ`-modules are formed. Standard model:
uses `AlgebraicGeometry.ProEtale.proetaleModuleDerivedDirectImage`, which exists only there.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u



namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasSheafify_proEt_moduleCat_succ
  isGrothendieckAbelian_proetaleModuleSheaf_succ

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- `D(X_proét, Λ)`: the unbounded derived category of pro-étale sheaves of `Λ`-modules. -/
abbrev ProetaleDerivedCategory (X : Scheme.{u}) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))

/-- Colimits indexed by `ℕ` are exact in the category of pro-étale sheaves of `Λ`-modules. -/
instance hasExactColimitsOfShape_nat_proetaleModuleSheaf (X : Scheme.{u}) :
    HasExactColimitsOfShape ℕ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) := by
  have := isGrothendieckAbelian_proetaleModuleSheaf.{u, u + 1, 0} Λ X
  infer_instance

/-- `D(X_proét, Λ)` has countable products. -/
instance hasProductsOfShape_nat_proetaleDerivedCategory (X : Scheme.{u}) :
    HasProductsOfShape ℕ (ProetaleDerivedCategory Λ X) := by
  have := isGrothendieckAbelian_proetaleModuleSheaf.{u, u + 1, 0} Λ X
  obtain ⟨NR⟩ := Stacks.Injectives.FunctorialEnlargement.exists_functorial_quasiIso_isKInjective
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
  exact Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_of_exists_quasiIso_isKInjective
    fun K => ⟨_, NR.inclusion.app K, NR.isKInjective K, NR.quasiIso K⟩


/-! ### Linearity of the derived direct and inverse images -/

/-- The direct image of pro-étale sheaves of `Λ`-modules is `Λ`-linear. -/
instance linear_proetaleModuleDirectImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    (proetaleModuleDirectImage.{u, u + 1, 0} (Λ := Λ) g).Linear Λ where
  map_smul _ _ := rfl

/-- The inverse image of pro-étale sheaves of `Λ`-modules is `Λ`-linear. -/
instance linear_proetaleModuleInverseImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    (proetaleModuleInverseImage.{u, u + 1, 0} g Λ).Linear Λ :=
  leftAdjoint_linear_of_rightAdjoint_linear Λ
    (proetaleModuleInverseImageAdjunction.{u, u + 1, 0} Λ g)

/-- The derived inverse image `g⁻¹` on `D(X_proét, Λ)` is `Λ`-linear. -/
instance linear_proetaleModuleDerivedInverseImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    (proetaleModuleDerivedInverseImage.{u, u + 1, 0} (Λ := Λ) g).Linear Λ := by
  dsimp only [proetaleModuleDerivedInverseImage]
  infer_instance

/-- The derived direct image `Rg_*` on `D(Z_proét, Λ)` is additive. -/
instance additive_proetaleModuleDerivedDirectImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    (proetaleModuleDerivedDirectImage.{u, u + 1, 0} (Λ := Λ) g).Additive := by
  have :=
    (proetaleModuleDerivedAdjunction.{u, u + 1, 0} (Λ := Λ) g).rightAdjoint_preservesLimits.{0, 0}
  exact Functor.additive_of_preserves_binary_products _

/-- The derived direct image `Rg_*` on `D(Z_proét, Λ)` is `Λ`-linear. -/
instance linear_proetaleModuleDerivedDirectImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    (proetaleModuleDerivedDirectImage.{u, u + 1, 0} (Λ := Λ) g).Linear Λ :=
  Stacks.LocalCohomology.rightAdjoint_linear (proetaleModuleDerivedAdjunction.{u, u + 1, 0} g)

/-! ### Derived completion and the completed pullback -/

variable [IsNoetherianRing Λ] (I : Ideal Λ)

/-- The inclusion of the derived complete objects of `D(X_proét, Λ)` is a right adjoint. -/
instance isRightAdjoint_ι_isDerivedComplete_proetale (X : Scheme.{u}) :
    (ObjectProperty.ι
      (IsDerivedComplete I : ObjectProperty (ProetaleDerivedCategory Λ X))).IsRightAdjoint :=
  DerivedCompletionReflection.isRightAdjoint_ι_isDerivedComplete I (IsNoetherian.noetherian I)

/-- The derived completion along `I`, as a left adjoint of the inclusion of the derived complete
objects of `D(X_proét, Λ)` (Stacks 099F). -/
def proetaleCompletionAdjunction (X : Scheme.{u}) :
    (ObjectProperty.ι
        (IsDerivedComplete I : ObjectProperty (ProetaleDerivedCategory Λ X))).leftAdjoint ⊣
      ObjectProperty.ι (IsDerivedComplete I : ObjectProperty (ProetaleDerivedCategory Λ X)) :=
  Adjunction.ofIsRightAdjoint _

/-- **Derived completion** `K ↦ K^∧` on `D(X_proét, Λ)`. -/
def proetaleDerivedCompletion (X : Scheme.{u}) :
    ProetaleDerivedCategory Λ X ⥤ ProetaleDerivedCategory Λ X :=
  (ObjectProperty.ι
      (IsDerivedComplete I : ObjectProperty (ProetaleDerivedCategory Λ X))).leftAdjoint ⋙
    ObjectProperty.ι _

/-- The completion map `K ⟶ K^∧`. -/
def proetaleDerivedCompletionUnit (X : Scheme.{u}) :
    𝟭 _ ⟶ proetaleDerivedCompletion Λ I X :=
  (proetaleCompletionAdjunction Λ I X).unit

/-- The derived completion `K^∧` is derived complete. -/
theorem isDerivedComplete_proetaleDerivedCompletion (X : Scheme.{u})
    (K : ProetaleDerivedCategory Λ X) :
    IsDerivedComplete I ((proetaleDerivedCompletion Λ I X).obj K) :=
  ((ObjectProperty.ι (IsDerivedComplete I :
    ObjectProperty (ProetaleDerivedCategory Λ X))).leftAdjoint.obj K).property

/-- **The completed pullback** `Lg^*_comp K = (g⁻¹ K)^∧`. -/
def proetaleCompletedInverseImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    ProetaleDerivedCategory Λ X ⥤ ProetaleDerivedCategory Λ Z :=
  proetaleModuleDerivedInverseImage.{u, u + 1, 0} g ⋙ proetaleDerivedCompletion Λ I Z

/-- The derived direct image `Rg_*` preserves countable products. -/
instance preservesProducts_proetaleModuleDerivedDirectImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    PreservesLimitsOfShape (Discrete ℕ)
      (proetaleModuleDerivedDirectImage.{u, u + 1, 0} (Λ := Λ) g) :=
  (proetaleModuleDerivedAdjunction.{u, u + 1, 0} g).rightAdjoint_preservesLimits
    |>.preservesLimitsOfShape

omit [IsNoetherianRing Λ] in
/-- `Rf_*` preserves derived completeness (Stacks 099N (1)). -/
theorem isDerivedComplete_proetaleModuleDerivedDirectImage {Z X : Scheme.{u}} (g : Z ⟶ X)
    {K : ProetaleDerivedCategory Λ Z} (hK : IsDerivedComplete I K) :
    IsDerivedComplete I ((proetaleModuleDerivedDirectImage.{u, u + 1, 0} g).obj K) :=
  DerivedCompletionReflection.isDerivedComplete_obj _ hK

section BaseChange

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (w : f' ≫ g = g' ≫ f)

/-- **The completed base change map** `Lg^*_comp Rf_* K ⟶ Rf'_* L(g')^*_comp K` of a commutative
square of schemes: the unique map out of the completion `(g⁻¹ Rf_* K)^∧` whose composite with the
completion map is the base change map `g⁻¹ Rf_* K ⟶ Rf'_* (g')⁻¹ K` followed by `Rf'_*` of the
completion map of `(g')⁻¹ K`. Its target is derived complete because `Rf'_*` preserves derived
completeness. -/
def proetaleCompletedBaseChangeMap (K : ProetaleDerivedCategory Λ X) :
    (proetaleCompletedInverseImage Λ I g).obj
        ((proetaleModuleDerivedDirectImage.{u, u + 1, 0} f).obj K) ⟶
      (proetaleModuleDerivedDirectImage.{u, u + 1, 0} f').obj
        ((proetaleCompletedInverseImage Λ I g').obj K) :=
  (ObjectProperty.ι _).map (((proetaleCompletionAdjunction Λ I Y').homEquiv _
    ⟨_, isDerivedComplete_proetaleModuleDerivedDirectImage Λ I f'
      (isDerivedComplete_proetaleDerivedCompletion Λ I X' _)⟩).symm
    (proetaleModuleDerivedBaseChangeMap f g f' g' w K ≫
      (proetaleModuleDerivedDirectImage.{u, u + 1, 0} f').map
        ((proetaleDerivedCompletionUnit Λ I X').app _)))

/-- The defining property of the completed base change map. -/
theorem proetaleDerivedCompletionUnit_comp_proetaleCompletedBaseChangeMap
    (K : ProetaleDerivedCategory Λ X) :
    (proetaleDerivedCompletionUnit Λ I Y').app _ ≫
        proetaleCompletedBaseChangeMap Λ I f g f' g' w K =
      proetaleModuleDerivedBaseChangeMap f g f' g' w K ≫
        (proetaleModuleDerivedDirectImage.{u, u + 1, 0} f').map
          ((proetaleDerivedCompletionUnit Λ I X').app _) := by
  unfold proetaleCompletedBaseChangeMap proetaleDerivedCompletionUnit
  exact (((proetaleCompletionAdjunction Λ I Y').homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _))

end BaseChange

/-! ### Derived reduction -/

/-- **The derived reduction** `K ↦ K ⊗^L_Λ Λ/Iⁿ` on `D(X_proét, Λ)`. -/
def proetaleDerivedReduction (X : Scheme.{u}) (n : ℕ) :
    ProetaleDerivedCategory Λ X ⥤ ProetaleDerivedCategory Λ X :=
  Stacks.ConstantModuleTensor.derivedTensor (Scheme.ProEt.topology X) Λ
    (ModuleCat.of Λ (Λ ⧸ I ^ n))

end AlgebraicGeometry.ProEtale
