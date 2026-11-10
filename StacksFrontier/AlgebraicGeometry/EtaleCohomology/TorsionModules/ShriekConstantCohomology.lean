module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CoefficientFunctorCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer

/-!
# Finiteness of the cohomology of `j_!(M̲)` through `j_!(ℤ/ℓ)`

Let `Λ` be a Noetherian ring, `X` a quasi-compact and quasi-separated scheme and `j : U ⟶ X` an
étale morphism. For a finite `Λ`-module `M` killed by an integer `n > 0`, the cohomology
`H^q(X, j_!(M̲))` of the extension by zero of the constant sheaf of `Λ`-modules `M̲` on `U` is a
finite `Λ`-module as soon as the abelian groups `H^q(X, j_!(ℤ/ℓ))` are finite for the primes `ℓ`
dividing `n`. This is the coefficient-functor form of the `𝔽_ℓ`-basis trick of [Stacks, Tag 0GJC]
(`Stacks.EtaleCohomology.module_finite_coefficientCohomology_of_nsmul_eq_zero`) for the functor
`M ↦ j_!(M̲)`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleShriekConstant`: the functor `M ↦ j_!(M̲)` on `Λ`-modules.
* `Stacks.EtaleCohomology.etaleAbelianShriekConstant`: the functor `A ↦ j_!(A̲)` on abelian
  groups.
* `Stacks.EtaleCohomology.etaleModuleForgetExtensionByZeroIso`: forgetting the module structure
  commutes with extension by zero.

## Main results

* `Stacks.EtaleCohomology.module_finite_etaleCohomology_etaleModuleShriekConstant`: the finiteness
  statement above.

## Implementation notes

Forgetting the module structure commutes with extension by zero because extension by zero is the
sheafification of a left Kan extension, the forgetful functor `ModuleCat Λ ⥤ Ab` preserves all
colimits, hence all pointwise left Kan extensions, and it commutes with sheafification on the
small étale site. The comparison is
`Stacks.EtaleCohomology.coefficientPullbackTwoSquare`, invertible by
`Stacks.EtaleCohomology.isIso_coefficientPullbackTwoSquare`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

section Functors

variable (Λ : Type r) [CommRing Λ] {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- The functor `M ↦ j_!(M̲)` from `Λ`-modules to sheaves of `Λ`-modules on `X_étale`, for an
étale morphism `j : U ⟶ X`: the constant sheaf on `U` followed by extension by zero. -/
abbrev etaleModuleShriekConstant : ModuleCat.{max (u + 1) r} Λ ⥤ EtaleModules.{u, r} Λ X :=
  constantSheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) ⋙
    etaleModuleExtensionByZero.{u, r} Λ j

/-- The functor `A ↦ j_!(A̲)` from abelian groups to abelian sheaves on `X_étale`, for an étale
morphism `j : U ⟶ X`. -/
abbrev etaleAbelianShriekConstant :
    AddCommGrpCat.{max (u + 1) r} ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r} :=
  constantSheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) r} ⋙ extensionByZero.{u, r} j

attribute [local instance] preservesSheafification_forget₂_moduleCat_smallEtale

/-- **Forgetting the module structure commutes with extension by zero**: the abelian sheaf
underlying `j_! G` is `j_!` of the abelian sheaf underlying `G`, naturally in the sheaf of
`Λ`-modules `G`. -/
def etaleModuleForgetExtensionByZeroIso :
    etaleModuleExtensionByZero.{u, r} Λ j ⋙ etaleModuleForgetAb.{u, r} Λ X ≅
      etaleModuleForgetAb.{u, r} Λ U ⋙ extensionByZero.{u, r} j :=
  (asIso (coefficientPullbackTwoSquare (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology
    X.smallEtaleTopology
    (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}))).symm

/-- The comparison of the coefficient-functor formalism for `M ↦ j_!(M̲)`: the abelian sheaf
underlying `j_!(M̲)` is `j_!` of the constant abelian sheaf on the underlying group of `M`. -/
def etaleModuleShriekConstantForgetIso :
    etaleModuleShriekConstant.{u, r} Λ j ⋙ etaleModuleForgetAb.{u, r} Λ X ≅
      forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r} ⋙
        etaleAbelianShriekConstant.{u, r} j :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleForgetExtensionByZeroIso.{u, r} Λ j) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etaleModuleForgetConstantSheafIso.{u, r} Λ U) _ ≪≫
    Functor.associator _ _ _

end Functors

section Properties

variable (Λ : Type r) [CommRing Λ] {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- **A left adjoint of a `Λ`-linear functor carries multiplication by a scalar to multiplication
by that scalar.** The adjoint transpose of `L.map (a • 𝟙 G)` is `(a • 𝟙 G) ≫ η = a • η`, which is
also the adjoint transpose of `a • 𝟙 (L G)`. -/
theorem map_smul_id_of_adjunction {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] [Linear Λ C] [Linear Λ D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hR : ∀ {M N : D} (a : Λ) (f : M ⟶ N), R.map (a • f) = a • R.map f) (G : C) (a : Λ) :
    L.map (a • 𝟙 G) = a • 𝟙 (L.obj G) := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, hR, CategoryTheory.Functor.map_id,
    Linear.comp_smul]
  have h := adj.unit_naturality (a • 𝟙 G)
  rw [Linear.smul_comp, Category.id_comp] at h
  rw [h]
  exact congrArg (a • ·) (Category.comp_id _).symm

/-- **Extension by zero of sheaves of `Λ`-modules carries multiplication by a scalar to
multiplication by that scalar**: it is left adjoint to restriction, which is computed sectionwise.
-/
theorem etaleModuleExtensionByZero_map_smul_id (G : EtaleModules.{u, r} Λ U) (a : Λ) :
    (etaleModuleExtensionByZero.{u, r} Λ j).map (a • 𝟙 G) = a • 𝟙 _ :=
  map_smul_id_of_adjunction Λ (etaleModuleExtensionByZeroAdj.{u, r} Λ j) (fun _ _ => rfl) G a

/-- **The functor `M ↦ j_!(M̲)` carries multiplication by a scalar to multiplication by that
scalar.** -/
theorem etaleModuleShriekConstant_map_smul_id (M : ModuleCat.{max (u + 1) r} Λ) (a : Λ) :
    (etaleModuleShriekConstant.{u, r} Λ j).map (a • 𝟙 M) = a • 𝟙 _ := by
  have : Functor.Linear Λ (constantSheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) :=
    inferInstanceAs (Functor.Linear Λ (Functor.const U.Etaleᵒᵖ ⋙
      presheafToSheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)))
  change (etaleModuleExtensionByZero.{u, r} Λ j).map
    ((constantSheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).map (a • 𝟙 M)) = _
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, etaleModuleExtensionByZero_map_smul_id]
  rfl

/-- The functor `A ↦ j_!(A̲)` from abelian groups to abelian sheaves on `X_étale` is additive.
-/
instance etaleAbelianShriekConstant_additive : (etaleAbelianShriekConstant.{u, r} j).Additive :=
  haveI : (constantSheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).Additive :=
    (constantSheafAdj U.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}
      (etaleSiteTerminalIsTerminal U)).left_adjoint_additive
  haveI : (extensionByZero.{u, r} j).Additive := (extensionByZeroAdj.{u, r} j).left_adjoint_additive
  inferInstance

/-- The functor `A ↦ j_!(A̲)` commutes with all colimits, being a composite of left adjoints. -/
theorem etaleAbelianShriekConstant_preservesColimitsOfShape (J : Type (max (u + 1) r))
    [SmallCategory J] : PreservesColimitsOfShape J (etaleAbelianShriekConstant.{u, r} j) :=
  have : PreservesColimitsOfShape J
      (constantSheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) :=
    (constantSheafAdj U.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}
      (etaleSiteTerminalIsTerminal U)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape J (extensionByZero.{u, r} j) :=
    (extensionByZeroAdj.{u, r} j).leftAdjoint_preservesColimits.preservesColimitsOfShape
  inferInstance

/-- The functor `M ↦ j_!(M̲)` from `Λ`-modules to sheaves of `Λ`-modules on `X_étale` preserves
finite colimits, being a composite of left adjoints. -/
instance etaleModuleShriekConstant_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModuleShriekConstant.{u, r} Λ j) :=
  haveI : PreservesFiniteColimits
      (constantSheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) :=
    (constantSheafAdj U.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
      (etaleSiteTerminalIsTerminal U)).leftAdjoint_preservesColimits.{0, 0}.preservesFiniteColimits
  inferInstance

/-- The functor `M ↦ j_!(M̲)` from `Λ`-modules to sheaves of `Λ`-modules on `X_étale` preserves
finite limits: it is exact. -/
instance etaleModuleShriekConstant_preservesFiniteLimits :
    PreservesFiniteLimits (etaleModuleShriekConstant.{u, r} Λ j) :=
  inferInstance

end Properties

section Finiteness

attribute [local instance] HasDerivedCategory.standard

/-- The global sections functor `Γ(X, -)` on abelian sheaves on `X_étale` is additive. -/
local instance (X : Scheme.{u}) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).Additive :=
  Functor.additive_of_preserves_binary_products _

variable {Λ : Type r} [CommRing Λ] [IsNoetherianRing Λ] {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  [CompactSpace X] [QuasiSeparatedSpace X]

/-- **The cohomology of `j_!(M̲)` is a finite `Λ`-module once that of `j_!(ℤ/ℓ)` is finite.** Let
`Λ` be Noetherian, `X` quasi-compact and quasi-separated, `j : U ⟶ X` étale, and `n > 0` an
integer such that `H^q(X, j_!(ℤ/ℓ))` is finite for every prime `ℓ` dividing `n` and every `q`.
Then `H^q(X, j_!(M̲))` is a finite `Λ`-module for every finite `Λ`-module `M` killed by `n`. -/
theorem module_finite_etaleCohomology_etaleModuleShriekConstant (n : ℕ) (hn : 0 < n)
    (hfin : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ∀ q : ℕ,
      Finite (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived q).obj
        ((etaleAbelianShriekConstant.{u, r} j).obj
          (AddCommGrpCat.of (ULift.{max (u + 1) r} (ZMod ℓ))))))
    (M : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ M] (hM : ∀ m : M, n • m = 0) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((etaleModuleShriekConstant.{u, r} Λ j).obj M)) :=
  module_finite_coefficientCohomology_of_nsmul_eq_zero
    (etaleModuleShriekConstantForgetIso.{u, r} Λ j)
    (fun J _ _ => etaleAbelianShriekConstant_preservesColimitsOfShape j J)
    (etaleModuleShriekConstant_map_smul_id Λ j) n hn hfin M hM q

end Finiteness

end Stacks.EtaleCohomology

end
