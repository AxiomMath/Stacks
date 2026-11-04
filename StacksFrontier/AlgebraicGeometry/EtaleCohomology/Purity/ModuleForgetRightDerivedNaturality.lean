module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperVanishing

/-!
# Naturality of forgetting the module structure on derived categories

The identification of the underlying abelian sheaf of `R^q f_* G` with `R^q f_*` of the
underlying abelian sheaf of `G`, for a sheaf `G` of `Λ`-modules
(`Stacks.EtaleCohomology.etaleModuleForgetRightDerivedDirectImageIso`), is a composite of
components of natural isomorphisms, except for the identification of the forgetful functor with
placing in degree `n`, which is the preimage of one under the fully faithful inclusion of the
bounded below derived category. This file proves that that piece is natural too
(`Stacks.EtaleCohomology.etaleModuleForgetPlusSingleIso_hom_naturality`).

This is used to compare towers `n ↦ R¹ j_*(j⁻¹ Gₙ)` of sheaves of `ℤ_ℓ`-modules on underlying
abelian sheaves, in the tower form of cohomological purity
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.etaleModuleForgetPlusSingleIso_hom_naturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Placing in degree `n` commutes with forgetting the module structure, naturally.** -/
theorem etaleModuleForgetPlusSingleIso_hom_naturality (n : ℤ) {G G' : EtaleModules.{u, 0} Λ X}
    (w : G ⟶ G') :
    (etaleModuleForgetAb.{u, 0} Λ X).mapDerivedCategoryPlus.map
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) n).map w) ≫
      (etaleModuleForgetPlusSingleIso Λ X n G').hom =
    (etaleModuleForgetPlusSingleIso Λ X n G).hom ≫
      (DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) n).map
        ((etaleModuleForgetAb.{u, 0} Λ X).map w) := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  unfold etaleModuleForgetPlusSingleIso
  have e : ∀ H : EtaleModules.{u, 0} Λ X, DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.ι.preimage
        (X := (etaleModuleForgetAb.{u, 0} Λ X).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) n).obj H))
        (Y := (DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) n).obj
            ((etaleModuleForgetAb.{u, 0} Λ X).obj H))
        (((etaleModuleForgetAb.{u, 0} Λ X).mapDerivedCategorySingleFunctor n).app H).hom) =
      (((etaleModuleForgetAb.{u, 0} Λ X).mapDerivedCategorySingleFunctor n).app H).hom :=
    fun H => CategoryTheory.Functor.map_preimage _ _
  refine (congrArg (_ ≫ ·) (e G')).trans (Eq.trans ?_ (congrArg (· ≫ _) (e G)).symm)
  exact ((etaleModuleForgetAb.{u, 0} Λ X).mapDerivedCategorySingleFunctor n).hom.naturality w

end Stacks.EtaleCohomology

end
