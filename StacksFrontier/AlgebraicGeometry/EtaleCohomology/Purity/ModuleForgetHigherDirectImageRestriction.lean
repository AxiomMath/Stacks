module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.ModuleForgetRightDerivedDirectImageNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange

/-!
# `R^q j_*(j⁻¹ P)` on underlying abelian sheaves, naturally

For `j : U₀ ⟶ U` an open immersion and `P` a sheaf of `Λ`-modules on `U_étale`, the underlying
abelian sheaf of `R^q j_*(j⁻¹ P)` is `R^q j_*` of the inverse image of the underlying abelian sheaf
of `P` (`Stacks.EtaleCohomology.etaleModuleForgetHigherDirectImageRestrictionIso`), naturally in
`P` (`Stacks.EtaleCohomology.etaleModuleForgetHigherDirectImageRestrictionIso_hom_naturality`).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleForgetHigherDirectImageRestrictionIso`: the underlying
  abelian sheaf of `R^q j_*(j⁻¹ P)` is `R^q j_*` of the inverse image of the underlying abelian
  sheaf of `P`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleForgetHigherDirectImageRestrictionIso_hom_naturality`: this
  identification is natural in `P`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] {U₀ U : Scheme.{u}} (j : U₀ ⟶ U) [IsOpenImmersion j]

/-- **The underlying abelian sheaf of `R^q j_*(j⁻¹ P)` is `R^q j_*` of the inverse image of the
underlying abelian sheaf of `P`**, for a sheaf `P` of `Λ`-modules on `U_étale`. -/
def etaleModuleForgetHigherDirectImageRestrictionIso (P : EtaleModules.{u, 0} Λ U) (q : ℕ) :
    (etaleModuleForgetAb.{u, 0} Λ U).obj
        (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived q).obj
          ((etaleModuleRestriction.{u, 0} Λ j).obj P)) ≅
      ((smallEtalePushforwardAb j).rightDerived q).obj
        ((smallEtalePullbackAb j).obj ((etaleModuleForgetAb.{u, 0} Λ U).obj P)) :=
  etaleModuleForgetRightDerivedDirectImageIso Λ j _ q ≪≫
    ((smallEtalePushforwardAb j).rightDerived q).mapIso
      ((smallEtalePullbackAbIsoEtaleRestriction j).app
        ((etaleModuleForgetAb.{u, 0} Λ U).obj P)).symm

/-- **The identification of `R^q j_*(j⁻¹ P)` on underlying abelian sheaves is natural in `P`.** -/
theorem etaleModuleForgetHigherDirectImageRestrictionIso_hom_naturality (q : ℕ)
    {P P' : EtaleModules.{u, 0} Λ U} (w : P ⟶ P') :
    (etaleModuleForgetAb.{u, 0} Λ U).map (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived q).map
        ((etaleModuleRestriction.{u, 0} Λ j).map w)) ≫
      (etaleModuleForgetHigherDirectImageRestrictionIso Λ j P' q).hom =
    (etaleModuleForgetHigherDirectImageRestrictionIso Λ j P q).hom ≫
      ((smallEtalePushforwardAb j).rightDerived q).map
        ((smallEtalePullbackAb j).map ((etaleModuleForgetAb.{u, 0} Λ U).map w)) := by
  have h₁ := etaleModuleForgetRightDerivedDirectImageIso_hom_naturality Λ j q
    ((etaleModuleRestriction.{u, 0} Λ j).map w)
  have h₂ : ((smallEtalePushforwardAb j).rightDerived q).map
        ((etaleRestriction.{u, 0} j).map ((etaleModuleForgetAb.{u, 0} Λ U).map w)) ≫
      ((smallEtalePushforwardAb j).rightDerived q).map
        ((smallEtalePullbackAbIsoEtaleRestriction j).inv.app
          ((etaleModuleForgetAb.{u, 0} Λ U).obj P')) =
      ((smallEtalePushforwardAb j).rightDerived q).map
        ((smallEtalePullbackAbIsoEtaleRestriction j).inv.app
          ((etaleModuleForgetAb.{u, 0} Λ U).obj P)) ≫
      ((smallEtalePushforwardAb j).rightDerived q).map
        ((smallEtalePullbackAb j).map ((etaleModuleForgetAb.{u, 0} Λ U).map w)) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      (smallEtalePullbackAbIsoEtaleRestriction j).inv.naturality]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

end Stacks.EtaleCohomology

end
