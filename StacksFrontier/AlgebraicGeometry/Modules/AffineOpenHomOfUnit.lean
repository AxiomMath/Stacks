module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineRestrictSections

/-!
# Morphisms into a module supported on an affine open

Let `U` be an affine open of a scheme `X` with inclusion `ι : U ⟶ X`, and let `F` be a
quasi-coherent `𝒪_X`-module for which the unit `F ⟶ ι_* ι^* F` is an isomorphism. Then for every
quasi-coherent `𝒪_X`-module `N`, a morphism `N ⟶ F` is the same datum as a `Γ(X, U)`-linear map
`Γ(N, U) → Γ(F, U)`: it is determined by its action on sections over `U`, and every such linear
map arises.

## Main results

* `Stacks.AlgebraicGeometry.hom_ext_of_app_affineOpen_of_isIso_unit`
* `Stacks.AlgebraicGeometry.exists_hom_app_affineOpen_of_isIso_unit`
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry

open ModuleLimits

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) {N F : X.Modules}
  [N.IsQuasicoherent] [F.IsQuasicoherent]
  (hF : IsIso ((Scheme.Modules.restrictAdjunction U.ι).unit.app F))
include hU hF

/-- Two morphisms into a module supported on an affine open `U` agree as soon as they agree on
sections over `U`. -/
theorem hom_ext_of_app_affineOpen_of_isIso_unit {φ φ' : N ⟶ F}
    (h : ∀ n : Γ(N, U), φ.app U n = φ'.app U n) : φ = φ' := by
  have hr : (Scheme.Modules.restrictFunctor U.ι).map φ =
      (Scheme.Modules.restrictFunctor U.ι).map φ' :=
    restrictSections_ext_of_isAffineOpen hU fun n => by
      rw [restrictSections_restrictFunctor_map, restrictSections_restrictFunctor_map, h n]
  have hu : φ ≫ (Scheme.Modules.restrictAdjunction U.ι).unit.app F =
      φ' ≫ (Scheme.Modules.restrictAdjunction U.ι).unit.app F := by
    rw [← Adjunction.unit_naturality, ← Adjunction.unit_naturality, hr]
  exact (cancel_mono _).1 hu

/-- Every `Γ(X, U)`-linear map on sections over an affine open `U` into a module supported on `U`
is the action on sections of a morphism of `𝒪_X`-modules. -/
theorem exists_hom_app_affineOpen_of_isIso_unit (l : Γ(N, U) →ₗ[Γ(X, U)] Γ(F, U)) :
    ∃ φ : N ⟶ F, ∀ n : Γ(N, U), φ.app U n = l n := by
  obtain ⟨θ, hθ⟩ := exists_restrictSections_eq_of_isAffineOpen (M := N) (N := F) hU l
  let adj := Scheme.Modules.restrictAdjunction U.ι
  let φ : N ⟶ F := adj.unit.app N ≫ (Scheme.Modules.pushforward U.ι).map θ ≫
    inv (adj.unit.app F)
  have hφ : φ ≫ adj.unit.app F = adj.homEquiv N _ θ := by
    simp [φ, adj.homEquiv_unit]
  have hθφ : θ = (Scheme.Modules.restrictFunctor U.ι).map φ := by
    apply (adj.homEquiv N _).injective
    rw [← hφ, adj.homEquiv_unit]
    exact (Adjunction.unit_naturality _ φ).symm
  refine ⟨φ, fun n => ?_⟩
  rw [← hθ n, hθφ, restrictSections_restrictFunctor_map]

end Stacks.AlgebraicGeometry
