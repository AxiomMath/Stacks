module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexChartInputs
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexDiagonalEndomorphisms

/-!
# Rigidity of the diagonal condition of a relative dualizing complex

Let `f : X ⟶ S` be a morphism of schemes, `W ⊆ X ×_S X` an open through which the diagonal
factors as a closed immersion `Δ : X ⟶ W`, and `K` an object of `D(𝒪_X)`. Suppose that
`Δ_*𝒪_X ≅ R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)` as objects, and that `ξ` freely generates
`Hom(Δ_*𝒪_X, L pr₁^*K|_W)` over `End(Δ_*𝒪_X)`. Then the map defined by `ξ` (Stacks 0E2T) is an
isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isIso_diagonalAction_of_iso_of_generator`: the map
  defined by a free generator is an isomorphism.

## References

* [Stacks Project, Definition 48.28.1 (Tag 0E2T)](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Lemma 48.28.6 (Tag 0E2X)](https://stacks.math.columbia.edu/tag/0E2X)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite StrictlyPerfect
  AlgebraicGeometry

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)

/-- **The left inverse of the map that `ξ` defines is `Γ(X, 𝒪_X)`-linear.** -/
theorem diagonalActionRetraction_smul {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (a : Γ(X, ⊤))
    (ψ : D.diagonalObject ⟶
      ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).obj (op D.diagonalObject)).obj
        (D.derivedPullbackProj K)) :
    letI := D.proj.linearStructureSheafModules
    D.diagonalActionRetraction (a • ψ) = a • D.diagonalActionRetraction ψ := by
  let := D.proj.linearStructureSheafModules
  rw [D.smul_eq_smul_id_comp a ψ, D.smul_eq_smul_id_comp a (D.diagonalActionRetraction ψ)]
  unfold diagonalActionRetraction
  have e₂ := congrArg (· ≫ Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf
    D.diagonalObject D.diagonalObject (D.derivedPullbackProj K) ψ)
    (D.derivedMulSection_comp_derivedTensor_map_smul_app a)
  simp only [Category.assoc] at e₂
  rw [D.derivedSheafHomTensorEquiv_comp_diagonalObject (K := K) (a • 𝟙 _) ψ]
  convert e₂ using 2

/-- **Rigidity of the diagonal condition.** If `Δ_*𝒪_X ≅ R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`
and `ξ` freely generates `Hom(Δ_*𝒪_X, L pr₁^*K|_W)` over `End(Δ_*𝒪_X)` by precomposition, then
`ξ` defines an isomorphism. -/
theorem isIso_diagonalAction_of_iso_of_generator
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (τ : D.diagonalObject ≅
      ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).obj (op D.diagonalObject)).obj
        (D.derivedPullbackProj K))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hgen : ∀ ζ : D.diagonalObject ⟶ D.derivedPullbackProj K,
      ∃ x : D.diagonalObject ⟶ D.diagonalObject, ζ = x ≫ ξ)
    (huniq : ∀ x y : D.diagonalObject ⟶ D.diagonalObject, x ≫ ξ = y ≫ ξ → x = y) :
    IsIso (D.diagonalAction K ξ) := by
  let := D.proj.linearStructureSheafModules
  exact isIso_of_leftInverse_of_generator τ (D.diagonalAction K) D.diagonalActionRetraction
    D.diagonalActionRetraction_diagonalAction D.diagonalActionRetraction_smul
    D.exists_eq_smul_id_diagonalObject ξ hgen huniq

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
