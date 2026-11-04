module

public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.DualizingSheafOfComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologicalAmplenessCriterion
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCongr
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge

/-!
# Tensor powers of a module restricted to a scheme

Let `𝓛` be an invertible module on an algebraic space `X` and `p : V ⟶ X` a morphism from a
scheme `V` of the site. If the restriction `𝓛|_V` of `𝓛` to `V` is isomorphic to an invertible
`𝒪_V`-module `M`, then for every `n ≥ 1` the restriction of `𝓛^{⊗ n}` to `V` is isomorphic to
`M^{⊗ n}`.

## Main results

* `AlgebraicGeometry.C1764Prereq.nonempty_baseChangeModule_invertibleTensorPower_iso`: the
  restriction of `𝓛^{⊗ n}` to `V` is isomorphic to `M^{⊗ n}`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace C1764Prereq

open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)

variable {S : Scheme.{u}} {hS : B.Contains S}

/-- For an invertible module `𝓛` on an algebraic space `X`, a scheme `V` of the site over `X` and
an isomorphism of `𝓛|_V` with an invertible `𝒪_V`-module `M`, the restriction of `𝓛^{⊗ n}` to `V`
is isomorphic to `M^{⊗ n}` for every `n ≥ 1`. -/
theorem nonempty_baseChangeModule_invertibleTensorPower_iso {X : AlgebraicSpaces B S hS}
    (L : Space.Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B S hS X.1 X.2).O)).property L]
    (V : BigFppfOver B S hS) (p : yoneda.obj V ⟶ X.1)
    (M : ((BigFppfOver.toScheme B S hS).obj V).Modules)
    [hM : SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj V).presheaf
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf.2 M]
    (e : Space.baseChangeModule B S hS L V p ≅ M) (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (Space.baseChangeModule B S hS (Space.invertibleTensorPower B S hS X.1 X.2 L n) V p ≅
      tensorPower ((BigFppfOver.toScheme B S hS).obj V).presheaf
        ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf.2 M n) := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj V)
      (Space.baseChangeModule B S hS L V p) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e.symm
  have e₁ := Space.baseChangeModuleTensorPowerIso L V p n
  have e₂ := (Stacks.PowerFamilyBridge.tensorPowerModuleIso _
    (Space.baseChangeModule B S hS L V p) ((n + 1 : ℕ) : ℤ)).symm
  exact ⟨e₁ ≪≫ e₂ ≪≫ Stacks.SheafOfModules.TensorPower.tensorPowerCongr
    ((BigFppfOver.toScheme B S hS).obj V).presheaf
    ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf.2 e _⟩

end C1764Prereq

end AlgebraicGeometry
