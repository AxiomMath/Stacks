module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheafCohomologyVanishing

/-!
# No higher cohomology of a quasi-coherent module over an affine étale chart, module-valued

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`. The
positive-degree right derived functors of `CategoryTheory.SheafOfModules.evaluation` vanish on a
quasi-coherent `𝒪_F`-module over every affine étale chart of `F`, at module universe `u`.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isQuasicoherentOnSite`: a
  quasi-coherent `𝒪_F`-module has no positive-degree derived sections over an affine étale
  chart.
* `AlgebraicGeometry.Space.chartwise_isZero_rightDerived_evaluation`: the same, quantified over
  all affine étale charts, quasi-coherent modules and positive degrees.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 08F6](https://stacks.math.columbia.edu/tag/08F6)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

attribute [local instance] enoughInjectives_sheaf_smallEtaleRingedSite
  hasExt_sheaf_smallEtaleRingedSite

attribute [local instance] enoughInjectives_modules

attribute [local instance] hasExt_modules

open Stacks.Cohomology.ModuleDirectImageOnACover in
/-- A quasi-coherent `𝒪_F`-module has no positive-degree derived sections over an affine étale
chart of an algebraic space. -/
theorem isZero_rightDerived_evaluation_of_isQuasicoherentOnSite
    (U : SmallEtale B S hS F) (hU : IsAffineChart B S hS F U)
    (M : Modules.{u, u} B S hS F hF) (hM : M.IsQuasicoherentOnSite) (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O)
      (op U)).rightDerived p).obj M) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  exact isZero_rightDerived_evaluation_of_isZero_H'_chgUniv
    (smallEtaleRingedSite B S hS F hF).J
    (ringSheaf (smallEtaleRingedSite B S hS F hF).O) U q M
    (isZero_sheafH'_of_isQuasicoherentOnSite M hM U hU (q + 1) (Nat.succ_pos q))

/-- A quasi-coherent `𝒪_F`-module has no positive-degree derived sections over any affine étale
chart of an algebraic space, at module universe `u`. -/
theorem chartwise_isZero_rightDerived_evaluation :
    ∀ U : SmallEtale B S hS F, IsAffineChart B S hS F U →
      ∀ M : Modules.{u, u} B S hS F hF, M.IsQuasicoherentOnSite → ∀ p : ℕ, 0 < p →
        IsZero (((SheafOfModules.evaluation
          (ringSheaf (smallEtaleRingedSite B S hS F hF).O)
          (op U)).rightDerived p).obj M) :=
  fun U hU M hM p hp ↦
    isZero_rightDerived_evaluation_of_isQuasicoherentOnSite B S hS F hF U hU M hM p hp

end AlgebraicGeometry.Space

end
