module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LocallyFreeProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.IntegralTransform

/-!
# The projection formula for `Rf_!`

For every commutative ring `Λ`, the projection formula `Rf_!(K ⊗ f⁻¹ N) ≅ Rf_! K ⊗ N` holds on
`D⁺_tors(X_étale, Λ)` for `N` étale-locally free of finite rank, in the standard model
`HasDerivedCategory.standard` of the derived category.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekProjectionFormula`: the proposition
  `Stacks.EtaleCohomology.DerivedLowerShriekProjectionFormula` holds for every commutative ring.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.EtaleCohomology

/-- The projection formula `Rf_!(K ⊗ f⁻¹ N) ≅ Rf_! K ⊗ N` on `D⁺_tors(X_étale, Λ)`, for `N`
étale-locally free of finite rank, holds for every commutative ring `Λ`. -/
theorem derivedLowerShriekProjectionFormula (Λ : Type) [CommRing Λ] :
    DerivedLowerShriekProjectionFormula.{u} Λ :=
  fun _ _ f j N hlf _ _ => ⟨Functor.isoWhiskerLeft _ (derivedLowerShriekProjectionIso f j N hlf)⟩

end Stacks.EtaleCohomology
