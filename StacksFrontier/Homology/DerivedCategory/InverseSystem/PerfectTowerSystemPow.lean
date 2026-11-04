module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTowerPow
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTowerSystem

/-!
# Traces of powers on the rationalised limit of a system isomorphic to a perfect tower

Let `S` be an inverse system of `ℤ_ℓ`-modules with an endomorphism `σ`, isomorphic to the
cohomology system `n ↦ Hⁱ(Kₙ)` of a tower of perfect complexes with `n ↦ Hⁱ(πₙ)`.  The
endomorphism induced by `σ` on `ℚ_ℓ ⊗ lim S` is conjugate to `πⁱ_∞ ⊗ ℚ_ℓ`, so the traces of all
its powers are those of the powers of `πⁱ_∞`, and Tag 03V4 (3) for the tower `(Kₙ, πₙ ^ m)` gives

`∑ᵢ (-1)ⁱ Tr((σ ⊗ ℚ_ℓ) ^ m | ℚ_ℓ ⊗ lim S i) = t_∞(πᵐ)`.

## Main results

* `Stacks.InverseSystem.baseChange_limMap_eq_conj`: the conjugacy.
* `Stacks.InverseSystem.alternating_trace_pow_rational_limit_of_iso`: the trace identity for the
  powers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe v

namespace Stacks.InverseSystem

attribute [local instance] HasDerivedCategory.standard

variable {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (i : ℤ)
  {S : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]} (e : S ≅ levelCohomologySystem T i) (σ : S ⟶ S)
  (hσ : σ ≫ e.hom = e.hom ≫ levelCohomologyEndoSystem T i)

include hσ in
/-- The endomorphism of `ℚ_ℓ ⊗ lim S` induced by `σ` is conjugate to `πⁱ_∞ ⊗ ℚ_ℓ`. -/
public theorem baseChange_limMap_eq_conj :
    LinearMap.baseChange ℚ_[ℓ] (limMap σ).hom =
      ((LinearEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _
        (limitLinearEquivLimitCohomology T i e)).symm).conj
        (LinearMap.baseChange ℚ_[ℓ] (limitCohomologyEndo T i)) := by
  let E := limitLinearEquivLimitCohomology T i e
  have hconj : (limMap σ).hom = E.symm.toLinearMap ∘ₗ limitCohomologyEndo T i ∘ₗ
      E.toLinearMap := by
    ext x
    apply E.injective
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply]
    exact congrArg (fun g => g x)
      (congrArg ModuleCat.Hom.hom (limMap_comp_limitIsoLimitCohomology_hom T i e σ hσ))
  rw [hconj, LinearEquiv.conj_apply]
  ext x
  simp [LinearEquiv.baseChange, E]

/-- Conjugation by a linear equivalence commutes with powers. -/
public theorem _root_.LinearEquiv.conj_pow {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (g : M ≃ₗ[R] N) (φ : Module.End R M) (m : ℕ) :
    g.conj φ ^ m = g.conj (φ ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Module.End.one_eq_id, Module.End.one_eq_id,
      LinearEquiv.conj_id]
  | succ m ih => rw [pow_succ, ih, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearEquiv.conj_comp]

include hσ in
/-- The traces of the powers of `σ ⊗ ℚ_ℓ` are those of the powers of `πⁱ_∞ ⊗ ℚ_ℓ`. -/
public theorem trace_baseChange_limMap_pow (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (limit S : ModuleCat.{v} ℤ_[ℓ]))
        (LinearMap.baseChange ℚ_[ℓ] (limMap σ).hom ^ m) =
      LinearMap.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] limitCohomology T i)
        (LinearMap.baseChange ℚ_[ℓ] (limitCohomologyEndo T i) ^ m) := by
  rw [baseChange_limMap_eq_conj T i e σ hσ, LinearEquiv.conj_pow, LinearMap.trace_conj']

/-- **Tag 03V4 (3) for the powers, on `lim S`.**  If, in every degree, `S i` with `σ i` is
isomorphic to `n ↦ Hⁱ(Kₙ)` with `n ↦ Hⁱ(πₙ)`, then
`∑ᵢ (-1)ⁱ Tr((σ i ⊗ ℚ_ℓ) ^ m | ℚ_ℓ ⊗ lim S i) = t_∞(πᵐ)`. -/
public theorem alternating_trace_pow_rational_limit_of_iso
    {S : ℤ → ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]} (σ : ∀ i, S i ⟶ S i)
    (e : ∀ i, S i ≅ levelCohomologySystem T i)
    (hσ : ∀ i, σ i ≫ (e i).hom = (e i).hom ≫ levelCohomologyEndoSystem T i) (m : ℕ) :
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (limit (S i) : ModuleCat.{v} ℤ_[ℓ]))
          (LinearMap.baseChange ℚ_[ℓ] (limMap (σ i)).hom ^ m) =
      (padicTrace (T.pow m) : ℚ_[ℓ]) := by
  rw [← alternating_trace_pow_eq_padicTrace T m]
  exact finsum_congr fun i => by rw [trace_baseChange_limMap_pow T i (e i) (σ i) (hσ i) m]

end Stacks.InverseSystem

end
