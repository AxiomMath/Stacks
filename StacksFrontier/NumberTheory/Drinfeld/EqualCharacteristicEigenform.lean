module

public import StacksFrontier.NumberTheory.Drinfeld.EqualCharacteristicObstruction
public import StacksFrontier.NumberTheory.Drinfeld.UnitEigenform
public import StacksFrontier.NumberTheory.Drinfeld.CurveFunctionField

/-!
# Theorem 03VT for `ℓ = p`: reduction to the existence of a cusp form

Stacks Theorem 03VT does not assume `ℓ ≠ p`. For `ℓ = p` the characteristic of the finite base
field `k`, its conclusion fails for every eigenform satisfying its hypothesis
(`Stacks.Drinfeld.not_isFrobeniusCompatible_of_eq_ringChar`). This file reduces the resulting
counterexample to one input: a curve `X` whose module `C(Ω)` of unramified cusp forms with
`q_v · U_v f = f` is nonzero. Given that, an eigenform in `C(Ω)` twisted by `D ↦ c^{deg D}`,
`c² = q⁻¹`, has central eigenvalues `u_v = 1` (`Stacks.Drinfeld.UnitEigenform`), hence
satisfies the hypothesis `u_v ∈ Z̄_p^*` of 03VT, while no continuous `ρ` is compatible with it.

## Main results

* `Stacks.Drinfeld.exists_eigenform_not_isFrobeniusCompatible_of_cuspFormsCentralChar_ne_bot`
  — for a smooth proper curve with `C(Ω) ≠ 0`, `Ω` an algebraic closure of `ℚ_p`, there is an
  eigenform with every `u_v` a unit of `Z̄_p` and no continuous `ρ : π₁(X) → GL₂(E)` compatible
  with its eigenvalues.

## Implementation notes

The existence of a curve with `C(Ω) ≠ 0`, i.e. of a nonzero unramified cusp form on `GL₂` over
some global function field, is not proved here; it is the hypothesis of the theorem below.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Adeles Stacks.Adeles.GlobalFunctionField

universe u

namespace Stacks.Drinfeld

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} [IsIntegral X] [ConnectedSpace X]
  (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f]

include f in
/-- **For `ℓ = p`, a nonzero cusp form gives an eigenform contradicting 03VT.** Let `X` be a
smooth proper curve over a finite field `k` of characteristic `p`, and `Ω` an algebraic closure
of `ℚ_p`. If `C(Ω) ≠ 0` for the function field of `X`, there is an eigenform `φ` with values in
`Ω` whose central eigenvalues `u_v` are units of the integral closure of `ℤ_p` in `Ω` (indeed
`u_v = 1`), and no continuous `ρ : π₁(X) → GL₂(E)`, `E` a finite extension of `ℚ_p` embedded in
`Ω`, has `t_v = Tr ρ(F_v)` and `u_v = q_v⁻¹ det ρ(F_v)`. -/
public theorem exists_eigenform_not_isFrobeniusCompatible_of_cuspFormsCentralChar_ne_bot
    (base : GeometricPoint X) {p : ℕ} [Fact p.Prime] (hp : p = ringChar k)
    {Ω : Type u} [Field Ω] [Algebra ℚ_[p] Ω] [IsAlgClosure ℚ_[p] Ω] [Algebra ℤ_[p] Ω]
    [IsScalarTower ℤ_[p] ℚ_[p] Ω] (hC : cuspFormsCentralChar X.functionField Ω ≠ ⊥) :
    ∃ (φ : GL (Fin 2) (AdeleRing X.functionField) → Ω) (t u : Place X.functionField → Ω),
      IsEigenform φ t u ∧
      (∀ v, ∃ w : (integralClosure ℤ_[p] Ω)ˣ, ((w : integralClosure ℤ_[p] Ω) : Ω) = u v) ∧
      ∀ (E : TopologicalFieldExtension ℚ_[p]) (j : E.carrier →ₐ[ℚ_[p]] Ω)
        (ρ : EtaleFundamentalGroup X base →* GL (Fin 2) E.carrier),
        Continuous (fun g => (ρ g : Matrix (Fin 2) (Fin 2) E.carrier)) →
          ¬ IsFrobeniusCompatible base ρ j.toRingHom t u := by
  obtain ⟨_, _, _, _⟩ := exists_functionField_of_isCurve f
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ_[p]
  have hunit : IsUnit (ringChar k : Ω) := by
    rw [← hp]
    refine IsUnit.mk0 _ ?_
    rw [← map_natCast (algebraMap ℚ_[p] Ω)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  obtain ⟨φ, t, hφ⟩ := exists_isEigenform_one_of_cuspFormsCentralChar_ne_bot k hunit hC
  refine ⟨φ, t, fun _ => 1, hφ, fun _ => ⟨1, rfl⟩, fun E j ρ hρ => ?_⟩
  exact not_isFrobeniusCompatible_of_eq_ringChar f base hp E j ρ hρ t _
    (nonempty_place k).some ⟨1, rfl⟩

end Stacks.Drinfeld

end
