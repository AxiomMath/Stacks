module

public import StacksFrontier.RingTheory.FormsTrace.Defs
public import StacksFrontier.RingTheory.DeRham.WedgeLeibniz
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.Connection

/-!
# The pull-back of absolute differential forms

Elementary properties of `Stacks.FormsTrace.formsMap`, the pull-back `Ω^p_A → Ω^p_B` of absolute
differential forms along a ring map `A → B`: it is multiplicative for the wedge product, it
commutes with the de Rham differential, and it is compatible with the identification of a form
of degree one with a Kähler differential.

## Main results

* `Stacks.FormsTrace.formsMap_wedgeMul`: `f^*(ω ∧ η) = f^*ω ∧ f^*η`.
* `Stacks.FormsTrace.formsMap_deRhamDifferential`: `f^*(dω) = d(f^*ω)`.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open KaehlerDifferential

universe u

namespace Stacks.FormsTrace

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The pull-back of forms carries a wedge of Kähler differentials to the wedge of their
images. -/
theorem formsMap_ιMulti (p : ℕ) (v : Fin p → Ω[A⁄ℤ]) :
    formsMap A B p (exteriorPower.ιMulti A p v) =
      exteriorPower.ιMulti B p fun i => KaehlerDifferential.map ℤ ℤ A B (v i) :=
  ExteriorAlgebra.powMapₛₗ_ιMulti p _ _ v

/-- The pull-back of forms is multiplicative: `f^*(ω ∧ η) = f^*ω ∧ f^*η`. -/
theorem formsMap_wedgeMul (q p : ℕ) (ω : ⋀[A]^q Ω[A⁄ℤ]) (η : ⋀[A]^p Ω[A⁄ℤ]) :
    formsMap A B (q + p) (exteriorPower.wedgeMul q p ω η) =
      exteriorPower.wedgeMul q p (formsMap A B q ω) (formsMap A B p η) := by
  refine Subtype.ext ?_
  simp only [ExteriorAlgebra.powMapₛₗ_coe, exteriorPower.wedgeMul_apply_coe, map_mul]

/-- **The pull-back of forms commutes with the de Rham differential**: `f^*(dω) = d(f^*ω)`. -/
theorem formsMap_deRhamDifferential (p : ℕ) (ω : ⋀[A]^p Ω[A⁄ℤ]) :
    formsMap A B (p + 1) (deRhamDifferential p ω) = deRhamDifferential p (formsMap A B p ω) := by
  have key : ∀ ω ∈ Submodule.span ℤ (Set.range fun a : Fin (p + 1) → A =>
      a 0 • exteriorPower.ιMulti A p fun i => D ℤ A (a i.succ)),
      formsMap A B (p + 1) (deRhamDifferential p ω) =
        deRhamDifferential p (formsMap A B p ω) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [deRhamDifferential_smul_ιMulti_D, formsMap_ιMulti, map_smulₛₗ, formsMap_ιMulti]
      have := deRhamDifferential_smul_ιMulti_D (A := ℤ) (B := B) p
        (fun i => algebraMap A B (a i))
      simp only [KaehlerDifferential.map_D] at this ⊢
      exact this.symm
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul n x _ hx => simp only [map_zsmul, hx]
  exact key ω (by
    rw [Crystalline.span_range_smul_ιMulti_eq_top (R := ℤ) (D ℤ A)
      (KaehlerDifferential.span_range_derivation ℤ A) p]
    trivial)

end Stacks.FormsTrace

end
