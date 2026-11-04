module

public import StacksFrontier.Algebra.Module.Injective.GroupAlgebraSelfInjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Hom_{A[H]}(N^∨, A[H]) ≅ N` for a representation of a finite group

Let `A` be a commutative ring, `H` a finite group and `N` an `A`-module with an action
`ρ : H →* End_A(N)`. The dual `N^∨ = Hom_A(N, A)` is a module over the group ring `A[H]` through
the contragredient action `h · φ = φ ∘ ρ(h⁻¹)`. For `y ∈ N` the map

`ψ_y : N^∨ → A[H]`, `φ ↦ ∑_g φ(g · y) g`

is `A[H]`-linear, and `y ↦ ψ_y` is a bijection `N ≅ Hom_{A[H]}(N^∨, A[H])` as soon as `N` is
reflexive over `A`: the coefficient of `1` in `ψ_y(φ)` is `φ(y)`, and an `A[H]`-linear map into
`A[H]` is determined by its coefficient of `1` (`MonoidAlgebra.coeff_one_single_inv_mul`).

## Main definitions

* `MonoidAlgebra.DualRep`: the `A[H]`-module `N^∨`.
* `MonoidAlgebra.dualRepHom`: `ψ_y`.

## Main results

* `MonoidAlgebra.bijective_dualRepHom`: `y ↦ ψ_y` is a bijection `N ≅ Hom_{A[H]}(N^∨, A[H])` when
  `N` is reflexive over `A`.
-/

@[expose] public noncomputable section

open Finset

universe u v w

namespace MonoidAlgebra

variable {A : Type u} [CommRing A] {H : Type v} [Group H] [Fintype H] {N : Type w}
  [AddCommGroup N] [Module A N] (ρ : H →* Module.End A N)

/-- The contragredient action `h · φ = φ ∘ ρ(h⁻¹)` on the dual. -/
@[sga "3 I 4.7.1.0" "partial", sga "5 I 5.1.9", sga "5 X 3.7"]
def dualRepAction : H →* Module.End A (Module.Dual A N) where
  toFun h := (ρ h⁻¹).dualMap
  map_one' := by
    ext φ y
    simp
  map_mul' g h := by
    ext φ y
    simp [mul_inv_rev]

omit [Fintype H] in
/-- The contragredient action is given by `(h · φ)(y) = φ(ρ(h⁻¹) y)`. -/
@[sga "5 X 3.7" "(x), special case"]
lemma dualRepAction_apply (h : H) (φ : Module.Dual A N) (y : N) :
    dualRepAction ρ h φ y = φ (ρ h⁻¹ y) :=
  rfl

/-- **The dual `N^∨` of a representation, as a module over the group ring.** -/
@[sga "5 I 5.1.9", sga "5 X 3.7" "partial"]
def DualRep (_ : H →* Module.End A N) : Type _ := Module.Dual A N

/-- `N^∨` is an additive commutative group, as `Hom_A(N, A)` is. -/
instance : AddCommGroup (DualRep ρ) := inferInstanceAs (AddCommGroup (Module.Dual A N))

/-- `N^∨` is an `A`-module, as `Hom_A(N, A)` is. -/
instance : Module A (DualRep ρ) := inferInstanceAs (Module A (Module.Dual A N))

/-- `N^∨` is a module over the ring of `A`-linear endomorphisms of `Hom_A(N, A)`. -/
instance : Module (Module.End A (Module.Dual A N)) (DualRep ρ) :=
  inferInstanceAs (Module (Module.End A (Module.Dual A N)) (Module.Dual A N))

/-- `N^∨` is an `A[H]`-module through the contragredient action `dualRepAction ρ`. -/
instance : Module (MonoidAlgebra A H) (DualRep ρ) :=
  Module.compHom (DualRep ρ)
    (MonoidAlgebra.lift A (Module.End A (Module.Dual A N)) H (dualRepAction ρ)).toRingHom

/-- The identification of `N^∨` with its underlying dual. -/
def DualRep.equiv : DualRep ρ ≃ₗ[A] Module.Dual A N := LinearEquiv.refl _ _

omit [Fintype H] in
/-- The basis element `a h` of `A[H]` acts on `N^∨` by `(a h · φ)(y) = a φ(ρ(h⁻¹) y)`. -/
lemma single_smul_dualRep (h : H) (a : A) (φ : DualRep ρ) (y : N) :
    DualRep.equiv ρ (single h a • φ) y = a * DualRep.equiv ρ φ (ρ h⁻¹ y) := by
  show (MonoidAlgebra.lift A (Module.End A (Module.Dual A N)) H (dualRepAction ρ)
    (single h a)) φ y = _
  rw [MonoidAlgebra.lift_single]
  rfl

/-- **`ψ_y : N^∨ → A[H]`, `φ ↦ ∑_g φ(g · y) g`**, an `A[H]`-linear map. -/
def dualRepHom (y : N) : DualRep ρ →ₗ[MonoidAlgebra A H] MonoidAlgebra A H where
  toFun φ := ∑ g : H, single g (DualRep.equiv ρ φ (ρ g y))
  map_add' φ φ' := by
    simp only [map_add, LinearMap.add_apply, single_add, sum_add_distrib]
  map_smul' r φ := by
    change ∑ g : H, single g (DualRep.equiv ρ (r • φ) (ρ g y)) =
      r * ∑ g : H, single g (DualRep.equiv ρ φ (ρ g y))
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add s t hs ht =>
      simp only [add_smul, map_add, LinearMap.add_apply, single_add, sum_add_distrib, hs, ht,
        add_mul]
    | single x a =>
      simp only [single_smul_dualRep, mul_sum, single_mul_single]
      rw [eq_comm]
      refine Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun g => ?_
      simp [← Module.End.mul_apply, ← map_mul]

/-- The coefficient of `h` in `ψ_y(φ)` is `φ(ρ(h) y)`. -/
lemma dualRepHom_coeff (y : N) (φ : DualRep ρ) (h : H) :
    (dualRepHom ρ y φ).coeff h = DualRep.equiv ρ φ (ρ h y) := by
  classical
  show (∑ g : H, single g (DualRep.equiv ρ φ (ρ g y))).coeff h = _
  simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply]

omit [Fintype H] in
/-- Scalar multiplication by `a ∈ A` on `N^∨` agrees with the action of `a · 1 ∈ A[H]`. -/
lemma smul_dualRep_eq_single_one_smul (a : A) (φ : DualRep ρ) :
    a • φ = single (1 : H) a • φ := by
  apply (DualRep.equiv ρ).injective
  ext y
  rw [single_smul_dualRep, inv_one, map_one, Module.End.one_apply]
  rfl

/-- **`y ↦ ψ_y` is a bijection `N ≅ Hom_{A[H]}(N^∨, A[H])`** for `N` reflexive over `A`. -/
theorem bijective_dualRepHom (heval : Function.Bijective (Module.Dual.eval A N)) :
    Function.Bijective (dualRepHom ρ) := by
  refine ⟨fun y y' hyy => heval.1 ?_, fun f => ?_⟩
  · ext φ
    have := congrArg (fun F : DualRep ρ →ₗ[MonoidAlgebra A H] MonoidAlgebra A H =>
      (F ((DualRep.equiv ρ).symm φ)).coeff 1) hyy
    simpa [dualRepHom_coeff] using this
  · let g : Module.Dual A (Module.Dual A N) :=
      { toFun := fun φ => (f ((DualRep.equiv ρ).symm φ)).coeff 1
        map_add' := fun φ φ' => by simp
        map_smul' := fun a φ => by
          show (f (a • (DualRep.equiv ρ).symm φ)).coeff 1 = a • (f _).coeff 1
          rw [smul_dualRep_eq_single_one_smul, map_smul, smul_eq_mul, coeff_single_mul_apply]
          simp }
    obtain ⟨y, hy⟩ := heval.2 g
    refine ⟨y, LinearMap.ext fun φ => MonoidAlgebra.ext (Finsupp.ext fun h => ?_)⟩
    rw [dualRepHom_coeff, ← coeff_one_single_inv_mul, ← smul_eq_mul, ← map_smul]
    have := congrArg (fun F => F (DualRep.equiv ρ (single h⁻¹ (1 : A) • φ))) hy
    change DualRep.equiv ρ (single h⁻¹ (1 : A) • φ) y = (f (single h⁻¹ (1 : A) • φ)).coeff 1
      at this
    rw [← this, single_smul_dualRep, one_mul, inv_inv]

end MonoidAlgebra

end
