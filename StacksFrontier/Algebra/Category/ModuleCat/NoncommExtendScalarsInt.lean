module

public import StacksFrontier.Algebra.Category.ModuleCat.NoncommExtendScalars
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# Extension of scalars from `ℤ` to a noncommutative ring

For a ring `B`, not necessarily commutative, the relative tensor product `B ⊗[ℤ] M` of
`Stacks.NoncommChangeOfRings.BaseChange` along `ℤ →+* B` has no relations to divide out: the
relation `(b * a) ⊗ m = b ⊗ (a • m)` already holds in the tensor product over `ℤ`. Hence base
change along `ℤ →+* B` of an injective map with torsion-free cokernel is injective, as for the
ordinary tensor product over the Dedekind domain `ℤ`.

## Main results

* `Stacks.NoncommChangeOfRings.tensorRel_intCast_eq_bot`: there are no relations.
* `Stacks.NoncommChangeOfRings.map_intCast_injective`: base change along `ℤ →+* B` keeps an
  injective map with torsion-free cokernel injective.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe v u₂

namespace Stacks.NoncommChangeOfRings

variable {B : Type u₂} [Ring B]

/-- **Base change from `ℤ` has no relations.** -/
lemma tensorRel_intCast_eq_bot (M : Type v) [AddCommGroup M] [inst : Module ℤ M] :
    tensorRel (Int.castRingHom B) M = ⊥ := by
  obtain rfl : inst = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  rw [tensorRel, Submodule.span_eq_bot]
  rintro x ⟨b, a, m, rfl⟩
  rw [sub_eq_zero, eq_intCast, ← (Int.cast_commute a b).eq, ← zsmul_eq_mul,
    TensorProduct.smul_tmul]

/-- The quotient map from `B ⊗[ℤ] M` onto the base change of `M` along `ℤ →+* B` is injective. -/
lemma mk_intCast_injective (M : Type v) [AddCommGroup M] [Module ℤ M] :
    Function.Injective (mk (Int.castRingHom B) M) := by
  intro x y h
  rw [← sub_eq_zero, ← map_sub] at h
  rw [← sub_eq_zero]
  have hx := (Submodule.Quotient.mk_eq_zero _).1 h
  rwa [tensorRel_intCast_eq_bot, Submodule.mem_bot] at hx

/-- **Base change along `ℤ →+* B` of an injective map with torsion-free cokernel is
injective.** -/
lemma map_intCast_injective {M N P : Type v} [AddCommGroup M] [instM : Module ℤ M]
    [AddCommGroup N] [instN : Module ℤ N] [AddCommGroup P] [instP : Module ℤ P]
    [Module.IsTorsionFree ℤ P] (ψ : M →ₗ[ℤ] N) (χ : N →ₗ[ℤ] P) (hψ : Function.Injective ψ)
    (h : Function.Exact ψ χ) :
    Function.Injective (map (Int.castRingHom B) ψ) := by
  obtain rfl : instM = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  obtain rfl : instN = AddCommGroup.toIntModule N := Subsingleton.elim _ _
  obtain rfl : instP = AddCommGroup.toIntModule P := Subsingleton.elim _ _
  have hl := ModuleSheafCohomology.lTensor_injective_of_exact_of_isTorsionFree ψ χ hψ h B
  have hc : ∀ y, map (Int.castRingHom B) ψ (mk (Int.castRingHom B) M y) =
      mk (Int.castRingHom B) N (ψ.lTensor B y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul b m => rfl
    | add y y' hy hy' => simp only [map_add, hy, hy']
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := mk_surjective (Int.castRingHom B) M x
  rw [hc, ← map_zero (mk (Int.castRingHom B) N)] at hx
  have hy := hl ((mk_intCast_injective N hx).trans (map_zero _).symm)
  rw [hy, map_zero]

end Stacks.NoncommChangeOfRings

end
