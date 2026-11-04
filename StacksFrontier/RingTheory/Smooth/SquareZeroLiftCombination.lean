module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Affine combinations of lifts across a square-zero ideal

Let `I` be an ideal of a commutative `R`-algebra `B` with `I ^ 2 = 0`, and let `C` be an
`R`-algebra. The `R`-algebra maps `C → B` which agree modulo `I` with a fixed one form an affine
space over the module of `I`-valued derivations; concretely, a linear combination
`∑ bᵢ ψᵢ` of such maps whose coefficients `bᵢ ∈ B` sum to `1` is again an `R`-algebra map,
congruent to each `ψᵢ` modulo `I`.

## Main definitions

* `Stacks.SquareZeroLift.affineCombination`: the `R`-algebra map `x ↦ ∑ bᵢ ψᵢ x`, and
  `Stacks.SquareZeroLift.affineCombinationRingHom`, the same for ring maps.

## Main results

* `Stacks.SquareZeroLift.affineCombination_apply` and
  `Stacks.SquareZeroLift.affineCombination_sub_mem`: its values, and its congruence to the base
  member of the family modulo `I`.
-/

@[expose] public section

open scoped BigOperators

namespace Stacks.SquareZeroLift

variable {R C B : Type*} [CommRing R] [CommRing C] [CommRing B] [Algebra R C] [Algebra R B]

section AffineCombination

variable (I : Ideal B) (hI : I ^ 2 = ⊥) {ι : Type*} (s : Finset ι) (ψ : ι → C →ₐ[R] B)
  (b : ι → B) (hb : ∑ i ∈ s, b i = 1) (i₀ : ι) (hagree : ∀ i ∈ s, ∀ x, ψ i x - ψ i₀ x ∈ I)

include I hI hb hagree in
/-- The multiplicativity of an affine combination of lifts. -/
theorem affineCombination_map_mul (x y : C) :
    ∑ i ∈ s, b i * ψ i (x * y) = (∑ i ∈ s, b i * ψ i x) * ∑ i ∈ s, b i * ψ i y := by
  have hsq : ∀ u ∈ I, ∀ v ∈ I, u * v = 0 := fun u hu v hv => by
    have : u * v ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hu hv
    simpa [hI] using this
  set D : C → B := fun z => ∑ i ∈ s, b i * (ψ i z - ψ i₀ z) with hD
  have hDmem : ∀ z, D z ∈ I := fun z =>
    I.sum_mem fun i hi => I.mul_mem_left _ (hagree i hi z)
  have hsplit : ∀ z, ∑ i ∈ s, b i * ψ i z = ψ i₀ z + D z := fun z => by
    simp only [hD, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hb, one_mul]
    ring
  have hterm : ∀ i ∈ s, ψ i x * ψ i y =
      ψ i₀ x * ψ i₀ y + ψ i₀ x * (ψ i y - ψ i₀ y) + (ψ i x - ψ i₀ x) * ψ i₀ y := by
    intro i hi
    have h0 := hsq _ (hagree i hi x) _ (hagree i hi y)
    linear_combination h0
  have hlhs : ∑ i ∈ s, b i * ψ i (x * y) =
      ψ i₀ x * ψ i₀ y + ψ i₀ x * D y + D x * ψ i₀ y := by
    calc ∑ i ∈ s, b i * ψ i (x * y) = ∑ i ∈ s, b i * (ψ i x * ψ i y) := by
          simp only [map_mul]
      _ = ∑ i ∈ s, (b i * (ψ i₀ x * ψ i₀ y) + ψ i₀ x * (b i * (ψ i y - ψ i₀ y)) +
            b i * (ψ i x - ψ i₀ x) * ψ i₀ y) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hterm i hi]; ring
      _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hb, one_mul,
            hD]
  rw [hlhs, hsplit x, hsplit y]
  have := hsq _ (hDmem x) _ (hDmem y)
  linear_combination -this

include hI in
/-- **An affine combination of lifts across a square-zero ideal is a lift.** For `R`-algebra maps
`ψᵢ : C → B` agreeing modulo an ideal `I` with `I ^ 2 = 0` and coefficients `bᵢ ∈ B` summing to
`1`, the map `x ↦ ∑ bᵢ ψᵢ x` is an `R`-algebra map. -/
noncomputable def affineCombination : C →ₐ[R] B where
  toFun x := ∑ i ∈ s, b i * ψ i x
  map_one' := by simp [hb]
  map_mul' x y := affineCombination_map_mul I hI s ψ b hb i₀ hagree x y
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  commutes' r := by simp [← Finset.sum_mul, hb]

/-- The value of `Stacks.SquareZeroLift.affineCombination` at `x` is `∑ bᵢ ψᵢ x`. -/
@[simp]
theorem affineCombination_apply (x : C) :
    affineCombination I hI s ψ b hb i₀ hagree x = ∑ i ∈ s, b i * ψ i x :=
  rfl

/-- An affine combination of lifts is congruent to the base member modulo `I`. -/
theorem affineCombination_sub_mem (x : C) :
    affineCombination I hI s ψ b hb i₀ hagree x - ψ i₀ x ∈ I := by
  have : affineCombination I hI s ψ b hb i₀ hagree x - ψ i₀ x =
      ∑ i ∈ s, b i * (ψ i x - ψ i₀ x) := by
    simp only [affineCombination_apply, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hb,
      one_mul]
  rw [this]
  exact I.sum_mem fun i hi => I.mul_mem_left _ (hagree i hi x)

/-- **An affine combination of ring maps across a square-zero ideal is a ring map**: the
`RingHom` form of `Stacks.SquareZeroLift.affineCombination`, for ring maps `C → B` agreeing modulo
`I`. -/
noncomputable def affineCombinationRingHom (φ : ι → C →+* B)
    (hφ : ∀ i ∈ s, ∀ x, φ i x - φ i₀ x ∈ I) :
    C →+* B :=
  (affineCombination (R := ℤ) I hI s (fun i => (φ i).toIntAlgHom) b hb i₀ hφ).toRingHom

/-- The value of `Stacks.SquareZeroLift.affineCombinationRingHom` at `x` is `∑ bᵢ φᵢ x`. -/
@[simp]
theorem affineCombinationRingHom_apply (φ : ι → C →+* B)
    (hφ : ∀ i ∈ s, ∀ x, φ i x - φ i₀ x ∈ I) (x : C) :
    affineCombinationRingHom I hI s b hb i₀ φ hφ x = ∑ i ∈ s, b i * φ i x :=
  rfl

/-- An affine combination of ring maps is congruent to the base member modulo `I`. -/
theorem affineCombinationRingHom_sub_mem (φ : ι → C →+* B)
    (hφ : ∀ i ∈ s, ∀ x, φ i x - φ i₀ x ∈ I) (x : C) :
    affineCombinationRingHom I hI s b hb i₀ φ hφ x - φ i₀ x ∈ I :=
  affineCombination_sub_mem (R := ℤ) I hI s (fun i => (φ i).toIntAlgHom) b hb i₀ hφ x

end AffineCombination


end Stacks.SquareZeroLift

end
