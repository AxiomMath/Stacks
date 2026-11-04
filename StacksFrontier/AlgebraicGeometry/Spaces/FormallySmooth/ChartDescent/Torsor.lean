module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Tactic.LinearCombination
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The torsor of lifts into a square-zero thickening

Let `q : R →ₐ[A'] Q` be a surjection of `A'`-algebras whose kernel `J` has square zero and let
`c : P →ₐ[A'] Q` be a map of `A'`-algebras. The lifts of `c` along `q` form a torsor under the
`A'`-derivations of `P` with values in `J`. This file records that torsor in a form keyed only to
a *reference lift* `ref` of `c`: the group is the `R`-submodule
`AlgebraicGeometry.Space.ChartDescent.sqDer J ref` of `P →ₗ[A'] R`, cut out by the condition that
the map takes values in `J` and satisfies the Leibniz rule along `ref`. Since `J ^ 2 = 0`, the
Leibniz rule along `ref` is the Leibniz rule along any other lift of `c`.

## Main definitions

* `AlgebraicGeometry.Space.ChartDescent.sqDer`: the derivations along a reference lift.
* `AlgebraicGeometry.Space.ChartDescent.Lifts`: the lifts of `c` along `q`.
* `AlgebraicGeometry.Space.ChartDescent.liftsAddTorsor`: the torsor structure.

## Main results

* `AlgebraicGeometry.Space.ChartDescent.vadd_apply`, `vsub_apply`: the action is addition of
  values and the difference is subtraction of values.
-/

@[expose] public section

namespace AlgebraicGeometry.Space.ChartDescent

variable {A' : Type*} [CommRing A'] {P : Type*} [CommRing P] [Algebra A' P]
  {R : Type*} [CommRing R] [Algebra A' R] {Q : Type*} [CommRing Q] [Algebra A' Q]

/-- The `A'`-linear maps `P → R` with values in `J` satisfying the Leibniz rule along `ref`. -/
def sqDer (J : Ideal R) (ref : P →ₐ[A'] R) : Submodule R (P →ₗ[A'] R) where
  carrier := {D | (∀ x, D x ∈ J) ∧ ∀ x y, D (x * y) = ref x * D y + ref y * D x}
  add_mem' := by
    rintro D E ⟨hD, hD'⟩ ⟨hE, hE'⟩
    refine ⟨fun x ↦ J.add_mem (hD x) (hE x), fun x y ↦ ?_⟩
    simp only [LinearMap.add_apply, hD', hE']
    ring
  zero_mem' := ⟨fun _ ↦ J.zero_mem, fun _ _ ↦ by simp⟩
  smul_mem' := by
    rintro r D ⟨hD, hD'⟩
    refine ⟨fun x ↦ J.mul_mem_left r (hD x), fun x y ↦ ?_⟩
    simp only [LinearMap.smul_apply, smul_eq_mul, hD']
    ring

variable {J : Ideal R} {ref : P →ₐ[A'] R}

/-- An element of `sqDer J ref` takes values in `J`. -/
theorem sqDer_mem (D : sqDer J ref) (x : P) : (D : P →ₗ[A'] R) x ∈ J := D.2.1 x

/-- An element `D` of `sqDer J ref` satisfies `D (x * y) = ref x * D y + ref y * D x`. -/
theorem sqDer_leibniz (D : sqDer J ref) (x y : P) :
    (D : P →ₗ[A'] R) (x * y) =
      ref x * (D : P →ₗ[A'] R) y + ref y * (D : P →ₗ[A'] R) x := D.2.2 x y

/-- An element of `sqDer J ref` vanishes at `1`. -/
theorem sqDer_one (D : sqDer J ref) : (D : P →ₗ[A'] R) 1 = 0 := by
  have h := sqDer_leibniz D 1 1
  simp only [mul_one, map_one, one_mul] at h
  linear_combination -h

/-- The lifts of `c` along `q`. -/
abbrev Lifts (q : R →ₐ[A'] Q) (c : P →ₐ[A'] Q) : Type _ := {ℓ : P →ₐ[A'] R // q.comp ℓ = c}

namespace Lifts

variable {q : R →ₐ[A'] Q} {c : P →ₐ[A'] Q}

/-- Two lifts are equal if their underlying maps agree at every point. -/
@[ext] theorem ext {ℓ₁ ℓ₂ : Lifts q c} (h : ∀ x, ℓ₁.1 x = ℓ₂.1 x) : ℓ₁ = ℓ₂ :=
  Subtype.ext (AlgHom.ext h)

/-- A lift `ℓ` of `c` satisfies `q (ℓ x) = c x`. -/
theorem reduce_apply (ℓ : Lifts q c) (x : P) : q (ℓ.1 x) = c x :=
  congrArg (fun f : P →ₐ[A'] Q ↦ f x) ℓ.2

/-- The difference of two lifts of `c` lies in the kernel of `q`. -/
theorem sub_reduce (ℓ₁ ℓ₂ : Lifts q c) (x : P) : q (ℓ₁.1 x - ℓ₂.1 x) = 0 := by
  rw [map_sub, reduce_apply, reduce_apply, sub_self]

end Lifts

section SquareZero

variable {q : R →ₐ[A'] Q} (hJ : ∀ r, r ∈ J ↔ q r = 0) (h2 : J ^ 2 = ⊥)
  {c : P →ₐ[A'] Q}

include h2 in
/-- If `J ^ 2 = ⊥`, the product of two elements of `J` is zero. -/
theorem mul_eq_zero_of_mem {a b : R} (ha : a ∈ J) (hb : b ∈ J) : a * b = 0 := by
  have : a * b ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
  rw [h2] at this
  simpa using this

include hJ h2 in
/-- Multiplying an element of `J` by two lifts of the same reduction gives the same result. -/
theorem lift_mul_eq (ℓ₁ ℓ₂ : Lifts q c) (x : P) {j : R} (hj : j ∈ J) :
    ℓ₁.1 x * j = ℓ₂.1 x * j := by
  have h := mul_eq_zero_of_mem h2 ((hJ _).2 (Lifts.sub_reduce ℓ₁ ℓ₂ x)) hj
  linear_combination h

/-- Adding a derivation to a lift. -/
def vaddHom (href : q.comp ref = c) (D : sqDer J ref) (ℓ : Lifts q c) : P →ₐ[A'] R where
  toFun x := ℓ.1 x + (D : P →ₗ[A'] R) x
  map_one' := by simp [sqDer_one]
  map_mul' x y := by
    have hy := lift_mul_eq hJ h2 ℓ ⟨ref, href⟩ x (sqDer_mem D y)
    have hx := lift_mul_eq hJ h2 ℓ ⟨ref, href⟩ y (sqDer_mem D x)
    have hz := mul_eq_zero_of_mem h2 (sqDer_mem D x) (sqDer_mem D y)
    simp only [map_mul, sqDer_leibniz]
    linear_combination -hy - hx - hz
  map_zero' := by simp
  map_add' x y := by simp only [map_add]; ring
  commutes' a := by
    have h1 := sqDer_one D
    have : (D : P →ₗ[A'] R) (algebraMap A' P a) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
    simp [this]

/-- Adding a derivation to a lift of `c` gives a lift of `c`. -/
theorem vaddHom_reduce (href : q.comp ref = c) (D : sqDer J ref) (ℓ : Lifts q c) :
    q.comp (vaddHom hJ h2 href D ℓ) = c := by
  ext x
  show q (ℓ.1 x + (D : P →ₗ[A'] R) x) = c x
  have hD : q ((D : P →ₗ[A'] R) x) = 0 := (hJ _).1 (sqDer_mem D x)
  rw [map_add, hD, add_zero]
  exact Lifts.reduce_apply ℓ x

/-- The difference of two lifts, as a derivation along `ref`. -/
def vsubDer (href : q.comp ref = c) (ℓ₁ ℓ₂ : Lifts q c) : sqDer J ref :=
  ⟨ℓ₁.1.toLinearMap - ℓ₂.1.toLinearMap, fun x ↦ (hJ _).2 (Lifts.sub_reduce ℓ₁ ℓ₂ x),
    fun x y ↦ by
      have h1 := lift_mul_eq hJ h2 ℓ₁ ⟨ref, href⟩ x ((hJ _).2 (Lifts.sub_reduce ℓ₁ ℓ₂ y))
      have h2' := lift_mul_eq hJ h2 ℓ₂ ⟨ref, href⟩ y ((hJ _).2 (Lifts.sub_reduce ℓ₁ ℓ₂ x))
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, map_mul]
      linear_combination h1 + h2'⟩

/-- **The lifts of `c` form a torsor under the derivations along a reference lift.** -/
@[instance_reducible, ega "IV 16.5.14", sga "3 III 0.1.8" "(a), special case"]
def liftsAddTorsor (href : q.comp ref = c) : AddTorsor (sqDer J ref) (Lifts q c) where
  vadd D ℓ := ⟨vaddHom hJ h2 href D ℓ, vaddHom_reduce hJ h2 href D ℓ⟩
  zero_vadd ℓ := Lifts.ext fun x ↦ by
    change ℓ.1 x + ((0 : sqDer J ref) : P →ₗ[A'] R) x = ℓ.1 x
    simp
  add_vadd D E ℓ := Lifts.ext fun x ↦ by
    change ℓ.1 x + ((D : P →ₗ[A'] R) x + (E : P →ₗ[A'] R) x) =
      ℓ.1 x + (E : P →ₗ[A'] R) x + (D : P →ₗ[A'] R) x
    ring
  vsub ℓ₁ ℓ₂ := vsubDer hJ h2 href ℓ₁ ℓ₂
  nonempty := ⟨⟨ref, href⟩⟩
  vsub_vadd' ℓ₁ ℓ₂ := Lifts.ext fun x ↦ by
    change ℓ₂.1 x + (ℓ₁.1 x - ℓ₂.1 x) = ℓ₁.1 x
    ring
  vadd_vsub' D ℓ := Subtype.ext (LinearMap.ext fun x ↦ by
    change (ℓ.1 x + (D : P →ₗ[A'] R) x) - ℓ.1 x = (D : P →ₗ[A'] R) x
    ring)

/-- The action of a derivation `D` on a lift `ℓ` is `x ↦ ℓ x + D x`. -/
theorem vadd_apply (href : q.comp ref = c) (D : sqDer J ref) (ℓ : Lifts q c) (x : P) :
    letI := liftsAddTorsor hJ h2 href
    (D +ᵥ ℓ).1 x = ℓ.1 x + (D : P →ₗ[A'] R) x := rfl

/-- The difference of two lifts `ℓ₁` and `ℓ₂` is the derivation `x ↦ ℓ₁ x - ℓ₂ x`. -/
theorem vsub_apply (href : q.comp ref = c) (ℓ₁ ℓ₂ : Lifts q c) (x : P) :
    letI := liftsAddTorsor hJ h2 href
    ((ℓ₁ -ᵥ ℓ₂ : sqDer J ref) : P →ₗ[A'] R) x = ℓ₁.1 x - ℓ₂.1 x := rfl

end SquareZero

end AlgebraicGeometry.Space.ChartDescent

end
