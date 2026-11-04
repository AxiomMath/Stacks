module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.QuasiFinite

/-!
# Comparing the adic completions of two cofinal ideals

Let `P` be an algebra over a commutative ring `A` and let `K₁`, `K₂` be ideals of `P` with
`K₁ ^ a ≤ K₂`. Then `K₁ ^ (a * n) ≤ K₂ ^ n` for every `n`, so the reductions
`P̂_{K₁} → P / K₂ ^ n` form a compatible family and assemble into an `A`-algebra map
`P̂_{K₁} → P̂_{K₂}`. If in addition `K₂ ^ b ≤ K₁`, the two maps so obtained are mutually
inverse: the adic completion depends only on the topology defined by the ideal, not on the
ideal defining it.

## Main definitions

* `AdicCompletion.compareComponent` — the level-`n` reduction of `P̂_{K₁}` to `P / K₂ ^ n`.
* `AdicCompletion.compareAlgHom` — the comparison map `P̂_{K₁} → P̂_{K₂}` attached to an
  inclusion `K₁ ^ a ≤ K₂`.
* `AdicCompletion.compareAlgEquiv` — the resulting isomorphism for a mutually cofinal pair.

## Main results

* `AdicCompletion.evalₐ_compareAlgHom` — the defining identity on level-`n` reductions.
* `AdicCompletion.compareAlgHom_of`, `AdicCompletion.compareAlgEquiv_of` — the comparison
  maps are compatible with the canonical maps from `P`.
-/

@[expose] public noncomputable section

namespace AdicCompletion

universe u v

variable (A : Type u) [CommRing A] {P : Type v} [CommRing P] [Algebra A P]

section

/-- From `K₁ ^ a ≤ K₂` one gets `K₁ ^ (a * n) ≤ K₂ ^ n`. -/
public theorem pow_mul_le_pow_of_pow_le {K₁ K₂ : Ideal P} {a : ℕ} (ha : K₁ ^ a ≤ K₂) (n : ℕ) :
    K₁ ^ (a * n) ≤ K₂ ^ n :=
  (pow_mul K₁ a n).le.trans (Ideal.pow_right_mono ha n)

end

section

variable {K₁ K₂ : Ideal P} {a : ℕ}

/-- The level-`n` component of the comparison map: reduce an element of the `K₁`-adic
completion modulo `K₁ ^ (a * n)` and push it into `P / K₂ ^ n`. -/
public def compareComponent (ha : K₁ ^ a ≤ K₂) (n : ℕ) :
    AdicCompletion K₁ P →ₐ[A] P ⧸ K₂ ^ n :=
  (Ideal.Quotient.factorₐ A (pow_mul_le_pow_of_pow_le ha n)).comp
    ((evalₐ K₁ (a * n)).restrictScalars A)

/-- The level-`n` component of the comparison map, evaluated on an element. -/
public theorem compareComponent_apply (ha : K₁ ^ a ≤ K₂) (n : ℕ) (x : AdicCompletion K₁ P) :
    compareComponent A ha n x =
      Ideal.Quotient.factor (pow_mul_le_pow_of_pow_le ha n) (evalₐ K₁ (a * n) x) :=
  rfl

/-- The level-`n` components of the comparison map are compatible with the reductions of the
`K₂`-adic tower. -/
public theorem factorₐ_comp_compareComponent (ha : K₁ ^ a ≤ K₂) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp
        (compareComponent A ha n) = compareComponent A ha m := by
  ext x
  simp only [AlgHom.comp_apply, compareComponent_apply, Ideal.Quotient.factorₐ_apply,
    Ideal.Quotient.factor_comp_apply, ← factor_evalₐ K₁ (Nat.mul_le_mul_left a hle) x]

/-- The comparison map between the `K₁`-adic and the `K₂`-adic completion of `P`, attached to
an inclusion `K₁ ^ a ≤ K₂`. -/
public def compareAlgHom (ha : K₁ ^ a ≤ K₂) :
    AdicCompletion K₁ P →ₐ[A] AdicCompletion K₂ P :=
  liftAlgHom K₂ (compareComponent A ha) (factorₐ_comp_compareComponent A ha)

/-- The reduction modulo `K₂ ^ n` of the comparison map is induced by the reduction modulo
`K₁ ^ (a * n)`. -/
@[simp]
public theorem evalₐ_compareAlgHom (ha : K₁ ^ a ≤ K₂) (n : ℕ) (x : AdicCompletion K₁ P) :
    evalₐ K₂ n (compareAlgHom A ha x) =
      Ideal.Quotient.factor (pow_mul_le_pow_of_pow_le ha n) (evalₐ K₁ (a * n) x) :=
  evalₐ_liftAlgHom _ _ _ _ _

/-- The comparison map commutes with the canonical maps from `P`. -/
@[simp]
public theorem compareAlgHom_of (ha : K₁ ^ a ≤ K₂) (x : P) :
    compareAlgHom A ha (of K₁ P x) = of K₂ P x :=
  ext_evalₐ fun _ ↦ by simp

end

section

variable {K₁ K₂ : Ideal P} {a b : ℕ}

/-- For a mutually cofinal pair of ideals, with positive exponents, the two comparison maps
compose to the identity. -/
public theorem compareAlgHom_compareAlgHom (ha : K₁ ^ a ≤ K₂) (hb : K₂ ^ b ≤ K₁)
    (hapos : 0 < a) (hbpos : 0 < b) (x : AdicCompletion K₁ P) :
    compareAlgHom A hb (compareAlgHom A ha x) = x := by
  refine ext_evalₐ fun n ↦ ?_
  have hn : n ≤ a * (b * n) :=
    (Nat.le_mul_of_pos_left n hbpos).trans (Nat.le_mul_of_pos_left (b * n) hapos)
  simp only [evalₐ_compareAlgHom, Ideal.Quotient.factor_comp_apply, factor_evalₐ K₁ hn x]

/-- For a mutually cofinal pair of ideals the two adic completions of `P` agree. -/
public def compareAlgEquiv (ha : K₁ ^ a ≤ K₂) (hb : K₂ ^ b ≤ K₁) :
    AdicCompletion K₁ P ≃ₐ[A] AdicCompletion K₂ P :=
  have ha' : K₁ ^ (a + 1) ≤ K₂ := (Ideal.pow_le_pow_right (Nat.le_succ a)).trans ha
  have hb' : K₂ ^ (b + 1) ≤ K₁ := (Ideal.pow_le_pow_right (Nat.le_succ b)).trans hb
  AlgEquiv.ofAlgHom (compareAlgHom A ha') (compareAlgHom A hb')
    (AlgHom.ext fun x ↦ compareAlgHom_compareAlgHom A hb' ha' b.succ_pos a.succ_pos x)
    (AlgHom.ext fun x ↦ compareAlgHom_compareAlgHom A ha' hb' a.succ_pos b.succ_pos x)

/-- The level-`n` components of the comparison isomorphism. -/
public theorem evalₐ_compareAlgEquiv (ha : K₁ ^ a ≤ K₂) (hb : K₂ ^ b ≤ K₁) (n : ℕ)
    (x : AdicCompletion K₁ P) :
    evalₐ K₂ n (compareAlgEquiv A ha hb x) =
      Ideal.Quotient.factor (pow_mul_le_pow_of_pow_le
        ((Ideal.pow_le_pow_right (Nat.le_succ a)).trans ha) n) (evalₐ K₁ ((a + 1) * n) x) :=
  evalₐ_compareAlgHom A _ n x

/-- The comparison isomorphism commutes with the canonical maps from `P`. -/
@[simp]
public theorem compareAlgEquiv_of (ha : K₁ ^ a ≤ K₂) (hb : K₂ ^ b ≤ K₁) (x : P) :
    compareAlgEquiv A ha hb (of K₁ P x) = of K₂ P x :=
  compareAlgHom_of A _ x

/-- The comparison isomorphism commutes with the algebra maps from `P`. -/
@[simp]
public theorem compareAlgEquiv_algebraMap (ha : K₁ ^ a ≤ K₂) (hb : K₂ ^ b ≤ K₁) (x : P) :
    compareAlgEquiv A ha hb (algebraMap P (AdicCompletion K₁ P) x) =
      algebraMap P (AdicCompletion K₂ P) x :=
  compareAlgHom_of A _ x

end

end AdicCompletion

end
