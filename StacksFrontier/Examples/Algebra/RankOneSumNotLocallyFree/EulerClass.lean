module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Algebra.Exact.Basic
public import StacksFrontier.LinearAlgebra.ExteriorPower.ProdInvertible

/-!
# Multiplication by `1 + t` on sequences modulo two

For a sequence `c : ℕ → G` in an additive group, `shiftAdd c` is the sequence of coefficients of
`(1 + t) · ∑ c k t ^ k`, that is `shiftAdd c 0 = c 0` and `shiftAdd c (k + 1) = c (k + 1) + c k`.
This operation is injective, and over `ZMod 2` the sum of the coefficients of `shiftAdd b` vanishes
for every finitely supported `b`, which is the evaluation of `(1 + t) · B(t)` at `t = 1 = -1`.

Consequently, if `(1 + t) ^ n · A(t) = (1 + t) ^ (n + 1) · B(t)` with `B` a polynomial, then the
coefficients of `A` sum to zero modulo two. This is the cancellation step of the argument that a
module `Q` with `R ^ n × Q ≃ R ^ (n + 1) × P'` has vanishing mod-two Euler class
`∑ k, φ (⋀^k Q)`, for any invariant `φ` additive on products.

## Main definitions

* `Stacks.Examples.ModTwoInvariant`: a `ZMod 2`-valued function on `B`-modules, invariant under
  isomorphism and additive on short exact sequences of finite modules.
* `Stacks.Examples.ModTwoInvariant.eulerSeq`: the sequence `k ↦ φ (⋀^k X)`.

## Main results

* `Stacks.Examples.ModTwoInvariant.sum_eulerSeq_eq_zero`: if `B ^ n × Q ≃ B ^ (n + 1) × P'` with
  `Q` and `P'` finite, then `∑ k, φ (⋀^k Q) = 0` over any range beyond the vanishing of the
  exterior powers of `P'`.
* `Stacks.Examples.shiftAdd_injective`: `shiftAdd` is injective.
* `Stacks.Examples.sum_range_eq_zero_of_iterate_shiftAdd_eq`: if `shiftAdd^[n] a` equals
  `shiftAdd^[n + 1] b` for a sequence `b` vanishing from `N` on, then `∑ k < N + 1, a k = 0` in
  `ZMod 2`.
-/

@[expose] public section

namespace Stacks.Examples

open Finset

variable {G : Type*} [AddCommGroup G]

/-- The coefficients of `(1 + t) · ∑ c k t ^ k`. -/
def shiftAdd (c : ℕ → G) : ℕ → G
  | 0 => c 0
  | k + 1 => c (k + 1) + c k

@[simp]
theorem shiftAdd_zero (c : ℕ → G) : shiftAdd c 0 = c 0 := rfl

@[simp]
theorem shiftAdd_succ (c : ℕ → G) (k : ℕ) : shiftAdd c (k + 1) = c (k + 1) + c k := rfl

theorem shiftAdd_sub (a b : ℕ → G) : shiftAdd (a - b) = shiftAdd a - shiftAdd b := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    change (a (k + 1) - b (k + 1)) + (a k - b k) = (a (k + 1) + a k) - (b (k + 1) + b k)
    abel

theorem eq_zero_of_shiftAdd_eq_zero (c : ℕ → G) (h : shiftAdd c = 0) : c = 0 := by
  have key : ∀ k, c k = 0 := by
    intro k
    induction k with
    | zero => exact congrFun h 0
    | succ k ih =>
      have hk : c (k + 1) + c k = 0 := congrFun h (k + 1)
      rw [ih, add_zero] at hk
      exact hk
  funext k
  exact key k

/-- Multiplication by `1 + t` is injective. -/
theorem shiftAdd_injective : Function.Injective (shiftAdd (G := G)) := by
  intro a b hab
  have h : shiftAdd (a - b) = 0 := by rw [shiftAdd_sub, hab, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_shiftAdd_eq_zero _ h)

/-- Over `ZMod 2`, the coefficients of `(1 + t) · B(t)` sum to zero. -/
theorem sum_range_shiftAdd_eq_zero (b : ℕ → ZMod 2) (N : ℕ) (hb : ∀ k, N ≤ k → b k = 0) :
    ∑ k ∈ range (N + 1), shiftAdd b k = 0 := by
  have h1 : ∑ k ∈ range (N + 1), shiftAdd b k =
      (∑ k ∈ range N, b (k + 1)) + (∑ k ∈ range N, b k) + b 0 := by
    rw [sum_range_succ', shiftAdd_zero]
    simp only [shiftAdd_succ, sum_add_distrib]
  have h2 : ∑ k ∈ range (N + 1), b k = (∑ k ∈ range N, b (k + 1)) + b 0 :=
    sum_range_succ' b N
  have h3 : ∑ k ∈ range (N + 1), b k = ∑ k ∈ range N, b k := by
    rw [sum_range_succ, hb N le_rfl, add_zero]
  rw [h1, add_right_comm, ← h2, h3, CharTwo.add_self_eq_zero]

/-- **Cancellation of `(1 + t) ^ n` modulo two.** If `(1 + t) ^ n · A = (1 + t) ^ (n + 1) · B`
with `B` vanishing from degree `N` on, then the coefficients of `A` of degree at most `N` sum to
zero in `ZMod 2`. -/
theorem sum_range_eq_zero_of_iterate_shiftAdd_eq (a b : ℕ → ZMod 2) (N n : ℕ)
    (hb : ∀ k, N ≤ k → b k = 0) (h : shiftAdd^[n] a = shiftAdd^[n + 1] b) :
    ∑ k ∈ range (N + 1), a k = 0 := by
  rw [Function.iterate_succ_apply] at h
  have ha : a = shiftAdd b := (shiftAdd_injective.iterate n) h
  rw [ha]
  exact sum_range_shiftAdd_eq_zero b N hb

/-! ### Invariants of modules and exterior powers -/

universe u

/-- A function from `B`-modules to `ZMod 2` which is invariant under isomorphism, additive on
products of finite modules and additive on short exact sequences of finite modules. -/
structure ModTwoInvariant (B : Type u) [CommRing B] where
  /-- The value of the invariant on a module. -/
  toFun : (X : Type u) → [AddCommGroup X] → [Module B X] → ZMod 2
  /-- Isomorphic modules have the same value. -/
  congr' : ∀ {X Y : Type u} [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y],
    (X ≃ₗ[B] Y) → toFun X = toFun Y
  /-- The value on a product of finite modules is the sum of the values. -/
  prod' : ∀ (X Y : Type u) [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y],
    Module.Finite B X → Module.Finite B Y → toFun (X × Y) = toFun X + toFun Y
  /-- The value is additive on short exact sequences of finite modules. -/
  shortExact' : ∀ (X Y Z : Type u) [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y]
    [AddCommGroup Z] [Module B Z], Module.Finite B X → Module.Finite B Y → Module.Finite B Z →
    ∀ (f : X →ₗ[B] Y) (g : Y →ₗ[B] Z), Function.Injective f → Function.Exact f g →
      Function.Surjective g → toFun Y = toFun X + toFun Z

/-- The linear equivalence of exterior powers induced by a linear equivalence. -/
noncomputable def exteriorPowerCongr {B : Type u} [CommRing B] {X Y : Type u} [AddCommGroup X]
    [Module B X] [AddCommGroup Y] [Module B Y] (k : ℕ) (e : X ≃ₗ[B] Y) :
    ⋀[B]^k X ≃ₗ[B] ⋀[B]^k Y :=
  LinearEquiv.ofLinearMap (exteriorPower.map k e.toLinearMap)
    (exteriorPower.map k e.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp, LinearEquiv.comp_symm, exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp, LinearEquiv.symm_comp, exteriorPower.map_id])

/-- The exterior powers of a finite module vanish in all large degrees. -/
theorem exists_subsingleton_exteriorPower (B : Type u) [CommRing B] (X : Type u)
    [AddCommGroup X] [Module B X] [Module.Finite B X] :
    ∃ N : ℕ, ∀ k, N ≤ k → Subsingleton (⋀[B]^k X) := by
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := X)
  refine ⟨m + 1, fun k hk => ?_⟩
  refine exteriorPower.subsingleton_of_span_eq_top_of_card_lt (R := B) s hs k ?_
  rw [Nat.card_fin]
  omega

/-- `(Fin (n + 1) → B) × X` is `((Fin n → B) × X) × B`. -/
noncomputable def finSuccProdEquiv (B : Type u) [CommRing B] (n : ℕ) (X : Type u)
    [AddCommGroup X] [Module B X] :
    ((Fin (n + 1) → B) × X) ≃ₗ[B] ((Fin n → B) × X) × B :=
  LinearEquiv.prodCongr
      (LinearEquiv.piCongrLeft B (fun _ : Option (Fin n) => B) (finSuccEquiv n) ≪≫ₗ
        LinearEquiv.piOptionEquivProd (R := B))
      (LinearEquiv.refl B X) ≪≫ₗ
    LinearEquiv.prodAssoc B B (Fin n → B) X ≪≫ₗ LinearEquiv.prodComm B B ((Fin n → B) × X)

namespace ModTwoInvariant

variable {B : Type u} [CommRing B] (φ : ModTwoInvariant B)

/-- The invariant vanishes on a finite module with one element. -/
theorem eq_zero_of_subsingleton (X : Type u) [AddCommGroup X] [Module B X] [Module.Finite B X]
    [Subsingleton X] : φ.toFun X = 0 := by
  have h1 : φ.toFun X = φ.toFun (X × X) := φ.congr' (LinearEquiv.ofSubsingleton X (X × X))
  rw [φ.prod' X X inferInstance inferInstance, CharTwo.add_self_eq_zero] at h1
  exact h1

/-- The sequence `k ↦ φ (⋀^k X)`, the coefficients of the mod-two Euler polynomial of `X`. -/
noncomputable def eulerSeq (X : Type u) [AddCommGroup X] [Module B X] : ℕ → ZMod 2 :=
  fun k => φ.toFun (⋀[B]^k X)

theorem eulerSeq_congr {X Y : Type u} [AddCommGroup X] [Module B X] [AddCommGroup Y]
    [Module B Y] (e : X ≃ₗ[B] Y) : φ.eulerSeq X = φ.eulerSeq Y :=
  funext fun k => φ.congr' (exteriorPowerCongr k e)

/-- Adding a free summand of rank one multiplies the Euler polynomial by `1 + t`. -/
theorem eulerSeq_prod_self (X : Type u) [AddCommGroup X] [Module B X] [Module.Finite B X] :
    φ.eulerSeq (X × B) = shiftAdd (φ.eulerSeq X) := by
  funext k
  cases k with
  | zero =>
    change φ.toFun (⋀[B]^0 (X × B)) = φ.toFun (⋀[B]^0 X)
    exact (φ.congr' (exteriorPower.zeroEquiv B (X × B))).trans
      (φ.congr' (exteriorPower.zeroEquiv B X)).symm
  | succ k =>
    change φ.toFun (⋀[B]^(k + 1) (X × B)) = φ.toFun (⋀[B]^(k + 1) X) + φ.toFun (⋀[B]^k X)
    rw [φ.congr' (exteriorPower.prodRingEquiv B X k)]
    exact φ.prod' _ _ inferInstance inferInstance

/-- Adding a free summand of rank `n` multiplies the Euler polynomial by `(1 + t) ^ n`. -/
theorem eulerSeq_pi_prod (X : Type u) [AddCommGroup X] [Module B X] [Module.Finite B X] :
    ∀ n : ℕ, φ.eulerSeq ((Fin n → B) × X) = shiftAdd^[n] (φ.eulerSeq X) := by
  intro n
  induction n with
  | zero => exact φ.eulerSeq_congr (LinearEquiv.uniqueProd (R := B) (M := X) (M₂ := Fin 0 → B))
  | succ n ih =>
    rw [φ.eulerSeq_congr (finSuccProdEquiv B n X), φ.eulerSeq_prod_self _, ih,
      Function.iterate_succ_apply']

/-- **The mod-two Euler class of a stably split module vanishes.** If
`B ^ n × Q ≃ B ^ (n + 1) × P'` for finite modules `Q` and `P'`, and the exterior powers of `P'`
vanish from degree `N` on, then `∑_{k ≤ N} φ (⋀^k Q) = 0`. -/
theorem sum_eulerSeq_eq_zero (n N : ℕ) (Q P' : Type u) [AddCommGroup Q] [Module B Q]
    [Module.Finite B Q] [AddCommGroup P'] [Module B P'] [Module.Finite B P']
    (hP' : ∀ k, N ≤ k → Subsingleton (⋀[B]^k P'))
    (e : ((Fin n → B) × Q) ≃ₗ[B] ((Fin (n + 1) → B) × P')) :
    ∑ k ∈ range (N + 1), φ.toFun (⋀[B]^k Q) = 0 := by
  have h := φ.eulerSeq_congr e
  rw [φ.eulerSeq_pi_prod Q n, φ.eulerSeq_pi_prod P' (n + 1)] at h
  refine sum_range_eq_zero_of_iterate_shiftAdd_eq (φ.eulerSeq Q) (φ.eulerSeq P') N n
    (fun k hk => ?_) h
  have := hP' k hk
  exact φ.eq_zero_of_subsingleton _

end ModTwoInvariant

end Stacks.Examples
