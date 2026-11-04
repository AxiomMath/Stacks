module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence

/-!
# The map of the projective space bundle formula

Let `π : P ⟶ U` be flat, locally of finite type and of relative dimension `n` over a base
situation of chapter 42, and let `ξ` be a first Chern class cap operator on `P`. [Stacks, Tag
02TX] is about the map

  `⨁_{i = 0}^{n} A_{k + i}(U) ⟶ A_{k + n}(P),  (α_i) ↦ ∑_i ξ^i ∩ π^* α_i`,

for `π` a projective bundle and `ξ = c₁(𝒪(1))`. This file defines the powers `ξ^s ∩ -` with
explicit degree bookkeeping, the flat pullback along `π`, the map itself, and the operation
`π_*(ξ^s ∩ π^*(-))` of [Stacks, Tag 02TW].

## Main definitions

* `Stacks.Chow.capPow` — `ξ^s ∩ - : A_a(P) ⟶ A_m(P)` for `a = m + s`, the innermost cap being
  applied first.
* `Stacks.Chow.bundlePullback` — `π^* : A_k(U) ⟶ A_{k+n}(P)`, Stacks 0FVK with Stacks 02S1.
* `Stacks.Chow.bundleTerm` — `ξ^i ∩ π^*(-) : A_{k+i}(U) ⟶ A_{k+n}(P)`.
* `Stacks.Chow.bundleMap` — the map of Stacks 02TX.
* `Stacks.Chow.bundleProjection` — `π_*(ξ^s ∩ π^*(-)) : A_k(U) ⟶ A_{k+n-s}(U)` for proper `π`.

## Main results

* `Stacks.Chow.capPow_succ_apply'` — `ξ^{s+1} ∩ x = ξ ∩ (ξ^s ∩ x)`: the outermost cap may be
  peeled off as well as the innermost.
* `Stacks.Chow.capPow_comm` — a family of degree-preserving maps commuting with one cap
  commutes with every power.
* `Stacks.Chow.capPow_eq_iteratedChernCapOnChow` — the comparison with
  `Stacks.Chow.iteratedChernCapOnChow` at a constant list.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

section Pow

variable (C : ChowSituation.{u}) {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (ξ : ChernCapOperator C sP)

/-- **`ξ^s ∩ - : A_a(P) ⟶ A_m(P)`** for `a = m + s`. The recursion applies the innermost cap
first: `ξ^{s+1} ∩ x = ξ^s ∩ (ξ ∩ x)`. -/
def capPow : (s : ℕ) → (a m : ℤ) → a = m + s → (chowGroup C sP a →+ chowGroup C sP m)
  | 0, _, _, h => (chowGroupCast C sP (by simpa using h)).toAddMonoidHom
  | s + 1, a, m, h => (capPow s (a - 1) m (by push_cast at h; omega)).comp
      ((ξ.capOnChow C sP (a - 1)).comp
        (chowGroupCast C sP (show a = a - 1 + 1 by ring)).toAddMonoidHom)

/-- The zeroth power `ξ^0 ∩ -` is the degree cast `A_a(P) ⟶ A_m(P)`. -/
@[simp]
theorem capPow_zero_apply (a m : ℤ) (h : a = m + ((0 : ℕ) : ℤ)) (x : chowGroup C sP a) :
    capPow C sP ξ 0 a m h x = chowGroupCast C sP (by simpa using h) x :=
  rfl

/-- `ξ^{s+1} ∩ x = ξ^s ∩ (ξ ∩ x)`, the innermost cap being applied first. -/
theorem capPow_succ_apply (s : ℕ) (a m : ℤ) (h : a = m + ((s + 1 : ℕ) : ℤ))
    (x : chowGroup C sP a) :
    capPow C sP ξ (s + 1) a m h x =
      capPow C sP ξ s (a - 1) m (by push_cast at h; omega)
        (ξ.capOnChow C sP (a - 1) (chowGroupCast C sP (show a = a - 1 + 1 by ring) x)) :=
  rfl

/-- The source degree of a power may be transported along an equality. -/
theorem capPow_cast (s : ℕ) {a a' : ℤ} (m : ℤ) (h : a' = m + s) (e : a = a')
    (x : chowGroup C sP a) :
    capPow C sP ξ s a' m h (chowGroupCast C sP e x) = capPow C sP ξ s a m (e.trans h) x := by
  subst e; rfl

/-- The target degree of a power may be transported along an equality. -/
theorem chowGroupCast_capPow (s : ℕ) (a : ℤ) {m m' : ℤ} (h : a = m + s) (e : m = m')
    (x : chowGroup C sP a) :
    chowGroupCast C sP e (capPow C sP ξ s a m h x) = capPow C sP ξ s a m' (e ▸ h) x := by
  subst e; rfl

/-- **The outermost cap may be peeled off**: `ξ^{s+1} ∩ x = ξ ∩ (ξ^s ∩ x)`. -/
theorem capPow_succ_apply' (s : ℕ) (a m : ℤ) (h : a = m + ((s + 1 : ℕ) : ℤ))
    (x : chowGroup C sP a) :
    capPow C sP ξ (s + 1) a m h x =
      ξ.capOnChow C sP m
        (capPow C sP ξ s a (m + 1) (by push_cast at h ⊢; omega) x) := by
  induction s generalizing a with
  | zero =>
    rw [capPow_succ_apply, capPow_zero_apply, capPow_zero_apply]
    have hm : a - 1 = m := by push_cast at h; omega
    subst hm
    simp only [chowGroupCast_rfl]
  | succ s ih =>
    rw [capPow_succ_apply, ih (a - 1) (by push_cast at h ⊢; omega), capPow_succ_apply]

/-- **A family of degree-preserving homomorphisms commuting with one cap commutes with every
power.** -/
theorem capPow_comm {Q : Scheme.{u}} (sQ : Q ⟶ C.S) [LocallyOfFiniteType sQ]
    (η : ChernCapOperator C sQ) (F : ∀ d : ℤ, chowGroup C sQ d →+ chowGroup C sP d)
    (hF : ∀ (d : ℤ) (x : chowGroup C sQ (d + 1)),
      F d (η.capOnChow C sQ d x) = ξ.capOnChow C sP d (F (d + 1) x))
    (s : ℕ) (a m : ℤ) (h : a = m + s) (x : chowGroup C sQ a) :
    F m (capPow C sQ η s a m h x) = capPow C sP ξ s a m h (F a x) := by
  have hcast : ∀ {d d' : ℤ} (e : d = d') (y : chowGroup C sQ d),
      F d' (chowGroupCast C sQ e y) = chowGroupCast C sP e (F d y) := by
    intro d d' e y; subst e; rfl
  induction s generalizing a with
  | zero => rw [capPow_zero_apply, capPow_zero_apply, hcast]
  | succ s ih => rw [capPow_succ_apply, capPow_succ_apply, ih, hF, hcast]

/-- **The comparison with the iterated cap product of a constant list.** -/
theorem capPow_eq_iteratedChernCapOnChow (s : ℕ) (m : ℤ)
    (x : chowGroup C sP (m + ((List.replicate s ξ).length : ℤ))) :
    capPow C sP ξ s _ m (by simp) x = iteratedChernCapOnChow C sP (List.replicate s ξ) m x := by
  induction s generalizing m with
  | zero =>
    simp only [List.replicate_zero, iteratedChernCapOnChow]
    rw [chowGroupDegreeCast_apply, capPow_zero_apply]
    rfl
  | succ s ih =>
    rw [capPow_succ_apply']
    simp only [List.replicate_succ, iteratedChernCapOnChow]
    rw [chowGroupDegreeCast_apply, AddMonoidHom.comp_apply, ← ih (m + 1),
      capPow_cast]

end Pow

section Map

variable (C : ChowSituation.{u}) {P U : Scheme.{u}} (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ U) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sU = sP) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π n)
  (ξ : ChernCapOperator C sP)

/-- **The flat pullback `π^* : A_k(U) ⟶ A_{k+n}(P)`** of Stacks 0FVK, its factoring through
rational equivalence being Stacks 02S1. -/
def bundlePullback (k : ℤ) : chowGroup C sU k →+ chowGroup C sP (k + n) :=
  flatPullbackChow C sP sU π hsP n hπ k
    (flatPullbackFactorsThroughRationalEquivalence_general C sP sU π hsP n hπ k)

/-- On the class of a cycle `α`, `π^*` is the class of the flat pullback of `α`. -/
@[simp]
theorem bundlePullback_mk (k : ℤ) (α : CycleGroup C sU k) :
    bundlePullback C sU sP π hsP n hπ k (QuotientAddGroup.mk' (rationalEquivalences C sU k) α) =
      QuotientAddGroup.mk' _ (flatPullback C sP sU π hsP n hπ k α) :=
  rfl

/-- **The summand `ξ^i ∩ π^*(-) : A_{k+i}(U) ⟶ A_{k+n}(P)`** of the map of Stacks 02TX. -/
def bundleTerm (k : ℤ) (i : ℕ) : chowGroup C sU (k + i) →+ chowGroup C sP (k + n) :=
  (capPow C sP ξ i (k + i + n) (k + n) (by ring)).comp
    (bundlePullback C sU sP π hsP n hπ (k + i))

/-- **The map of Stacks 02TX**, `⨁_{i ≤ n} A_{k+i}(U) ⟶ A_{k+n}(P)`,
`(α_i) ↦ ∑_i ξ^i ∩ π^* α_i`. -/
def bundleMap (k : ℤ) :
    (∀ i : Fin (n + 1), chowGroup C sU (k + (i : ℕ))) →+ chowGroup C sP (k + n) :=
  ∑ i : Fin (n + 1), (bundleTerm C sU sP π hsP n hπ ξ k i).comp (Pi.evalAddMonoidHom _ i)

/-- The map sends `(β_i)` to `∑_i ξ^i ∩ π^* β_i`. -/
theorem bundleMap_apply (k : ℤ) (β : ∀ i : Fin (n + 1), chowGroup C sU (k + (i : ℕ))) :
    bundleMap C sU sP π hsP n hπ ξ k β =
      ∑ i : Fin (n + 1), bundleTerm C sU sP π hsP n hπ ξ k i (β i) := by
  simp [bundleMap]

/-- **The operation of Stacks 02TW**, `π_*(ξ^s ∩ π^*(-)) : A_k(U) ⟶ A_m(U)` for
`k + n = m + s`, for proper `π`. -/
def bundleProjection [IsProper π] (s : ℕ) (k m : ℤ) (h : k + n = m + s) :
    chowGroup C sU k →+ chowGroup C sU m :=
  (properChowPushforward C sP sU π hsP m
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP m)).comp
    ((capPow C sP ξ s (k + n) m h).comp (bundlePullback C sU sP π hsP n hπ k))

end Map

end Stacks.Chow

end
