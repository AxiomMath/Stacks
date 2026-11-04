module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Map

/-!
# Injectivity of the map of the projective space bundle formula

Let `π : P ⟶ X` be flat and proper of relative dimension `n` and `ξ` a first Chern class cap
operator on `P`. If `π_*(ξ^s ∩ π^*α) = 0` for `s < n` and `π_*(ξ^n ∩ π^*α) = α` — which is
[Stacks, Tag 02TW] — then the map of [Stacks, Tag 02TX] is injective. This is the first half of
the source's proof of Stacks 02TX: from `∑_i ξ^i ∩ π^*α_i = 0`, applying `π_*(ξ^{n-m} ∩ -)` kills
every summand but the `m`-th once the summands of index `> m` are known to vanish.

## Main results

* `Stacks.Chow.capPow_capPow` — `ξ^j ∩ (ξ^i ∩ x) = ξ^{i+j} ∩ x`.
* `Stacks.Chow.bundleProjection_eq_zero_of_lt` — Stacks 02TW, the vanishing below the fibre
  dimension, in the notation of `Stacks.Chow.bundleProjection`.
* `Stacks.Chow.bundleMap_injective` — **Stacks 02TX, injectivity**, from the top case of Stacks
  02TW.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- The exponent of a power may be transported along an equality. -/
theorem capPow_congr (C : ChowSituation.{u}) {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (ξ : ChernCapOperator C sP) {s s' : ℕ} (e : s = s') (a m : ℤ)
    (h : a = m + s) (x : chowGroup C sP a) :
    capPow C sP ξ s a m h x = capPow C sP ξ s' a m (e ▸ h) x := by
  subst e; rfl

/-- **Powers of a cap operator compose additively**: `ξ^j ∩ (ξ^i ∩ x) = ξ^{i+j} ∩ x`. -/
theorem capPow_capPow (C : ChowSituation.{u}) {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (ξ : ChernCapOperator C sP) (i j : ℕ) (a b m : ℤ)
    (hi : a = b + i) (hj : b = m + j) (x : chowGroup C sP a) :
    capPow C sP ξ j b m hj (capPow C sP ξ i a b hi x) =
      capPow C sP ξ (i + j) a m (by rw [hi, hj]; push_cast; ring) x := by
  induction i generalizing a with
  | zero =>
    rw [capPow_zero_apply, capPow_cast]
    simp only [zero_add]
  | succ i ih =>
    rw [capPow_succ_apply, ih, capPow_congr C sP ξ (show i + 1 + j = (i + j) + 1 by ring),
      capPow_succ_apply]

section Projection

variable (C : ChowSituation.{u}) {P X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [Flat π] [IsProper π] (hsP : π ≫ sX = sP)
  (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π n)
  (ξ : ChernCapOperator C sP)

/-- **Stacks 02TW, vanishing below the fibre dimension.** For `s < n`,
`π_*(ξ^s ∩ π^*α) = 0`. This is the dimension count of
`Stacks.Chow.properChowPushforward_iteratedChernCapOnChow_flatPullbackChow_eq_zero`. -/
theorem bundleProjection_eq_zero_of_lt (s : ℕ) (hs : s < n) (k m : ℤ) (h : k + n = m + s)
    (α : chowGroup C sX k) : bundleProjection C sX sP π hsP n hπ ξ s k m h α = 0 := by
  simp only [bundleProjection, AddMonoidHom.coe_comp, Function.comp_apply]
  have hcast : k + (n : ℤ) = m + ((List.replicate s ξ).length : ℕ) := by
    simp only [List.length_replicate]; exact h
  have hpow : capPow C sP ξ s (k + n) m h (bundlePullback C sX sP π hsP n hπ k α) =
      iteratedChernCapOnChow C sP (List.replicate s ξ) m
        (chowGroupCast C sP hcast (bundlePullback C sX sP π hsP n hπ k α)) := by
    rw [← capPow_eq_iteratedChernCapOnChow, capPow_cast]
  rw [hpow]
  exact properChowPushforward_iteratedChernCapOnChow_flatPullbackChow_eq_zero C sX sP π hsP n
    hπ k m (by have : (s : ℤ) < n := by exact_mod_cast hs
               omega)
    (flatPullbackFactorsThroughRationalEquivalence_general C sP sX π hsP n hπ k)
    (List.replicate s ξ) hcast α

/-- **Stacks 02TX, injectivity.** If `π_*(ξ^n ∩ π^*α) = α` for every class `α` on `X` — the top
case of Stacks 02TW — then the map `(α_i) ↦ ∑_i ξ^i ∩ π^*α_i` is injective in every degree. -/
theorem bundleMap_injective
    (htop : ∀ (k : ℤ) (α : chowGroup C sX k),
      bundleProjection C sX sP π hsP n hπ ξ n k k (by ring) α = α) (k : ℤ) :
    Function.Injective (bundleMap C sX sP π hsP n hπ ξ k) := by
  rw [injective_iff_map_eq_zero]
  intro β hβ
  -- the operation `π_*(ξ^{n-m} ∩ -)` applied to the `i`-th summand
  have hterm : ∀ (i : Fin (n + 1)) (m : ℕ) (hm : m ≤ n),
      properChowPushforward C sP sX π hsP (k + m)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sX π hsP _)
          (capPow C sP ξ (n - m) (k + n) (k + m) (by push_cast [hm]; ring)
            (bundleTerm C sX sP π hsP n hπ ξ k i (β i))) =
        bundleProjection C sX sP π hsP n hπ ξ ((i : ℕ) + (n - m)) (k + (i : ℕ)) (k + m)
          (by push_cast [hm]; ring) (β i) := by
    intro i m hm
    simp only [bundleTerm, bundleProjection, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [capPow_capPow]
  have hexp : ∀ {s s' : ℕ} (e : s = s') (a b : ℤ) (h : a + n = b + s) (x : chowGroup C sX a),
      bundleProjection C sX sP π hsP n hπ ξ s a b h x =
        bundleProjection C sX sP π hsP n hπ ξ s' a b (e ▸ h) x := by
    intro s s' e a b h x; subst e; rfl
  -- one step of the downward induction
  have step : ∀ i : Fin (n + 1), (∀ i' : Fin (n + 1), (i : ℕ) < i' → β i' = 0) → β i = 0 := by
    intro i hi
    have hle : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    have h0 := congrArg (fun z ↦ properChowPushforward C sP sX π hsP (k + (i : ℕ))
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sX π hsP _)
      (capPow C sP ξ (n - i) (k + n) (k + (i : ℕ)) (by push_cast [hle]; ring) z)) hβ
    simp only [map_zero] at h0
    rw [bundleMap_apply, map_sum, map_sum] at h0
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j i hle] at h0
    rw [Finset.sum_eq_single i (fun j _ hj ↦ ?_) (by simp)] at h0
    · rw [hexp (show (i : ℕ) + (n - i) = n by omega)] at h0
      rw [← htop (k + (i : ℕ)) (β i)]
      exact h0
    · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hj) with hlt | hgt
      · exact bundleProjection_eq_zero_of_lt C sX sP π hsP n hπ ξ _ (by omega) _ _ _ _
      · rw [hi j hgt, map_zero]
  have all : ∀ d : ℕ, ∀ i : Fin (n + 1), n - d ≤ (i : ℕ) → β i = 0 := by
    intro d
    induction d with
    | zero =>
      intro i hi
      exact step i fun i' hi' ↦ absurd i'.isLt (by omega)
    | succ d ih =>
      intro i hi
      by_cases h : n - d ≤ (i : ℕ)
      · exact ih i h
      · exact step i fun i' hi' ↦ ih i' (by omega)
  funext i
  exact all n i (by omega)

end Projection

end Stacks.Chow

end
