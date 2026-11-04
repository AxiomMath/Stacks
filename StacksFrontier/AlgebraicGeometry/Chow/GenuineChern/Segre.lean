module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProperPushforward

/-!
# The first Chern class as a pushforward from the projective bundle

Let `(π : P ⟶ X, 𝒪_P(1))` be the projective bundle of a finite locally free module `ℰ` of rank
`r ≥ 1`, and let `(α_j)_{j ≤ r}` be the family of Chern class cap products of a class
`α ∈ CH_k(X)`, characterized by `α_0 = α` and the relation of [Stacks, Tag 02U6]

  `∑_{i=0}^{r} (-1)^i c₁(𝒪_P(1))^i ∩ π^*α_{r-i} = 0`.

Pushing the relation forward along `π` and applying [Stacks, Tag 02TW] kills every summand with
`i < r - 1`, leaves `(-1)^{r-1} α_1` at `i = r - 1`, and leaves `(-1)^r π_*(c₁(𝒪_P(1))^r ∩ π^*α)`
at `i = r`. Hence

  `c₁(ℰ) ∩ α = π_*(c₁(𝒪_P(1))^r ∩ π^*α)`.

This file proves that formula for an arbitrary bundle datum satisfying both halves of 02TW. The
vanishing half is `Stacks.Chow.projectiveBundleProjection_eq_zero_of_lt`; the top half is the
hypothesis `htop`.

## Main results

* `Stacks.Chow.properChowPushforward_projectiveBundleChernTerm` — the pushforward of a summand of
  the relation is the operation of 02TW, read in the right degree.
* `Stacks.Chow.chowGroupCast_one_eq_projectiveBundleProjection_of_isChernCapFamily` — the
  formula `α_1 = π_*(c₁(𝒪_P(1))^r ∩ π^*α)`.

## References

* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- Transport along an equality of degrees commutes with any degree-indexed family of additive
maps between Chow groups. -/
theorem chowGroupCast_natural (C : ChowSituation.{u}) {X Y : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (q : Y ⟶ C.S) [LocallyOfFiniteType q] (g h : ℤ → ℤ)
    (F : ∀ d : ℤ, chowGroup C p (g d) →+ chowGroup C q (h d)) {d₁ d₂ : ℤ} (hd : d₁ = d₂)
    (y : chowGroup C p (g d₁)) :
    F d₂ (chowGroupCast C p (congrArg g hd) y) = chowGroupCast C q (congrArg h hd) (F d₁ y) := by
  subst hd; rfl

/-- Iterated cap products commute with transport along an equality of degrees. -/
theorem iteratedChernCapOnChow_chowGroupCast (C : ChowSituation.{u}) {P : Scheme.{u}}
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (Os : List (ChernCapOperator C sP)) {d₁ d₂ e : ℤ}
    (hd : d₁ = d₂) (he₁ : e = d₁ + (Os.length : ℤ)) (he₂ : e = d₂ + (Os.length : ℤ))
    (y : chowGroup C sP e) :
    iteratedChernCapOnChow C sP Os d₂ (chowGroupCast C sP he₂ y) =
      chowGroupCast C sP hd (iteratedChernCapOnChow C sP Os d₁ (chowGroupCast C sP he₁ y)) := by
  subst hd; rfl

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [Flat π] [IsProper π]
  (hsP : π ≫ sX = sP) (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
  (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)
  (twist : ChernCapOperator C sP)

omit [Flat π] in
/-- Pushforward after an iterated cap product commutes with transport along an equality of
degrees. -/
theorem properChowPushforward_iteratedChernCapOnChow_chowGroupCast
    (Os : List (ChernCapOperator C sP)) {d₁ d₂ e : ℤ} (hd : d₁ = d₂)
    (he₁ : e = d₁ + (Os.length : ℤ)) (he₂ : e = d₂ + (Os.length : ℤ)) (y : chowGroup C sP e) :
    properChowPushforward C sP sX π hsP d₂
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sX π hsP d₂)
        (iteratedChernCapOnChow C sP Os d₂ (chowGroupCast C sP he₂ y)) =
      chowGroupCast C sX hd (properChowPushforward C sP sX π hsP d₁
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sX π hsP d₁)
        (iteratedChernCapOnChow C sP Os d₁ (chowGroupCast C sP he₁ y))) := by
  subst hd; rfl

/-- **The pushforward of a summand of the relation.** For `i ≤ r`, pushing the `i`-th summand
`c₁(𝒪_P(1))^i ∩ π^*x` of the relation of Stacks 02U6 forward to `X` is the operation of
Stacks 02TW at `s = i`, read in the degree of the relation. -/
theorem properChowPushforward_projectiveBundleChernTerm (k : ℤ) (i : ℕ) (hi : i ≤ r)
    (x : chowGroup C sX (k - ((r - i : ℕ) : ℤ))) :
    properChowPushforward C sP sX π hsP (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sX π hsP _)
        (projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k i hi x) =
      chowGroupCast C sX (by omega)
        (projectiveBundleProjection C sX sP π hsP r hπ hfac twist i
          (k - ((r - i : ℕ) : ℤ)) x) :=
  properChowPushforward_iteratedChernCapOnChow_chowGroupCast C sX sP π hsP
    (List.replicate i twist) (by omega) (by simp only [List.length_replicate]; omega)
    (by simp only [List.length_replicate]; omega) _

/-- Members of a family of Chow classes indexed by `Fin (r + 1)`, in degrees `k - j`, agree up
to transport at equal indices. -/
theorem chowGroupCast_family_congr {X : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q]
    {n : ℕ} (k : ℤ) (c : ∀ j : Fin n, chowGroup C q (k - (j : ℤ))) {i j : Fin n} (h : i = j) :
    chowGroupCast C q (by rw [h]) (c i) = c j := by
  subst h; rfl

/-- An equation between transports, moved to the other side. -/
theorem chowGroupCast_eq_iff {X : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q] {d e : ℤ}
    (h : d = e) (x : chowGroup C q d) (y : chowGroup C q e) :
    chowGroupCast C q h x = y ↔ x = chowGroupCast C q h.symm y := by
  subst h; rfl

/-- **The first Chern class as a pushforward from the projective bundle.** If `c` is the family
of Chern class cap products of `α ∈ CH_k(X)` for a module of rank `r ≥ 1`, and the bundle
satisfies the top half of Stacks 02TW, then

  `c₁(ℰ) ∩ α = π_*(c₁(𝒪_P(1))^r ∩ π^*α)`. -/
theorem chowGroupCast_one_eq_projectiveBundleProjection_of_isChernCapFamily (hr : 1 ≤ r)
    (htop : ∀ (k : ℤ) (β : chowGroup C sX k),
      projectiveBundleProjection C sX sP π hsP r hπ hfac twist (r - 1) k β =
        chowGroupCast C sX (by omega) β)
    (k : ℤ) (α : chowGroup C sX k) (c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)))
    (hc : IsChernCapFamily C sX sP π hsP r hπ hfac twist k α c) :
    chowGroupCast C sX (by simp only [Nat.cast_one]; omega) (c ⟨1, by omega⟩) =
      projectiveBundleProjection C sX sP π hsP r hπ hfac twist r k α := by
  obtain ⟨h0, hrel⟩ := hc
  have hpush := congrArg (properChowPushforward C sP sX π hsP (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sX π hsP _)) hrel
  rw [map_zero, map_sum] at hpush
  simp only [map_zsmul, properChowPushforward_projectiveBundleChernTerm] at hpush
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add] at hpush
  swap
  · intro i _
    rw [projectiveBundleProjection_eq_zero_of_lt C sX sP π hsP (m + 1) hπ hfac twist _
      (by simp only [Fin.val_castSucc]; omega)]
    simp
  simp only [Fin.val_castSucc, Fin.val_last] at hpush
  -- the summand `i = m`
  have hm : chowGroupCast C sX (show k - ((m + 1 - m : ℕ) : ℤ) + ((m + 1 - 1 : ℕ) : ℤ) -
        (m : ℤ) = k + ((m + 1 - 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ) by omega)
      (projectiveBundleProjection C sX sP π hsP (m + 1) hπ hfac twist m
        (k - ((m + 1 - m : ℕ) : ℤ)) (c ⟨m + 1 - m, by omega⟩)) =
      chowGroupCast C sX (by simp only [Nat.cast_one]; omega) (c ⟨1, by omega⟩) := by
    have hmt : projectiveBundleProjection C sX sP π hsP (m + 1) hπ hfac twist m
        (k - ((m + 1 - m : ℕ) : ℤ)) (c ⟨m + 1 - m, by omega⟩) =
        chowGroupCast C sX (by simp only; omega) (c ⟨m + 1 - m, by omega⟩) :=
      htop (k - ((m + 1 - m : ℕ) : ℤ)) (c ⟨m + 1 - m, by omega⟩)
    rw [hmt, chowGroupCast_chowGroupCast]
    rw [← chowGroupCast_family_congr C sX k c (show (⟨m + 1 - m, by omega⟩ : Fin (m + 2)) =
      ⟨1, by omega⟩ from Fin.ext (by simp)), chowGroupCast_chowGroupCast]
  -- the summand `i = m + 1`
  have hlast : chowGroupCast C sX (show k - ((m + 1 - (m + 1) : ℕ) : ℤ) +
        ((m + 1 - 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ) =
        k + ((m + 1 - 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ) by omega)
      (projectiveBundleProjection C sX sP π hsP (m + 1) hπ hfac twist (m + 1)
        (k - ((m + 1 - (m + 1) : ℕ) : ℤ)) (c ⟨m + 1 - (m + 1), by omega⟩)) =
      projectiveBundleProjection C sX sP π hsP (m + 1) hπ hfac twist (m + 1) k α := by
    rw [← h0, ← chowGroupCast_family_congr C sX k c
      (show (⟨m + 1 - (m + 1), by omega⟩ : Fin (m + 2)) = ⟨0, by omega⟩ from Fin.ext (by simp)),
      chowGroupCast_chowGroupCast]
    exact chowGroupCast_natural C sX sX (fun d => d)
      (fun d => d + ((m + 1 - 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ))
      (fun d => projectiveBundleProjection C sX sP π hsP (m + 1) hπ hfac twist (m + 1) d)
      (by simp) _ |>.symm
  rw [hm, hlast] at hpush
  have hsign : ((-1 : ℤ) ^ (m + 1)) = -((-1 : ℤ) ^ m) := by ring
  rw [hsign, neg_smul, ← sub_eq_add_neg, sub_eq_zero] at hpush
  have hunit : IsUnit ((-1 : ℤ) ^ m) := (isUnit_neg_one (α := ℤ)).pow m
  rcases neg_one_pow_eq_or ℤ m with h | h <;> rw [h] at hpush <;> simpa using hpush

end Stacks.Chow

end
