module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneForkSystem

/-!
# The affine extension system over the exceptional diagrams of type E

The affine extension system of
`AlgebraicGeometry.NumericalType.affine_system_of_erase_leaf` asks for a positive vector `m` on
the vertices of a Dynkin shape `d` annihilated by the weighted Cartan matrix of `d` away from a
single vertex `r₀`, where instead `2 (M m)_{r₀} = k · wf(r₀) · m_{r₀}` for some `k ∈ {1, 2, 3}`.
This file solves that system over the three exceptional diagrams `E₆`, `E₇` and `E₈`.

Every weight factor of a diagram of type `E` is one, so the row of the weighted Cartan matrix at
a vertex is twice the multiplicity there minus the multiplicities of its neighbours. Each of the
three diagrams has a branch vertex, so the system is not a single three-term recurrence as it is
along a chain; instead the homogeneous equations away from `r₀` already determine the
multiplicities up to a scalar, and the inhomogeneous equation at `r₀` becomes a condition
`α c = k β c` on the level `k`, which has an integral solution for exactly one position of `r₀`:

* over `E₆` the attachment vertex is the tip of the short branch, the level is one and the
  multiplicities are `(a, 2a, 3a, 2a, a, 2a)`;
* over `E₇` it is the far end of the two-vertex branch, the level is one and the multiplicities
  are `(a, 2a, 3a, 4a, 3a, 2a, 2a)`;
* over `E₈` it is the far end of the long arm, the level is one and the multiplicities are
  `(2a, 3a, 4a, 5a, 6a, 4a, 2a, 3a)`.

## Main results

* `AlgebraicGeometry.DynkinShape.row_one_of_weight_one`,
  `AlgebraicGeometry.DynkinShape.row_two_of_weight_one`,
  `AlgebraicGeometry.DynkinShape.row_three_of_weight_one` — a row of the weighted Cartan matrix
  of a diagram all of whose weight factors are one, at a vertex with one, two or three
  neighbours.
* `AlgebraicGeometry.affine_system_solved_E6`, `AlgebraicGeometry.affine_system_solved_E7`,
  `AlgebraicGeometry.affine_system_solved_E8` — the system solved over `E₆`, `E₇` and `E₈`.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry

/-! ### Rows of a diagram with all weight factors one -/

/-- A row of the weighted Cartan matrix of a diagram all of whose weight factors are one, at a
vertex with exactly one neighbour. -/
public lemma DynkinShape.row_one_of_weight_one {t : ℕ} (d : DynkinShape) (ht : d.Allows t)
    (hwf : ∀ r : Fin t, d.weightFactor r = 1) (m : Fin t → ℤ) (r a : Fin t) (ha : d.Edge r a)
    (hother : ∀ s, d.Edge r s → s = a) :
    ∑ s, d.weightedCartan r s * m s = 2 * m r - m a := by
  rw [d.row_one ht m r a ha hother, hwf r, hwf a]
  norm_num

/-- A row of the weighted Cartan matrix of a diagram all of whose weight factors are one, at a
vertex with exactly two neighbours. -/
public lemma DynkinShape.row_two_of_weight_one {t : ℕ} (d : DynkinShape) (ht : d.Allows t)
    (hwf : ∀ r : Fin t, d.weightFactor r = 1) (m : Fin t → ℤ) (r a b : Fin t) (hab : a ≠ b)
    (ha : d.Edge r a) (hb : d.Edge r b) (hother : ∀ s, d.Edge r s → s = a ∨ s = b) :
    ∑ s, d.weightedCartan r s * m s = 2 * m r - m a - m b := by
  rw [d.row_two ht m r a b hab ha hb hother, hwf r, hwf a, hwf b]
  norm_num

/-- A row of the weighted Cartan matrix of a diagram all of whose weight factors are one, at a
vertex with exactly three neighbours. -/
public lemma DynkinShape.row_three_of_weight_one {t : ℕ} (d : DynkinShape) (ht : d.Allows t)
    (hwf : ∀ r : Fin t, d.weightFactor r = 1) (m : Fin t → ℤ) (r a b c : Fin t) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : d.Edge r a) (hb : d.Edge r b) (hc : d.Edge r c)
    (hother : ∀ s, d.Edge r s → s = a ∨ s = b ∨ s = c) :
    ∑ s, d.weightedCartan r s * m s = 2 * m r - m a - m b - m c := by
  rw [d.row_three ht m r a b c hab hac hbc ha hb hc hother, hwf r, hwf a, hwf b, hwf c]
  norm_num

/-! ### Type E₆ -/

private lemma E6_rows (m : Fin 6 → ℤ) :
    ∑ s, DynkinShape.E6.weightedCartan 0 s * m s = 2 * m 0 - m 1 ∧
    ∑ s, DynkinShape.E6.weightedCartan 1 s * m s = 2 * m 1 - m 0 - m 2 ∧
    ∑ s, DynkinShape.E6.weightedCartan 2 s * m s = 2 * m 2 - m 1 - m 3 - m 5 ∧
    ∑ s, DynkinShape.E6.weightedCartan 3 s * m s = 2 * m 3 - m 2 - m 4 ∧
    ∑ s, DynkinShape.E6.weightedCartan 4 s * m s = 2 * m 4 - m 3 ∧
    ∑ s, DynkinShape.E6.weightedCartan 5 s * m s = 2 * m 5 - m 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Fin.sum_univ_succ, DynkinShape.weightedCartan, DynkinShape.Edge,
      DynkinShape.weightFactor] <;> ring

/-- The affine extension system solved over the diagram `E₆`: it has a solution only when the
attached component hangs at the tip of the short branch, where the level is one and the
multiplicities are `(a, 2a, 3a, 2a, a, 2a)`. -/
public lemma affine_system_solved_E6 (m : Fin 6 → ℤ) (hpos : ∀ r, 0 < m r) (r₀ : Fin 6) (k : ℤ)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.E6.weightedCartan r s * m s = 0)
    (hmain : 2 * ∑ s, DynkinShape.E6.weightedCartan r₀ s * m s
      = k * DynkinShape.E6.weightFactor r₀ * m r₀) :
    r₀.val = 5 ∧ k = 1 ∧ ∃ a : ℤ, 0 < a ∧ ∀ r : Fin 6,
      m r = (if r.val = 0 ∨ r.val = 4 then 1 else if r.val = 2 then 3 else 2) * a := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := E6_rows m
  have h0 := hrest 0
  have h1 := hrest 1
  have h2 := hrest 2
  have h3 := hrest 3
  have h4 := hrest 4
  have h5 := hrest 5
  have hwf : DynkinShape.E6.weightFactor r₀ = 1 := rfl
  rw [hwf, mul_one] at hmain
  have hcase : r₀ = 0 ∨ r₀ = 1 ∨ r₀ = 2 ∨ r₀ = 3 ∨ r₀ = 4 ∨ r₀ = 5 := by
    fin_cases r₀ <;> simp
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [e0, e1, e2, e3, e4, e5, ne_eq, Fin.reduceEq, not_false_eq_true, forall_const]
      at h0 h1 h2 h3 h4 h5 hmain
  · have hk : (2 * k) * m 0 = 3 * m 0 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 0).ne' hk) (by omega)
  · have hk : (5 * k) * m 1 = 3 * m 1 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 1).ne' hk) (by omega)
  · have hk : (3 * k) * m 2 = 1 * m 2 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 2).ne' hk) (by omega)
  · have hk : (5 * k) * m 3 = 3 * m 3 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 3).ne' hk) (by omega)
  · have hk : (2 * k) * m 4 = 3 * m 4 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 4).ne' hk) (by omega)
  · have hk : k * m 5 = 1 * m 5 := by linarith
    refine ⟨rfl, mul_right_cancel₀ (hpos 5).ne' hk, m 0, hpos 0, fun r => ?_⟩
    fin_cases r <;> simp <;> linarith

/-! ### Type E₇ -/

private lemma E7_rows (m : Fin 7 → ℤ) :
    ∑ s, DynkinShape.E7.weightedCartan 0 s * m s = 2 * m 0 - m 1 ∧
    ∑ s, DynkinShape.E7.weightedCartan 1 s * m s = 2 * m 1 - m 0 - m 2 ∧
    ∑ s, DynkinShape.E7.weightedCartan 2 s * m s = 2 * m 2 - m 1 - m 3 ∧
    ∑ s, DynkinShape.E7.weightedCartan 3 s * m s = 2 * m 3 - m 2 - m 4 - m 6 ∧
    ∑ s, DynkinShape.E7.weightedCartan 4 s * m s = 2 * m 4 - m 3 - m 5 ∧
    ∑ s, DynkinShape.E7.weightedCartan 5 s * m s = 2 * m 5 - m 4 ∧
    ∑ s, DynkinShape.E7.weightedCartan 6 s * m s = 2 * m 6 - m 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Fin.sum_univ_succ, DynkinShape.weightedCartan, DynkinShape.Edge,
      DynkinShape.weightFactor] <;> ring

/-- The affine extension system solved over the diagram `E₇`: it has a solution only when the
attached component hangs at the far end of the two-vertex branch, where the level is one and the
multiplicities are `(a, 2a, 3a, 4a, 3a, 2a, 2a)`. -/
public lemma affine_system_solved_E7 (m : Fin 7 → ℤ) (hpos : ∀ r, 0 < m r) (r₀ : Fin 7) (k : ℤ)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.E7.weightedCartan r s * m s = 0)
    (hmain : 2 * ∑ s, DynkinShape.E7.weightedCartan r₀ s * m s
      = k * DynkinShape.E7.weightFactor r₀ * m r₀) :
    r₀.val = 5 ∧ k = 1 ∧ ∃ a : ℤ, 0 < a ∧ ∀ r : Fin 7,
      m r = (if r.val = 0 then 1 else if r.val = 1 ∨ r.val = 5 ∨ r.val = 6 then 2
        else if r.val = 2 ∨ r.val = 4 then 3 else 4) * a := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := E7_rows m
  have h0 := hrest 0
  have h1 := hrest 1
  have h2 := hrest 2
  have h3 := hrest 3
  have h4 := hrest 4
  have h5 := hrest 5
  have h6 := hrest 6
  have hwf : DynkinShape.E7.weightFactor r₀ = 1 := rfl
  rw [hwf, mul_one] at hmain
  have hcase : r₀ = 0 ∨ r₀ = 1 ∨ r₀ = 2 ∨ r₀ = 3 ∨ r₀ = 4 ∨ r₀ = 5 ∨ r₀ = 6 := by
    fin_cases r₀ <;> simp
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [e0, e1, e2, e3, e4, e5, e6, ne_eq, Fin.reduceEq, not_false_eq_true, forall_const]
      at h0 h1 h2 h3 h4 h5 h6 hmain
  · have hk : (3 * k) * m 0 = 4 * m 0 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 0).ne' hk) (by omega)
  · have hk : (2 * k) * m 1 = 1 * m 1 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 1).ne' hk) (by omega)
  · have hk : (15 * k) * m 2 = 4 * m 2 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 2).ne' hk) (by omega)
  · have hk : (6 * k) * m 3 = 1 * m 3 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 3).ne' hk) (by omega)
  · have hk : (3 * k) * m 4 = 1 * m 4 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 4).ne' hk) (by omega)
  · have hk : k * m 5 = 1 * m 5 := by linarith
    refine ⟨rfl, mul_right_cancel₀ (hpos 5).ne' hk, m 0, hpos 0, fun r => ?_⟩
    fin_cases r <;> simp <;> linarith
  · have hk : (7 * k) * m 6 = 4 * m 6 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 6).ne' hk) (by omega)

/-! ### Type E₈ -/

private lemma E8_rows (m : Fin 8 → ℤ) :
    ∑ s, DynkinShape.E8.weightedCartan 0 s * m s = 2 * m 0 - m 1 ∧
    ∑ s, DynkinShape.E8.weightedCartan 1 s * m s = 2 * m 1 - m 0 - m 2 ∧
    ∑ s, DynkinShape.E8.weightedCartan 2 s * m s = 2 * m 2 - m 1 - m 3 ∧
    ∑ s, DynkinShape.E8.weightedCartan 3 s * m s = 2 * m 3 - m 2 - m 4 ∧
    ∑ s, DynkinShape.E8.weightedCartan 4 s * m s = 2 * m 4 - m 3 - m 5 - m 7 ∧
    ∑ s, DynkinShape.E8.weightedCartan 5 s * m s = 2 * m 5 - m 4 - m 6 ∧
    ∑ s, DynkinShape.E8.weightedCartan 6 s * m s = 2 * m 6 - m 5 ∧
    ∑ s, DynkinShape.E8.weightedCartan 7 s * m s = 2 * m 7 - m 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Fin.sum_univ_succ, DynkinShape.weightedCartan, DynkinShape.Edge,
      DynkinShape.weightFactor] <;> ring

/-- The affine extension system solved over the diagram `E₈`: it has a solution only when the
attached component hangs at the far end of the long arm, where the level is one and the
multiplicities are `(2a, 3a, 4a, 5a, 6a, 4a, 2a, 3a)`. -/
public lemma affine_system_solved_E8 (m : Fin 8 → ℤ) (hpos : ∀ r, 0 < m r) (r₀ : Fin 8) (k : ℤ)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.E8.weightedCartan r s * m s = 0)
    (hmain : 2 * ∑ s, DynkinShape.E8.weightedCartan r₀ s * m s
      = k * DynkinShape.E8.weightFactor r₀ * m r₀) :
    r₀.val = 0 ∧ k = 1 ∧ ∃ a : ℤ, 0 < a ∧ ∀ r : Fin 8,
      m r = (if r.val = 0 ∨ r.val = 6 then 2 else if r.val = 1 ∨ r.val = 7 then 3
        else if r.val = 2 ∨ r.val = 5 then 4 else if r.val = 3 then 5 else 6) * a := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := E8_rows m
  have h0 := hrest 0
  have h1 := hrest 1
  have h2 := hrest 2
  have h3 := hrest 3
  have h4 := hrest 4
  have h5 := hrest 5
  have h6 := hrest 6
  have h7 := hrest 7
  have hwf : DynkinShape.E8.weightFactor r₀ = 1 := rfl
  rw [hwf, mul_one] at hmain
  have hcase : r₀ = 0 ∨ r₀ = 1 ∨ r₀ = 2 ∨ r₀ = 3 ∨ r₀ = 4 ∨ r₀ = 5 ∨ r₀ = 6 ∨ r₀ = 7 := by
    fin_cases r₀ <;> simp
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [e0, e1, e2, e3, e4, e5, e6, e7, ne_eq, Fin.reduceEq, not_false_eq_true, forall_const]
      at h0 h1 h2 h3 h4 h5 h6 h7 hmain
  · have hk : k * m 0 = 1 * m 0 := by linarith
    refine ⟨rfl, mul_right_cancel₀ (hpos 0).ne' hk, m 7 - m 6, by linarith [hpos 6],
      fun r => ?_⟩
    fin_cases r <;> simp <;> linarith
  · have hk : (3 * k) * m 1 = 1 * m 1 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 1).ne' hk) (by omega)
  · have hk : (6 * k) * m 2 = 1 * m 2 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 2).ne' hk) (by omega)
  · have hk : (10 * k) * m 3 = 1 * m 3 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 3).ne' hk) (by omega)
  · have hk : (15 * k) * m 4 = 1 * m 4 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 4).ne' hk) (by omega)
  · have hk : (7 * k) * m 5 = 1 * m 5 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 5).ne' hk) (by omega)
  · have hk : (2 * k) * m 6 = 1 * m 6 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 6).ne' hk) (by omega)
  · have hk : (4 * k) * m 7 = 1 * m 7 := by linarith
    exact absurd (mul_right_cancel₀ (hpos 7).ne' hk) (by omega)

end AlgebraicGeometry
