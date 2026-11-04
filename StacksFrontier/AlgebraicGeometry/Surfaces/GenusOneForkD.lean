module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneForkSystem

/-!
# The affine extension system over a diagram of type D

This file solves the affine extension system of
`AlgebraicGeometry.NumericalType.affine_system_of_erase_leaf` over a Dynkin diagram of type `D`
on `t ≥ 4` vertices: a main chain `0, …, t - 2` with one further vertex `t - 1` attached to
`t - 3`.

Away from the branch vertex a row of the weighted Cartan matrix is the three-term recurrence
`2 mⱼ = mⱼ₋₁ + mⱼ₊₁` of a chain, so the multiplicities along the main chain are an arithmetic
progression between the branch vertex and the attachment vertex. The two one-vertex arms at the
branch each carry half the multiplicity of the branch vertex, and feeding that into the row at
the branch vertex leaves a single Diophantine condition on the level `k`:

* at either of the two one-vertex arms, `k t = 8`, so `(k, t) = (2, 4)` or `(1, 8)`;
* at the branch vertex itself, `k (t - 2) = 2`, so `t = 4` and `k = 1`;
* on the long arm at distance `i` from its far end, `k i = 2`, so the attachment vertex is the
  first or the second one of the long arm, with `k = 2` and `k = 1` respectively.

## Main results

* `AlgebraicGeometry.affine_system_solved_D` — the four possibilities, with the multiplicity
  vector in each.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry

/-! ### Sequences satisfying the three-term recurrence -/

/-- A sequence vanishing at `0` and satisfying the three-term recurrence up to `n` is linear on
`[0, n]`. -/
private lemma recurrence_linear (M : ℕ → ℤ) (n : ℕ) (hM0 : M 0 = 0)
    (h : ∀ j, j + 2 ≤ n → 2 * M (j + 1) = M j + M (j + 2)) (j : ℕ) (hj : j ≤ n) :
    M j = j * M 1 := by
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases j <;> simp [hM0]
  · simpa [hM0] using recurrence_arith M 0 (n - 2) (fun i _ hi => h i (by omega)) j (by omega)

/-- A sequence satisfying the three-term recurrence on `[a, b]` whose last two values on
`[a, b + 2]` agree is constant on `[a, b + 2]`. -/
private lemma recurrence_const (M : ℕ → ℤ) (a b : ℕ) (hab : a ≤ b + 1)
    (h : ∀ j, a ≤ j → j ≤ b → 2 * M (j + 1) = M j + M (j + 2))
    (hflat : M (b + 2) = M (b + 1)) (j : ℕ) (hj₁ : a ≤ j) (hj₂ : j ≤ b + 2) : M j = M a := by
  have hd : M (a + 1) - M a = 0 := by
    have h₁ := recurrence_arith M a b h (b + 2 - a) (by omega)
    have h₂ := recurrence_arith M a b h (b + 1 - a) (by omega)
    rw [show a + (b + 2 - a) = b + 2 by omega, hflat,
      show ((b + 2 - a : ℕ) : ℤ) = ((b + 1 - a : ℕ) : ℤ) + 1 by omega] at h₁
    rw [show a + (b + 1 - a) = b + 1 by omega] at h₂
    linarith
  obtain ⟨p, rfl⟩ : ∃ p, j = a + p := ⟨j - a, by omega⟩
  rw [recurrence_arith M a b h p hj₂, hd]
  ring

/-- A sequence linear on `[0, t - 2]` takes the values `(t - 3) N 1` and `(t - 2) N 1` at
`t - 3` and `t - 2`. -/
private lemma linear_sub_three_sub_two {N : ℕ → ℤ} {t : ℕ} (ht : 4 ≤ t)
    (hlin : ∀ j, j ≤ t - 2 → N j = j * N 1) :
    N (t - 3) = ((t : ℤ) - 3) * N 1 ∧ N (t - 2) = ((t : ℤ) - 2) * N 1 := by
  constructor
  · rw [hlin (t - 3) (by omega)]
    congr 1
    omega
  · rw [hlin (t - 2) le_rfl]
    congr 1
    omega

/-! ### The rows of the weighted Cartan matrix of type `D` -/

/-- The edges of the diagram of type `D` on `t` vertices: the main chain `0, …, t - 2` and the
edge joining `t - 3` to `t - 1`. -/
private lemma DynkinShape.edge_D_iff {t : ℕ} (r s : Fin t) : DynkinShape.D.Edge r s ↔
    (((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < t - 1 ∧ s.val < t - 1) ∨
      (r.val = t - 3 ∧ s.val = t - 1) ∨ (s.val = t - 3 ∧ r.val = t - 1)) :=
  Iff.rfl

/-- Every vertex of the diagram of type `D` has weight factor `1`. -/
private lemma DynkinShape.weightFactor_D {t : ℕ} (r : Fin t) :
    DynkinShape.D.weightFactor r = 1 :=
  rfl

/-- The row of the weighted Cartan matrix of type `D` at the vertex `0`, in terms of the shifted
multiplicities `N`. -/
private lemma DynkinShape.sum_weightedCartan_D_zero {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ)
    {N : ℕ → ℤ} (hN0 : N 0 = 0) (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r)
    (r : Fin t) (h0 : r.val = 0) :
    ∑ s, DynkinShape.D.weightedCartan r s * m s = 2 * m r - N r.val - N (r.val + 2) := by
  obtain ⟨b, hb⟩ : ∃ b : Fin t, b.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hoth : ∀ s, DynkinShape.D.Edge r s → s = b := fun s hs =>
    Fin.ext (by have := (edge_D_iff r s).mp hs; omega)
  rw [DynkinShape.D.row_one ht m r b
      ((edge_D_iff r b).mpr (Or.inl ⟨Or.inl (by omega), by omega, by omega⟩)) hoth,
    weightFactor_D r, weightFactor_D b, h0, hN0, show (0 : ℕ) + 2 = b.val + 1 by omega,
    hNs b (by omega)]
  norm_num

/-- The row of the weighted Cartan matrix of type `D` at the far end `t - 2` of the main chain,
in terms of the shifted multiplicities `N`. -/
private lemma DynkinShape.sum_weightedCartan_D_end {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ)
    {N : ℕ → ℤ} (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r)
    (hNt : ∀ j, t ≤ j → N j = 0) (r : Fin t) (hr : r.val + 2 = t) :
    ∑ s, DynkinShape.D.weightedCartan r s * m s = 2 * m r - N r.val - N (r.val + 2) := by
  obtain ⟨b, hb⟩ : ∃ b : Fin t, b.val = t - 3 := ⟨⟨t - 3, by omega⟩, rfl⟩
  have hoth : ∀ s, DynkinShape.D.Edge r s → s = b := fun s hs =>
    Fin.ext (by have := (edge_D_iff r s).mp hs; omega)
  rw [DynkinShape.D.row_one ht m r b
      ((edge_D_iff r b).mpr (Or.inl ⟨Or.inr (by omega), by omega, by omega⟩)) hoth,
    weightFactor_D r, weightFactor_D b, hNt (r.val + 2) (by omega),
    (congrArg N (by omega : r.val = b.val + 1)).trans (hNs b (by omega))]
  norm_num

/-- The row of the weighted Cartan matrix of type `D` at an interior vertex of the main chain
away from the branch vertex, in terms of the shifted multiplicities `N`. -/
private lemma DynkinShape.sum_weightedCartan_D_interior {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ)
    {N : ℕ → ℤ} (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r)
    (r : Fin t) (h0 : 0 < r.val) (h4 : r.val + 4 ≤ t) :
    ∑ s, DynkinShape.D.weightedCartan r s * m s = 2 * m r - N r.val - N (r.val + 2) := by
  obtain ⟨p, hp⟩ : ∃ p : Fin t, p.val = r.val - 1 := ⟨⟨r.val - 1, by omega⟩, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin t, q.val = r.val + 1 := ⟨⟨r.val + 1, by omega⟩, rfl⟩
  have hoth : ∀ s, DynkinShape.D.Edge r s → s = p ∨ s = q := fun s hs => by
    have := (edge_D_iff r s).mp hs
    by_cases h : s.val = p.val
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext (by omega))
  rw [DynkinShape.D.row_two ht m r p q (fun h => by subst h; omega)
      ((edge_D_iff r p).mpr (Or.inl ⟨Or.inr (by omega), by omega, by omega⟩))
      ((edge_D_iff r q).mpr (Or.inl ⟨Or.inl (by omega), by omega, by omega⟩)) hoth,
    weightFactor_D r, weightFactor_D p, weightFactor_D q,
    (congrArg N (by omega : r.val = p.val + 1)).trans (hNs p (by omega)),
    (congrArg N (by omega : r.val + 2 = q.val + 1)).trans (hNs q (by omega))]
  norm_num

/-- The row of the weighted Cartan matrix of type `D` at a vertex of the main chain other than
the branch vertex, in terms of the shifted multiplicities `N`. -/
private lemma DynkinShape.sum_weightedCartan_D_chain {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ)
    {N : ℕ → ℤ} (hN0 : N 0 = 0) (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r)
    (hNt : ∀ j, t ≤ j → N j = 0) (r : Fin t) (h2 : r.val + 2 ≤ t) (h3 : r.val + 3 ≠ t) :
    ∑ s, DynkinShape.D.weightedCartan r s * m s = 2 * m r - N r.val - N (r.val + 2) := by
  rcases Nat.eq_zero_or_pos r.val with h0 | h0
  · exact sum_weightedCartan_D_zero ht m hN0 hNs r h0
  rcases eq_or_ne (r.val + 2) t with he | he
  · exact sum_weightedCartan_D_end ht m hNs hNt r he
  exact sum_weightedCartan_D_interior ht m hNs r h0 (by omega)

/-- The row of the weighted Cartan matrix of type `D` at the branch vertex `t - 3`, in terms of
the shifted multiplicities `N`. -/
private lemma DynkinShape.sum_weightedCartan_D_branch {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ)
    {N : ℕ → ℤ} (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r)
    (r b : Fin t) (hr : r.val + 3 = t) (hb : b.val + 1 = t) :
    ∑ s, DynkinShape.D.weightedCartan r s * m s
      = 2 * N (t - 2) - N (t - 3) - N (t - 1) - m b := by
  obtain ⟨p, hp⟩ : ∃ p : Fin t, p.val = t - 4 := ⟨⟨t - 4, by omega⟩, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin t, q.val = t - 2 := ⟨⟨t - 2, by omega⟩, rfl⟩
  have hoth : ∀ s, DynkinShape.D.Edge r s → s = p ∨ s = q ∨ s = b := fun s hs => by
    have := (edge_D_iff r s).mp hs
    by_cases h : s.val = p.val
    · exact Or.inl (Fin.ext h)
    by_cases h' : s.val = q.val
    · exact Or.inr (Or.inl (Fin.ext h'))
    exact Or.inr (Or.inr (Fin.ext (by omega)))
  rw [DynkinShape.D.row_three ht m r p q b (fun h => by subst h; omega)
      (fun h => by subst h; omega) (fun h => by subst h; omega)
      ((edge_D_iff r p).mpr (Or.inl ⟨Or.inr (by omega), by omega, by omega⟩))
      ((edge_D_iff r q).mpr (Or.inl ⟨Or.inl (by omega), by omega, by omega⟩))
      ((edge_D_iff r b).mpr (Or.inr (Or.inl ⟨by omega, by omega⟩))) hoth,
    weightFactor_D r, weightFactor_D p, weightFactor_D q, weightFactor_D b,
    (congrArg N (by omega : t - 2 = r.val + 1)).trans (hNs r (by omega)),
    (congrArg N (by omega : t - 3 = p.val + 1)).trans (hNs p (by omega)),
    (congrArg N (by omega : t - 1 = q.val + 1)).trans (hNs q (by omega))]
  norm_num

/-- The row of the weighted Cartan matrix of type `D` at the one-vertex arm `t - 1`, in terms of
the shifted multiplicities `N`. -/
private lemma DynkinShape.sum_weightedCartan_D_leaf {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ)
    {N : ℕ → ℤ} (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r)
    (r : Fin t) (hr : r.val + 1 = t) :
    ∑ s, DynkinShape.D.weightedCartan r s * m s = 2 * m r - N (t - 2) := by
  obtain ⟨p, hp⟩ : ∃ p : Fin t, p.val = t - 3 := ⟨⟨t - 3, by omega⟩, rfl⟩
  have hoth : ∀ s, DynkinShape.D.Edge r s → s = p := fun s hs =>
    Fin.ext (by have := (edge_D_iff r s).mp hs; omega)
  rw [DynkinShape.D.row_one ht m r p
      ((edge_D_iff r p).mpr (Or.inr (Or.inr ⟨by omega, by omega⟩))) hoth,
    weightFactor_D r, weightFactor_D p,
    (congrArg N (by omega : t - 2 = p.val + 1)).trans (hNs p (by omega))]
  norm_num

/-! ### The equations of the affine extension system -/

private lemma affine_system_D_recurrence {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ) (r₀ : Fin t)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * m s = 0) {N : ℕ → ℤ}
    (hN0 : N 0 = 0) (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r)
    (hNt : ∀ j, t ≤ j → N j = 0) (j : ℕ) (h₂ : j + 2 ≤ t) (h₃ : j + 3 ≠ t) (hj : j ≠ r₀.val) :
    2 * N (j + 1) = N j + N (j + 2) := by
  obtain ⟨r, rfl⟩ : ∃ r : Fin t, r.val = j := ⟨⟨j, by omega⟩, rfl⟩
  have h := (DynkinShape.sum_weightedCartan_D_chain ht m hN0 hNs hNt r h₂ h₃).symm.trans
    (hrest r fun hc => hj (congrArg Fin.val hc))
  rw [hNs r (by omega)]
  linarith

private lemma affine_system_D_end_eq {t : ℕ} (ht : 4 ≤ t) {N : ℕ → ℤ} {ρ : ℕ}
    (hrec : ∀ j, j + 2 ≤ t → j + 3 ≠ t → j ≠ ρ → 2 * N (j + 1) = N j + N (j + 2))
    (hNt : ∀ j, t ≤ j → N j = 0) (h : ρ + 2 ≠ t) : 2 * N (t - 1) = N (t - 2) := by
  have h' := hrec (t - 2) (by omega) (by omega) (by omega)
  rw [show t - 2 + 1 = t - 1 by omega, show t - 2 + 2 = t by omega, hNt t le_rfl] at h'
  linarith

private lemma affine_system_D_branch_eq {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ) (r₀ : Fin t)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * m s = 0) {N : ℕ → ℤ}
    (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r) (h : r₀.val + 3 ≠ t)
    (b : Fin t) (hb : b.val + 1 = t) :
    2 * N (t - 2) - N (t - 3) - N (t - 1) - m b = 0 := by
  obtain ⟨r, hr⟩ : ∃ r : Fin t, r.val = t - 3 := ⟨⟨t - 3, by omega⟩, rfl⟩
  exact (DynkinShape.sum_weightedCartan_D_branch ht m hNs r b (by omega) hb).symm.trans
    (hrest r (by rintro rfl; omega))

/-- The row at the one-vertex arm `v = t - 1` gives `2 m v = N (t - 2)` once `v` is not the
attachment vertex. -/
private lemma affine_system_D_leaf_eq {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ) (r₀ : Fin t)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * m s = 0) {N : ℕ → ℤ}
    (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r) (h : r₀.val + 1 ≠ t)
    (v : Fin t) (hv : v.val + 1 = t) : 2 * m v - N (t - 2) = 0 :=
  (DynkinShape.sum_weightedCartan_D_leaf ht m hNs v hv).symm.trans
    (hrest v (by rintro rfl; omega))

/-- If `N` is linear on `[0, t - 2]`, the multiplicity at `r` with `r + 3 ≤ t` is
`(r + 1) N 1`. -/
private lemma affine_system_D_mult_of_linear {t : ℕ} {m : Fin t → ℤ} {N : ℕ → ℤ}
    (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r)
    (hlin : ∀ j, j ≤ t - 2 → N j = j * N 1) (r : Fin t) (hr : r.val + 3 ≤ t) :
    m r = ((r.val : ℤ) + 1) * N 1 := by
  rw [← hNs r (by omega), hlin (r.val + 1) (by omega)]
  push_cast
  ring

/-! ### The four positions of the attachment vertex -/

/-- The affine extension system of type `D` with the attachment vertex at the one-vertex arm
`t - 1`. -/
private lemma affine_system_D_of_leaf {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ) (r₀ : Fin t) (k : ℤ)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * m s = 0)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * m s
      = k * DynkinShape.D.weightFactor r₀ * m r₀)
    {N : ℕ → ℤ} (hN0 : N 0 = 0) (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r)
    (hNt : ∀ j, t ≤ j → N j = 0) (hA : 0 < N 1) (hc : r₀.val + 1 = t) :
    ∃ a : ℤ, 0 < a ∧ r₀.val + 1 = t ∧ k * t = 8 ∧
      (∀ r : Fin t, r.val + 3 ≤ t → m r = ((r.val : ℤ) + 1) * a) ∧
      (∀ r : Fin t, r.val + 2 = t → 2 * m r = ((t : ℤ) - 2) * a) ∧
      (∀ r : Fin t, r.val + 1 = t → 2 * m r = (t : ℤ) * a) := by
  have hrec := affine_system_D_recurrence ht m r₀ hrest hN0 hNs hNt
  have hlin := recurrence_linear N (t - 2) hN0 fun i hi => hrec i (by omega) (by omega) (by omega)
  have hPN := affine_system_D_end_eq ht hrec hNt (by omega)
  have hbr := affine_system_D_branch_eq ht m r₀ hrest hNs (by omega) r₀ hc
  obtain ⟨h3, h2⟩ := linear_sub_three_sub_two ht hlin
  have hLval : 2 * m r₀ = (t : ℤ) * N 1 := by linarith
  rw [DynkinShape.sum_weightedCartan_D_leaf ht m hNs r₀ hc, DynkinShape.weightFactor_D r₀] at hmain
  have hkey : (8 : ℤ) * N 1 = (k * t) * N 1 := by
    linear_combination 2 * hmain + (k - 4) * hLval + 4 * h2
  refine ⟨N 1, hA, hc, mul_right_cancel₀ hA.ne' hkey.symm, fun r hr => ?_,
    fun r hr => ?_, fun r hr => ?_⟩
  · exact affine_system_D_mult_of_linear hNs hlin r (by omega)
  · rw [← hNs r (by omega), show r.val + 1 = t - 1 by omega]
    linarith
  · rw [show r = r₀ from Fin.ext (by omega)]
    exact hLval

/-- The affine extension system of type `D` with the attachment vertex at the far end `t - 2`
of the main chain. -/
private lemma affine_system_D_of_chain_end {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ) (r₀ : Fin t)
    (k : ℤ) (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * m s = 0)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * m s
      = k * DynkinShape.D.weightFactor r₀ * m r₀)
    {N : ℕ → ℤ} (hN0 : N 0 = 0) (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r)
    (hNt : ∀ j, t ≤ j → N j = 0) (hA : 0 < N 1) (hc : r₀.val + 2 = t) :
    ∃ a : ℤ, 0 < a ∧ r₀.val + 2 = t ∧ k * t = 8 ∧
      (∀ r : Fin t, r.val + 3 ≤ t → m r = ((r.val : ℤ) + 1) * a) ∧
      (∀ r : Fin t, r.val + 2 = t → 2 * m r = (t : ℤ) * a) ∧
      (∀ r : Fin t, r.val + 1 = t → 2 * m r = ((t : ℤ) - 2) * a) := by
  have hrec := affine_system_D_recurrence ht m r₀ hrest hN0 hNs hNt
  have hlin := recurrence_linear N (t - 2) hN0 fun i hi => hrec i (by omega) (by omega) (by omega)
  obtain ⟨vL, hvL⟩ : ∃ r : Fin t, r.val = t - 1 := ⟨⟨t - 1, by omega⟩, rfl⟩
  have hlf := affine_system_D_leaf_eq ht m r₀ hrest hNs (by omega) vL (by omega)
  have hbr := affine_system_D_branch_eq ht m r₀ hrest hNs (by omega) vL (by omega)
  obtain ⟨h3, h2⟩ := linear_sub_three_sub_two ht hlin
  have hPval : 2 * N (t - 1) = (t : ℤ) * N 1 := by linarith
  rw [DynkinShape.sum_weightedCartan_D_end ht m hNs hNt r₀ hc, DynkinShape.weightFactor_D r₀,
    ← (congrArg N (by omega : t - 1 = r₀.val + 1)).trans (hNs r₀ (by omega)),
    congrArg N (by omega : r₀.val = t - 2), hNt (r₀.val + 2) (by omega)] at hmain
  have hkey : (8 : ℤ) * N 1 = (k * t) * N 1 := by
    linear_combination 2 * hmain + (k - 4) * hPval + 4 * h2
  refine ⟨N 1, hA, hc, mul_right_cancel₀ hA.ne' hkey.symm, fun r hr => ?_,
    fun r hr => ?_, fun r hr => ?_⟩
  · exact affine_system_D_mult_of_linear hNs hlin r (by omega)
  · rw [← hNs r (by omega), show r.val + 1 = t - 1 by omega]
    exact hPval
  · rw [show r = vL from Fin.ext (by omega)]
    linarith

/-- The affine extension system of type `D` with the attachment vertex at the branch vertex
`t - 3`. -/
private lemma affine_system_D_of_branch {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ) (r₀ : Fin t)
    (k : ℤ) (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * m s = 0)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * m s
      = k * DynkinShape.D.weightFactor r₀ * m r₀)
    {N : ℕ → ℤ} (hN0 : N 0 = 0) (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r)
    (hNt : ∀ j, t ≤ j → N j = 0) (hA : 0 < N 1) (hc : r₀.val + 3 = t) :
    ∃ a : ℤ, 0 < a ∧ r₀.val = 1 ∧ k = 1 ∧ (∀ r : Fin t, r.val = 0 → m r = a) ∧
      (∀ r : Fin t, 1 ≤ r.val → r.val + 3 ≤ t → m r = 2 * a) ∧
      (∀ r : Fin t, t ≤ r.val + 2 → m r = a) := by
  have hrec := affine_system_D_recurrence ht m r₀ hrest hN0 hNs hNt
  have hlin := recurrence_linear N (t - 2) hN0 fun i hi => hrec i (by omega) (by omega) (by omega)
  have hPN := affine_system_D_end_eq ht hrec hNt (by omega)
  obtain ⟨vL, hvL⟩ : ∃ r : Fin t, r.val = t - 1 := ⟨⟨t - 1, by omega⟩, rfl⟩
  have hlf := affine_system_D_leaf_eq ht m r₀ hrest hNs (by omega) vL (by omega)
  obtain ⟨h3, h2⟩ := linear_sub_three_sub_two ht hlin
  rw [DynkinShape.sum_weightedCartan_D_branch ht m hNs r₀ vL hc (by omega),
    DynkinShape.weightFactor_D r₀,
    ← (congrArg N (by omega : t - 2 = r₀.val + 1)).trans (hNs r₀ (by omega))] at hmain
  have hkey : (2 : ℤ) * N 1 = (k * ((t : ℤ) - 2)) * N 1 := by
    linear_combination hmain + hPN + hlf + 2 * h3 + (k - 2) * h2
  have hki := mul_right_cancel₀ hA.ne' hkey
  have hle := Int.le_of_dvd (by norm_num) (⟨k, by linarith⟩ : ((t : ℤ) - 2) ∣ 2)
  have ht4 : t = 4 := by omega
  have h2' : N (t - 2) = 2 * N 1 := by
    rw [h2, ht4]
    norm_num
  refine ⟨N 1, hA, by omega, ?_, fun r hr => ?_, fun r hr₁ hr₂ => ?_, fun r hr => ?_⟩
  · rw [ht4] at hki
    omega
  · simpa [hr] using (hNs r (by omega)).symm
  · rw [affine_system_D_mult_of_linear hNs hlin r (by omega), show (r.val : ℤ) = 1 by omega]
    ring
  · rcases (show r.val + 1 = t ∨ r.val + 2 = t by omega) with h | h
    · rw [show r = vL from Fin.ext (by omega)]
      linarith
    · rw [← hNs r (by omega), show r.val + 1 = t - 1 by omega]
      linarith

/-- With the attachment vertex `ρ` on the long arm away from the branch vertex, `k (ρ + 1) = 2`,
the multiplicities are constant from `ρ` up to the branch vertex, and the two one-vertex arms
carry half of that constant. -/
private lemma affine_system_D_long_arm_shape {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ) (r₀ : Fin t)
    (k : ℤ) (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * m s = 0)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * m s
      = k * DynkinShape.D.weightFactor r₀ * m r₀)
    {N : ℕ → ℤ} (hN0 : N 0 = 0) (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r)
    (hNt : ∀ j, t ≤ j → N j = 0) (hA : 0 < N 1) (hc : r₀.val + 4 ≤ t) :
    k * ((r₀.val : ℤ) + 1) = 2 ∧
      (∀ r : Fin t, r₀.val ≤ r.val → r.val + 3 ≤ t → m r = ((r₀.val : ℤ) + 1) * N 1) ∧
      (∀ r : Fin t, t ≤ r.val + 2 → 2 * m r = ((r₀.val : ℤ) + 1) * N 1) := by
  have hrec := affine_system_D_recurrence ht m r₀ hrest hN0 hNs hNt
  have hleft := recurrence_linear N (r₀.val + 1) hN0
    fun i hi => hrec i (by omega) (by omega) (by omega)
  have hPN := affine_system_D_end_eq ht hrec hNt (by omega)
  obtain ⟨vL, hvL⟩ : ∃ r : Fin t, r.val = t - 1 := ⟨⟨t - 1, by omega⟩, rfl⟩
  have hlf := affine_system_D_leaf_eq ht m r₀ hrest hNs (by omega) vL (by omega)
  have hbr := affine_system_D_branch_eq ht m r₀ hrest hNs (by omega) vL (by omega)
  have hconst := recurrence_const N (r₀.val + 1) (t - 4) (by omega)
    (fun i _ _ => hrec i (by omega) (by omega) (by omega)) (by
      rw [show t - 4 + 2 = t - 2 by omega, show t - 4 + 1 = t - 3 by omega]
      linarith)
  have hc' : ∀ j, r₀.val + 1 ≤ j → j ≤ t - 2 → N j = ((r₀.val : ℤ) + 1) * N 1 :=
    fun j h₁ h₂ => by
      rw [hconst j h₁ (by omega), hleft _ le_rfl]
      push_cast
      ring
  rw [DynkinShape.sum_weightedCartan_D_chain ht m hN0 hNs hNt r₀ (by omega) (by omega),
    DynkinShape.weightFactor_D r₀, ← hNs r₀ (by omega),
    hconst (r₀.val + 2) (by omega) (by omega), hleft r₀.val (by omega),
    hleft (r₀.val + 1) le_rfl] at hmain
  -- `2 = k (ρ + 1)`
  have hkey : (2 : ℤ) * N 1 = (k * ((r₀.val : ℤ) + 1)) * N 1 := by
    push_cast at hmain
    linear_combination hmain
  refine ⟨(mul_right_cancel₀ hA.ne' hkey).symm, fun r hr₁ hr₂ => ?_, fun r hr => ?_⟩
  · rw [← hNs r (by omega)]
    exact hc' _ (by omega) (by omega)
  · rcases (show r.val + 1 = t ∨ r.val + 2 = t by omega) with h | h
    · rw [show r = vL from Fin.ext (by omega)]
      linarith [hc' (t - 2) (by omega) le_rfl]
    · rw [← hNs r (by omega), show r.val + 1 = t - 1 by omega]
      linarith [hc' (t - 2) (by omega) le_rfl]

/-- The affine extension system of type `D` with the attachment vertex on the long arm away
from the branch vertex: it is the first or the second vertex of the long arm. -/
private lemma affine_system_D_of_long_arm {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ)
    (hpos : ∀ r, 0 < m r) (r₀ : Fin t) (k : ℤ)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * m s = 0)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * m s
      = k * DynkinShape.D.weightFactor r₀ * m r₀)
    {N : ℕ → ℤ} (hN0 : N 0 = 0) (hNs : ∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r)
    (hNt : ∀ j, t ≤ j → N j = 0) (hA : 0 < N 1) (hc : r₀.val + 4 ≤ t) :
    ∃ a : ℤ, 0 < a ∧
      ((r₀.val = 0 ∧ k = 2 ∧ (∀ r : Fin t, r.val + 3 ≤ t → m r = 2 * a) ∧
          (∀ r : Fin t, t ≤ r.val + 2 → m r = a)) ∨
       (r₀.val = 1 ∧ k = 1 ∧ (∀ r : Fin t, r.val = 0 → m r = a) ∧
          (∀ r : Fin t, 1 ≤ r.val → r.val + 3 ≤ t → m r = 2 * a) ∧
          (∀ r : Fin t, t ≤ r.val + 2 → m r = a))) := by
  obtain ⟨hk, hconst, htop⟩ :=
    affine_system_D_long_arm_shape ht m r₀ k hrest hmain hN0 hNs hNt hA hc
  have hle := Int.le_of_dvd (by norm_num) (⟨k, by linarith⟩ : ((r₀.val : ℤ) + 1) ∣ 2)
  obtain ⟨vL, hvL⟩ : ∃ r : Fin t, r.val = t - 1 := ⟨⟨t - 1, by omega⟩, rfl⟩
  rcases (show r₀.val = 0 ∨ r₀.val = 1 by omega) with h0 | h1
  · -- the first vertex of the long arm
    refine ⟨m vL, hpos _, Or.inl ⟨h0, ?_, fun r hr => ?_, fun r hr => ?_⟩⟩
    · rw [show (r₀.val : ℤ) = 0 by exact_mod_cast h0] at hk
      linarith
    · linarith [hconst r (by omega) hr, htop vL (by omega)]
    · linarith [htop r hr, htop vL (by omega)]
  · -- the second vertex of the long arm
    rw [show (r₀.val : ℤ) = 1 by exact_mod_cast h1] at hk hconst htop
    refine ⟨N 1, hA, Or.inr ⟨h1, by linarith, fun r hr => ?_, fun r hr₁ hr₂ => ?_,
      fun r hr => ?_⟩⟩
    · simpa [hr] using (hNs r (by omega)).symm
    · linarith [hconst r (by omega) hr₂]
    · linarith [htop r hr]

/-- **The affine extension system solved over a diagram of type `D`.** The attachment vertex is
the first or the second vertex of the long arm, or one of the two one-vertex arms; in the first
two cases the level is `2` and `1` and the multiplicities are `(2a, …, 2a, a, a)` and
`(a, 2a, …, 2a, a, a)`, in the last two `k t = 8` and the multiplicities rise linearly along the
long arm, halving onto the two short arms. -/
public lemma affine_system_solved_D {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ) (hpos : ∀ r, 0 < m r)
    (r₀ : Fin t) (k : ℤ)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * m s = 0)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * m s
      = k * DynkinShape.D.weightFactor r₀ * m r₀) :
    ∃ a : ℤ, 0 < a ∧
      ((r₀.val = 0 ∧ k = 2 ∧ (∀ r : Fin t, r.val + 3 ≤ t → m r = 2 * a) ∧
          (∀ r : Fin t, t ≤ r.val + 2 → m r = a)) ∨
       (r₀.val = 1 ∧ k = 1 ∧ (∀ r : Fin t, r.val = 0 → m r = a) ∧
          (∀ r : Fin t, 1 ≤ r.val → r.val + 3 ≤ t → m r = 2 * a) ∧
          (∀ r : Fin t, t ≤ r.val + 2 → m r = a)) ∨
       (r₀.val + 1 = t ∧ k * t = 8 ∧
          (∀ r : Fin t, r.val + 3 ≤ t → m r = ((r.val : ℤ) + 1) * a) ∧
          (∀ r : Fin t, r.val + 2 = t → 2 * m r = ((t : ℤ) - 2) * a) ∧
          (∀ r : Fin t, r.val + 1 = t → 2 * m r = (t : ℤ) * a)) ∨
       (r₀.val + 2 = t ∧ k * t = 8 ∧
          (∀ r : Fin t, r.val + 3 ≤ t → m r = ((r.val : ℤ) + 1) * a) ∧
          (∀ r : Fin t, r.val + 2 = t → 2 * m r = (t : ℤ) * a) ∧
          (∀ r : Fin t, r.val + 1 = t → 2 * m r = ((t : ℤ) - 2) * a))) := by
  -- the multiplicities along the main chain, as a sequence on `ℕ` shifted by one
  obtain ⟨N, hN0, hNs, hNt⟩ : ∃ N : ℕ → ℤ, N 0 = 0 ∧
      (∀ r : Fin t, r.val + 2 ≤ t → N (r.val + 1) = m r) ∧ (∀ j, t ≤ j → N j = 0) := by
    refine ⟨shiftExtend (fun j : Fin (t - 1) => m ⟨j.val, by have := j.isLt; omega⟩),
      shiftExtend_zero _, fun r hr => ?_, fun j hj => shiftExtend_of_le _ (by omega)⟩
    exact shiftExtend_succ (fun j : Fin (t - 1) => m ⟨j.val, by have := j.isLt; omega⟩)
      ⟨r.val, by omega⟩
  obtain ⟨v0, hv0⟩ : ∃ r : Fin t, r.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  have hA : 0 < N 1 := by
    have h := hNs v0 (by omega)
    rw [hv0, zero_add] at h
    rw [h]
    exact hpos v0
  by_cases hcA : r₀.val + 1 = t
  · -- at the one-vertex arm hanging off the branch vertex
    obtain ⟨a, ha, h⟩ := affine_system_D_of_leaf ht m r₀ k hrest hmain hN0 hNs hNt hA hcA
    exact ⟨a, ha, Or.inr (Or.inr (Or.inl h))⟩
  by_cases hcD : r₀.val + 2 = t
  · -- at the far end of the main chain
    obtain ⟨a, ha, h⟩ := affine_system_D_of_chain_end ht m r₀ k hrest hmain hN0 hNs hNt hA hcD
    exact ⟨a, ha, Or.inr (Or.inr (Or.inr h))⟩
  by_cases hcB : r₀.val + 3 = t
  · -- at the branch vertex itself
    obtain ⟨a, ha, h⟩ := affine_system_D_of_branch ht m r₀ k hrest hmain hN0 hNs hNt hA hcB
    exact ⟨a, ha, Or.inr (Or.inl h)⟩
  -- on the long arm, away from the branch vertex
  obtain ⟨a, ha, h | h⟩ :=
    affine_system_D_of_long_arm ht m hpos r₀ k hrest hmain hN0 hNs hNt hA (by omega)
  · exact ⟨a, ha, Or.inl h⟩
  · exact ⟨a, ha, Or.inr (Or.inl h)⟩

end AlgebraicGeometry
