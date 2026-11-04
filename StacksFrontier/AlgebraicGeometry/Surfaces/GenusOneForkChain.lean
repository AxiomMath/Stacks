module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneForkSystem

/-!
# The affine extension system over a chain diagram

The affine extension system of
`AlgebraicGeometry.NumericalType.affine_system_of_erase_leaf` asks for a positive vector `m` on
the vertices of a Dynkin shape `d` annihilated by the weighted Cartan matrix of `d` away from a
single vertex `r₀`, where instead `2 (M m)_{r₀} = k · wf(r₀) · m_{r₀}` for some `k ∈ {1, 2, 3}`.
This file solves that system over the five chain-shaped diagrams `A`, `B`, `C`, `F₄` and `G₂`,
at an *interior* vertex `r₀` — the case in which the resulting numerical type has a component
meeting three others, namely `r₀` itself.

Along a chain the row of the weighted Cartan matrix at the `j`-th vertex is a three-term
recurrence in the multiplicities at `j - 1`, `j` and `j + 1`, so the multiplicities are an
arithmetic progression on each side of `r₀`; matching the two progressions at `r₀` and reading
off the inhomogeneous equation there leaves a single Diophantine condition on `k` and the
position of `r₀`.

* In type `A` that condition is `k · i · (N - i) = 2 N` for `N = t + 1` the number of
  components and `i = r₀ + 1` the position of `r₀`, whose only solutions with `N ≥ 5` are
  `(N, i) = (8, 4)` and `(N, i) = (9, 3)`, `(9, 6)`, all with `k = 1`.
* In types `B` and `C` the weight at the far end of the chain makes the progression on that
  side constant, and the condition becomes `k · i = 2`, so `r₀` is the second vertex and
  `k = 1`.
* In type `F₄` there is no solution at either interior vertex, and type `G₂` has no interior
  vertex at all.

## Main results

* `AlgebraicGeometry.DynkinShape.row_chain` — a row of the weighted Cartan matrix of a
  chain-shaped diagram.
* `AlgebraicGeometry.affine_system_solved_A`, `affine_system_solved_B`,
  `affine_system_solved_C` — the system solved over a chain of type `A`, `B` and `C`.
* `AlgebraicGeometry.not_affine_system_F4` — the system has no solution over `F₄` at an
  interior vertex.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry

/-! ### Rows of a chain diagram -/

/-- The shifted extension at `n` is the entry at any vertex `r` with `r + 1 = n`. -/
private lemma shiftExtend_of_val_succ_eq {t : ℕ} (m : Fin t → ℤ) {r : Fin t} {n : ℕ}
    (h : r.val + 1 = n) : shiftExtend m n = m r := by
  rw [← h, shiftExtend_succ]

/-- A row of the weighted Cartan matrix at a vertex of a chain-shaped diagram, read through the
shifted extension of the vector: the two neighbours of the `j`-th vertex sit at `j` and `j + 2`,
and the extension by zero makes the formula hold at the two ends of the chain as well, whatever
the coefficients `cm` and `cp` are taken to be there. -/
public lemma DynkinShape.row_chain {t : ℕ} (d : DynkinShape) (ht : d.Allows t) (ht2 : 2 ≤ t)
    (hchain : ∀ r s : Fin t, d.Edge r s ↔ (r.val + 1 = s.val ∨ s.val + 1 = r.val))
    (m : Fin t → ℤ) (r : Fin t) (cm cp : ℤ)
    (hcm : ∀ s : Fin t, s.val + 1 = r.val → max (d.weightFactor r) (d.weightFactor s) = cm)
    (hcp : ∀ s : Fin t, r.val + 1 = s.val → max (d.weightFactor r) (d.weightFactor s) = cp) :
    ∑ s, d.weightedCartan r s * m s
      = 2 * d.weightFactor r * m r - cm * shiftExtend m r.val
        - cp * shiftExtend m (r.val + 2) := by
  have hr := r.isLt
  by_cases h0 : 0 < r.val
  · obtain ⟨a, ha'⟩ : ∃ a : Fin t, a.val + 1 = r.val :=
      ⟨⟨r.val - 1, by omega⟩, Nat.sub_add_cancel h0⟩
    have ha : d.Edge r a := (hchain r a).mpr (Or.inr ha')
    have e1 : shiftExtend m r.val = m a := shiftExtend_of_val_succ_eq m ha'
    by_cases h1 : r.val + 1 < t
    · obtain ⟨b, hb'⟩ : ∃ b : Fin t, r.val + 1 = b.val := ⟨⟨r.val + 1, by omega⟩, rfl⟩
      have hab : a ≠ b := fun h => by rw [h] at ha'; omega
      have hb : d.Edge r b := (hchain r b).mpr (Or.inl hb')
      have e2 : shiftExtend m (r.val + 2) = m b := by
        rw [show r.val + 2 = b.val + 1 by omega, shiftExtend_succ]
      rw [e1, e2, d.row_two ht m r a b hab ha hb (fun s hs => by
        rcases (hchain r s).mp hs with h | h
        · exact Or.inr (Fin.ext (by omega))
        · exact Or.inl (Fin.ext (by omega))), hcm a ha', hcp b hb']
    · have e2 : shiftExtend m (r.val + 2) = 0 := shiftExtend_of_le m (by omega)
      rw [e1, e2, d.row_one ht m r a ha (fun s hs => by
        rcases (hchain r s).mp hs with h | h
        · exact absurd (s.isLt) (by omega)
        · exact Fin.ext (by omega)), hcm a ha']
      ring
  · obtain ⟨b, hb'⟩ : ∃ b : Fin t, r.val + 1 = b.val := ⟨⟨r.val + 1, by omega⟩, rfl⟩
    have hb : d.Edge r b := (hchain r b).mpr (Or.inl hb')
    have e1 : shiftExtend m r.val = 0 := by
      rw [show r.val = 0 by omega, shiftExtend_zero]
    have e2 : shiftExtend m (r.val + 2) = m b := by
      rw [show r.val + 2 = b.val + 1 by omega, shiftExtend_succ]
    rw [e1, e2, d.row_one ht m r b hb (fun s hs => by
      rcases (hchain r s).mp hs with h | h
      · exact Fin.ext (by omega)
      · exact absurd h (by omega)), hcp b hb']
    ring

/-! ### Progressions along a chain -/

/-- The first entry of the shifted extension of a positive vector is positive. -/
private lemma shiftExtend_one_pos {t : ℕ} (m : Fin t → ℤ) (hpos : ∀ r, 0 < m r) (ht : 0 < t) :
    0 < shiftExtend m 1 := by
  rw [shiftExtend_of_val_succ_eq m (r := ⟨0, ht⟩) rfl]
  exact hpos _

/-- If the three-term recurrence holds below `n`, the shifted extension is linear on
`[0, n + 1]`. -/
private lemma shiftExtend_eq_mul_of_rec {t : ℕ} (m : Fin t → ℤ) (n : ℕ)
    (hrec : ∀ j, j < n →
      2 * shiftExtend m (j + 1) = shiftExtend m j + shiftExtend m (j + 2)) :
    ∀ j, j ≤ n + 1 → shiftExtend m j = (j : ℤ) * shiftExtend m 1 := by
  intro j hj
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · interval_cases j <;> simp
  · simpa using recurrence_arith (shiftExtend m) 0 (n - 1)
      (fun i _ hib => hrec i (by omega)) j (by omega)

/-- If the three-term recurrence holds on `[n + 1, b]`, the shifted extension is an arithmetic
progression on `[n + 1, b + 2]`. -/
private lemma shiftExtend_progression {t : ℕ} (m : Fin t → ℤ) (n b : ℕ)
    (hrec : ∀ j, n + 1 ≤ j → j ≤ b →
      2 * shiftExtend m (j + 1) = shiftExtend m j + shiftExtend m (j + 2)) :
    ∀ p, n + 1 + p ≤ b + 2 → shiftExtend m (n + 1 + p) = shiftExtend m (n + 1)
      + (p : ℤ) * (shiftExtend m (n + 2) - shiftExtend m (n + 1)) := by
  intro p hp
  simpa using recurrence_arith (shiftExtend m) (n + 1) b hrec p hp

/-- If the recurrence holds on `[n + 1, E - 2]` and the last two entries up to `E` agree, the
shifted extension is constant on `[n + 1, E]`. -/
private lemma shiftExtend_const_of_rec {t : ℕ} (m : Fin t → ℤ) (n E : ℕ) (hE : n + 2 ≤ E)
    (hrec : ∀ j, n + 1 ≤ j → j + 2 ≤ E →
      2 * shiftExtend m (j + 1) = shiftExtend m j + shiftExtend m (j + 2))
    (hend : shiftExtend m E = shiftExtend m (E - 1)) :
    ∀ j, n + 1 ≤ j → j ≤ E → shiftExtend m j = shiftExtend m (n + 1) := by
  have hright := shiftExtend_progression m n (E - 2) (fun i hia hib => hrec i hia (by omega))
  have hD : shiftExtend m (n + 2) - shiftExtend m (n + 1) = 0 := by
    have h1 := hright (E - (n + 1)) (by omega)
    have h2 := hright (E - 1 - (n + 1)) (by omega)
    rw [show n + 1 + (E - (n + 1)) = E by omega,
      show ((E - (n + 1) : ℕ) : ℤ) = ((E - 1 - (n + 1) : ℕ) : ℤ) + 1 by omega] at h1
    rw [show n + 1 + (E - 1 - (n + 1)) = E - 1 by omega] at h2
    rw [hend, h2] at h1
    linarith
  intro j h1 h2
  have h := hright (j - (n + 1)) (by omega)
  rw [show n + 1 + (j - (n + 1)) = j by omega] at h
  rw [h, hD]
  ring

/-- A product equal to `2` bounds the second factor by `2`. -/
private lemma le_two_of_two_eq_mul {k c : ℤ} (h : 2 = k * c) : c ≤ 2 :=
  Int.le_of_dvd (by norm_num) ⟨k, by linarith⟩

/-! ### Type A -/

/-- The affine extension system solved over a chain of type `A`. Writing `N = t + 1` for the
number of components of the resulting numerical type and `i = r₀ + 1` for the position of the
attachment vertex, the level `k` satisfies `k · i · (N - i) = 2 N`, and the multiplicities rise
linearly from each end of the chain to the attachment vertex. -/
public lemma affine_system_solved_A {t : ℕ} (ht : 2 ≤ t) (m : Fin t → ℤ) (hpos : ∀ r, 0 < m r)
    (r₀ : Fin t) (k : ℤ)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.A.weightedCartan r s * m s = 0)
    (hmain : 2 * ∑ s, DynkinShape.A.weightedCartan r₀ s * m s
      = k * DynkinShape.A.weightFactor r₀ * m r₀) :
    k * ((r₀.val : ℤ) + 1) * ((t : ℤ) - r₀.val) = 2 * ((t : ℤ) + 1) ∧
      ∃ a b : ℤ, 0 < a ∧ 0 < b ∧
        (∀ r : Fin t, r.val ≤ r₀.val → m r = ((r.val : ℤ) + 1) * a) ∧
        (∀ r : Fin t, r₀.val ≤ r.val → m r = ((t : ℤ) - r.val) * b) := by
  have hr₀ := r₀.isLt
  have hwf : ∀ r : Fin t, DynkinShape.A.weightFactor r = 1 := fun _ => rfl
  have hchain : ∀ r s : Fin t,
      DynkinShape.A.Edge r s ↔ (r.val + 1 = s.val ∨ s.val + 1 = r.val) := fun _ _ => Iff.rfl
  have hrow : ∀ r : Fin t, ∑ s, DynkinShape.A.weightedCartan r s * m s
      = 2 * m r - shiftExtend m r.val - shiftExtend m (r.val + 2) := by
    intro r
    rw [DynkinShape.A.row_chain ht ht hchain m r 1 1 (fun s _ => by simp [hwf])
      (fun s _ => by simp [hwf]), hwf r]
    ring
  -- the recurrence away from the attachment vertex
  have hrec : ∀ j, j < t → j ≠ r₀.val →
      2 * shiftExtend m (j + 1) = shiftExtend m j + shiftExtend m (j + 2) := by
    intro j hj hne
    have hne' : (⟨j, hj⟩ : Fin t) ≠ r₀ := fun h => hne (congrArg Fin.val h)
    have h := (hrow ⟨j, hj⟩).symm.trans (hrest ⟨j, hj⟩ hne')
    dsimp only at h
    rw [shiftExtend_of_val_succ_eq m (r := ⟨j, hj⟩) rfl]
    linarith
  -- the progression on the near side
  have hleft := shiftExtend_eq_mul_of_rec m r₀.val (fun j hj => hrec j (by omega) (by omega))
  have ha1 := shiftExtend_one_pos m hpos (by omega)
  -- the progression on the far side
  have hright := shiftExtend_progression m r₀.val (t - 1)
    (fun i hia hib => hrec i (by omega) (by omega))
  have hend := hright (t - r₀.val) (by omega)
  rw [show r₀.val + 1 + (t - r₀.val) = t + 1 by omega, shiftExtend_of_le m le_rfl,
    show ((t - r₀.val : ℕ) : ℤ) = (t : ℤ) - r₀.val by omega] at hend
  have hMi : shiftExtend m (r₀.val + 1) = ((r₀.val : ℤ) + 1) * shiftExtend m 1 := by
    rw [hleft (r₀.val + 1) le_rfl]
    push_cast
    ring
  have hqpos : (0 : ℤ) < (t : ℤ) - r₀.val := by omega
  have hipos : (0 : ℤ) < (r₀.val : ℤ) + 1 := by positivity
  have hbpos : 0 < -(shiftExtend m (r₀.val + 2) - shiftExtend m (r₀.val + 1)) := by
    nlinarith [hend, hMi, ha1, hqpos, hipos]
  have hmr : m r₀ = shiftExtend m (r₀.val + 1) := (shiftExtend_succ m r₀).symm
  have hprev : shiftExtend m r₀.val
      = ((r₀.val : ℤ) + 1) * shiftExtend m 1 - shiftExtend m 1 := by
    rcases Nat.eq_zero_or_pos r₀.val with h0 | h0
    · rw [h0]
      simp
    · rw [hleft r₀.val (by omega)]
      ring
  rw [hrow r₀, hwf r₀] at hmain
  refine ⟨?_, shiftExtend m 1, -(shiftExtend m (r₀.val + 2) - shiftExtend m (r₀.val + 1)),
    ha1, hbpos, ?_, ?_⟩
  · -- the Diophantine condition at the attachment vertex
    have hD : ((t : ℤ) - r₀.val)
        * (shiftExtend m (r₀.val + 2) - shiftExtend m (r₀.val + 1))
        = -(((r₀.val : ℤ) + 1) * shiftExtend m 1) := by
      linear_combination -hend - hMi
    have hE : 2 * (shiftExtend m 1
          - (shiftExtend m (r₀.val + 2) - shiftExtend m (r₀.val + 1)))
        = k * (((r₀.val : ℤ) + 1) * shiftExtend m 1) := by
      linear_combination hmain + (k - 4) * hmr + 2 * hprev + (k - 2) * hMi
    have hfin : 2 * (((r₀.val : ℤ) + 1) + ((t : ℤ) - r₀.val)) * shiftExtend m 1
        = (k * ((r₀.val : ℤ) + 1) * ((t : ℤ) - r₀.val)) * shiftExtend m 1 := by
      linear_combination ((t : ℤ) - r₀.val) * hE + 2 * hD
    linarith [mul_right_cancel₀ ha1.ne' hfin]
  · intro r hrle
    rw [← shiftExtend_succ m r, hleft (r.val + 1) (by omega)]
    push_cast
    ring
  · intro r hrge
    have hrt := r.isLt
    have h := hright (r.val - r₀.val) (by omega)
    rw [show r₀.val + 1 + (r.val - r₀.val) = r.val + 1 by omega] at h
    rw [← shiftExtend_succ m r, h,
      show ((r.val - r₀.val : ℕ) : ℤ) = (r.val : ℤ) - r₀.val by omega]
    linear_combination -hend

/-! ### Type B -/

/-- The affine extension system solved over a chain of type `B` at an interior vertex. The
weight at the far end makes the multiplicities constant from the attachment vertex onwards, and
the inhomogeneous equation there forces the attachment vertex to be the second one and the level
to be one: the multiplicities are `(a, 2a, …, 2a)`. -/
public lemma affine_system_solved_B {t : ℕ} (ht : 2 ≤ t) (m : Fin t → ℤ) (hpos : ∀ r, 0 < m r)
    (r₀ : Fin t) (k : ℤ) (hlo : 1 ≤ r₀.val) (hhi : r₀.val + 2 ≤ t)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.B.weightedCartan r s * m s = 0)
    (hmain : 2 * ∑ s, DynkinShape.B.weightedCartan r₀ s * m s
      = k * DynkinShape.B.weightFactor r₀ * m r₀) :
    r₀.val = 1 ∧ k = 1 ∧ ∃ a : ℤ, 0 < a ∧
      (∀ r : Fin t, r.val = 0 → m r = a) ∧ (∀ r : Fin t, 1 ≤ r.val → m r = 2 * a) := by
  have hr₀ := r₀.isLt
  have hwf : ∀ r : Fin t, DynkinShape.B.weightFactor r = if r.val + 1 = t then 1 else 2 :=
    fun _ => rfl
  have hwfle : ∀ r : Fin t, DynkinShape.B.weightFactor r ≤ 2 := by
    intro r
    rw [hwf]
    split_ifs <;> norm_num
  have hrow : ∀ r : Fin t, ∑ s, DynkinShape.B.weightedCartan r s * m s
      = 2 * DynkinShape.B.weightFactor r * m r - 2 * shiftExtend m r.val
        - 2 * shiftExtend m (r.val + 2) := by
    intro r
    refine DynkinShape.B.row_chain ht ht (fun _ _ => Iff.rfl) m r 2 2 (fun s hs => ?_)
      (fun s hs => ?_)
    · have := r.isLt
      rw [show DynkinShape.B.weightFactor s = 2 by rw [hwf, if_neg (by omega)]]
      exact max_eq_right (hwfle r)
    · have := s.isLt
      rw [show DynkinShape.B.weightFactor r = 2 by rw [hwf, if_neg (by omega)]]
      exact max_eq_left (hwfle s)
  have hrec : ∀ j, j + 1 < t → j ≠ r₀.val →
      2 * shiftExtend m (j + 1) = shiftExtend m j + shiftExtend m (j + 2) := by
    intro j hj hne
    obtain ⟨r, hrv⟩ : ∃ r : Fin t, r.val = j := ⟨⟨j, by omega⟩, rfl⟩
    have h := (hrow r).symm.trans (hrest r (fun hc => hne (by rw [← hrv, hc])))
    rw [hrv, show DynkinShape.B.weightFactor r = 2 by rw [hwf, if_neg (by omega)]] at h
    rw [shiftExtend_of_val_succ_eq m (r := r) (n := j + 1) (by omega)]
    linarith
  have hlast : shiftExtend m t = shiftExtend m (t - 1) := by
    obtain ⟨r, hrv⟩ : ∃ r : Fin t, r.val = t - 1 := ⟨⟨t - 1, by omega⟩, rfl⟩
    have h := (hrow r).symm.trans (hrest r (fun hc => by rw [hc] at hrv; omega))
    rw [hrv, show DynkinShape.B.weightFactor r = 1 by rw [hwf, if_pos (by omega)],
      show shiftExtend m (t - 1 + 2) = 0 from shiftExtend_of_le m (by omega)] at h
    rw [shiftExtend_of_val_succ_eq m (r := r) (n := t) (by omega)]
    linarith
  have hleft := shiftExtend_eq_mul_of_rec m r₀.val (fun j hj => hrec j (by omega) (by omega))
  have ha1 := shiftExtend_one_pos m hpos (by omega)
  have hconst := shiftExtend_const_of_rec m r₀.val t (by omega)
    (fun j h1 h2 => hrec j (by omega) (by omega)) hlast
  have hmr : m r₀ = shiftExtend m (r₀.val + 1) := (shiftExtend_succ m r₀).symm
  have hS : shiftExtend m (r₀.val + 1) = ((r₀.val : ℤ) + 1) * shiftExtend m 1 := by
    rw [hleft (r₀.val + 1) le_rfl]
    push_cast
    ring
  have hprev : shiftExtend m r₀.val = (r₀.val : ℤ) * shiftExtend m 1 := hleft r₀.val (by omega)
  have hnext : shiftExtend m (r₀.val + 2) = shiftExtend m (r₀.val + 1) :=
    hconst (r₀.val + 2) (by omega) (by omega)
  rw [hrow r₀, show DynkinShape.B.weightFactor r₀ = 2 by rw [hwf, if_neg (by omega)]] at hmain
  have e1 : (4 : ℤ) * shiftExtend m 1
      = (2 * k * ((r₀.val : ℤ) + 1)) * shiftExtend m 1 := by
    linear_combination hmain + (2 * k - 8) * hmr + 4 * hnext + 4 * hprev + (2 * k - 4) * hS
  have hki : 2 = k * ((r₀.val : ℤ) + 1) := by linarith [mul_right_cancel₀ ha1.ne' e1]
  have hle := le_two_of_two_eq_mul hki
  have hrho : r₀.val = 1 := by omega
  rw [show ((r₀.val : ℤ) + 1) = 2 by omega] at hki
  refine ⟨hrho, by omega, shiftExtend m 1, ha1, ?_, ?_⟩
  · intro r hr0
    rw [← shiftExtend_succ m r, hr0]
  · intro r hr1
    have := r.isLt
    rw [← shiftExtend_succ m r, hconst (r.val + 1) (by omega) (by omega), hS, hrho]
    push_cast
    ring

/-! ### Type C -/

/-- The affine extension system solved over a chain of type `C` at an interior vertex. As in
type `B` the attachment vertex is forced to be the second one and the level to be one; the
multiplicities are `(a, 2a, …, 2a, a)`, the last entry being the one at the heavy end. -/
public lemma affine_system_solved_C {t : ℕ} (ht : 4 ≤ t) (m : Fin t → ℤ) (hpos : ∀ r, 0 < m r)
    (r₀ : Fin t) (k : ℤ) (hlo : 1 ≤ r₀.val) (hhi : r₀.val + 2 ≤ t)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.C.weightedCartan r s * m s = 0)
    (hmain : 2 * ∑ s, DynkinShape.C.weightedCartan r₀ s * m s
      = k * DynkinShape.C.weightFactor r₀ * m r₀) :
    r₀.val = 1 ∧ k = 1 ∧ ∃ a : ℤ, 0 < a ∧
      (∀ r : Fin t, r.val = 0 → m r = a) ∧
      (∀ r : Fin t, 1 ≤ r.val → r.val + 2 ≤ t → m r = 2 * a) ∧
      (∀ r : Fin t, r.val + 1 = t → m r = a) := by
  have hr₀ := r₀.isLt
  have hwf : ∀ r : Fin t, DynkinShape.C.weightFactor r = if r.val + 1 = t then 2 else 1 :=
    fun _ => rfl
  have hwfge : ∀ r : Fin t, 1 ≤ DynkinShape.C.weightFactor r := by
    intro r
    rw [hwf]
    split_ifs <;> norm_num
  have hrow : ∀ r : Fin t, ∑ s, DynkinShape.C.weightedCartan r s * m s
      = 2 * DynkinShape.C.weightFactor r * m r
        - DynkinShape.C.weightFactor r * shiftExtend m r.val
        - (if r.val + 2 = t then 2 else 1) * shiftExtend m (r.val + 2) := by
    intro r
    refine DynkinShape.C.row_chain (show (2 : ℕ) ≤ t by omega) (by omega)
      (fun _ _ => Iff.rfl) m r _ _ (fun s hs => ?_) (fun s hs => ?_)
    · have := r.isLt
      rw [show DynkinShape.C.weightFactor s = 1 by rw [hwf, if_neg (by omega)]]
      exact max_eq_left (hwfge r)
    · have := s.isLt
      rw [show DynkinShape.C.weightFactor r = 1 by rw [hwf, if_neg (by omega)], hwf s]
      by_cases hc : r.val + 2 = t
      · rw [if_pos (show s.val + 1 = t by omega), if_pos hc]
        norm_num
      · rw [if_neg (show ¬ (s.val + 1 = t) by omega), if_neg hc]
        norm_num
  have hrec : ∀ j, j + 2 < t → j ≠ r₀.val →
      2 * shiftExtend m (j + 1) = shiftExtend m j + shiftExtend m (j + 2) := by
    intro j hj hne
    obtain ⟨r, hrv⟩ : ∃ r : Fin t, r.val = j := ⟨⟨j, by omega⟩, rfl⟩
    have h := (hrow r).symm.trans (hrest r (fun hc => hne (by rw [← hrv, hc])))
    rw [hrv, show DynkinShape.C.weightFactor r = 1 by rw [hwf, if_neg (by omega)],
      if_neg (show ¬ (j + 2 = t) by omega)] at h
    rw [shiftExtend_of_val_succ_eq m (r := r) (n := j + 1) (by omega)]
    linarith
  have hend1 : 2 * shiftExtend m t = shiftExtend m (t - 1) := by
    obtain ⟨r, hrv⟩ : ∃ r : Fin t, r.val = t - 1 := ⟨⟨t - 1, by omega⟩, rfl⟩
    have h := (hrow r).symm.trans (hrest r (fun hc => by rw [hc] at hrv; omega))
    rw [hrv, show DynkinShape.C.weightFactor r = 2 by rw [hwf, if_pos (by omega)],
      if_neg (show ¬ (t - 1 + 2 = t) by omega),
      show shiftExtend m (t - 1 + 2) = 0 from shiftExtend_of_le m (by omega)] at h
    rw [shiftExtend_of_val_succ_eq m (r := r) (n := t) (by omega)]
    linarith
  have hleft := shiftExtend_eq_mul_of_rec m r₀.val (fun j hj => hrec j (by omega) (by omega))
  have ha1 := shiftExtend_one_pos m hpos (by omega)
  have hmr : m r₀ = shiftExtend m (r₀.val + 1) := (shiftExtend_succ m r₀).symm
  have hS : shiftExtend m (r₀.val + 1) = ((r₀.val : ℤ) + 1) * shiftExtend m 1 := by
    rw [hleft (r₀.val + 1) le_rfl]
    push_cast
    ring
  have hprev : shiftExtend m r₀.val = (r₀.val : ℤ) * shiftExtend m 1 := hleft r₀.val (by omega)
  rw [hrow r₀, show DynkinShape.C.weightFactor r₀ = 1 by rw [hwf, if_neg (by omega)]] at hmain
  by_cases hcase : r₀.val + 2 = t
  · -- the attachment vertex is the penultimate one: no solution
    exfalso
    rw [if_pos hcase] at hmain
    have hM2 : shiftExtend m r₀.val = ((t : ℤ) - 2) * shiftExtend m 1 := by
      rw [hprev]
      congr 1
      omega
    have hM1 : shiftExtend m (r₀.val + 1) = ((t : ℤ) - 1) * shiftExtend m 1 := by
      rw [hS]
      congr 1
      omega
    have hMt : 2 * shiftExtend m (r₀.val + 2) = ((t : ℤ) - 1) * shiftExtend m 1 := by
      rw [show r₀.val + 2 = t from hcase, hend1, show t - 1 = r₀.val + 1 by omega, hM1]
    have hkey : (2 : ℤ) * shiftExtend m 1 = (k * ((t : ℤ) - 1)) * shiftExtend m 1 := by
      linear_combination hmain + (k - 4) * hmr + 2 * hM2 + (k - 4) * hM1 + 2 * hMt
    have hle := le_two_of_two_eq_mul (mul_right_cancel₀ ha1.ne' hkey)
    omega
  · -- the attachment vertex is further in: the far side is constant
    rw [if_neg hcase] at hmain
    have hend2 : shiftExtend m (t - 1) = shiftExtend m (t - 2) := by
      obtain ⟨r, hrv⟩ : ∃ r : Fin t, r.val = t - 2 := ⟨⟨t - 2, by omega⟩, rfl⟩
      have h := (hrow r).symm.trans (hrest r (fun hc => by rw [hc] at hrv; omega))
      have hmr2 : m r = shiftExtend m (t - 1) := (shiftExtend_of_val_succ_eq m (by omega)).symm
      rw [hrv, show DynkinShape.C.weightFactor r = 1 by rw [hwf, if_neg (by omega)],
        if_pos (show t - 2 + 2 = t by omega), show t - 2 + 2 = t by omega,
        hmr2] at h
      linarith [hend1]
    have hconst := shiftExtend_const_of_rec m r₀.val (t - 1) (by omega)
      (fun j h1 h2 => hrec j (by omega) (by omega))
      (by rw [show t - 1 - 1 = t - 2 by omega]; exact hend2)
    have hnext : shiftExtend m (r₀.val + 2) = shiftExtend m (r₀.val + 1) :=
      hconst (r₀.val + 2) (by omega) (by omega)
    have e1 : (2 : ℤ) * shiftExtend m 1
        = (k * ((r₀.val : ℤ) + 1)) * shiftExtend m 1 := by
      linear_combination hmain + (k - 4) * hmr + 2 * hnext + 2 * hprev + (k - 2) * hS
    have hki := mul_right_cancel₀ ha1.ne' e1
    have hle := le_two_of_two_eq_mul hki
    have hrho : r₀.val = 1 := by omega
    have hk1 : k = 1 := by
      rw [show ((r₀.val : ℤ) + 1) = 2 by omega] at hki
      omega
    refine ⟨hrho, hk1, shiftExtend m 1, ha1, ?_, ?_, ?_⟩
    · intro r hr0
      rw [← shiftExtend_succ m r, hr0]
    · intro r hr1 hr2
      rw [← shiftExtend_succ m r, hconst (r.val + 1) (by omega) (by omega), hS, hrho]
      push_cast
      ring
    · intro r hrt
      rw [← shiftExtend_succ m r, show r.val + 1 = t from hrt]
      rw [hconst (t - 1) (by omega) (by omega), hS, hrho] at hend1
      push_cast at hend1
      linarith

/-! ### Type F₄ -/

/-- The affine extension system has no solution over the diagram `F₄` at an interior vertex:
at either of the two the inhomogeneous equation reads `3 k = 1`. -/
public lemma not_affine_system_F4 (m : Fin 4 → ℤ) (hpos : ∀ r, 0 < m r) (r₀ : Fin 4) (k : ℤ)
    (hlo : 1 ≤ r₀.val) (hhi : r₀.val + 2 ≤ 4)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.F4.weightedCartan r s * m s = 0)
    (hmain : 2 * ∑ s, DynkinShape.F4.weightedCartan r₀ s * m s
      = k * DynkinShape.F4.weightFactor r₀ * m r₀) : False := by
  have hwf : ∀ r : Fin 4, DynkinShape.F4.weightFactor r = if r.val < 2 then 1 else 2 :=
    fun _ => rfl
  have hrow : ∀ r : Fin 4, ∑ s, DynkinShape.F4.weightedCartan r s * m s
      = 2 * DynkinShape.F4.weightFactor r * m r
        - (if r.val ≤ 1 then 1 else 2) * shiftExtend m r.val
        - (if r.val = 0 then 1 else 2) * shiftExtend m (r.val + 2) := by
    intro r
    refine DynkinShape.F4.row_chain rfl (by omega) (fun _ _ => Iff.rfl) m r _ _
      (fun s hs => ?_) (fun s hs => ?_)
    · have h1 := s.isLt
      have h2 := r.isLt
      rw [hwf r, hwf s]
      rcases (show r.val = 1 ∨ r.val = 2 ∨ r.val = 3 by omega) with h | h | h
      · rw [h, show s.val = 0 by omega]
        norm_num
      · rw [h, show s.val = 1 by omega]
        norm_num
      · rw [h, show s.val = 2 by omega]
        norm_num
    · have h1 := s.isLt
      have h2 := r.isLt
      rw [hwf r, hwf s]
      rcases (show r.val = 0 ∨ r.val = 1 ∨ r.val = 2 by omega) with h | h | h
      · rw [h, show s.val = 1 by omega]
        norm_num
      · rw [h, show s.val = 2 by omega]
        norm_num
      · rw [h, show s.val = 3 by omega]
        norm_num
  obtain ⟨v0, hv0⟩ : ∃ r : Fin 4, r.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨v1, hv1⟩ : ∃ r : Fin 4, r.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨v2, hv2⟩ : ∃ r : Fin 4, r.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  obtain ⟨v3, hv3⟩ : ∃ r : Fin 4, r.val = 3 := ⟨⟨3, by omega⟩, rfl⟩
  have hs1 : shiftExtend m 1 = m v0 := shiftExtend_of_val_succ_eq m (by omega)
  have hs2 : shiftExtend m 2 = m v1 := shiftExtend_of_val_succ_eq m (by omega)
  have hs3 : shiftExtend m 3 = m v2 := shiftExtend_of_val_succ_eq m (by omega)
  have hs4 : shiftExtend m 4 = m v3 := shiftExtend_of_val_succ_eq m (by omega)
  have hs5 : shiftExtend m 5 = 0 := shiftExtend_of_le m (by omega)
  have row0 : ∑ s, DynkinShape.F4.weightedCartan v0 s * m s = 2 * m v0 - m v1 := by
    rw [hrow v0, hwf, hv0]
    norm_num [hs2]
  have row1 : ∑ s, DynkinShape.F4.weightedCartan v1 s * m s
      = 2 * m v1 - m v0 - 2 * m v2 := by
    rw [hrow v1, hwf, hv1]
    norm_num [hs1, hs3]
  have row2 : ∑ s, DynkinShape.F4.weightedCartan v2 s * m s
      = 4 * m v2 - 2 * m v1 - 2 * m v3 := by
    rw [hrow v2, hwf, hv2]
    norm_num [hs2, hs4]
  have row3 : ∑ s, DynkinShape.F4.weightedCartan v3 s * m s = 4 * m v3 - 2 * m v2 := by
    rw [hrow v3, hwf, hv3]
    norm_num [hs3, hs5]
  have hcase : r₀ = v1 ∨ r₀ = v2 := by
    rcases (show r₀.val = 1 ∨ r₀.val = 2 by omega) with h1 | h1
    · exact Or.inl (Fin.ext (by omega))
    · exact Or.inr (Fin.ext (by omega))
  rcases hcase with hc | hc
  · have q0 : 2 * m v0 - m v1 = 0 :=
      row0.symm.trans (hrest v0 (fun h => by rw [h, hc] at hv0; omega))
    have q2 : 4 * m v2 - 2 * m v1 - 2 * m v3 = 0 :=
      row2.symm.trans (hrest v2 (fun h => by rw [h, hc] at hv2; omega))
    have q3 : 4 * m v3 - 2 * m v2 = 0 :=
      row3.symm.trans (hrest v3 (fun h => by rw [h, hc] at hv3; omega))
    have hmn : 2 * (2 * m v1 - m v0 - 2 * m v2) = k * m v1 := by
      rw [hc, row1, hwf, hv1, if_pos (show (1 : ℕ) < 2 by omega)] at hmain
      linear_combination hmain
    have hm2 : m v2 = 2 * m v3 := by linarith
    have hm1 : m v1 = 3 * m v3 := by linarith
    have hm0 : 2 * m v0 = 3 * m v3 := by linarith
    have hkey : m v3 = 3 * k * m v3 := by
      linear_combination hmn + (k - 4) * hm1 + 4 * hm2 + hm0
    have hz : (3 * k - 1) * m v3 = 0 := by linarith
    rcases mul_eq_zero.mp hz with h | h
    · omega
    · exact absurd h (hpos v3).ne'
  · have q0 : 2 * m v0 - m v1 = 0 :=
      row0.symm.trans (hrest v0 (fun h => by rw [h, hc] at hv0; omega))
    have q1 : 2 * m v1 - m v0 - 2 * m v2 = 0 :=
      row1.symm.trans (hrest v1 (fun h => by rw [h, hc] at hv1; omega))
    have q3 : 4 * m v3 - 2 * m v2 = 0 :=
      row3.symm.trans (hrest v3 (fun h => by rw [h, hc] at hv3; omega))
    have hmn : 2 * (4 * m v2 - 2 * m v1 - 2 * m v3) = k * 2 * m v2 := by
      rw [hc, row2, hwf, hv2, if_neg (show ¬ ((2 : ℕ) < 2) by omega)] at hmain
      linear_combination hmain
    have hm1 : m v1 = 2 * m v0 := by linarith
    have h2m2 : 2 * m v2 = 3 * m v0 := by linarith
    have hm3 : 2 * m v3 = m v2 := by linarith
    have hkey : 2 * m v2 = 6 * k * m v2 := by
      linear_combination 3 * hmn + 12 * hm1 + 6 * hm3 - 8 * h2m2
    have hz : (6 * k - 2) * m v2 = 0 := by linarith
    rcases mul_eq_zero.mp hz with h | h
    · omega
    · exact absurd h (hpos v2).ne'

end AlgebraicGeometry
