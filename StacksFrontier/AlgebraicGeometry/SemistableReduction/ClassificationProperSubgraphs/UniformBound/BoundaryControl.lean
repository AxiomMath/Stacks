module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound.EdgeSums
import all StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound.EdgeSums
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound.MinusTwoComponents
import all StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound.MinusTwoComponents

/-!
# Boundary control of the multiplicities of a Dynkin configuration

A connected component of minus-two indices of a minimal numerical type is one of
the Dynkin configurations. For the configurations of types `A`, `B`, `C` and
`D`, all its multiplicities are within a factor of two of a multiplicity on its
boundary, which is bounded directly. This gives the diagonal bound on such a
component.

## References

* [Stacks Project, Tag 0C9W](https://stacks.math.columbia.edu/tag/0C9W)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

private def BoundaryAt {t : ℕ} (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (v : Fin t → Fin T.componentCount)
    (r : Fin t) : Prop :=
  ∃ y, y ∉ I ∧ 0 < T.intersection (v r) y

private theorem no_outside_of_not_boundary {t : ℕ} (T : NumericalType)
    (i : Fin T.componentCount) (hi : IsMinusTwoIndex T i)
    (v : Fin t → Fin T.componentCount)
    (hrange : Set.range v = (MinusTwoComponent T i : Set _))
    (r : Fin t) (hnot : ¬ BoundaryAt T (MinusTwoComponent T i) v r) :
    ∀ y, y ∉ MinusTwoComponent T i → T.intersection (v r) y = 0 :=
  no_outside_intersection_of_no_boundary T i hi v hrange r
    fun ⟨y, hy, _, hpos⟩ => hnot ⟨y, hy, hpos⟩

private theorem row_eq_of_not_boundary {t : ℕ} (T : NumericalType)
    (i : Fin T.componentCount) (hi : IsMinusTwoIndex T i)
    (v : Fin t → Fin T.componentCount)
    (d : DynkinShape) (w : ℤ)
    (hconfig : IsDynkinConfiguration T v d w)
    (hinj : Function.Injective v)
    (hrange : Set.range v = (MinusTwoComponent T i : Set _))
    (r : Fin t) (hnot : ¬ BoundaryAt T (MinusTwoComponent T i) v r) :
    (∑ s : Fin t,
      if DynkinShape.Edge d r s then
        max (d.weightFactor r) (d.weightFactor s) * T.multiplicity (v s) else 0) =
        2 * d.weightFactor r * T.multiplicity (v r) :=
  row_eq_on_minusTwoComponent T (MinusTwoComponent T i) v d w
    hconfig hinj hrange r (no_outside_of_not_boundary T i hi v hrange r hnot)

private theorem row_eq_A_boundary {t : ℕ} (T : NumericalType)
    (i : Fin T.componentCount) (hi : IsMinusTwoIndex T i)
    (v : Fin t → Fin T.componentCount)
    (w : ℤ) (hconfig : IsDynkinConfiguration T v .A w)
    (hinj : Function.Injective v)
    (hrange : Set.range v = (MinusTwoComponent T i : Set _))
    (r : Fin t) (hnot : ¬ BoundaryAt T (MinusTwoComponent T i) v r) :
    (∑ s : Fin t,
      if DynkinShape.Edge .A r s then T.multiplicity (v s) else 0) =
        2 * T.multiplicity (v r) := by
  simpa [DynkinShape.weightFactor] using
    (row_eq_of_not_boundary T i hi v .A w hconfig hinj hrange r hnot)

/-- A function on `Fin t` attains its maximum at a least index. -/
private theorem exists_max_min_index {t : ℕ} (m : Fin t → ℤ) (ht : 0 < t) :
    ∃ r : Fin t, (∀ s, m s ≤ m r) ∧ ∀ s, m s = m r → r.val ≤ s.val := by
  classical
  obtain ⟨r₀, -, hr₀max⟩ := Finset.exists_max_image Finset.univ m
    (⟨⟨0, ht⟩, Finset.mem_univ _⟩ : Finset.univ.Nonempty)
  obtain ⟨r, hrS, hrmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun s => m s = m r₀) Fin.val ⟨r₀, by simp⟩
  have hrr₀ : m r = m r₀ := (Finset.mem_filter.mp hrS).2
  exact ⟨r, fun s => (hr₀max s (Finset.mem_univ s)).trans hrr₀.ge, fun s hs =>
    hrmin s (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs.trans hrr₀⟩)⟩

private theorem exists_A_boundary_max {t : ℕ} (T : NumericalType)
    (i : Fin T.componentCount) (hi : IsMinusTwoIndex T i)
    (v : Fin t → Fin T.componentCount) (hinj : Function.Injective v)
    (hrange : Set.range v = (MinusTwoComponent T i : Set _))
    (w : ℤ) (hconfig : IsDynkinConfiguration T v .A w) :
    ∃ r : Fin t, BoundaryAt T (MinusTwoComponent T i) v r ∧
      ∀ s : Fin t, T.multiplicity (v s) ≤ T.multiplicity (v r) := by
  classical
  let m : Fin t → ℤ := fun s => T.multiplicity (v s)
  have ht : 2 ≤ t := hconfig.1
  obtain ⟨r, hmax, hmin⟩ := exists_max_min_index m (by omega)
  have hpositive : 0 < m r := by
    dsimp [m]
    exact T.multiplicity_pos (v r)
  have hboundary : BoundaryAt T (MinusTwoComponent T i) v r := by
    by_contra hnot
    have hrow := row_eq_A_boundary T i hi v w hconfig hinj hrange r hnot
    by_cases hrzero : r.val = 0
    · have hrEq : r = ⟨0, by omega⟩ := Fin.ext hrzero
      rw [hrEq] at hrow
      rw [hrEq] at hmax hmin
      rw [sum_edge_A_head (by omega) m] at hrow
      dsimp [m] at hrow
      have hmax' := hmax ⟨1, by omega⟩
      dsimp [m] at hmax'
      have hp := T.multiplicity_pos (v ⟨0, by omega⟩)
      omega
    · by_cases hrtail : r.val + 1 = t
      · have htval : r.val = t - 1 := by omega
        have hrEq : r = ⟨t - 1, by omega⟩ := Fin.ext htval
        rw [hrEq] at hrow
        rw [hrEq] at hmax hmin
        rw [sum_edge_A_tail (by omega) m] at hrow
        dsimp [m] at hrow
        have hmax' := hmax ⟨t - 2, by omega⟩
        dsimp [m] at hmax'
        have hp := T.multiplicity_pos (v ⟨t - 1, by omega⟩)
        omega
      · have hrpos : 0 < r.val := by omega
        have hrlt : r.val + 1 < t := by omega
        let n := r.val
        have hrEq : r = ⟨n, by dsimp [n]; omega⟩ := rfl
        rw [hrEq] at hrow
        rw [hrEq] at hmax hmin
        have hrow' := hrow
        rw [sum_edge_A_inner n (by dsimp [n]; omega)
          (by dsimp [n]; omega) m] at hrow'
        dsimp [m] at hrow'
        have hprev : m ⟨n - 1, by omega⟩ < m ⟨n, by omega⟩ := by
          have hle := hmax ⟨n - 1, by omega⟩
          have hne : m ⟨n - 1, by omega⟩ ≠ m ⟨n, by omega⟩ := by
            intro heq
            have hmin' := hmin ⟨n - 1, by omega⟩ heq
            change n ≤ n - 1 at hmin'
            omega
          omega
        have hnext := hmax ⟨n + 1, by omega⟩
        dsimp [m] at hprev hnext
        omega
  exact ⟨r, hboundary, hmax⟩

private theorem exists_BC_boundary_control {t : ℕ} (T : NumericalType)
    (i : Fin T.componentCount) (hi : IsMinusTwoIndex T i)
    (v : Fin t → Fin T.componentCount) (hinj : Function.Injective v)
    (hrange : Set.range v = (MinusTwoComponent T i : Set _))
    (d : DynkinShape) (w : ℤ)
    (hd : d = .B ∨ d = .C)
    (hconfig : IsDynkinConfiguration T v d w) (ht : 2 < t) :
    ∃ r : Fin t, BoundaryAt T (MinusTwoComponent T i) v r ∧
      ∀ s : Fin t, T.multiplicity (v s) ≤ 2 * T.multiplicity (v r) := by
  classical
  let m : Fin t → ℤ := fun s => T.multiplicity (v s)
  have ht' : 1 < t := by omega
  obtain ⟨r, hmax, hmin⟩ := exists_max_min_index m (by omega)
  have hpositive : 0 < m r := by
    dsimp [m]
    exact T.multiplicity_pos (v r)
  have hboundary_or_max :
      ∃ b : Fin t, BoundaryAt T (MinusTwoComponent T i) v b ∧
        ∀ s : Fin t, m s ≤ 2 * m b := by
    rcases hd with hB | hC
    · subst d
      by_cases hboundary : BoundaryAt T (MinusTwoComponent T i) v r
      · exact ⟨r, hboundary, fun s => by have := hmax s; omega⟩
      · by_cases hzero : r.val = 0
        · have hrow := row_eq_of_not_boundary T i hi v .B w hconfig hinj hrange r hboundary
          change (∑ s : Fin t, if DynkinShape.Edge .B r s then
            max (DynkinShape.weightFactor .B r)
              (DynkinShape.weightFactor .B s) * m s else 0) =
              2 * DynkinShape.weightFactor .B r * m r at hrow
          have hrEq : r = ⟨0, by omega⟩ := Fin.ext hzero
          rw [hrEq] at hrow hmax hmin hpositive
          rw [sum_edge_B_nonlast _ (by omega) m, sum_edge_A_head ht' m] at hrow
          have hfr : DynkinShape.weightFactor .B
              (⟨0, by omega⟩ : Fin t) = 2 := by
            show (if 0 + 1 = t then 1 else 2) = 2
            rw [ite_eq_right (by omega)]
          rw [hfr] at hrow
          have hmax1 := hmax ⟨1, by omega⟩
          have hp0 := T.multiplicity_pos (v ⟨0, by omega⟩)
          dsimp [m] at hrow hmax1
          nlinarith [hrow, hmax1, hp0]
        · by_cases hlast : r.val + 1 = t
          · have hrEq : r = ⟨t - 1, by omega⟩ := Fin.ext (show r.val = t - 1 by omega)
            rw [hrEq] at hboundary hmax hmin
            have hrow := row_eq_of_not_boundary T i hi v .B w hconfig hinj hrange
              ⟨t - 1, by omega⟩ hboundary
            change (∑ s : Fin t, if DynkinShape.Edge .B
              (⟨t - 1, by omega⟩ : Fin t) s then
              max (DynkinShape.weightFactor .B
                (⟨t - 1, by omega⟩ : Fin t))
                (DynkinShape.weightFactor .B s) * m s else 0) =
              2 * DynkinShape.weightFactor .B
                (⟨t - 1, by omega⟩ : Fin t) * m ⟨t - 1, by omega⟩ at hrow
            rw [sum_edge_B_last ht' m] at hrow
            have hprev : m ⟨t - 2, by omega⟩ = m ⟨t - 1, by omega⟩ := by
              have hlast : t - 1 + 1 = t := Nat.sub_add_cancel (by omega : 1 ≤ t)
              have hfactor : DynkinShape.weightFactor .B
                  (⟨t - 1, by omega⟩ : Fin t) = 1 := by
                show (if t - 1 + 1 = t then 1 else 2) = 1
                simp [hlast]
              rw [hfactor] at hrow
              dsimp [m] at hrow
              nlinarith [hrow]
            have hmin' := hmin ⟨t - 2, by omega⟩ hprev
            change t - 1 ≤ t - 2 at hmin'
            omega
          · have hrow := row_eq_of_not_boundary T i hi v .B w hconfig hinj hrange r hboundary
            change (∑ s : Fin t, if DynkinShape.Edge .B r s then
              max (DynkinShape.weightFactor .B r)
                (DynkinShape.weightFactor .B s) * m s else 0) =
              2 * DynkinShape.weightFactor .B r * m r at hrow
            rw [sum_edge_B_nonlast r (by omega) m] at hrow
            have hrne : r.val + 1 < t := by omega
            let n := r.val
            have hrEq : r = ⟨n, by dsimp [n]; omega⟩ := rfl
            rw [hrEq] at hrow hmax hmin
            rw [sum_edge_A_inner n (by dsimp [n]; omega)
              (by dsimp [n]; omega) m] at hrow
            have hfr : DynkinShape.weightFactor .B
                (⟨n, by omega⟩ : Fin t) = 2 := by
              show (if n + 1 = t then 1 else 2) = 2
              rw [ite_eq_right (by omega)]
            rw [hfr] at hrow
            have hprev : m ⟨n - 1, by omega⟩ = m ⟨n, by omega⟩ := by
              have hle := hmax ⟨n - 1, by omega⟩
              have hnext := hmax ⟨n + 1, by omega⟩
              dsimp [m] at hrow hle hnext
              nlinarith [hrow, hle, hnext]
            have hmin' := hmin ⟨n - 1, by omega⟩ hprev
            change n ≤ n - 1 at hmin'
            omega
    · subst d
      by_cases hboundary : BoundaryAt T (MinusTwoComponent T i) v r
      · exact ⟨r, hboundary, fun s => by have := hmax s; omega⟩
      · by_cases hzero : r.val = 0
        · have hrow := row_eq_of_not_boundary T i hi v .C w hconfig hinj hrange r hboundary
          change (∑ s : Fin t, if DynkinShape.Edge .C r s then
            max (DynkinShape.weightFactor .C r)
              (DynkinShape.weightFactor .C s) * m s else 0) =
              2 * DynkinShape.weightFactor .C r * m r at hrow
          have hrEq : r = ⟨0, by omega⟩ := Fin.ext hzero
          rw [hrEq] at hrow hmax hmin hpositive
          rw [sum_edge_C_nonlast _ (by omega) m, sum_edge_A_head ht' m] at hrow
          have hfr : DynkinShape.weightFactor .C
              (⟨0, by omega⟩ : Fin t) = 1 := by
            show (if 0 + 1 = t then 2 else 1) = 1
            rw [ite_eq_right (by omega)]
          rw [hfr] at hrow
          have h1 : m ⟨1, by omega⟩ = 2 * m ⟨0, by omega⟩ := by
            nlinarith [hrow]
          have hmax1 := hmax ⟨1, by omega⟩
          have hp0 := T.multiplicity_pos (v ⟨0, by omega⟩)
          dsimp [m] at hrow h1 hmax1
          nlinarith [hrow, h1, hmax1, hp0]
        · by_cases hlast : r.val + 1 = t
          · have hrEq : r = ⟨t - 1, by omega⟩ := Fin.ext (show r.val = t - 1 by omega)
            rw [hrEq] at hboundary hmax hmin
            have hrow := row_eq_of_not_boundary T i hi v .C w hconfig hinj hrange
              ⟨t - 1, by omega⟩ hboundary
            change (∑ s : Fin t, if DynkinShape.Edge .C
              (⟨t - 1, by omega⟩ : Fin t) s then
              max (DynkinShape.weightFactor .C
                (⟨t - 1, by omega⟩ : Fin t))
                (DynkinShape.weightFactor .C s) * m s else 0) =
              2 * DynkinShape.weightFactor .C
                (⟨t - 1, by omega⟩ : Fin t) * m ⟨t - 1, by omega⟩ at hrow
            rw [sum_edge_C_last ht' m] at hrow
            have hprev : m ⟨t - 2, by omega⟩ = 2 * m ⟨t - 1, by omega⟩ := by
              have hlast : t - 1 + 1 = t := Nat.sub_add_cancel (by omega : 1 ≤ t)
              have hfactor : DynkinShape.weightFactor .C
                  (⟨t - 1, by omega⟩ : Fin t) = 2 := by
                show (if t - 1 + 1 = t then 2 else 1) = 2
                simp [hlast]
              rw [hfactor] at hrow
              dsimp [m] at hrow
              nlinarith [hrow]
            have hmaxprev := hmax ⟨t - 2, by omega⟩
            have hp := T.multiplicity_pos (v ⟨t - 1, by omega⟩)
            dsimp [m] at hprev hmaxprev
            nlinarith [hprev, hmaxprev, hp]
          · have hrow := row_eq_of_not_boundary T i hi v .C w hconfig hinj hrange r hboundary
            change (∑ s : Fin t, if DynkinShape.Edge .C r s then
              max (DynkinShape.weightFactor .C r)
                (DynkinShape.weightFactor .C s) * m s else 0) =
              2 * DynkinShape.weightFactor .C r * m r at hrow
            by_cases hstd : r.val + 2 < t
            · rw [sum_edge_C_nonlast r hstd m] at hrow
              let n := r.val
              have hrEq : r = ⟨n, by dsimp [n]; omega⟩ := rfl
              rw [hrEq] at hrow hmax hmin
              rw [sum_edge_A_inner n (by dsimp [n]; omega)
                (by dsimp [n]; omega) m] at hrow
              have hfr : DynkinShape.weightFactor .C
                  (⟨n, by omega⟩ : Fin t) = 1 := by
                show (if n + 1 = t then 2 else 1) = 1
                rw [ite_eq_right (by omega)]
              rw [hfr] at hrow
              have hprev : m ⟨n - 1, by omega⟩ = m ⟨n, by omega⟩ := by
                have hle := hmax ⟨n - 1, by omega⟩
                have hnext := hmax ⟨n + 1, by omega⟩
                dsimp [m] at hrow hle hnext
                nlinarith [hrow, hle, hnext]
              have hmin' := hmin ⟨n - 1, by omega⟩ hprev
              change n ≤ n - 1 at hmin'
              have hne := hzero
              omega
            · have hn : r.val + 2 = t := by omega
              have hrEq : r = ⟨t - 2, by omega⟩ := Fin.ext (show r.val = t - 2 by omega)
              rw [hrEq] at hrow hmax hmin
              have htC : 2 < t := by omega
              rw [sum_edge_C_penultimate htC m] at hrow
              have hfr : DynkinShape.weightFactor .C
                  (⟨t - 2, by omega⟩ : Fin t) = 1 := by
                show (if t - 2 + 1 = t then 2 else 1) = 1
                rw [ite_eq_right (by omega)]
              rw [hfr] at hrow
              let e : Fin t := ⟨t - 1, by omega⟩
              by_cases hend : BoundaryAt T (MinusTwoComponent T i) v e
              · have hle := hmax ⟨t - 3, by omega⟩
                have hle' := hmax e
                dsimp [m] at hrow hle hle'
                have hlow : m ⟨t - 2, by omega⟩ ≤ 2 * m e := by
                  nlinarith [hrow, hle]
                exact ⟨e, hend, fun s => (hmax s).trans hlow⟩
              · have heqrow := row_eq_of_not_boundary T i hi v .C w hconfig hinj hrange e hend
                change (∑ s : Fin t, if DynkinShape.Edge .C e s then
                  max (DynkinShape.weightFactor .C e)
                    (DynkinShape.weightFactor .C s) * m s else 0) =
                  2 * DynkinShape.weightFactor .C e * m e at heqrow
                rw [sum_edge_C_last ht' m] at heqrow
                have hprev : m ⟨t - 2, by omega⟩ = 2 * m e := by
                  have hlast : t - 1 + 1 = t := Nat.sub_add_cancel (by omega : 1 ≤ t)
                  have hfactor : DynkinShape.weightFactor .C e = 2 := by
                    show (if t - 1 + 1 = t then 2 else 1) = 2
                    simp [hlast]
                  rw [hfactor] at heqrow
                  dsimp [m] at heqrow
                  nlinarith [heqrow]
                have hprevmax := hmax ⟨t - 2, by omega⟩
                have hmiddle : m ⟨t - 3, by omega⟩ = m ⟨t - 2, by omega⟩ := by
                  dsimp [m] at hprev hrow hprevmax
                  nlinarith [hrow, hprev]
                have hmin' := hmin ⟨t - 3, by omega⟩ hmiddle
                change t - 2 ≤ t - 3 at hmin'
                omega
  rcases hboundary_or_max with ⟨b, hb, hbmax⟩
  exact ⟨b, hb, by simpa [m] using hbmax⟩

private theorem diagonal_bound_of_config_control {t : ℕ} (T : NumericalType)
    (g : ℤ) (hg : 2 ≤ g) (hgenus : genus T = g) (hminimal : IsMinimal T)
    (hn : 1 < T.componentCount) (i : Fin T.componentCount)
    (hi : IsMinusTwoIndex T i) (v : Fin t → Fin T.componentCount)
    (_hinj : Function.Injective v)
    (hrange : Set.range v = (MinusTwoComponent T i : Set _))
    (d : DynkinShape) (w : ℤ)
    (hconfig : IsDynkinConfiguration T v d w)
    (b : Fin t) (hb : BoundaryAt T (MinusTwoComponent T i) v b)
    (hfac : ∀ r : Fin t,
      1 ≤ d.weightFactor r ∧ d.weightFactor r ≤ 2)
    (C : ℤ) (hC : C ≤ 2)
    (hcontrol : ∀ r, T.multiplicity (v r) ≤
      C * T.multiplicity (v b))
    (r : Fin t) :
    T.multiplicity (v r) * |T.intersection (v r) (v r)| ≤ 768 * g := by
  obtain ⟨j, hj, hbj⟩ := hb
  have hbmem : v b ∈ MinusTwoComponent T i := by
    have hx : v b ∈ Set.range v := ⟨b, rfl⟩
    rw [hrange] at hx
    exact hx
  have hbminus : IsMinusTwoIndex T (v b) :=
    (minusTwoComponent_mem_iff T i (v b)).mp hbmem |>.1
  have hjminus : ¬ IsMinusTwoIndex T j :=
    minusTwoComponent_outside_pos_not_minus T i hi hbmem hj hbj
  have hbdiag := minus_two_diagonal_bound_of_nonminus_neighbor T g hg hgenus
    hminimal hn (v b) j hbminus hjminus hbj
  rcases hconfig with ⟨hd, hw, hweights, hinter, hineq⟩
  have hdiag (x : Fin t) : T.multiplicity (v x) * |T.intersection (v x) (v x)| =
      2 * T.multiplicity (v x) * d.weightFactor x * w := by
    have hinter'' : T.intersection (v x) (v x) =
        -2 * d.weightFactor x * w := by simpa using hinter x x
    rw [hinter'']
    have hpos : 0 < d.weightFactor x * w :=
      mul_pos (by have := hfac x; omega) hw
    rw [abs_of_nonpos (by nlinarith : -2 * d.weightFactor x * w ≤ 0)]
    ring
  have hbpos := (T.multiplicity_pos (v b)).le
  have hfactor : T.multiplicity (v r) * d.weightFactor r ≤
      4 * T.multiplicity (v b) * d.weightFactor b := by
    linarith [mul_le_mul_of_nonneg_left (hfac r).2 (T.multiplicity_pos (v r)).le,
      mul_le_mul_of_nonneg_right hC hbpos, mul_le_mul_of_nonneg_left (hfac b).1 hbpos, hcontrol r]
  calc
    T.multiplicity (v r) * |T.intersection (v r) (v r)| =
        2 * w * (T.multiplicity (v r) * d.weightFactor r) := by
          rw [hdiag r]
          ring
    _ ≤ 2 * w * (4 * T.multiplicity (v b) * d.weightFactor b) :=
          mul_le_mul_of_nonneg_left hfactor (by positivity : 0 ≤ 2 * w)
    _ = 4 * (T.multiplicity (v b) * |T.intersection (v b) (v b)|) := by
          rw [hdiag b]
          ring
    _ ≤ 768 * g := by linarith

private lemma sum_edge_D_nonbranch {t : ℕ} (r : Fin t)
    (hr : r.val + 1 < t - 2) (f : Fin t → ℤ) :
    (∑ s : Fin t, if DynkinShape.Edge .D r s then f s else 0) =
      ∑ s : Fin t, if DynkinShape.Edge .A r s then f s else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro s hs
  have hedge : DynkinShape.Edge .D r s ↔
      DynkinShape.Edge .A r s := by
    simp [DynkinShape.Edge]
    omega
  by_cases h : DynkinShape.Edge .A r s
  · simp [hedge.mpr h, h]
  · simp [mt hedge.mp h, h]

private lemma sum_edge_D_branch {t : ℕ} (ht : 3 < t) (f : Fin t → ℤ) :
    (∑ s : Fin t,
      if DynkinShape.Edge .D
        (⟨t - 3, by omega⟩ : Fin t) s then f s else 0) =
      f ⟨t - 4, by omega⟩ + f ⟨t - 2, by omega⟩ + f ⟨t - 1, by omega⟩ := by
  classical
  have hpoint (s : Fin t) :
      (if DynkinShape.Edge .D
        (⟨t - 3, by omega⟩ : Fin t) s then f s else 0) =
        (if s.val = t - 4 then f s else 0) +
        (if s.val = t - 2 then f s else 0) +
        (if s.val = t - 1 then f s else 0) := by
    by_cases h₁ : s.val = t - 4 <;>
      by_cases h₂ : s.val = t - 2 <;>
      by_cases h₃ : s.val = t - 1 <;>
      simp [DynkinShape.Edge, h₁, h₂, h₃] <;> omega
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_if_fin_val_eq (t - 4) (by omega) f,
    sum_if_fin_val_eq (t - 2) (by omega) f,
    sum_if_fin_val_eq (t - 1) (by omega) f]

private lemma sum_edge_D_leaf {t : ℕ} (ht : 3 < t)
    (r : Fin t) (hr : r.val = t - 2 ∨ r.val = t - 1)
    (f : Fin t → ℤ) :
    (∑ s : Fin t, if DynkinShape.Edge .D r s then f s else 0) =
      f ⟨t - 3, by omega⟩ := by
  classical
  have hpoint (s : Fin t) :
      (if DynkinShape.Edge .D r s then f s else 0) =
        if s.val = t - 3 then f s else 0 := by
    rcases hr with hr | hr
    · have hrEq : r = ⟨t - 2, by omega⟩ := Fin.ext hr
      rw [hrEq]
      (simp [DynkinShape.Edge]; omega)
    · have hrEq : r = ⟨t - 1, by omega⟩ := Fin.ext hr
      rw [hrEq]
      (simp [DynkinShape.Edge]; omega)
  simp_rw [hpoint]
  exact sum_if_fin_val_eq (t - 3) (by omega) f

private theorem exists_D_boundary_control {t : ℕ} (T : NumericalType)
    (i : Fin T.componentCount) (hi : IsMinusTwoIndex T i)
    (v : Fin t → Fin T.componentCount) (hinj : Function.Injective v)
    (hrange : Set.range v = (MinusTwoComponent T i : Set _))
    (w : ℤ) (hconfig : IsDynkinConfiguration T v .D w) :
    ∃ r : Fin t, BoundaryAt T (MinusTwoComponent T i) v r ∧
      ∀ s : Fin t, T.multiplicity (v s) ≤ 2 * T.multiplicity (v r) := by
  classical
  let m : Fin t → ℤ := fun s => T.multiplicity (v s)
  have ht : 4 ≤ t := hconfig.1
  obtain ⟨r, hmax, hmin⟩ := exists_max_min_index m (by omega)
  have hboundary_or_control :
      ∃ b : Fin t, BoundaryAt T (MinusTwoComponent T i) v b ∧
        ∀ s : Fin t, m s ≤ 2 * m b := by
    by_cases hboundary : BoundaryAt T (MinusTwoComponent T i) v r
    · exact ⟨r, hboundary, fun s => by
        have := hmax s
        have hp := T.multiplicity_pos (v r)
        dsimp [m] at this hp ⊢
        nlinarith⟩
    · have hrow := row_eq_of_not_boundary T i hi v .D w hconfig hinj hrange r hboundary
      have hfactor (s : Fin t) : DynkinShape.weightFactor .D s = 1 := rfl
      have hrow' :
          (∑ s : Fin t,
            if DynkinShape.Edge .D r s then m s else 0) = 2 * m r := by
        simpa [hfactor] using hrow
      by_cases hrbranch : r.val = t - 3
      · have hrEq : r = ⟨t - 3, by omega⟩ := Fin.ext hrbranch
        rw [hrEq] at hrow' hmax hmin hboundary
        rw [sum_edge_D_branch (by omega) m] at hrow'
        let left : Fin t := ⟨t - 2, by omega⟩
        let right : Fin t := ⟨t - 1, by omega⟩
        by_cases hleft : BoundaryAt T (MinusTwoComponent T i) v left
        · refine ⟨left, hleft, ?_⟩
          intro s
          have hle := hmax s
          have hratio : m ⟨t - 3, by omega⟩ ≤ 2 * m left := by
            have hrowleft :
                (∑ s : Fin t, if DynkinShape.Edge .D left s then
                  m s else 0) ≤ 2 * m left := by
              simpa [hfactor] using hconfig.2.2.2.2 left
            rwa [sum_edge_D_leaf (by omega) left (Or.inl rfl) m] at hrowleft
          dsimp [m] at hle hratio ⊢
          nlinarith [hle, hratio]
        · by_cases hright : BoundaryAt T (MinusTwoComponent T i) v right
          · refine ⟨right, hright, ?_⟩
            intro s
            have hle := hmax s
            have hratior : m ⟨t - 3, by omega⟩ ≤ 2 * m right := by
              have hraw := hconfig.2.2.2.2 right
              have hrowright :
                  (∑ s : Fin t, if DynkinShape.Edge .D right s then
                    m s else 0) ≤ 2 * m right := by
                simpa [hfactor] using hraw
              rw [sum_edge_D_leaf (by omega) right (Or.inr rfl) m] at hrowright
              exact hrowright
            dsimp [m] at hle hratior ⊢
            nlinarith [hle, hratior]
          · have hleftrow := row_eq_of_not_boundary T i hi v .D w hconfig
              hinj hrange left hleft
            have hrightrow := row_eq_of_not_boundary T i hi v .D w hconfig
              hinj hrange right hright
            have hleftsum : m ⟨t - 3, by omega⟩ = 2 * m left := by
              have hs :
                  (∑ s : Fin t, if DynkinShape.Edge .D left s then
                    m s else 0) = 2 * m left := by
                simpa [hfactor] using hleftrow
              rw [sum_edge_D_leaf (by omega) left (Or.inl rfl) m] at hs
              exact hs
            have hrightsum : m ⟨t - 3, by omega⟩ = 2 * m right := by
              have hs :
                  (∑ s : Fin t, if DynkinShape.Edge .D right s then
                    m s else 0) = 2 * m right := by
                simpa [hfactor] using hrightrow
              rw [sum_edge_D_leaf (by omega) right (Or.inr rfl) m] at hs
              exact hs
            have hmaxleft := hmax left
            have hmaxright := hmax right
            have hbranchrow :
                m ⟨t - 4, by omega⟩ + m left + m right =
                  2 * m ⟨t - 3, by omega⟩ := by
                simpa [hfactor, left, right] using hrow'
            have hmaxprev := hmax ⟨t - 4, by omega⟩
            have heqprev : m ⟨t - 4, by omega⟩ = m ⟨t - 3, by omega⟩ := by
              dsimp [m] at hleftsum hrightsum hbranchrow
              nlinarith [hleftsum, hrightsum, hbranchrow]
            have hmin' := hmin ⟨t - 4, by omega⟩ heqprev
            change t - 3 ≤ t - 4 at hmin'
            omega
      · by_cases hzero : r.val = 0
        · have hrEq : r = ⟨0, by omega⟩ := Fin.ext hzero
          rw [hrEq] at hrow' hmax hmin
          rw [sum_edge_D_nonbranch ⟨0, by omega⟩ (by omega) m] at hrow'
          rw [sum_edge_A_head (by omega) m] at hrow'
          have hmax1 := hmax ⟨1, by omega⟩
          have hp := T.multiplicity_pos (v ⟨0, by omega⟩)
          dsimp [m] at hrow' hmax1
          omega
        · by_cases hshortleaf : r.val = t - 2 ∨ r.val = t - 1
          · rw [sum_edge_D_leaf (by omega) r hshortleaf m] at hrow'
            have hp := T.multiplicity_pos (v r)
            have hmaxbranch := hmax ⟨t - 3, by omega⟩
            dsimp [m] at hrow' hmaxbranch
            linarith
          · have hrpos : 0 < r.val := by omega
            have hrinner : r.val < t - 3 := by omega
            rw [sum_edge_D_nonbranch r (by omega) m] at hrow'
            rw [sum_edge_A_inner r.val (by omega) (by omega) m] at hrow'
            have hprev : m ⟨r.val - 1, by omega⟩ = m r := by
              have hle := hmax ⟨r.val - 1, by omega⟩
              have hnext := hmax ⟨r.val + 1, by omega⟩
              dsimp [m] at hrow' hle hnext
              nlinarith [hrow', hle, hnext]
            have hmin' := hmin ⟨r.val - 1, by omega⟩ hprev
            change r.val ≤ r.val - 1 at hmin'
            omega
  rcases hboundary_or_control with ⟨b, hb, hcontrol⟩
  exact ⟨b, hb, by simpa [m] using hcontrol⟩

end AlgebraicGeometry.NumericalType
