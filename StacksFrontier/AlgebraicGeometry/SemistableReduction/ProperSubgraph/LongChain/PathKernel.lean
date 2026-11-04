module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FiveChain
public import Mathlib.Basic.Real.Basic

/-!
# Path kernels and two special endpoints

The quadratic form of a numerical type is negative on nonzero vectors supported
on a proper subset of the components, so an injective chain with fewer indices
than components has no vector with positive first entry satisfying the kernel
row equations. Consequently a chain of at least six minus-two indices cannot have
special endpoint scales (weight `2 * W` or `W / 2`) at both of its ends.

## Main results

* `AlgebraicGeometry.NumericalType.two_special_endpoints_impossible`.
-/

@[expose] public section

open Matrix

namespace AlgebraicGeometry.NumericalType

private lemma quadraticForm_lt_zero_of_proper_support
    (T : NumericalType) (x : Fin T.componentCount → ℝ)
    (I : Set (Fin T.componentCount)) (_hIne : I.Nonempty) (hIproper : I ≠ Set.univ)
    (hsupport : ∀ j, j ∉ I → x j = 0) (hx : ∃ j, x j ≠ 0) :
    x ⬝ᵥ ((fun i j => (T.intersection i j : ℝ)) *ᵥ x) < 0 := by
  let A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℝ :=
    fun i j => (T.intersection i j : ℝ)
  let m : Fin T.componentCount → ℝ := fun i => (T.multiplicity i : ℝ)
  have hsymm : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change (T.intersection j i : ℝ) = (T.intersection i j : ℝ)
    exact_mod_cast T.intersection_symm j i
  have hoff : ∀ i j, i ≠ j → 0 ≤ A i j := by
    intro i j hij
    change (0 : ℝ) ≤ (T.intersection i j : ℝ)
    exact_mod_cast T.intersection_nonneg i j hij
  have hm : ∀ i, 0 < m i := by
    intro i
    change (0 : ℝ) < (T.multiplicity i : ℝ)
    exact_mod_cast T.multiplicity_pos i
  have hAm : A *ᵥ m = 0 := by
    ext i
    simp only [mulVec, dotProduct, A, m, Pi.zero_apply]
    exact_mod_cast T.intersection_mul_multiplicity i
  have hconnected : ∀ J : Set (Fin T.componentCount), J.Nonempty → J ≠ Set.univ →
      ¬ ∀ i ∈ J, ∀ j ∉ J, A i j = 0 := by
    intro J hJne hJproper hcut
    apply T.connected ⟨J, hJne, hJproper, ?_⟩
    intro i hi j hj
    have hzero : (T.intersection i j : ℝ) = 0 := hcut i hi j hj
    exact_mod_cast hzero
  have hnonpos :=
    dotProduct_mulVec_nonpos_of_positive_kernel hsymm hoff hm hAm x
  have hzero_iff :=
    dotProduct_mulVec_eq_zero_iff_of_positive_kernel
      hsymm hoff hm hAm hconnected (x := x)
  have hne : x ⬝ᵥ (A *ᵥ x) ≠ 0 := by
    intro hq
    obtain ⟨q, hqmul⟩ := hzero_iff.mp hq
    obtain ⟨j, hj⟩ : ∃ j, j ∉ I := by
      by_contra h
      exact hIproper (Set.eq_univ_of_forall fun j => by_contra fun hj => h ⟨j, hj⟩)
    have hqj : q * m j = 0 := by
      have hval : x j = q * m j := by
        simpa [Pi.smul_apply] using congrFun hqmul j
      rw [← hval, hsupport j hj]
    have hqzero : q = 0 := (mul_eq_zero.mp hqj).resolve_right (ne_of_gt (hm j))
    subst q
    obtain ⟨k, hk⟩ := hx
    exact hk (by simpa [Pi.smul_apply] using congrFun hqmul k)
  change x ⬝ᵥ (A *ᵥ x) < 0
  exact lt_of_le_of_ne hnonpos hne

private lemma sum_single_support {ι κ : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq κ] (i : ι → κ) (c : ι → ℝ) (f : κ → ℝ) :
    ∑ a, f a * (∑ r, if a = i r then c r else 0) =
      ∑ r, c r * f (i r) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq', mul_comm]

private lemma sum_piecewise_three {ι : Type*} {R : Type*} [Fintype ι]
    [DecidableEq ι] [AddCommMonoid R]
    (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f g h : ι → R) :
    (∑ x, if x = a then f x else if x = b then g x else
      if x = c then h x else 0) = f a + g b + h c := by
  classical
  have hpt (x : ι) :
      (if x = a then f x else if x = b then g x else if x = c then h x else 0) =
        (if x = a then f x else 0) + (if x = b then g x else 0) +
          (if x = c then h x else 0) := by
    by_cases hxa : x = a
    · subst x
      simp [hab, hac]
    · by_cases hxb : x = b
      · subst x
        simp [Ne.symm hab, hbc]
      · by_cases hxc : x = c
        · subst x
          simp [Ne.symm hac, Ne.symm hbc]
        · simp [hxa, hxb, hxc]
  simp_rw [hpt, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

private lemma sum_supported_path_row {t : ℕ} {R : Type*} [AddCommMonoid R]
    (ht : 3 ≤ t) (r : Fin t) (f : Fin t → R)
    (hzero : ∀ s, s ≠ r → s.val + 1 ≠ r.val → r.val + 1 ≠ s.val → f s = 0) :
    ∑ s, f s = f r +
      (if h : 0 < r.val then f ⟨r.val - 1, by omega⟩ else 0) +
      (if h : r.val + 1 < t then f ⟨r.val + 1, h⟩ else 0) := by
  classical
  have hrlt := r.isLt
  by_cases hfirst : r.val = 0
  · let n : Fin t := ⟨r.val + 1, by omega⟩
    have hrn : r ≠ n := by
      intro he
      have hv := congrArg Fin.val he
      simp [n] at hv
    have hpoint (s : Fin t) :
        f s = (if s = r then f s else if s = n then f s else 0) := by
      by_cases hsr : s = r
      · simp [hsr]
      · by_cases hsn : s = n
        · simp [hsn]
        · have hprev : s.val + 1 ≠ r.val := by omega
          have hnext : r.val + 1 ≠ s.val := by
            intro he
            apply hsn
            apply Fin.ext
            simp [n, hfirst]
            omega
          rw [hzero s hsr hprev hnext]
          simp [hsr, hsn]
    have hsum := sum_piecewise_two r n hrn f f
    have hrep : (∑ s, f s) =
        ∑ s, if s = r then f s else if s = n then f s else 0 :=
      Finset.sum_congr rfl fun s _ => hpoint s
    rw [hrep, hsum]
    have hprev : ¬ 0 < r.val := by omega
    have hnext : r.val + 1 < t := by omega
    have hn' : n = ⟨r.val + 1, hnext⟩ := rfl
    simp only [dite_eq_right hprev, dite_eq_left hnext]
    rw [hn']
    simp
  · by_cases hlast : r.val + 1 = t
    · let p : Fin t := ⟨r.val - 1, by omega⟩
      have hpr : p ≠ r := by
        intro he
        have hv := congrArg Fin.val he
        simp [p] at hv
        omega
      have hpoint (s : Fin t) :
          f s = (if s = r then f s else if s = p then f s else 0) := by
        by_cases hsr : s = r
        · simp [hsr]
        · by_cases hsp : s = p
          · simp [hsp]
          · have hprev : s.val + 1 ≠ r.val := by
              intro he
              apply hsp
              apply Fin.ext
              simp [p]
              omega
            have hnext : r.val + 1 ≠ s.val := by omega
            rw [hzero s hsr hprev hnext]
            simp [hsr, hsp]
      have hsum := sum_piecewise_two r p hpr.symm f f
      have hrep : (∑ s, f s) =
          ∑ s, if s = r then f s else if s = p then f s else 0 :=
        Finset.sum_congr rfl fun s _ => hpoint s
      rw [hrep, hsum]
      have hrval : r.val = t - 1 := by omega
      have hp : p = ⟨t - 2, by omega⟩ := by
        apply Fin.ext
        change r.val - 1 = t - 2
        omega
      have hprev : 0 < r.val := by omega
      have hnext : ¬ r.val + 1 < t := by omega
      simp only [dite_eq_left hprev, dite_eq_right hnext]
      rw [hp]
      have hpi : (⟨t - 2, by omega⟩ : Fin t) = ⟨r.val - 1, by omega⟩ := by
        apply Fin.ext
        omega
      rw [hpi]
      simp
    · let p : Fin t := ⟨r.val - 1, by omega⟩
      let n : Fin t := ⟨r.val + 1, by omega⟩
      have hpr : r ≠ p := by
        intro he
        have hv := congrArg Fin.val he
        simp [p] at hv
        omega
      have hrn : r ≠ n := by
        intro he
        have hv := congrArg Fin.val he
        simp [n] at hv
      have hpn : p ≠ n := by
        intro he
        have hv := congrArg Fin.val he
        simp [p, n] at hv
      have hpoint (s : Fin t) :
          f s = (if s = r then f s else if s = p then f s else
            if s = n then f s else 0) := by
        by_cases hsr : s = r
        · simp [hsr]
        · by_cases hsp : s = p
          · simp [hsp]
          · by_cases hsn : s = n
            · simp [hsn]
            · have hprev : s.val + 1 ≠ r.val := by
                intro he
                apply hsp
                apply Fin.ext
                change s.val = r.val - 1
                omega
              have hnext : r.val + 1 ≠ s.val := by
                intro he
                apply hsn
                apply Fin.ext
                change s.val = r.val + 1
                omega
              rw [hzero s hsr hprev hnext]
              simp [hsr, hsp, hsn]
      have hsum := sum_piecewise_three r p n hpr hrn hpn f f f
      have hrep : (∑ s, f s) =
          ∑ s, if s = r then f s else if s = p then f s else
            if s = n then f s else 0 :=
        Finset.sum_congr rfl fun s _ => hpoint s
      rw [hrep, hsum]
      have hprev : 0 < r.val := by omega
      have hnext : r.val + 1 < t := by omega
      simp only [dite_eq_left hprev, dite_eq_left hnext]
      rfl

private lemma chain_path_kernel_rows {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 6 ≤ t) (W : ℤ) (c : Fin t → ℤ)
    (hzero : ∀ j k, j.val + 1 < k.val → T.intersection (i j) (i k) = 0)
    (hdiagInner : ∀ j, 0 < j.val → j.val + 1 < t →
      T.intersection (i j) (i j) = -2 * W)
    (hedgeInner : ∀ j k, k.val = j.val + 1 → 0 < j.val → k.val + 1 < t →
      T.intersection (i j) (i k) = W)
    (hcInner : ∀ j, 0 < j.val → j.val + 1 < t → c j = 2)
    (hrowLeft : T.intersection (i ⟨0, by omega⟩) (i ⟨0, by omega⟩) *
        c ⟨0, by omega⟩ +
      T.intersection (i ⟨0, by omega⟩) (i ⟨1, by omega⟩) * c ⟨1, by omega⟩ = 0)
    (hrowRight : T.intersection (i ⟨t - 1, by omega⟩) (i ⟨t - 1, by omega⟩) *
        c ⟨t - 1, by omega⟩ +
      T.intersection (i ⟨t - 1, by omega⟩) (i ⟨t - 2, by omega⟩) *
        c ⟨t - 2, by omega⟩ = 0)
    (himpactLeft : T.intersection (i ⟨0, by omega⟩) (i ⟨1, by omega⟩) *
        c ⟨0, by omega⟩ = 2 * W)
    (himpactRight : T.intersection (i ⟨t - 1, by omega⟩)
        (i ⟨t - 2, by omega⟩) * c ⟨t - 1, by omega⟩ = 2 * W) :
    ∀ j, ∑ k, T.intersection (i j) (i k) * c k = 0 := by
  classical
  intro j
  have hsupport (k : Fin t) (hkj : k ≠ j) (hprev : k.val + 1 ≠ j.val)
      (hnext : j.val + 1 ≠ k.val) : T.intersection (i j) (i k) * c k = 0 := by
    have hgap : j.val + 1 < k.val ∨ k.val + 1 < j.val := by omega
    rcases hgap with hgap | hgap
    · rw [hzero j k hgap]
      simp
    · rw [T.intersection_symm, hzero k j hgap]
      simp
  have hsum := sum_supported_path_row (t := t) (by omega) j
    (fun k => T.intersection (i j) (i k) * c k) hsupport
  by_cases hj0 : j.val = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext (by simpa using hj0)
    rw [hj] at hsum ⊢
    have h := hsum
    simp only [dite_eq_right (by omega : ¬ 0 < (0 : ℕ)), dite_eq_left (by omega : 0 + 1 < t)] at h
    have h' : ∑ k, T.intersection (i ⟨0, by omega⟩) (i k) * c k =
        T.intersection (i ⟨0, by omega⟩) (i ⟨0, by omega⟩) * c ⟨0, by omega⟩ +
          T.intersection (i ⟨0, by omega⟩) (i ⟨1, by omega⟩) * c ⟨1, by omega⟩ := by
      simpa only [add_zero, Nat.zero_add] using h
    exact h'.trans hrowLeft
  · by_cases hjlast : j.val + 1 = t
    · have hj : j = ⟨t - 1, by omega⟩ := by
        apply Fin.ext
        change j.val = t - 1
        omega
      rw [hj] at hsum ⊢
      have h := hsum
      simp only [dite_eq_left (by omega : 0 < t - 1),
        dite_eq_right (by omega : ¬ t - 1 + 1 < t)] at h
      have h' : ∑ k, T.intersection (i ⟨t - 1, by omega⟩) (i k) * c k =
          T.intersection (i ⟨t - 1, by omega⟩) (i ⟨t - 1, by omega⟩) *
              c ⟨t - 1, by omega⟩ +
            T.intersection (i ⟨t - 1, by omega⟩) (i ⟨t - 2, by omega⟩) *
              c ⟨t - 2, by omega⟩ := by
        have hp : (⟨t - 1 - 1, by omega⟩ : Fin t) = ⟨t - 2, by omega⟩ := by
          apply Fin.ext
          change t - 1 - 1 = t - 2
          omega
        rw [hp] at h
        simpa only [add_zero] using h
      exact h'.trans hrowRight
    · have hjleft : 0 < j.val := by omega
      have hjright : j.val + 1 < t := by omega
      let p : Fin t := ⟨j.val - 1, by omega⟩
      let n : Fin t := ⟨j.val + 1, by omega⟩
      have h := hsum
      simp only [dite_eq_left hjleft, dite_eq_left hjright] at h
      have hdiag := hdiagInner j hjleft hjright
      have hself : c j = 2 := hcInner j hjleft hjright
      have hleftTerm : T.intersection (i j) (i p) * c p = 2 * W := by
        by_cases hfirst : j.val = 1
        · have hp : p = ⟨0, by omega⟩ := by
            apply Fin.ext
            simp [p, hfirst]
          have hj' : j = ⟨1, by omega⟩ := Fin.ext (by omega)
          rw [hj', hp, T.intersection_symm]
          exact himpactLeft
        · have hprev : 0 < j.val - 1 := by omega
          have hedge : T.intersection (i p) (i j) = W := by
            apply hedgeInner p j
            · simp [p]
              omega
            · exact hprev
            · exact hjright
          have hprevRight : j.val - 1 + 1 < t := by omega
          rw [T.intersection_symm, hedge, hcInner p hprev hprevRight]
          omega
      have hrightTerm : T.intersection (i j) (i n) * c n = 2 * W := by
        by_cases hlast : j.val + 2 = t
        · have hn : n = ⟨t - 1, by omega⟩ := by
            apply Fin.ext
            change j.val + 1 = t - 1
            omega
          have hj' : j = ⟨t - 2, by omega⟩ := by
            apply Fin.ext
            change j.val = t - 2
            omega
          rw [hj', hn, T.intersection_symm]
          exact himpactRight
        · have hedge : T.intersection (i j) (i n) = W := by
            have hnextRight : j.val + 2 < t := by omega
            apply hedgeInner j n
            · simp [n]
            · exact hjleft
            · simp [n]
              omega
          have hnleft : 0 < n.val := by change 0 < j.val + 1; omega
          have hnright : n.val + 1 < t := by change j.val + 2 < t; omega
          rw [hedge, hcInner n hnleft hnright]
          omega
      rw [hdiag, hself, hleftTerm, hrightTerm] at h
      omega

private lemma quadraticForm_finite_support {ι κ : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℝ) (i : ι → κ) (c : ι → ℝ)
    (_hinj : Function.Injective i) :
    (fun a => ∑ r, if a = i r then c r else 0) ⬝ᵥ
      (A *ᵥ fun a => ∑ r, if a = i r then c r else 0) =
      ∑ r, c r * ∑ s, A (i r) (i s) * c s := by
  classical
  simp only [dotProduct, Matrix.mulVec]
  have hinner (a : κ) :
      (∑ b, A a b * (∑ s, if b = i s then c s else 0)) =
        ∑ s, A a (i s) * c s :=
    by simpa [mul_comm] using sum_single_support i c (A a)
  simp_rw [hinner]
  have houter := sum_single_support i c (fun a => ∑ s, A a (i s) * c s)
  simpa [mul_comm] using houter

private lemma proper_path_kernel_impossible {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 0 < t)
    (hproper : t < T.componentCount) (hinj : Function.Injective i)
    (c : Fin t → ℝ) (hc0 : 0 < c ⟨0, ht⟩)
    (hrows : ∀ r, ∑ s, (T.intersection (i r) (i s) : ℝ) * c s = 0) : False := by
  classical
  let I : Set (Fin T.componentCount) := Set.range i
  have hIne : I.Nonempty := ⟨i ⟨0, ht⟩, ⟨⟨0, ht⟩, rfl⟩⟩
  have hIproper : I ≠ Set.univ := by
    intro hI
    have hsurj : Function.Surjective i := by
      intro a
      have ha : a ∈ I := by rw [hI]; simp
      simpa [I] using ha
    have hcard : T.componentCount ≤ t := by
      simpa using Fintype.card_le_of_surjective i hsurj
    omega
  let x : Fin T.componentCount → ℝ := fun a =>
    ∑ r, if a = i r then c r else 0
  have hxout : ∀ a, a ∉ I → x a = 0 := by
    intro a ha
    dsimp [x]
    apply Finset.sum_eq_zero
    intro r hr
    have hne : a ≠ i r := fun he => ha ⟨r, he.symm⟩
    simp [hne]
  have hx0 : x (i (⟨0, ht⟩ : Fin t)) = c ⟨0, ht⟩ := by
    dsimp [x]
    have hterm (r : Fin t) :
        (if i (⟨0, ht⟩ : Fin t) = i r then c r else 0) =
          if r = (⟨0, ht⟩ : Fin t) then c r else 0 := by
      by_cases hr : r = (⟨0, ht⟩ : Fin t)
      · subst r
        simp
      · have hne : i (⟨0, ht⟩ : Fin t) ≠ i r := by
          intro he
          exact hr (hinj he).symm
        simp [hr, hne]
    simp_rw [hterm]
    simp
  have hx : ∃ a, x a ≠ 0 := ⟨i ⟨0, ht⟩, by rw [hx0]; exact ne_of_gt hc0⟩
  let A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℝ :=
    fun a b => (T.intersection a b : ℝ)
  have hquad : x ⬝ᵥ (A *ᵥ x) = 0 := by
    rw [quadraticForm_finite_support A i c hinj]
    simp only [A]
    simp [hrows]
  have hnegative := quadraticForm_lt_zero_of_proper_support T x I hIne hIproper
    hxout hx
  exact (ne_of_lt hnegative) hquad

lemma two_special_endpoints_impossible {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 6 ≤ t)
    (hproper : t < T.componentCount) (hinj : Function.Injective i)
    (hminusTwo : ∀ j, IsMinusTwoIndex T (i j)) (W : ℤ) (_hW : 0 < W)
    (hweights : ∀ j, 0 < j.val → j.val + 1 < t → T.weight (i j) = W)
    (hedges : ∀ j k, k.val = j.val + 1 → 0 < j.val → k.val + 1 < t →
      T.intersection (i j) (i k) = W)
    (hzero : ∀ j k, j.val + 1 < k.val → T.intersection (i j) (i k) = 0)
    (hleft : (T.weight (i ⟨0, by omega⟩) = 2 * W ∧
        T.intersection (i ⟨0, by omega⟩) (i ⟨1, by omega⟩) = 2 * W) ∨
      (2 * T.weight (i ⟨0, by omega⟩) = W ∧
        T.intersection (i ⟨0, by omega⟩) (i ⟨1, by omega⟩) = W))
    (hright : (T.weight (i ⟨t - 1, by omega⟩) = 2 * W ∧
        T.intersection (i ⟨t - 1, by omega⟩) (i ⟨t - 2, by omega⟩) = 2 * W) ∨
      (2 * T.weight (i ⟨t - 1, by omega⟩) = W ∧
        T.intersection (i ⟨t - 1, by omega⟩) (i ⟨t - 2, by omega⟩) = W)) : False := by
  classical
  have hz : ∀ j, 0 < j.val → j.val + 1 < t →
      T.intersection (i j) (i j) = -2 * W := by
    intro j hj hj'
    rw [(hminusTwo j).2, hweights j hj hj']
  have endpoint (x y : Fin T.componentCount) (hx : IsMinusTwoIndex T x)
      (h : (T.weight x = 2 * W ∧ T.intersection x y = 2 * W) ∨
        (2 * T.weight x = W ∧ T.intersection x y = W)) :
      ∃ a : ℤ, 0 < a ∧ T.intersection x x * a + T.intersection x y * 2 = 0 ∧
        T.intersection x y * a = 2 * W := by
    rw [hx.2]
    rcases h with ⟨hw, he⟩ | ⟨hw, he⟩
    · exact ⟨1, by norm_num, by omega, by omega⟩
    · exact ⟨2, by norm_num, by omega, by omega⟩
  obtain ⟨a, ha, hrowL, hiL⟩ := endpoint _ _ (hminusTwo _) hleft
  obtain ⟨b, hb, hrowR, hiR⟩ := endpoint _ _ (hminusTwo _) hright
  let c : Fin t → ℤ := fun j => if j.val = 0 then a else if j.val + 1 = t then b else 2
  have hc0 : c ⟨0, by omega⟩ = a := by simp [c]
  have hclast : c ⟨t - 1, by omega⟩ = b := by simp [c]; omega
  have hcInner : ∀ j, 0 < j.val → j.val + 1 < t → c j = 2 := by
    intro j hj hj'
    simp [c, Nat.ne_of_gt hj, Nat.ne_of_lt hj']
  have hc1 : c ⟨1, by omega⟩ = 2 := by simp [c]; omega
  have hcp : c ⟨t - 2, by omega⟩ = 2 := by simp [c]; omega
  have hrowsZ := chain_path_kernel_rows T i ht W c hzero hz hedges hcInner
    (by rw [hc0, hc1]; exact hrowL) (by rw [hclast, hcp]; exact hrowR)
    (by rw [hc0]; exact hiL) (by rw [hclast]; exact hiR)
  refine proper_path_kernel_impossible T i (by omega) hproper hinj
    (fun j => (c j : ℝ)) (by simpa [hc0] using ha) fun j => ?_
  exact_mod_cast hrowsZ j

end AlgebraicGeometry.NumericalType
