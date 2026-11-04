module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FiveChain
public import Mathlib.Basic.Real.Basic
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.LongChain.PathKernel
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.LongChain.NonconsecutiveIntersection

/-!
# Classification of long chains of minus-two indices

A chain of at least five minus-two indices in a numerical type with more
components than the chain is, up to reversal, a chain of type `A`, `B`, `C` or
`D` with prescribed weights and edge intersection numbers.

## Main definitions

* `AlgebraicGeometry.NumericalType.IsLongChainConfiguration`.

## Main results

* `AlgebraicGeometry.NumericalType.classify_long_chain_of_minus_two_indices`.

## References

* [Stacks Project, Tag 0C89](https://stacks.math.columbia.edu/tag/0C89)
-/

@[expose] public section

open Matrix

namespace AlgebraicGeometry.NumericalType

private abbrev IsFiveConfiguration (T : NumericalType) (v : Fin 5 → Fin T.componentCount)
    (w : ℤ) : Prop :=
  IsA5Configuration T v w ∨ IsC5Configuration T v w ∨
    IsB5Configuration T v w

private abbrev EndpointScale (T : NumericalType) (v : Fin 5 → Fin T.componentCount)
    (r s : Fin 5) (W : ℤ) : Prop := ChainEndpointScale T (v r) (v s) W

private lemma five_configuration_middle_data (T : NumericalType)
    (v : Fin 5 → Fin T.componentCount)
    (hconfig : ∃ w, IsFiveConfiguration T v w) :
    ∃ W : ℤ, 0 < W ∧
      T.weight (v 1) = W ∧ T.weight (v 2) = W ∧ T.weight (v 3) = W ∧
      T.intersection (v 1) (v 2) = W ∧ T.intersection (v 2) (v 3) = W ∧
      EndpointScale T v 0 1 W ∧ EndpointScale T v 4 3 W := by
  have hpos := T.weight_pos (v 1)
  rcases hconfig with ⟨w, ⟨hweights, hmatrix, _⟩ | ⟨hweights, hmatrix, _⟩ |
      ⟨hweights, hmatrix, _⟩⟩ <;>
    replace hweights := congrFun hweights <;>
    replace hmatrix := fun r s => congrFun (congrFun hmatrix r) s
  · refine ⟨w, ?_, ?_⟩ <;> simp_all [EndpointScale, ChainEndpointScale]
  · refine ⟨w, ?_, ?_⟩ <;> simp_all [EndpointScale, ChainEndpointScale]
  · refine ⟨2 * w, ?_, ?_⟩ <;> simp_all [EndpointScale, ChainEndpointScale]

/-- The components `i 0, …, i (t - 1)` form a chain of one of three shapes: there is `w` with
all weights and all intersections of consecutive components equal to `w`; or the same except that
the last component has weight `2 * w` and meets its neighbour with intersection `2 * w`; or all
weights except the last one, and all consecutive intersections, are `2 * w` while the last weight
is `w`. In each case non-consecutive components do not meet. -/
public abbrev IsLongChainConfiguration {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) : Prop :=
  (∃ w : ℤ,
      (∀ j, T.weight (i j) = w) ∧
      (∀ j k, k.val = j.val + 1 → T.intersection (i j) (i k) = w) ∧
      (∀ j k, j.val + 1 < k.val → T.intersection (i j) (i k) = 0)) ∨
  (∃ w : ℤ,
      (∀ j, j.val + 1 < t → T.weight (i j) = w) ∧
      (∀ j, j.val + 1 = t → T.weight (i j) = 2 * w) ∧
      (∀ j k, k.val = j.val + 1 → k.val + 1 < t →
        T.intersection (i j) (i k) = w) ∧
      (∀ j k, k.val = j.val + 1 → k.val + 1 = t →
        T.intersection (i j) (i k) = 2 * w) ∧
      (∀ j k, j.val + 1 < k.val → T.intersection (i j) (i k) = 0)) ∨
  (∃ w : ℤ,
      (∀ j, j.val + 1 < t → T.weight (i j) = 2 * w) ∧
      (∀ j, j.val + 1 = t → T.weight (i j) = w) ∧
      (∀ j k, k.val = j.val + 1 → T.intersection (i j) (i k) = 2 * w) ∧
      (∀ j k, j.val + 1 < k.val → T.intersection (i j) (i k) = 0))

private lemma build_oriented_long_chain {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 6 ≤ t) (W : ℤ)
    (hweights : ∀ j, 0 < j.val → j.val + 1 < t → T.weight (i j) = W)
    (hedges : ∀ j k, k.val = j.val + 1 → 0 < j.val → k.val + 1 < t →
      T.intersection (i j) (i k) = W)
    (hzero : ∀ j k, j.val + 1 < k.val → T.intersection (i j) (i k) = 0)
    (hleft : T.weight (i ⟨0, by omega⟩) = W ∧
      T.intersection (i ⟨0, by omega⟩) (i ⟨1, by omega⟩) = W)
    (hright : ChainEndpointScale T (i ⟨t - 1, by omega⟩)
      (i ⟨t - 2, by omega⟩) W) : IsLongChainConfiguration T i := by
  have hwFirst (j : Fin t) (hj0 : j.val = 0) : T.weight (i j) = W := by
    rw [show j = ⟨0, by omega⟩ from Fin.ext hj0]
    exact hleft.1
  have hwEnd (j : Fin t) (hj : j.val + 1 = t) :
      T.weight (i j) = T.weight (i ⟨t - 1, by omega⟩) :=
    congrArg (fun x => T.weight (i x))
      (Fin.ext (show j.val = t - 1 by omega) : j = ⟨t - 1, by omega⟩)
  have heFirst (j k : Fin t) (hstep : k.val = j.val + 1) (hj0 : j.val = 0) :
      T.intersection (i j) (i k) = W := by
    rw [show j = ⟨0, by omega⟩ from Fin.ext hj0,
      show k = ⟨1, by omega⟩ from Fin.ext (show k.val = 1 by omega)]
    exact hleft.2
  have heEnd (j k : Fin t) (hstep : k.val = j.val + 1) (hk : k.val + 1 = t) :
      T.intersection (i j) (i k) =
        T.intersection (i ⟨t - 1, by omega⟩) (i ⟨t - 2, by omega⟩) := by
    rw [T.intersection_symm]
    exact congrArg₂ (fun x y => T.intersection (i x) (i y))
      (Fin.ext (show k.val = t - 1 by omega) : k = ⟨t - 1, by omega⟩)
      (Fin.ext (show j.val = t - 2 by omega) : j = ⟨t - 2, by omega⟩)
  rcases hright with ⟨hwLast, heLast⟩ | ⟨hwLast, heLast⟩ | ⟨hwLast, heLast⟩
  · left
    refine ⟨W, fun j => ?_, fun j k hstep => ?_, hzero⟩
    · by_cases hj0 : j.val = 0
      · exact hwFirst j hj0
      by_cases hjl : j.val + 1 = t
      · exact (hwEnd j hjl).trans hwLast
      exact hweights j (by omega) (by omega)
    · by_cases hj0 : j.val = 0
      · exact heFirst j k hstep hj0
      by_cases hkl : k.val + 1 = t
      · exact (heEnd j k hstep hkl).trans heLast
      exact hedges j k hstep (by omega) (by omega)
  · right
    left
    refine ⟨W, fun j hj => ?_, fun j hj => (hwEnd j hj).trans hwLast, fun j k hstep hk => ?_,
      fun j k hstep hk => (heEnd j k hstep hk).trans heLast, hzero⟩
    · by_cases hj0 : j.val = 0
      · exact hwFirst j hj0
      exact hweights j (by omega) (by omega)
    · by_cases hj0 : j.val = 0
      · exact heFirst j k hstep hj0
      exact hedges j k hstep (by omega) (by omega)
  · right
    right
    refine ⟨T.weight (i ⟨t - 1, by omega⟩), fun j hj => ?_, hwEnd, fun j k hstep => ?_, hzero⟩
    · by_cases hj0 : j.val = 0
      · rw [hwFirst j hj0]
        omega
      have hwj := hweights j (by omega) (by omega)
      omega
    · by_cases hj0 : j.val = 0
      · rw [heFirst j k hstep hj0]
        omega
      by_cases hkl : k.val + 1 = t
      · rw [heEnd j k hstep hkl]
        omega
      have hedge := hedges j k hstep (by omega) (by omega)
      omega

private lemma classify_initial_five {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 5 ≤ t)
    (hproper : t < T.componentCount) (hinj : Function.Injective i)
    (hminusTwo : ∀ j, IsMinusTwoIndex T (i j))
    (hadjacent : ∀ j k, k.val = j.val + 1 →
      T.intersection (i j) (i k) ≠ 0) :
    ∃ σ : Equiv.Perm (Fin 5), ∃ w : ℤ, 0 < w ∧
      (IsA5Configuration T (fun r => i ⟨(σ r).val, by omega⟩) w ∨
       IsC5Configuration T (fun r => i ⟨(σ r).val, by omega⟩) w ∨
       IsB5Configuration T (fun r => i ⟨(σ r).val, by omega⟩) w) := by
  let e : Fin 5 → Fin t := fun r => ⟨r.val, by omega⟩
  have hein : Function.Injective e := by
    intro x y h
    apply Fin.ext
    simpa [e] using congrArg Fin.val h
  have hadj : ∀ r : Fin 4,
      T.intersection (i (e r.castSucc)) (i (e r.succ)) ≠ 0 := by
    intro r
    apply hadjacent
    simp [e]
  obtain ⟨σ, w, hw, hconfig⟩ :=
    five_chain_is_A5_or_C5_or_B5 T (by omega) (fun r => i (e r))
      (hinj.comp hein) (fun r => hminusTwo (e r)) hadj
  refine ⟨σ, w, hw, ?_⟩
  simpa [e] using hconfig

private lemma nonzero_edge_in_five_configuration_is_adjacent
    (T : NumericalType) (v : Fin 5 → Fin T.componentCount)
    (hconfig : ∃ w, IsFiveConfiguration T v w)
    (r s : Fin 5) (hrs : r ≠ s)
    (hne : T.intersection (v r) (v s) ≠ 0) :
    r.val + 1 = s.val ∨ s.val + 1 = r.val := by
  rcases hconfig with ⟨_, ⟨_, hmat, _⟩ | ⟨_, hmat, _⟩ | ⟨_, hmat, _⟩⟩
  all_goals
    have hentry := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℤ => M r s) hmat
    change T.intersection (v r) (v s) = _ at hentry
    rw [hentry] at hne
    fin_cases r <;> fin_cases s <;> simp_all [Matrix.of_apply]

private lemma path_order_on_five_vertices (f : Fin 5 → Fin 5)
    (hf : Function.Injective f)
    (hadj : ∀ r : Fin 4,
      (f r.castSucc).val + 1 = (f r.succ).val ∨
      (f r.succ).val + 1 = (f r.castSucc).val) :
    (∀ r, f r = r) ∨ (∀ r, f r = Fin.rev r) := by
  have h01 : (f 0).val + 1 = (f 1).val ∨ (f 1).val + 1 = (f 0).val := by
    simpa using hadj (0 : Fin 4)
  have h12 : (f 1).val + 1 = (f 2).val ∨ (f 2).val + 1 = (f 1).val := by
    simpa using hadj (1 : Fin 4)
  have h23 : (f 2).val + 1 = (f 3).val ∨ (f 3).val + 1 = (f 2).val := by
    simpa using hadj (2 : Fin 4)
  have h34 : (f 3).val + 1 = (f 4).val ∨ (f 4).val + 1 = (f 3).val := by
    simpa using hadj (3 : Fin 4)
  have h02 : (f 0).val ≠ (f 2).val := fun h => absurd (hf (Fin.ext h)) (by decide)
  have h13 : (f 1).val ≠ (f 3).val := fun h => absurd (hf (Fin.ext h)) (by decide)
  have h24 : (f 2).val ≠ (f 4).val := fun h => absurd (hf (Fin.ext h)) (by decide)
  have := (f 0).isLt
  have := (f 4).isLt
  rcases (by omega : ((f 0).val = 0 ∧ (f 1).val = 1 ∧ (f 2).val = 2 ∧ (f 3).val = 3 ∧
      (f 4).val = 4) ∨ ((f 0).val = 4 ∧ (f 1).val = 3 ∧ (f 2).val = 2 ∧ (f 3).val = 1 ∧
      (f 4).val = 0)) with hvals | hvals
  · left
    intro r
    fin_cases r <;> apply Fin.ext <;> simp_all
  · right
    intro r
    fin_cases r <;> apply Fin.ext <;> simp_all [Fin.rev]

private lemma classify_initial_five_up_to_reverse {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 5 ≤ t)
    (hproper : t < T.componentCount) (hinj : Function.Injective i)
    (hminusTwo : ∀ j, IsMinusTwoIndex T (i j))
    (hadjacent : ∀ j k, k.val = j.val + 1 →
      T.intersection (i j) (i k) ≠ 0) :
    ∃ w : ℤ, 0 < w ∧
      (IsFiveConfiguration T (fun r => i ⟨r.val, by omega⟩) w ∨
       IsFiveConfiguration T (fun r => i ⟨(Fin.rev r).val, by omega⟩) w) := by
  obtain ⟨σ, w, hw, hc⟩ := classify_initial_five T i ht hproper hinj hminusTwo hadjacent
  let e : Fin 5 → Fin t := fun r => ⟨r.val, by omega⟩
  let f : Fin 5 → Fin 5 := σ.symm
  let v : Fin 5 → Fin T.componentCount := fun r => i (e (σ r))
  have hcin : IsFiveConfiguration T v w := by
    simpa [IsFiveConfiguration, v, e] using hc
  have hf : Function.Injective f := σ.symm.injective
  have hpath : ∀ r : Fin 4,
      (f r.castSucc).val + 1 = (f r.succ).val ∨
      (f r.succ).val + 1 = (f r.castSucc).val := by
    intro r
    have hindices : r.castSucc ≠ r.succ := by
      intro h
      have : r.castSucc.val ≠ r.succ.val := by simp
      exact this (congrArg Fin.val h)
    have hne : f r.castSucc ≠ f r.succ := fun h => hindices (hf h)
    have hnonzero : T.intersection (v (f r.castSucc)) (v (f r.succ)) ≠ 0 := by
      have hstep : (e r.succ).val = (e r.castSucc).val + 1 := by simp [e]
      simpa [v, f, e] using hadjacent (e r.castSucc) (e r.succ) hstep
    exact nonzero_edge_in_five_configuration_is_adjacent T v ⟨w, hcin⟩
      (f r.castSucc) (f r.succ) hne hnonzero
  obtain horder | horder := path_order_on_five_vertices f hf hpath
  · refine ⟨w, hw, Or.inl ?_⟩
    have hσ : ∀ r, σ r = r := fun r => by simpa [f] using (congrArg σ (horder r)).symm
    have hv : v = fun r => i (e r) := by
      funext r
      simp [v, e, hσ]
    rwa [hv] at hcin
  · refine ⟨w, hw, Or.inr ?_⟩
    have hσ : ∀ r, σ r = Fin.rev r := fun r => by
      simpa [f, Fin.rev_rev] using (congrArg σ (horder (Fin.rev r))).symm
    have hv : v = fun r => i (e (Fin.rev r)) := by
      funext r
      simp [v, e, hσ]
    rwa [hv] at hcin

private lemma classify_chain_window {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount)
    (hproper : t < T.componentCount) (hinj : Function.Injective i)
    (hminusTwo : ∀ j, IsMinusTwoIndex T (i j))
    (hadjacent : ∀ j k, k.val = j.val + 1 →
      T.intersection (i j) (i k) ≠ 0) (s : ℕ) (hs : s + 4 < t) :
    ∃ W : ℤ, 0 < W ∧
      (IsFiveConfiguration T (fun r => i ⟨s + r.val, by omega⟩) W ∨
       IsFiveConfiguration T (fun r => i ⟨s + (Fin.rev r).val, by omega⟩) W) := by
  let v : Fin 5 → Fin T.componentCount := fun r => i ⟨s + r.val, by omega⟩
  have hv : Function.Injective v := by
    intro a b hab
    have hab' : (⟨s + a.val, by omega⟩ : Fin t) = ⟨s + b.val, by omega⟩ :=
      hinj (by simpa [v] using hab)
    apply Fin.ext
    have hval := congrArg Fin.val hab'
    simp at hval
    omega
  have hminus : ∀ r, IsMinusTwoIndex T (v r) := fun _ => hminusTwo _
  have hcount : 5 < T.componentCount := by omega
  obtain ⟨W, hW, hc⟩ := classify_initial_five_up_to_reverse T v le_rfl hcount
    hv hminus (fun j k hjk => by
      let j' : Fin t := ⟨s + j.val, by omega⟩
      let k' : Fin t := ⟨s + k.val, by omega⟩
      have hstep : k'.val = j'.val + 1 := by simp [j', k']; omega
      simpa [v, j', k'] using hadjacent j' k' hstep)
  refine ⟨W, hW, ?_⟩
  simpa [v] using hc

private abbrev ChainWindowData {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (s : ℕ) (hs : s + 4 < t) (W : ℤ) : Prop :=
  T.weight (i ⟨s + 1, by omega⟩) = W ∧
  T.weight (i ⟨s + 2, by omega⟩) = W ∧
  T.weight (i ⟨s + 3, by omega⟩) = W ∧
  T.intersection (i ⟨s + 1, by omega⟩) (i ⟨s + 2, by omega⟩) = W ∧
  T.intersection (i ⟨s + 2, by omega⟩) (i ⟨s + 3, by omega⟩) = W ∧
  ChainEndpointScale T (i ⟨s, by omega⟩) (i ⟨s + 1, by omega⟩) W ∧
  ChainEndpointScale T (i ⟨s + 4, by omega⟩) (i ⟨s + 3, by omega⟩) W

private lemma chain_window_middle_data {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount)
    (hproper : t < T.componentCount) (hinj : Function.Injective i)
    (hminusTwo : ∀ j, IsMinusTwoIndex T (i j))
    (hadjacent : ∀ j k, k.val = j.val + 1 →
      T.intersection (i j) (i k) ≠ 0) (s : ℕ) (hs : s + 4 < t) :
    ∃ W : ℤ, 0 < W ∧ ChainWindowData T i s hs W := by
  let v : Fin 5 → Fin T.componentCount := fun r => i ⟨s + r.val, by omega⟩
  obtain ⟨w, hw, hc⟩ := classify_chain_window T i hproper hinj hminusTwo hadjacent s hs
  rcases hc with hc | hc
  · obtain ⟨W, hW, h1, h2, h3, h12, h23, h0, h4⟩ :=
      five_configuration_middle_data T v ⟨w, hc⟩
    refine ⟨W, hW, ?_⟩
    simpa [ChainWindowData, v, EndpointScale, ChainEndpointScale] using
      (show T.weight (v 1) = W ∧ T.weight (v 2) = W ∧ T.weight (v 3) = W ∧
        T.intersection (v 1) (v 2) = W ∧ T.intersection (v 2) (v 3) = W ∧
        ChainEndpointScale T (v 0) (v 1) W ∧ ChainEndpointScale T (v 4) (v 3) W
        from ⟨h1, h2, h3, h12, h23, h0, h4⟩)
  · let vr : Fin 5 → Fin T.componentCount := fun r => v (Fin.rev r)
    obtain ⟨W, hW, h1, h2, h3, h12, h23, h0, h4⟩ :=
      five_configuration_middle_data T vr ⟨w, hc⟩
    refine ⟨W, hW, ?_⟩
    have hr0 : Fin.rev (0 : Fin 5) = 4 := by decide
    have hr1 : Fin.rev (1 : Fin 5) = 3 := by decide
    have hr2 : Fin.rev (2 : Fin 5) = 2 := by decide
    have hr3 : Fin.rev (3 : Fin 5) = 1 := by decide
    have hr4 : Fin.rev (4 : Fin 5) = 0 := by decide
    have hv0 : (0 : Fin 5).val = 0 := by decide
    have hv1 : (1 : Fin 5).val = 1 := by decide
    have hv2 : (2 : Fin 5).val = 2 := by decide
    have hv3 : (3 : Fin 5).val = 3 := by decide
    have hv4 : (4 : Fin 5).val = 4 := by decide
    have hwt1 : T.weight (i ⟨s + 1, by omega⟩) = W := by
      simpa only [vr, hr3, v, hv1, hv2, hv3] using h3
    have hwt2 : T.weight (i ⟨s + 2, by omega⟩) = W := by
      simpa only [vr, hr2, v, hv1, hv2, hv3] using h2
    have hwt3 : T.weight (i ⟨s + 3, by omega⟩) = W := by
      simpa only [vr, hr1, v, hv1, hv2, hv3] using h1
    have hedge1 : T.intersection (i ⟨s + 1, by omega⟩)
        (i ⟨s + 2, by omega⟩) = W := by
      rw [← T.intersection_symm]
      simpa only [vr, hr2, hr3, v, hv1, hv2, hv3] using h23
    have hedge2 : T.intersection (i ⟨s + 2, by omega⟩)
        (i ⟨s + 3, by omega⟩) = W := by
      rw [← T.intersection_symm]
      simpa only [vr, hr1, hr2, v, hv1, hv2, hv3] using h12
    have hleft : ChainEndpointScale T (i ⟨s, by omega⟩)
        (i ⟨s + 1, by omega⟩) W := by
      simpa only [vr, hr3, hr4, v, hv0, hv1, hv3, hv4, Nat.add_zero,
        EndpointScale] using h4
    have hright : ChainEndpointScale T (i ⟨s + 4, by omega⟩)
        (i ⟨s + 3, by omega⟩) W := by
      simpa only [vr, hr0, hr1, v, hv0, hv1, hv3, hv4, EndpointScale] using h0
    exact ⟨hwt1, hwt2, hwt3, hedge1, hedge2, hleft, hright⟩

private lemma adjacent_chain_window_scales_equal {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (s : ℕ)
    (hs : s + 4 < t) (hs' : s + 1 + 4 < t) (W W' : ℤ)
    (hfirst : ChainWindowData T i s hs W)
    (hsecond : ChainWindowData T i (s + 1) hs' W') : W = W' := by
  rcases hfirst with ⟨_, _, _, _, hedgeFirst, _, _⟩
  rcases hsecond with ⟨_, _, _, hedgeSecond, _, _, _⟩
  have hedgeSecond' :
      T.intersection (i ⟨s + 2, by omega⟩) (i ⟨s + 3, by omega⟩) = W' := by
    simpa [Nat.add_assoc] using hedgeSecond
  exact hedgeFirst.symm.trans hedgeSecond'

private lemma fixed_chain_window_data {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 6 ≤ t)
    (hproper : t < T.componentCount) (hinj : Function.Injective i)
    (hminusTwo : ∀ j, IsMinusTwoIndex T (i j))
    (hadjacent : ∀ j k, k.val = j.val + 1 →
      T.intersection (i j) (i k) ≠ 0) :
    ∃ W : ℤ, 0 < W ∧
      ∀ s : ℕ, ∀ hs : s + 4 < t, ChainWindowData T i s hs W := by
  obtain ⟨W, hW, hzero⟩ := chain_window_middle_data T i hproper hinj hminusTwo
    hadjacent 0 (by omega)
  refine ⟨W, hW, ?_⟩
  intro s
  induction s with
  | zero =>
      intro hs
      exact hzero
  | succ s ih =>
      intro hs
      have hsPrev : s + 4 < t := by omega
      have hprev := ih hsPrev
      obtain ⟨W', hW', hnext⟩ := chain_window_middle_data T i hproper hinj
        hminusTwo hadjacent (s + 1) hs
      have hscale := adjacent_chain_window_scales_equal T i s hsPrev hs W W'
        hprev hnext
      rw [← hscale] at hnext
      exact hnext

private lemma internal_vertex_weight {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 6 ≤ t) (W : ℤ)
    (hfixed : ∀ s : ℕ, ∀ hs : s + 4 < t, ChainWindowData T i s hs W)
    (j : Fin t) (hjleft : 0 < j.val) (hjright : j.val + 1 < t) :
    T.weight (i j) = W := by
  by_cases hfirst : j.val = 1
  · have hd := hfixed 0 (by omega)
    rcases hd with ⟨h1, _, _, _, _, _, _⟩
    have heq : j = ⟨1, by omega⟩ := Fin.ext (by simpa using hfirst)
    rw [heq]
    simpa using h1
  · by_cases hlast : j.val + 2 = t
    · have hd := hfixed (t - 5) (by omega)
      rcases hd with ⟨_, _, h3, _, _, _, _⟩
      have hjval : j.val = t - 2 := by omega
      have hlastval : (t - 5) + 3 = t - 2 := by omega
      have heq : j = ⟨(t - 5) + 3, by omega⟩ := by
        apply Fin.ext
        simp only [hjval, hlastval]
      rw [heq]
      exact h3
    · let s := j.val - 2
      have hs : s + 4 < t := by dsimp [s]; omega
      have hd := hfixed s hs
      rcases hd with ⟨_, h2, _, _, _, _, _⟩
      have heq : j = ⟨s + 2, by omega⟩ := by
        apply Fin.ext
        dsimp [s]
        omega
      rw [heq]
      exact h2

private lemma internal_edge_weight {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 6 ≤ t) (W : ℤ)
    (hfixed : ∀ s : ℕ, ∀ hs : s + 4 < t, ChainWindowData T i s hs W)
    (j k : Fin t) (hstep : k.val = j.val + 1)
    (hjleft : 0 < j.val) (hkright : k.val + 1 < t) :
    T.intersection (i j) (i k) = W := by
  by_cases hmiddle : j.val + 3 < t
  · let s := j.val - 1
    have hs : s + 4 < t := by dsimp [s]; omega
    have hd := hfixed s hs
    rcases hd with ⟨_, _, _, hedge, _, _, _⟩
    have heqj : j = ⟨s + 1, by omega⟩ := by
      apply Fin.ext
      dsimp [s]
      omega
    have heqk : k = ⟨s + 2, by omega⟩ := by
      apply Fin.ext
      dsimp [s]
      omega
    simpa only [heqj, heqk] using hedge
  · have hlast : j.val + 3 = t := by omega
    have hd := hfixed (t - 5) (by omega)
    rcases hd with ⟨_, _, _, _, hedge, _, _⟩
    have hjval : j.val = t - 3 := by omega
    have hkval : k.val = t - 2 := by omega
    have heqj : j = ⟨(t - 5) + 2, by omega⟩ := by
      apply Fin.ext
      simp only [hjval]
      omega
    have heqk : k = ⟨(t - 5) + 3, by omega⟩ := by
      apply Fin.ext
      simp only [hkval]
      omega
    simpa only [heqj, heqk] using hedge

private lemma endpoint_scales_of_fixed_windows {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 6 ≤ t) (W : ℤ)
    (hfixed : ∀ s : ℕ, ∀ hs : s + 4 < t, ChainWindowData T i s hs W) :
    ChainEndpointScale T (i ⟨0, by omega⟩) (i ⟨1, by omega⟩) W ∧
    ChainEndpointScale T (i ⟨t - 1, by omega⟩) (i ⟨t - 2, by omega⟩) W := by
  have hfirst := hfixed 0 (by omega)
  have hlast := hfixed (t - 5) (by omega)
  rcases hfirst with ⟨_, _, _, _, _, hleft, _⟩
  rcases hlast with ⟨_, _, _, _, _, _, hright⟩
  constructor
  · simpa [Nat.zero_add] using hleft
  · have hidx1 : (t - 5) + 4 = t - 1 := by omega
    have hidx2 : (t - 5) + 3 = t - 2 := by omega
    simpa only [hidx1, hidx2] using hright

private lemma chain_basic_data {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 6 ≤ t)
    (hproper : t < T.componentCount) (hinj : Function.Injective i)
    (hminusTwo : ∀ j, IsMinusTwoIndex T (i j))
    (hadjacent : ∀ j k, k.val = j.val + 1 →
      T.intersection (i j) (i k) ≠ 0) :
    ∃ W : ℤ, 0 < W ∧
      (∀ j, 0 < j.val → j.val + 1 < t → T.weight (i j) = W) ∧
      (∀ j k, k.val = j.val + 1 → 0 < j.val → k.val + 1 < t →
        T.intersection (i j) (i k) = W) ∧
      ChainEndpointScale T (i ⟨0, by omega⟩) (i ⟨1, by omega⟩) W ∧
      ChainEndpointScale T (i ⟨t - 1, by omega⟩) (i ⟨t - 2, by omega⟩) W := by
  obtain ⟨W, hW, hfixed⟩ := fixed_chain_window_data T i ht hproper hinj hminusTwo
    hadjacent
  exact ⟨W, hW, internal_vertex_weight T i ht W hfixed, internal_edge_weight T i ht W hfixed,
    endpoint_scales_of_fixed_windows T i ht W hfixed⟩

private lemma build_reversed_oriented_long_chain {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 6 ≤ t) (W : ℤ)
    (hweights : ∀ j, 0 < j.val → j.val + 1 < t → T.weight (i j) = W)
    (hedges : ∀ j k, k.val = j.val + 1 → 0 < j.val → k.val + 1 < t →
      T.intersection (i j) (i k) = W)
    (hzero : ∀ j k, j.val + 1 < k.val → T.intersection (i j) (i k) = 0)
    (hleft : ChainEndpointScale T (i ⟨0, by omega⟩) (i ⟨1, by omega⟩) W)
    (hright : T.weight (i ⟨t - 1, by omega⟩) = W ∧
      T.intersection (i ⟨t - 1, by omega⟩) (i ⟨t - 2, by omega⟩) = W) :
    IsLongChainConfiguration T (fun j => i (Fin.rev j)) := by
  let ri : Fin t → Fin T.componentCount := fun j => i (Fin.rev j)
  have hrevweights : ∀ j, 0 < j.val → j.val + 1 < t → T.weight (ri j) = W :=
    fun j hj hj' => hweights (Fin.rev j) (by simp [Fin.rev]; omega) (by simp [Fin.rev]; omega)
  have hrevedges : ∀ j k, k.val = j.val + 1 → 0 < j.val → k.val + 1 < t →
      T.intersection (ri j) (ri k) = W := by
    intro j k hstep hj hk
    change T.intersection (i (Fin.rev j)) (i (Fin.rev k)) = W
    rw [T.intersection_symm]
    exact hedges (Fin.rev k) (Fin.rev j) (by simp [Fin.rev]; omega)
      (by simp [Fin.rev]; omega) (by simp [Fin.rev]; omega)
  have hrevzero : ∀ j k, j.val + 1 < k.val →
      T.intersection (ri j) (ri k) = 0 := by
    intro j k hgap
    change T.intersection (i (Fin.rev j)) (i (Fin.rev k)) = 0
    rw [T.intersection_symm]
    exact hzero (Fin.rev k) (Fin.rev j) (by simp [Fin.rev]; omega)
  have hrev0 : Fin.rev (⟨0, by omega⟩ : Fin t) = ⟨t - 1, by omega⟩ :=
    Fin.ext (by simp [Fin.rev])
  have hrev1 : Fin.rev (⟨1, by omega⟩ : Fin t) = ⟨t - 2, by omega⟩ :=
    Fin.ext (by simp [Fin.rev])
  have hrevLast : Fin.rev (⟨t - 1, by omega⟩ : Fin t) = ⟨0, by omega⟩ :=
    Fin.ext (by simp [Fin.rev]; omega)
  have hrevLastPrev : Fin.rev (⟨t - 2, by omega⟩ : Fin t) = ⟨1, by omega⟩ :=
    Fin.ext (by simp [Fin.rev]; omega)
  have hleftRev : T.weight (ri ⟨0, by omega⟩) = W ∧
      T.intersection (ri ⟨0, by omega⟩) (ri ⟨1, by omega⟩) = W := by
    simpa only [ri, hrev0, hrev1] using hright
  have hrightRev : ChainEndpointScale T (ri ⟨t - 1, by omega⟩)
      (ri ⟨t - 2, by omega⟩) W := by
    simpa only [ri, hrevLast, hrevLastPrev] using hleft
  exact build_oriented_long_chain T ri ht W hrevweights hrevedges hrevzero
    hleftRev hrightRev

/-- A proper chain of more than five distinct minus-two indices has one of the
three long-chain configurations, after possibly reversing the chain. -/
@[stacks 0C89]
public lemma classify_long_chain_of_minus_two_indices {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 5 < t)
    (hproper : t < T.componentCount) (hinj : Function.Injective i)
    (hminusTwo : ∀ j, IsMinusTwoIndex T (i j))
    (hadjacent : ∀ j k, k.val = j.val + 1 → T.intersection (i j) (i k) ≠ 0) :
    IsLongChainConfiguration T i ∨
      IsLongChainConfiguration T (fun j => i (Fin.rev j)) := by
  have ht' : 6 ≤ t := by omega
  obtain ⟨W, hW, hweights, hedges, hleft, hright⟩ :=
    chain_basic_data T i ht' hproper hinj hminusTwo hadjacent
  have hzero := no_nonconsecutive_intersection T i ht' hproper hinj hminusTwo W hW
    hweights hedges hleft hright
  rcases hleft with hleftA | hleftC | hleftB
  · left
    exact build_oriented_long_chain T i ht' W hweights hedges hzero hleftA hright
  · rcases hright with hrightA | hrightC | hrightB
    · right
      exact build_reversed_oriented_long_chain T i ht' W hweights hedges hzero
        (Or.inr (Or.inl hleftC)) hrightA
    · exact False.elim (two_special_endpoints_impossible T i ht' hproper hinj
        hminusTwo W hW hweights hedges hzero (Or.inl hleftC) (Or.inl hrightC))
    · exact False.elim (two_special_endpoints_impossible T i ht' hproper hinj
        hminusTwo W hW hweights hedges hzero (Or.inl hleftC) (Or.inr hrightB))
  · rcases hright with hrightA | hrightC | hrightB
    · right
      exact build_reversed_oriented_long_chain T i ht' W hweights hedges hzero
        (Or.inr (Or.inr hleftB)) hrightA
    · exact False.elim (two_special_endpoints_impossible T i ht' hproper hinj
        hminusTwo W hW hweights hedges hzero (Or.inr hleftB) (Or.inl hrightC))
    · exact False.elim (two_special_endpoints_impossible T i ht' hproper hinj
        hminusTwo W hW hweights hedges hzero (Or.inr hleftB) (Or.inr hrightB))

end AlgebraicGeometry.NumericalType
