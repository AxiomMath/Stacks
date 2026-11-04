module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.AffineE7
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.E8

/-!
# Nonexistence of a completed E8 subgraph

A numerical type with more than nine components cannot contain nine distinct
minus-two indices forming a chain of eight vertices with an additional vertex
joined to the fifth vertex: discarding the first chain vertex leaves the affine
Dynkin diagram `Ẽ₇`, which already fails to occur.

The same holds when the additional vertex is joined to the sixth chain vertex,
that is, for the affine Dynkin diagram `Ẽ₈`. Deleting the far end of the long
arm leaves an `E₈` configuration and deleting the near end leaves a fork, so
all nine weights agree with a common value `w` and all eight edges have
intersection number `w`. The weighted `Ẽ₈` Cartan matrix is then an entrywise
lower bound for the intersection submatrix, and it annihilates the positive
vector `(1, 2, 3, 4, 5, 6, 4, 2; 3)`. The intersection form, being negative
semidefinite, therefore vanishes on that vector; but a strictly positive
combination of components supported on a proper subset cannot lie in its zero
locus.

## Main results

* `AlgebraicGeometry.NumericalType.not_exists_branched_chain_of_nine_minus_two_indices`:
  the indicated nine-vertex subgraph does not occur.
* `AlgebraicGeometry.NumericalType.not_exists_branched_chain_of_nine_minus_two_indices_at_sixth`:
  the same with the additional vertex joined to the sixth chain vertex.

## Implementation notes

The nine named indices of the source are represented, in their displayed order,
by an injective map from `Fin 9`: `i 0, …, i 7` is the chain and `i 8` the
extra vertex. The eight required nonzero intersection numbers are stated
explicitly; no condition is imposed on the others.

The source is internally inconsistent about where the extra vertex attaches.
Its diagram draws the branch edge at the sixth vertex of the chain, giving the
affine diagram `Ẽ₈`, whereas its list of nonzero entries ends with `a_{lh}`,
attaching `l` to `h`, the fifth vertex of the chain `d, e, f, g, h, i, j, k`.
Both configurations are proved here not to occur. The bare tag follows the
diagram, at `not_exists_branched_chain_of_nine_minus_two_indices_at_sixth`:
only that reading gives an affine diagram, the section classifies the affine
diagrams, and the branch at the sixth vertex is the convention used by
`no_affine_e8_ordering` in `Classification.lean`. The index list appears to
repeat `a_{lh}` from the eight-index statement, where `h` is indeed the fifth
and last interior vertex. The fifth-vertex reading is proved as
`not_exists_branched_chain_of_nine_minus_two_indices`; its graph contains
`Ẽ₇` and so is not affine.

## References

* [Stacks Project, Tag 0C8P](https://stacks.math.columbia.edu/tag/0C8P)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

open Matrix

/-- If a numerical type has more than nine components, it has no nine distinct
minus-two indices forming an eight-vertex chain with an extra vertex joined to
the fifth vertex.

This is the configuration of the source's displayed *formula*: it asks for nine
distinct `(-2)`-indices `d, e, f, g, h, i, j, k, l` with
`a_{de}, a_{ef}, a_{fg}, a_{gh}, a_{hi}, a_{ij}, a_{jk}, a_{lh}` nonzero, so the
chain is `d - e - f - g - h - i - j - k` and the extra index `l` is joined to
`h`, the fifth vertex of that chain.  The source's displayed *diagram* instead
hangs the extra vertex below the sixth bullet of the chain; the two readings
differ, and `not_exists_branched_chain_of_nine_minus_two_indices_at_sixth` is
the diagram reading. -/
@[stacks 0C8P]
public lemma not_exists_branched_chain_of_nine_minus_two_indices
    (T : NumericalType) (hcount : 9 < T.componentCount) :
    ¬ ∃ i : Fin 9 → Fin T.componentCount,
      Function.Injective i ∧
      (∀ r, IsMinusTwoIndex T (i r)) ∧
      T.intersection (i 0) (i 1) ≠ 0 ∧
      T.intersection (i 1) (i 2) ≠ 0 ∧
      T.intersection (i 2) (i 3) ≠ 0 ∧
      T.intersection (i 3) (i 4) ≠ 0 ∧
      T.intersection (i 4) (i 5) ≠ 0 ∧
      T.intersection (i 5) (i 6) ≠ 0 ∧
      T.intersection (i 6) (i 7) ≠ 0 ∧
      T.intersection (i 8) (i 4) ≠ 0 := by
  rintro ⟨i, hi, hminus, -, h12, h23, h34, h45, h56, h67, h84⟩
  refine not_exists_branched_chain_of_eight_minus_two_indices T (by omega) ?_
  let m : Fin 8 → Fin 9 := ![1, 2, 3, 4, 5, 6, 7, 8]
  have hm : Function.Injective m := by decide
  refine ⟨i ∘ m, hi.comp hm, fun r => hminus _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [m, *]

/-- The integer quadratic form of the intersection matrix is nonpositive on any
integer combination of components. -/
private lemma intersection_int_quadratic_nonpos (T : NumericalType) {n : ℕ}
    (v : Fin n → Fin T.componentCount) (c : Fin n → ℤ) :
    ∑ r, ∑ s, c r * T.intersection (v r) (v s) * c s ≤ 0 := by
  have hQ := T.intersection_quadratic_nonpos (∑ r, (c r : ℚ) • Pi.single (v r) (1 : ℚ))
  rw [Matrix.dotProduct_mulVec_sum_single (ratIntersection T) v fun r => (c r : ℚ)] at hQ
  have hcast : ((∑ r, ∑ s, c r * T.intersection (v r) (v s) * c s : ℤ) : ℚ) ≤ 0 := by
    push_cast
    simpa [ratIntersection] using hQ
  exact_mod_cast hcast

/-- A proper nonempty family of distinct components admits no entrywise lower bound
of its intersection submatrix whose quadratic form vanishes on a strictly positive
vector. -/
private lemma false_of_le_intersection_of_quadratic_eq_zero (T : NumericalType) {n : ℕ}
    (hn : n < T.componentCount) (hn0 : 0 < n)
    (v : Fin n → Fin T.componentCount) (hv : Function.Injective v)
    (B : Fin n → Fin n → ℤ) (hle : ∀ r s, B r s ≤ T.intersection (v r) (v s))
    (c : Fin n → ℤ) (hc : ∀ r, 0 < c r)
    (hB : ∑ r, ∑ s, c r * B r s * c s = 0) : False := by
  have hge : 0 ≤ ∑ r, ∑ s, c r * T.intersection (v r) (v s) * c s := by
    rw [← hB]
    exact Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hle r s) (hc r).le) (hc s).le
  exact no_positive_supported_kernel T n ⟨v, hv⟩ hn hn0 c hc
    (by simpa using le_antisymm (T.intersection_int_quadratic_nonpos v c) hge)

/-- Nine minus-two indices carrying the eight edges of `Ẽ₈` share a common weight
`w`, and each of the eight edges has intersection number `w`. -/
private lemma affine_e8_weights_and_edges (T : NumericalType)
    (hcount : 9 < T.componentCount)
    (v : Fin 9 → Fin T.componentCount) (hv : Function.Injective v)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (h01 : T.intersection (v 0) (v 1) ≠ 0)
    (h12 : T.intersection (v 1) (v 2) ≠ 0)
    (h23 : T.intersection (v 2) (v 3) ≠ 0)
    (h34 : T.intersection (v 3) (v 4) ≠ 0)
    (h45 : T.intersection (v 4) (v 5) ≠ 0)
    (h56 : T.intersection (v 5) (v 6) ≠ 0)
    (h67 : T.intersection (v 6) (v 7) ≠ 0)
    (h58 : T.intersection (v 5) (v 8) ≠ 0) :
    ∃ w, (∀ r, T.weight (v r) = w) ∧ T.intersection (v 0) (v 1) = w ∧
      T.intersection (v 1) (v 2) = w ∧ T.intersection (v 2) (v 3) = w ∧
      T.intersection (v 3) (v 4) = w ∧ T.intersection (v 4) (v 5) = w ∧
      T.intersection (v 5) (v 6) = w ∧ T.intersection (v 6) (v 7) = w ∧
      T.intersection (v 5) (v 8) = w := by
  let f : Fin 8 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 8]
  have hf : Function.Injective f := by decide
  have hfc : ∀ j : Fin 6, T.intersection (v (f ⟨j, by omega⟩))
      (v (f ⟨j + 1, by omega⟩)) ≠ 0 := by
    intro j
    fin_cases j <;> simp [f, *]
  obtain ⟨w, hwF, hedgeF, hbranchF, -⟩ := eq_fork_of_isMinusTwoIndex T 7 (by decide)
    (by omega) (v ∘ f) (hv.comp hf) (fun r => hminus _) hfc
    (by simpa [f, Function.comp_def] using h58)
  let g : Fin 8 → Fin 9 := ![1, 2, 3, 4, 5, 6, 7, 8]
  have hg : Function.Injective g := by decide
  obtain ⟨w', hwE, hmatE⟩ := e8_submatrix_of_minus_two_indices T (by omega)
    (v ∘ g) (hv.comp hg) (fun r => hminus _)
    (by simp [g, *]) (by simp [g, *])
    (by simp [g, *]) (by simp [g, *])
    (by simp [g, *]) (by simp [g, *])
    (by simp [g, *])
  have hww : w' = w := (hwE 0).symm.trans (hwF 1)
  refine ⟨w, fun r => ?_, by simpa [f] using hedgeF 0, by simpa [f] using hedgeF 1,
    by simpa [f] using hedgeF 2, by simpa [f] using hedgeF 3, by simpa [f] using hedgeF 4,
    by simpa [f] using hedgeF 5, ?_, by simpa [f] using hbranchF⟩
  · fin_cases r
    exacts [hwF 0, hwF 1, hwF 2, hwF 3, hwF 4, hwF 5, hwF 6, (hwE 6).trans hww, hwF 7]
  · have h := congrFun (congrFun hmatE 5) 6
    simp only [g, Function.comp_def, e8IntersectionMatrix, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.of_apply] at h
    simpa [hww] using h

/-- Nine minus-two indices of a numerical type with more than nine components
cannot carry the eight edges of the affine Dynkin diagram `Ẽ₈`. -/
private lemma false_of_affine_e8_configuration (T : NumericalType)
    (hcount : 9 < T.componentCount)
    (v : Fin 9 → Fin T.componentCount) (hv : Function.Injective v)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (h01 : T.intersection (v 0) (v 1) ≠ 0)
    (h12 : T.intersection (v 1) (v 2) ≠ 0)
    (h23 : T.intersection (v 2) (v 3) ≠ 0)
    (h34 : T.intersection (v 3) (v 4) ≠ 0)
    (h45 : T.intersection (v 4) (v 5) ≠ 0)
    (h56 : T.intersection (v 5) (v 6) ≠ 0)
    (h67 : T.intersection (v 6) (v 7) ≠ 0)
    (h58 : T.intersection (v 5) (v 8) ≠ 0) : False := by
  classical
  obtain ⟨w, hweights, e01, e12, e23, e34, e45, e56, e67, e58⟩ :=
    affine_e8_weights_and_edges T hcount v hv hminus h01 h12 h23 h34 h45 h56 h67 h58
  have hchainW : ∀ r s : Fin 9, s.val = r.val + 1 → s.val < 8 →
      T.intersection (v r) (v s) = w := by
    have key : ∀ (k : ℕ), k < 7 → ∀ (h1 : k < 9) (h2 : k + 1 < 9),
        T.intersection (v ⟨k, h1⟩) (v ⟨k + 1, h2⟩) = w := by
      intro k hk h1 h2
      interval_cases k <;> assumption
    intro r s hrs hs
    rw [show s = ⟨r.val + 1, by omega⟩ from Fin.ext hrs]
    exact key r.val (by omega) r.isLt _
  let E : Fin 9 → Fin 9 → Prop := fun r s =>
    ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < 8 ∧ s.val < 8) ∨
      (r = 5 ∧ s = 8) ∨ (r = 8 ∧ s = 5)
  have hE : ∀ r s : Fin 9, E r s → T.intersection (v r) (v s) = w := by
    intro r s h
    rcases h with ⟨h | h, hr, hs⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hchainW r s h.symm hs
    · exact (T.intersection_symm _ _).trans (hchainW s r h.symm hr)
    · exact e58
    · exact (T.intersection_symm _ _).trans e58
  let B : Fin 9 → Fin 9 → ℤ := fun r s =>
    if r = s then -2 * w else if E r s then w else 0
  let c : Fin 9 → ℤ := ![1, 2, 3, 4, 5, 6, 4, 2, 3]
  refine false_of_le_intersection_of_quadratic_eq_zero T hcount (by omega) v hv B
    (fun r s => ?_) c (fun r => by fin_cases r <;> norm_num [c]) ?_
  · dsimp only [B]
    split_ifs with hrs he
    · subst hrs
      exact le_of_eq (by rw [(hminus r).2, hweights r])
    · exact (hE r s he).ge
    · exact T.intersection_nonneg _ _ (hv.ne hrs)
  · simp [Fin.sum_univ_succ, c, B, E]
    ring

/-- The configuration drawn in the source's diagram, with the extra vertex
joined to the sixth vertex of the chain rather than the fifth: the affine Dynkin
diagram `Ẽ₈`, which likewise does not occur in a numerical type with more than
nine components.

The source's diagram and its displayed formula disagree about which chain vertex
carries the extra index: the diagram shows the sixth, the formula writes
`a_{lh}` with `h` the fifth; `not_exists_branched_chain_of_nine_minus_two_indices`
is the formula reading. -/
@[stacks 0C8P "the configuration of the source's diagram, extra vertex at the sixth chain vertex \
  rather than the fifth of the displayed formula"]
public lemma not_exists_branched_chain_of_nine_minus_two_indices_at_sixth
    (T : NumericalType) (hcount : 9 < T.componentCount) :
    ¬ ∃ i : Fin 9 → Fin T.componentCount,
      Function.Injective i ∧
      (∀ r, IsMinusTwoIndex T (i r)) ∧
      T.intersection (i 0) (i 1) ≠ 0 ∧
      T.intersection (i 1) (i 2) ≠ 0 ∧
      T.intersection (i 2) (i 3) ≠ 0 ∧
      T.intersection (i 3) (i 4) ≠ 0 ∧
      T.intersection (i 4) (i 5) ≠ 0 ∧
      T.intersection (i 5) (i 6) ≠ 0 ∧
      T.intersection (i 6) (i 7) ≠ 0 ∧
      T.intersection (i 8) (i 5) ≠ 0 := by
  rintro ⟨i, hi, hminus, h01, h12, h23, h34, h45, h56, h67, h85⟩
  exact false_of_affine_e8_configuration T hcount i hi hminus h01 h12 h23 h34
    h45 h56 h67 (by rwa [T.intersection_symm])

end AlgebraicGeometry.NumericalType
