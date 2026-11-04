module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.BoundingInvariants
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Contribution

/-!
# Connected components of minus-two indices

For a minimal numerical type of genus `g` at least two, a component that is not
a minus-two index has its diagonal entry bounded by `6 * g` outright. A
minus-two index adjacent to a bounded component has its own diagonal entry
bounded by twice that bound, so a minus-two index joined to a non-minus-two
component by a chain of `k` minus-two indices is bounded by `6 * g * 2 ^ k`.

Every connected component of minus-two indices is a proper subgraph, hence one
of the Dynkin configurations. Connected components of minus-two indices are the
`Relation.ReflTransGen` classes of the relation `MinusTwoEdge`, realized as a
`Finset` so that the classification applies to them. This file also records the
row equation of the intersection matrix on such a component and the existence
of a boundary edge leaving it.

## References

* [Stacks Project, Tag 0C9W](https://stacks.math.columbia.edu/tag/0C9W)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

private lemma nonminus_diagonal_bound (T : NumericalType) (g : ℤ)
    (hg : 2 ≤ g) (hgenus : genus T = g) (hminimal : IsMinimal T)
    (hn : 1 < T.componentCount) (i : Fin T.componentCount)
    (hi : ¬ IsMinusTwoIndex T i) :
    T.multiplicity i * |T.intersection i i| ≤ 6 * g :=
  (multiplicity_mul_abs_intersection_self_le
    T g hg hgenus hminimal hn i hi).trans (by omega)

private lemma minus_two_diagonal_doubles_of_neighbor (T : NumericalType)
    (i j : Fin T.componentCount) (hi : IsMinusTwoIndex T i)
    (hij : 0 < T.intersection i j) (B : ℤ)
    (hbound : T.multiplicity j * |T.intersection j j| ≤ B) :
    T.multiplicity i * |T.intersection i i| ≤ 2 * B := by
  rcases hi with ⟨-, hai⟩
  have hmul := (multiplicity_mul_weight_le T i j hij).trans hbound
  rw [hai, abs_of_nonpos (by linarith [T.weight_pos i] : -2 * T.weight i ≤ 0)]
  linarith

private lemma minus_two_diagonal_bound_of_nonminus_neighbor (T : NumericalType)
    (g : ℤ) (hg : 2 ≤ g) (hgenus : genus T = g) (hminimal : IsMinimal T)
    (hn : 1 < T.componentCount) (i j : Fin T.componentCount)
    (hi : IsMinusTwoIndex T i) (hj : ¬ IsMinusTwoIndex T j)
    (hij : 0 < T.intersection i j) :
    T.multiplicity i * |T.intersection i i| ≤ 12 * g :=
  (minus_two_diagonal_doubles_of_neighbor T i j hi hij (6 * g)
    (nonminus_diagonal_bound T g hg hgenus hminimal hn j hj)).trans_eq (by ring)

/-- Distinct indices with nonzero intersection number intersect positively. -/
private lemma intersection_pos_of_ne_zero (T : NumericalType) {x y : Fin T.componentCount}
    (hxy : x ≠ y) (h : T.intersection x y ≠ 0) : 0 < T.intersection x y :=
  (T.intersection_nonneg x y hxy).lt_of_ne' h

private inductive BoundaryChain (T : NumericalType)
    (j : Fin T.componentCount) : Fin T.componentCount → ℕ → Prop where
  | start {i} (hi : IsMinusTwoIndex T i)
      (hji : 0 < T.intersection j i) : BoundaryChain T j i 1
  | step {i i' k} (hpath : BoundaryChain T j i k)
      (hi' : IsMinusTwoIndex T i') (hii : 0 < T.intersection i i') :
      BoundaryChain T j i' (k + 1)

private def MinusTwoEdge (T : NumericalType)
    (i j : Fin T.componentCount) : Prop :=
  IsMinusTwoIndex T i ∧ IsMinusTwoIndex T j ∧ 0 < T.intersection i j

private theorem minusTwoEdge_symm (T : NumericalType) {i j : Fin T.componentCount}
    (h : MinusTwoEdge T i j) : MinusTwoEdge T j i :=
  ⟨h.2.1, h.1, T.intersection_symm i j ▸ h.2.2⟩

private theorem reflTransGen_reverse_minusTwo (T : NumericalType)
    {i j : Fin T.componentCount}
    (h : Relation.ReflTransGen (MinusTwoEdge T) i j) :
    Relation.ReflTransGen (MinusTwoEdge T) j i := by
  induction h with
  | refl => exact .refl
  | @tail b c hpath hedge ih =>
      exact Relation.ReflTransGen.head (minusTwoEdge_symm T hedge) ih

private theorem exists_boundary_edge_of_minus_two (T : NumericalType)
    {i : Fin T.componentCount} (hi : IsMinusTwoIndex T i)
    (hJ : ∃ j : Fin T.componentCount, ¬ IsMinusTwoIndex T j) :
    ∃ v j : Fin T.componentCount,
      IsMinusTwoIndex T v ∧ Relation.ReflTransGen (MinusTwoEdge T) i v ∧
      ¬ IsMinusTwoIndex T j ∧ 0 < T.intersection v j := by
  classical
  by_contra h
  let S : Set (Fin T.componentCount) :=
    {v | IsMinusTwoIndex T v ∧ Relation.ReflTransGen (MinusTwoEdge T) i v}
  have hS_proper : S ≠ Set.univ := by
    obtain ⟨j, hj⟩ := hJ
    exact fun hEq => hj (Set.eq_univ_iff_forall.mp hEq j).1
  have hcross : ∀ x, x ∈ S → ∀ y, y ∉ S → T.intersection x y = 0 := by
    intro x hx y hy
    by_contra hzero
    have hpos := intersection_pos_of_ne_zero T (by rintro rfl; exact hy hx) hzero
    by_cases hym : IsMinusTwoIndex T y
    · exact hy ⟨hym, hx.2.tail ⟨hx.1, hym, hpos⟩⟩
    · exact h ⟨x, y, hx.1, hx.2, hym, hpos⟩
  exact T.connected ⟨S, ⟨i, hi, .refl⟩, hS_proper, hcross⟩

private theorem diagonal_bound_of_boundary_chain (T : NumericalType) (g : ℤ)
    (hg : 2 ≤ g) (hgenus : genus T = g) (hminimal : IsMinimal T)
    (hn : 1 < T.componentCount) (j : Fin T.componentCount)
    (hj : ¬ IsMinusTwoIndex T j) :
    ∀ {i k}, BoundaryChain T j i k →
      T.multiplicity i * |T.intersection i i| ≤ 6 * g * (2 : ℤ)^k := by
  intro i k hpath
  induction hpath with
  | start hi hji =>
      exact (minus_two_diagonal_doubles_of_neighbor T _ j hi (by rwa [T.intersection_symm])
        (6 * g) (nonminus_diagonal_bound T g hg hgenus hminimal hn j hj)).trans_eq (by ring)
  | @step i i' k hpath hi' hii ih =>
      exact (minus_two_diagonal_doubles_of_neighbor T i' i hi' (by rwa [T.intersection_symm])
        _ ih).trans_eq (by ring)

private theorem diagonal_bound_of_short_boundary_chain (T : NumericalType)
    (g : ℤ) (hg : 2 ≤ g) (hgenus : genus T = g) (hminimal : IsMinimal T)
    (hn : 1 < T.componentCount) (j i : Fin T.componentCount)
    (hj : ¬ IsMinusTwoIndex T j) (k : ℕ) (hk : k ≤ 7)
    (hpath : BoundaryChain T j i k) :
    T.multiplicity i * |T.intersection i i| ≤ 768 * g := by
  calc
    T.multiplicity i * |T.intersection i i| ≤ 6 * g * (2 : ℤ)^k :=
      diagonal_bound_of_boundary_chain T g hg hgenus hminimal hn j hj hpath
    _ ≤ 6 * g * 128 :=
      mul_le_mul_of_nonneg_left (by interval_cases k <;> norm_num) (by omega)
    _ = 768 * g := by ring

private noncomputable def MinusTwoComponent (T : NumericalType) (i : Fin T.componentCount) :
    Finset (Fin T.componentCount) := by
  classical
  exact Finset.univ.filter fun v =>
    IsMinusTwoIndex T v ∧ Relation.ReflTransGen (MinusTwoEdge T) i v

private theorem minusTwoComponent_mem_iff (T : NumericalType)
    (i v : Fin T.componentCount) :
    v ∈ MinusTwoComponent T i ↔
      IsMinusTwoIndex T v ∧ Relation.ReflTransGen (MinusTwoEdge T) i v := by
  simp [MinusTwoComponent]

private theorem minusTwoComponent_connected (T : NumericalType)
    (i : Fin T.componentCount) (_hi : IsMinusTwoIndex T i) :
    ¬ ∃ J : Finset (Fin T.componentCount), J.Nonempty ∧
      J ⊂ MinusTwoComponent T i ∧
      (∀ x ∈ J, ∀ y ∈ MinusTwoComponent T i, y ∉ J →
        T.intersection x y = 0) := by
  classical
  rintro ⟨J, hJne, hJproper, hcut⟩
  let I := MinusTwoComponent T i
  have hpreserve {x y : Fin T.componentCount}
      (hpath : Relation.ReflTransGen (MinusTwoEdge T) x y)
      (hxI : x ∈ I) (hyI : y ∈ I) : x ∈ J → y ∈ J := by
    induction hpath with
    | refl => exact id
    | @tail b c hpath hedge ih =>
        intro haJ
        have hreachB := ((minusTwoComponent_mem_iff T i x).mp hxI).2.trans hpath
        have hbJ := ih ((minusTwoComponent_mem_iff T i b).mpr ⟨hedge.1, hreachB⟩) haJ
        by_contra hcJ
        exact (ne_of_gt hedge.2.2) (hcut b hbJ c
          ((minusTwoComponent_mem_iff T i c).mpr ⟨hedge.2.1, hreachB.tail hedge⟩) hcJ)
  obtain ⟨x, hxJ⟩ := hJne
  obtain ⟨y, hyI, hyJ⟩ := Finset.exists_of_ssubset hJproper
  have hxI : x ∈ I := hJproper.subset hxJ
  have hpath :=
    (reflTransGen_reverse_minusTwo T
      ((minusTwoComponent_mem_iff T i x).mp hxI).2).trans
      ((minusTwoComponent_mem_iff T i y).mp hyI).2
  exact hyJ (hpreserve hpath hxI hyI hxJ)

private theorem classify_minusTwoComponent (T : NumericalType)
    (i : Fin T.componentCount) (hi : IsMinusTwoIndex T i)
    (hcard : 2 ≤ (MinusTwoComponent T i).card)
    (hproper : (MinusTwoComponent T i).card < T.componentCount) :
    ∃ v : Fin (MinusTwoComponent T i).card → Fin T.componentCount,
      Function.Injective v ∧
      Set.range v = ((MinusTwoComponent T i : Finset (Fin T.componentCount)) :
        Set (Fin T.componentCount)) ∧
      ∃ (d : DynkinShape) (w : ℤ),
        IsDynkinConfiguration T v d w := by
  classical
  exact classify_connected_proper_minusTwo_subgraph T (MinusTwoComponent T i) hcard hproper
    (fun x hx => ((minusTwoComponent_mem_iff T i x).mp hx).1)
    (minusTwoComponent_connected T i hi)

private theorem minusTwoComponent_outside_pos_not_minus (T : NumericalType)
    (i : Fin T.componentCount) (_hi : IsMinusTwoIndex T i)
    {x y : Fin T.componentCount} (hx : x ∈ MinusTwoComponent T i)
    (hy : y ∉ MinusTwoComponent T i) (hxy : 0 < T.intersection x y) :
    ¬ IsMinusTwoIndex T y := by
  intro hyminus
  have hx' := (minusTwoComponent_mem_iff T i x).mp hx
  exact hy ((minusTwoComponent_mem_iff T i y).mpr ⟨hyminus, hx'.2.tail ⟨hx'.1, hyminus, hxy⟩⟩)

private theorem no_outside_intersection_of_no_boundary {t : ℕ}
    (T : NumericalType) (i : Fin T.componentCount) (hi : IsMinusTwoIndex T i)
    (v : Fin t → Fin T.componentCount)
    (hrange : Set.range v = (MinusTwoComponent T i : Set _)) (r : Fin t)
    (hboundary : ¬ ∃ y, y ∉ MinusTwoComponent T i ∧ ¬ IsMinusTwoIndex T y ∧
      0 < T.intersection (v r) y) :
    ∀ y, y ∉ MinusTwoComponent T i → T.intersection (v r) y = 0 := by
  intro y hy
  have hmem : v r ∈ MinusTwoComponent T i := by
    have : v r ∈ Set.range v := ⟨r, rfl⟩
    rw [hrange] at this
    exact this
  by_contra hzero
  have hpos := intersection_pos_of_ne_zero T (by rintro rfl; exact hy hmem) hzero
  exact hboundary ⟨y, hy, minusTwoComponent_outside_pos_not_minus T i hi hmem hy hpos, hpos⟩

private noncomputable instance {t : ℕ} (d : DynkinShape) :
    DecidableRel (@DynkinShape.Edge t d) := Classical.decRel _

private theorem row_eq_on_minusTwoComponent {t : ℕ} (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (v : Fin t → Fin T.componentCount)
    (d : DynkinShape) (w : ℤ)
    (hconfig : IsDynkinConfiguration T v d w)
    (hinj : Function.Injective v) (hrange : Set.range v = (I : Set _))
    : ∀ r, (∀ j, j ∉ I → T.intersection (v r) j = 0) → (∑ s : Fin t,
      (if d.Edge r s then
        max (d.weightFactor r) (d.weightFactor s) * T.multiplicity (v s)
      else 0)) = 2 * d.weightFactor r * T.multiplicity (v r) := by
  classical
  intro r hno
  rcases hconfig with ⟨hd, hw, hweights, hinter, hineq⟩
  let e : Fin t ≃ I := Equiv.ofBijective
    (fun a => ⟨v a, by
      have ha : v a ∈ Set.range v := ⟨a, rfl⟩
      rw [hrange] at ha
      exact ha⟩)
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun x => by
      have hx : (x : Fin T.componentCount) ∈ Set.range v := by
        rw [hrange]
        exact x.property
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, Subtype.ext ha⟩⟩
  let f : Fin T.componentCount → ℤ := fun j =>
    T.intersection (v r) j * T.multiplicity j
  have hrow := T.intersection_mul_multiplicity (v r)
  have hsplit : (∑ j ∈ I, f j) + (∑ j ∈ Iᶜ, f j) = 0 := by
    rw [Finset.sum_add_sum_compl I f]
    simpa [f] using hrow
  have hcompl : ∑ j ∈ Iᶜ, f j = 0 :=
    Finset.sum_eq_zero fun j hj => by simp [f, hno j (by simpa using hj)]
  have hsumI : ∑ j ∈ I, f j = 0 := by omega
  have hsumRank : ∑ s : Fin t, f (v s) = 0 := by
    have hsumSubtype : ∑ x : I, f x = ∑ j ∈ I, f j := by
      rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach]
    have hequiv : (∑ s : Fin t, f (v s)) = ∑ x : I, f x :=
      Fintype.sum_equiv e (fun s => f (v s)) (fun x => f x) fun _ => rfl
    rw [hequiv, hsumSubtype, hsumI]
  have hedge_refl : ¬ d.Edge r r := by
    have hlt := r.isLt
    cases d <;> simp [DynkinShape.Edge,
      DynkinShape.Allows] at hd ⊢ <;> omega
  have hterm (s : Fin t) : f (v s) =
      (if s = r then -2 * d.weightFactor r * w * T.multiplicity (v r) else 0) +
        w * (if d.Edge r s then
          max (d.weightFactor r) (d.weightFactor s) * T.multiplicity (v s) else 0) := by
    dsimp only [f]
    rw [hinter r s]
    by_cases hrs : s = r
    · subst hrs
      simp [hedge_refl]
    · simp only [hrs, Ne.symm hrs, ite_false, zero_add]
      split_ifs <;> ring
  have hmul : w * ((∑ s : Fin t,
      if d.Edge r s then
        max (d.weightFactor r) (d.weightFactor s) * T.multiplicity (v s)
      else 0) - 2 * d.weightFactor r * T.multiplicity (v r)) = 0 := by
    rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_add_distrib,
      ← Finset.mul_sum] at hsumRank
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsumRank
    linear_combination hsumRank
  rcases mul_eq_zero.mp hmul with hwzero | hzero
  · omega
  · linarith

private lemma exists_not_minus_two_index (T : NumericalType) (g : ℤ)
    (hg : 2 ≤ g) (hgenus : genus T = g) :
    ∃ i : Fin T.componentCount, ¬ IsMinusTwoIndex T i := by
  classical
  by_contra! hall
  have hsum :
      ∑ i : Fin T.componentCount,
        (T.multiplicity i : ℚ) *
          ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
            (T.intersection i i : ℚ) / 2) = 0 :=
    Finset.sum_eq_zero fun i _ => contribution_eq_zero_of_isMinusTwoIndex T i (hall i)
  have hcast : (g : ℚ) = 1 +
      ∑ i : Fin T.componentCount,
        (T.multiplicity i : ℚ) *
          ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
            (T.intersection i i : ℚ) / 2) := by
    rw [← hgenus]
    exact cast_genus T
  rw [hsum] at hcast
  have hg' : (1 : ℚ) < (g : ℚ) := by exact_mod_cast (show 1 < g by omega)
  linarith

private theorem minusTwoComponent_boundary_exists (T : NumericalType)
    (g : ℤ) (hg : 2 ≤ g) (hgenus : genus T = g)
    (i : Fin T.componentCount) (hi : IsMinusTwoIndex T i) :
    ∃ v ∈ MinusTwoComponent T i, ∃ j, ¬ IsMinusTwoIndex T j ∧
      0 < T.intersection v j := by
  obtain ⟨v, j, hv, hreach, hj, hvj⟩ :=
    exists_boundary_edge_of_minus_two T hi (exists_not_minus_two_index T g hg hgenus)
  exact ⟨v, (minusTwoComponent_mem_iff T i v).mpr ⟨hv, hreach⟩, j, hj, hvj⟩

end AlgebraicGeometry.NumericalType
