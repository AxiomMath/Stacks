module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Contribution
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Irreducible
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.TwoVertices

/-!
# Genus-one configurations of numerical types

A minimal numerical type of genus one is, up to a relabelling of its components, one of an
explicit list: the single component of genus one with arbitrary multiplicity and weight,
twenty-six exceptional affine configurations with between two and nine components, and seven
unbounded families. This file writes down that list — the coefficient tables, the seven
families, and the resulting predicate `IsGenusOneConfiguration` — and proves the elementary
half of the classification together with the reduction that drives the other half.

The elementary half is uniform. Every multi-component configuration on the list has all
component genera zero and diagonal intersection number minus twice the weight, so every one of
its indices is a minus-two index; such a numerical type contributes nothing to the genus and
has no minus-one index, hence is minimal of genus one. The one-component configuration is
handled by the genus formula for an irreducible type.

The reduction in the other direction is the converse statement at the level of indices: a
minimal numerical type of genus one with more than one component has *only* minus-two indices,
because a non-minus-two index of a minimal type contributes at least one half to the genus
while the total contribution of a genus-one type is zero. Combined with that reduction, the
classification is carried out here for one, two, three and four components. In the two-component
case
connectedness makes the single off-diagonal entry `a` positive, the two balance relations force
`a² = 4w₁w₂`, and divisibility of `a` by both weights leaves exactly the two-cycle
`(w, w, 2w)` and the doubled edge `(w, 4w, 4w)` up to exchanging the components.

The three-component case is in
`StacksFrontier/AlgebraicGeometry/Surfaces/GenusOneConfiguration/ThreeComponents.lean`, and the
four-component case in
`StacksFrontier/AlgebraicGeometry/Surfaces/GenusOneConfiguration/FourComponentShape.lean` (the shape
of the incidence graph) and
`StacksFrontier/AlgebraicGeometry/Surfaces/GenusOneConfiguration/FourComponents.lean` (the level
identity of each shape and the classification);
`StacksFrontier/AlgebraicGeometry/Surfaces/GenusOneConfiguration.lean` re-exports all four files.

## Main definitions

* `AlgebraicGeometry.NumericalType.MatchesCoefficients` — a numerical type has prescribed
  multiplicity, weight, intersection and component-genus coefficients, up to a relabelling of
  its components and up to common positive scalings of the multiplicities and of the
  weight/intersection data.
* `AlgebraicGeometry.NumericalType.MatchesFinite` — the same, with the coefficient tables
  given as lists.
* `AlgebraicGeometry.NumericalType.GenusOne.finitePatterns` — the twenty-six exceptional
  affine coefficient tables.
* `AlgebraicGeometry.NumericalType.GenusOne.LongFamily` and
  `AlgebraicGeometry.NumericalType.GenusOne.longMultiplicity`, `longWeight`, `longEdge`,
  `longIntersection` — the seven unbounded families and their coefficient tables.
* `AlgebraicGeometry.NumericalType.IsGenusOneConfiguration` — the disjunction of all of these.

## Main results

* `AlgebraicGeometry.NumericalType.isMinimal_and_genus_eq_one_of_isGenusOneConfiguration` —
  every configuration on the list is minimal of genus one.
* `AlgebraicGeometry.NumericalType.forall_isMinusTwoIndex_of_isMinimal_of_genus_eq_one` — a
  minimal numerical type of genus one with more than one component consists of minus-two
  indices.
* `AlgebraicGeometry.NumericalType.isMinimal_and_genus_eq_one_iff_of_componentCount_eq_one`,
  `AlgebraicGeometry.NumericalType.isMinimal_and_genus_eq_one_iff_of_componentCount_eq_two`,
  `AlgebraicGeometry.NumericalType.isMinimal_and_genus_eq_one_iff_of_componentCount_eq_three` and
  `AlgebraicGeometry.NumericalType.isMinimal_and_genus_eq_one_iff_of_componentCount_eq_four` —
  the classification itself, for one, two, three and four components.
* `AlgebraicGeometry.NumericalType.isGenusOneConfiguration_of_componentCount_eq_three` and
  `AlgebraicGeometry.NumericalType.isGenusOneConfiguration_of_componentCount_eq_four` — the
  three- and four-component cases of the direction from minimality and genus one to the list,
  stated at the level of indices.

## Implementation notes

The finite tables are recorded as integer coefficient lists; their common positive parameters
multiply the multiplicity table and the intersection/weight tables separately. The diagonal
entries of an unbounded family are minus twice the weight by construction. All components of a
multicomponent configuration have genus zero, so `MatchesCoefficients` takes the zero
component-genus table as its default. A relabelling is an `Equiv` of the finite index types,
which also records that the two numerical types have the same number of components.

`@[stacks 0C8T]` is carried here in phrase form, one attribute per clause of the two-sided
classification: the direction from the list to minimality and genus one, which is proved for
every component count, and the two-sided classification for one, for two, for three and for
four components, which are cases (1), (2)-(3), (4)-(9) and (10)-(15) of the source's
enumeration.

What no declaration *in this file* claims is the direction from minimality and genus one to the
list for five or more components — equivalently, that a connected numerical type with at least
five components all of whose indices are minus-two indices appears on the list. That is the
classification of connected affine generalized Cartan matrices, and in the source it is carried
out alongside Proposition 0C8Q and Lemmas 0C8D, 0C8H, 0C8J, 0C8L, 0C8N, 0C8P. The argument used
here for four components does not extend to it uniformly: with four components Proposition 0C8Q
excludes a triangle and connectedness then leaves only three shapes, each with one counting
identity in the levels, whereas from five components on the shapes multiply and the list
acquires the seven unbounded families.

`StacksFrontier/AlgebraicGeometry/Surfaces/GenusOneCycle.lean` settles half of that, for every
component count at once:
`AlgebraicGeometry.NumericalType.isMinimal_and_genus_eq_one_iff_of_two_le_neighborCount` is the
classification for a type with at least five components each of which meets at least two
others, which is the cycle — case (16) for five components and the `n`-cycle family, case (25),
for six or more. The complementary case, some component meeting exactly one other, is reduced
there by
`AlgebraicGeometry.NumericalType.exists_dynkinConfiguration_of_erase_leaf` to a Dynkin
configuration on one fewer component, via Proposition 0C8Q, which this repository has as
`AlgebraicGeometry.NumericalType.classify_connected_proper_minusTwo_subgraph` and which the
four-component case above already uses. The enumeration of the ways the deleted component can
attach to each Dynkin diagram, cases (17)-(24) and (26)-(34), is carried out in
`StacksFrontier/AlgebraicGeometry/Surfaces/GenusOneChain.lean` for an attachment leaving every
degree at most two and in
`StacksFrontier/AlgebraicGeometry/Surfaces/GenusOneForkClassification.lean` for the rest, and those
two together give the two-sided classification for every component count from five on.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

/-! ### Coefficient tables -/

/-- The coefficient tables for a numerical type, up to reindexing: a relabelling `e` of the
components and positive scalars `m`, `w` scaling the multiplicity table and the
weight/intersection tables. -/
public def MatchesCoefficients (T : NumericalType) (n : ℕ)
    (mc wc : Fin n → ℤ) (ac : Fin n → Fin n → ℤ)
    (gc : Fin n → ℤ := fun _ => 0) : Prop :=
  ∃ (e : Fin n ≃ Fin T.componentCount) (m w : ℤ), 0 < m ∧ 0 < w ∧
    (∀ i, T.multiplicity (e i) = mc i * m) ∧
    (∀ i, T.weight (e i) = wc i * w) ∧
    (∀ i j, T.intersection (e i) (e j) = ac i j * w) ∧
    (∀ i, T.componentGenus (e i) = gc i)

/-- A finite coefficient table, given by lists of multiplicities, weights and rows of the
intersection matrix. -/
public def MatchesFinite (T : NumericalType) (mc wc : List ℤ)
    (ac : List (List ℤ)) : Prop :=
  MatchesCoefficients T mc.length
    (fun i => mc.getD i.val 0)
    (fun i => wc.getD i.val 0)
    (fun i j => (ac.getD i.val []).getD j.val 0)

namespace GenusOne

/-! ### The exceptional affine configurations -/

/-- The twenty-six exceptional affine coefficient tables of genus one, from two to nine
components. Each entry lists the multiplicities, the weights and the rows of the intersection
matrix. -/
public def finitePatterns : List (List ℤ × List ℤ × List (List ℤ)) := [
  -- Two components: cycle and doubled edge.
  ([1,1], [1,1], [[-2,2],[2,-2]]),
  ([2,1], [1,4], [[-2,4],[4,-8]]),
  -- Three components.
  ([1,1,1], [1,1,1], [[-2,1,1],[1,-2,1],[1,1,-2]]),
  ([1,2,1], [1,1,3], [[-2,1,0],[1,-2,3],[0,3,-6]]),
  ([1,2,3], [3,3,1], [[-6,3,0],[3,-6,3],[0,3,-2]]),
  ([2,2,1], [1,2,4], [[-2,2,0],[2,-4,4],[0,4,-8]]),
  ([1,1,1], [1,2,1], [[-2,2,0],[2,-4,2],[0,2,-2]]),
  ([1,2,1], [2,1,2], [[-4,2,0],[2,-2,2],[0,2,-4]]),
  -- Four components.
  ([1,1,1,1], [1,1,1,1],
    [[-2,1,0,1],[1,-2,1,0],[0,1,-2,1],[1,0,1,-2]]),
  ([2,2,2,1], [1,2,2,4],
    [[-2,2,0,0],[2,-4,2,0],[0,2,-4,4],[0,0,4,-8]]),
  ([1,1,1,1], [1,2,2,1],
    [[-2,2,0,0],[2,-4,2,0],[0,2,-4,2],[0,0,2,-2]]),
  ([1,2,2,1], [2,1,1,2],
    [[-4,2,0,0],[2,-2,1,0],[0,1,-2,2],[0,0,2,-4]]),
  ([2,1,1,1], [1,1,1,2],
    [[-2,1,1,2],[1,-2,0,0],[1,0,-2,0],[2,0,0,-4]]),
  ([2,1,1,2], [2,2,2,1],
    [[-4,2,2,2],[2,-4,0,0],[2,0,-4,0],[2,0,0,-2]]),
  -- Five components.
  ([1,1,1,1,1], [1,1,1,1,1],
    [[-2,1,0,0,1],[1,-2,1,0,0],[0,1,-2,1,0],[0,0,1,-2,1],[1,0,0,1,-2]]),
  ([1,2,3,2,1], [1,1,1,2,2],
    [[-2,1,0,0,0],[1,-2,1,0,0],[0,1,-2,2,0],[0,0,2,-4,2],[0,0,0,2,-4]]),
  ([1,2,3,4,2], [2,2,2,1,1],
    [[-4,2,0,0,0],[2,-4,2,0,0],[0,2,-4,2,0],[0,0,2,-2,1],[0,0,0,1,-2]]),
  ([2,2,2,2,1], [1,2,2,2,4],
    [[-2,2,0,0,0],[2,-4,2,0,0],[0,2,-4,2,0],[0,0,2,-4,4],[0,0,0,4,-8]]),
  ([1,1,1,1,1], [1,2,2,2,1],
    [[-2,2,0,0,0],[2,-4,2,0,0],[0,2,-4,2,0],[0,0,2,-4,2],[0,0,0,2,-2]]),
  ([1,2,2,2,1], [2,1,1,1,2],
    [[-4,2,0,0,0],[2,-2,1,0,0],[0,1,-2,1,0],[0,0,1,-2,2],[0,0,0,2,-4]]),
  ([2,1,1,1,1], [1,1,1,1,1],
    [[-2,1,1,1,1],[1,-2,0,0,0],[1,0,-2,0,0],[1,0,0,-2,0],[1,0,0,0,-2]]),
  ([1,2,2,1,1], [2,1,1,1,1],
    [[-4,2,0,0,0],[2,-2,1,0,0],[0,1,-2,1,1],[0,0,1,-2,0],[0,0,1,0,-2]]),
  ([2,2,2,1,1], [1,2,2,2,2],
    [[-2,2,0,0,0],[2,-4,2,0,0],[0,2,-4,2,2],[0,0,2,-4,0],[0,0,2,0,-4]]),
  -- Completed E6, E7, E8.
  ([1,2,3,1,2,1,2], [1,1,1,1,1,1,1],
    [[-2,1,0,0,0,0,0],[1,-2,1,0,0,0,0],[0,1,-2,0,1,0,1],
     [0,0,0,-2,1,0,0],[0,0,1,1,-2,0,0],[0,0,0,0,0,-2,1],
     [0,0,1,0,0,1,-2]]),
  ([1,2,3,4,3,2,1,2], [1,1,1,1,1,1,1,1],
    [[-2,1,0,0,0,0,0,0],[1,-2,1,0,0,0,0,0],[0,1,-2,1,0,0,0,0],
     [0,0,1,-2,1,0,0,1],[0,0,0,1,-2,1,0,0],[0,0,0,0,1,-2,1,0],
     [0,0,0,0,0,1,-2,0],[0,0,0,1,0,0,0,-2]]),
  ([1,2,3,4,5,6,4,2,3], [1,1,1,1,1,1,1,1,1],
    [[-2,1,0,0,0,0,0,0,0],[1,-2,1,0,0,0,0,0,0],
     [0,1,-2,1,0,0,0,0,0],[0,0,1,-2,1,0,0,0,0],
     [0,0,0,1,-2,1,0,0,0],[0,0,0,0,1,-2,1,0,1],
     [0,0,0,0,0,1,-2,1,0],[0,0,0,0,0,0,1,-2,0],
     [0,0,0,0,0,1,0,0,-2]])
]

/-! ### The unbounded affine families -/

/-- The seven unbounded families of affine configurations. -/
public inductive LongFamily where
  /-- The `n`-cycle. -/
  | cycle
  /-- A chain with a weight-four end at one side and a weight-one end at the other. -/
  | upUp
  /-- A chain with weight-one ends and weight-two interior. -/
  | upDown
  /-- A chain with weight-two ends and weight-one interior. -/
  | downUp
  /-- A fork with a weight-two end opposite the two prongs. -/
  | forkUp
  /-- A fork with a weight-one end opposite the two prongs. -/
  | forkDown
  /-- A chain with two prongs at each end. -/
  | doubleFork
  deriving DecidableEq

/-- Multiplicity coefficients in an unbounded affine family. -/
public def longMultiplicity (f : LongFamily) (n : ℕ) (i : Fin n) : ℤ :=
  match f with
  | .cycle | .upDown => 1
  | .upUp => if i.val = n - 1 then 1 else 2
  | .downUp => if i.val = 0 ∨ i.val = n - 1 then 1 else 2
  | .forkUp => if i.val = 0 ∨ n - 2 ≤ i.val then 1 else 2
  | .forkDown => if n - 2 ≤ i.val then 1 else 2
  | .doubleFork => if i.val ≤ 1 ∨ n - 2 ≤ i.val then 1 else 2

/-- Weight coefficients in an unbounded affine family. -/
public def longWeight (f : LongFamily) (n : ℕ) (i : Fin n) : ℤ :=
  match f with
  | .cycle | .doubleFork => 1
  | .upUp => if i.val = 0 then 1 else if i.val = n - 1 then 4 else 2
  | .upDown => if i.val = 0 ∨ i.val = n - 1 then 1 else 2
  | .downUp => if i.val = 0 ∨ i.val = n - 1 then 2 else 1
  | .forkUp => if i.val = 0 then 2 else 1
  | .forkDown => if i.val = 0 then 1 else 2

/-- Off-diagonal intersection coefficients in an unbounded affine family.
The smaller and larger endpoint numbers make the definition symmetric. -/
public def longEdge (f : LongFamily) (n a b : ℕ) : ℤ :=
  let adjacent := b = a + 1
  match f with
  | .cycle => if adjacent ∨ (a = 0 ∧ b = n - 1) then 1 else 0
  | .upUp =>
      if adjacent then (if b = n - 1 then 4 else 2) else 0
  | .upDown => if adjacent then 2 else 0
  | .downUp =>
      if adjacent then (if a = 0 ∨ b = n - 1 then 2 else 1) else 0
  | .forkUp =>
      if (adjacent ∧ b < n - 1) ∨ (a = n - 3 ∧ b = n - 1) then
        (if a = 0 then 2 else 1) else 0
  | .forkDown =>
      if (adjacent ∧ b < n - 1) ∨ (a = n - 3 ∧ b = n - 1) then 2 else 0
  | .doubleFork =>
      if (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
          (2 ≤ a ∧ adjacent ∧ b < n - 1) ∨ (a = n - 3 ∧ b = n - 1) then
        1 else 0

/-- The full intersection matrix of an unbounded affine family. -/
public def longIntersection (f : LongFamily) (n : ℕ) (i j : Fin n) : ℤ :=
  if i = j then -2 * longWeight f n i
  else longEdge f n (min i.val j.val) (max i.val j.val)

/-- The diagonal of the intersection matrix of an unbounded affine family is minus twice the
weight. -/
public lemma longIntersection_self (f : LongFamily) (n : ℕ) (i : Fin n) :
    longIntersection f n i i = -2 * longWeight f n i := by
  simp [longIntersection]

/-- The diagonal of each exceptional affine coefficient table is minus twice the weight. -/
public lemma finitePatterns_diagonal :
    ∀ p ∈ finitePatterns, ∀ i < p.1.length,
      (p.2.2.getD i []).getD i 0 = -2 * p.2.1.getD i 0 := by
  decide

end GenusOne

/-! ### The list of genus-one configurations -/

/-- One of the genus-one affine configurations, up to a permutation of its components. The
common parameters in the coefficient tables are positive. -/
public def IsGenusOneConfiguration (T : NumericalType) : Prop :=
  MatchesCoefficients T 1 (fun _ => 1) (fun _ => 1) (fun _ _ => 0)
    (fun _ => 1) ∨
  (∃ p ∈ GenusOne.finitePatterns, MatchesFinite T p.1 p.2.1 p.2.2) ∨
  (∃ (n : ℕ) (f : GenusOne.LongFamily), 6 ≤ n ∧
    MatchesCoefficients T n (GenusOne.longMultiplicity f n) (GenusOne.longWeight f n)
      (GenusOne.longIntersection f n))

/-! ### Numerical types all of whose indices are minus-two indices -/

/-- A numerical type all of whose indices are minus-two indices is minimal of genus one: no
index can be a minus-one index, and every contribution to the genus vanishes. -/
public lemma isMinimal_and_genus_eq_one_of_forall_isMinusTwoIndex (T : NumericalType)
    (h : ∀ i, IsMinusTwoIndex T i) : IsMinimal T ∧ genus T = 1 := by
  constructor
  · rintro ⟨i, -, hone⟩
    have htwo := (h i).2
    have hw := T.weight_pos i
    omega
  · have h1 : ∑ i, T.multiplicity i * (T.weight i * (T.componentGenus i - 1))
        = -∑ i, T.multiplicity i * T.weight i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [(h i).1]; ring
    have h2 : ∑ i, T.multiplicity i * T.intersection i i
        = 2 * -∑ i, T.multiplicity i * T.weight i := by
      have hrow : ∑ i, T.multiplicity i * T.intersection i i
          = ∑ i, 2 * -(T.multiplicity i * T.weight i) :=
        Finset.sum_congr rfl fun i _ => by rw [(h i).2]; ring
      rw [hrow, ← Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [genus, h1, h2, Int.mul_ediv_cancel_left _ (by norm_num)]
    ring

/-- A numerical type matching a coefficient table whose component genera vanish and whose
diagonal is minus twice the weight consists of minus-two indices. -/
public lemma forall_isMinusTwoIndex_of_matchesCoefficients {T : NumericalType} {n : ℕ}
    {mc wc : Fin n → ℤ} {ac : Fin n → Fin n → ℤ} {gc : Fin n → ℤ}
    (h : MatchesCoefficients T n mc wc ac gc)
    (hgc : ∀ i, gc i = 0) (hac : ∀ i, ac i i = -2 * wc i) :
    ∀ j, IsMinusTwoIndex T j := by
  obtain ⟨e, m, w, -, -, -, hwt, hint, hgen⟩ := h
  intro j
  obtain ⟨i, rfl⟩ := e.surjective j
  refine ⟨by rw [hgen i, hgc i], ?_⟩
  rw [hint i i, hac i, hwt i]
  ring

/-! ### The elementary half of the classification -/

/-- **Stacks Project, Tag 0C8T**, the direction from the list to minimality and genus one.
Every configuration on the genus-one list is a minimal numerical type of genus one. -/
@[stacks 0C8T "every numerical type on the list is minimal of genus one"]
public lemma isMinimal_and_genus_eq_one_of_isGenusOneConfiguration (T : NumericalType)
    (h : IsGenusOneConfiguration T) : IsMinimal T ∧ genus T = 1 := by
  rcases h with h | ⟨p, hp, h⟩ | ⟨n, f, -, h⟩
  · obtain ⟨e, m, w, hm, hw, hmul, hwt, hint, hgen⟩ := h
    have hgen' : ∀ i : Fin 1, T.componentGenus (e i) = 1 := hgen
    have hcount : T.componentCount = 1 := by
      simpa using (Fintype.card_congr e).symm
    have huniq : ∀ x y : Fin T.componentCount, x = y := fun x y =>
      Fin.ext (by have := x.isLt; have := y.isLt; omega)
    refine ⟨?_, ?_⟩
    · rintro ⟨i, hzero, -⟩
      have h1 := hgen' 0
      rw [huniq (e 0) i] at h1
      omega
    · rw [genus_eq_of_componentCount_eq_one T hcount,
        huniq ⟨0, T.componentCount_pos⟩ (e 0), hgen' 0]
      ring
  · have h' : MatchesCoefficients T p.1.length
        (fun i => p.1.getD i.val 0) (fun i => p.2.1.getD i.val 0)
        (fun i j => (p.2.2.getD i.val []).getD j.val 0) := h
    exact isMinimal_and_genus_eq_one_of_forall_isMinusTwoIndex T
      (forall_isMinusTwoIndex_of_matchesCoefficients h' (fun _ => rfl)
        (fun i => GenusOne.finitePatterns_diagonal p hp i.val i.isLt))
  · exact isMinimal_and_genus_eq_one_of_forall_isMinusTwoIndex T
      (forall_isMinusTwoIndex_of_matchesCoefficients h (fun _ => rfl)
        (fun i => GenusOne.longIntersection_self f n i))

/-! ### The reduction driving the other half -/

/-- Every index of a minimal numerical type of genus one with more than one component is a
minus-two index: a non-minus-two index of a minimal type contributes at least one half to the
genus, while in genus one no contribution exceeds zero. -/
public lemma forall_isMinusTwoIndex_of_isMinimal_of_genus_eq_one (T : NumericalType)
    (hmin : IsMinimal T) (hgenus : genus T = 1) (hn : 1 < T.componentCount) :
    ∀ i, IsMinusTwoIndex T i := by
  intro i
  by_contra hi
  have hlower := one_half_le_contribution_of_not_isMinusTwoIndex T hmin hn i hi
  have hupper := contribution_le_genus_sub_one T 1 hgenus hmin hn i
  norm_num at hupper
  linarith

/-! ### The classification for one component -/

/-- **Stacks Project, Tag 0C8T**, case (1). A numerical type with a single component is
minimal of genus one exactly when it is the one-component genus-one configuration: diagonal
intersection number zero, component genus one, and arbitrary positive multiplicity and
weight. -/
@[stacks 0C8T "the classification for one component, case (1)"]
public lemma isMinimal_and_genus_eq_one_iff_of_componentCount_eq_one (T : NumericalType)
    (hn : T.componentCount = 1) :
    (IsMinimal T ∧ genus T = 1) ↔ IsGenusOneConfiguration T := by
  refine ⟨fun hT => Or.inl ?_, isMinimal_and_genus_eq_one_of_isGenusOneConfiguration T⟩
  have hformula := genus_eq_of_componentCount_eq_one T hn
  have hzero := intersection_self_eq_zero_of_componentCount_eq_one T hn
  have hm := T.multiplicity_pos ⟨0, T.componentCount_pos⟩
  have hw := T.weight_pos ⟨0, T.componentCount_pos⟩
  rw [hT.2] at hformula
  have hgen : T.componentGenus ⟨0, T.componentCount_pos⟩ = 1 := by
    have hprod : T.multiplicity ⟨0, T.componentCount_pos⟩ *
        T.weight ⟨0, T.componentCount_pos⟩ *
        (T.componentGenus ⟨0, T.componentCount_pos⟩ - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hprod with hmw | hg
    · rcases mul_eq_zero.mp hmw with h | h <;> omega
    · omega
  have hall : ∀ i : Fin 1,
      (finCongr hn.symm) i = (⟨0, T.componentCount_pos⟩ : Fin T.componentCount) :=
    fun i => Fin.ext (by simp)
  exact ⟨finCongr hn.symm, T.multiplicity ⟨0, T.componentCount_pos⟩,
    T.weight ⟨0, T.componentCount_pos⟩, hm, hw,
    fun i => by rw [hall i]; ring,
    fun i => by rw [hall i]; ring,
    fun i j => by rw [hall i, hall j, hzero]; ring,
    fun i => by rw [hall i, hgen]⟩

/-! ### The classification for two components -/

/-- In a numerical type with exactly two components, the intersection matrix balances the
multiplicities two terms at a time. -/
private lemma intersection_balance_two (T : NumericalType) (hn : T.componentCount = 2)
    (x : Fin T.componentCount) :
    T.intersection x (finCongr hn.symm 0) * T.multiplicity (finCongr hn.symm 0) +
      T.intersection x (finCongr hn.symm 1) * T.multiplicity (finCongr hn.symm 1) = 0 := by
  have hsum : ∑ k : Fin 2, T.intersection x (finCongr hn.symm k) *
      T.multiplicity (finCongr hn.symm k)
      = ∑ y, T.intersection x y * T.multiplicity y :=
    Fintype.sum_equiv (finCongr hn.symm) _ _ fun _ => rfl
  rwa [T.intersection_mul_multiplicity x, Fin.sum_univ_two] at hsum

/-- If `a = wᵢ p = wⱼ q` is the intersection number of two components satisfying the balance
relations with positive multiplicities and weights, then `(p, q)` is `(2, 2)`, `(1, 4)` or
`(4, 1)`. -/
private lemma quotient_cases_of_balance {a wi wj mi mj p q : ℤ} (hmi : 0 < mi) (hmj : 0 < mj)
    (hwi : 0 < wi) (hwj : 0 < wj) (ha : 0 < a) (hbi : -2 * wi * mi + a * mj = 0)
    (hbj : a * mi + -2 * wj * mj = 0) (hp : a = wi * p) (hq : a = wj * q) :
    (p = 2 ∧ q = 2) ∨ (p = 1 ∧ q = 4) ∨ (p = 4 ∧ q = 1) := by
  -- The determinant of the intersection matrix vanishes.
  have hdet : a * a = 4 * (wi * wj) := by
    have hprod : (a * a) * (mi * mj) = (4 * (wi * wj)) * (mi * mj) := by
      linear_combination a * mi * hbi + 2 * wi * mi * hbj
    exact mul_right_cancel₀ (by positivity) hprod
  have hppos : 0 < p := by rcases lt_trichotomy p 0 with h' | h' | h' <;> nlinarith
  have hqpos : 0 < q := by rcases lt_trichotomy q 0 with h' | h' | h' <;> nlinarith
  have hpq : p * q = 4 := by
    have hprod : (p * q) * (wi * wj) = 4 * (wi * wj) := by nlinarith
    exact mul_right_cancel₀ (by positivity) hprod
  have hple : p ≤ 4 := by nlinarith
  interval_cases p <;> omega

/-- A numerical type with two components all of whose indices are minus-two indices is one of
the first two exceptional configurations: the two-cycle, or the doubled edge. -/
public lemma isGenusOneConfiguration_of_componentCount_eq_two (T : NumericalType)
    (hn : T.componentCount = 2) (h : ∀ i, IsMinusTwoIndex T i) :
    IsGenusOneConfiguration T := by
  set e : Fin 2 ≃ Fin T.componentCount := finCongr hn.symm with he
  set i : Fin T.componentCount := e 0 with hidef
  set j : Fin T.componentCount := e 1 with hjdef
  have hne : i ≠ j := fun heq => by simpa [hidef, hjdef] using e.injective heq
  have hother : ∀ x : Fin T.componentCount, x = i ∨ x = j := by
    intro x
    have hx := x.isLt
    rcases (by omega : x.val = 0 ∨ x.val = 1) with hx0 | hx1
    · exact Or.inl (Fin.ext (by simpa [hidef, he] using hx0))
    · exact Or.inr (Fin.ext (by simpa [hjdef, he] using hx1))
  -- The two components meet, by connectedness.
  have hcpos : 0 < T.intersection i j := by
    refine lt_of_le_of_ne (T.intersection_nonneg i j hne) fun hzero => T.connected ?_
    refine ⟨{i}, ⟨i, rfl⟩, fun huniv => hne ?_, ?_⟩
    · exact (Set.mem_singleton_iff.mp (Set.eq_univ_iff_forall.mp huniv j)).symm
    · intro x hx y hy
      obtain rfl : x = i := hx
      obtain rfl : y = j := (hother y).resolve_left fun hyi => hy (hyi ▸ rfl)
      exact hzero.symm
  have hmi := T.multiplicity_pos i
  have hmj := T.multiplicity_pos j
  have hwi := T.weight_pos i
  have hwj := T.weight_pos j
  -- The two balance relations.
  have hbi : -2 * T.weight i * T.multiplicity i +
      T.intersection i j * T.multiplicity j = 0 := by
    have := intersection_balance_two T hn i
    rw [← hidef, ← hjdef, (h i).2] at this
    linarith
  have hbj : T.intersection i j * T.multiplicity i +
      -2 * T.weight j * T.multiplicity j = 0 := by
    have := intersection_balance_two T hn j
    rw [← hidef, ← hjdef, (h j).2, T.intersection_symm j i] at this
    linarith
  -- The weights divide the intersection number, which splits it into three cases.
  obtain ⟨p, hp⟩ := T.weight_dvd_intersection i j
  obtain ⟨q, hq⟩ := T.weight_dvd_intersection j i
  rw [T.intersection_symm j i] at hq
  -- The balance relations, with the weights divided out, relate the multiplicities.
  have hpm : p * T.multiplicity j = 2 * T.multiplicity i := by
    have h0 : T.weight i * (p * T.multiplicity j - 2 * T.multiplicity i) = 0 := by
      linear_combination hbi - T.multiplicity j * hp
    linarith [(mul_eq_zero.mp h0).resolve_left hwi.ne']
  have hqm : q * T.multiplicity i = 2 * T.multiplicity j := by
    have h0 : T.weight j * (q * T.multiplicity i - 2 * T.multiplicity j) = 0 := by
      linear_combination hbj - T.multiplicity i * hq
    linarith [(mul_eq_zero.mp h0).resolve_left hwj.ne']
  rcases quotient_cases_of_balance hmi hmj hwi hwj hcpos hbi hbj hp hq with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- Equal weights: the two-cycle.
    have hweq : T.weight j = T.weight i := by linarith [hp, hq]
    have hmeq : T.multiplicity j = T.multiplicity i := by linarith
    refine Or.inr (Or.inl ⟨([1, 1], [1, 1], [[-2, 2], [2, -2]]), by decide, ?_⟩)
    refine ⟨e, T.multiplicity i, T.weight i, hmi, hwi, ?_, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp [← hidef, ← hjdef, hmeq]
    · intro k; fin_cases k <;> simp [← hidef, ← hjdef, hweq]
    · intro k l
      fin_cases k <;> fin_cases l
      all_goals simp [← hidef, ← hjdef, (h i).2, (h j).2, hweq, hp, T.intersection_symm j i]
      all_goals ring
    · exact fun k => (h _).1
  · -- The first component carries the small weight: the doubled edge, as listed.
    have hwij : T.weight i = 4 * T.weight j := by linarith [hp, hq]
    have hmij : T.multiplicity j = 2 * T.multiplicity i := by linarith
    refine Or.inr (Or.inl ⟨([2, 1], [1, 4], [[-2, 4], [4, -8]]), by decide, ?_⟩)
    refine ⟨(Equiv.swap 0 1).trans e, T.multiplicity i, T.weight j, hmi, hwj, ?_, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp [← hidef, ← hjdef, hmij]
    · intro k; fin_cases k <;> simp [← hidef, ← hjdef, hwij]
    · intro k l
      fin_cases k <;> fin_cases l
      all_goals simp [← hidef, ← hjdef, (h i).2, (h j).2, hwij, hp, T.intersection_symm j i]
      all_goals ring
    · exact fun k => (h _).1
  · -- The second component carries the small weight: the doubled edge, with the roles swapped.
    have hwji : T.weight j = 4 * T.weight i := by linarith [hp, hq]
    have hmji : T.multiplicity i = 2 * T.multiplicity j := by linarith
    refine Or.inr (Or.inl ⟨([2, 1], [1, 4], [[-2, 4], [4, -8]]), by decide, ?_⟩)
    refine ⟨e, T.multiplicity j, T.weight i, hmj, hwi, ?_, ?_, ?_, ?_⟩
    · intro k; fin_cases k <;> simp [← hidef, ← hjdef, hmji]
    · intro k; fin_cases k <;> simp [← hidef, ← hjdef, hwji]
    · intro k l
      fin_cases k <;> fin_cases l
      all_goals simp [← hidef, ← hjdef, (h i).2, (h j).2, hwji, hq, T.intersection_symm j i]
      all_goals ring
    · exact fun k => (h _).1

/-- **Stacks Project, Tag 0C8T**, cases (2) and (3). A numerical type with two components is
minimal of genus one exactly when it is one of the first two exceptional configurations. -/
@[stacks 0C8T "the classification for two components, cases (2) and (3)"]
public lemma isMinimal_and_genus_eq_one_iff_of_componentCount_eq_two (T : NumericalType)
    (hn : T.componentCount = 2) :
    (IsMinimal T ∧ genus T = 1) ↔ IsGenusOneConfiguration T :=
  ⟨fun hT => isGenusOneConfiguration_of_componentCount_eq_two T hn
      (forall_isMinusTwoIndex_of_isMinimal_of_genus_eq_one T hT.1 hT.2 (by omega)),
    isMinimal_and_genus_eq_one_of_isGenusOneConfiguration T⟩

end AlgebraicGeometry.NumericalType
