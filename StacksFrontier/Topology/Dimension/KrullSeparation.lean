module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Nontrivial specializations and the Krull dimension of a topological space

A chain of irreducible closed subsets is a chain of *sets*, so a nontrivial specialization
`x ⤳ y` with `x ≠ y` bounds the Krull dimension of a space from below only when the two
closures `closure {x}` and `closure {y}` are different sets. That extra condition is exactly
the Kolmogorov condition at the pair `x`, `y`: in a space which is not `T0` there are distinct
points with the same closure, and they witness a nontrivial specialization which contributes
no chain.

The failure is not a curiosity of pathological examples only: a space with the indiscrete
topology and at least two points has Krull dimension zero, is not discrete, and every ordered
pair of its points is a nontrivial specialization. The two-element indiscrete space is such a
space, and `not_forall_one_le_topologicalKrullDim_of_specializes_of_ne` records that it refutes
the implication "a nontrivial specialization between distinct points forces Krull dimension at
least one".

This matters for Stacks 0ACA, which compares, for an algebraic space `X` locally of finite type
over a field, the conditions that `|X|` be discrete, that `dim |X| = 0`, that `dim X = 0`, and
that `X → Spec k` be locally quasi-finite. The argument there produces a nontrivial
specialization with distinct images in `|X|` and reads off `dim |X| ≥ 1` from it; that step
needs `|X|` to be Kolmogorov, and the point space of an algebraic space need not be. With the
Kolmogorov hypothesis added the implication is
`AlgebraicGeometry.Space.FiniteTypeOverField.discretePoints_of_zeroTopologicalDimension`.

## Main results

* `one_le_topologicalKrullDim_of_specializes_of_closure_ne`: a nontrivial specialization whose
  two closures differ does bound the Krull dimension below by one.
* `one_le_topologicalKrullDim_of_specializes_of_ne`: in a `T0` space it suffices that the two
  points be distinct.
* `exists_ne_closure_eq_of_not_t0Space`: outside the `T0` setting distinct points can share a
  closure, and then they specialize to one another.
* `topologicalKrullDim_eq_zero_of_indiscreteTopology`,
  `not_discreteTopology_of_indiscreteTopology` and `specializes_of_indiscreteTopology`: a
  nonempty indiscrete space has Krull dimension zero, is not discrete once it has two points,
  and all of its specializations hold.
* `not_forall_one_le_topologicalKrullDim_of_specializes_of_ne`: the implication from a
  nontrivial specialization between distinct points to Krull dimension at least one is false.

## References

* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
-/

@[expose] public section

open Order Set TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-! ### When a specialization bounds the dimension from below -/

/-- The irreducible closed subset `closure {x}`. -/
private def closureSingleton (x : X) : IrreducibleCloseds X :=
  ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- A nontrivial specialization `x ⤳ y` whose two point closures are distinct sets exhibits a
strictly increasing pair of irreducible closed subsets, so the Krull dimension is at least
one. -/
theorem one_le_topologicalKrullDim_of_specializes_of_closure_ne {x y : X} (h : x ⤳ y)
    (hne : closure ({x} : Set X) ≠ closure ({y} : Set X)) :
    (1 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  have hlt : closureSingleton y < closureSingleton x :=
    lt_of_le_of_ne (specializes_iff_closure_subset.mp h) fun hEq ↦
      hne (congrArg IrreducibleCloseds.carrier hEq).symm
  exact_mod_cast one_le_krullDim_iff.mpr ⟨_, _, hlt⟩

/-- In a Kolmogorov space a nontrivial specialization between distinct points bounds the Krull
dimension below by one: distinct points of a `T0` space have distinct closures. -/
theorem one_le_topologicalKrullDim_of_specializes_of_ne [T0Space X] {x y : X} (h : x ⤳ y)
    (hne : x ≠ y) : (1 : WithBot ℕ∞) ≤ topologicalKrullDim X :=
  one_le_topologicalKrullDim_of_specializes_of_closure_ne h fun hEq ↦
    hne ((t0Space_iff_inseparable X).mp ‹_› x y (inseparable_iff_closure_eq.mpr hEq))

/-- A space which is not Kolmogorov has two distinct points which specialize to one another and
have the same closure. Such a pair is a nontrivial specialization contributing no chain of
irreducible closed subsets. -/
theorem exists_ne_closure_eq_of_not_t0Space (h : ¬ T0Space X) :
    ∃ x y : X, x ≠ y ∧ x ⤳ y ∧ y ⤳ x ∧ closure ({x} : Set X) = closure ({y} : Set X) := by
  by_contra hcon
  refine h ((t0Space_iff_inseparable X).mpr fun x y hins ↦ ?_)
  by_contra hne
  obtain ⟨hxy, hyx⟩ := inseparable_iff_specializes_and.mp hins
  exact hcon ⟨x, y, hne, hxy, hyx, inseparable_iff_closure_eq.mp hins⟩

/-! ### Indiscrete spaces -/

/-- The only irreducible closed subset of an indiscrete space is the whole space: a closed
subset is empty or everything, and an irreducible one is nonempty. -/
theorem TopologicalSpace.IrreducibleCloseds.subsingleton_of_indiscreteTopology
    [IndiscreteTopology X] : Subsingleton (IrreducibleCloseds X) := by
  have huniv (C : IrreducibleCloseds X) : C.carrier = univ :=
    ((IndiscreteTopology.isClosed_iff C.carrier).mp C.isClosed).resolve_left
      C.isIrreducible.nonempty.ne_empty
  exact ⟨fun A B ↦ IrreducibleCloseds.ext ((huniv A).trans (huniv B).symm)⟩

/-- A nonempty indiscrete space has Krull dimension zero: it has exactly one irreducible closed
subset, namely itself. -/
theorem topologicalKrullDim_eq_zero_of_indiscreteTopology [IndiscreteTopology X] [Nonempty X] :
    topologicalKrullDim X = (0 : WithBot ℕ∞) := by
  have : Subsingleton (IrreducibleCloseds X) :=
    IrreducibleCloseds.subsingleton_of_indiscreteTopology
  have : Nonempty (IrreducibleCloseds X) := ⟨closureSingleton (Classical.arbitrary X)⟩
  exact krullDim_eq_zero

/-- An indiscrete space with at least two points is not discrete. -/
theorem not_discreteTopology_of_indiscreteTopology [IndiscreteTopology X] [Nontrivial X] :
    ¬ DiscreteTopology X := by
  intro hdisc
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  have hopen : IsOpen ({x} : Set X) := isOpen_discrete _
  rcases (IndiscreteTopology.isOpen_iff ({x} : Set X)).mp hopen with hempty | huniv
  · exact absurd (hempty ▸ rfl : x ∈ (∅ : Set X)) (by simp)
  · exact hxy (((Set.eq_singleton_iff_unique_mem.mp huniv.symm).2 y (mem_univ y)).symm ▸ rfl)

/-- Every ordered pair of points of an indiscrete space is a specialization, since the closure
of a nonempty subset is the whole space. -/
theorem specializes_of_indiscreteTopology [IndiscreteTopology X] (x y : X) : x ⤳ y := by
  have hd : Dense ({x} : Set X) := dense_indiscrete ⟨x, rfl⟩
  rw [specializes_iff_mem_closure, hd.closure_eq]
  exact mem_univ y

/-! ### The failing implication -/

/-- A nontrivial specialization between distinct points does **not** force the Krull dimension
to be at least one. The two-element indiscrete space has Krull dimension zero, and its two
points specialize to one another.

In a Kolmogorov space the implication does hold, by
`one_le_topologicalKrullDim_of_specializes_of_ne`; what a general space provides instead is
`one_le_topologicalKrullDim_of_specializes_of_closure_ne`, whose hypothesis is that the two
closures differ. -/
theorem not_forall_one_le_topologicalKrullDim_of_specializes_of_ne :
    ¬ ∀ (Y : Type) (t : TopologicalSpace Y) (y z : Y),
        @Specializes Y t y z → y ≠ z → (1 : WithBot ℕ∞) ≤ @topologicalKrullDim Y t := by
  intro h
  have hspec : @Specializes Bool ⊤ true false :=
    @specializes_of_indiscreteTopology Bool ⊤ inferInstance true false
  have hdim : @topologicalKrullDim Bool ⊤ = (0 : WithBot ℕ∞) :=
    @topologicalKrullDim_eq_zero_of_indiscreteTopology Bool ⊤ inferInstance inferInstance
  have hone := h Bool ⊤ true false hspec (by simp)
  rw [hdim] at hone
  exact absurd hone (not_le.mpr zero_lt_one)

/-- An indiscrete space with at least two points separates condition (3) of Stacks 0ACA from
condition (2): its Krull dimension is zero while it is not discrete. -/
theorem topologicalKrullDim_eq_zero_and_not_discreteTopology_of_indiscreteTopology
    [IndiscreteTopology X] [Nontrivial X] :
    topologicalKrullDim X = (0 : WithBot ℕ∞) ∧ ¬ DiscreteTopology X :=
  have : Nonempty X := inferInstance
  ⟨topologicalKrullDim_eq_zero_of_indiscreteTopology, not_discreteTopology_of_indiscreteTopology⟩

end
