module

public import Mathlib.Order.Setoid.Partition
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.SetTheory.ZFC.PSet
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Partitions into locally closed subsets and their refinements

A *topological partition* of a space `X` is a set-theoretic partition of `X` all of whose parts
are locally closed. A collection of subsets refines another when each of its members is contained
in a member of the other.

## Main definitions

* `IsTopologicalPartition`: a partition of `X` all of whose parts are locally closed.
* `local_Refines`: the refinement relation between collections of subsets of `X`.

## Main results

* `refines_iff_parts_are_unions`: one topological partition refines another exactly when every
  part of the coarser one is the union of the parts of the finer one contained in it.
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- **Stacks 09XZ**.
A *topological partition* of `X` is a set-theoretic partition of `X` all of whose
parts are locally closed. -/
@[stacks 09XZ]
def IsTopologicalPartition (c : Set (Set X)) : Prop :=
  Setoid.IsPartition c ∧ ∀ s ∈ c, IsLocallyClosed s

/-- **Stacks 09XZ**.
A collection `P` of subsets of `X` *refines* a collection `Q` when every member of
`P` is contained in some member of `Q`. -/
@[stacks 09XZ]
def local_Refines (P Q : Set (Set X)) : Prop :=
  ∀ s ∈ P, ∃ t ∈ Q, s ⊆ t

/-- In a set-theoretic partition `P`, if two parts share a point, they coincide. -/
private lemma eq_of_mem_of_mem_partition {α : Type*} {P : Set (Set α)}
    (hP : Setoid.IsPartition P) {s s' : Set α} (hs : s ∈ P) (hs' : s' ∈ P)
    {x : α} (hxs : x ∈ s) (hxs' : x ∈ s') : s = s' :=
  (hP.2 x).unique ⟨hs, hxs⟩ ⟨hs', hxs'⟩

/-- A topological partition `P` refines a topological partition `Q` if and only if every part
of `Q` is the union of the parts of `P` contained in it. -/
theorem refines_iff_parts_are_unions
    {P Q : Set (Set X)} (hP : IsTopologicalPartition P)
    (hQ : IsTopologicalPartition Q) :
    local_Refines P Q ↔ ∀ t ∈ Q, t = ⋃₀ {s ∈ P | s ⊆ t} := by
  obtain ⟨hPpart, -⟩ := hP
  obtain ⟨hQpart, -⟩ := hQ
  refine ⟨fun hPQ t ht ↦ Set.eq_of_subset_of_subset (fun x hx ↦ ?_)
    (fun _ ⟨_, ⟨_, hst⟩, hxs⟩ ↦ hst hxs), fun h s hs ↦ ?_⟩
  · obtain ⟨s, ⟨hsP, hxs⟩, _⟩ := hPpart.2 x
    obtain ⟨u, hu, hsu⟩ := hPQ s hsP
    exact ⟨s, ⟨hsP, eq_of_mem_of_mem_partition hQpart hu ht (hsu hxs) hx ▸ hsu⟩, hxs⟩
  · obtain ⟨x, hxs⟩ : s.Nonempty :=
      Set.nonempty_iff_ne_empty.mpr fun he ↦ hPpart.1 (he ▸ hs)
    obtain ⟨t, ⟨htQ, hxt⟩, _⟩ := hQpart.2 x
    refine ⟨t, htQ, fun y hys ↦ ?_⟩
    obtain ⟨ty, ⟨htyQ, hyty⟩, _⟩ := hQpart.2 y
    rw [h ty htyQ] at hyty
    obtain ⟨s', ⟨hs'P, hs'ty⟩, hys'⟩ := hyty
    have hsty : s ⊆ ty := eq_of_mem_of_mem_partition hPpart hs'P hs hys' hys ▸ hs'ty
    exact eq_of_mem_of_mem_partition hQpart htyQ htQ (hsty hxs) hxt ▸ hsty hys

