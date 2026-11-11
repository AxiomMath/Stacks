module

public import Mathlib.Order.Setoid.Partition
public import Mathlib.Order.CompletePartialOrder
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
public import StacksCore.Tactic.StacksAttribute

/-!
# Good stratifications of a topological space

A *good stratification* is a partition of a topological space into nonempty strata satisfying the
frontier condition: a stratum meeting the closure of another stratum is contained in that closure.

## Main definitions

* `IsGoodStratification`: the good stratification condition on a family `S : I → Set X`.

## Main results

* `isGoodStratification_iff`: the condition unbundled as a conjunction.
* `IsGoodStratification.isPartition_range`: the strata of an injectively indexed good
  stratification form a `Setoid.IsPartition`.
-/

@[expose] public section

open Set Topology

/-- A *good stratification* of a topological space `X`, indexed by `I`, is a
family of subsets `S : I → Set X` which forms a partition (the sets are
pairwise disjoint, each nonempty, and their union covers `X`) and which
satisfies the frontier condition: if `S i ∩ closure (S j) ≠ ∅`, then
`S i ⊆ closure (S j)`. This variant of Stacks 09Y0 (registered on `IsGoodPartition`) asks the
strata to be nonempty and does not ask them to be locally closed. -/
structure IsGoodStratification {X : Type*} [TopologicalSpace X] {I : Type*}
    (S : I → Set X) : Prop where
  /-- Each stratum is nonempty. -/
  nonempty : ∀ i, (S i).Nonempty
  /-- Distinct strata are disjoint. -/
  disjoint : ∀ ⦃i j⦄, i ≠ j → Disjoint (S i) (S j)
  /-- The strata cover the whole space. -/
  iUnion_eq : ⋃ i, S i = Set.univ
  /-- Frontier condition: if a stratum meets the closure of another, it is
  contained in it. -/
  subset_closure_of_inter_closure_nonempty :
    ∀ ⦃i j⦄, (S i ∩ closure (S j)).Nonempty → S i ⊆ closure (S j)

/-- A family `S` is a good stratification iff it is a partition (in the indexed
sense — disjoint, nonempty, covering) and any stratum that meets the closure of
another is contained in it. -/
theorem isGoodStratification_iff {X : Type*} [TopologicalSpace X] {I : Type*}
    (S : I → Set X) :
    IsGoodStratification S ↔
      ((∀ i, (S i).Nonempty) ∧
       (∀ ⦃i j⦄, i ≠ j → Disjoint (S i) (S j)) ∧
       ((⋃ i, S i) = Set.univ) ∧
       (∀ ⦃i j⦄, (S i ∩ closure (S j)).Nonempty → S i ⊆ closure (S j))) :=
  ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

/-- The strata of a good stratification indexed injectively form a partition in
the sense of `Setoid.IsPartition`. -/
theorem IsGoodStratification.isPartition_range {X : Type*} [TopologicalSpace X]
    {I : Type*} {S : I → Set X} (hS : IsGoodStratification S)
    (_hS_inj : Function.Injective S) :
    Setoid.IsPartition (Set.range S) := by
  refine ⟨?_, fun x => ?_⟩
  · rintro ⟨i, hi⟩
    exact not_nonempty_empty (hi ▸ hS.nonempty i)
  · obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp (hS.iUnion_eq ▸ mem_univ x)
    refine ⟨S i₀, ⟨⟨i₀, rfl⟩, hi₀⟩, ?_⟩
    rintro b ⟨⟨i, rfl⟩, hxi⟩
    congr 1
    by_contra hne
    exact (hS.disjoint hne).notMem_of_mem_left hxi hi₀

