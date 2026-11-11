module

public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Noetherian topological spaces via well-foundedness

A topological space is Noetherian exactly when its lattice of closed sets is well-founded for
the strict order, and every Noetherian space is locally Noetherian.

## Main results

* `noetherianSpace_iff_wellFoundedLT_closeds`: `NoetherianSpace X` is equivalent to
  `WellFoundedLT (Closeds X)`.
* `isLocallyNoetherianSpace_iff_forall_exists_mem_nhds`: `IsLocallyNoetherianSpace X` (every
  point has a Noetherian open neighbourhood) is equivalent to every point having a Noetherian
  neighbourhood in the sense of Stacks, i.e. any subset containing an open set containing it.
* `isLocallyNoetherianSpace_of_noetherianSpace`: a Noetherian space is locally Noetherian.
-/

@[expose] public section

open TopologicalSpace

/-- A topological space is Noetherian if and only if its lattice of closed subsets is
well-founded for the strict order. -/
@[stacks 0051 "Part (1): a space is Noetherian iff the descending chain condition holds for its
  closed subsets; part (2) is `isLocallyNoetherianSpace_iff_forall_exists_mem_nhds`.",
  ega "0 2.2.1" "opens max ⇔ closeds min", sga "3 V 7.2" "partial"]
theorem noetherianSpace_iff_wellFoundedLT_closeds
    (X : Type*) [TopologicalSpace X] :
    NoetherianSpace X ↔ WellFoundedLT (Closeds X) :=
  (TopologicalSpace.noetherianSpace_TFAE X).out 1 2

/-- A Noetherian topological space is locally Noetherian. -/
theorem isLocallyNoetherianSpace_of_noetherianSpace
    (X : Type*) [TopologicalSpace X] [NoetherianSpace X] :
    IsLocallyNoetherianSpace X :=
  fun x ↦ ⟨Set.univ, isOpen_univ, Set.mem_univ x, inferInstance⟩

/-- A topological space is locally Noetherian, i.e. every point has a Noetherian open
neighbourhood, if and only if every point has a neighbourhood (a subset containing an open set
containing the point) which is Noetherian in the induced topology. -/
@[stacks 0051 "Part (2): the definition of a locally Noetherian space, with Stacks'
  neighbourhoods (any subset containing an open set containing the point)."]
theorem isLocallyNoetherianSpace_iff_forall_exists_mem_nhds
    (X : Type*) [TopologicalSpace X] :
    IsLocallyNoetherianSpace X ↔ ∀ x : X, ∃ N ∈ nhds x, NoetherianSpace N := by
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨U, hU, hxU, hN⟩ := h x
    exact ⟨U, hU.mem_nhds hxU, hN⟩
  · obtain ⟨N, hN, hNN⟩ := h x
    obtain ⟨U, hUN, hU, hxU⟩ := mem_nhds_iff.mp hN
    refine ⟨U, hU, hxU, (noetherianSpace_set_iff U).mpr fun t ht ↦ ?_⟩
    exact (noetherianSpace_set_iff N).mp hNN t (ht.trans hUN)
