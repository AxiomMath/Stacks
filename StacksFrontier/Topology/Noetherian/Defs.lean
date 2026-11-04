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
* `isLocallyNoetherianSpace_of_noetherianSpace`: a Noetherian space is locally Noetherian.
-/

@[expose] public section

open TopologicalSpace

/-- A topological space is Noetherian if and only if its lattice of closed subsets is
well-founded for the strict order. -/
@[stacks 0051, ega "0 2.2.1" "opens max ⇔ closeds min", sga "3 V 7.2" "partial"]
theorem noetherianSpace_iff_wellFoundedLT_closeds
    (X : Type*) [TopologicalSpace X] :
    NoetherianSpace X ↔ WellFoundedLT (Closeds X) :=
  (TopologicalSpace.noetherianSpace_TFAE X).out 1 2

/-- A Noetherian topological space is locally Noetherian. -/
theorem isLocallyNoetherianSpace_of_noetherianSpace
    (X : Type*) [TopologicalSpace X] [NoetherianSpace X] :
    IsLocallyNoetherianSpace X :=
  fun x ↦ ⟨Set.univ, isOpen_univ, Set.mem_univ x, inferInstance⟩
