module

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
public import StacksFrontier.Topology.Spectral.BijectionHomeomorph
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible sets stable under specialization or generalization

In a Noetherian sober topological space, a constructible subset stable under generalization is
open, and a constructible subset stable under specialization is closed.

## Main results

* `isOpen_of_stableUnderGeneralization_of_isConstructible`: a constructible set stable under
  generalization is open.
* `isClosed_of_stableUnderSpecialization_of_isConstructible`: a constructible set stable under
  specialization is closed.
-/

@[expose] public section

universe u

open TopologicalSpace Topology Set

/-- A Noetherian sober `T0` space is spectral. Every subset of a Noetherian space is
quasi-compact, which at once gives quasi-compactness of the space, a basis of quasi-compact
opens (all opens are quasi-compact) and quasi-separatedness. -/
@[ega "0 2.2.4" "special case"]
lemma SpectralSpace.of_noetherianSpace (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    [QuasiSober X] [T0Space X] : SpectralSpace X :=
  have : PrespectralSpace X :=
    .of_isTopologicalBasis isTopologicalBasis_opens fun U _ => NoetherianSpace.isCompact U
  have : QuasiSeparatedSpace X := ⟨fun _ _ _ _ _ _ => NoetherianSpace.isCompact _⟩
  ⟨⟩

/-- **Stacks 0542** (2).
In a Noetherian sober topological space, every constructible subset that is stable under
generalization is open. -/
@[stacks 0542 "(2)",
  ega "IV 12.0.2" "more general",
  ega "IV 2.3.6" "(i), special case",
  ega "IV 7.9.10" "(ii)",
  sga "1 IV 6.3" "special case",
  sga "1 IV 6.4" "special case",
  sga "3 XV 3.3" "special case",
  sga "3 XV 6.6" "special case"]
theorem isOpen_of_stableUnderGeneralization_of_isConstructible
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X] [T0Space X]
    (E : Set X) (hcon : Topology.IsConstructible E) (hgen : StableUnderGeneralization E) :
    IsOpen E :=
  have := SpectralSpace.of_noetherianSpace X
  Topology.IsConstructible.isOpen_of_stableUnderGeneralization hcon hgen

/-- **Stacks 0542** (1).
In a Noetherian sober topological space, every constructible subset that is stable under
specialization is closed. -/
@[stacks 0542 "(1)", sga "3 XV 3.3" "special case"]
theorem isClosed_of_stableUnderSpecialization_of_isConstructible
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X] [T0Space X]
    (E : Set X) (hcon : Topology.IsConstructible E) (hspec : StableUnderSpecialization E) :
    IsClosed E := by
  rw [← isOpen_compl_iff]
  exact isOpen_of_stableUnderGeneralization_of_isConstructible
    X Eᶜ hcon.compl hspec.compl

