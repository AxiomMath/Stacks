module

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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Irreducible subsets of a Hausdorff space

In a Hausdorff space the irreducible subsets are exactly the singletons, so the space is
irreducible only when it has a single point. Consequently every Hausdorff space is sober:
it is Kolmogorov, and the unique point of an irreducible closed subset is its generic point.

## Main results

* `t2Space_iff_stacks`: `T2Space` is separation of distinct points by disjoint opens.
* `isIrreducible_iff_singleton_of_t2`: a subset of a Hausdorff space is irreducible iff it is
  a singleton.
* `irreducibleSpace_iff_univ_singleton_of_t2`: a Hausdorff space is irreducible iff it has
  exactly one point.
* `quasiSober_of_t2`, `sober_of_t2`: a Hausdorff space is quasi-sober, hence sober.
-/

@[expose] public section

/-- A space is Hausdorff exactly when any two distinct points are separated by disjoint
open sets. -/
theorem t2Space_iff_stacks (X : Type*) [TopologicalSpace X] :
    T2Space X ↔
      ∀ x y : X, x ≠ y → ∃ U V : Set X,
        IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V :=
  ⟨fun _ _ _ hxy => T2Space.t2 hxy, fun h => ⟨fun _ _ hxy => h _ _ hxy⟩⟩

/-- **Stacks 004Y** (subset irreducible iff singleton).
A subset `s` of a Hausdorff space `X` is irreducible if and only if `s` is a singleton. -/
@[stacks 004Y "subset irreducible iff singleton"]
theorem isIrreducible_iff_singleton_of_t2 (X : Type*) [TopologicalSpace X]
    [T2Space X] (s : Set X) :
    IsIrreducible s ↔ ∃ x : X, s = {x} :=
  isIrreducible_iff_singleton

/-- **Stacks 004Y** (space irreducible iff singleton).
A Hausdorff space `X` is irreducible as a space if and only if its underlying set is a
singleton. -/
@[stacks 004Y "space irreducible iff singleton"]
theorem irreducibleSpace_iff_univ_singleton_of_t2 (X : Type*)
    [TopologicalSpace X] [T2Space X] :
    IrreducibleSpace X ↔ ∃ x : X, (Set.univ : Set X) = {x} := by
  refine ⟨fun h => (isIrreducible_iff_singleton_of_t2 X Set.univ).mp
    h.isIrreducible_univ, fun hx => ?_⟩
  have hirr : IsIrreducible (Set.univ : Set X) :=
    (isIrreducible_iff_singleton_of_t2 X Set.univ).mpr hx
  have : PreirreducibleSpace X := ⟨hirr.isPreirreducible⟩
  exact ⟨⟨hirr.nonempty.choose⟩⟩

/-- A Hausdorff space satisfies Mathlib's `QuasiSober` predicate: every
irreducible closed subset has a generic point. -/
theorem quasiSober_of_t2 (X : Type*) [TopologicalSpace X] [T2Space X] :
    QuasiSober X := by
  refine ⟨?_⟩
  intro S hirr _
  obtain ⟨x, rfl⟩ := (isIrreducible_iff_singleton_of_t2 X S).mp hirr
  exact ⟨x, isClosed_singleton.closure_eq⟩

/-- **Stacks 004Y** (Hausdorff implies sober).
A Hausdorff space is `T0` and quasi-sober, that is, sober. -/
@[stacks 004Y "Hausdorff implies sober", sga "4 IV 4.2.1" "Hausdorff ⇒ sober"]
theorem sober_of_t2 (X : Type*) [TopologicalSpace X] [T2Space X] :
    T0Space X ∧ QuasiSober X :=
  ⟨inferInstance, quasiSober_of_t2 X⟩

