module
public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.ExtremallyDisconnected
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

/-!
# The Stone–Čech compactification of a discrete space

## Main definitions

* `stoneCechAsProfinite`: the Stone–Čech compactification of a discrete space, as a profinite
  space.

## Main results

* `stoneCech_projective_of_discrete`: for a discrete space `X`, `StoneCech X` is projective among
  quasi-compact Hausdorff spaces.
* `stoneCech_extremallyDisconnected_of_discrete` (Stacks 090C): `StoneCech X` is extremally
  disconnected.
* `stoneCech_totallyDisconnected_of_discrete` (Stacks 090C): `StoneCech X` is totally
  disconnected.
-/

@[expose] public section

/-- **Stacks 090C.** The Stone–Čech compactification of a discrete topological space is
extremally disconnected. -/
@[stacks 090C]
theorem stoneCech_extremallyDisconnected_of_discrete
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    ExtremallyDisconnected (StoneCech X) :=
  CompactT2.projective_iff_extremallyDisconnected.mp StoneCech.projective

/-- **Stacks 090C.** The Stone–Čech compactification of a discrete topological space is totally
disconnected. -/
@[stacks 090C]
theorem stoneCech_totallyDisconnected_of_discrete
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    TotallyDisconnectedSpace (StoneCech X) :=
  have := stoneCech_extremallyDisconnected_of_discrete X
  inferInstance

/-- The Stone–Čech compactification of a discrete topological space, viewed as a profinite
space. -/
noncomputable def stoneCechAsProfinite
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X] : Profinite :=
  haveI : TotallyDisconnectedSpace (StoneCech X) :=
    stoneCech_totallyDisconnected_of_discrete X
  Profinite.of (StoneCech X)
