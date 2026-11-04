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
public import Mathlib.Topology.Sheaves.SheafOfFunctions

/-!
# Stacks 006X — The pointwise product of a family of sets is a sheaf

Stacks 006X constructs a sheaf of sets from a family of sets `(A x)` indexed by the points of a
topological space `X`: the presheaf `Π` with `Π(U) = ∏_{x ∈ U} A x` and restriction sending
`(a_x)_{x ∈ U}` to `(a_x)_{x ∈ V}` for `V ⊆ U`.

## Main results

* `presheafToTypes_isSheaf`: Mathlib's `TopCat.presheafToTypes X A`, whose sections over `U` are
  the dependent functions `∀ x : U, A x`, is a sheaf.
-/

@[expose] public section

open CategoryTheory TopCat Opposite

universe u

/-- Let `X` be a topological space and `A : X → Type u` a family of sets indexed by the points of
`X`. The pointwise product presheaf `Π`, given on an open `U` by `Π(U) = ∏_{x ∈ U} A x` (encoded as
the dependent product `∀ x : U, A x`, i.e. Mathlib's `TopCat.presheafToTypes X A`), with
restriction sending `(a_x)_{x ∈ U}` to `(a_x)_{x ∈ V}` for `V ⊆ U`, is a sheaf of sets. -/
@[stacks 006X]
theorem presheafToTypes_isSheaf {X : TopCat.{u}} (A : X → Type u) :
    (X.presheafToTypes A).IsSheaf :=
  TopCat.Presheaf.toTypes_isSheaf X A

