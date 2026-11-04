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

@[expose] public section

universe u v

/-! # Geometrically connected algebras

Let `k` be a field and let `S` be a `k`-algebra. Then `S` is *geometrically connected over `k`*
if for every field extension `K/k` the spectrum of `K ⊗[k] S` is connected, i.e. is nonempty and
is not the disjoint union of two nonempty open and closed subsets. Taking `K = k` shows that the
spectrum of a geometrically connected algebra is itself connected, and the condition is strictly
stronger: `ℂ` is a field, so `Spec ℂ` is a point, but `ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ` has a two-point
spectrum, so `ℂ` is not geometrically connected over `ℝ`.

## Main definitions

* `Algebra.IsGeometricallyConnected`: the `k`-algebra `S` is geometrically connected over the
  field `k`, that is, `PrimeSpectrum (K ⊗[k] S)` is a connected space for every field extension
  `K/k` in the universe of `k`.

## References

* [Stacks 037T](https://stacks.math.columbia.edu/tag/037T)
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra

/-- A `k`-algebra `S` over a field `k` is *geometrically connected over `k`* if for every field
extension `K/k` the spectrum of `K ⊗[k] S` is connected. -/
@[stacks 037T]
public class IsGeometricallyConnected (k : Type u) (S : Type v) [Field k] [CommRing S]
    [Algebra k S] : Prop where
  /-- For every field extension `K/k`, the spectrum of `K ⊗[k] S` is a connected space. -/
  connectedSpace_primeSpectrum_tensorProduct (K : Type u) [Field K] [Algebra k K] :
    ConnectedSpace (PrimeSpectrum (K ⊗[k] S))

end Algebra

end
