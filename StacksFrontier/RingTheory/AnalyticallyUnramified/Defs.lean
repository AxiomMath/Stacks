module

public import Mathlib.RingTheory.AdicCompletion.Algebra
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

@[expose] public section



/-!
# Analytically unramified local rings

Let `(R, m)` be a local ring and let `R^ = lim_n R ⧸ mⁿ` be its `m`-adic completion. The ring `R`
is *analytically unramified* when `R^` is reduced. Following the source, a prime ideal `p ⊂ R` is
called analytically unramified when the local ring `R ⧸ p` is, that is when
`IsAnalyticallyUnramified (R ⧸ p)` holds.

Reducedness does not travel along completion. For a Noetherian local ring the map `R → R^` is a
faithfully flat local ring homomorphism, hence injective, so an analytically unramified ring is
reduced; the converse fails, there being one-dimensional Noetherian local domains whose completion
has nonzero nilpotents. Analytic unramifiedness is the hypothesis that excludes those, and it is
what makes the finiteness theorems of the Nagata theory available: an analytically unramified
Noetherian local ring has finite integral closure in its total ring of fractions, its minimal
primes are again analytically unramified, and it is N-1 when it is a domain (Tag 032Y).

## Main definitions

* `IsAnalyticallyUnramified`: the completion of the local ring `R` along its maximal ideal is
  reduced.

## Implementation notes

The completion is pinned to `AdicCompletion (IsLocalRing.maximalIdeal R) R`, Mathlib's inverse
limit of the tower `R ⧸ mⁿ`, which is the source's `R^ = lim_n R ⧸ mⁿ` and not merely some ring
that happens to receive a map from `R` with complete separated target; the ideal completed along
is `R`'s own maximal ideal, so no choice of ideal is left open.

The source states the definition for a Noetherian local ring, and `IsNoetherianRing R` is dropped
here: the tower `R ⧸ mⁿ`, its limit and reducedness of that limit are meaningful for every local
ring, nothing in the condition consumes Noetherianity, and on a Noetherian local ring the
condition is verbatim the source's. The statements that do consume it — faithful flatness of
`R → R^` (Tag 00MC), Noetherianity of `R^` (Tag 05GH), and Tag 032Y — carry it themselves.

The prime case is left as the composite `IsAnalyticallyUnramified (R ⧸ p)` rather than given a
second name: it is the ring case at the local ring `R ⧸ p`, has no property the ring case lacks,
and a name for it would only hide which ring is being completed. It does ask for
`IsLocalRing (R ⧸ p)`, which holds whenever `p ≠ ⊤` but is not an instance in Mathlib; that
obligation belongs to the statements about primes, each of which speaks of the local ring `R ⧸ p`
in any case.

The definition is the source's, point by point. Both hypotheses are used by the condition:
`CommRing R` carries the tower of quotients and `IsLocalRing R` is what supplies the ideal `m`
completed along, without which there is nothing to complete at. The ring completed is `R` itself
and the reducedness asserted is that of the ring `R^`, not of a fibre of `R → R^`, of a residue
ring of `R^`, nor of `R^` as an `R`-algebra. The object the source names is pinned rather than
asserted to exist, as above. The condition is neither vacuous nor automatic: an `m`-adically
complete Noetherian local domain is analytically unramified, the canonical map `R → R^` being
bijective there (`AdicCompletion.ofLinearEquiv`), so `ℤ_[p]` and `k[[X]]` satisfy it, while the
Noetherian local domains of Nagata with non-reduced completion do not.

## References

* [Stacks Project, Tag 032X](https://stacks.math.columbia.edu/tag/032X)
* [Stacks Project, Tag 032Y](https://stacks.math.columbia.edu/tag/032Y)
-/

@[expose] public section

/-- A local ring `R` with maximal ideal `m` is **analytically unramified** if its completion
`R^ = lim_n R ⧸ mⁿ` is reduced.

The source asks for `R` Noetherian; that hypothesis is not needed to state the condition and is
carried by the lemmas about it. A prime ideal `p ⊂ R` is analytically unramified when the local
ring `R ⧸ p` is, i.e. when `IsAnalyticallyUnramified (R ⧸ p)` holds. -/
@[stacks 032X, sga "1 I 9.4"]
public def IsAnalyticallyUnramified (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  IsReduced (AdicCompletion (IsLocalRing.maximalIdeal R) R)

/-- Analytic unramifiedness is reducedness of the completion at the maximal ideal. -/
public theorem isAnalyticallyUnramified_iff (R : Type*) [CommRing R] [IsLocalRing R] :
    IsAnalyticallyUnramified R ↔ IsReduced (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  Iff.rfl

end
