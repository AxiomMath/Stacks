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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A field of finite type over a Jacobson ring

Let `R` be a Jacobson ring and let `K` be a field which is of finite type as an `R`-algebra.
Then the kernel of `algebraMap R K` is a maximal ideal of `R`. In the situation of the source,
where `R ⊂ K` is a subring, that kernel is `⊥`, so the assertion is that `R` is a field; the
companion assertion that `K/R` is a finite extension is Mathlib's
`finite_of_finite_type_of_isJacobsonRing`.

## Main results

* `Algebra.ker_algebraMap_isMaximal_of_finiteType_of_isJacobsonRing`: for `K` a field of finite
  type over a Jacobson ring `R`, the ideal `RingHom.ker (algebraMap R K)` is maximal.

## Implementation notes

The source states two conclusions under the hypothesis `R ⊂ K`: that `R` is a field, and that
`K/R` is a finite field extension. The second is exactly Mathlib's
`finite_of_finite_type_of_isJacobsonRing`, which already carries this tag upstream, so it is
not restated here; only the first is, and in the form that drops the inclusion hypothesis.
Dropping it costs nothing and gains the form a user wants: `R ⊂ K` is used in the source only
to identify the kernel with `⊥`, and `Ring.isField_iff_maximal_bot` turns the maximality
statement back into `IsField R` as soon as `algebraMap R K` is injective. The general form is
also the one the source's own applications need — in Tag 00GB the lemma is applied to
`R → S/𝔪'`, whose kernel is the contracted ideal `𝔪 = 𝔪' ∩ R`, and the kernel form gives its
maximality without passing to `R/𝔪` first. The name mutates the Mathlib sibling
`Algebra.ker_algebraMap_isMaximal_of_isIntegral`, which is the same conclusion with
integrality in place of the Jacobson and finite-type hypotheses.

Faithfulness. (1) No hypothesis is dead: `Field K` and `Algebra.FiniteType R K` and
`IsJacobsonRing R` are all used, and the source's `R ⊂ K` is dropped rather than carried
unused. (2) The base is the source's: `R` is the Jacobson ring itself and `K` the field itself,
with no quotient or localization interposed. (3) The map the source writes as the inclusion
`R ⊂ K` is pinned as `algebraMap R K`, and the ideal is its kernel, not merely some maximal
ideal asserted to exist. (4) A witness: `R = k[X]` for a field `k`, `K = k` with `X ↦ 0`, where
the kernel is the nonzero maximal ideal `(X)`; the source's own case is `R = K = ℚ`, kernel `⊥`,
giving `IsField ℚ`.

## References

* [StackProject 0CY7](https://stacks.math.columbia.edu/tag/0CY7)
-/

@[expose] public section

/-- **Stacks 0CY7.** Let `R` be a Jacobson ring and let `K` be a field which is of finite type
as an `R`-algebra. Then `RingHom.ker (algebraMap R K)` is a maximal ideal of `R`. In particular,
if `R` is a subring of `K` then `R` is a field; that `K` is then finite over `R` is
`finite_of_finite_type_of_isJacobsonRing`. -/
@[stacks 0CY7, ega "IV 10.4.6" "preimage of max ideal"]
public theorem Algebra.ker_algebraMap_isMaximal_of_finiteType_of_isJacobsonRing
    (R K : Type*) [CommRing R] [Field K] [Algebra R K] [IsJacobsonRing R]
    [Algebra.FiniteType R K] :
    (RingHom.ker (algebraMap R K)).IsMaximal := by
  have : Module.Finite R K := finite_of_finite_type_of_isJacobsonRing R K
  exact Algebra.ker_algebraMap_isMaximal_of_isIntegral R K

end
