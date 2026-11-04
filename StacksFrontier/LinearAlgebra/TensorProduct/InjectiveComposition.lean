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

/-!
# Universal injectivity of the first map in a composition

Let `R` be a commutative semiring, let `f : M →ₗ[R] M'` and `g : M' →ₗ[R] M''` be `R`-module maps
and let `Q` be an `R`-module. If `(g ∘ f) ⊗ id_Q` is injective, then so is `f ⊗ id_Q`. Quantified
over `Q`, this says that if the composition `g ∘ f` is universally injective, then so is `f`.

## Main results

* `Stacks.TensorProduct.RightFactorInjective.solution`: if `(g ∘ₗ f) ⊗ id_Q` is injective, then
  so is `f ⊗ id_Q`.
* `Function.Injective.of_rTensor_comp`: the same statement, in the `Function.Injective`
  namespace.

## References

* [Stacks Project, Tag 05CJ](https://stacks.math.columbia.edu/tag/05CJ)
-/

@[expose] public section

@[expose] public section

namespace Stacks.TensorProduct.RightFactorInjective

/-- If `(g ∘ₗ f) ⊗ id_Q` is injective, then so is `f ⊗ id_Q`. -/
public theorem solution {R : Type*} [CommSemiring R] {M M' M'' Q : Type*} [AddCommMonoid M]
    [Module R M] [AddCommMonoid M'] [Module R M'] [AddCommMonoid M''] [Module R M'']
    [AddCommMonoid Q] [Module R Q] {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (h : Function.Injective ((g ∘ₗ f).rTensor Q)) : Function.Injective (f.rTensor Q) :=
  .of_comp (f := g.rTensor Q) <| by rwa [← LinearMap.coe_comp, ← LinearMap.rTensor_comp]

end Stacks.TensorProduct.RightFactorInjective

end

@[expose] public section

/-- Let `f : M →ₗ[R] M'` and `g : M' →ₗ[R] M''` be `R`-module maps and let `Q` be an `R`-module.
If `(g ∘ₗ f) ⊗ id_Q` is injective, then so is `f ⊗ id_Q`. Quantifying over `Q`: if the
composition `g ∘ₗ f` is universally injective, then `f` is universally injective. -/
@[stacks 05CJ "Stated for one test module `Q`; the source's form is its closure over `Q`."]
public theorem Function.Injective.of_rTensor_comp {R : Type*} [CommSemiring R] {M M' M'' Q : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M'] [AddCommMonoid M'']
    [Module R M''] [AddCommMonoid Q] [Module R Q] {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (h : Function.Injective ((g ∘ₗ f).rTensor Q)) : Function.Injective (f.rTensor Q) :=
  Stacks.TensorProduct.RightFactorInjective.solution h

end
