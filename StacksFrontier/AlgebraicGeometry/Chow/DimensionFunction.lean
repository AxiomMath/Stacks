module

public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass.WeilDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension

/-!
# The canonical dimension function on a scheme over a Chow situation

Let `C = (S, δ)` be a Chow situation — `S` locally Noetherian and universally catenary with a
dimension function `δ` on its points — and let `p : X ⟶ C.S` be locally of finite type. The
function `x ↦ δ (p x) + trdeg_{κ(p x)} κ(x)`, `Stacks.Chow.relativeDimension δ p`, is the
underlying function of a `TopologicalSpace.DimensionFunction` on `X`. This file names that
dimension function, `Stacks.Chow.deltaDimensionFunction C p`, and computes the delta-dimension
of a codimension-one integral closed subscheme and of the cycle of a Weil divisor on an integral
`X` of delta-dimension `n`.

## Main definitions

* `Stacks.Chow.deltaDimensionFunction` — the dimension function on `X` whose value at `x` is
  `δ (p x) + trdeg_{κ(p x)} κ(x)`.
* `Stacks.Chow.weilDivisorCycleOfDeltaDimension` — the cycle of a Weil divisor on an integral
  `X` of delta-dimension `n`, as an element of `Z_{n-1}(X)` with its coefficient
  specification.

## Main results

* `Stacks.Chow.deltaDimensionFunction_apply` — the values of `deltaDimensionFunction` are the
  relative dimensions.
* `Stacks.Chow.deltaDimension_closure_singleton_eq_sub_one` — on an integral scheme of
  delta-dimension `n`, an integral closed subscheme of codimension one has delta-dimension
  `n - 1`.
* `Stacks.Chow.weilDivisorAlgebraicCycle_mem_cyclesOfDimension_sub_one` — the cycle of a Weil
  divisor on such a scheme has delta-dimension `n - 1`.

## References

* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-- The dimension function on `X` induced by the dimension function of the base along a locally
finite-type morphism `p : X ⟶ C.S`, whose values are the relative dimensions. -/
def deltaDimensionFunction (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] : DimensionFunction X :=
  (relativeDimension_isDimensionFunction C.isUniversallyCatenary C.dimensionFunction p).choose

/-- The dimension function `Stacks.Chow.deltaDimensionFunction C p` takes the value
`δ (p x) + trdeg_{κ(p x)} κ(x)` at a point `x` of `X`. -/
@[simp]
theorem deltaDimensionFunction_apply (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (x : X) :
    deltaDimensionFunction C p x = relativeDimension C.dimensionFunction p x :=
  (relativeDimension_isDimensionFunction C.isUniversallyCatenary
    C.dimensionFunction p).choose_spec x

/-- On an integral scheme of delta-dimension `n` over the base, an integral closed subscheme of
codimension one has delta-dimension `n - 1`. -/
theorem deltaDimension_closure_singleton_eq_sub_one (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) {x : X} (hx : coheight x = 1) :
    deltaDimension C p
        ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩ = n - 1 :=
  deltaDimension_closure_singleton_of_coheight_one C p hn (deltaDimensionFunction_apply C p) hx

/-- On an integral scheme of delta-dimension `n` the cycle of a Weil divisor has
delta-dimension `n - 1`. -/
theorem weilDivisorAlgebraicCycle_mem_cyclesOfDimension_sub_one (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) (D : WeilDivisor X) :
    weilDivisorAlgebraicCycle D ∈ cyclesOfDimension C p (n - 1) :=
  weilDivisorAlgebraicCycle_mem_cyclesOfDimension C p hn (deltaDimensionFunction_apply C p) D

/-- The cycle of a Weil divisor on an integral scheme of delta-dimension `n`, as an element of
`Z_{n-1}(X)` together with its coefficient specification. -/
def weilDivisorCycleOfDeltaDimension (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] [IsIntegral X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) (D : WeilDivisor X) :
    { c : CycleGroup C p (n - 1) // IsWeilDivisorCycle C p n D.val c } :=
  weilDivisorCycle C p hn (deltaDimensionFunction_apply C p) D

end Stacks.Chow

end
