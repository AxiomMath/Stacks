module

public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The principal divisor of a rational function as a cycle

Let `C = (S, δ)` be a Chow situation, let `X` be integral and locally of finite type over `S`
with `dim_δ(X) = n`, and let `f` be a nonzero rational function on `X`. The principal divisor

  `div(f) = ∑_Z ord_Z(f) [Z]`

of Stacks 0BE3 is then a cycle of delta-dimension `n - 1` (Stacks 02RO).

## Main definitions

* `Stacks.Chow.principalDivisorCycle` — `div(f)` as an element of `Z_{n-1}(X)`.

## Main results

* `Stacks.Chow.principalCycle_mem_cyclesOfDimension` — `div(f)` has delta-dimension `n - 1`.
* `Stacks.Chow.principalDivisorCycle_apply` — the coefficient of `div(f)` at a point is the
  order of vanishing of `f` there.

## References

* [Stacks Project, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3)
* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
* [Stacks Project, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

/-- The principal divisor of a rational function on an integral scheme of delta-dimension `n`
over the base is a cycle of delta-dimension `n - 1`. -/
theorem principalCycle_mem_cyclesOfDimension (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X] [IsLocallyNoetherian X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) (f : X.functionField) :
    principalCycle X f ∈ cyclesOfDimension C p (n - 1) := by
  intro Z hZ
  have hx : coheight Z.isIrreducible.genericPoint = 1 := by
    by_contra h
    exact hZ (by simpa using X.ord_eq_zero_of_coheight_neq_one h f)
  have heq : IrreducibleCloseds.closureSingleton Z.isIrreducible.genericPoint = Z :=
    IrreducibleCloseds.ext
      (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).def
  rw [← heq]
  exact deltaDimension_closure_singleton_eq_sub_one C p hn hx

/-- The principal divisor `div(f) = ∑_Z ord_Z(f) [Z]` of a rational function on an integral
scheme `X` of delta-dimension `n` locally of finite type over the base, as an element of the
group `Z_{n-1}(X)` of cycles of delta-dimension `n - 1`. -/
@[stacks 02RO, ega "IV 21.6.7" "cyc(div(f))"]
def principalDivisorCycle (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] [IsIntegral X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) (f : X.functionField) :
    CycleGroup C p (n - 1) :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  ⟨principalCycle X f, principalCycle_mem_cyclesOfDimension C p hn f⟩

/-- The coefficient of the principal divisor of `f` at a point of `X` is the order of vanishing
of `f` there. -/
@[simp]
theorem principalDivisorCycle_apply (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] [IsIntegral X] [IsLocallyNoetherian X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) (f : X.functionField) (z : X) :
    (principalDivisorCycle C p hn f : AlgebraicCycle X ℤ) z = X.ord f z :=
  rfl

end Stacks.Chow

end
