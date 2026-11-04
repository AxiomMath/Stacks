module

public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass.PrimeDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary

/-!
# The cycle of a Weil divisor

Chapter 42 of the Stacks Project turns a Weil divisor on an integral scheme `X` locally of finite
type over the base `S` into a cycle of delta-dimension one less than that of `X`. This happens
twice with the identical argument: for the principal divisor of a rational function (Stacks
02RO), and for the divisor of a nonzero meromorphic section of an invertible module (Stacks
02SJ). The passage depends on nothing about the divisor, so it is performed once here.

A Weil divisor `D = ∑ n_Z [Z]` is a coefficient family indexed by prime divisors; Mathlib's
`AlgebraicGeometry.AlgebraicCycle` is a coefficient family indexed by points. The associated
cycle has coefficient `n_Z` at the generic point of each prime divisor `Z` and `0` at every point
that is not the generic point of a prime divisor — equivalently, at every point whose coheight is
not one, by `Stacks.Divisors.PrimeDivisor.equivCoheightOne`. Local finiteness of the family of
prime divisors carrying a nonzero coefficient is exactly local finiteness of the support of that
coefficient function, since the support of a prime divisor is the closure of its generic point.

That the resulting cycle has delta-dimension `n - 1`, where `n` is the delta-dimension of `X`, is
the one step that needs Stacks 02JW — that `Stacks.Chow.relativeDimension` really is a dimension
function on `X`. As in `StacksFrontier.AlgebraicGeometry.Chow.Vocabulary`, that input is carried
here as an explicit hypothesis: a `TopologicalSpace.DimensionFunction X` whose underlying
function is `relativeDimension`.

02JW IS proved — `Stacks.Chow.relativeDimension_isDimensionFunction` in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension` — so the hypothesis is a matter of import
order rather than a gap, and the unconditional form is
`Stacks.Chow.weilDivisorCycleOfDeltaDimension` in
`StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction`. Use that in preference to this one unless
you specifically need to supply your own dimension function.

## Main definitions

* `Stacks.Chow.weilDivisorCoeff` — the coefficient function on points of `X` attached to a
  coefficient family on prime divisors.
* `Stacks.Chow.weilDivisorAlgebraicCycle` — the algebraic cycle of a Weil divisor.
* `Stacks.Chow.IsWeilDivisorCycle` — the specification of that cycle by its coefficients.
* `Stacks.Chow.weilDivisorCycle` — the cycle of a Weil divisor as an element of `Z_{n-1}(X)`,
  together with its coefficient specification.

## Main results

* `Stacks.Chow.weilDivisorCoeff_genericPoint` — the coefficient at the generic point of a prime
  divisor is the coefficient of the divisor there.
* `Stacks.Chow.weilDivisorCoeff_eq_zero` — the coefficient vanishes at every point that is not
  the generic point of a prime divisor.
* `Stacks.Chow.locallyFiniteSupport_weilDivisorCoeff` — local finiteness of the coefficient
  function.
* `Stacks.Chow.weilDivisorAlgebraicCycle_mem_cyclesOfDimension` — the cycle has
  delta-dimension `n - 1`.

## References

* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

variable {X : Scheme.{u}}

/-! ### The coefficient function of a Weil divisor -/

/-- The coefficient function on the points of `X` attached to a coefficient family on prime
divisors: at a point of coheight one it is the coefficient of the corresponding prime divisor,
and elsewhere it is zero. -/
def weilDivisorCoeff (D : PrimeDivisor X → ℤ) (x : X) : ℤ :=
  open Classical in
  if hx : coheight x = 1 then D (PrimeDivisor.ofCoheightOne x hx) else 0

/-- At the generic point of a prime divisor the coefficient function takes the value of the
divisor at that prime divisor. -/
@[simp]
theorem weilDivisorCoeff_genericPoint (D : PrimeDivisor X → ℤ) (Z : PrimeDivisor X) :
    weilDivisorCoeff D Z.genericPoint = D Z := by
  rw [weilDivisorCoeff, dite_eq_left Z.coheight_genericPoint]
  exact congrArg D
    (PrimeDivisor.genericPoint_injective (PrimeDivisor.genericPoint_ofCoheightOne _ _))

/-- The coefficient function vanishes at every point whose coheight is not one. -/
theorem weilDivisorCoeff_eq_zero_of_coheight_ne_one (D : PrimeDivisor X → ℤ) {x : X}
    (hx : coheight x ≠ 1) : weilDivisorCoeff D x = 0 :=
  dite_eq_right hx

/-- The coefficient function vanishes at every point that is not the generic point of a prime
divisor. -/
theorem weilDivisorCoeff_eq_zero (D : PrimeDivisor X → ℤ) (x : X)
    (hx : ∀ Z : PrimeDivisor X, Z.genericPoint ≠ x) : weilDivisorCoeff D x = 0 := by
  refine weilDivisorCoeff_eq_zero_of_coheight_ne_one D fun h => ?_
  exact hx (PrimeDivisor.ofCoheightOne x h) (PrimeDivisor.genericPoint_ofCoheightOne x h)

/-- A point carrying a nonzero coefficient is the generic point of a prime divisor on which the
divisor is nonzero. -/
theorem exists_primeDivisor_of_weilDivisorCoeff_ne_zero (D : PrimeDivisor X → ℤ) {x : X}
    (hx : weilDivisorCoeff D x ≠ 0) :
    ∃ Z : PrimeDivisor X, Z.genericPoint = x ∧ D Z ≠ 0 := by
  have hco : coheight x = 1 := by
    by_contra h
    exact hx (weilDivisorCoeff_eq_zero_of_coheight_ne_one D h)
  refine ⟨PrimeDivisor.ofCoheightOne x hco, PrimeDivisor.genericPoint_ofCoheightOne x hco, ?_⟩
  rwa [weilDivisorCoeff, dite_eq_left hco] at hx

/-- The coefficient function of a Weil divisor has locally finite support: a point carrying a
nonzero coefficient lies in the support of a prime divisor on which the divisor is nonzero, and
those supports form a locally finite family. -/
theorem locallyFiniteSupport_weilDivisorCoeff (D : WeilDivisor X) :
    LocallyFiniteSupport (weilDivisorCoeff D.val) := by
  intro x
  obtain ⟨U, hU, hfin⟩ := D.property x
  refine ⟨U, hU, ?_⟩
  refine (hfin.image PrimeDivisor.genericPoint).subset fun y hy => ?_
  obtain ⟨Z, hZy, hDZ⟩ := exists_primeDivisor_of_weilDivisorCoeff_ne_zero D.val hy.2
  have hyS : y ∈ Z.support := by
    rw [Z.support_eq_closure, ← hZy]
    exact subset_closure rfl
  exact ⟨Z, ⟨y, by simpa [hDZ] using hyS, hy.1⟩, hZy⟩

/-! ### The cycle of a Weil divisor -/

/-- The algebraic cycle of a Weil divisor: Mathlib's generic-point indexed form of
`D = ∑ n_Z [Z]`. -/
def weilDivisorAlgebraicCycle (D : WeilDivisor X) : AlgebraicCycle X ℤ where
  toFun := weilDivisorCoeff D.val
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' x _ := locallyFiniteSupport_weilDivisorCoeff D x

/-- The value of the cycle of a Weil divisor at a point is the coefficient `weilDivisorCoeff`
of the divisor there. -/
@[simp]
theorem weilDivisorAlgebraicCycle_apply (D : WeilDivisor X) (x : X) :
    weilDivisorAlgebraicCycle D x = weilDivisorCoeff D.val x :=
  rfl

/-- On an integral scheme of delta-dimension `n` the cycle of a Weil divisor has
delta-dimension `n - 1`: its nonzero coefficients sit at points of coheight one, and such a
point has delta-dimension `n - 1`.

The dimension function `d` is the input of Stacks 02JW; see the module documentation. -/
theorem weilDivisorAlgebraicCycle_mem_cyclesOfDimension (C : ChowSituation.{u})
    (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) {d : DimensionFunction X}
    (hd : ∀ y, d y = relativeDimension C.dimensionFunction p y) (D : WeilDivisor X) :
    weilDivisorAlgebraicCycle D ∈ cyclesOfDimension C p (n - 1) := by
  intro Z hZ
  obtain ⟨W, hWZ, -⟩ := exists_primeDivisor_of_weilDivisorCoeff_ne_zero D.val hZ
  have hx : coheight Z.isIrreducible.genericPoint = 1 := hWZ ▸ W.coheight_genericPoint
  have heq : IrreducibleCloseds.closureSingleton Z.isIrreducible.genericPoint = Z :=
    IrreducibleCloseds.ext
      (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).def
  rw [← heq]
  exact deltaDimension_closure_singleton_of_coheight_one C p hn hd hx

/-- The specification of the cycle of a Weil divisor by its coefficients: the value at the
generic point of each prime divisor is the coefficient of the divisor there, and the value at
every other point is zero. -/
def IsWeilDivisorCycle (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p] (n : ℤ)
    (D : PrimeDivisor X → ℤ) (c : CycleGroup C p (n - 1)) : Prop :=
  (∀ Z : PrimeDivisor X, (c : AlgebraicCycle X ℤ) Z.genericPoint = D Z) ∧
  (∀ x : X, (∀ Z : PrimeDivisor X, Z.genericPoint ≠ x) → (c : AlgebraicCycle X ℤ) x = 0)

/-- The cycle of a Weil divisor on an integral scheme of delta-dimension `n`, as an element of
`Z_{n-1}(X)` together with its coefficient specification.

The dimension function `d` is the input of Stacks 02JW; see the module documentation. -/
def weilDivisorCycle (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X]
    {n : ℤ} (hn : schemeDeltaDimension C p = (n : EInt)) {d : DimensionFunction X}
    (hd : ∀ y, d y = relativeDimension C.dimensionFunction p y) (D : WeilDivisor X) :
    { c : CycleGroup C p (n - 1) // IsWeilDivisorCycle C p n D.val c } :=
  ⟨⟨weilDivisorAlgebraicCycle D,
      weilDivisorAlgebraicCycle_mem_cyclesOfDimension C p hn hd D⟩,
    fun Z => weilDivisorCoeff_genericPoint D.val Z,
    fun x hx => weilDivisorCoeff_eq_zero D.val x hx⟩

end Stacks.Chow

end
