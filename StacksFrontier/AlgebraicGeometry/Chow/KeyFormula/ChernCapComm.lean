module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinGysinKeyFormula
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapDischarge

/-!
# Stacks 02TH for the canonical divisor cycles of a situation

`Stacks.Chow.KeyFormulaSituation.firstChernClassCapOfInvertible_comm` of
`StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapDischarge` still carries `div_L(s)` as a
parameter together with its presentation `∑ ord_{B_i}(f_i) [Z_i]` by the family. The presentation
of `div_N(t)` is `Stacks.Chow.KeyFormulaSituation.weilDivisorAlgebraicCycle_weilDivisorN_apply`,
and the one of `div_L(s)` is the same statement about the other module: the situation of Stacks
0AYB is symmetric in its two modules, so `Stacks.Chow.KeyFormulaSituation.swap` of
`StacksFrontier.AlgebraicGeometry.Chow.GysinGysinKeyFormula` exchanges them and the `N`-side
presentation, read on the swapped situation, is the `L`-side one. Both parameters are then the
canonical divisor cycles of the two sections.

## Main results

* `Stacks.Chow.KeyFormulaSituation.firstChernClassCapOfInvertible_comm_weilDivisorCycleN` —
  **Stacks 02TH** for the two canonical divisor cycles, with no parameter besides the situation.
* `Stacks.Chow.firstChernClassCapOfInvertible_comm_chernComponentCycle` — **Stacks 02TH** for the
  divisor cycles of two arbitrary nonzero meromorphic sections, which is the form the component
  rules of Stacks 02SO take.

## References

* [Stacks Project, Tag 02TH](https://stacks.math.columbia.edu/tag/02TH)
* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

namespace KeyFormulaSituation

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {L N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (ℱ : KeyFormulaSituation L N)

variable (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p] {k : ℤ}

/-- **Stacks 02TH for the two canonical divisor cycles.** On an integral, locally Noetherian
scheme of delta-dimension `k + 2`,

`c₁(N) ∩ div_L(s) = c₁(L) ∩ div_N(t)`  in  `A_k(X)`,

where `div_L(s)` and `div_N(t)` are the divisor cycles of the two sections of the situation. No
parameter besides the situation remains: the two presentations by the family that
`Stacks.Chow.KeyFormulaSituation.firstChernClassCapOfInvertible_comm` asks for are
`Stacks.Chow.KeyFormulaSituation.weilDivisorAlgebraicCycle_weilDivisorN_apply`, read on `ℱ` for
`div_N(t)` and on `ℱ.swap` for `div_L(s)`. -/
@[stacks 02TH "the identity for two invertible modules with nonzero meromorphic sections on an \
integral, locally Noetherian scheme of delta-dimension `k + 2`, with no hypothesis: the key \
formula of Stacks 0AYC is discharged by \
`Stacks.Chow.KeyFormulaSituation.keyFormula_toKeyFormulaData` and the two divisor cycles of \
Stacks 02SJ are the canonical ones of the two sections"]
theorem firstChernClassCapOfInvertible_comm_weilDivisorCycleN
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) :
    firstChernClassCapOfInvertible C p k N (ℱ.swap.weilDivisorCycleN C p hn) =
      firstChernClassCapOfInvertible C p k L (ℱ.weilDivisorCycleN C p hn) := by
  refine ℱ.firstChernClassCapOfInvertible_comm C p hn (ℱ.swap.weilDivisorCycleN C p hn)
    (ℱ.weilDivisorCycleN C p hn) ?_ ?_
  · exact ℱ.swap.weilDivisorAlgebraicCycle_weilDivisorN_apply C p k hn
  · exact ℱ.weilDivisorAlgebraicCycle_weilDivisorN_apply C p k hn

end KeyFormulaSituation

/-! ### Stacks 02TH for the divisor cycles of two arbitrary sections -/

section ComponentCycle

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (C : ChowSituation.{u})
  (p : X ⟶ C.S) [LocallyOfFiniteType p] {k : ℤ} (L N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- **Stacks 02TH for the divisor cycle of an arbitrary nonzero meromorphic section.** On an
integral, locally Noetherian scheme of delta-dimension `k + 2`,

`c₁(L) ∩ div_N(t) = c₁(N) ∩ div_L(s)`  in  `A_k(X)`,

for any two nonzero meromorphic sections `s` of `L` and `t` of `N`. This is the shape the
component rules of Stacks 02SO take, their values being divisor cycles of chosen sections:
`Stacks.Chow.chernComponentCycle` is the divisor cycle graded as a `(k+1)`-cycle.

The situation of Stacks 0AYB built on the two sections by
`Stacks.Chow.keyFormulaSituationOf` has them as its own two sections, so its two canonical
divisor cycles are the two component cycles here and the identity is
`Stacks.Chow.KeyFormulaSituation.firstChernClassCapOfInvertible_comm_weilDivisorCycleN`. -/
theorem firstChernClassCapOfInvertible_comm_chernComponentCycle
    (hk : schemeDeltaDimension C p = ((k + 1 + 1 : ℤ) : EInt))
    (hLt : ∀ x : X, IsTrivializedNear L x) (hNt : ∀ x : X, IsTrivializedNear N x)
    {s : L.presheaf.stalk (genericPoint X)} (hs : s ≠ 0)
    {t : N.presheaf.stalk (genericPoint X)} (ht : t ≠ 0) :
    firstChernClassCapOfInvertible C p k L (chernComponentCycle C p hk hNt t) =
      firstChernClassCapOfInvertible C p k N (chernComponentCycle C p hk hLt s) := by
  have hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt) := by
    rw [hk, show (k + 1 + 1 : ℤ) = k + 2 from by ring]
  have hcycL : (keyFormulaSituationOf L N s t hs ht).swap.weilDivisorCycleN C p hn =
      chernComponentCycle C p hk hLt s := Subtype.ext rfl
  have hcycN : (keyFormulaSituationOf L N s t hs ht).weilDivisorCycleN C p hn =
      chernComponentCycle C p hk hNt t := Subtype.ext rfl
  rw [← hcycL, ← hcycN]
  exact ((keyFormulaSituationOf L N s t hs
    ht).firstChernClassCapOfInvertible_comm_weilDivisorCycleN C p hn).symm

end ComponentCycle

end Stacks.Chow

end
