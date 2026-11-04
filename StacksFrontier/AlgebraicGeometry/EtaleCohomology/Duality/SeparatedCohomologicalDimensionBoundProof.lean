module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SeparatedFiniteType
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.SeparatedCohomologicalDimensionBound
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `SeparatedCohomologicalDimensionBound` over a separably closed field

`Stacks.EtaleCohomology.SeparatedCohomologicalDimensionBound k` is the bound `cd(X) ≤ 2 dim X`
on torsion abelian sheaves for `X` separated, quasi-compact and locally of finite type over `k`.
It is false over a general field (for `X = Spec ℚ` it would say `H^1(ℚ, ℤ/ℓ) = 0`); over a
separably closed field it is `AlgebraicGeometry.isEtaleCohomologyBound_two_mul_of_isSepClosed`
(SGA 4, Exposé X, Corollaire 4.3). Over an algebraically closed field it therefore discharges the
input `Stacks.EtaleCohomology.CohomologicalDimensionInput` of the fibration step of Poincaré
duality.

## Main results

* `Stacks.EtaleCohomology.separatedCohomologicalDimensionBound_of_isSepClosed`.
* `Stacks.EtaleCohomology.cohomologicalDimensionInput_of_isAlgClosed`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **`cd(X) ≤ 2 dim X` over a separably closed field**: the bound
`SeparatedCohomologicalDimensionBound k` holds for every separably closed field `k`. -/
@[sga "4 X 5.2" "special case"]
theorem separatedCohomologicalDimensionBound_of_isSepClosed (k : Type u) [Field k]
    [IsSepClosed k] : SeparatedCohomologicalDimensionBound k :=
  fun X p _ _ _ n hn => isEtaleCohomologyBound_two_mul_of_isSepClosed k n X p hn

/-- **The input `CohomologicalDimensionInput` over an algebraically closed field**: for `X`
separated, quasi-compact and locally of finite type over `k` with `dim X ≤ n`, `F` locally
constant of finite type and `G` any sheaf of `ℤ/ℓ`-modules on `X_ét`, `Ext^q_X(F, G) = 0` for
`q > 2n`. -/
theorem cohomologicalDimensionInput_of_isAlgClosed (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [IsAlgClosed k] : CohomologicalDimensionInput ℓ k :=
  cohomologicalDimensionInput_of_separatedCohomologicalDimensionBound ℓ
    (separatedCohomologicalDimensionBound_of_isSepClosed k)

end Stacks.EtaleCohomology

end
