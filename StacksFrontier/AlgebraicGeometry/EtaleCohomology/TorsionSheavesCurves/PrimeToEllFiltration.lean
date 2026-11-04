module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.PrimeToEllFiltration
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.LocallyConstantReduction

/-!
# Tag 0A3R as consumed by the dévissage of Theorem 03SC

The dévissage of Theorem 03SC (Lemma 03SD) consumes Tag 0A3R through the statement
`Stacks.EtaleCohomology.PrimeToEllFiltrationStatement`. This file proves that statement for every
prime `ℓ`, from the unconditional form of Tag 0A3R,
`Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_relSeries_constantRankOneStep`.

## Main results

* `Stacks.EtaleCohomology.primeToEllFiltrationStatement`: the statement of Tag 0A3R consumed by
  Lemma 03SD holds for every prime `ℓ`.
-/

@[expose] public section

universe u

namespace Stacks.EtaleCohomology

/-- **Tag 0A3R in the form consumed by Lemma 03SD.** For every prime `ℓ`, every finite type
locally constant sheaf of `F_ℓ`-vector spaces on the small étale site of a connected scheme
becomes, after a finite étale cover of degree prime to `ℓ`, a successive extension of copies of
`Z/ℓZ`. -/
theorem primeToEllFiltrationStatement {ℓ : ℕ} (hℓ : ℓ.Prime) :
    PrimeToEllFiltrationStatement.{u} ℓ :=
  fun _ _ F hF ↦ exists_primeToEll_finiteEtale_relSeries_constantRankOneStep hℓ F hF

end Stacks.EtaleCohomology

end
