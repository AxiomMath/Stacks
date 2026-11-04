module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierLevelIsogenyOfCore
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierLineAbsIrrOfLatticeDichotomy

/-!
# The absolute irreducibility input of Laumon's argument for `ℓ ≠ p`

The input `Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput'` of Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (piece L6) holds, with no remaining inputs:

* the level isogeny over the integers of every finite extension of `E`
  (`Stacks.EtaleCohomology.laumonFourierLevelIsogenyInput`, from the core case over the integers of
  `E`);
* that gives the level dichotomy of the lattices of `τ ⊗ E''`
  (`Stacks.EtaleCohomology.laumonLatticeLevelDichotomyInput_of_levelIsogeny`);
* that gives the absolute irreducibility
  (`Stacks.EtaleCohomology.laumonFourierLineAbsIrrInput'_of_latticeLevelDichotomy`).

## Main results

* `Stacks.EtaleCohomology.laumonLatticeLevelDichotomyInput`.
* `Stacks.EtaleCohomology.laumonFourierLineAbsIrrInput'`.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.EtaleCohomology

/-- **The lattice level dichotomy of `τ ⊗ E''` holds.** -/
theorem laumonLatticeLevelDichotomyInput : LaumonLatticeLevelDichotomyInput.{u} :=
  laumonLatticeLevelDichotomyInput_of_levelIsogeny laumonFourierLevelIsogenyInput

/-- **Piece L6 of Laumon's argument for `ℓ ≠ p` holds**: the absolute irreducibility input
`Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput'`, with no remaining inputs. -/
theorem laumonFourierLineAbsIrrInput' : LaumonFourierLineAbsIrrInput'.{u} :=
  laumonFourierLineAbsIrrInput'_of_latticeLevelDichotomy laumonLatticeLevelDichotomyInput

end Stacks.EtaleCohomology

end
