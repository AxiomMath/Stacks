module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierFamilyLevelIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierRepresentationLevelIsogeny

/-!
# The level isogeny of Laumon's argument over the integers of `E`

The level isogeny `Stacks.EtaleCohomology.LaumonFourierLevelIsogenyCoreInput` of Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) holds: it is assembled
(`Stacks.EtaleCohomology.laumonFourierLevelIsogenyCoreInput_of_levelIsogenies`) from its
representation side (`Stacks.EtaleCohomology.laumonFourierRepresentationLevelIsogenyInput`) and its
Fourier side (`Stacks.EtaleCohomology.laumonFourierFamilyLevelIsogenyInput`).

## Main results

* `Stacks.EtaleCohomology.laumonFourierLevelIsogenyCoreInput`.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.EtaleCohomology

/-- **The level isogeny over the integers of `E` holds.** -/
theorem laumonFourierLevelIsogenyCoreInput : LaumonFourierLevelIsogenyCoreInput.{u} :=
  laumonFourierLevelIsogenyCoreInput_of_levelIsogenies laumonFourierRepresentationLevelIsogenyInput
    laumonFourierFamilyLevelIsogenyInput

end Stacks.EtaleCohomology

end
