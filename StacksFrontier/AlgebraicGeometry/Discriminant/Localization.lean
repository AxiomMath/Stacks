module

public import StacksFrontier.AlgebraicGeometry.Discriminant.BaseLocalization
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleLocalization
public import StacksFrontier.AlgebraicGeometry.Discriminant.FactorizationRefinement
public import StacksFrontier.AlgebraicGeometry.Discriminant.SimultaneousLocalization
public import StacksFrontier.AlgebraicGeometry.Discriminant.TargetLocalization

/-!
# Localization of relative dualizing modules

The relative dualizing module of a quasi-finite map of Noetherian rings is unchanged when the
base is replaced by a localization through which the map factors, and it commutes with
localization in the target. This module gathers the three parts of Tag 0BT2, each of which is
proved in a file of its own.

## Main results

* `Stacks.Discriminant.dualizingModule_equiv_of_isLocalization_away` identifies the dualizing
  modules before and after replacing the base by a localization through which the map factors.
  With its pure-tensor formula and its naturality in the finite-open factorization, it is part
  (1) of Tag 0BT2 and lives in
  `StacksFrontier/AlgebraicGeometry/Discriminant/BaseLocalization.lean`.
* `Stacks.Discriminant.localizedModule_dualizingModule_equiv` identifies a localization of a
  dualizing module with the dualizing module of the localized target. With its pure-tensor
  formula and its two naturality statements, it is part (2) and lives in
  `StacksFrontier/AlgebraicGeometry/Discriminant/TargetLocalization.lean`.
* `Stacks.Discriminant.localizedModule_dualizingModule_equiv_of_baseLocalization` identifies a
  localization of a dualizing module with the dualizing module of the simultaneously localized
  base and target, and
  `Stacks.Discriminant.localizedModule_dualizingModule_equiv_of_baseLocalization_eq_comp`
  exhibits it as the composite of the two preceding identifications. Together they are part (3)
  and live in `StacksFrontier/AlgebraicGeometry/Discriminant/SimultaneousLocalization.lean`.

## Implementation notes

The source writes its canonical identifications as equalities. Here they are expressed as linear
equivalences. Localized rings and modules are kept abstract through `IsLocalization.Away` and
`IsLocalizedModule`, so the results apply to any chosen models of the localizations. The tensor
formulas use the finite-open models and the comparison of Tag 0BT1 makes them independent of
those choices.

Base replacement is built from Tag 0BT3: the dualizing module of the base change along
`A → A_f` is the scalar extension, and `A_f ⊗_A B` is `B` because `f` is already invertible in
`B`. `Stacks.Discriminant.retargetFactorization` and
`Stacks.Discriminant.dualizingModule_retargetEquiv` transport a finite-open factorization and
its dualizing module along that identification of targets, after which the comparison of Tag
0BT1 matches the result with an arbitrary factorization over `A_f`. They are in
`StacksFrontier/AlgebraicGeometry/Discriminant/FactorizationRefinement.lean` and
`StacksFrontier/AlgebraicGeometry/Discriminant/DualizingModuleLocalization.lean`.

Localization in the target is built from `Stacks.Discriminant.locFact`, which keeps the
intermediate algebra and replaces the target by its localization. That this is again a
finite-open factorization is the only geometric input: on a basic open of the intermediate
algebra contained in the image, the localization of the target at `g` is already a localization
of the away localization, which is
`Stacks.Discriminant.unit_image_of_range_localization` together with
`Stacks.Discriminant.awayMap_bijective_if_unit`.

## References

* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
-/
