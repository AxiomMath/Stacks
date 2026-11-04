module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcPlumbing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separatedness, universal closedness and properness are fpqc local on the base

A morphism of schemes is universally closed, separated, or proper precisely when its base
change along every member of an fpqc covering of its target is. In Mathlib this is
`CategoryTheory.MorphismProperty.IsLocalAtTarget P AlgebraicGeometry.Scheme.fpqcPrecoverage`
for the property `P` in question.

## Main results

* `AlgebraicGeometry.universallyClosed_isLocalAtTarget_fpqc`: universal closedness is fpqc
  local on the base.
* `AlgebraicGeometry.isSeparated_isLocalAtTarget_fpqc`: separatedness is fpqc local on the base.
* `AlgebraicGeometry.isProper_isLocalAtTarget_fpqc`: properness is fpqc local on the base.

## Implementation notes

All three follow from the criterion `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` (the fpqc
case of Tag 02KP): a property which is Zariski local on the target, stable under base change and
which descends along surjective flat quasi-compact morphisms is fpqc local on the target. Zariski
locality and base-change stability are Mathlib instances in each case, so only the descent input
has to be produced.

For universal closedness that input is Mathlib's
`AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`. For
separatedness it is obtained from the descent of closed immersions along such morphisms (Tag
02L6, proved in `StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget`) together with
`CategoryTheory.MorphismProperty.diagonal`: separatedness *is* the diagonal of being a closed
immersion, and the diagonal of a property that descends descends. Properness is then the
infimum of separatedness, universal closedness and being locally of finite type, the last of
which descends by a Mathlib instance.

The three `DescendsAlong` facts are stated as named lemmas rather than instances: the diagonal
instance of Mathlib takes its morphism properties as explicit arguments, so instance search does
not find it on its own, and `isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact` has to
be applied by hand anyway.

The base-change stability of `Surjective ⊓ Flat ⊓ QuasiCompact`, which is a lemma rather than an
instance, is imported from `StacksFrontier.AlgebraicGeometry.Descent.FpqcPlumbing`.

## References

* [Stacks Project, Tag 02KP](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Tag 02KS](https://stacks.math.columbia.edu/tag/02KS)
* [Stacks Project, Tag 02KU](https://stacks.math.columbia.edu/tag/02KU)
* [Stacks Project, Tag 02L1](https://stacks.math.columbia.edu/tag/02L1)
-/

@[expose] public section

open CategoryTheory MorphismProperty

universe u

namespace AlgebraicGeometry

/-- Separated morphisms satisfy fpqc descent: if the base change of `g` along a surjective flat
quasi-compact morphism is separated, then so is `g`. -/
@[ega "IV 2.7.1" "(i)", sga "1 VIII 4.8" "partial", sga "4 IV 8.5.5" "partial"]
theorem isSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := Stacks.Descent.isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact.{u}
  rw [IsSeparated.isSeparated_eq_diagonal_isClosedImmersion]
  exact instDescendsAlongDiagonalOfRespectsIsoOfIsStableUnderBaseChange
    @IsClosedImmersion (@Surjective ⊓ @Flat ⊓ @QuasiCompact)

/-- Proper morphisms satisfy fpqc descent: if the base change of `g` along a surjective flat
quasi-compact morphism is proper, then so is `g`. -/
@[ega "IV 2.7.1" "(vii)", sga "1 VIII 4.8" "partial", sga "4 IV 8.5.5" "Target"]
theorem isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@IsProper : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := isSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  have : MorphismProperty.DescendsAlong
      (@IsSeparated ⊓ @UniversallyClosed : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := DescendsAlong.inf
  have h : MorphismProperty.DescendsAlong
      ((@IsSeparated ⊓ @UniversallyClosed : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := DescendsAlong.inf
  rw [isProper_eq]
  exact h

/-- **Stacks Project, Tag 02KS.** Universal closedness of morphisms of schemes is fpqc local on
the target. -/
@[stacks 02KS, ega "IV 2.6.4" "more general"]
instance universallyClosed_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@UniversallyClosed : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@UniversallyClosed : MorphismProperty Scheme.{u})
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

/-- **Stacks Project, Tag 02KU.** Separatedness of morphisms of schemes is fpqc local on the
target. -/
@[stacks 02KU, ega "IV 2.7.1" "more general", sga "1 VIII 4.8" "more general", sga "4 IV 8.5.5"]
instance isSeparated_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@IsSeparated : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := isSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@IsSeparated : MorphismProperty Scheme.{u})
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

/-- **Stacks Project, Tag 02L1.** Properness of morphisms of schemes is fpqc local on the
target. -/
@[stacks 02L1, ega "IV 2.7.1" "more general", sga "1 VIII 4.8" "more general", sga "4 IV 8.5.5"]
instance isProper_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@IsProper : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@IsProper : MorphismProperty Scheme.{u})
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

end AlgebraicGeometry

end
