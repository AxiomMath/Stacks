module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcPlumbing
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Quasi-separatedness and finite presentation are fpqc local on the base

A morphism of schemes is quasi-separated, or of finite presentation, precisely when its base
changes along the members of an fpqc covering of the target are.

## Main results

* `AlgebraicGeometry.quasiSeparated_isLocalAtTarget_fpqc`: quasi-separatedness is fpqc local on
  the base.
* `AlgebraicGeometry.finitePresentation_isLocalAtTarget`: finite presentation is fpqc local on
  the base.

## Implementation notes

A morphism is quasi-separated exactly when its diagonal is quasi-compact
(`AlgebraicGeometry.quasiSeparated_eq_diagonal_is_quasiCompact`), and the diagonal of a property
descending along a class of morphisms stable under base change descends along the same class, so
fpqc descent of quasi-separatedness is fpqc descent of quasi-compactness. The remaining two
hypotheses of the criterion `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` are available for
quasi-separatedness itself.

Finite presentation is then immediate: it is the conjunction of being locally of finite
presentation, quasi-compact and quasi-separated, each of which is fpqc local on the base.

## References

* [Stacks Project, Tag 02KR](https://stacks.math.columbia.edu/tag/02KR)
* [Stacks Project, Tag 02L0](https://stacks.math.columbia.edu/tag/02L0)
-/

@[expose] public section

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

universe u

/-- Quasi-separatedness is Zariski local on the target. -/
@[sga "4 IV 8.5.5" "Zariski target coverings"]
private lemma quasiSeparated_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@QuasiSeparated : MorphismProperty Scheme.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _
    instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat

/-- Quasi-separatedness of morphisms of schemes descends along surjective flat quasi-compact
morphisms. -/
@[ega "IV 1.2.5" "special case"]
instance quasiSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@QuasiSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := Stacks.Descent.isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact.{u}
  have : MorphismProperty.RespectsIso (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [quasiSeparated_eq_diagonal_is_quasiCompact]
  exact MorphismProperty.instDescendsAlongDiagonalOfRespectsIsoOfIsStableUnderBaseChange
    (@QuasiCompact : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact)

/-- **Stacks Project, Tag 02KR.** Quasi-separatedness of morphisms of schemes is fpqc local on
the base. -/
@[stacks 02KR, ega "IV 2.7.1" "more general", sga "4 IV 8.5.5"]
instance quasiSeparated_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@QuasiSeparated : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := quasiSeparated_isZariskiLocalAtTarget.{u}
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@QuasiSeparated : MorphismProperty Scheme.{u})
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

/-- **Stacks Project, Tag 02L0.** Being of finite presentation is fpqc local on the base. -/
@[stacks 02L0, sga "4 IV 8.5.5"]
instance finitePresentation_isLocalAtTarget :
    MorphismProperty.IsLocalAtTarget
      (@FinitePresentation : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage :=
  have : MorphismProperty.IsLocalAtTarget
      (@QuasiCompact ⊓ @QuasiSeparated : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := .inf _ _
  MorphismProperty.IsLocalAtTarget.inf
    (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) _

end AlgebraicGeometry

end
