module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# Unramified morphisms are fpqc local on the base

A morphism of schemes is formally unramified, unramified, or G-unramified precisely when its base
changes along the members of an fpqc covering of the target are.

## Main results

* `AlgebraicGeometry.formallyUnramified_isLocalAtTarget_fpqc`: being formally unramified is fpqc
  local on the base.
* `AlgebraicGeometry.unramified_isLocalAtTarget_fpqc`: being unramified is fpqc local on the base.
* `AlgebraicGeometry.gUnramified_isLocalAtTarget_fpqc`: being G-unramified is fpqc local on the
  base.

## Implementation notes

Formal unramifiedness is an affine-local description by a ring-map property which satisfies
faithfully flat codescent, so it is handed straight to the criterion
`Stacks.Descent.isLocalAtTarget_fpqcPrecoverage`; the Zariski locality and the flat base-change
hypotheses have to be supplied by name, as the docstrings of
`AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget` and
`Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange` explain.

Unramifiedness and G-unramifiedness are then decompositions into properties already known to be
fpqc local: an unramified morphism is one which is locally of finite type and formally
unramified, and a G-unramified morphism is one which is locally of finite presentation and
formally unramified
(`AlgebraicGeometry.unramified_iff_locallyOfFiniteType_and_formallyUnramified` and its companion).
The Stacks argument instead characterises the two by an open diagonal; the decomposition used
here needs no separate treatment of the diagonal.

## References

* [Stacks Project, Tag 02VM](https://stacks.math.columbia.edu/tag/02VM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- Being formally unramified is fpqc local on the target of a morphism of schemes. -/
instance formallyUnramified_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (@FormallyUnramified : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage :=
  have : IsZariskiLocalAtTarget (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @FormallyUnramified)
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@FormallyUnramified : MorphismProperty Scheme.{u})
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

/-- **Stacks Project, Tag 02VM.** Unramifiedness of morphisms of schemes is fpqc local on the
base. -/
@[stacks 02VM "unramified", ega "IV 17.7.3" "special case"]
instance unramified_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@Unramified : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := by
  rw [MorphismProperty.ext _ (@LocallyOfFiniteType ⊓ @FormallyUnramified)
    fun _ _ f ↦ unramified_iff_locallyOfFiniteType_and_formallyUnramified f]
  exact .inf _ _

/-- **Stacks Project, Tag 02VM.** G-unramifiedness of morphisms of schemes is fpqc local on the
base. -/
@[stacks 02VM "g_unramified",
  ega "IV 17.7.3" "special case",
  sga "3 VIB 2.1.2" "Remark 2.1.2",
  sga "4 IV 8.5.5" "partial"]
instance gUnramified_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@GUnramified : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := by
  rw [MorphismProperty.ext _ (@LocallyOfFinitePresentation ⊓ @FormallyUnramified)
    fun _ _ f ↦ gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified f]
  exact .inf _ _

end AlgebraicGeometry

end
