module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness and local finite presentation are fpqc local on the base

Two further morphism properties are shown to be local on the target for the fpqc precoverage,
by feeding the criterion `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` with the missing
descent input in each case.

## Main results

* `RingHom.Flat.codescendsAlong_faithfullyFlat`: flatness of a ring homomorphism codescends
  along faithfully flat ring homomorphisms.
* `AlgebraicGeometry.flat_descendsAlong_surjective_inf_flat_inf_quasiCompact`: flat morphisms
  satisfy fpqc descent.
* `Stacks.Descent.flat_isLocalAtTarget_fpqc`: flatness is fpqc local on the base.
* `Stacks.Descent.locallyOfFinitePresentation_isLocalAtTarget_fpqc`: being locally of finite
  presentation is fpqc local on the base.

## Implementation notes

Mathlib packages faithfully flat descent of finiteness, finite type, finite presentation,
smoothness and étaleness of ring homomorphisms as `RingHom.CodescendsAlong … FaithfullyFlat`,
but not flatness itself; `Module.Flat.of_flat_tensorProduct` is the mathematical content and is
packaged here. The scheme-level descent then comes from
`AlgebraicGeometry.HasRingHomProperty.descendsAlong_flat`, exactly as in
`Mathlib/AlgebraicGeometry/Morphisms/LocalFlatDescent.lean` for the properties Mathlib does
cover.

For local finite presentation every input is already available, Mathlib's own descent instance
included; only the application of the criterion was missing.

Both applications of the criterion supply `Stacks.Descent.IsStableUnderFlatBaseChange` by name
rather than leaving it to instance synthesis. Each property is stable under *arbitrary* base
change in Mathlib, hence a fortiori under the flat base change the criterion asks for, and
`Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange` is the step across;
its own docstring records why synthesis cannot take it for a property whose morphism arguments
are implicit, as `@Flat` and `@LocallyOfFinitePresentation` are.

## References

* [Stacks Project, Tag 02KY](https://stacks.math.columbia.edu/tag/02KY)
* [Stacks Project, Tag 02L2](https://stacks.math.columbia.edu/tag/02L2)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry TensorProduct

universe u

/-- Flatness of a ring homomorphism codescends along faithfully flat ring homomorphisms: if
`R → S` is faithfully flat and `S → S ⊗[R] T` is flat, then `R → T` is flat. -/
@[sga "3 XIX 2.1" "special case"]
lemma RingHom.Flat.codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.Flat RingHom.FaithfullyFlat := by
  refine RingHom.CodescendsAlong.mk _ RingHom.Flat.respectsIso ?_
  intro R S T _ _ _ _ _ hff hflat
  have : Module.FaithfullyFlat R S := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  have : Module.Flat S (S ⊗[R] T) := RingHom.flat_algebraMap_iff.mp hflat
  exact RingHom.flat_algebraMap_iff.mpr (Module.Flat.of_flat_tensorProduct R T S)

namespace AlgebraicGeometry

/-- Flat morphisms of schemes satisfy fpqc descent: if the base change of `g` along a
surjective flat quasi-compact morphism is flat, then so is `g`. -/
instance flat_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@Flat : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat (Q := RingHom.Flat)
    RingHom.Flat.codescendsAlong_faithfullyFlat

end AlgebraicGeometry

namespace Stacks.Descent

/-- Flatness is Zariski local on the target. -/
@[sga "4 IV 8.5.5" "special case"]
lemma flat_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Flat)

/-- Being locally of finite presentation is Zariski local on the target. -/
@[sga "4 IV 8.5.5" "special case"]
lemma locallyOfFinitePresentation_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FinitePresentation)

/-- **Stacks Project, Tag 02L2.** Flatness of a morphism of schemes is fpqc local on the
base. -/
@[stacks 02L2, sga "4 IV 8.5.5" "partial"]
instance flat_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@Flat : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := flat_isZariskiLocalAtTarget.{u}
  have := isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@Flat : MorphismProperty Scheme.{u})
  isLocalAtTarget_fpqcPrecoverage _

/-- **Stacks Project, Tag 02KY.** Being locally of finite presentation is fpqc local on the
base. -/
@[stacks 02KY, ega "IV 2.7.1" "(iv)", sga "4 IV 8.5.5" "fpqc target locality"]
instance locallyOfFinitePresentation_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage :=
  have := locallyOfFinitePresentation_isZariskiLocalAtTarget.{u}
  have := isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
  isLocalAtTarget_fpqcPrecoverage _

end Stacks.Descent

end
