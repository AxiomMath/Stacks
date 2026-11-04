module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.RingTheory.QuasiFinite.Descent

/-!
# Quasi-finiteness is fpqc local on the base

A morphism of schemes is *locally quasi-finite* in the sense of the Stacks Project when it is
locally of finite type and has isolated points in its fibres; it is *quasi-finite* when it is
moreover quasi-compact. This file shows that both properties are local on the base for the fpqc
topology.

## Main results

* `Stacks.Descent.locallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact`:
  `AlgebraicGeometry.LocallyQuasiFinite` satisfies fpqc descent.
* `Stacks.Descent.locallyQuasiFinite_isLocalAtTarget_fpqc`:
  `AlgebraicGeometry.LocallyQuasiFinite` is fpqc local on the base.
* `Stacks.Descent.locallyOfFiniteType_inf_locallyQuasiFinite_isLocalAtTarget_fpqc`: being locally
  quasi-finite in the sense of the Stacks Project is fpqc local on the base.
* `Stacks.Descent.finiteType_inf_locallyQuasiFinite_isLocalAtTarget_fpqc`: being quasi-finite is
  fpqc local on the base.

## Implementation notes

Mathlib's `AlgebraicGeometry.LocallyQuasiFinite` is the affine-local property attached to
`RingHom.QuasiFinite`, which — unlike the Stacks Project's Tag 00PL — does not include a
finite-type hypothesis. The Stacks notions are therefore the infima
`@LocallyOfFiniteType ⊓ @LocallyQuasiFinite` and
`(@LocallyOfFiniteType ⊓ @QuasiCompact) ⊓ @LocallyQuasiFinite`, and the Stacks proof's appeal to
Tags 02KX and 02KQ is exactly `CategoryTheory.MorphismProperty.IsLocalAtTarget.inf` applied to
those, the finite-type and quasi-compact factors being supplied by
`StacksFrontier/AlgebraicGeometry/Descent/FpqcLocalAtTarget.lean`.

The remaining factor, `@LocallyQuasiFinite` itself, is handled by the fpqc criterion
`Stacks.Descent.isLocalAtTarget_fpqcPrecoverage`: it is Zariski local on the target and stable
under base change by Mathlib -- hence, a fortiori, under the flat base change the criterion asks
for, by `Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange` -- and it descends
along surjective flat quasi-compact morphisms because `RingHom.QuasiFinite` codescends along
faithfully flat ring maps (`RingHom.QuasiFinite.codescendsAlong_faithfullyFlat`).

Following `FpqcLocalAtTarget.lean`, the Zariski locality of `@LocallyQuasiFinite` is packaged as a
`private` lemma rather than left to instance synthesis, which cannot solve for the
ring-homomorphism parameter of `AlgebraicGeometry.HasRingHomProperty` without reducibility
settings that this development does not use.

## References

* [Stacks Project, Tag 02VI](https://stacks.math.columbia.edu/tag/02VI)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-- Being locally quasi-finite is Zariski local on the target. -/
private lemma locallyQuasiFinite_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.QuasiFinite)

/-- Locally quasi-finite morphisms satisfy fpqc descent: if the base change of `g` along a
surjective flat quasi-compact morphism is locally quasi-finite, then so is `g`. -/
instance locallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@LocallyQuasiFinite : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.QuasiFinite.codescendsAlong_faithfullyFlat

/-- Mathlib's `AlgebraicGeometry.LocallyQuasiFinite` is fpqc local on the base. -/
instance locallyQuasiFinite_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@LocallyQuasiFinite : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := locallyQuasiFinite_isZariskiLocalAtTarget.{u}
  have := isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@LocallyQuasiFinite : MorphismProperty Scheme.{u})
  isLocalAtTarget_fpqcPrecoverage _

/-- **Stacks Project, Tag 02VI.** Local quasi-finiteness of a scheme morphism is fpqc local on the
base. -/
@[stacks 02VI "locally quasi-finite case", sga "1 VIII 3.5" "special case"]
instance locallyOfFiniteType_inf_locallyQuasiFinite_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      ((@LocallyOfFiniteType : MorphismProperty Scheme.{u}) ⊓ @LocallyQuasiFinite)
      Scheme.fpqcPrecoverage :=
  .inf _ _

/-- **Stacks Project, Tag 02VI.** Quasi-finiteness of a scheme morphism is fpqc local on the
base. -/
@[stacks 02VI "quasi-finite case",
  sga "1 VIII 3.5" "more general",
  sga "3 VIB 2.1.2" "partial",
  sga "4 IV 8.5.5"]
instance finiteType_inf_locallyQuasiFinite_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (((@LocallyOfFiniteType : MorphismProperty Scheme.{u}) ⊓ @QuasiCompact) ⊓
        @LocallyQuasiFinite) Scheme.fpqcPrecoverage :=
  .inf _ _

end Stacks.Descent

end
