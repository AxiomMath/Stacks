module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent

/-!
# Integral morphisms satisfy fpqc descent

A morphism of schemes is *integral* when the preimage of every affine open of the target is
affine and the induced ring map is integral. This file shows that integrality satisfies fpqc
descent and is fpqc local on the base — Stacks Tag 02L9 — and deduces effective descent for
integral morphisms along a surjective étale morphism of the big fppf site of a scheme, which is
what the normalization of an algebraic space needs.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Descent.isIntegralHom_descendsAlong_surjective_inf_flat_inf_quasiCompact`:
  `AlgebraicGeometry.IsIntegralHom` satisfies fpqc descent. Its fppf weakening, which is the form
  consumed by the effective-descent machinery of
  `StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent`, is
  `AlgebraicGeometry.isIntegralHom_descendsAlong_fppf` in
  `StacksFrontier.AlgebraicGeometry.Descent.FiniteDescentFromAffine`.
* `Stacks.Descent.isIntegralHom_isLocalAtTarget_fpqc`: integrality of a morphism of schemes is
  fpqc local on the base. This is Stacks Tag 02L9.
* `Stacks.Descent.isIntegralHom_respectsIso`: integrality of a morphism of schemes respects
  isomorphisms, in the named form that instance synthesis does not find.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isIntegralHom`: effective
  descent for integral morphisms along a surjective étale morphism of the big fppf site of `S`.

## Implementation notes

The descent step does not go through the ring-level statement
`RingHom.IsIntegral.codescendsAlong_faithfullyFlat`
(`StacksFrontier.RingTheory.IntegralClosure.FaithfullyFlatDescent`), and this is deliberate. The
route through `AlgebraicGeometry.HasAffineProperty.descendsAlong_of_affineAnd`, which is the one
that consumes that ring-level statement, asks for the instance
`CategoryTheory.MorphismProperty.DescendsAlong AlgebraicGeometry.IsAffineHom
(AlgebraicGeometry.Surjective ⊓ AlgebraicGeometry.Flat)` — affine descent along a surjective flat
morphism that is *not* assumed quasi-compact — which this library does not have: Stacks Tag 02L5,
carried here by
`Stacks.Descent.isAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact`, is the
quasi-compact statement.

Instead, Mathlib's `AlgebraicGeometry.IsIntegralHom.eq_universallyClosed_inf_isAffineHom`
decomposes integrality as universal closedness together with affineness, and both factors
already descend along surjective flat quasi-compact morphisms — the first in Mathlib, the second
by Tag 02L5 — so `CategoryTheory.MorphismProperty.DescendsAlong.inf` finishes. The ring-level
statement is therefore not needed for integrality of morphisms of schemes, although it remains
the ring-level content of this tag.

As in `StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasiFinite`, the Zariski locality of
integrality at the target and its respecting of isomorphisms are named rather than left to
instance synthesis, which cannot solve for the affine-target parameter of
`AlgebraicGeometry.HasAffineProperty` without reducibility settings that this development does
not use. The locality is already carried by
`AlgebraicGeometry.Space.isZariskiLocalAtTarget_isIntegralHom` and is not restated here.

## References

* [Stacks Project, Tag 02L5](https://stacks.math.columbia.edu/tag/02L5)
* [Stacks Project, Tag 02L9](https://stacks.math.columbia.edu/tag/02L9)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
-/

@[expose] public section

open CategoryTheory MorphismProperty AlgebraicGeometry

universe u

namespace Stacks.Descent

/-- Integrality of a morphism of schemes respects isomorphisms. -/
theorem isIntegralHom_respectsIso :
    MorphismProperty.RespectsIso (@IsIntegralHom.{u} : MorphismProperty Scheme.{u}) :=
  @HasAffineProperty.instRespectsIsoScheme _ _ IsIntegralHom.hasAffineProperty

/-- **Stacks Project, Tag 02L9**, the descent step. Integral morphisms satisfy fpqc descent: if
the base change of `g` along a surjective flat quasi-compact morphism is integral, then so is
`g`.

Integrality is universal closedness together with affineness
(`AlgebraicGeometry.IsIntegralHom.eq_universallyClosed_inf_isAffineHom`), and both factors
descend along surjective flat quasi-compact morphisms, the second by Tag 02L5. -/
@[stacks 02L9 "the descent step", ega "IV 2.7.1" "(xvii)", sga "1 VIII 5.7" "detection (integral)"]
theorem isIntegralHom_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [IsIntegralHom.eq_universallyClosed_inf_isAffineHom]
  exact DescendsAlong.inf

/-- **Stacks Project, Tag 02L9.** Integrality of a morphism of schemes is fpqc local on the
base. -/
@[stacks 02L9, ega "IV 2.7.1" "(xvii)", sga "1 VIII 5.7" "more general", sga "4 IV 8.5.5"]
instance isIntegralHom_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := isIntegralHom_descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  have := AlgebraicGeometry.Space.isZariskiLocalAtTarget_isIntegralHom.{u}
  -- Supplied by name rather than left to synthesis: instance search cannot unfold
  -- `MorphismProperty` for a property whose morphism arguments are implicit. This is
  -- the idiom `isStableUnderFlatBaseChange_of_isStableUnderBaseChange` documents for
  -- itself, and that `FiniteLocallyFree/FpqcDescent.lean:97,108` already follows.
  have := isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@IsIntegralHom.{u} : MorphismProperty Scheme.{u})
  isLocalAtTarget_fpqcPrecoverage _

end Stacks.Descent

namespace AlgebraicGeometry.Space

/-- **Effective descent for integral morphisms along a surjective étale morphism of the site.**
This is Stacks 03I2 at the class of integral morphisms of schemes.

It follows from the affine case,
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom`, because an integral
morphism is affine and integrality satisfies fppf descent. -/
theorem isEffectiveDescentAlongSurjectiveEtale_isIntegralHom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u}) :=
  have _hri := Stacks.Descent.isIntegralHom_respectsIso.{u}
  have _hfppf : MorphismProperty.DescendsAlong
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    _root_.AlgebraicGeometry.isIntegralHom_descendsAlong_fppf.{u}
  isEffectiveDescentAlongSurjectiveEtale_of_le
    (isEffectiveDescentAlongSurjectiveEtale_isAffineHom B S hS)
    fun _ _ f hf =>
      have : _root_.AlgebraicGeometry.IsIntegralHom f := hf
      inferInstanceAs (_root_.AlgebraicGeometry.IsAffineHom f)

end AlgebraicGeometry.Space

end
