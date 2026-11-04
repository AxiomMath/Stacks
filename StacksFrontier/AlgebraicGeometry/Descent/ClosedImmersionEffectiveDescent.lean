module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent of closed immersions along a surjective étale chart

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS P` is the one geometric
hypothesis of Stacks 03I2 at a property `P` of morphisms of schemes. At the closed immersions it
need not be assumed: **this file proves it outright**, by the same two-step argument that
`StacksFrontier.AlgebraicGeometry.Descent.FiniteDescentFromAffine` runs for the integral and the
finite morphisms.

A closed immersion is an affine morphism, so
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom` — effective descent
at `AlgebraicGeometry.IsAffineHom`, with no hypothesis left — already produces the descended
morphism of schemes. That it is again a closed immersion is fppf descent of closed immersions,
Stacks 02L6, which is
`Stacks.Descent.isClosedImmersion_descendsAlong_surjective_inf_flat_inf_quasiCompact` upgraded
from the fpqc to the fppf form. Both halves are exactly what
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_le` consumes.

The affine case is strictly weaker than the quasi-affine case of Stacks 0247: it is Stacks 0245,
whose proof over an affine chart is effective descent for algebras along a faithfully flat ring
map and needs neither a relative spectrum nor the glueing of quasi-compact opens. Everything in
this development which asks for effective descent at the closed immersions — the existence clause
of Stacks 03IQ, and the surjectivity and bijectivity clauses of Stacks 0ENF — therefore depends on
Stacks 0245 and not on Stacks 0247.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_le_isAffineHom`: a closed immersion of schemes is an
  affine morphism.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`: **closed
  immersions of schemes descend effectively along the surjective étale morphisms of the big fppf
  site of `S`**, outright. This discharges the hypothesis of every statement in this development
  which assumes `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` at
  `AlgebraicGeometry.IsClosedImmersion`.

## Implementation notes

*Why the fppf form of Stacks 02L6 is reassembled here.* The fpqc descent of closed immersions is
an instance, `Stacks.Descent.isClosedImmersion_descendsAlong_surjective_inf_flat_inf_quasiCompact`
of `StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget`, and so is Mathlib's Zariski locality
`AlgebraicGeometry.IsClosedImmersion.isZariskiLocalAtTarget`; Mathlib's upgrade of fpqc to fppf
descent is also an instance but does not fire on a concrete property, so it is applied through the
named `AlgebraicGeometry.descendsAlong_fppf_of`. The same combination is available as
`Stacks.Descent.isClosedImmersion_descendsAlong_fppf` in
`StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae`, but that module is not in the import closure
of the affine effective-descent theorem and nothing else here needs it.

*Why not the quasi-affine route.* The declaration
`isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion_of_isQuasiAffineHom` of
`StacksFrontier.AlgebraicGeometry.Descent.StableOpenQuasiFiniteDescent` reaches the same
conclusion from the quasi-affine case, which
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom` proves. The
affine case is taken instead because it is a strictly weaker input: the quasi-affine case needs
a relative spectrum and the glueing of quasi-compact opens, steps 2 to 5 of Stacks 02W8, and
none of that is used for a closed immersion.

*No tag is carried.* Stacks 0245 and Stacks 0247 quantify over arbitrary fpqc coverings of an
arbitrary scheme, whereas
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` quantifies over the surjective
étale morphisms of one big fppf site; it is a predicate of this development and not a Stacks
lemma, so neither tag may sit on a statement about it. Stacks 02L6 already sits on
`Stacks.Descent.isClosedImmersion_descendsAlong_surjective_inf_flat_inf_quasiCompact`, which is
used and not restated. This is the position already taken by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom` and by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isFinite_of_isAffineHom`.

## References

* [Stacks Project, Tag 02L6](https://stacks.math.columbia.edu/tag/02L6)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MorphismProperty

universe u

namespace AlgebraicGeometry

namespace Space

/-- A closed immersion of schemes is affine. -/
@[ega "II 1.6.2"]
theorem isClosedImmersion_le_isAffineHom :
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) ≤
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) := by
  intro _ _ _ hf
  have := hf
  exact inferInstance

/-- **Closed immersions of schemes descend effectively along the surjective étale morphisms of
the big fppf site of `S`**, outright. Whenever a morphism `f : X ⟶ Y` of sheaves becomes
representable by a closed immersion after base change along a surjective étale morphism
`q : c ⟶ a` of the site, its base change along `h : yoneda.obj a ⟶ Y` is already representable by
a closed immersion.

A closed immersion is affine, so
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom` already produces the
descended morphism; that it is a closed immersion is then fppf descent of closed immersions,
Stacks 02L6.

This discharges the hypothesis `hdesc` of every statement which takes
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` at
`AlgebraicGeometry.IsClosedImmersion`. See the implementation notes of this file for why no
Stacks tag is carried. -/
@[sga "3 VIII 6.4" "partial"]
theorem isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
  have _hri : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _hd : MorphismProperty.DescendsAlong
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    descendsAlong_fppf_of _
  isEffectiveDescentAlongSurjectiveEtale_of_le
    (isEffectiveDescentAlongSurjectiveEtale_isAffineHom B S hS) isClosedImmersion_le_isAffineHom.{u}

end Space

end AlgebraicGeometry

end
