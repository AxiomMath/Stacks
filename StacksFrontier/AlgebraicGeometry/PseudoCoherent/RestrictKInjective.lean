module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.RestrictionOfKInjectives

/-!
# Restriction to an open subspace preserves K-injectivity, in the `restrictModules` idiom

`ExtensionByZeroModules.isKInjective_jStar` (Stacks 08BS) says that restriction of modules to an
open subspace of a ringed space carries K-injective complexes to K-injective complexes, stated
for `ExtensionByZeroModules.jStar`. The pseudo-coherence development phrases restriction instead
as `AlgebraicGeometry.RingedSpace.restrictModules`, the pushforward to the ringed space
`X.restrict U.isOpenEmbedding`. The two functors are **the same functor**:
`AlgebraicGeometry.RingedSpace.restrictModules_eq_jStar` says so by `rfl`, both being
`CategoryTheory.SheafOfModules.pushforward` of the identity of the restricted sheaf of rings
along the image functor of the open embedding. This file records that identification and the
resulting statement about `AlgebraicGeometry.RingedSpace.restrictComplex`.

That statement is what identifies a derived direct image after restriction to an open subspace:
the comparison `(Rf_*E)|_V ≅ Rg_*(E|_U)` of Stacks 08FE is computed on a K-injective
representative `I` of `E`, where it is the underived base-change square
`AlgebraicGeometry.RingedSpace.restrictPushforwardIso`, and the right-hand side is a derived
direct image only because `I|_U` is again K-injective.

## Main results

* `AlgebraicGeometry.RingedSpace.restrictModules_eq_jStar`: the two spellings of restriction
  agree, definitionally.
* `AlgebraicGeometry.RingedSpace.isKInjective_restrictComplex`: the degreewise restriction to an
  open subspace of a K-injective complex of `𝒪_X`-modules is K-injective.

## Implementation notes

No tag is placed here. The content of Stacks 08BS is stated by
`ExtensionByZeroModules.isKInjective_jStar`, which carries the attribute; the results below are
that one statement in the spelling its consumers use, and a second placement of the tag would
claim the lemma twice.

`ExtensionByZeroModules.isKInjective_jStar` is an `instance`, but
`AlgebraicGeometry.RingedSpace.restrictComplex` is a `def` and instance search does not unfold it
to the `mapHomologicalComplex` shape, so the result below is a `theorem` that consumers apply by
name.

## References

* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

universe u

/-- **The two spellings of restriction of modules to an open subspace agree.** Both
`AlgebraicGeometry.RingedSpace.restrictModules` and `ExtensionByZeroModules.jStar` are
`CategoryTheory.SheafOfModules.pushforward` of the identity of the restricted sheaf of rings
along the image functor of the open embedding, so the identification is definitional. -/
public theorem restrictModules_eq_jStar (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    restrictModules X U =
      ExtensionByZeroModules.jStar U (StrictlyPerfect.structureSheafOfRings X) :=
  rfl

/-- **Stacks 08BS in the `restrictModules` idiom.** The degreewise restriction to an open
subspace `U` of `X` of a K-injective complex of `𝒪_X`-modules is K-injective.

This is `ExtensionByZeroModules.isKInjective_jStar` read through
`AlgebraicGeometry.RingedSpace.restrictModules_eq_jStar`. -/
public theorem isKInjective_restrictComplex {X : RingedSpace.{u, u}}
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ) [E.IsKInjective]
    (U : Opens X.carrier) :
    CochainComplex.IsKInjective (restrictComplex E U) :=
  ExtensionByZeroModules.isKInjective_jStar U (StrictlyPerfect.structureSheafOfRings X) E

end AlgebraicGeometry.RingedSpace

end
