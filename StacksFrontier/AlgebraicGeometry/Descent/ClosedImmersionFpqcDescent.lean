module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityLargeIndex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending closed immersions along an fpqc covering

Let `S` be a scheme and let `{X i ⟶ S}` be an fpqc covering. A descent datum relative to that
covering whose component morphisms are closed immersions is effective. A closed immersion is
affine, so this is the affine case of effective descent, Stacks 0245, applied to a smaller class
of morphisms.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.DescentData.isFamilyEffective_of_isClosedImmersion`: **a descent datum
  relative to an fpqc covering whose components are closed immersions is effective.**

## Implementation notes

*Stacks 0245 is used, not assumed.* Effectivity of a descent datum whose components are affine
along an arbitrary fpqc covering is
`AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom` of
`StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcFamilyEffective`, for a covering family indexed
in the universe of the schemes, and
`AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom_of_anyIndex` of
`StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityLargeIndex` with no restriction on the
index type at all. The latter is what is applied here, so the statement below carries no
effectivity hypothesis and no hypothesis on the index type of the covering: all it adds to
Stacks 0245 is the source's own observation that a closed immersion is affine, which instance
resolution supplies from `AlgebraicGeometry.IsClosedImmersion.isAffineHom`. The implication is
strict — the affine morphisms are a strictly larger class — so the conclusion is a genuine
special case and not a restatement of its input.

*Why no statement here is about the big fppf site.*
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion` of
`StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent` proves effective descent
of closed immersions outright, but for the surjective étale morphisms of one big fppf site and
for morphisms of sheaves; that predicate is a notion of this development rather than a Stacks
statement, which is why that file carries no tag. Stacks 03I0 is about descent data of schemes
relative to an arbitrary fpqc covering, so it is stated here instead.

## References

* [Stacks Project, Tag 01SE](https://stacks.math.columbia.edu/tag/01SE)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 03I0](https://stacks.math.columbia.edu/tag/03I0)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

namespace DescentData

/-- **A descent datum relative to an fpqc covering whose components are closed immersions is
effective.** Let `S` be a scheme, let `{X i ⟶ S}` be an fpqc covering and let `D` be a descent
datum relative to it whose structure morphism over each `X i` is a closed immersion. Then `D` is
isomorphic to the canonical descent datum of a scheme over `S`.

A closed immersion is affine, so this is effective descent for affine morphisms along an fpqc
covering, Stacks 0245, at a smaller class of morphisms. -/
@[stacks 03I0,
  sga "3 IV 4.7" "partial",
  sga "3 IV 6.4.1" "partial",
  sga "3 VIII 6.4" "Object effectivity"]
theorem isFamilyEffective_of_isClosedImmersion {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S) (D : DescentData f)
    (hD : ∀ i, IsClosedImmersion (D.obj i).hom) :
    D.IsFamilyEffective :=
  isFamilyEffective_of_isAffineHom_of_anyIndex f hf D fun i ↦ have := hD i; inferInstance

end DescentData

end AlgebraicGeometry

end
