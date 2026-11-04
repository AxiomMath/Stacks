module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFppfLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyMono
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects

/-!
# An open immersion is limit preserving on objects (Stacks 06CY)

Let `p : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S` which is representable by algebraic spaces and an open immersion in the sense of
Stacks 04XB. **Stacks 06CY** says that `p` is limit preserving on objects.

The source deduces this from Stacks 06CX, the characterisation of limit preservation on objects
for a 1-morphism representable by algebraic spaces: such a 1-morphism is limit preserving on
objects exactly when the morphism of algebraic spaces representing each of its base changes
along a scheme-valued point of the target is locally of finite presentation. An open immersion
of algebraic spaces is locally of finite presentation (Stacks 06CN), and a relative property of
Stacks 03YK may be weakened along any implication between properties of morphisms of algebraic
spaces (Stacks 045F), so the relative open-immersion property implies the relative property of
being locally of finite presentation, whence the conclusion.

Both steps are carried out:
`AlgebraicGeometry.Stack.hasRelativeProperty_locallyOfFinitePresentation_of_isOpenImmersion`
is the passage between the two relative properties, and
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation` is
Stacks 06CX.

*Index universes.* Limit preservation on objects quantifies over a cofiltered index category,
and the formalized form of Stacks 06CX is proved for index categories in the universe of the
schemes: it concludes
`AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, u, u}`. Stacks 06CY is therefore
proved at those index universes, which is the scope recorded on the tag. The condition for a
larger index universe is strictly stronger than for a smaller one, so it cannot be recovered
from the pinned form; the statement for arbitrary index universes is
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isOpenImmersion_of_criterion`, which
takes Stacks 06CX at those universes as a hypothesis and is otherwise the same deduction.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isOpenImmersion`: **Stacks 06CY**, for
  index categories in the universe of the schemes.
* `AlgebraicGeometry.Stack.hasRelativeProperty_locallyOfFinitePresentation_of_isOpenImmersion`:
  the relative open-immersion property of Stacks 03YK implies the relative property of being
  locally of finite presentation.
* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isOpenImmersion_of_criterion`: the same
  conclusion at arbitrary index universes, granted Stacks 06CX there.

## Implementation notes

`AlgebraicGeometry.Stack.IsOpenImmersion` is the relative property of Stacks 03YK at
`AlgebraicGeometry.Space.openImmersionProperty` written out, so Stacks 045F applies to it
directly. Stacks 045F asks for the property to be local at the target for the fppf precoverage,
which for open immersions follows from the fpqc form (Stacks 041X) along the comparison of
precoverages `AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`; that instance is
supplied inside the proof, since the statements here use the written-out predicate and so need
no instance in scope.

## References

* [Stacks Project, Tag 06CY](https://stacks.math.columbia.edu/tag/06CY)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
* [Stacks Project, Tag 06CN](https://stacks.math.columbia.edu/tag/06CN)
* [Stacks Project, Tag 045F](https://stacks.math.columbia.edu/tag/045F)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w vI wI

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces and an open immersion in the sense of Stacks 04XB has the
relative property of Stacks 03YK of being locally of finite presentation.

An open immersion of algebraic spaces is locally of finite presentation (Stacks 06CN), and a
relative property may be weakened along such an implication (Stacks 045F). -/
theorem hasRelativeProperty_locallyOfFinitePresentation_of_isOpenImmersion
    {p : 𝒳 ⟶ 𝒴} (hp : IsRepresentableByAlgebraicSpaces B S hS p.hom)
    (hopen : IsOpenImmersion B S hS p) :
    HasRelativeProperty.{u, v, w, u} B S hS
      (Space.locallyOfFinitePresentationProperty B S hS) p hp := by
  have : (Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  exact hasRelativeProperty_mono.{u, v, w, u, u} B S hS
    (P := Space.openImmersionProperty B S hS)
    (fun _ _ a ha => Space.isLocallyOfFinitePresentation_of_isOpenImmersion B S hS ha) hp hopen

/-- **Stacks 06CY.** A 1-morphism of categories fibred in groupoids over the big fppf site of
`S` which is representable by algebraic spaces and an open immersion in the sense of Stacks 04XB
is limit preserving on objects.

An open immersion of algebraic spaces is locally of finite presentation, so the relative
open-immersion property of Stacks 03YK implies the relative property of being locally of finite
presentation; Stacks 06CX turns the latter into limit preservation on objects. -/
@[stacks 06CY "index categories in the universe of the schemes, which is the scope of the \
formalized form of Tag 06CX that the proof uses. Limit preservation on objects for a larger index \
universe is a strictly stronger condition, so it does not follow from the pinned form; it is \
`isLimitPreservingOnObjects_of_isOpenImmersion_of_criterion`, which takes Tag 06CX at those \
universes as a hypothesis"]
theorem isLimitPreservingOnObjects_of_isOpenImmersion
    (p : 𝒳 ⟶ 𝒴) (hp : IsRepresentableByAlgebraicSpaces B S hS p.hom)
    (hopen : IsOpenImmersion B S hS p) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳 𝒴 p :=
  (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B S hS 𝒳 𝒴 p hp).2
    (hasRelativeProperty_locallyOfFinitePresentation_of_isOpenImmersion B S hS hp hopen)

/-- Stacks 06CY for index categories in arbitrary universes, granted Stacks 06CX there.

Limit preservation on objects quantifies over the cofiltered index category, so the condition
for a larger index universe is strictly stronger and is not implied by the one for a smaller
universe. The formalized form of Stacks 06CX is proved for index categories in the universe of the
schemes, which is why
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isOpenImmersion` is stated there; this is
the same deduction with Stacks 06CX at the index universes in play supplied as a hypothesis. -/
theorem isLimitPreservingOnObjects_of_isOpenImmersion_of_criterion
    (p : 𝒳 ⟶ 𝒴) (hp : IsRepresentableByAlgebraicSpaces B S hS p.hom)
    (hopen : IsOpenImmersion B S hS p)
    (h06CX : ∀ (𝒳' 𝒴' : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
      (q : 𝒳' ⟶ 𝒴') (hq : IsRepresentableByAlgebraicSpaces B S hS q.hom),
      HasRelativeProperty.{u, v, w, u} B S hS
        (Space.locallyOfFinitePresentationProperty B S hS) q hq →
      BigFppfOver.IsLimitPreservingOnObjects.{u, vI, wI} B S hS 𝒳' 𝒴' q) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, vI, wI} B S hS 𝒳 𝒴 p :=
  h06CX 𝒳 𝒴 p hp
    (hasRelativeProperty_locallyOfFinitePresentation_of_isOpenImmersion B S hS hp hopen)

end AlgebraicGeometry.Stack

end
