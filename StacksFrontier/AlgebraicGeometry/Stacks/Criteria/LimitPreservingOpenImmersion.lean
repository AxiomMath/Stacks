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

*Index universes.* Limit preservation on objects quantifies over a cofiltered index category.
The directed systems of the source are sets, which here means index categories whose objects and
morphisms lie in universes bounded by the universe `u` of the schemes. The formalized form of
Stacks 06CX concludes the condition for index categories in the universe `u` itself; every index
category in universes bounded by `u` is equivalent to one in `u`, and the condition is invariant
under such a replacement (`AlgebraicGeometry.BigFppfOver.isLimitPreservingOnObjects_of_univLE`),
which gives Stacks 06CY for all of the source's index categories.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isOpenImmersion_of_univLE`:
  **Stacks 06CY**, for every index category in universes bounded by that of the schemes.
* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isOpenImmersion`: the same at index
  categories in the universe of the schemes.
* `AlgebraicGeometry.BigFppfOver.isLimitPreservingOnObjects_of_univLE`: the condition at index
  categories in the universe of the schemes implies it in all universes bounded by it.
* `AlgebraicGeometry.Stack.hasRelativeProperty_locallyOfFinitePresentation_of_isOpenImmersion`:
  the relative open-immersion property of Stacks 03YK implies the relative property of being
  locally of finite presentation.
* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isOpenImmersion_of_criterion`: the
  deduction from Stacks 06CX phrased for index categories in arbitrary universes, from the
  corresponding form of Stacks 06CX.

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

universe u v w vI wI

namespace AlgebraicGeometry.BigFppfOver

/-- Limit preservation on objects for index categories in the universe `u` of the schemes implies
it for every index category in universes `vI` and `wI` bounded by `u`: such a category is
essentially small, and the condition is invariant under replacing the index category by an
equivalent one. -/
theorem isLimitPreservingOnObjects_of_univLE [hv : UnivLE.{vI, u}] [hw : UnivLE.{wI, u}]
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳 𝒴 f) :
    IsLimitPreservingOnObjects.{u, vI, wI} B S hS 𝒳 𝒴 f := by
  intro I _ _ D c hc i y x γ hγ
  let E : I ≃ Shrink.{u} I := equivShrink I
  let I' := InducedCategory I E.symm
  have : LocallySmall.{u} I' := ⟨fun _ _ => inferInstance⟩
  let J := ShrinkHoms I'
  have : (inducedFunctor E.symm).EssSurj :=
    ⟨fun X => ⟨E X, ⟨eqToIso (E.symm_apply_apply X)⟩⟩⟩
  have : (inducedFunctor E.symm).IsEquivalence := { }
  let e : J ≌ I := (ShrinkHoms.equivalence I' : I' ≌ J).symm.trans
    (inducedFunctor E.symm).asEquivalence
  let q : J ⥤ I := e.functor
  have : IsCofiltered J := IsCofiltered.of_equivalence e.symm
  have hc' : Limits.IsLimit ((BigAffineFppf.toScheme B S hS).mapCone (c.whisker q)) :=
    (Functor.Initial.isLimitWhiskerEquiv q
      ((BigAffineFppf.toScheme B S hS).mapCone c)).symm hc
  obtain ⟨k, rfl⟩ : ∃ k : J, q.obj k = i :=
    ⟨ShrinkHoms.toShrinkHoms (E i), E.symm_apply_apply i⟩
  obtain ⟨j, a, x', xU, δ, β, γ', hδ, hβ, hβiso, hγ', hcomm⟩ :=
    hf J (q ⋙ D) (c.whisker q) hc' k y x γ hγ
  exact ⟨q.obj j, q.map a, x', xU, δ, β, γ', hδ, hβ, hβiso, hγ', hcomm⟩

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.Stack

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

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces and an open immersion in the sense of Stacks 04XB is limit
preserving on objects, for index categories in the universe of the schemes. Stacks 06CY for every
index category of the source is
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isOpenImmersion_of_univLE`.

An open immersion of algebraic spaces is locally of finite presentation, so the relative
open-immersion property of Stacks 03YK implies the relative property of being locally of finite
presentation; Stacks 06CX turns the latter into limit preservation on objects. -/
theorem isLimitPreservingOnObjects_of_isOpenImmersion
    (p : 𝒳 ⟶ 𝒴) (hp : IsRepresentableByAlgebraicSpaces B S hS p.hom)
    (hopen : IsOpenImmersion B S hS p) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳 𝒴 p :=
  (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B S hS 𝒳 𝒴 p hp).2
    (hasRelativeProperty_locallyOfFinitePresentation_of_isOpenImmersion B S hS hp hopen)

/-- **Stacks 06CY.** A 1-morphism of categories fibred in groupoids over the big fppf site of
`S` which is representable by algebraic spaces and an open immersion in the sense of Stacks 04XB
is limit preserving on objects, for every index category whose objects and morphisms form sets,
that is, live in universes `vI` and `wI` bounded by the universe `u` of the schemes.

The directed systems of the source are sets, so these are exactly its index categories. Such an
index category is equivalent to one in the universe `u`, and the condition there is
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isOpenImmersion`; the transport is
`AlgebraicGeometry.BigFppfOver.isLimitPreservingOnObjects_of_univLE`. -/
@[stacks 06CY "index categories range over all cofiltered categories whose objects and morphisms \
lie in universes bounded by that of the schemes, which covers the directed sets of the source"]
theorem isLimitPreservingOnObjects_of_isOpenImmersion_of_univLE
    [UnivLE.{vI, u}] [UnivLE.{wI, u}]
    (p : 𝒳 ⟶ 𝒴) (hp : IsRepresentableByAlgebraicSpaces B S hS p.hom)
    (hopen : IsOpenImmersion B S hS p) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, vI, wI} B S hS 𝒳 𝒴 p :=
  BigFppfOver.isLimitPreservingOnObjects_of_univLE (hv := inferInstanceAs UnivLE.{vI, u})
    (hw := inferInstanceAs UnivLE.{wI, u}) B S hS p
    (isLimitPreservingOnObjects_of_isOpenImmersion B S hS p hp hopen)

/-- The deduction of Stacks 06CY from Stacks 06CX, phrased for index categories in arbitrary
universes: given the implication of Stacks 06CX from local finite presentation to limit
preservation on objects at the index universes `vI` and `wI`, an open immersion is limit
preserving on objects at those universes. For index universes bounded by that of the schemes,
which are the source's, the conclusion holds outright:
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isOpenImmersion_of_univLE`. -/
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
