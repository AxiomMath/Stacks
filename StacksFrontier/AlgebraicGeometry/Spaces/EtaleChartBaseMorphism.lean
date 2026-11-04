module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType

/-!
# The morphism of schemes from an étale chart to a representable base

Let `f : X ⟶ h_{Y₀}` be a morphism from a presheaf on the big fppf site of `S` to a
representable presheaf and let `φ : h_T ⟶ X` be an étale chart of `X`. Then `φ ≫ f` is a
morphism between representable presheaves, hence the Yoneda image of a morphism `t : T ⟶ Y₀`
of the site. The conditions on `f` of Stacks 03MJ are conditions on the morphisms of schemes
arising from commuting squares of étale charts of the source and the target, and the identity
is an étale chart of a representable presheaf, so every such condition on `f` is inherited by
the underlying scheme morphism of `t`.

This is the step of the proof of Stacks 082H which turns its morphism of algebraic spaces,
after the target has been replaced by an affine scheme and an affine étale chart `Z` of the
source has been chosen, into the morphism of affine *schemes* `Z ⟶ Y` to which
Tag 02LN is applied.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.prop_toScheme_map_of_holdsOnEveryEtaleChart`: a property of scheme
  morphisms which holds on every étale chart of `f` holds for the underlying scheme morphism
  of `t`.
* `AlgebraicGeometry.Space.locallyOfFiniteType_toScheme_map_of_chart` and
  `AlgebraicGeometry.Space.locallyQuasiFinite_toScheme_map_of_chart`: the instances of that
  for parts (1) of Stacks 03XF and of Stacks 03XJ.

## Implementation notes

`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` quantifies over a chart `a` of the source, a
chart `b` of the target and a morphism `h` of the site with `yoneda.map h ≫ b = a ≫ f`. Here
`b` is taken to be the Yoneda image of the identity of `Y₀`, which is an étale chart by
`AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff` and the étaleness of an
identity morphism of schemes; no étale chart of the target other than the identity is needed
and no algebraicity hypothesis enters.

The morphism `t` is a hypothesis rather than constructed by `yoneda.preimage`, so that a
caller which already has a morphism of the site in hand — as Stacks 082H does, since its
chart is built from a morphism of the site — can use it directly. Fullness of the Yoneda
embedding supplies one in general.

No declaration here carries a Stacks tag. Stacks 03MJ is about the *equivalence* of the
conditions it lists, and the implication used here is the trivial direction of condition (1)
applied to a single square, not an assertion of that tag.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A property holding on every étale chart holds for the chart-to-base morphism of
schemes.** If `P` holds on every étale chart of `f : X ⟶ h_{Y₀}`, if `φ : h_T ⟶ X` is an
étale chart of `X` and if `t : T ⟶ Y₀` is a morphism of the site whose Yoneda image is
`φ ≫ f`, then the scheme morphism underlying `t` has `P`.

The étale chart of the target is the identity of `Y₀`. -/
theorem prop_toScheme_map_of_holdsOnEveryEtaleChart
    {P : MorphismProperty Scheme.{u}}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ T : BigFppfOver B S hS}
    {f : X ⟶ yoneda.obj Y₀} (hf : HoldsOnEveryEtaleChart B S hS P f)
    (φ : yoneda.obj T ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    {t : T ⟶ Y₀} (ht : yoneda.map t = φ ≫ f) :
    P ((BigFppfOver.toScheme B S hS).map t) := by
  refine hf T Y₀ φ (yoneda.map (𝟙 Y₀)) t hφ ?_ (by simpa using ht)
  refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (𝟙 Y₀)).2 ?_
  simpa using
    (inferInstance : AlgebraicGeometry.Etale (𝟙 ((BigFppfOver.toScheme B S hS).obj Y₀)))

/-- **The chart-to-base morphism of a morphism locally of finite type is locally of finite
type.** This is `AlgebraicGeometry.Space.prop_toScheme_map_of_holdsOnEveryEtaleChart` at part
(1) of Stacks 03XF. -/
theorem locallyOfFiniteType_toScheme_map_of_chart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ T : BigFppfOver B S hS}
    {f : X ⟶ yoneda.obj Y₀} (hf : IsLocallyOfFiniteType B S hS f)
    (φ : yoneda.obj T ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    {t : T ⟶ Y₀} (ht : yoneda.map t = φ ≫ f) :
    AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map t) :=
  prop_toScheme_map_of_holdsOnEveryEtaleChart B S hS hf φ hφ ht

/-- **The chart-to-base morphism of a locally quasi-finite morphism is locally of finite type
and locally quasi-finite.** This is
`AlgebraicGeometry.Space.prop_toScheme_map_of_holdsOnEveryEtaleChart` at part (1) of
Stacks 03XJ, whose property is the infimum of the two conditions. -/
theorem locallyQuasiFinite_toScheme_map_of_chart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ T : BigFppfOver B S hS}
    {f : X ⟶ yoneda.obj Y₀} (hf : IsLocallyQuasiFinite B S hS f)
    (φ : yoneda.obj T ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    {t : T ⟶ Y₀} (ht : yoneda.map t = φ ≫ f) :
    AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map t) ∧
      AlgebraicGeometry.LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map t) :=
  prop_toScheme_map_of_holdsOnEveryEtaleChart B S hS hf φ hφ ht

end AlgebraicGeometry.Space

end
