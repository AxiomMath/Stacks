module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackTwoIso
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation

/-!
# Replacing the target by a substack the 1-morphism factors through up to 2-isomorphism

`StacksFrontier/AlgebraicGeometry/Stacks/RelativeDimensionSchemeTheoreticImage.lean` replaces the
target `𝒳` of `f : 𝒯 ⟶ 𝒳` by a substack `𝒵` that `f` lands in object by object. The scheme
theoretic image of Stacks 0CMI is a substack through which `f` factors only up to
2-isomorphism (`AlgebraicGeometry.Stack.FactorsThroughSubstack`), and the statements here take
that weaker input: the factorization `AlgebraicGeometry.Stack.factorsThroughSubstackHom` is
locally of finite type, and when the inclusion of `𝒵` is a monomorphism (Stacks 04ZW) the
relative dimension of Stacks 0DRL of `f` is that of the factorization.

## Main results

* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_substackFactorizationHom`
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_substackFactorizationHom`

## References

* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 06U9](https://stacks.math.columbia.edu/tag/06U9)
* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The factorization of a 1-morphism locally of finite type through a substack is locally of
finite type.** Its composite with the inclusion of the substack is 2-isomorphic to the given
1-morphism, hence locally of finite type, and Stacks 06U9 cancels the inclusion. -/
theorem isLocallyOfFiniteType_substackFactorizationHom
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    {P : ObjectProperty 𝒳.val.val.obj}
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hfac : FactorsThroughSubstack f P) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS (factorsThroughSubstackHom f hA hfac) :=
  AlgebraicStacks.isLocallyOfFiniteType_of_comp B S hS (factorsThroughSubstackHom f hA hfac)
    (fullSubcategoryInclusion 𝒳 P hA)
    (AlgebraicStacks.isLocallyOfFiniteType_of_twoIso B S hS
      (Bicategory.InducedBicategory.isoHom (factorsThroughSubstackIso f hA hfac).symm) hf)

/-- **The relative dimension of Stacks 0DRL is unchanged when the target is replaced by a
monomorphic substack the 1-morphism factors through.** Let `f : 𝒯 ⟶ 𝒳` be locally of finite type
with `𝒯` and `𝒳` locally Noetherian algebraic stacks over `S`, let `P` cut out a substack `𝒵`
whose inclusion is a monomorphism (Stacks 04ZW) and which is locally Noetherian, and suppose `f`
factors through `P`. Then the relative dimension of Stacks 0DRL of `f` at every `t ∈ |𝒯|` is
that of the factorization `𝒯 ⟶ 𝒵`.

For the scheme theoretic image of **Stacks 0CMI** this is the reduction with which the proof of
**Stacks 0DS4** begins: the inclusion of the image is a closed immersion, hence an immersion,
hence a monomorphism, so the fibre dimension of `f` may be read over the image instead of over
`𝒳`. -/
theorem relativeStackDimensionAt_substackFactorizationHom
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    {P : ObjectProperty 𝒳.val.val.obj}
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hfac : FactorsThroughSubstack f P)
    (hi : AlgebraicStacks.IsMonomorphism B S hS (fullSubcategoryInclusion 𝒳 P hA))
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒵 : IsLocallyNoetherianStack.{u, w} B S hS (fullSubcategoryAlgebraicStack 𝒳 P hA))
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t =
      relativeStackDimensionAt.{u, w} B S hS (factorsThroughSubstackHom f hA hfac)
        (isLocallyOfFiniteType_substackFactorizationHom.{u, w} B S hS f hf hA hfac) h𝒯 h𝒵 t :=
  relativeStackDimensionAt_comp_of_isMonomorphism_of_twoIso.{u, w} B S hS f
    (factorsThroughSubstackHom f hA hfac) (fullSubcategoryInclusion 𝒳 P hA)
    (factorsThroughSubstackIso f hA hfac).symm hi hf
    (isLocallyOfFiniteType_substackFactorizationHom.{u, w} B S hS f hf hA hfac)
    (AlgebraicStacks.isLocallyOfFiniteType_of_twoIso B S hS
      (Bicategory.InducedBicategory.isoHom (factorsThroughSubstackIso f hA hfac).symm) hf)
    h𝒯 h𝒵 h𝒳 t

end AlgebraicGeometry.Stack

end
