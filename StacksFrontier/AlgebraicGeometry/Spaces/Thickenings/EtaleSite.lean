module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings

/-!
# The inclusion of a thickening of algebraic spaces

Let `X` be an algebraic space over a scheme `S` and let `G ⊂ X` be a thickening of it, that is
a closed subspace whose inclusion is surjective on the points of Stacks 03BU. The inclusion
`G ⟶ X` is then integral, universally injective and surjective, and in fact a universal
homeomorphism. These are the properties of the inclusion which make the spaces-étale site of a
thickening agree with that of the ambient space, as in Stacks 05ZL; the identification itself,
`V ↦ G ×_X V` as an equivalence of categories, is
`AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsThickening` in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SpacesEtaleEquivalence.lean`, and the
integrality and universal injectivity proved here are what its full faithfulness rests on.

## Main results

* `AlgebraicGeometry.Space.isIntegralHom_ι_of_isThickening`: the inclusion of a thickening is
  integral.
* `AlgebraicGeometry.Space.universallyInjective_ι_of_isThickening`: it is universally
  injective.
* `AlgebraicGeometry.Space.isSurjective_ι_of_isThickening`: it is surjective.
* `AlgebraicGeometry.Space.isIntegralHom_universallyInjective_isSurjective_ι_of_isThickening`
  bundles the three.
* `AlgebraicGeometry.Space.universalHomeomorphism_ι_of_isThickening`: it is a universal
  homeomorphism.

## Implementation notes

Integrality and surjectivity are immediate from the definition of a thickening: the inclusion
is a closed immersion, and a closed immersion of algebraic spaces is integral by Stacks 081Y,
while surjectivity on points is the defining condition.

Universal injectivity and the universal homeomorphism property are conditions on the base
change of the inclusion along a morphism `g : Z ⟶ X` from an arbitrary algebraic space over
`S`, and both rest on two properties of that base change. It is again a closed immersion,
being a base change of one, so its map on points is a topological embedding by Stacks 0ABJ;
and it is surjective on points, because a point of `Z` together with the point of `G` lying
over its image in `X` is the datum of a point of the fibre product, by Stacks 03H4. A
surjective topological embedding is a homeomorphism. Neither step needs the inclusion to be
representable, so no hypothesis beyond algebraicity of the test space `Z` appears.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 05ZL](https://stacks.math.columbia.edu/tag/05ZL)
* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A base change of the inclusion of a closed subspace along a morphism to the ambient
algebraic space is again a closed immersion, hence an immersion. -/
private theorem isImmersion_pullback_fst_ι (hG : IsClosedImmersion B S hS G.ι)
    (g : Z ⟶ X.1) : IsImmersion B S hS (pullback.fst g G.ι) :=
  isImmersion_of_isClosedImmersion B S hS
    ((MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback
      (IsPullback.of_hasPullback g G.ι).flip hG)

/-- A base change of the inclusion of a thickening along a morphism to the ambient algebraic
space is surjective on points: a point of the base and the point of the thickening over its
image assemble into a point of the fibre product. -/
private theorem surjective_pointsMap_pullback_fst_ι (hG : IsThickening B S hS X G)
    (g : Z ⟶ X.1) :
    Function.Surjective (pointsMap B S hS (pullback g G.ι) (pullback.fst g G.ι)) := by
  intro y
  obtain ⟨x, hx⟩ := hG.2 (pointsMap B S hS Z g y)
  obtain ⟨w, hw, -⟩ :=
    exists_points_of_isPullback B S hS (IsPullback.of_hasPullback g G.ι) y x hx.symm
  exact ⟨w, hw⟩

/-- The inclusion of a thickening of an algebraic space over `S` is integral: it is a closed
immersion, and a closed immersion is integral. -/
theorem isIntegralHom_ι_of_isThickening (hG : IsThickening B S hS X G) :
    IsIntegralHom B S hS G.ι :=
  isIntegralHom_of_isClosedImmersion B S hS G.ι hG.1.2

/-- The inclusion of a thickening of an algebraic space over `S` is universally injective: each
of its base changes is a closed immersion, hence an immersion, and an immersion is injective on
points. -/
theorem universallyInjective_ι_of_isThickening (hG : IsThickening B S hS X G) :
    UniversallyInjective B S hS G.ι := fun _ hZ g ↦
  injective_pointsMap_of_isImmersion B S hS hZ _ (isImmersion_pullback_fst_ι B S hS hG.1.2 g)

/-- The inclusion of a thickening of an algebraic space over `S` is surjective: this is the
defining condition of a thickening. -/
theorem isSurjective_ι_of_isThickening (hG : IsThickening B S hS X G) :
    IsSurjective B S hS G.ι :=
  hG.2

/-- **Stacks 05ZL.** The inclusion of a thickening of an algebraic space over `S` is integral,
universally injective and surjective. -/
@[stacks 05ZL "the inclusion of a thickening is integral, universally injective and surjective"]
theorem isIntegralHom_universallyInjective_isSurjective_ι_of_isThickening
    (hG : IsThickening B S hS X G) :
    IsIntegralHom B S hS G.ι ∧ UniversallyInjective B S hS G.ι ∧ IsSurjective B S hS G.ι :=
  ⟨isIntegralHom_ι_of_isThickening B S hS hG, universallyInjective_ι_of_isThickening B S hS hG,
    isSurjective_ι_of_isThickening B S hS hG⟩

/-- The inclusion of a thickening of an algebraic space over `S` is a universal homeomorphism:
each of its base changes is a closed immersion, hence an embedding on points, and it is
surjective on points, and a surjective embedding is a homeomorphism. -/
theorem universalHomeomorphism_ι_of_isThickening (hG : IsThickening B S hS X G) :
    UniversalHomeomorphism B S hS G.ι := fun _ hZ g ↦
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨isEmbedding_pointsMap_of_isImmersion B S hS hZ _
      (isImmersion_pullback_fst_ι B S hS hG.1.2 g),
      surjective_pointsMap_pullback_fst_ι B S hS hG g⟩

end AlgebraicGeometry.Space

end
