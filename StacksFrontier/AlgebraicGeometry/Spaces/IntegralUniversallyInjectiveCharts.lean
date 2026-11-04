module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Represented base changes of an integral universally injective morphism

Let `f : Y ⟶ X` be an integral and universally injective morphism of algebraic spaces over a
scheme `S`. This file records what its *represented* base changes look like as morphisms of
schemes: each of them is integral, injective on points, and therefore a homeomorphism onto a
closed subset of its target.

That last property is exactly the hypothesis of Étale Cohomology 04DW, property (C) for a
morphism of schemes, and it is also all that the open-extension step in the proof of
Stacks 04FV uses about a closed immersion. It is therefore the geometric input through which
the chart-level statements for an integral universally injective morphism are proved.

## Main results

* `AlgebraicGeometry.Space.injective_toScheme_map_of_injective_pointsMap`: a morphism of the
  big fppf site of `S` is injective on the points of the underlying schemes as soon as it is
  injective on the points of the represented presheaves.
* `AlgebraicGeometry.Space.injective_toScheme_map_snd_of_universallyInjective`: the represented
  base changes of a universally injective morphism are injective on points.
* `AlgebraicGeometry.Space.isIntegralHom_toScheme_map_snd`: the represented base changes of an
  integral morphism are integral morphisms of schemes.
* `AlgebraicGeometry.Space.isClosedEmbedding_toScheme_map_snd`: the represented base changes of
  an integral universally injective morphism are homeomorphisms onto closed subsets.

## References

* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 03MV](https://stacks.math.columbia.edu/tag/03MV)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the big fppf site of `S` which is injective on the points of the represented
presheaves is injective on the points of the underlying schemes, the two point sets being
identified by the bijection of Stacks 03BV. -/
theorem injective_toScheme_map_of_injective_pointsMap {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (hinj : Function.Injective (pointsMap B S hS (yoneda.obj U) (yoneda.map h))) :
    Function.Injective ((BigFppfOver.toScheme B S hS).map h) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := surjective_pointsToScheme B S hS U x
  obtain ⟨b, rfl⟩ := surjective_pointsToScheme B S hS U y
  refine congrArg (pointsToScheme B S hS U) (hinj (injective_pointsToScheme B S hS V ?_))
  rw [pointsToScheme_pointsMap_yoneda, pointsToScheme_pointsMap_yoneda]
  exact hxy

variable {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : Y ⟶ X}

/-- **The represented base changes of a universally injective morphism are injective on
points.** Universal injectivity is stable under base change, and a universally injective
morphism is injective on points; the points of a represented presheaf are those of the
representing scheme by Stacks 03BV. -/
theorem injective_toScheme_map_snd_of_universallyInjective
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (hrep : yoneda.relativelyRepresentable f) (hui : UniversallyInjective B S hS f)
    {A : BigFppfOver B S hS} (g : yoneda.obj A ⟶ X) :
    Function.Injective ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) :=
  injective_toScheme_map_of_injective_pointsMap B S hS (hrep.snd g)
    (injective_pointsMap_of_universallyInjective B S hS (isAlgebraicSpace_yoneda B S hS A)
      (universallyInjective_of_isPullback B S hS hY (isAlgebraicSpace_yoneda B S hS A) hX f g
        hui (hrep.isPullback g).flip))

/-- **The represented base changes of an integral morphism are integral.** This is conditions
(1) and (2) of Stacks 03ZQ read at the chosen representable pullback. -/
theorem isIntegralHom_toScheme_map_snd (hY : IsAlgebraicSpace B S hS Y)
    (hX : IsAlgebraicSpace B S hS X) (hrep : yoneda.relativelyRepresentable f)
    (hint : IsIntegralHom B S hS f) {A : BigFppfOver B S hS} (g : yoneda.obj A ⟶ X) :
    _root_.AlgebraicGeometry.IsIntegralHom
      ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) :=
  ((isIntegralHom_iff_representable B S hS f hY hX).mp hint).2.property g (hrep.fst g)
    (hrep.snd g) (hrep.isPullback g)

/-- **The represented base changes of an integral universally injective morphism are
homeomorphisms onto closed subsets.** An integral morphism of schemes is universally closed,
hence a closed map, and the base change is injective on points by universal injectivity; a
continuous injective closed map is a closed embedding.

This is the hypothesis under which Étale Cohomology 04DW gives property (C), and it is also
all that the open-extension step of Stacks 04FV uses. -/
theorem isClosedEmbedding_toScheme_map_snd (hY : IsAlgebraicSpace B S hS Y)
    (hX : IsAlgebraicSpace B S hS X) (hrep : yoneda.relativelyRepresentable f)
    (hint : IsIntegralHom B S hS f) (hui : UniversallyInjective B S hS f)
    {A : BigFppfOver B S hS} (g : yoneda.obj A ⟶ X) :
    Topology.IsClosedEmbedding
      ((BigFppfOver.toScheme B S hS).map (hrep.snd g)).base := by
  have hi : _root_.AlgebraicGeometry.IsIntegralHom
      ((BigFppfOver.toScheme B S hS).map (hrep.snd g)) :=
    isIntegralHom_toScheme_map_snd B S hS hY hX hrep hint g
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    ((BigFppfOver.toScheme B S hS).map (hrep.snd g)).continuous
    (injective_toScheme_map_snd_of_universallyInjective B S hS hY hX hrep hui g)
    ((BigFppfOver.toScheme B S hS).map (hrep.snd g)).isClosedMap

end AlgebraicGeometry.Space

end
