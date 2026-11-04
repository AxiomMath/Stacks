module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings

/-!
# Morphisms of algebraic spaces that are thickenings

Stacks 05ZK, part (1) defines a thickening as a *closed subspace* `G ⊆ X'` whose points
exhaust those of `X'`. Most statements about thickenings are instead phrased for a
*morphism* `i : X ⟶ X'`, which is a thickening when it is an isomorphism onto its range
and that range is a thickening subspace of `X'`. This file introduces that morphism-level
notion and proves the three facts about it that the subspace-level definition does not
give directly: a thickening is a monomorphism, it is a closed immersion, and it is
surjective — the morphism form of "the associated topological spaces are equal".

## Main definitions

* `AlgebraicGeometry.Space.IsThickeningHom` is the morphism-level thickening condition.

## Main results

* `AlgebraicGeometry.Space.isThickeningHom_iff_of_mono` identifies the condition, for a
  monomorphism, with the subspace-level condition on its range.
* `AlgebraicGeometry.Space.IsThickeningHom.mono`,
  `AlgebraicGeometry.Space.IsThickeningHom.isClosedImmersion` and
  `AlgebraicGeometry.Space.IsThickeningHom.surjective_pointsMap` extract the three
  properties of a thickening from the definition.
* `AlgebraicGeometry.Space.IsThickeningHom.surjective` combines the last two with Stacks
  03MD to conclude that a thickening is a surjective morphism of algebraic spaces.

Also proved here, and used throughout, is
`AlgebraicGeometry.Space.pointsMap_surjective_of_isIso`: the map on points induced by an
isomorphism of presheaves on the big fppf site is surjective. The library had this only
for isomorphisms of algebraic spaces, as a private lemma.

## Implementation notes

A thickening is *not* defined as the conjunction "closed immersion and surjective". That
conjunction is equivalent, but only via the fact that the range of a closed immersion is
again an algebraic space, which is not available here; the range formulation is the one
that Stacks 05ZK part (1) states and the one that composes with the subspace-level API.
The three results above are therefore one-directional: they go from the range formulation
to the closed-immersion formulation and not back.

The morphism-level notion is the shape in which thickenings of algebraic spaces appear in
Stacks 05ZS, 07VX and 0AIC, none of whose statements mention a subfunctor.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 03MD](https://stacks.math.columbia.edu/tag/03MD)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of algebraic spaces over `S` *is a thickening* when it identifies its
source with a thickening subspace of its target: it is an isomorphism onto its range, and
that range is a thickening of the target in the sense of Stacks 05ZK, part (1). -/
def IsThickeningHom {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X') : Prop :=
  IsIso (Subfunctor.toRange i.hom) ∧ IsThickening B S hS X' (Subfunctor.range i.hom)

variable {B S hS}

/-- For a monomorphism of algebraic spaces, being a thickening is exactly the statement
that its range is a thickening subspace of the target. -/
theorem isThickeningHom_iff_of_mono {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X')
    [Mono i.hom] :
    IsThickeningHom B S hS i ↔ IsThickening B S hS X' (Subfunctor.range i.hom) :=
  ⟨fun h => h.2, fun h => ⟨inferInstance, h⟩⟩

/-- A thickening of algebraic spaces is a monomorphism. -/
theorem IsThickeningHom.mono {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'}
    (hi : IsThickeningHom B S hS i) : Mono i.hom := by
  have := hi.1
  rw [← Subfunctor.toRange_ι i.hom]
  exact mono_comp _ _

/-- A thickening of algebraic spaces is surjective on points: the source and the target
have the same points. -/
theorem IsThickeningHom.surjective_pointsMap {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'}
    (hi : IsThickeningHom B S hS i) :
    Function.Surjective (pointsMap B S hS X.obj i.hom) := by
  have e : pointsMap B S hS X.obj i.hom
      = pointsMap B S hS (Subfunctor.range i.hom).toFunctor (Subfunctor.range i.hom).ι
        ∘ pointsMap B S hS X.obj (Subfunctor.toRange i.hom) := by
    rw [← pointsMap_comp, Subfunctor.toRange_ι]
  rw [e]
  exact hi.2.2.comp
    (@pointsMap_surjective_of_isIso B S hS _ _ (Subfunctor.toRange i.hom) hi.1)

/-- A thickening of algebraic spaces is a closed immersion. -/
theorem IsThickeningHom.isClosedImmersion {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'}
    (hi : IsThickeningHom B S hS i) : IsClosedImmersion B S hS i.hom := by
  have := hi.1
  let Q := MorphismProperty.presheaf
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
  let _ : Q.RespectsIso := inferInstance
  have h : Q (Subfunctor.toRange i.hom ≫ (Subfunctor.range i.hom).ι) :=
    MorphismProperty.RespectsIso.precomp Q (Subfunctor.toRange i.hom)
      (Subfunctor.range i.hom).ι hi.2.1.2
  rwa [Subfunctor.toRange_ι] at h

/-- **Stacks 05ZK, part (1), morphism form.** A thickening of algebraic spaces is a
surjective morphism. -/
theorem IsThickeningHom.surjective {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'}
    (hi : IsThickeningHom B S hS i) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom :=
  (surjective_iff_pointsMap_surjective B S hS X.property X'.property i.hom
    hi.isClosedImmersion.rep).mpr hi.surjective_pointsMap

end AlgebraicGeometry.Space

end
