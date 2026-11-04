module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralGenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Alterations of an integral algebraic space

An *alteration* of an integral algebraic space `X` over a scheme `S` is a proper dominant
morphism `f : Y ⟶ X` of algebraic spaces over `S` whose source `Y` is again integral and
which is finite over some nonempty open subspace of `X`.

## Main definitions

* `AlgebraicGeometry.Space.IsAlteration` is the property of being an alteration.

## Main results

* `AlgebraicGeometry.Space.IsAlteration.isIntegralSpace_target`,
  `AlgebraicGeometry.Space.IsAlteration.isIntegralSpace_source`,
  `AlgebraicGeometry.Space.IsAlteration.isProper`,
  `AlgebraicGeometry.Space.IsAlteration.isDominant` and
  `AlgebraicGeometry.Space.IsAlteration.exists_isFinite_over_nonempty_open` read off the
  five conditions.
* `AlgebraicGeometry.Space.isAlteration_iff_isQuasiFiniteAt` is **Stacks 0ADB**: a proper
  dominant morphism of integral algebraic spaces is an alteration exactly when it is
  quasi-finite at the generic point of its source.

## Implementation notes

The nonempty open subspace of the target is a subfunctor `U` of `X` which is an open
subspace in the sense of Stacks 02YU, nonempty in the sense that its space of points of
Stacks 03BU is inhabited. Its inverse image and the restriction of `f` to that inverse image
are `CategoryTheory.Subfunctor.preimage` and `CategoryTheory.Subfunctor.fromPreimage`, so
finiteness over `U` is finiteness of `U.fromPreimage f` in the sense of Stacks 03ZP.

Integrality of source and target is part of the predicate rather than of its context, so
that the predicate applies to a morphism of presheaves before an integral target has been
selected; the neighbouring `AlgebraicGeometry.Space.IsIntegralModification` of Stacks 0AD8
keeps integrality of the target as context instead because birationality, which that notion
uses and this one does not, needs it to make sense. Algebraicity of source and target is a
conjunct for the same reason, as it is for `AlgebraicGeometry.Space.IsModification` of
Stacks 0BGY.

The definition is an `abbrev`, as `AlgebraicGeometry.Space.IsIntegralSpace` is, so that its
conjuncts are available to statements about alterations without an unfolding lemma; the five
projections below are the named form of that.

Stacks 0ADB is stated against condition (4) of Stacks 0AD5, quasi-finiteness at the generic
point of the source: that is the condition the two implications are proved from, and
Stacks 0AD5 compares it with the others. The generic points of source and target are part of
the datum, as in `StacksFrontier/AlgebraicGeometry/Spaces/IntegralGenericallyFinite.lean`: the
point spaces are irreducible, so a generic point exists, but choosing one is a choice.

## References

* [Stacks Project, Tag 0ADA](https://stacks.math.columbia.edu/tag/0ADA)
* [Stacks Project, Tag 0ADB](https://stacks.math.columbia.edu/tag/0ADB)
* [Stacks Project, Tag 0AD5](https://stacks.math.columbia.edu/tag/0AD5)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0ADA.** An *alteration* of an integral algebraic space `X` over `S` is a proper
dominant morphism `f : Y ⟶ X` of algebraic spaces over `S` with `Y` integral such that the
inverse image of some nonempty open subspace `U ⊆ X` is finite over `U`. -/
@[stacks 0ADA]
abbrev IsAlteration (f : Y ⟶ X) : Prop :=
  IsAlgebraicSpace B S hS X ∧ IsIntegralSpace B S hS X ∧
    IsAlgebraicSpace B S hS Y ∧ IsIntegralSpace B S hS Y ∧
      IsProper B S hS f ∧ IsDominant B S hS f ∧
        ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
          Nonempty (points B S hS U.toFunctor) ∧ IsFinite B S hS (U.fromPreimage f)

/-- The target of an alteration is an algebraic space over `S`. -/
theorem IsAlteration.isAlgebraicSpace_target {f : Y ⟶ X}
    (hf : IsAlteration B S hS f) : IsAlgebraicSpace B S hS X := hf.1

/-- The target of an alteration is integral. -/
theorem IsAlteration.isIntegralSpace_target {f : Y ⟶ X}
    (hf : IsAlteration B S hS f) : IsIntegralSpace B S hS X := hf.2.1

/-- The source of an alteration is an algebraic space over `S`. -/
theorem IsAlteration.isAlgebraicSpace_source {f : Y ⟶ X}
    (hf : IsAlteration B S hS f) : IsAlgebraicSpace B S hS Y := hf.2.2.1

/-- The source of an alteration is integral. -/
theorem IsAlteration.isIntegralSpace_source {f : Y ⟶ X}
    (hf : IsAlteration B S hS f) : IsIntegralSpace B S hS Y := hf.2.2.2.1

/-- An alteration is proper. -/
theorem IsAlteration.isProper {f : Y ⟶ X} (hf : IsAlteration B S hS f) :
    IsProper B S hS f := hf.2.2.2.2.1

/-- An alteration is dominant. -/
theorem IsAlteration.isDominant {f : Y ⟶ X} (hf : IsAlteration B S hS f) :
    IsDominant B S hS f := hf.2.2.2.2.2.1

/-- An alteration is finite over some nonempty open subspace of its target. -/
theorem IsAlteration.exists_isFinite_over_nonempty_open {f : Y ⟶ X}
    (hf : IsAlteration B S hS f) :
    ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
      Nonempty (points B S hS U.toFunctor) ∧ IsFinite B S hS (U.fromPreimage f) :=
  hf.2.2.2.2.2.2

/-- **Stacks 0ADB.** A proper dominant morphism `f : Y ⟶ X` of integral algebraic spaces over
`S` is an alteration exactly when it is quasi-finite at the generic point of `|Y|`, which is
condition (4) of Stacks 0AD5 and hence equivalent to the other conditions compared there. -/
@[stacks 0ADB "against condition (4) of Stacks 0AD5"]
theorem isAlteration_iff_isQuasiFiniteAt (hY : IsAlgebraicSpace B S hS Y)
    (hX : IsAlgebraicSpace B S hS X) (hYint : IsIntegralSpace B S hS Y)
    (hXint : IsIntegralSpace B S hS X) (f : Y ⟶ X) (hp : IsProper B S hS f)
    (hdom : IsDominant B S hS f)
    {y : points B S hS Y} (hy : IsGenericPoint y (Set.univ : Set (points B S hS Y)))
    {x : points B S hS X} (hx : IsGenericPoint x (Set.univ : Set (points B S hS X))) :
    IsAlteration B S hS f ↔ IsQuasiFiniteAt B S hS f y := by
  have hyx : pointsMap B S hS Y f y = x :=
    pointsMap_eq_of_isGenericPoint B S hS hX hXint.isDecentSpace f hdom hy hx
  constructor
  · rintro ⟨-, -, -, -, -, -, U, hU, hUne, hfin⟩
    exact isQuasiFiniteAt_of_isFinite_fromPreimage B S hS hY hX f hx hyx U hU hUne hfin
  · intro hqf
    obtain ⟨U, hU, hUne, hfin⟩ :=
      exists_isFinite_fromPreimage_of_isQuasiFiniteAt B S hS hY hX hXint f hp hdom hy hx hqf
    exact ⟨hX, hXint, hY, hYint, hp, hdom, U, hU, hUne, hfin⟩

end AlgebraicGeometry.Space

end
