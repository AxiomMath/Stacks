module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# Étale-smooth locality on the source and target for algebraic spaces (Stacks 0CFZ)

A property of morphisms of algebraic spaces over a scheme `S` is *étale-smooth local on the
source-and-target* when it is stable under precomposition by étale morphisms and under smooth
base change, and when it can be checked on an étale neighbourhood over a smooth target
neighbourhood of every point of the source.

This is the hypothesis under which Stacks 0CIF introduces the corresponding property of
Deligne–Mumford morphisms of algebraic stacks, so it is part of that statement, and the three
fields are the API every locality result above it uses. It is the Deligne–Mumford analogue of
`AlgebraicGeometry.Space.IsSmoothLocalOnSourceAndTarget` (**Stacks 06F8**), with étale replacing
smooth on the source side only.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget`: **Stacks 0CFZ**.

## Implementation notes

Unlike `AlgebraicGeometry.Space.IsSmoothLocalOnSourceAndTarget`, which is stated for a property
of natural transformations of presheaves with the algebraicity of each object carried by an
explicit hypothesis in every clause, this is stated for a property of morphisms of the category
`AlgebraicGeometry.AlgebraicSpaces` of **Stacks 02X2**, so algebraicity is part of the objects
and no clause needs such a hypothesis. That is the level Stacks 0CIF, 0CIG and 0CIT are written
at.

The base change in the second and third clauses is the fibre product
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` of **Stacks 02X2**, with its second projection
to the new target; the neighbourhood in the locality clause consists of a smooth `b : V ⟶ Y` and
an étale `e : U ⟶ X ×_Y V`, whose composites with the two projections give the commuting square
and the point condition.

## References

* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

/-- **Stacks 0CFZ.** A property of morphisms of algebraic spaces over `S` is *étale-smooth local
on the source-and-target* when it is stable under étale precomposition and under smooth base
change, and holds exactly when it holds on an étale neighbourhood over a smooth target
neighbourhood of every point of the source. -/
@[stacks 0CFZ]
structure IsEtaleSmoothLocalOnSourceAndTarget
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS)) : Prop where
  /-- Étale precomposition preserves the property. -/
  precomp_of_etale :
    ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
      IsEtale B S hS f.hom → P g → P (f ≫ g)
  /-- Smooth base change preserves the property. -/
  pullbackSnd_of_smooth :
    ∀ {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y), P f →
      ∀ (b : Y' ⟶ Y), IsSmooth B S hS b.hom →
        P (ObjectProperty.homMk (pullback.snd f.hom b.hom) :
          AlgebraicSpaces.fiberProduct B S hS f b ⟶ Y')
  /-- The property is equivalent to holding on an étale neighbourhood over a smooth target
  neighbourhood of each source point. -/
  iff_forall_exists_etale_smooth_neighborhood :
    ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
      P f ↔
        ∀ x : points B S hS X.1,
          ∃ (V U : AlgebraicSpaces B S hS)
            (b : V ⟶ Y)
            (e : U ⟶ AlgebraicSpaces.fiberProduct B S hS f b)
            (u : points B S hS U.1),
            IsSmooth B S hS b.hom ∧
              IsEtale B S hS e.hom ∧
              pointsMap B S hS U.1
                (e ≫ (ObjectProperty.homMk (pullback.fst f.hom b.hom) :
                  AlgebraicSpaces.fiberProduct B S hS f b ⟶ X)).hom u = x ∧
              P (e ≫ (ObjectProperty.homMk (pullback.snd f.hom b.hom) :
                AlgebraicSpaces.fiberProduct B S hS f b ⟶ V))

end AlgebraicGeometry.Space

end
