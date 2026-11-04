module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.CartesianFiniteOrderMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Morphisms

/-!
# Relative dimension across a cartesian morphism of finite-order thickenings

Let

```
X --f--→ Y
|        |
↓        ↓
X' -f'-→ Y'
```

be a commutative square of algebraic spaces over a scheme `S` in which `X ⊂ X'` and `Y ⊂ Y'`
are thickenings, the thickening `Y ⊂ Y'` is of finite order, and the square identifies `X` with
`Y ×_{Y'} X'`; that is, let it be a
`AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings`. This file records part (4)
of Stacks 09ZZ for that situation: `f` is locally of finite type of relative dimension `d`
exactly when `f'` is.

Being locally of finite type of relative dimension `d` is a conjunction of two conditions, and
the statement below is the conjunction: local finite type, and relative dimension `d` at every
point of the source. The first conjunct is part (2) of Stacks 09ZZ, already available as
`AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.isLocallyOfFiniteType_iff`.

The second conjunct needs no finite-order input beyond that. Relative dimension is a pointwise
condition, the square is cartesian, and `f` is the base change of `f'` along the thickening
`Y ⊂ Y'`, so the invariance of relative dimension under base change, part (1) of Stacks 04NS,
compares the relative dimension of `f` at a point `x` of `X` with that of `f'` at the image of
`x` in `X'`. A thickening is a bijection on points, so quantifying over the points of `X` and
quantifying over the points of `X'` give the same condition.

## Main results

In the namespace
`AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings`:

* `hasRelativeDimension_iff_of_isLocallyOfFiniteType`: relative dimension `d` transfers in both
  directions once the ambient morphism is known to be locally of finite type.
* `isLocallyOfFiniteType_and_hasRelativeDimension_iff`: part (4) of Stacks 09ZZ.

## Implementation notes

**The finite-order hypothesis is on the target thickening `Y ⊂ Y'`, not on the source
`X ⊂ X'`.** This is the convention of the frame file
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/CartesianFiniteOrderMorphism.lean`, whose
implementation notes explain it: the tag's text puts finite order on the source, but the lemma
it reduces to, Stacks 09ZW, puts it on the target, and the tag's own proof argues by induction
on the order of the thickening `Y ⊂ Y'`. In the presence of the cartesian square target finite
order implies source finite order, by Stacks 09ZX, but not conversely, so the statement below
is weaker than the tag's text announces. The clause string of the theorem says so.

The relative-dimension half does not go through the engine
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderMorphismOfThickenings`
of the frame file, and so does not need the relative-dimension clause of Stacks 09ZW for
morphisms of schemes, which the library does not have. It goes instead through
`AlgebraicGeometry.Space.hasRelativeDimensionAt_iff_of_isPullback`, part (1) of Stacks 04NS,
applied at each point of `X`, and transports the quantifier along
`AlgebraicGeometry.Space.bijective_pointsMap_ι_of_isThickening`. Only surjectivity of that map
on points is used; injectivity is not needed, since the statement being transported is a
universally quantified one.

Note the argument order of `AlgebraicGeometry.Space.HasRelativeDimension`: the dimension comes
first, before the site data, so the condition is written `HasRelativeDimension d B S hS f`.
Its dimension argument is a natural number, while that of
`AlgebraicGeometry.Space.HasRelativeDimensionAt` is in `ℕ∞`, and the unfolding of the former
inserts the coercion.

## References

* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
* [Stacks Project, Tag 09ZW](https://stacks.math.columbia.edu/tag/09ZW)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 09ZZ](https://stacks.math.columbia.edu/tag/09ZZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace CartesianFiniteOrderMorphismOfThickenings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- In a cartesian morphism of thickenings of algebraic spaces whose ambient morphism `f'` is
locally of finite type, `f` has relative dimension `d` exactly when `f'` does.

Each point of `X'` is the image of a point of `X`, because the inclusion of a thickening is
surjective on points, and at corresponding points the two relative dimensions agree by the
invariance of relative dimension under base change, part (1) of Stacks 04NS, applied to the
cartesian square. No finite-order hypothesis is used here. -/
theorem hasRelativeDimension_iff_of_isLocallyOfFiniteType
    (M : CartesianFiniteOrderMorphismOfThickenings B S hS) (d : ℕ)
    (hf' : IsLocallyOfFiniteType B S hS M.f') :
    HasRelativeDimension d B S hS M.f ↔ HasRelativeDimension d B S hS M.f' := by
  have key (x : points B S hS M.X.toFunctor) :
      HasRelativeDimensionAt (d : ℕ∞) B S hS M.f'
          (pointsMap B S hS M.X.toFunctor M.X.ι x) ↔
        HasRelativeDimensionAt (d : ℕ∞) B S hS M.f x :=
    hasRelativeDimensionAt_iff_of_isPullback B S hS M.cartesian.flip M.X'.property
      M.targetThickening.1.1 M.Y'.property hf' x (d : ℕ∞)
  refine ⟨fun h y => ?_, fun h x => (key x).mp (h _)⟩
  obtain ⟨x, rfl⟩ := (bijective_pointsMap_ι_of_isThickening B S hS M.sourceThickening).2 y
  exact (key x).mpr (h x)

/-- **Stacks 09ZZ, part (4).** Being locally of finite type of relative dimension `d` is
invariant under a cartesian morphism of thickenings of algebraic spaces whose target thickening
is of finite order: the map between the smaller spaces is locally of finite type of relative
dimension `d` exactly when the map between the ambient spaces is.

The property is the conjunction of local finite type and relative dimension `d`, and the
statement is that conjunction. Its first half is part (2) of the same tag.

The hypothesis is the finite order of the target thickening `Y ⊂ Y'`, which is stronger than
the finite order of the source thickening `X ⊂ X'` that the tag's text states; see the
implementation notes of this file. -/
@[stacks 09ZZ "part (4), locally of finite type of relative dimension d, stated as the \
conjunction of local finite type and relative dimension d which is what that property means; \
the finite-order hypothesis is on the TARGET thickening Y ⊆ Y', which is strictly stronger \
than the source hypothesis X ⊆ X' in the tag's text, so this is a weaker theorem than the \
tag announces. It is the hypothesis the tag's own proof uses: it reduces to Tag 09ZW, which \
puts finite order on the target, and says 'by induction on the order of the thickening we may \
assume that Y ⊆ Y' is a first order thickening'. Cartesianness plus target finite order gives \
source finite order by Tag 09ZX, but not conversely"]
theorem isLocallyOfFiniteType_and_hasRelativeDimension_iff
    (M : CartesianFiniteOrderMorphismOfThickenings B S hS) (d : ℕ) :
    (IsLocallyOfFiniteType B S hS M.f ∧ HasRelativeDimension d B S hS M.f) ↔
      (IsLocallyOfFiniteType B S hS M.f' ∧ HasRelativeDimension d B S hS M.f') :=
  (and_congr_left' M.isLocallyOfFiniteType_iff).trans
    (and_congr_right (M.hasRelativeDimension_iff_of_isLocallyOfFiniteType d))

end CartesianFiniteOrderMorphismOfThickenings

end AlgebraicGeometry.Space

end
