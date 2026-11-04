module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Morphism properties of the projections of a pullback of schemes over a base

The image of the canonical pullback square of `Over S` under `Over.forget S` is again a pullback
square, and therefore each projection of a fibre product in `Over S` inherits, on underlying
schemes, every property stable under base change from the opposite leg.

## Main results

* `AlgebraicGeometry.overFibreProduct_isPullback`: the underlying square of a fibre product in
  `Over S` is cartesian.
* `AlgebraicGeometry.overFibreProduct_fst` and `AlgebraicGeometry.overFibreProduct_snd`:
  a property stable under base change transfers to the projections.
* `AlgebraicGeometry.overFibreProduct_comp`: a property stable under composition transfers to
  a composite in `Over S`.

## References

* [Stacks Project, Tag 04MP](https://stacks.math.columbia.edu/tag/04MP)
* [Stacks Project, Tag 04MV](https://stacks.math.columbia.edu/tag/04MV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The underlying square of schemes of the canonical fibre product square in `Over S` is
cartesian. -/
public theorem overFibreProduct_isPullback {S : Scheme.{u}} {A B C : Over S}
    (f : A ⟶ C) (g : B ⟶ C) [HasPullback f g] :
    IsPullback (pullback.fst f g).left (pullback.snd f g).left f.left g.left := by
  simpa only [Over.forget_map] using (IsPullback.of_hasPullback f g).map (Over.forget S)

/-- The second projection of a fibre product in `Over S` has every property of morphisms of
schemes which is stable under base change and holds for the opposite leg. -/
public theorem overFibreProduct_snd {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {S : Scheme.{u}} {A B C : Over S}
    (f : A ⟶ C) (g : B ⟶ C) [HasPullback f g] (hf : P f.left) :
    P (pullback.snd f g).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (overFibreProduct_isPullback f g) hf

/-- The first projection of a fibre product in `Over S` has every property of morphisms of
schemes which is stable under base change and holds for the opposite leg. -/
public theorem overFibreProduct_fst {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {S : Scheme.{u}} {A B C : Over S}
    (f : A ⟶ C) (g : B ⟶ C) [HasPullback f g] (hg : P g.left) :
    P (pullback.fst f g).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (overFibreProduct_isPullback f g).flip hg

/-- A composite in `Over S` has, on underlying schemes, every property of morphisms of schemes
which is stable under composition and holds for both factors. -/
public theorem overFibreProduct_comp {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderComposition] {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : P f.left) (hg : P g.left) : P (f ≫ g).left := by
  rw [Over.comp_left]
  exact P.comp_mem f.left g.left hf hg

end AlgebraicGeometry
