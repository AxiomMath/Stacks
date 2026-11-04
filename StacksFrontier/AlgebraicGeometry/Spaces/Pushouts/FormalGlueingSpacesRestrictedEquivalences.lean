module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCase
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesHomSheafSizeBound

/-!
# Stacks 0AF4: the three restrictions of the functor of Stacks 0AF3 are equivalences

In a formal glueing situation `(f : Y ⟶ X, Z, U, V)` (Stacks 0AEV), the functor of Stacks 0AF3
sending an algebraic space `X'` over `X` to the glueing triple `(U ×_X X' ⟵ V ×_X X' ⟶ Y ×_X X')`
restricts to three equivalences:

1. from algebraic spaces affine over `X` to triples whose three maps `U' ⟶ U`, `V' ⟶ V`,
   `Y' ⟶ Y` are affine;
2. from closed immersions into `X` to triples whose three maps are closed immersions;
3. from algebraic spaces finite over `X` to triples whose three maps are finite.

The source subcategories are `AlgebraicGeometry.Space.FormalGlueingSituation.affineOverX`,
`closedOverX` and `finiteOverX`, the target subcategories `affineLegs`, `closedLegs` and
`finiteLegs` (all full subcategories, cut out by exactly the conditions of the tag), and the
functors `affineGlueingFunctor`, `closedGlueingFunctor` and `finiteGlueingFunctor` are the
restrictions of `formalGlueingFunctor` (Stacks 0AF3) to them.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.affineGlueingFunctor_isEquivalence`,
  `closedGlueingFunctor_isEquivalence` and `finiteGlueingFunctor_isEquivalence`: the three
  parts of Stacks 0AF4.

The input over an affine base is
`AlgebraicGeometry.Space.FormalGlueingSituation.affineBaseEssSurj` (proved from Stacks 0AF0);
the globalization is that of `FormalGlueingSpacesHomSheafSizeBound`.

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
* [Stacks Project, Tag 0AF3](https://stacks.math.columbia.edu/tag/0AF3)
* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0AF4, part (1).**  The functor of Stacks 0AF3 is an equivalence from algebraic
spaces affine over `X` onto glueing triples whose maps `U' ⟶ U`, `V' ⟶ V` and `Y' ⟶ Y` are
affine. -/
@[stacks 0AF4 "part (1)"]
theorem affineGlueingFunctor_isEquivalence (D : FormalGlueingSituation B S hS) :
    (affineGlueingFunctor D).IsEquivalence :=
  isEquivalence_affineGlueingFunctor_of_affineBaseEssSurj (affineBaseEssSurj B S hS) D

/-- **Stacks 0AF4, part (2).**  The functor of Stacks 0AF3 is an equivalence from closed
immersions into `X` onto glueing triples whose three maps are closed immersions. -/
@[stacks 0AF4 "part (2)"]
theorem closedGlueingFunctor_isEquivalence (D : FormalGlueingSituation B S hS) :
    (closedGlueingFunctor D).IsEquivalence :=
  isEquivalence_closedGlueingFunctor_of_affineBaseEssSurj (affineBaseEssSurj B S hS) D

/-- **Stacks 0AF4, part (3).**  The functor of Stacks 0AF3 is an equivalence from algebraic
spaces finite over `X` onto glueing triples whose three maps are finite. -/
@[stacks 0AF4 "part (3)"]
theorem finiteGlueingFunctor_isEquivalence (D : FormalGlueingSituation B S hS) :
    (finiteGlueingFunctor D).IsEquivalence :=
  isEquivalence_finiteGlueingFunctor_of_affineBaseEssSurj (affineBaseEssSurj B S hS) D

end AlgebraicGeometry.Space.FormalGlueingSituation
