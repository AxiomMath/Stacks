module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCase
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesHomSheafSizeBound

/-!
# The hom-set bijection of Stacks 0AF6

In a formal glueing situation `D` (Stacks 0AEV), write `F` for the restriction functor of
Stacks 0AF3. Stacks 0AF6 says that `F` induces a bijection
`Mor_X(X'₁, X'₂) ⟶ Mor(F X'₁, F X'₂)` whenever `X'₂ ⟶ X` is separated.

The source's proof uses one input beyond the situation: clause (2) of Stacks 0AF4, applied to the
base change of the situation along `X'₁ ×_X X'₂ ⟶ X`. The bijection from that input, for every
situation, is `FormalGlueingSituation.bijective_formalGlueingFunctor_map_of_essSurj`. This module
supplies that input from
`FormalGlueingSituation.isEquivalence_closedGlueingFunctor_of_affineBaseEssSurj`, so the bijection
depends only on `FormalGlueingSituation.AffineBaseEssSurj`, the affine case to which this library
reduces Stacks 0AF4; that is proved, from Stacks 0AF0, as
`FormalGlueingSituation.affineBaseEssSurj`.

## Main results

* `bijective_formalGlueingFunctor_map_of_isSeparated_of_affineBaseEssSurj`: the bijection of
  Stacks 0AF6 from `AffineBaseEssSurj`.
* `bijective_formalGlueingFunctor_map_of_isSeparated`: the restriction functor is bijective on
  morphisms `X'₁ ⟶ X'₂` whenever `X'₂ ⟶ X` is separated.

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
* [Stacks Project, Tag 0AF6](https://stacks.math.columbia.edu/tag/0AF6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The bijection of Stacks 0AF6, from the affine case of Stacks 0AF4.** For `X'₂ ⟶ X`
separated, the restriction functor of Stacks 0AF3 induces a bijection
`Mor_X(X'₁, X'₂) ⟶ Mor(F X'₁, F X'₂)`. Clause (2) of Stacks 0AF4 for every situation, which the
graph argument applies to a base change of `D`, comes from `AffineBaseEssSurj`. -/
theorem bijective_formalGlueingFunctor_map_of_isSeparated_of_affineBaseEssSurj
    (hA : AffineBaseEssSurj B S hS) (D : FormalGlueingSituation B S hS) {X₁ X₂ : spacesOverX D}
    (hsep : IsSeparated B S hS X₂.obj.hom) :
    Function.Bijective fun a : X₁ ⟶ X₂ ↦ (formalGlueingFunctor D).1.map a :=
  bijective_formalGlueingFunctor_map_of_essSurj D
    (fun D' ↦ (isEquivalence_closedGlueingFunctor_of_affineBaseEssSurj hA D').essSurj) hsep

/-- In a formal glueing situation, the functor of Stacks 0AF3 is bijective on
morphisms `X'₁ ⟶ X'₂` of algebraic spaces over `X` whenever `X'₂ ⟶ X` is separated. -/
@[stacks 0AF6]
theorem bijective_formalGlueingFunctor_map_of_isSeparated (D : FormalGlueingSituation B S hS)
    {X₁ X₂ : spacesOverX D} (hsep : IsSeparated B S hS X₂.obj.hom) :
    Function.Bijective fun a : X₁ ⟶ X₂ ↦ (formalGlueingFunctor D).1.map a :=
  bijective_formalGlueingFunctor_map_of_isSeparated_of_affineBaseEssSurj
    (affineBaseEssSurj B S hS) D hsep

end AlgebraicGeometry.Space.FormalGlueingSituation

end
