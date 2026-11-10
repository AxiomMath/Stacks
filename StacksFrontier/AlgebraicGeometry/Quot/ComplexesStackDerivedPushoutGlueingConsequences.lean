module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDerivedPushoutGlueing
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFlatPushoutConsequences

/-!
# Pushout comparison for `Complexes_{X/B}` from the derived pushout statement on the base

Let `D : ComplexesSituation B S hS`. For a pushout square of schemes over `S` along a finite
order thickening `i : Z ⟶ Z'` and an affine morphism `f : Z ⟶ Y`, the comparison functor from the
fibre of `complexesFunctor D` over `Y'` to the fibre product of the fibres over `Z'`, `Y` and `Z`
is an equivalence, provided the base satisfies
`AlgebraicGeometry.Space.DerivedPushoutEssentialImage`. In particular `complexesFunctor D`
satisfies condition (RS) under the same hypothesis.

This is Stacks 0DLK with Stacks 07W3 discharged and Stacks 0DL7 read from its base statement:
the hypothesis `h0DL7` of `isEquivalence_complexesFiberSquareComparison_of_derivedGluing` and
`satisfiesRS_complexesFunctor_of_derivedGluing` is supplied by
`AlgebraicGeometry.Space.exists_glue_of_isPushout_of_derivedPushoutEssentialImage`. The base
proves `DerivedPushoutEssentialImage` (`AlgebraicGeometry.Space.derivedPushoutEssentialImage`);
the hypothesis-free forms are in
`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackPushoutsProved.lean`. Nothing is registered
here.

## Main results

* `isEquivalence_complexesFiberSquareComparison_of_derivedPushoutEssentialImage`: Stacks 0DLK,
  given `AlgebraicGeometry.Space.DerivedPushoutEssentialImage`: the fibre square comparison functor
  of `complexesFunctor D` at a pushout along a finite order thickening and an affine morphism is
  an equivalence.
* `satisfiesRS_complexesFunctor_of_derivedPushoutEssentialImage`: given
  `AlgebraicGeometry.Space.DerivedPushoutEssentialImage`, the functor `complexesFunctor D`
  satisfies condition (RS).

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
* [Stacks Project, Tag 0DLK](https://stacks.math.columbia.edu/tag/0DLK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift

universe u

namespace AlgebraicGeometry.Space.ComplexesSituation

section Pushouts

open AlgebraicGeometry CategoryTheory.Functor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] complexesCategory instModulesHasDerivedCategory

variable (D : ComplexesSituation B S hS)

/-- **Stacks 0DLK, granted the base statement of Stacks 0DL7** (unregistered): given
`DerivedPushoutEssentialImage B S hS`, for a pushout square of schemes over `S` along a finite
order thickening `i` and an affine morphism `f`, the comparison functor from the fibre of
`complexesFunctor D` over `Y'` to the fibre product of the fibres over `Z'`, `Y` and `Z` is an
equivalence. -/
theorem isEquivalence_complexesFiberSquareComparison_of_derivedPushoutEssentialImage
    (h : DerivedPushoutEssentialImage.{u + 1, u + 1, u + 1, u + 1, u} B S hS)
    {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y) (a : Z' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    [_root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hpush : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : (complexesFunctor D).IsFibered := (complexesFunctor_isFiberedInGroupoids D).isFibered
    (Deformation.Artin.fiberSquareComparison (complexesFunctor D)
      (Functor.chosenPullbacks (complexesFunctor D)) f i b a w.symm).IsEquivalence :=
  isEquivalence_complexesFiberSquareComparison_of_derivedGluing D
    (exists_glue_of_isPushout_of_derivedPushoutEssentialImage B S hS h) i f a b w hi hpush

/-- **Condition (RS) for `Complexes_{X/B}`, granted the base statement of Stacks 0DL7**
(unregistered): given `DerivedPushoutEssentialImage B S hS`, the functor `complexesFunctor D`
satisfies condition (RS). -/
theorem satisfiesRS_complexesFunctor_of_derivedPushoutEssentialImage
    (h : DerivedPushoutEssentialImage.{u + 1, u + 1, u + 1, u + 1, u} B S hS) :
    Deformation.Artin.SatisfiesRS B S hS (complexesFunctor D)
      (complexesFunctor_isFiberedInGroupoids D) :=
  satisfiesRS_complexesFunctor_of_derivedGluing D
    (exists_glue_of_isPushout_of_derivedPushoutEssentialImage B S hS h)

end Pushouts

end AlgebraicGeometry.Space.ComplexesSituation

end
