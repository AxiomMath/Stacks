module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDerivedPushoutGlueingConsequences
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DerivedPushoutGlueingRepresentedAffine

/-!
# Stacks 0DLK for `Complexes_{X/B}`

In Situation 0DLE, let `Y' = Y ⨿_Z Z'` be a pushout of schemes over `S` along a finite order
thickening `Z ⟶ Z'` and an affine morphism `Z ⟶ Y`. Then the functor on fibre categories
`Complexes_{X/B, Y'} ⟶ Complexes_{X/B, Y} ×_{Complexes_{X/B, Z}} Complexes_{X/B, Z'}` is an
equivalence.

The proof is the source's, from Stacks 07W3 and 0DL7.
`ComplexesSituation.isEquivalence_complexesFiberSquareComparison_of_derivedPushoutEssentialImage`
proves the statement from Stacks 07W3 at schemes of the site
(`AlgebraicGeometry.Space.isPushout_of_isFlat_of_isPushout_schemeSpace`) and the statement of
Stacks 0DL7 on the base, `AlgebraicGeometry.Space.DerivedPushoutEssentialImage`. The base proves
that statement (`AlgebraicGeometry.Space.derivedPushoutEssentialImage`), so here no hypothesis
is left.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isEquivalence_complexesFiberSquareComparison_proved`:
  Stacks 0DLK.
* `AlgebraicGeometry.Space.ComplexesSituation.satisfiesRS_complexesFunctor_proved`: the condition
  (RS) that Stacks 0DLK gives for `Complexes_{X/B}`.

## References

* [Stacks Project, Tag 0DLK](https://stacks.math.columbia.edu/tag/0DLK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation.Artin

universe u

namespace AlgebraicGeometry.Space.ComplexesSituation

open AlgebraicGeometry CategoryTheory.Functor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] complexesCategory instModulesHasDerivedCategory

variable (D : ComplexesSituation B S hS)

/-- **Stacks 0DLK.** In Situation 0DLE, let `i ≫ a = f ≫ b` be a commutative square of the site
whose image in schemes is a pushout `Y' = Y ⨿_Z Z'` along the finite order thickening
`i : Z ⟶ Z'` and the affine morphism `f : Z ⟶ Y`. Then the functor on fibre categories
`Complexes_{X/B, Y'} ⟶ Complexes_{X/B, Y} ×_{Complexes_{X/B, Z}} Complexes_{X/B, Z'}` is an
equivalence.

This is
`isEquivalence_complexesFiberSquareComparison_of_derivedPushoutEssentialImage`
with Stacks 0DL7 given by the base's `AlgebraicGeometry.Space.derivedPushoutEssentialImage`. -/
theorem isEquivalence_complexesFiberSquareComparison_proved
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
  isEquivalence_complexesFiberSquareComparison_of_derivedPushoutEssentialImage D
    (derivedPushoutEssentialImage.{u + 1, u + 1, u + 1, u + 1, u} B S hS) i f a b w hi hpush

/-- **Condition (RS) for `Complexes_{X/B}`**, the form in which Stacks 0DLK enters
Artin's criterion (unregistered):
`satisfiesRS_complexesFunctor_of_derivedPushoutEssentialImage`
with Stacks 0DL7 given by the base's `AlgebraicGeometry.Space.derivedPushoutEssentialImage`. -/
theorem satisfiesRS_complexesFunctor_proved :
    Deformation.Artin.SatisfiesRS B S hS (complexesFunctor D)
      (complexesFunctor_isFiberedInGroupoids D) :=
  satisfiesRS_complexesFunctor_of_derivedPushoutEssentialImage D
    (derivedPushoutEssentialImage.{u + 1, u + 1, u + 1, u + 1, u} B S hS)

end AlgebraicGeometry.Space.ComplexesSituation

end
