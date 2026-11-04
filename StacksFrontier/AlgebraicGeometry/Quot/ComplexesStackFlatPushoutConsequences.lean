module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityProved
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFlatPushoutProved

/-!
# Stacks 0DLK with Stacks 07W3 discharged

The proof of Stacks 0DLK in the namespace `AlgebraicGeometry.Space`,
`ComplexesSituation.isEquivalence_complexesFiberSquareComparison_of_pushouts`, takes the counit
clause of Stacks 07W3, for pushouts of schemes of the site along a thickening and an affine
morphism, as the hypothesis `h07W3`. That clause is
`AlgebraicGeometry.Space.isPushout_of_isFlat_of_isPushout_schemeSpace`; this file discharges it.
The statements still carry Stacks 0DL7 as the hypothesis `h0DL7`. With Stacks 0DL7 from the base
they are `ComplexesSituation.isEquivalence_complexesFiberSquareComparison_proved` and
`ComplexesSituation.satisfiesRS_complexesFunctor_proved`.

## Main results

* `ComplexesSituation.isEquivalence_complexesFiberSquareComparison_of_derivedGluing` and
  `ComplexesSituation.satisfiesRS_complexesFunctor_of_derivedGluing`: Stacks 0DLK and the
  condition (RS) it gives, granted only Stacks 0DL7.

## References

* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
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

/-- **Stacks 0DLK, granted Stacks 0DL7**:
`ComplexesSituation.isEquivalence_complexesFiberSquareComparison_of_pushouts` with Stacks 07W3
discharged by `AlgebraicGeometry.Space.isPushout_of_isFlat_of_isPushout_schemeSpace`. The
hypothesis `h0DL7` is Stacks 0DL7. -/
theorem isEquivalence_complexesFiberSquareComparison_of_derivedGluing
    (h0DL7 : ∀ {P P' Q Q' : AlgebraicSpaces B S hS} (k : P ⟶ P') (l : P ⟶ Q) (m : P' ⟶ Q')
      (n : Q ⟶ Q') (hsq : IsPushout k l m n),
      IsThickeningHom B S hS k → IsAffineHom B S hS l.hom →
      ∀ (M : derivedModules B S hS Q) (K' : derivedModules B S hS P'),
        IsPseudoCoherentObject M → IsPseudoCoherentObject K' →
        ∀ α : ((smallEtaleDerivedPullbackData B S hS).pull l).obj M ≅
            ((smallEtaleDerivedPullbackData B S hS).pull k).obj K',
          ∃ (N : derivedModules B S hS Q')
            (eQ : ((smallEtaleDerivedPullbackData B S hS).pull n).obj N ≅ M)
            (eP' : ((smallEtaleDerivedPullbackData B S hS).pull m).obj N ≅ K'),
            ((smallEtaleDerivedPullbackData B S hS).pull l).map eQ.hom ≫ α.hom =
              ((smallEtaleDerivedPullbackData B S hS).compIso l n).inv.app N ≫
                eqToHom (congrArg
                  (fun g => ((smallEtaleDerivedPullbackData B S hS).pull g).obj N)
                  hsq.w.symm) ≫
                ((smallEtaleDerivedPullbackData B S hS).compIso k m).hom.app N ≫
                ((smallEtaleDerivedPullbackData B S hS).pull k).map eP'.hom)
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
  isEquivalence_complexesFiberSquareComparison_of_pushouts D
    (isPushout_of_isFlat_of_isPushout_schemeSpace B S hS)
    h0DL7 i f a b w hi hpush

/-- **Condition (RS) for `Complexes_{X/B}`, granted Stacks 0DL7**:
`ComplexesSituation.satisfiesRS_complexesFunctor_of_pushouts` with Stacks 07W3 discharged by
`AlgebraicGeometry.Space.isPushout_of_isFlat_of_isPushout_schemeSpace`. The hypothesis `h0DL7` is
Stacks 0DL7. -/
theorem satisfiesRS_complexesFunctor_of_derivedGluing
    (h0DL7 : ∀ {P P' Q Q' : AlgebraicSpaces B S hS} (k : P ⟶ P') (l : P ⟶ Q) (m : P' ⟶ Q')
      (n : Q ⟶ Q') (hsq : IsPushout k l m n),
      IsThickeningHom B S hS k → IsAffineHom B S hS l.hom →
      ∀ (M : derivedModules B S hS Q) (K' : derivedModules B S hS P'),
        IsPseudoCoherentObject M → IsPseudoCoherentObject K' →
        ∀ α : ((smallEtaleDerivedPullbackData B S hS).pull l).obj M ≅
            ((smallEtaleDerivedPullbackData B S hS).pull k).obj K',
          ∃ (N : derivedModules B S hS Q')
            (eQ : ((smallEtaleDerivedPullbackData B S hS).pull n).obj N ≅ M)
            (eP' : ((smallEtaleDerivedPullbackData B S hS).pull m).obj N ≅ K'),
            ((smallEtaleDerivedPullbackData B S hS).pull l).map eQ.hom ≫ α.hom =
              ((smallEtaleDerivedPullbackData B S hS).compIso l n).inv.app N ≫
                eqToHom (congrArg
                  (fun g => ((smallEtaleDerivedPullbackData B S hS).pull g).obj N)
                  hsq.w.symm) ≫
                ((smallEtaleDerivedPullbackData B S hS).compIso k m).hom.app N ≫
                ((smallEtaleDerivedPullbackData B S hS).pull k).map eP'.hom) :
    Deformation.Artin.SatisfiesRS B S hS (complexesFunctor D)
      (complexesFunctor_isFiberedInGroupoids D) :=
  satisfiesRS_complexesFunctor_of_pushouts D
    (isPushout_of_isFlat_of_isPushout_schemeSpace B S hS)
    h0DL7

end Pushouts

end AlgebraicGeometry.Space.ComplexesSituation

end
