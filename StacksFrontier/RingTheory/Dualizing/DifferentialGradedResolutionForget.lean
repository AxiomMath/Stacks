module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorRegularRight
public import StacksFrontier.RingTheory.Dualizing.DifferentialGradedResolutionCompact

/-! # Forgetting the action is derived tensoring with the resolving bimodule

Let `(E, d)` be a differential graded algebra over a commutative ring `R`. The algebra `E`,
viewed as a differential graded `(E, R)`-bimodule through the structure homomorphism
`R → E` — `Dualizing.resolvingBimodule` — computes the forgetful functor
`D(E, d) ⥤ D(R)`: derived tensoring with it, read in the derived category of `R`-modules
through `DifferentialGradedModule.degreeZeroDerivedEquivalence`, is the underlying-complex
functor. This is the tensor half of Stacks 0BYX for the structure homomorphism of `E`, and it
is the input the proof of Stacks 0BZE needs in order to turn the adjunction of Tag 09LT into
the adjunction of the forgetful functor.

## Main definitions

* `DifferentialGradedModule.degreeZeroComponentForgetNatIso`: over the base ring the complex of
  homogeneous components of a differential graded module is its underlying complex of
  `R`-modules, naturally in the module.
* `Dualizing.homotopyRestrictBaseForgetIso` and `Dualizing.derivedRestrictBaseForgetIso`:
  restriction of scalars along `R → E`, read in the derived category of `R`-modules, is the
  forgetful functor, first on the homotopy category and then on the derived category.

## Main results

* `Dualizing.derivedTensorResolvingBimoduleForgetIso`: **the tensor half of Stacks 0BYX for the
  structure homomorphism of `E`** — derived tensoring with the resolving bimodule is the
  forgetful functor `D(E, d) ⥤ D(R)`.
* `Dualizing.DGAResolution.derivedTensorResolvingBimoduleIso`: the same statement read at the
  resolving algebra of Situation 0BZB.

## Implementation notes

The identification is assembled from two halves. Over `R` itself, tensoring with the resolving
bimodule is restriction of scalars along the structure homomorphism — that is
`DifferentialGraded.Bimodule.derivedTensorRegularRightIso`, since the resolving bimodule *is*
the regular `(E, R)`-bimodule of the structure homomorphism. Restriction of scalars along
`R → E` then reads as the underlying complex of `R`-modules, because a differential graded
module over `R` placed in degree zero has the same two underlying complexes: the complex of its
homogeneous components and the complex of `R`-modules it is made of. That is
`DifferentialGradedModule.degreeZeroComponentForgetIso`, whose naturality is the identity in
every degree.

Both identifications are isomorphisms of functors out of `D(E, d)`, which is a localization of
`K(E, d)` at the quasi-isomorphisms, so each is lifted from the homotopy category by
`CategoryTheory.Localization.liftNatIso`; on the homotopy category, in turn, both sides are
quotient lifts, so the comparison is lifted once more by
`CategoryTheory.Quotient.natIsoLift`.

## References

* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX), restriction of scalars
  as tensoring with the regular bimodule.
* [Stacks Project, Tag 0BZB](https://stacks.math.columbia.edu/tag/0BZB), the situation, and
  [Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE), where this identification is used.
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGraded DifferentialGradedModule

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- **Over the base ring the two underlying complexes agree, naturally.** The complex of
homogeneous components of a differential graded module over `R` placed in degree zero is its
underlying complex of `R`-modules, and the identification is natural in the module: in every
degree it is the identity map. -/
def degreeZeroComponentForgetNatIso :
    degreeZeroComponentFunctor R R ≅
      forgetToCochainComplex (DifferentialGradedAlgebra.degreeZero R R) :=
  NatIso.ofComponents degreeZeroComponentForgetIso (by
    intro M N f
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

end DifferentialGradedModule

namespace Dualizing

variable {R : Type u} [CommRing R]

/-- Restriction of scalars along `R → E` followed by taking homogeneous components is the
underlying complex of `R`-modules. -/
def degreeZeroForgetBaseIso (E : DifferentialGradedAlgebra.{u, u} R) :
    restrictScalarsFunctor (baseHom E) ⋙
        degreeZeroComponentFunctor R R ⋙ DerivedCategory.Q ≅
      forgetToCochainComplex E ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft (restrictScalarsFunctor (baseHom E))
    (Functor.isoWhiskerRight degreeZeroComponentForgetNatIso DerivedCategory.Q)

/-- **Restriction of scalars along `R → E` is the underlying complex, on homotopy categories.**
Both sides are lifts through the homotopy quotient of `K(E, d)`, so the comparison is checked on
differential graded modules, where it is the identity in every degree. -/
def homotopyRestrictBaseForgetIso (E : DifferentialGradedAlgebra.{u, u} R) :
    restrictScalarsHomotopyFunctor (baseHom E) ⋙
        ((quasiIsomorphisms' (baseAlgebra R)).Q ⋙
          (degreeZeroDerivedEquivalence (R := R) (A := R)).functor) ≅
      forgetHomotopyToDerivedCategory E :=
  CategoryTheory.Quotient.natIsoLift _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (restrictScalarsHomotopyFunctorIso (baseHom E)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (restrictScalarsFunctor (baseHom E))
        ((Functor.associator _ _ _).symm ≪≫
          degreeZeroDerivedComponentIso (R := R) (A := R)) ≪≫
      degreeZeroForgetBaseIso E ≪≫
      (forgetHomotopyToDerivedCategoryIso E).symm)

/-- **Restriction of scalars along `R → E` is the forgetful functor.** Derived restriction of
scalars along the structure homomorphism, read in the derived category of `R`-modules through
the degree-zero equivalence, is the underlying-complex functor `D(E, d) ⥤ D(R)`. -/
def derivedRestrictBaseForgetIso (E : DifferentialGradedAlgebra.{u, u} R) :
    derivedRestriction (baseHom E) ⋙
        (degreeZeroDerivedEquivalence (R := R) (A := R)).functor ≅ derivedForget E :=
  Localization.liftNatIso (quasiIsomorphisms' E).Q (quasiIsomorphisms' E)
    ((quasiIsomorphisms' E).Q ⋙ (derivedRestriction (baseHom E) ⋙
      (degreeZeroDerivedEquivalence (R := R) (A := R)).functor))
    ((quasiIsomorphisms' E).Q ⋙ derivedForget E)
    (derivedRestriction (baseHom E) ⋙
      (degreeZeroDerivedEquivalence (R := R) (A := R)).functor) (derivedForget E)
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedRestrictionFactorization (baseHom E))
        (degreeZeroDerivedEquivalence (R := R) (A := R)).functor ≪≫
      Functor.associator _ _ _ ≪≫
      homotopyRestrictBaseForgetIso E ≪≫
      (derivedForgetFactorization E).symm)

/-- The resolving bimodule is the regular `(E, R)`-bimodule of the structure homomorphism. -/
theorem resolvingBimodule_eq (E : DifferentialGradedAlgebra.{u, u} R) :
    resolvingBimodule E = Bimodule.regularRight (baseHom E) := rfl

/-- **The tensor half of Stacks 0BYX for the structure homomorphism of `E`.** Derived tensoring
with the resolving bimodule `E`, read in the derived category of `R`-modules through the
degree-zero equivalence, is the forgetful functor `D(E, d) ⥤ D(R)`: forgetting the `E`-action is
restriction of scalars along `R → E`, which is tensoring with the regular `(E, R)`-bimodule. -/
@[stacks 0BYX "forgetting the action is derived tensoring with the regular (E, R)-bimodule"]
def derivedTensorResolvingBimoduleForgetIso (E : DifferentialGradedAlgebra.{u, u} R) :
    Bimodule.derivedTensorFunctor (resolvingBimodule E) ⋙
        (degreeZeroDerivedEquivalence (R := R) (A := R)).functor ≅ derivedForget E :=
  Functor.isoWhiskerRight (Bimodule.derivedTensorRegularRightIso (baseHom E))
      (degreeZeroDerivedEquivalence (R := R) (A := R)).functor ≪≫
    derivedRestrictBaseForgetIso E

namespace DGAResolution

variable {A : Type u} [CommRing A] [Algebra R A]

/-- **The tensor half of Stacks 0BYX at the resolving algebra of Situation 0BZB.** Derived
tensoring with the resolving bimodule of `E`, read in the derived category of `R`-modules, is
the forgetful functor `D(E, d) ⥤ D(R)`. -/
@[stacks 0BYX "forgetting the action of the resolving algebra is derived tensoring with its \
regular (E, R)-bimodule"]
def derivedTensorResolvingBimoduleIso (S : Dualizing.DGAResolution R A) :
    Bimodule.derivedTensorFunctor (Dualizing.resolvingBimodule S.E) ⋙
        (degreeZeroDerivedEquivalence (R := R) (A := R)).functor ≅
      DifferentialGradedModule.derivedForget S.E :=
  derivedTensorResolvingBimoduleForgetIso S.E

end DGAResolution

end Dualizing

end
