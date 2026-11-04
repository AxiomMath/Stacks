module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction
public import StacksFrontier.RingTheory.Dualizing.DifferentialGradedResolutionForget

/-!
# Derived extension of scalars to a differential graded algebra

Let `(E, d)` be a differential graded algebra over a commutative ring `R`. Derived tensoring
with the regular bimodule of the structure homomorphism `R → E`, read on `D(R)` through the
degree-zero equivalence, is a functor `- ⊗_R^𝐋 E : D(R) ⥤ D(E, d)`, and it is left adjoint to
the forgetful functor `D(E, d) ⥤ D(R)`. This is the second functor of Situation 0BZB, built
rather than assumed: the second diagram of Situation 0BZB and Stacks 0BZE are stated for an
arbitrary left adjoint of the forgetful functor, and this module supplies one.

## Main definitions

* `Dualizing.derivedExtensionToDGA`: the functor `- ⊗_R^𝐋 E : D(R) ⥤ D(E, d)`, derived
  extension of scalars along the structure homomorphism `R → E`.

## Main results

* `Dualizing.derivedExtensionToDGA_adj`: **Stacks 0BYX** for the structure homomorphism of `E`,
  read on `D(R)` — derived extension of scalars `- ⊗_R^𝐋 E` is left adjoint to the forgetful
  functor `D(E, d) ⥤ D(R)`.
* `Dualizing.DGAResolution.derivedExtensionToDGA_comp_iso`: **the second diagram of Situation
  0BZB**, with no assumed functor: derived extension of scalars to the resolving algebra
  followed by the horizontal equivalence `- ⊗_E^𝐋 A` is derived extension of scalars
  `- ⊗_R^𝐋 A : D(R) ⥤ D(A)`.

## Implementation notes

The adjunction is the composite of two: the degree-zero equivalence
`DifferentialGradedModule.degreeZeroDerivedEquivalence`, which identifies `D(R)` with the
derived category of differential graded modules over `R` placed in degree zero, and the
adjunction of Tag 0BYX, `DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction`,
between derived extension and derived restriction of scalars along
`Dualizing.baseHom E : R → E`. Its right adjoint is derived restriction of scalars read on
`D(R)`, which is the forgetful functor by `Dualizing.derivedRestrictBaseForgetIso`.

The base ring and the differential graded algebra live in a single universe, which is the
encoding of the differential graded chapter in this tree (Tag 09JJ):
`DifferentialGradedModule.degreeZeroDerivedEquivalence` is available only at module universe
equal to ring universe. The derived category of `R`-modules is taken at the standard model,
which is the model `Dualizing.derivedRestrictBaseForgetIso` and Situation 0BZB use.

## References

* [Stacks Project, Tag 0BZB](https://stacks.math.columbia.edu/tag/0BZB), the situation, whose
  second diagram this module states with the functor `- ⊗_R^𝐋 E` constructed.
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX), Example 22.33.2, the
  adjunction between extension and restriction of scalars.
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGraded DifferentialGradedModule

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Dualizing

variable {R : Type u} [CommRing R]

/-- **Derived extension of scalars to a differential graded algebra**, `- ⊗_R^𝐋 E`. A complex of
`R`-modules is read as a differential graded module over `R` placed in degree zero, by
`DifferentialGradedModule.degreeZeroDerivedEquivalence`, and then tensored with the regular
bimodule of the structure homomorphism `R → E`. This is the functor `- ⊗_R^𝐋 E : D(R) ⥤ D(E, d)`
of Situation 0BZB. -/
def derivedExtensionToDGA (E : DifferentialGradedAlgebra.{u, u} R) :
    DerivedCategory (ModuleCat.{u} R) ⥤ derivedCategory' E :=
  (degreeZeroDerivedEquivalence (R := R) (A := R)).inverse ⋙
    Bimodule.derivedTensorFunctor (Bimodule.regular (baseHom E))

/-- **Stacks 0BYX for the structure homomorphism of `E`, read on `D(R)`.** Derived extension of
scalars `- ⊗_R^𝐋 E : D(R) ⥤ D(E, d)` is left adjoint to the forgetful functor
`D(E, d) ⥤ D(R)`.

The adjunction of Tag 0BYX is between derived extension and derived restriction of scalars along
`R → E`; transporting its right adjoint along `Dualizing.derivedRestrictBaseForgetIso`, which
identifies derived restriction read on `D(R)` with the forgetful functor, gives the statement in
the form Situation 0BZB uses. -/
@[stacks 0BYX "extension of scalars along R -> E is left adjoint to forgetting the action"]
def derivedExtensionToDGA_adj (E : DifferentialGradedAlgebra.{u, u} R) :
    derivedExtensionToDGA E ⊣ derivedForget E :=
  Adjunction.ofNatIsoRight
    ((degreeZeroDerivedEquivalence (R := R) (A := R)).symm.toAdjunction.comp
      (Bimodule.derivedTensorFunctor_adj_derivedRestriction (baseHom E)))
    (derivedRestrictBaseForgetIso E)

namespace DGAResolution

variable {A : Type u} [CommRing A] [Algebra R A]

/-- **The second diagram of Situation 0BZB commutes, with no assumed functor.** Derived
extension of scalars `- ⊗_R^𝐋 E : D(R) ⥤ D(E, d)` followed by the horizontal equivalence
`- ⊗_E^𝐋 A : D(E, d) ⥤ D(A)` is derived extension of scalars `- ⊗_R^𝐋 A : D(R) ⥤ D(A)`.

This is `Dualizing.DGAResolution.derivedExtension_comp_iso` with its parameters `F` and `adjF`
discharged by `Dualizing.derivedExtensionToDGA` and `Dualizing.derivedExtensionToDGA_adj`. -/
@[stacks 0BZB "extension triangle, with the functor constructed"]
def derivedExtensionToDGA_comp_iso (S : Dualizing.DGAResolution R A) :
    derivedExtensionToDGA S.E ⋙ S.derivedEquivalence.functor ≅
      Dualizing.DGAResolution.ordinaryExtension (R := R) (A := A) :=
  S.derivedExtension_comp_iso (derivedExtensionToDGA S.E) (derivedExtensionToDGA_adj S.E)

end DGAResolution

end Dualizing

end
