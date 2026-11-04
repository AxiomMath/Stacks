module

public import StacksFrontier.Algebra.DifferentialGraded.Module.AbsoluteTensorModuleExtTotalNatural
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroBaseForget

/-!
# The change-of-rings tensor complex comparison, over the base ring in degree zero

`DifferentialGraded.absExtTensorRightNatIso` identifies the change-of-rings tensor complex of
Tag 06Y6, built from the complex of `R`-modules underlying a right differential graded
`A₁`-module `L`, with the complex of homogeneous components of `L ⊗_R N`, naturally in `L`. Its
source therefore begins with `DifferentialGradedModule.forgetToCochainComplex A₁`.

The conjugation that carries the differential graded statement of Tag 0BZE to the derived
change-of-rings shape of Tag 06Y6 needs that identification along the *other* half of
`DifferentialGradedModule.degreeZeroEquivalence`, at `A₁ = R` placed in degree zero: the
comparison must be read as an isomorphism of functors of a *cochain complex* of `R`-modules,
precomposed with `DifferentialGradedModule.degreeZeroTotalFunctor R R` rather than postcomposed
with the forgetful functor. The two differ by
`DifferentialGradedModule.degreeZeroTotalForgetSelfIso`, which this file whiskers in.

## Main definitions

* `DifferentialGraded.absExtTensorRightTotalNatIso`: **the change-of-rings tensor complex of a
  cochain complex of `R`-modules is the complex of homogeneous components of its total direct
  sum tensored with `N`**, naturally in the complex.

## References

* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6) is the derived
  change-of-rings tensor product.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct DirectSum

universe u

namespace DifferentialGraded

open DifferentialGradedAlgebra DifferentialGradedModule

variable {R A : Type u} [CommRing R] [CommRing A]

/-- **The change-of-rings tensor complex of Tag 06Y6, read on cochain complexes of
`R`-modules.** For a cochain complex `K` of `R`-modules, the complex `A ⊗_R K ⊗_A N^•` is the
complex of homogeneous components of the absolute tensor product of the differential graded
module `⊕_n K^n` with `N`, naturally in `K`.

This is `DifferentialGraded.absExtTensorRightNatIso` at `A₁ = R` in degree zero, precomposed
with `DifferentialGradedModule.degreeZeroTotalFunctor R R` and simplified by
`DifferentialGradedModule.degreeZeroTotalForgetSelfIso`. It is the isomorphism `e₁` that
`CategoryTheory.LocalizerMorphism.isLeftDerivedFunctor_iff_precomp` asks for along the
quasi-inverse half of `DifferentialGradedModule.degreeZeroEquivalence`. -/
def absExtTensorRightTotalNatIso (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A)),
      degreeZeroTotalFunctor R R ⋙
            absoluteTensorLeftFunctor (A := degreeZero R R) N ⋙
            degreeZeroComponentFunctor R A ≅
        CochainComplex.extendScalarsLarge.{u, u, u} f ⋙
          CochainComplex.tensorRightLarge.{u, u} (degreeZeroComplex N) := by
  letI := f.toAlgebra
  intro N
  exact Functor.isoWhiskerLeft (degreeZeroTotalFunctor R R)
        (absExtTensorRightNatIso f N (degreeZero R R)).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (degreeZeroTotalForgetSelfIso R) _ ≪≫
      Functor.leftUnitor _

end DifferentialGraded

end
