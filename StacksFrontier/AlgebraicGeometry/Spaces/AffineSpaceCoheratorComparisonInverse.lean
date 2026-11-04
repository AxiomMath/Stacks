module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Coherator
import StacksCore.Tactic.StacksAttribute

/-!
# The derived coherator of an affine algebraic space inverts the comparison functor

Let `X` be an affine algebraic space over a scheme `S`.  The comparison functor
`i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is then an equivalence, and the derived
coherator `RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))` of Stacks 08GZ, restricted to the complexes of
`𝒪_X`-modules with quasi-coherent cohomology, is a quasi-inverse of it.

## Main definitions

* `AlgebraicGeometry.Space.derivedCoheratorIsoComparisonInv_of_isAffineSpace`: on an affine
  algebraic space, the restriction of `RQ_X` to `D_QCoh(𝒪_X)` is naturally isomorphic to the
  inverse of `i_X` (Stacks 08H0 (3)).

## References

* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 08F1](https://stacks.math.columbia.edu/tag/08F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
  isClosedUnderKernels_quasicoherentSheaves_schemeUniverse
  isClosedUnderCokernels_quasicoherentSheaves quasicoherentSheaves_abelian_of_closure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 08H0 (3).**  On an affine algebraic space the derived coherator `RQ_X`, restricted
to the complexes of `𝒪_X`-modules with quasi-coherent cohomology, is naturally isomorphic to the
inverse of the comparison functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1. -/
@[stacks 08H0 "part (3)"]
def derivedCoheratorIsoComparisonInv_of_isAffineSpace (hAffine : IsAffineSpace B S hS F) :
    letI := isEquivalence_quasicoherentDerivedComparison_of_isAffineSpace B S hS F hF hAffine
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)))).ι ⋙ derivedCoherator B S hS F hF ≅
      (quasicoherentDerivedComparison B S hS F hF).inv :=
  letI := isEquivalence_quasicoherentDerivedComparison_of_isAffineSpace B S hS F hF hAffine
  derivedCoherator_isoInv B S hS F hF (coherator B S hS F hF) (coheratorAdjunction B S hS F hF)
    (derivedCoherator B S hS F hF) (derivedCoheratorUnit B S hS F hF)

end AlgebraicGeometry.Space

end
