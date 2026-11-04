module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoheratorQuasiInverse
import StacksCore.Tactic.StacksAttribute

/-!
# The derived coherator is a quasi-inverse of the comparison on an affine algebraic space

Let `X` be an affine algebraic space over a scheme `S` contained in a big fppf site `B`. The
comparison functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is an equivalence, and a
derived coherator `RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))`, restricted to `D_QCoh(𝒪_X)`, is a
quasi-inverse of it (Stacks 08H0 (3)).

## Main definitions

* `AlgebraicGeometry.Space.derivedCoherator_isoInv_of_isAffineSpace`: for any coherator `C_X`
  with its adjunction `ι ⊣ C_X` and any total right derived functor `RQ_X` of `C_X`, the
  restriction of `RQ_X` to `D_QCoh(𝒪_X)` is naturally isomorphic to the inverse of `i_X`.

## Implementation notes

The coherator (Stacks 077V (2)) and its total right derived functor are determined only up to
canonical isomorphism, so the statement is over arbitrary such data: a coherator `CF` with its
adjunction `adjF`, and a functor `RQ` with a unit `RQUnit` exhibiting it as a right derived
functor of `CF`. The derived categories are the standard models, and the closure of
quasi-coherent modules under kernels and cokernels (Stacks 03M1) is installed as local instances
(`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_schemeUniverse` and
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`).

## References

* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 08F1](https://stacks.math.columbia.edu/tag/08F1)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
* [Stacks Project, Tag 08D9](https://stacks.math.columbia.edu/tag/08D9)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] isClosedUnderKernels_quasicoherentSheaves_schemeUniverse
  isClosedUnderCokernels_quasicoherentSheaves

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (CF : Modules.{u, u} B S hS F hF ⥤ QuasicoherentSheaves.{u, u} B S hS F hF)
    (adjF : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι ⊣ CF)
    [CF.Additive]
    (RQ : DerivedCategory (Modules.{u, u} B S hS F hF) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS F hF))
    (RQUnit : CF.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS F hF) ⟶
      DerivedCategory.Q (C := Modules.{u, u} B S hS F hF) ⋙ RQ)
    [RQ.IsRightDerivedFunctor RQUnit
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ))]

/-- **Stacks 08H0 (3).**  Let `X` be an affine algebraic space over a scheme `S`, let `C_X` be a
coherator of `X` and let `RQ_X` be a total right derived functor of `C_X`.  Then `RQ_X`,
restricted to the complexes of `𝒪_X`-modules with quasi-coherent cohomology, is a quasi-inverse
of the comparison functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1: it is naturally
isomorphic to the inverse of `i_X`, which is an equivalence because `X` is affine. -/
def derivedCoherator_isoInv_of_isAffineSpace (hAffine : IsAffineSpace B S hS F) :
    letI := isEquivalence_quasicoherentDerivedComparison_of_isAffineSpace B S hS F hF hAffine
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)))).ι ⋙ RQ ≅
      (quasicoherentDerivedComparison B S hS F hF).inv :=
  letI := isEquivalence_quasicoherentDerivedComparison_of_isAffineSpace B S hS F hF hAffine
  derivedCoherator_isoInv B S hS F hF CF adjF RQ RQUnit

end AlgebraicGeometry.Space

end
