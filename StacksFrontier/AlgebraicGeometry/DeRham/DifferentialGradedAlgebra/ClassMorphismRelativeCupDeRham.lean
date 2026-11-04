module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassMorphismRelativeCup
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.RelativeCupProduct
import StacksCore.Tactic.StacksAttribute

/-!
# The morphism `ξ' : Ω^• ⟶ Ω^•[n]` and the relative cup product of Remark 0FU6

Property (5) of Remark 0FU7, for the relative de Rham complex: for a morphism of ringed spaces
`f : (X, A) ⟶ (Y, 𝒪_Y)` (for a commutative square of schemes as in Remark 0FU6, the morphism
`AlgebraicGeometry.Scheme.squareHom`), the square

`Rf_*Ω^• ⊗^𝐋 Rf_*Ω^• --μ--> Rf_*Ω^•`, `Rf_*Ω^•[n] ⊗^𝐋 Rf_*Ω^• --μ--> Rf_*Ω^•[n]`

with vertical maps `Rf_*ξ' ⊗ 1` and `Rf_*ξ'` commutes in `D(Y)`. The top `μ` is the relative cup
product `AlgebraicGeometry.SheafOfModules.deRhamRelativeCupProduct` of Remark 0FU6; the bottom
one is the relative cup product followed by `Rf_*` of the multiplication of the right differential
graded module `Ω^•[n]` (Section 0FU3's `μ_{M[n]}`).

## Main results

* `AlgebraicGeometry.SheafOfModules.deRhamRelativeCupProduct_deRhamClassMorphism`.

## References

* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Tag 0FU6](https://stacks.math.columbia.edu/tag/0FU6)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf
attribute [local implicit_reducible] structureSheafRing

open CategoryTheory Opposite TopologicalSpace
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B) {Y : RingedSpace.{u, u}} (F : baseRingedSpace A ⟶ Y)

/-- The relative cup product of Remark 0FU6 is the relative cup product followed by `Rf_*` of the
derived action of the regular module `Ω^•`. -/
theorem deRhamRelativeCupProduct_eq_derivedAction :
    Eq (deRhamRelativeCupProduct B D F)
      (Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct F
          (DerivedCategory.Q.obj
            (deRhamDifferentialGradedAlgebra (X := X) (A := A) (φ := φ) B D).complex)
          (DerivedCategory.Q.obj
            (deRhamDifferentialGradedAlgebra (X := X) (A := A) (φ := φ) B D).complex) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward F).map
          (derivedAction (S := baseRingedSpace A)
            (deRhamDifferentialGradedAlgebra (X := X) (A := A) (φ := φ) B D)
            (_root_.SheafOfModules.DifferentialGradedModule.regularModule
              (deRhamDifferentialGradedAlgebra (X := X) (A := A) (φ := φ) B D)))) := by
  have h := dgAction_regular_deRham B D
  exact (congrArg (fun t => Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct F
      (DerivedCategory.Q.obj
        (deRhamDifferentialGradedAlgebra (X := X) (A := A) (φ := φ) B D).complex)
      (DerivedCategory.Q.obj
        (deRhamDifferentialGradedAlgebra (X := X) (A := A) (φ := φ) B D).complex) ≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward F).map
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans (baseRingedSpace A)).app
        ((deRhamDifferentialGradedAlgebra (X := X) (A := A) (φ := φ) B D).complex,
          (deRhamDifferentialGradedAlgebra (X := X) (A := A) (φ := φ) B D).complex) ≫
        DerivedCategory.Q.map t)) h).symm

/-- **Stacks Project, Tag 0FU7, property (5).** For a morphism of ringed spaces
`f : (X, A) ⟶ (Y, 𝒪_Y)` (for a commutative square of schemes as in Remark 0FU6 this is
`AlgebraicGeometry.Scheme.squareHom`, with `A = p⁻¹𝒪_S` and `𝒪_Y` replaced by `q⁻¹𝒪_T`) and
`ξ ∈ H^n_{dR}`, the square

`Rf_*Ω^• ⊗^𝐋 Rf_*Ω^• --μ--> Rf_*Ω^•`, `Rf_*Ω^•[n] ⊗^𝐋 Rf_*Ω^• --μ--> Rf_*Ω^•[n]`

with vertical maps `Rf_*ξ' ⊗ 1` and `Rf_*ξ'` commutes in `D(Y)`. The top `μ` is the relative cup
product `deRhamRelativeCupProduct` of Remark 0FU6; the bottom `μ` is the relative cup product
followed by `Rf_*` of the multiplication `derivedShiftedMul` of the right differential graded
module `Ω^•[n]`. -/
@[stacks 0FU7 "property (5): compatibility with the relative cup product of Remark 0FU6"]
theorem deRhamRelativeCupProduct_deRhamClassMorphism (n : ℤ) (ξ : deRhamCohomology B D n) :
    Eq ((Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward F).map
          (deRhamClassMorphism B D n ξ) ×ₘ
          𝟙 ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward F).obj
            (DerivedCategory.Q.obj
              (deRhamDifferentialGradedAlgebra (X := X) (A := A) (φ := φ) B D).complex))) ≫
        Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct F
          ((DerivedCategory.Q.obj
            (deRhamDifferentialGradedAlgebra (X := X) (A := A) (φ := φ) B D).complex)⟦n⟧)
          (DerivedCategory.Q.obj
            (deRhamDifferentialGradedAlgebra (X := X) (A := A) (φ := φ) B D).complex) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward F).map
          (derivedShiftedMul (S := baseRingedSpace A)
            (deRhamDifferentialGradedAlgebra (X := X) (A := A) (φ := φ) B D) n))
      (deRhamRelativeCupProduct B D F ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward F).map
          (deRhamClassMorphism B D n ξ)) :=
  (relativeCupProduct_comp_of_derivedAction (S := baseRingedSpace A)
    (deRhamDifferentialGradedAlgebra (X := X) (A := A) (φ := φ) B D) F n
    (deRhamClassMorphism B D n ξ)
    (derivedForgetShiftedHom_derivedAction (S := baseRingedSpace A)
      (deRhamDifferentialGradedAlgebra (X := X) (A := A) (φ := φ) B D) n
      (deRhamClassDerivedEquiv B D n ξ))).trans
    (congrArg (· ≫ _) (deRhamRelativeCupProduct_eq_derivedAction B D F).symm)

end AlgebraicGeometry.SheafOfModules
