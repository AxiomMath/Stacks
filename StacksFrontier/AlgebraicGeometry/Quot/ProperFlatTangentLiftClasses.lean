module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSquareZeroLiftDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFibreLift

/-!
# The tangent lift classes of `Spaces'_{fp, flat, proper}` are flat deformation classes

For an `A`-module `M` whose trivial square-zero extension lies in the site, the closed immersion
`Spec A ⟶ Spec A[M]` is a square-zero closed immersion
(`AlgebraicGeometry.Space.isSquareZeroClosedImmersion_squareZeroArrow`), so the lift classes
`Deformation.Artin.squareZeroLiftClasses` of an object `x = (X ⟶ Spec A)` of
`Spaces'_{fp, flat, proper}`, out of which the tangent functor of Stacks 07Y9 is built, are the
isomorphism classes of flat deformations of `X ⟶ Spec A` over `Spec A[M]` (Stacks 0D17). This is
the first step of the identification `T_x(M) = Ext¹(L_{X/A}, 𝒪_X ⊗_A M)` of Remark 0D1P.

## Main definitions

* `AlgebraicGeometry.Space.properFlatLiftClassesEquivDeformationClasses`.

## References

* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation.Artin

universe u

namespace AlgebraicGeometry.Space

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}

variable (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)

/-- **The tangent lift classes of `Spaces'_{fp, flat, proper}` over `A[M]` are the isomorphism
classes of flat deformations of `X ⟶ Spec A` over `Spec A[M]`** (Stacks 0D17): the lift
classes of `x` along `Spec A ⊆ Spec A[M]` in the sense of Stacks 07Y9 are the classes of flat
families `X' ⟶ Spec A[M]` with a cartesian square over `Spec A ⊆ Spec A[M]`. -/
def properFlatLiftClassesEquivDeformationClasses (M : SiteModule A B) :
    squareZeroLiftClasses A B S hS toS hA (cartesianProperFlatProjection B S hS) x hx M ≃
      FlatThickeningDeformation.Classes
        (ProperFlatLift.specialMap (squareZeroArrow A B S hS toS hA M)
          (isSquareZeroClosedImmersion_squareZeroArrow A toS hA M) x hx) :=
  ProperFlatLift.liftClassesEquivDeformationClasses _ _ x hx

end AlgebraicGeometry.Space

end
