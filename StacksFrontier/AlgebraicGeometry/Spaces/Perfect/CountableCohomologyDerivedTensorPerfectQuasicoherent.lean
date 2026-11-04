module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorArbitrary

/-!
# The derived tensor product of a quasi-coherent object with a perfect one

Let `X` be an algebraic space over a scheme `S`, let `K` be an object of `D_QCoh(𝒪_X)` and let
`E` be a perfect object of `D(𝒪_X)` (Stacks 08G5).  Then `K ⊗^𝐋_{𝒪_X} E` again has
quasi-coherent cohomology sheaves.

A perfect object is pseudo-coherent, hence lies in `D_QCoh(𝒪_X)` by Stacks 08JL
(`AlgebraicGeometry.Space.qcohDerived_of_isPerfect`), and `D_QCoh(𝒪_X)` is closed under the
derived tensor product by Stacks 08F5
(`AlgebraicGeometry.Space.derivedQuasicoherent_derivedTensor`).

## Main results

* `AlgebraicGeometry.Space.qcohDerived_derivedTensor_of_isPerfect`.

## References

* [Stacks Project, Tag 08F5](https://stacks.math.columbia.edu/tag/08F5)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The derived tensor product of a quasi-coherent object with a perfect one is
quasi-coherent.**  For `K` in `D_QCoh(𝒪_X)`, `E` a perfect object of `D(𝒪_X)` and any derived
tensor product datum `T` on the small étale ringed site of `X`, the cohomology sheaves of
`K ⊗^𝐋_{𝒪_X} E` are quasi-coherent.

`E` is pseudo-coherent, hence lies in `D_QCoh(𝒪_X)` (Stacks 08JL), and `D_QCoh(𝒪_X)` is closed
under the derived tensor product (Stacks 08F5). -/
theorem qcohDerived_derivedTensor_of_isPerfect (X : AlgebraicSpaces B S hS)
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E) :
    QcohDerived B S hS X ((T.tensor.obj K.obj).obj E) :=
  derivedQuasicoherent_derivedTensor B S hS X.2 T K ⟨E, qcohDerived_of_isPerfect B S hS X E hE⟩

end AlgebraicGeometry.Space

end
