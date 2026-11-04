module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.InverseImage
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap

/-!
# The projection map `Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f^{-1}K)` on `D(X_étale, Λ)`

Let `f : X ⟶ Y` be a morphism of schemes and `Λ` a commutative ring. For `E` in `D(X_étale, Λ)`
and `K` in `D(Y_étale, Λ)` the canonical map of Cohomology on Sites, Section 21.50 ([Stacks,
Tag 0943]),

`Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f^{-1}K)`,

is the adjoint transpose, for `f^{-1} ⊣ Rf_*`, of the comparison
`f^{-1}(Rf_*E ⊗^L_Λ K) ≅ f^{-1}Rf_*E ⊗^L_Λ f^{-1}K` of [Stacks, Tag 07A4] followed by the counit in
the first factor. This file defines it on the unbounded derived categories of sheaves of
`Λ`-modules on the small étale sites, where `f^{-1}` is
`Stacks.EtaleCohomology.etaleModuleDerivedInverseImage`, `Rf_*` is
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded` and `⊗^L_Λ` is
`Stacks.EtaleCohomology.etaleDerivedTensor`.

## Main definitions

* `Stacks.EtaleCohomology.etalePushforwardProjectionMap`: the projection map.

Naturality in both arguments is `CategoryTheory.adjunctionTensorMap_natural`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The projection map** `Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f^{-1}K)` of [Stacks, Tag 0943] on
`D(X_étale, Λ)` and `D(Y_étale, Λ)`: the adjoint transpose, for `f^{-1} ⊣ Rf_*`, of the
comparison of [Stacks, Tag 07A4] followed by the counit in the first factor. -/
def etalePushforwardProjectionMap (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    ((etaleDerivedTensor.{u, r} Λ Y).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj E)).obj K ⟶
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj
        (((etaleDerivedTensor.{u, r} Λ X).obj E).obj
          ((etaleModuleDerivedInverseImage.{u, r} Λ f).obj K)) :=
  adjunctionTensorMap (etaleModuleDerivedInverseImageAdj.{u, r} Λ f)
    (Functor.uncurry.obj (etaleDerivedTensor.{u, r} Λ Y))
    (Functor.uncurry.obj (etaleDerivedTensor.{u, r} Λ X))
    (etaleDerivedInverseImageTensorIso.{u, r} Λ f).hom E K

end Stacks.EtaleCohomology
