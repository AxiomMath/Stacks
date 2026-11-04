module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeBridge
import all StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeBridge

/-!
# Components of the comparison of two models of derived extension of scalars

`Dualizing.tensorBaseChangeMor` — the [stacks 068I] candidate for the lax monoidal structure map
of derived base change — is the component of `Dualizing.tensorBaseChangeNatIso`, which is built
from three factors: the canonical [stacks 068I] comparison
`CochainComplex.DerivedTensor.derivedExtensionScalarsTensorIso`, and two whiskerings of
`Dualizing.extensionModelIso`, the comparison of the given model `F` of derived extension of
scalars with the total derived model `D`.

`Dualizing.extensionModelIso` is `CategoryTheory.Functor.leftDerivedUnique`, an isomorphism
produced by uniqueness of a left derived functor. This file records its characterisation by
`CategoryTheory.Functor.leftDerivedNatTrans_app`.

## Main results

* `Dualizing.extensionModelIso_hom_app_comp_comparison`: the defining identity — on a localized
  complex the comparison carries `comparison` back to `D.comparison`.

## Implementation notes

Wherever `comparison.app X` is invertible — which is at every K-flat complex, by
`CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat` — the identity determines
the component. It is not stated in solved form: `D.comparison` and `comparison` have targets
spelled by `CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral` and by
`CategoryTheory.Functor.mapHomologicalComplex` respectively, which are definitionally but not
syntactically equal, and composing an inverse against the wrong spelling is not type-correct at
`implicit` transparency.

`import all` is used to reach the body of `Dualizing.extensionModelIso`, which is not exposed.
-/

section ExtensionModelComponent

open CategoryTheory StacksDraft.DerivedHom

namespace Dualizing

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
  (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR,
    max uR uA uM, uA} f)

/-- **The defining identity of the comparison of two models of derived extension of scalars.**
On a localized complex `Q X`, the component of `Dualizing.extensionModelIso` followed by the
comparison `comparison` of the model `F` is the comparison `D.comparison` of the total derived
model `D`. -/
public theorem extensionModelIso_hom_app_comp_comparison
    (X : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ) :
    (extensionModelIso.{uR, uA, uM} f F comparison D).hom.app (DerivedCategory.Q.obj X) ≫
        comparison.app X =
      D.comparison.app X :=
  (Functor.leftDerivedNatTrans_app D.functor F D.comparison comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ)) (𝟙 _)
    X).trans (Category.comp_id _)

end Dualizing

end ExtensionModelComponent
