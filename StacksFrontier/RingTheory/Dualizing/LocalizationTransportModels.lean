module

public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange

/-!
# Exact extension of scalars on derived categories, at every model

`Dualizing.totalDerivedExtensionScalarsIsoExtendScalars` at arbitrary models of the two derived
categories.

## Main results

* `Dualizing.totalDerivedExtensionScalarsIsoExtendScalarsOfModels`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)

universe u w w'

namespace Dualizing

variable {B C : Type u} [CommRing B] [CommRing C] (φ : B →+* C)
  [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φ)]

/-- For exact extension of scalars, the total derived functor of degreewise extension of scalars
is the functor induced degreewise: the comparison of
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` is invertible on every
complex, not only on the K-flat ones. This holds at every model of the two derived
categories. -/
@[no_expose] noncomputable def totalDerivedExtensionScalarsIsoExtendScalarsOfModels
    [HasDerivedCategory.{w} (ModuleCat.{u} B)] [HasDerivedCategory.{w'} (ModuleCat.{u} C)] :
    (totalDerivedExtensionScalars.{u, u, u} φ).functor ≅
      (ModuleCat.extendScalars φ).mapDerivedCategory := by
  let F := ModuleCat.extendScalars.{u, u, u} φ
  let D := totalDerivedExtensionScalars.{u, u, u} φ
  have : IsIso D.comparison := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    D.functor D.comparison
    (W := HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)) (by
      intro X Y g hg
      have : QuasiIso g := hg
      change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex _).map g))
      infer_instance)
  exact Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
    (DerivedCategory.Q ⋙ D.functor) (DerivedCategory.Q ⋙ F.mapDerivedCategory) _ _
    (asIso D.comparison ≪≫ F.mapDerivedCategoryFactors.symm)

end Dualizing

end
