module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ExtensionModelIsoComponent

/-!
# The inverse component of the model comparison against the degreewise comparison

`Dualizing.extensionModelIso` compares an arbitrary left derived model `F` of extension of
scalars with the total derived model `D` that [stacks 068I] is stated for, and
`Dualizing.extensionModelIso_hom_app_comp_comparison` says that its forward component at the
class of a complex carries the degreewise comparison of `F` to that of `D`.

Every consumer that meets the comparison of `D` and wants the comparison of `F` needs the
statement in the other direction -- the *inverse* component followed by `D`'s comparison is `F`'s
comparison -- and it has been re-derived as a proof-local `have` wherever it was needed.  This
file states it once.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  This is a bookkeeping identity.

## Main results

* `Dualizing.extensionModelIso_inv_app_comp_comparison` -- the inverse component of the model
  comparison followed by the degreewise comparison of the total derived model is the degreewise
  comparison of the model itself.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **The inverse component of the model comparison against the degreewise comparison.**

`Dualizing.extensionModelIso_hom_app_comp_comparison` read with the component moved across: the
inverse component of `Dualizing.extensionModelIso` at the class of a complex, followed by the
degreewise comparison of the total derived model, is the degreewise comparison of `F`.

This is the direction a consumer holding the comparison of the total derived model needs, and it
is what lets the total derived model disappear from a value of the [stacks 068I] candidate. -/
theorem extensionModelIso_inv_app_comp_comparison
    (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
      max uR uA uM + 1} f)
    (K : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ) :
    (extensionModelIso.{uR, uA, uM} f F comparison D).inv.app
          (DerivedCategory.Q.obj K) ≫ D.comparison.app K =
      comparison.app K := by
  rw [← extensionModelIso_hom_app_comp_comparison.{uR, uA, uM} f F comparison D K]
  exact Iso.inv_hom_id_app_assoc _ _ _

end Dualizing

end
