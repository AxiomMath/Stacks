module

public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsResolution
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorCovariantKFlatLift

/-!
# The unit of [stacks 0GMT] at a derived tensor product of K-flat classes

`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat`
pins the unit of [stacks 0GMT] only at `DerivedCategory.Q` of a K-flat complex.  The right-hand
side of the [stacks 068I] identification carries the unit at the [stacks 0A63] derived tensor
product `Q K ⊗ᴸ_R Q L`, which is not of that form -- it is not presented as a localization at all.

`…_unit_app_eq_of_model` removes the restriction, at the price of a presentation `φ` of the object
as a localization of a K-flat complex.  At a K-flat pair the presentation is available and
canonical: `CochainComplex.DerivedTensor.derivedTensor_comparison` identifies
`Q K ⊗ᴸ_R Q L` with `Q (K ⊗_R L)`, needing only the *second* complex to be K-flat, and
`Stacks.DerivedHom.BaseChange.kFlat_tensorComplex` says the total tensor complex `K ⊗_R L` is
itself K-flat in the spelling the model comparison asks for.  So the unit is pinned there, with
no hypothesis beyond K-flatness of the two complexes.

**What is not done here.**  Nothing is registered and no caveat is lifted.  This values one of the
two sides of the equation that `Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftTranspose` reduces
the [stacks 068I] identification to; the identification itself stays open, as does the companion
hypothesis `h` of `Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor`, whose frontier
is `Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.

## Main results

* `Stacks.DerivedHom.BaseChange.derivedExtensionScalarsAdjunction_unit_app_tensor_kFlat` -- the
  unit of [stacks 0GMT] at `Q K ⊗ᴸ_R Q L` for a K-flat pair: the canonical tensor comparison,
  then the degreewise unit of the extension--restriction adjunction on cochain complexes read
  through `CategoryTheory.Functor.mapDerivedCategoryFactors` and back along the model comparison,
  then the restriction of `F` applied to the inverse comparison.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Stacks.DerivedHom.BaseChange

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **The unit of [stacks 0GMT] at a derived tensor product of K-flat classes.**

For K-flat complexes `K` and `L`, the unit of [stacks 0GMT] at the derived tensor product
`Q K ⊗ᴸ_R Q L` of [stacks 0A63] is the canonical tensor comparison
`CochainComplex.DerivedTensor.derivedTensor_comparison`, then the degreewise unit of the
extension--restriction adjunction on cochain complexes read through
`CategoryTheory.Functor.mapDerivedCategoryFactors` and back along the model comparison, then the
restriction of `F` applied to the inverse tensor comparison. -/
public theorem derivedExtensionScalarsAdjunction_unit_app_tensor_kFlat
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    letI : IsIso (comparison.app (tensorComplex.{uR, max uR uA uM} K L)) :=
      isIso_comparison_app_of_kFlat.{uR, uA, uM} f F comparison
        (tensorComplex.{uR, max uR uA uM} K L)
        (kFlat_tensorComplex.{uR, uA, uM} K L hK hL)
    (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
        ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) =
      (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom ≫
        (DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app (tensorComplex.{uR, max uR uA uM} K L)) ≫
          (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategoryFactors.inv.app
              (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj (tensorComplex.{uR, max uR uA uM} K L)) ≫
            (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
              (inv (comparison.app (tensorComplex.{uR, max uR uA uM} K L)))) ≫
        (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
          (F.map (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).inv) :=
  derivedExtensionScalarsAdjunction_unit_app_eq_of_model.{uR, uA, uM} f F comparison
    ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max uR uA uM,
        max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))
    (tensorComplex.{uR, max uR uA uM} K L) (kFlat_tensorComplex.{uR, uA, uM} K L hK hL)
    (derivedTensor_comparison.{uR, max uR uA uM} R K L hL)

end Stacks.DerivedHom.BaseChange

end
