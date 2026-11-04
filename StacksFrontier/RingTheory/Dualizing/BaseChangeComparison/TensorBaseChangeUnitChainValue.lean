module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.RestrictScalarsDerivedLax
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorCovariantKFlatLift

/-!
# The keystone at a K-flat pair, with the [stacks 068I] candidate replaced by its value

`Dualizing.eq_derivedTensorBaseChange_iff_unit_monoidal` says that the [stacks 068I] candidate
`μ'` agrees with the lax monoidal structure map `Dualizing.derivedTensorBaseChange` of derived base
change if and only if the unit `η` of [stacks 0GMT] is monoidal for `μ'` and the lax structure
`Dualizing.restrictScalarsDerivedLaxTensor` of derived restriction of scalars.  In that equation
`μ'` still occurs as the opaque component of the transported monoidality isomorphism of
[stacks 068I].

`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` evaluates that component at a pair of localizations
of K-flat complexes, but only after postcomposition with the two invertible factors that identify
`F (Q K ⊗ᴸ_R Q L)` with the class of `A ⊗_R (K ⊗_R L)`.  Those two factors are exactly the `hom` of
`Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso`, so the evaluation can be solved for `μ'`
itself.  This file does that, and substitutes the result into the keystone.

What comes out is the keystone at a K-flat pair as one equation of morphisms
`Q K ⊗ᴸ_R Q L ⟶ Res_f (F (Q K ⊗ᴸ_R Q L))` in `D(R)` whose factors are, in order: the unit of
[stacks 0GMT] in both variables; the lax monoidal structure map of derived restriction of scalars;
the [stacks 0A63] tensor of two components of the model comparison `comparison`; the K-flat
description `CochainComplex.DerivedTensor.derivedTensor_comparison` of the [stacks 0A63] tensor
product over `A`; the ordinary tensor base-change isomorphism `e` of total complexes, pinned
summand by summand by `CochainComplex.DerivedTensor.IsTensorBaseChangeIso`; and the K-flat
description of `F (Q K ⊗ᴸ_R Q L)`.  Every one of those but the lax structure map is a localized
chain map or a localization comparison.  So the only object of the keystone that is still not
chain-level is the lax monoidal structure map of restriction of scalars, i.e. the inverse component
of [stacks 0E1W], and `Dualizing.restrictScalarsDerivedProjection_eq_evaluation` is the hook
through which its computed values enter.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is that the other
hypothesis, at a K-flat pair, no longer mentions the transported monoidality isomorphism of
[stacks 068I], only the ordinary tensor base-change isomorphism of total complexes.

## Main results

* `Dualizing.tensorBaseChangeMor_eq_q_obj` -- **the value of the [stacks 068I] candidate** at a
  pair of localizations of K-flat complexes, with nothing postcomposed:
  `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` solved for the candidate across
  `Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso`.
* `Dualizing.tensorBaseChangeMor_eq_iff_unit_chain_value` -- **the keystone at a K-flat pair with
  that value substituted**: the identification holds if and only if the unit of [stacks 0GMT] is
  monoidal for the lax structure of restriction of scalars and the chain-level value.

## Implementation notes

The hypothesis `hK` enters only through
`Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso`, whose invertibility needs the total
tensor complex of `K` and `L` to be K-flat; `hL` enters there and in
`CochainComplex.DerivedTensor.derivedTensor_comparison` over `R`.  Neither is used by
`Dualizing.eq_derivedTensorBaseChange_iff_unit_monoidal`, which holds at arbitrary objects.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
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
/-- **The value of the [stacks 068I] candidate at a pair of localizations of K-flat complexes.**

`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` gives the value of `μ'` composed with
`F (derivedTensor_comparison)` and `comparison` at the total tensor complex; those two factors are
the `hom` of `Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso`, which is invertible, so the
equation solves for `μ'`.

The result: `μ'` at `(Q K, Q L)` is the [stacks 0A63] tensor over `A` of the two components of the
model comparison, then the K-flat description of the [stacks 0A63] tensor product over `A`, then
the ordinary tensor base-change isomorphism `e` of total complexes, then the inverse of the K-flat
description of `F (Q K ⊗ᴸ_R Q L)`.  Nothing in it is a derived-functor lift or an adjoint
transpose, and the total derived model `D` of [stacks 068I] does not occur. -/
theorem tensorBaseChangeMor_eq_q_obj
    (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
      max uR uA uM + 1} f)
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    ∃ (hFL : IsKFlat.{uA, max uR uA uM}
          ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L))
        (e : tensorComplex.{uA, max uR uA uM}
            ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
            ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) ≅
          (extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
            (tensorComplex.{uR, max uR uA uM} K L)),
      IsTensorBaseChangeIso.{uR, uA, max uR uA uM} f K L e ∧
        tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
            (DerivedCategory.Q.obj L) =
          (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.map
              ((CategoryTheory.Prod.mkHom (comparison.app K) (comparison.app L) :
                ((F.obj (DerivedCategory.Q.obj K), F.obj (DerivedCategory.Q.obj L)) :
                    DerivedCategory (ModuleCat.{max uR uA uM} A) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶
                  (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                      max uR uA uM} f).obj K),
                    DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                      max uR uA uM} f).obj L)))) ≫
            (derivedTensor_comparison.{uA, max uR uA uM} A
                ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
                ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) hFL).hom ≫
              DerivedCategory.Q.map e.hom ≫
                (_root_.Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso.{uR, uA, uM} f F
                  comparison K L hK hL).inv := by
  obtain ⟨hFL, e, he, hcan⟩ :=
    tensorBaseChangeMor_comp_eq_q_obj.{uR, uA, uM} f D F comparison K L hK hL
  refine ⟨hFL, e, he, ?_⟩
  refine Eq.trans ((Iso.eq_comp_inv
    (_root_.Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso.{uR, uA, uM} f F
      comparison K L hK hL)).mpr hcan) ?_
  exact Eq.trans (Category.assoc _ _ _)
    (congrArg (fun z =>
      (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.map
        ((CategoryTheory.Prod.mkHom (comparison.app K) (comparison.app L) :
          ((F.obj (DerivedCategory.Q.obj K), F.obj (DerivedCategory.Q.obj L)) :
              DerivedCategory (ModuleCat.{max uR uA uM} A) ×
                DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶
            (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                max uR uA uM} f).obj K),
              DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                max uR uA uM} f).obj L)))) ≫ z) (Category.assoc _ _ _))

include hF in
/-- **The keystone at a K-flat pair, with the [stacks 068I] candidate replaced by its chain-level
value.**

`Dualizing.eq_derivedTensorBaseChange_iff_unit_monoidal` at the [stacks 068I] candidate, with the
candidate rewritten by `Dualizing.tensorBaseChangeMor_eq_q_obj`.  So the identification of the
[stacks 068I] candidate with the lax monoidal structure map of derived base change at a pair of
localizations of K-flat complexes holds if and only if one equation of morphisms out of
`Q K ⊗ᴸ_R Q L` holds, in which the transported monoidality isomorphism of [stacks 068I] has been
replaced by the ordinary tensor base-change isomorphism of total complexes and the only remaining
non-chain-level factor is the lax monoidal structure map
`Dualizing.restrictScalarsDerivedLaxTensor` of derived restriction of scalars. -/
theorem tensorBaseChangeMor_eq_iff_unit_chain_value
    (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
      max uR uA uM + 1} f)
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L) :
    ∃ (hFL : IsKFlat.{uA, max uR uA uM}
          ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L))
        (e : tensorComplex.{uA, max uR uA uM}
            ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
            ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) ≅
          (extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
            (tensorComplex.{uR, max uR uA uM} K L)),
      IsTensorBaseChangeIso.{uR, uA, max uR uA uM} f K L e ∧
        (tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
              (DerivedCategory.Q.obj L) =
            derivedTensorBaseChange.{uR, uA, uM} f F comparison (DerivedCategory.Q.obj K)
              (DerivedCategory.Q.obj L) ↔
          (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
                (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
                      (DerivedCategory.Q.obj K),
                    (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
                      (DerivedCategory.Q.obj L)) :
                  ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :
                      DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                        DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
                    ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                        (F.obj (DerivedCategory.Q.obj K)),
                      (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                        (F.obj (DerivedCategory.Q.obj L)))) ≫
              restrictScalarsDerivedLaxTensor.{uR, uA, uM} f F comparison
                  (F.obj (DerivedCategory.Q.obj K)) (F.obj (DerivedCategory.Q.obj L)) ≫
                (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
                  ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                        max uR uA uM + 1} A).tensor.map
                      ((CategoryTheory.Prod.mkHom (comparison.app K) (comparison.app L) :
                        ((F.obj (DerivedCategory.Q.obj K), F.obj (DerivedCategory.Q.obj L)) :
                            DerivedCategory (ModuleCat.{max uR uA uM} A) ×
                              DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶
                          (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                              max uR uA uM} f).obj K),
                            DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                              max uR uA uM} f).obj L)))) ≫
                    (derivedTensor_comparison.{uA, max uR uA uM} A
                        ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
                        ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) hFL).hom ≫
                      DerivedCategory.Q.map e.hom ≫
                        (_root_.Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso.{uR, uA,
                          uM} f F comparison K L hK hL).inv) =
            (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
              ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                max uR uA uM + 1} R).tensor.obj (DerivedCategory.Q.obj K,
                  DerivedCategory.Q.obj L))) := by
  obtain ⟨hFL, e, he, hv⟩ :=
    tensorBaseChangeMor_eq_q_obj.{uR, uA, uM} f F comparison D K L hK hL
  refine ⟨hFL, e, he, Iff.trans
    (eq_derivedTensorBaseChange_iff_unit_monoidal.{uR, uA, uM} f F comparison
      (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) _) (Eq.congr ?_ rfl)⟩
  exact congrArg (fun z =>
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
          (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
                (DerivedCategory.Q.obj K),
              (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
                (DerivedCategory.Q.obj L)) :
            ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :
                DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
              ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                  (F.obj (DerivedCategory.Q.obj K)),
                (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                  (F.obj (DerivedCategory.Q.obj L)))) ≫
        restrictScalarsDerivedLaxTensor.{uR, uA, uM} f F comparison
            (F.obj (DerivedCategory.Q.obj K)) (F.obj (DerivedCategory.Q.obj L)) ≫
          (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map z) hv

end Dualizing

end
