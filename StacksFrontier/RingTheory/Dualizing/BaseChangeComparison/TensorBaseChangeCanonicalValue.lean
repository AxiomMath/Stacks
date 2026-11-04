module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ExtensionModelIsoComponent
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeBridge

/-!
# The [stacks 068I] candidate pinned at a pair of K-flat complexes

`Dualizing.canonicalTensorBaseChangeNatIso` is the monoidality isomorphism of [stacks 068I] read
in the vocabulary of the tensor--Hom bundle of [stacks 0A63], for a total left derived model `D`
of extension of scalars.  It is a composite of three factors: two whiskerings of
`Dualizing.derivedHomAdjunctionTensorNatIsoGeneral`, which compares the
`CochainComplex.DerivedTensor.DerivedTensorProductGeneral` datum [stacks 068I] is stated for with
the [stacks 0A63] bundle, and the [stacks 068I] isomorphism itself.

This file evaluates that composite at a pair of localizations of K-flat complexes, where it is
built only from

* `CochainComplex.DerivedTensor.derivedTensor_comparison`, the K-flat comparison of the
  [stacks 0A63] tensor product with the ordinary total tensor complex;
* the comparison `D.comparison` of the model with degreewise extension of scalars; and
* a chain isomorphism `e` satisfying
  `CochainComplex.DerivedTensor.IsTensorBaseChangeIso`, i.e. the ordinary tensor base-change
  isomorphism `(A ⊗_R K) ⊗_A (A ⊗_R L) ≅ A ⊗_R (K ⊗_R L)` of total complexes.

The identity is stated with the two factors
`D.functor.map (derivedTensor_comparison R K L hL).hom` and `D.comparison.app (K ⊗_R L)` on the
left-hand side, so nothing is inverted.  It nonetheless determines the component, both factors
being invertible: the first because `CochainComplex.DerivedTensor.derivedTensor_comparison` is an
isomorphism, the second by `TotalDerivedExtensionScalars.comparison_isIso_of_kFlat` at the total
tensor complex of two K-flat complexes, which is K-flat by [stacks 0795].

The identification of the [stacks 068I] morphism with the lax monoidal structure map
`Dualizing.derivedTensorBaseChange` is not proved here.  By
`Dualizing.tensorBaseChangeMor_eq_iff_section_comp` and
`Dualizing.tensorBaseChangeMor_eq_of_kFlat` it is the single equation `ν ≫ μ' = 𝟙` at a pair of
localizations of K-flat complexes; this file gives a chain-level value for `μ'` there, and `ν`,
equivalently the component of [stacks 0E1W], remains.
`Dualizing.tensorBaseChangeMor_eq_iff_natIso_inv` is the same identification with only the
**inverse** of the component of [stacks 0E1W] occurring; the inverse of its representative model
comparison is valued with nothing inverted by
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_monoidalIso`, whereas the
hom value `Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_monoidalIso`
contains an inverted [stacks 0A63] transpose.

## Main results

* `Dualizing.derivedHomAdjunctionTensorNatIsoGeneral_hom_app_comp_derivedTensor_comparison` and
  `Dualizing.derivedHomAdjunctionTensorNatIsoGeneral_inv_app_comp_comparison`: the bifunctorial
  comparison of the two derived tensor products carries the K-flat comparison of the
  `CochainComplex.DerivedTensor.DerivedTensorProductGeneral` datum of [stacks 068I] to the K-flat
  comparison `CochainComplex.DerivedTensor.derivedTensor_comparison` of the [stacks 0A63] bundle,
  and back.
* `Dualizing.canonicalTensorBaseChangeNatIso_hom_app_q_obj`: the value of the [stacks 068I]
  candidate at a pair of localizations of K-flat complexes, in the vocabulary of [stacks 0A63].
* `Dualizing.tensorBaseChangeMor_comp_eq_q_obj`: the same for `Dualizing.tensorBaseChangeMor`,
  the candidate at an arbitrary left derived model `F`, expressed in the comparison `comparison`
  of `F` itself.

## Implementation notes

The two spellings of degreewise extension of scalars followed by localization,
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral` (the target of
`D.comparison`) and `CochainComplex.DerivedTensor.extensionOfScalarsCochain` followed by
`DerivedCategory.Q` (what the chain-level data is stated for), are definitionally but not
syntactically equal; the statements below are written in the second spelling.

No `@[stacks]` attribute is placed here: the identification of the [stacks 068I] morphism with the
lax monoidal structure map of derived base change is still open, so nothing in this file covers a
tag.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0795](https://stacks.math.columbia.edu/tag/0795)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

section Bifunctor

universe u v

/-- **The bifunctorial comparison of the two derived tensor products carries the K-flat comparison
of [stacks 068I]'s datum to the K-flat comparison of the [stacks 0A63] bundle.**  At a pair of
K-flat complexes, `Dualizing.derivedHomAdjunctionTensorNatIsoGeneral` followed by
`CochainComplex.DerivedTensor.derivedTensor_comparison` is
`CochainComplex.DerivedTensor.DerivedTensorProductGeneral.comparison`. -/
theorem derivedHomAdjunctionTensorNatIsoGeneral_hom_app_comp_derivedTensor_comparison
    (A : Type u) [CommRing A] (K L : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : IsKFlat.{u, v} K) (hL : IsKFlat.{u, v} L) :
    (derivedHomAdjunctionTensorNatIsoGeneral.{u, v} A).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (derivedTensor_comparison.{u, v} A K L hL).hom =
      ((canonicalDerivedTensorProductGeneral.{u, v} A).comparison K L hK hL).hom := by
  rw [derivedHomAdjunctionTensorNatIsoGeneral_hom_app_kFlat.{u, v} K L hK hL]
  dsimp only [kFlatDerivedTensorIsoGeneral, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The transport of the [stacks 068I] characterization into the vocabulary of [stacks 0A63].**
The inverse of the bifunctorial comparison
`Dualizing.derivedHomAdjunctionTensorNatIsoGeneral`, followed by the K-flat comparison of the
`CochainComplex.DerivedTensor.DerivedTensorProductGeneral` datum that [stacks 068I] is stated
for, is the K-flat comparison
`CochainComplex.DerivedTensor.derivedTensor_comparison` of the [stacks 0A63] bundle. -/
theorem derivedHomAdjunctionTensorNatIsoGeneral_inv_app_comp_comparison
    (A : Type u) [CommRing A] (K L : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hK : IsKFlat.{u, v} K) (hL : IsKFlat.{u, v} L) :
    (derivedHomAdjunctionTensorNatIsoGeneral.{u, v} A).inv.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        ((canonicalDerivedTensorProductGeneral.{u, v} A).comparison K L hK hL).hom =
      (derivedTensor_comparison.{u, v} A K L hL).hom := by
  rw [← derivedHomAdjunctionTensorNatIsoGeneral_hom_app_comp_derivedTensor_comparison.{u, v}
      A K L hK hL, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

end Bifunctor

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA} f)

/-- **The [stacks 068I] candidate at a pair of localizations of K-flat complexes.**  The component
of `Dualizing.canonicalTensorBaseChangeNatIso` at `(Q K, Q L)`, followed by the two invertible
factors that compare `K ⊗ᴸ_R L` with the total tensor complex and its base change with the
degreewise one, is the [stacks 0A63] tensor of the two model comparisons followed by the K-flat
comparison over `A` and a chain isomorphism `e` satisfying
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso`, the ordinary tensor base-change
isomorphism of total complexes. -/
theorem canonicalTensorBaseChangeNatIso_hom_app_q_obj
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
        (canonicalTensorBaseChangeNatIso.{uR, uA, uM} f D).hom.app
              (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
            D.functor.map (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom ≫
            D.comparison.app (tensorComplex.{uR, max uR uA uM} K L) =
          (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                max uR uA uM + 1} A).tensor.map
              ((CategoryTheory.Prod.mkHom (D.comparison.app K) (D.comparison.app L) :
                  ((D.functor.obj (DerivedCategory.Q.obj K),
                      D.functor.obj (DerivedCategory.Q.obj L)) :
                    DerivedCategory (ModuleCat.{max uR uA uM} A) ×
                      DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶
                  (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                      max uR uA uM} f).obj K),
                    DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                      max uR uA uM} f).obj L)))) ≫
            (derivedTensor_comparison.{uA, max uR uA uM} A
                ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
                ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) hFL).hom ≫
            DerivedCategory.Q.map e.hom := by
  obtain ⟨hFK, hFL, e, he, hc⟩ :=
    (derivedExtensionScalarsTensorIso.{uR, uA, max uR uA uM} f
      (canonicalDerivedTensorProductGeneral.{uR, max uR uA uM} R)
      (canonicalDerivedTensorProductGeneral.{uA, max uR uA uM} A) D).comparison K L hK hL
  refine ⟨hFL, e, he, ?_⟩
  have hR := derivedHomAdjunctionTensorNatIsoGeneral_hom_app_comp_derivedTensor_comparison.{uR,
    max uR uA uM} R K L hK hL
  have hAinv := derivedHomAdjunctionTensorNatIsoGeneral_inv_app_comp_comparison.{uA,
    max uR uA uM} A ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
    ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) hFK hFL
  have hnat : (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uA, max uR uA uM,
            max uR uA uM + 1} A).tensor.map
          ((CategoryTheory.Prod.mkHom (D.comparison.app K) (D.comparison.app L) :
            ((D.functor.obj (DerivedCategory.Q.obj K),
                D.functor.obj (DerivedCategory.Q.obj L)) :
              DerivedCategory (ModuleCat.{max uR uA uM} A) ×
                DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶
            (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                max uR uA uM} f).obj K),
              DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                max uR uA uM} f).obj L)))) ≫
        (derivedHomAdjunctionTensorNatIsoGeneral.{uA, max uR uA uM} A).inv.app
          (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K),
            DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L)) =
      (derivedHomAdjunctionTensorNatIsoGeneral.{uA, max uR uA uM} A).inv.app
            (D.functor.obj (DerivedCategory.Q.obj K),
              D.functor.obj (DerivedCategory.Q.obj L)) ≫
          ((canonicalDerivedTensorProductGeneral.{uA, max uR uA uM} A).tensor.map
              (D.comparison.app K)).app (D.functor.obj (DerivedCategory.Q.obj L)) ≫
            ((canonicalDerivedTensorProductGeneral.{uA, max uR uA uM} A).tensor.obj
                (DerivedCategory.Q.obj
                  ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K))).map
              (D.comparison.app L) :=
    (derivedHomAdjunctionTensorNatIsoGeneral.{uA, max uR uA uM} A).inv.naturality _
  dsimp only [canonicalTensorBaseChangeNatIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  dsimp only [Functor.prod_obj]
  simp only [Category.assoc]
  rw [← D.functor.map_comp_assoc, hR, ← hc, ← reassoc_of% hAinv, reassoc_of% hnat]
  exact (Eq.trans (Category.assoc _ _ _)
    (congrArg (fun z => _ ≫ z) (Category.assoc _ _ _))).symm

variable (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **The [stacks 068I] candidate for an arbitrary left derived model, at a pair of localizations
of K-flat complexes.**  The candidate `Dualizing.tensorBaseChangeMor` at `(Q K, Q L)`, followed by
the two invertible factors comparing `K ⊗ᴸ_R L` with the total tensor complex and its base change
with the degreewise one, is the [stacks 0A63] tensor of two components of `comparison`, followed by
the K-flat comparison of [stacks 0A63] over `A` and the ordinary tensor base-change isomorphism of
total complexes. -/
theorem tensorBaseChangeMor_comp_eq_q_obj
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
              (DerivedCategory.Q.obj L) ≫
            F.map (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom ≫
            comparison.app (tensorComplex.{uR, max uR uA uM} K L) =
          (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uA, max uR uA uM,
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
            DerivedCategory.Q.map e.hom := by
  obtain ⟨hFL, e, he, hcan⟩ :=
    canonicalTensorBaseChangeNatIso_hom_app_q_obj.{uR, uA, uM} f D K L hK hL
  refine ⟨hFL, e, he, ?_⟩
  have hinv : ∀ X : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ,
      (extensionModelIso.{uR, uA, uM} f F comparison D).inv.app (DerivedCategory.Q.obj X) ≫
        D.comparison.app X = comparison.app X := fun X => by
    rw [← extensionModelIso_hom_app_comp_comparison.{uR, uA, uM} f F comparison D X]
    exact Iso.inv_hom_id_app_assoc _ _ _
  have key : (canonicalTensorBaseChangeNatIso.{uR, uA, uM} f D).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        D.functor.map (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom ≫
          (extensionModelIso.{uR, uA, uM} f F comparison D).hom.app
            (DerivedCategory.Q.obj (tensorComplex.{uR, max uR uA uM} K L)) ≫
            comparison.app (tensorComplex.{uR, max uR uA uM} K L) =
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uA, max uR uA uM,
            max uR uA uM + 1} A).tensor.map
          ((CategoryTheory.Prod.mkHom (D.comparison.app K) (D.comparison.app L) :
              ((D.functor.obj (DerivedCategory.Q.obj K),
                  D.functor.obj (DerivedCategory.Q.obj L)) :
                DerivedCategory (ModuleCat.{max uR uA uM} A) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶
              (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                  max uR uA uM} f).obj K),
                DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                  max uR uA uM} f).obj L)))) ≫
        (derivedTensor_comparison.{uA, max uR uA uM} A
            ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
            ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) hFL).hom ≫
          DerivedCategory.Q.map e.hom := by
    rw [extensionModelIso_hom_app_comp_comparison.{uR, uA, uM} f F comparison D
      (tensorComplex.{uR, max uR uA uM} K L)]
    exact hcan
  have hpair : (NatIso.prod (extensionModelIso.{uR, uA, uM} f F comparison D)
            (extensionModelIso.{uR, uA, uM} f F comparison D)).inv.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (CategoryTheory.Prod.mkHom (D.comparison.app K) (D.comparison.app L) :
          ((D.functor.obj (DerivedCategory.Q.obj K),
              D.functor.obj (DerivedCategory.Q.obj L)) :
            DerivedCategory (ModuleCat.{max uR uA uM} A) ×
              DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶
          (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K),
            DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
              max uR uA uM} f).obj L))) =
      (CategoryTheory.Prod.mkHom (comparison.app K) (comparison.app L) :
        ((F.obj (DerivedCategory.Q.obj K), F.obj (DerivedCategory.Q.obj L)) :
          DerivedCategory (ModuleCat.{max uR uA uM} A) ×
            DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶
        (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K),
          DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
            max uR uA uM} f).obj L))) :=
    congrArg₂ Prod.mk (hinv K) (hinv L)
  dsimp only [tensorBaseChangeMor, tensorBaseChangeNatIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  rw [← reassoc_of% ((extensionModelIso.{uR, uA, uM} f F comparison D).hom.naturality
      (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom), key]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
      (derivedTensor_comparison.{uA, max uR uA uM} A
          ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
          ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) hFL).hom ≫
        DerivedCategory.Q.map e.hom)
    (Functor.map_comp _ _ _).symm) ?_
  exact congrArg (fun z => (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uA, max uR uA uM,
        max uR uA uM + 1} A).tensor.map z ≫
      (derivedTensor_comparison.{uA, max uR uA uM} A
          ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
          ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) hFL).hom ≫
        DerivedCategory.Q.map e.hom) hpair

end Dualizing

end
