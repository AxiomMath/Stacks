module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatTensorComplexGeneral

/-!
# Stacks 07A4 commutes with the shift

Let `f` be a morphism of ringed topoi. For a fixed `L`, the isomorphism
`Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L` of Stacks 07A4 is an isomorphism of functors of `K`; it
commutes with the shift in `K` for the canonical derived tensor products. The proof checks this
on K-flat complexes with flat terms, where the isomorphism is a composite of comparisons each of
which commutes with the shift.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorModelLeftNatIso` and
  `derivedPullbackTensorModelRightFstNatIso`, `derivedPullbackTensorModelRightSndNatIso`: the
  two halves of the isomorphism on models, as isomorphisms commuting with the shift.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorFlipObjIso_commShift`:
  Stacks 07A4 with the second variable fixed commutes with the shift in the first, for the
  canonical derived tensor products.

## Implementation notes

The statements comparing the canonical derived tensor product with
`Stacks.SheafOfModules.derivedTensorBifunctor` unfold it.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat hasResolutions_isKFlat)
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)

universe c u d c'

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

open AlgebraicGeometry.RingedToposHom Stacks.SheafOfModules

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

/- The construction behind `Stacks.SheafOfModules.canonicalDerivedTensorProduct`, which is
opaque (`irreducible_def`); the computations below are made with it. -/
local notation "exactTensorProduct" Z:max => derivedTensorProductOfExact Z
  (derivedTensorBifunctor_commShift₂Int Z) (derivedTensorBifunctor_isTriangulated_flipObj Z)
  (derivedTensorBifunctor_isTriangulated_obj Z)

variable {X : RingedTopos.{u, c, u}} {Y : RingedTopos.{u, c', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

/-- The first half of Stacks 07A4 on models, as an isomorphism of functors of a K-flat
complex `P` with flat terms: `Lf^*(Q P ⊗^L Q N) ≅ Q f^*Tot(P ⊗ N)`. -/
def derivedPullbackTensorModelLeftNatIso
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) :
    ((flatKFlatComplexes Y).ι ⋙ DerivedCategory.Q) ⋙
        (((derivedTensorBifunctor Y.toRingedSite).flip.obj (DerivedCategory.Q.obj N)) ⋙
        (derivedPullback f)) ≅
      ((flatKFlatComplexes Y).ι ⋙
          ((Tensor.sheafTensor.{c', u, u, u, u} Y.O).map₂CochainComplex.flip.obj N)) ⋙
          ((pullbackComplex f) ⋙ DerivedCategory.Q) :=
  (Functor.associator ((flatKFlatComplexes Y).ι ⋙ DerivedCategory.Q)
      ((derivedTensorBifunctor Y.toRingedSite).flip.obj (DerivedCategory.Q.obj N))
      (derivedPullback f)).symm ≪≫
    Functor.isoWhiskerRight
        (Functor.associator (flatKFlatComplexes Y).ι DerivedCategory.Q
        ((derivedTensorBifunctor Y.toRingedSite).flip.obj (DerivedCategory.Q.obj N)))
        (derivedPullback f) ≪≫
    Functor.isoWhiskerRight
        (kFlatComparisonFlipIsoOf (X := Y.toRingedSite) (flatKFlatComplexes Y).ι
        (fun (P : (flatKFlatComplexes Y).FullSubcategory) => P.2.1) N) (derivedPullback f) ≪≫
    Functor.isoWhiskerRight
        (Functor.associator (flatKFlatComplexes Y).ι
        ((Tensor.sheafTensor.{c', u, u, u, u} Y.O).map₂CochainComplex.flip.obj N)
        DerivedCategory.Q).symm (derivedPullback f) ≪≫
    (Functor.associator ((flatKFlatComplexes Y).ι ⋙
        ((Tensor.sheafTensor.{c', u, u, u, u} Y.O).map₂CochainComplex.flip.obj N)) DerivedCategory.Q
        (derivedPullback f)) ≪≫
    flatPullbackNatIsoOf f
        ((flatKFlatComplexes Y).ι ⋙
        ((Tensor.sheafTensor.{c', u, u, u, u} Y.O).map₂CochainComplex.flip.obj N))
      (fun (P : (flatKFlatComplexes Y).FullSubcategory) => ⟨kFlat_mapBifunctor (X := Y) P.2.1 hN.1,
        isFlat_mapBifunctor_X (X := Y) _ _ P.2.2 hN.2⟩)

/-- The forward map of `derivedPullbackTensorModelLeftNatIso` is the composite of the forward maps
of its constituent isomorphisms. -/
theorem derivedPullbackTensorModelLeftNatIso_hom_eq
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) :
    (derivedPullbackTensorModelLeftNatIso f N hN).hom =
      ((Functor.associator ((flatKFlatComplexes Y).ι ⋙ DerivedCategory.Q)
          ((derivedTensorBifunctor Y.toRingedSite).flip.obj (DerivedCategory.Q.obj N))
          (derivedPullback f)).inv ≫
    Functor.whiskerRight
        (Functor.associator (flatKFlatComplexes Y).ι DerivedCategory.Q
        ((derivedTensorBifunctor Y.toRingedSite).flip.obj (DerivedCategory.Q.obj N))).hom
        (derivedPullback f) ≫
    Functor.whiskerRight
        (kFlatComparisonFlipIsoOf (X := Y.toRingedSite) (flatKFlatComplexes Y).ι
        (fun (P : (flatKFlatComplexes Y).FullSubcategory) => P.2.1) N).hom (derivedPullback f) ≫
    Functor.whiskerRight
        (Functor.associator (flatKFlatComplexes Y).ι
        ((Tensor.sheafTensor.{c', u, u, u, u} Y.O).map₂CochainComplex.flip.obj N)
        DerivedCategory.Q).inv (derivedPullback f) ≫
    (Functor.associator ((flatKFlatComplexes Y).ι ⋙
        ((Tensor.sheafTensor.{c', u, u, u, u} Y.O).map₂CochainComplex.flip.obj N)) DerivedCategory.Q
        (derivedPullback f)).hom ≫
    (flatPullbackNatIsoOf f
        ((flatKFlatComplexes Y).ι ⋙
        ((Tensor.sheafTensor.{c', u, u, u, u} Y.O).map₂CochainComplex.flip.obj N))
      (fun (P : (flatKFlatComplexes Y).FullSubcategory) => ⟨kFlat_mapBifunctor (X := Y) P.2.1 hN.1,
        isFlat_mapBifunctor_X (X := Y) _ _ P.2.2 hN.2⟩)).hom) := rfl

/-- `derivedPullbackTensorModelLeftNatIso` commutes with the shift. -/
theorem derivedPullbackTensorModelLeftNatIso_commShift
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) :
    letI := derivedTensorBifunctor_commShift₂Int Y.toRingedSite
    NatTrans.CommShift (derivedPullbackTensorModelLeftNatIso f N hN).hom ℤ := by
  let := derivedTensorBifunctor_commShift₂Int Y.toRingedSite
  have h2 : NatTrans.CommShift
      (Functor.whiskerRight
      (kFlatComparisonFlipIsoOf (X := Y.toRingedSite) (flatKFlatComplexes Y).ι
      (fun (P : (flatKFlatComplexes Y).FullSubcategory) => P.2.1) N).hom (derivedPullback f)) ℤ :=
    @NatTrans.CommShift.whiskerRight _ _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ _
        (kFlatComparisonFlipIsoOf_commShift (X := Y.toRingedSite) (flatKFlatComplexes Y).ι
        (fun (P : (flatKFlatComplexes Y).FullSubcategory) => P.2.1) N)
  rw [derivedPullbackTensorModelLeftNatIso_hom_eq]
  infer_instance

/-- The first part of the second half of Stacks 07A4 on models, as an isomorphism of
functors of a K-flat complex `P` with flat terms: `Lf^*(Q P) ⊗^L Lf^*(Q N) ≅ Q f^*P ⊗^L Q f^*N`. -/
def derivedPullbackTensorModelRightFstNatIso
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) :
    ((flatKFlatComplexes Y).ι ⋙ DerivedCategory.Q) ⋙
        ((derivedPullback f) ⋙
        ((derivedTensorBifunctor X.toRingedSite).flip.obj
        ((derivedPullback f).obj (DerivedCategory.Q.obj N)))) ≅
      ((flatKFlatComplexes Y).ι ⋙ (pullbackComplex f)) ⋙
          (DerivedCategory.Q ⋙
          ((derivedTensorBifunctor X.toRingedSite).flip.obj
          (DerivedCategory.Q.obj ((pullbackComplex f).obj N)))) :=
  (Functor.associator ((flatKFlatComplexes Y).ι ⋙ DerivedCategory.Q) (derivedPullback f)
      ((derivedTensorBifunctor X.toRingedSite).flip.obj
      ((derivedPullback f).obj (DerivedCategory.Q.obj N)))).symm ≪≫
    Functor.isoWhiskerRight
        (Functor.associator (flatKFlatComplexes Y).ι DerivedCategory.Q (derivedPullback f))
        ((derivedTensorBifunctor X.toRingedSite).flip.obj
        ((derivedPullback f).obj (DerivedCategory.Q.obj N))) ≪≫
    Functor.isoWhiskerRight
        (flatPullbackNatIsoOf f (flatKFlatComplexes Y).ι
        (fun (P : (flatKFlatComplexes Y).FullSubcategory) => P.2))
        ((derivedTensorBifunctor X.toRingedSite).flip.obj
        ((derivedPullback f).obj (DerivedCategory.Q.obj N))) ≪≫
    Functor.isoWhiskerLeft ((flatKFlatComplexes Y).ι ⋙ (pullbackComplex f) ⋙ DerivedCategory.Q)
        ((derivedTensorBifunctor X.toRingedSite).flip.mapIso (flatPullbackIso f N hN.1 hN.2)) ≪≫
    Functor.isoWhiskerRight
        (Functor.associator (flatKFlatComplexes Y).ι (pullbackComplex f) DerivedCategory.Q).symm
        ((derivedTensorBifunctor X.toRingedSite).flip.obj
        (DerivedCategory.Q.obj ((pullbackComplex f).obj N))) ≪≫
    (Functor.associator ((flatKFlatComplexes Y).ι ⋙ (pullbackComplex f)) DerivedCategory.Q
        ((derivedTensorBifunctor X.toRingedSite).flip.obj
        (DerivedCategory.Q.obj ((pullbackComplex f).obj N))))

/-- The forward map of `derivedPullbackTensorModelRightFstNatIso` is the composite of the forward
maps of its constituent isomorphisms. -/
theorem derivedPullbackTensorModelRightFstNatIso_hom_eq
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) :
    (derivedPullbackTensorModelRightFstNatIso f N hN).hom =
      ((Functor.associator ((flatKFlatComplexes Y).ι ⋙ DerivedCategory.Q) (derivedPullback f)
          ((derivedTensorBifunctor X.toRingedSite).flip.obj
          ((derivedPullback f).obj (DerivedCategory.Q.obj N)))).inv ≫
    Functor.whiskerRight
        (Functor.associator (flatKFlatComplexes Y).ι DerivedCategory.Q (derivedPullback f)).hom
        ((derivedTensorBifunctor X.toRingedSite).flip.obj
        ((derivedPullback f).obj (DerivedCategory.Q.obj N))) ≫
    Functor.whiskerRight
        (flatPullbackNatIsoOf f (flatKFlatComplexes Y).ι
        (fun (P : (flatKFlatComplexes Y).FullSubcategory) => P.2)).hom
        ((derivedTensorBifunctor X.toRingedSite).flip.obj
        ((derivedPullback f).obj (DerivedCategory.Q.obj N))) ≫
    Functor.whiskerLeft ((flatKFlatComplexes Y).ι ⋙ (pullbackComplex f) ⋙ DerivedCategory.Q)
        ((derivedTensorBifunctor X.toRingedSite).flip.map (flatPullbackIso f N hN.1 hN.2).hom) ≫
    Functor.whiskerRight
        (Functor.associator (flatKFlatComplexes Y).ι (pullbackComplex f) DerivedCategory.Q).inv
        ((derivedTensorBifunctor X.toRingedSite).flip.obj
        (DerivedCategory.Q.obj ((pullbackComplex f).obj N))) ≫
    (Functor.associator ((flatKFlatComplexes Y).ι ⋙ (pullbackComplex f)) DerivedCategory.Q
        ((derivedTensorBifunctor X.toRingedSite).flip.obj
        (DerivedCategory.Q.obj ((pullbackComplex f).obj N)))).hom) := rfl

/-- `derivedPullbackTensorModelRightFstNatIso` commutes with the shift. -/
theorem derivedPullbackTensorModelRightFstNatIso_commShift
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) :
    letI := derivedTensorBifunctor_commShift₂Int X.toRingedSite
    NatTrans.CommShift (derivedPullbackTensorModelRightFstNatIso f N hN).hom ℤ := by
  let := derivedTensorBifunctor_commShift₂Int X.toRingedSite
  have h3 : NatTrans.CommShift
      (Functor.whiskerLeft ((flatKFlatComplexes Y).ι ⋙ (pullbackComplex f) ⋙ DerivedCategory.Q)
      ((derivedTensorBifunctor X.toRingedSite).flip.map (flatPullbackIso f N hN.1 hN.2).hom)) ℤ :=
    @NatTrans.CommShift.whiskerLeft _ _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ _
        ((derivedTensorBifunctor_commShift₂Int X.toRingedSite).commShift_flip_map
        (flatPullbackIso f N hN.1 hN.2).hom)
  rw [derivedPullbackTensorModelRightFstNatIso_hom_eq]
  infer_instance

/-- The second part of the second half of Stacks 07A4 on models, as an isomorphism of
functors of a K-flat complex `P` with flat terms: `Q f^*P ⊗^L Q f^*N ≅ Q f^*Tot(P ⊗ N)`. -/
def derivedPullbackTensorModelRightSndNatIso
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (_hN : flatKFlatComplexes Y N) :
    ((flatKFlatComplexes Y).ι ⋙ (pullbackComplex f)) ⋙
        (DerivedCategory.Q ⋙
        ((derivedTensorBifunctor X.toRingedSite).flip.obj
        (DerivedCategory.Q.obj ((pullbackComplex f).obj N)))) ≅
      ((flatKFlatComplexes Y).ι ⋙
          ((Tensor.sheafTensor.{c', u, u, u, u} Y.O).map₂CochainComplex.flip.obj N)) ⋙
          ((pullbackComplex f) ⋙ DerivedCategory.Q) :=
  (kFlatComparisonFlipIsoOf (X := X.toRingedSite) ((flatKFlatComplexes Y).ι ⋙ (pullbackComplex f))
      (fun (P : (flatKFlatComplexes Y).FullSubcategory) =>
      kFlat_pullbackComplex' f P.obj P.2.1 P.2.2) ((pullbackComplex f).obj N)) ≪≫
    (Functor.associator ((flatKFlatComplexes Y).ι ⋙ (pullbackComplex f))
        ((Tensor.sheafTensor.{c, u, u, u, u} X.O).map₂CochainComplex.flip.obj
        ((pullbackComplex f).obj N)) DerivedCategory.Q).symm ≪≫
    Functor.isoWhiskerRight
        (Functor.associator (flatKFlatComplexes Y).ι (pullbackComplex f)
        ((Tensor.sheafTensor.{c, u, u, u, u} X.O).map₂CochainComplex.flip.obj
        ((pullbackComplex f).obj N))) DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (flatKFlatComplexes Y).ι
        (pullbackTensorTotalComplexFlipObjIso f N).symm) DerivedCategory.Q ≪≫
    Functor.isoWhiskerRight
        (Functor.associator (flatKFlatComplexes Y).ι
        ((Tensor.sheafTensor.{c', u, u, u, u} Y.O).map₂CochainComplex.flip.obj N)
        (pullbackComplex f)).symm DerivedCategory.Q ≪≫
    (Functor.associator ((flatKFlatComplexes Y).ι ⋙
        ((Tensor.sheafTensor.{c', u, u, u, u} Y.O).map₂CochainComplex.flip.obj N))
        (pullbackComplex f) DerivedCategory.Q)

/-- The forward map of `derivedPullbackTensorModelRightSndNatIso` is the composite of the forward
maps of its constituent isomorphisms. -/
theorem derivedPullbackTensorModelRightSndNatIso_hom_eq
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) :
    (derivedPullbackTensorModelRightSndNatIso f N hN).hom =
      ((kFlatComparisonFlipIsoOf (X := X.toRingedSite)
          ((flatKFlatComplexes Y).ι ⋙ (pullbackComplex f))
          (fun (P : (flatKFlatComplexes Y).FullSubcategory) =>
          kFlat_pullbackComplex' f P.obj P.2.1 P.2.2) ((pullbackComplex f).obj N)).hom ≫
    (Functor.associator ((flatKFlatComplexes Y).ι ⋙ (pullbackComplex f))
        ((Tensor.sheafTensor.{c, u, u, u, u} X.O).map₂CochainComplex.flip.obj
        ((pullbackComplex f).obj N)) DerivedCategory.Q).inv ≫
    Functor.whiskerRight
        (Functor.associator (flatKFlatComplexes Y).ι (pullbackComplex f)
        ((Tensor.sheafTensor.{c, u, u, u, u} X.O).map₂CochainComplex.flip.obj
        ((pullbackComplex f).obj N))).hom DerivedCategory.Q ≫
    Functor.whiskerRight
        (Functor.whiskerLeft (flatKFlatComplexes Y).ι
        (pullbackTensorTotalComplexFlipObjIso f N).inv) DerivedCategory.Q ≫
    Functor.whiskerRight
        (Functor.associator (flatKFlatComplexes Y).ι
        ((Tensor.sheafTensor.{c', u, u, u, u} Y.O).map₂CochainComplex.flip.obj N)
        (pullbackComplex f)).inv DerivedCategory.Q ≫
    (Functor.associator ((flatKFlatComplexes Y).ι ⋙
        ((Tensor.sheafTensor.{c', u, u, u, u} Y.O).map₂CochainComplex.flip.obj N))
        (pullbackComplex f) DerivedCategory.Q).hom) := rfl

/-- `derivedPullbackTensorModelRightSndNatIso` commutes with the shift. -/
theorem derivedPullbackTensorModelRightSndNatIso_commShift
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) :
    letI := derivedTensorBifunctor_commShift₂Int X.toRingedSite
    NatTrans.CommShift (derivedPullbackTensorModelRightSndNatIso f N hN).hom ℤ := by
  let := derivedTensorBifunctor_commShift₂Int X.toRingedSite
  have h0 : NatTrans.CommShift
      ((kFlatComparisonFlipIsoOf (X := X.toRingedSite)
      ((flatKFlatComplexes Y).ι ⋙ (pullbackComplex f))
      (fun (P : (flatKFlatComplexes Y).FullSubcategory) =>
      kFlat_pullbackComplex' f P.obj P.2.1 P.2.2) ((pullbackComplex f).obj N)).hom) ℤ :=
    kFlatComparisonFlipIsoOf_commShift (X := X.toRingedSite)
        ((flatKFlatComplexes Y).ι ⋙ (pullbackComplex f))
        (fun (P : (flatKFlatComplexes Y).FullSubcategory) =>
        kFlat_pullbackComplex' f P.obj P.2.1 P.2.2) ((pullbackComplex f).obj N)
  rw [derivedPullbackTensorModelRightSndNatIso_hom_eq]
  infer_instance

omit [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [HasSheafify Y.J (Type u)] in
/-- The K-flat comparison on K-flat complexes with flat terms, componentwise. -/
theorem kFlatComparisonFlipIsoOf_flatKFlatComplexes_hom_app
    (N : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Y.O)) ℤ)
    (_hN : flatKFlatComplexes Y N) (P : (flatKFlatComplexes Y).FullSubcategory) :
    (kFlatComparisonFlipIsoOf (X := Y.toRingedSite) (flatKFlatComplexes Y).ι
      (fun (P : (flatKFlatComplexes Y).FullSubcategory) => P.2.1) N).hom.app P =
      (kFlatComparison Y.toRingedSite P.obj P.2.1 N).hom :=
  kFlatComparisonFlipIsoOf_hom_app (X := Y.toRingedSite) (flatKFlatComplexes Y).ι
      (fun (P : (flatKFlatComplexes Y).FullSubcategory) => P.2.1) N P

/-- The computation of `Lf^*` on a total tensor complex does not depend on the flatness proofs. -/
theorem flatPullbackIso_mapBifunctor_congr
    (N : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) (P : (flatKFlatComplexes Y).FullSubcategory) :
    flatPullbackIso f (HomologicalComplex.mapBifunctor P.obj N
            (Stacks.SheafOfModules.Tensor.sheafTensor.{c', u, u, u, u} Y.O) (ComplexShape.up ℤ))
      (kFlat_mapBifunctor (X := Y) P.2.1 hN.1) (isFlat_mapBifunctor_X (X := Y) _ _ P.2.2 hN.2) =
    flatPullbackIso f (HomologicalComplex.mapBifunctor P.obj N
            (Stacks.SheafOfModules.Tensor.sheafTensor.{c', u, u, u, u} Y.O) (ComplexShape.up ℤ))
          (Stacks.SheafOfModules.kFlat_tensorComplex Y.O P.2.1 hN.1)
          (Stacks.Sheaves.DerivedPullback.isFlat_tensorComplex_X_general Y.O P.obj N P.2.2 hN.2) :=
              rfl

/-- The computation of `Lf^*` on `Tot(P ⊗ N)`, for the two spellings of the total complex. -/
theorem flatPullbackIso_flatKFlatComplexes_tensor
    (N : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) (P : (flatKFlatComplexes Y).FullSubcategory) :
    flatPullbackIso f (((flatKFlatComplexes Y).ι ⋙
        (Tensor.sheafTensor.{c', u, u, u, u} Y.O).map₂CochainComplex.flip.obj N).obj P)
      (kFlat_mapBifunctor (X := Y) P.2.1 hN.1) (isFlat_mapBifunctor_X (X := Y) _ _ P.2.2 hN.2) =
    flatPullbackIso f (HomologicalComplex.mapBifunctor P.obj N
            (Stacks.SheafOfModules.Tensor.sheafTensor.{c', u, u, u, u} Y.O) (ComplexShape.up ℤ))
      (kFlat_mapBifunctor (X := Y) P.2.1 hN.1) (isFlat_mapBifunctor_X (X := Y) _ _ P.2.2 hN.2) :=
          rfl

/-- The K-flat comparison on pulled back K-flat complexes with flat terms, componentwise. -/
theorem kFlatComparisonFlipIsoOf_pullbackComplex_hom_app
    (N : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Y.O)) ℤ)
    (_hN : flatKFlatComplexes Y N) (P : (flatKFlatComplexes Y).FullSubcategory) :
    (kFlatComparisonFlipIsoOf (X := X.toRingedSite)
        ((flatKFlatComplexes Y).ι ⋙ pullbackComplex f)
        (fun (P : (flatKFlatComplexes Y).FullSubcategory) =>
          kFlat_pullbackComplex' f P.obj P.2.1 P.2.2) ((pullbackComplex f).obj N)).hom.app P =
              (kFlatComparison X.toRingedSite (((flatKFlatComplexes Y).ι ⋙ pullbackComplex f).obj P)
      ((fun (P : (flatKFlatComplexes Y).FullSubcategory) =>
          kFlat_pullbackComplex' f P.obj P.2.1 P.2.2) P) ((pullbackComplex f).obj N)).hom :=
  kFlatComparisonFlipIsoOf_hom_app (X := X.toRingedSite)
        ((flatKFlatComplexes Y).ι ⋙ pullbackComplex f)
        (fun (P : (flatKFlatComplexes Y).FullSubcategory) =>
          kFlat_pullbackComplex' f P.obj P.2.1 P.2.2) ((pullbackComplex f).obj N) P

/-- The inverse of the comparison of Stacks 03EL as a transformation, componentwise. -/
theorem pullbackTensorTotalComplexFlipObjIso_inv_app_flatKFlatComplexes
    (N : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Y.O)) ℤ)
    (_hN : flatKFlatComplexes Y N) (P : (flatKFlatComplexes Y).FullSubcategory) :
    (pullbackTensorTotalComplexFlipObjIso f N).inv.app ((flatKFlatComplexes Y).ι.obj P) =
      (pullbackTensorTotalComplexIso f ((flatKFlatComplexes Y).ι.obj P) N).inv := rfl

/-- The component of `derivedPullbackTensorModelLeftNatIso` at `P` is `Lf^*` of the K-flat
comparison `Q P ⊗^L Q N ≅ Q Tot(P ⊗ N)` followed by the computation of `Lf^*` on `Tot(P ⊗ N)`. -/
lemma derivedPullbackTensorModelLeftNatIso_hom_app
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) (P : (flatKFlatComplexes Y).FullSubcategory) :
    (derivedPullbackTensorModelLeftNatIso f N hN).hom.app P =
      (derivedPullback f).map (kFlatComparison Y.toRingedSite P.obj P.2.1 N).hom ≫
        (flatPullbackIso f
          (HomologicalComplex.mapBifunctor P.obj N
            (Stacks.SheafOfModules.Tensor.sheafTensor.{c', u, u, u, u} Y.O) (ComplexShape.up ℤ))
          (Stacks.SheafOfModules.kFlat_tensorComplex Y.O P.2.1 hN.1)
          (Stacks.Sheaves.DerivedPullback.isFlat_tensorComplex_X_general Y.O P.obj N P.2.2
              hN.2)).hom := by
  rw [derivedPullbackTensorModelLeftNatIso_hom_eq]
  simp only [NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerRight_app, CategoryTheory.Functor.map_id, Category.id_comp,
    flatPullbackNatIsoOf_hom_app]
  exact (Category.id_comp _).trans (congrArg₂ (· ≫ ·)
    (congrArg (derivedPullback f).map (kFlatComparisonFlipIsoOf_flatKFlatComplexes_hom_app N hN P))
    ((Category.id_comp _).trans
        (congrArg Iso.hom ((flatPullbackIso_flatKFlatComplexes_tensor f N hN P).trans
        (flatPullbackIso_mapBifunctor_congr f N hN P)))))

/-- The second half of Stacks 07A4 on models, componentwise. -/
lemma derivedPullbackTensorModelRightFstNatIso_hom_app_comp
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) (P : (flatKFlatComplexes Y).FullSubcategory) :
    (derivedPullbackTensorModelRightFstNatIso f N hN).hom.app P ≫
        (derivedPullbackTensorModelRightSndNatIso f N hN).hom.app P =
      ((derivedTensorBifunctor X.toRingedSite).map (flatPullbackIso f P.obj P.2.1 P.2.2).hom).app
          ((derivedPullback f).obj (DerivedCategory.Q.obj N)) ≫
        ((derivedTensorBifunctor X.toRingedSite).obj
          (DerivedCategory.Q.obj ((pullbackComplex f).obj P.obj))).map
            (flatPullbackIso f N hN.1 hN.2).hom ≫
        (kFlatComparison X.toRingedSite ((pullbackComplex f).obj P.obj)
          (kFlat_pullbackComplex' f P.obj P.2.1 P.2.2) ((pullbackComplex f).obj N)).hom ≫
        DerivedCategory.Q.map (pullbackTensorTotalComplexIso f P.obj N).inv := by
  rw [derivedPullbackTensorModelRightFstNatIso_hom_eq,
    derivedPullbackTensorModelRightSndNatIso_hom_eq]
  simp only [NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.assoc, flatPullbackNatIsoOf_hom_app,
    Functor.flip_obj_map, Functor.flip_map_app]
  rw [kFlatComparisonFlipIsoOf_pullbackComplex_hom_app f N hN P,
      pullbackTensorTotalComplexFlipObjIso_inv_app_flatKFlatComplexes f N hN P]
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.flip_obj_obj,
    Functor.map₂HomologicalComplex_obj_obj]
  simp only [NatTrans.id_app, Category.id_comp, Category.comp_id]
  rfl

/-- The first half of Stacks 07A4 on models for the construction behind the canonical derived
tensor product, `Stacks.SheafOfModules.derivedTensorProductOfExact`. -/
theorem derivedPullbackTensorModelLeft_ofExact_hom
    (N : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) (P : (flatKFlatComplexes Y).FullSubcategory) :
    (derivedPullbackTensorModelLeft f (exactTensorProduct Y.toRingedSite) P.obj N P.2.1 hN.1 P.2.2
        hN.2).hom =
      (derivedPullback f).map (toTensor Y.toRingedSite P.obj N) ≫
        (flatPullbackIso f
          (HomologicalComplex.mapBifunctor P.obj N
            (Stacks.SheafOfModules.Tensor.sheafTensor.{c', u, u, u, u} Y.O) (ComplexShape.up ℤ))
          (Stacks.SheafOfModules.kFlat_tensorComplex Y.O P.2.1 hN.1)
          (Stacks.Sheaves.DerivedPullback.isFlat_tensorComplex_X_general Y.O P.obj N P.2.2
              hN.2)).hom := rfl

/-- The second half of Stacks 07A4 on models for the construction behind the canonical derived
tensor product, `Stacks.SheafOfModules.derivedTensorProductOfExact`. -/
theorem derivedPullbackTensorModelRight_ofExact_hom
    (N : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) (P : (flatKFlatComplexes Y).FullSubcategory) :
    (derivedPullbackTensorModelRight f (exactTensorProduct X.toRingedSite) P.obj N P.2.1 hN.1 P.2.2
        hN.2).hom =
      ((derivedTensorBifunctor X.toRingedSite).map (flatPullbackIso f P.obj P.2.1 P.2.2).hom).app
          ((derivedPullback f).obj (DerivedCategory.Q.obj N)) ≫
        ((derivedTensorBifunctor X.toRingedSite).obj
          (DerivedCategory.Q.obj ((pullbackComplex f).obj P.obj))).map
            (flatPullbackIso f N hN.1 hN.2).hom ≫
        toTensor X.toRingedSite ((pullbackComplex f).obj P.obj) ((pullbackComplex f).obj N) ≫
        DerivedCategory.Q.map (pullbackTensorTotalComplexIso f P.obj N).inv := by
  dsimp only [derivedPullbackTensorModelRight, Iso.trans_hom, Functor.mapIso_hom,
      Iso.prod_hom, Functor.uncurry_obj_map, Iso.symm_hom, Functor.mapIso_inv]
  simp only [Category.assoc]
  rfl

/-- The first half of Stacks 07A4 on models is the component of
`derivedPullbackTensorModelLeftNatIso`. -/
theorem derivedPullbackTensorModelLeft_ofExact_hom_eq_app
    (N : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) (P : (flatKFlatComplexes Y).FullSubcategory) :
    (derivedPullbackTensorModelLeft f (exactTensorProduct Y.toRingedSite) P.obj N P.2.1 hN.1 P.2.2
        hN.2).hom =
      (derivedPullbackTensorModelLeftNatIso f N hN).hom.app P := by
  rw [derivedPullbackTensorModelLeft_ofExact_hom f N hN P,
      toTensor_eq_kFlatComparison Y.toRingedSite P.2.1 N,
    derivedPullbackTensorModelLeftNatIso_hom_app f N hN P]

/-- The second half of Stacks 07A4 on models is the component of the composite of
`derivedPullbackTensorModelRightFstNatIso` and `derivedPullbackTensorModelRightSndNatIso`. -/
theorem derivedPullbackTensorModelRight_ofExact_hom_eq_app
    (N : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) (P : (flatKFlatComplexes Y).FullSubcategory) :
    (derivedPullbackTensorModelRight f (exactTensorProduct X.toRingedSite) P.obj N P.2.1 hN.1 P.2.2
        hN.2).hom =
      (derivedPullbackTensorModelRightFstNatIso f N hN).hom.app P ≫
        (derivedPullbackTensorModelRightSndNatIso f N hN).hom.app P := by
  rw [derivedPullbackTensorModelRight_ofExact_hom f N hN P,
      toTensor_eq_kFlatComparison X.toRingedSite
    (kFlat_pullbackComplex' f P.obj P.2.1 P.2.2) _,
        derivedPullbackTensorModelRightFstNatIso_hom_app_comp f N hN P]

/-- On K-flat complexes with flat terms, Stacks 07A4 with the second factor the class of a
K-flat complex with flat terms commutes with the shift in the first factor. -/
theorem derivedPullbackTensorFlipObjIso_commShift_model
    (N : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Y.O)) ℤ)
    (hN : flatKFlatComplexes Y N) :
    letI := (exactTensorProduct X.toRingedSite).commShift_left
    letI := (exactTensorProduct Y.toRingedSite).commShift_left
    NatTrans.CommShift
      (Functor.whiskerLeft ((flatKFlatComplexes Y).ι ⋙ DerivedCategory.Q)
        (Functor.flipObjIsoOfUncurryIso
          (derivedPullbackTensorIso f (exactTensorProduct X.toRingedSite)
              (exactTensorProduct Y.toRingedSite)) (DerivedCategory.Q.obj N)).hom) ℤ := by
  let := (exactTensorProduct X.toRingedSite).commShift_left
  let := (exactTensorProduct Y.toRingedSite).commShift_left
  let := derivedTensorBifunctor_commShift₂Int X.toRingedSite
  let := derivedTensorBifunctor_commShift₂Int Y.toRingedSite
  have hL := derivedPullbackTensorModelLeftNatIso_commShift f N hN
  have hR1 := derivedPullbackTensorModelRightFstNatIso_commShift f N hN
  have hR2 := derivedPullbackTensorModelRightSndNatIso_commShift f N hN
  have hR := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ hR1 hR2
  have hRi := @NatTrans.CommShift.of_iso_inv _ _ _ _ _ _
    (derivedPullbackTensorModelRightFstNatIso f N hN ≪≫
      derivedPullbackTensorModelRightSndNatIso f N hN) ℤ _ _ _ _ _ hR
  have hθ := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ hL hRi
  refine @NatTrans.commShift_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ hθ ?_
  ext P
  have eR' : derivedPullbackTensorModelRight f (exactTensorProduct X.toRingedSite) P.obj N P.2.1
      hN.1 P.2.2 hN.2 =
      (derivedPullbackTensorModelRightFstNatIso f N hN ≪≫
        derivedPullbackTensorModelRightSndNatIso f N hN).app P :=
            Iso.ext (derivedPullbackTensorModelRight_ofExact_hom_eq_app f N hN P)
  have e := derivedPullbackTensorIso_hom_app_model f (exactTensorProduct X.toRingedSite)
      (exactTensorProduct Y.toRingedSite) P.obj N P.2.1 hN.1 P.2.2 hN.2
  dsimp only [derivedPullbackTensorModelIso, Iso.trans_hom, Iso.symm_hom] at e
  rwa [derivedPullbackTensorModelLeft_ofExact_hom_eq_app f N hN P, eR'] at e

/-- **Stacks 07A4 commutes with the shift in the first variable**, for the construction behind
the canonical derived tensor products: `Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L` with `L` fixed is
compatible with the shift in `K`. -/
theorem derivedPullbackTensorFlipObjIso_commShift_ofExact
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    letI := (exactTensorProduct X.toRingedSite).commShift_left
    letI := (exactTensorProduct Y.toRingedSite).commShift_left
    NatTrans.CommShift (Functor.flipObjIsoOfUncurryIso
      (derivedPullbackTensorIso f (exactTensorProduct X.toRingedSite)
          (exactTensorProduct Y.toRingedSite)) L).hom ℤ := by
  let := (exactTensorProduct X.toRingedSite).commShift_left
  let := (exactTensorProduct Y.toRingedSite).commShift_left
  obtain ⟨N, hN, ⟨e⟩⟩ := exists_flatKFlatComplexes_iso L
  have hq : ((flatKFlatComplexes Y).ι ⋙ DerivedCategory.Q).EssSurj := ⟨fun L' => by
    obtain ⟨N', hN', ⟨e'⟩⟩ := exists_flatKFlatComplexes_iso L'
    exact ⟨⟨N', hN'⟩, ⟨e'⟩⟩⟩
  have hN' := NatTrans.commShift_of_whiskerLeft _ _
    (derivedPullbackTensorFlipObjIso_commShift_model f N hN)
  have h1 : NatTrans.CommShift (Functor.whiskerRight
      ((exactTensorProduct Y.toRingedSite).tensor.flip.map e.inv) (derivedPullback f)) ℤ :=
    @NatTrans.CommShift.whiskerRight _ _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ _
      ((exactTensorProduct Y.toRingedSite).commShift₂.commShift_flip_map e.inv)
  have h3 : NatTrans.CommShift (Functor.whiskerLeft (derivedPullback f)
      ((exactTensorProduct X.toRingedSite).tensor.flip.map ((derivedPullback f).map e.hom))) ℤ :=
    @NatTrans.CommShift.whiskerLeft _ _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ _
      ((exactTensorProduct X.toRingedSite).commShift₂.commShift_flip_map _)
  have h23 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ hN' h3
  have h123 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h1 h23
  refine @NatTrans.commShift_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ h123 ?_
  ext K
  have key : (derivedPullbackTensorIso f (exactTensorProduct X.toRingedSite)
      (exactTensorProduct Y.toRingedSite)).hom.app (K, L) =
      (Functor.uncurry.obj (exactTensorProduct Y.toRingedSite).tensor ⋙ derivedPullback f).map
          ((𝟙 K, e.inv) : ((K, L) : _ × _) ⟶ (K, DerivedCategory.Q.obj N)) ≫
        (derivedPullbackTensorIso f (exactTensorProduct X.toRingedSite)
            (exactTensorProduct Y.toRingedSite)).hom.app (K, DerivedCategory.Q.obj N) ≫
        ((derivedPullback f).prod (derivedPullback f) ⋙
            Functor.uncurry.obj (exactTensorProduct X.toRingedSite).tensor).map
          ((𝟙 K, e.hom) : ((K, DerivedCategory.Q.obj N) : _ × _) ⟶ (K, L)) := by
    rw [← Category.assoc,
        (derivedPullbackTensorIso f (exactTensorProduct X.toRingedSite)
        (exactTensorProduct Y.toRingedSite)).hom.naturality, Category.assoc,
      ← Functor.map_comp]
    simp
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.flip_map_app, ← Iso.app_hom, Functor.flipObjIsoOfUncurryIso_app]
  simp only [Iso.app_hom]
  rw [key]
  dsimp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map, Functor.prod_obj,
    Functor.comp_obj, Functor.uncurry_obj_obj]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- **Stacks 07A4 commutes with the shift in the first variable**: for the canonical derived
tensor products, `Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L` with `L` fixed is compatible with the shift
in `K`.  The canonical derived tensor product is opaque (`irreducible_def`); its defining equation
`Stacks.SheafOfModules.canonicalDerivedTensorProduct_def` reduces this to
`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorFlipObjIso_commShift_ofExact`. -/
theorem derivedPullbackTensorFlipObjIso_commShift
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    letI := (canonicalDerivedTensorProduct X.toRingedSite).commShift_left
    letI := (canonicalDerivedTensorProduct Y.toRingedSite).commShift_left
    NatTrans.CommShift (Functor.flipObjIsoOfUncurryIso
      (derivedPullbackTensorIso f (canonicalDerivedTensorProduct X.toRingedSite)
        (canonicalDerivedTensorProduct Y.toRingedSite)) L).hom ℤ := by
  have key : ∀ (TX : DerivedTensorProduct X.toRingedSite)
      (TY : DerivedTensorProduct Y.toRingedSite),
      exactTensorProduct X.toRingedSite = TX → exactTensorProduct Y.toRingedSite = TY →
      let := TX.commShift_left
      let := TY.commShift_left
      NatTrans.CommShift (Functor.flipObjIsoOfUncurryIso
        (derivedPullbackTensorIso f TX TY) L).hom ℤ := by
    rintro _ _ rfl rfl
    exact derivedPullbackTensorFlipObjIso_commShift_ofExact f L
  exact key _ _ (canonicalDerivedTensorProduct_def _).symm
      (canonicalDerivedTensorProduct_def _).symm

/-- **Stacks 07A4 commutes with the shift in the first variable**, for any presentations `TX`,
`TY` of the canonical derived tensor products and any presentation `e` of the isomorphism of
Stacks 07A4. Instantiating it with the presentations at hand avoids comparing them inside the
statement. -/
theorem derivedPullbackTensorFlipObjIso_commShift_of_eq
    (TX : DerivedTensorProduct X.toRingedSite) (TY : DerivedTensorProduct Y.toRingedSite)
    (hX : TX = canonicalDerivedTensorProduct X.toRingedSite)
    (hY : TY = canonicalDerivedTensorProduct Y.toRingedSite)
    (e : Functor.uncurry.obj TY.tensor ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ Functor.uncurry.obj TX.tensor)
    (he : e = derivedPullbackTensorIso f TX TY)
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    letI := TX.commShift_left
    letI := TY.commShift_left
    NatTrans.CommShift (Functor.flipObjIsoOfUncurryIso e L).hom ℤ := by
  subst hX hY he
  exact derivedPullbackTensorFlipObjIso_commShift f L

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
