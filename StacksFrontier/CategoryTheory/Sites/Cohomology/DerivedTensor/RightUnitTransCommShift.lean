module

public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ComparisonCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorCommShiftTwoField
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalRightUnitorCommShift

/-!
# The unit constraint on the right of the derived tensor product commutes with the shift

Let `(C, O)` be a ringed site and `T` the canonical derived tensor product on `D(O)`. Its unit
constraint on the right, `K ⊗^L_O O ⟶ K`, is a natural transformation
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitTrans` from `- ⊗^L_O O` to the
identity. This file shows that it commutes with the shift in `K`, for the commutation of
`- ⊗^L_O O` with the shift carried by the derived tensor product.

Both sides are tested on the left K-flat complexes, which reach every object of `D(O)`. There
the transformation is the one-sided K-flat comparison `Q(K) ⊗^L_O Q(O[0]) ≅ Q(Tot(K ⊗_O O[0]))`
followed by `Q` of the unit law `Tot(K ⊗_O O[0]) ≅ K` of complexes. The comparison commutes
with the shift in `K` (`Stacks.SheafOfModules.DerivedMonoidal.commShift_comparisonRightFirst`),
and so does the unit law of complexes, which is given on each summand by the unit law
`K^n ⊗_O O ≅ K^n` of sheaves of modules (`CochainComplex.commShift_of_ιMapBifunctor_single`).

## Main definitions

* `Stacks.SheafOfModules.tensorComplexUnitNatTrans`: the unit law `Tot(K ⊗_O O[0]) ⟶ K` as a
  morphism of functors of `K`.

## Main results

* `Stacks.SheafOfModules.commShift_tensorComplexUnitNatTrans`: the unit law of complexes
  commutes with the shift.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift_rightUnitTrans`: the unit
  constraint on the right of the canonical derived tensor product commutes with the shift.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift_rightUnitTrans_canonicalTensor`:
  the same, for the shift datum
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int`.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_hom_commShift`: the same
  statement for the components `(T.rightUnitIso X A).hom`.

## References

* [Stacks Project, Tag 0B4C](https://stacks.math.columbia.edu/tag/0B4C)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

/-! ### The unit law of complexes commutes with the shift -/

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v}) [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} R).obj
    M).Additive]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} R)
      (ComplexShape.up ℤ)]

/-- **The unit law `Tot(K ⊗_O O[0]) ⟶ K` of complexes of `O`-modules**, as a morphism of
functors of `K`; its components are `Stacks.SheafOfModules.tensorComplexUnitIso`. -/
def tensorComplexUnitNatTrans :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v}
        R).map₂CochainComplex.flip.obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))) ⟶
      𝟭 (CochainComplex (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) where
  app K := (tensorComplexUnitIso R K).hom
  naturality _ _ φ := tensorComplexUnitIso_naturality R φ

/-- The components of `Stacks.SheafOfModules.tensorComplexUnitNatTrans` are the unit law
`Stacks.SheafOfModules.tensorComplexUnitIso`. -/
lemma tensorComplexUnitNatTrans_app
    (K : CochainComplex (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    (tensorComplexUnitNatTrans R).app K = (tensorComplexUnitIso R K).hom :=
  rfl

/-- **The unit law `Tot(K ⊗_O O[0]) ≅ K` on a summand**: on the summand of bidegree `(n, 0)` it
is the unit law `K^n ⊗_O O ≅ K^n` of `⊗_O`. -/
lemma ι_tensorComplexUnitIso_hom_f
    (K : CochainComplex (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) (n : ℤ) (h : n + 0 = n) :
    HomologicalComplex.ιMapBifunctor K ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)))
        (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ) n 0 n h ≫
        (tensorComplexUnitIso R K).hom.f n =
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj (K.X n)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).hom ≫
        (sheafTensorUnitNatIso R).hom.app (K.X n) := by
  have h1 := CochainComplex.KFlatBifunctor.ι_totalSingleIso_hom_f
    (Stacks.SheafOfModules.Tensor.sheafTensor R) K
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) n
  have h2 : (tensorComplexUnitIso R K).hom.f n =
      (CochainComplex.KFlatBifunctor.totalSingleIso (Stacks.SheafOfModules.Tensor.sheafTensor R) K
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).hom.f n ≫
        (rowComplexUnitIso R K).hom.f n := rfl
  have h3 : (rowComplexUnitIso R K).hom.f n = (sheafTensorUnitNatIso R).hom.app (K.X n) :=
    Category.comp_id _
  rw [h2, ← Category.assoc, h1, h3]
  rfl

/-- **The unit law `Tot(K ⊗_O O[0]) ≅ K` of complexes commutes with the shift in `K`.** -/
instance commShift_tensorComplexUnitNatTrans :
    NatTrans.CommShift (tensorComplexUnitNatTrans R) ℤ :=
  CochainComplex.commShift_of_ιMapBifunctor_single (Stacks.SheafOfModules.Tensor.sheafTensor R)
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)))
    (fun q hq => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ q hq)
    (tensorComplexUnitNatTrans R)
    (fun A => ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).hom ≫
      (sheafTensorUnitNatIso R).hom.app A)
    (fun K n h => ι_tensorComplexUnitIso_hom_f R K n h)

end Stacks.SheafOfModules

/-! ### The unit constraint on the right of the derived tensor product -/

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.DerivedTensor.RingedSite

open Stacks.SheafOfModules.DerivedMonoidal CochainComplex.KFlatBifunctor

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctorReg K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

namespace DerivedTensorProduct

/-- On the left K-flat complexes, the unit constraint on the right of the canonical derived
tensor product is the one-sided K-flat comparison followed by `Q` of the unit law of
complexes. -/
lemma whiskerLeft_kFlatComplexQLeft_rightUnitTrans :
    Functor.whiskerLeft
        (kFlatComplexQLeft (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O))
        (rightUnitTrans X (canonicalDerivedTensorProduct X.O)) =
      (comparisonRightFirst (canonicalDerivedTensorProduct X.O)
          (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
        Functor.whiskerLeft
          (kFlatComplexesLeft (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)).ι
          (Functor.whiskerRight (Stacks.SheafOfModules.tensorComplexUnitNatTrans X.O)
              DerivedCategory.Q ≫
            (Functor.leftUnitor DerivedCategory.Q).hom) ≫
        (Functor.rightUnitor
          (kFlatComplexQLeft
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O))).inv := by
  ext K
  refine (rightUnitTrans_app_Q X _ K.1).trans ?_
  simp [comparisonRightFirst_hom_app, Stacks.SheafOfModules.tensorComplexUnitNatTrans_app]
  rfl

/-- **The unit constraint on the right of the canonical derived tensor product commutes with the
shift**, for the commutation of `- ⊗^L_O O` with the shift carried by the derived tensor
product. -/
instance commShift_rightUnitTrans :
    NatTrans.CommShift (rightUnitTrans X (canonicalDerivedTensorProduct X.O)) ℤ := by
  have := kFlatComplexQLeft_essSurj X.O
  have hc := commShift_comparisonRightFirst X.O (Stacks.SheafOfModules.isKFlat_single_unit X.O)
  apply NatTrans.commShift_of_whiskerLeft
    (kFlatComplexQLeft (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O))
  rw [whiskerLeft_kFlatComplexQLeft_rightUnitTrans]
  infer_instance

/-- **The unit constraint on the right commutes with the shift**, for the commutation of
`- ⊗^L_O O` with the shift read off
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int`. That datum is the shift
datum of the canonical derived tensor product
(`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq`), so this
is `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift_rightUnitTrans`. -/
theorem commShift_rightUnitTrans_canonicalTensor :
    letI := (Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int
      X.O).commShiftFlipObj (unitObject X)
    NatTrans.CommShift (rightUnitTrans X (canonicalDerivedTensorProduct X.O)) ℤ := by
  rw [← Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq X.O]
  exact commShift_rightUnitTrans X

/-- **The unit constraint on the right of the canonical derived tensor product commutes with the
shift, at one object**: for `A` in `D(O)` and `n : ℤ`, the isomorphism `(A ⊗^L_O O)[n] ≅ A[n]`
obtained by shifting the unit constraint of `A` is the unit constraint of `A[n]` composed with
the commutation of `- ⊗^L_O O` with the shift. -/
theorem rightUnitIso_hom_commShift (A : DerivedModules X.O) (n : ℤ) :
    (((canonicalDerivedTensorProduct X.O).tensor.flip.obj (unitObject X)).commShiftIso
          n).hom.app A ≫
        (shiftFunctor (DerivedModules X.O) n).map
          ((canonicalDerivedTensorProduct X.O).rightUnitIso X A).hom =
      ((canonicalDerivedTensorProduct X.O).rightUnitIso X
        ((shiftFunctor (DerivedModules X.O) n).obj A)).hom := by
  rw [rightUnitIso_hom_eq, rightUnitIso_hom_eq, NatTrans.shift_app_comm,
    Functor.commShiftIso_id_hom_app]
  exact Category.comp_id _

end DerivedTensorProduct

end Stacks.DerivedTensor.RingedSite

end
