module

public import StacksFrontier.Homology.KFlat.BifunctorComplexModelsShift

/-!
# The left mirror of the shift-compatible model for the K-flat objects

`StacksFrontier/Homology/KFlat/BifunctorComplexModelsShift.lean` proves that the homotopy quotient
from the K-flat cochain complexes to the K-flat objects of the homotopy category commutes with the
shift, and that the bridge `kFlatQuotient ⋙ kFlatQ ≅ kFlatComplexQ` is shift-compatible.  It does
that for the **second** variable of the bifunctor `F` only, which is all a one-sided descent
needs.

The two-sided K-flat comparison of [Stacks, Tag 06YU] — `CochainComplex.KFlatBifunctor.comparison`
and its bundled form `derivedComparisonNatIso` — is a transformation of bifunctors on *left*
K-flat complexes in the first variable and K-flat complexes in the second, so its shift
compatibility needs the same package in the first variable.  This file supplies it.

## Main results

* `CochainComplex.KFlatBifunctor.kFlatQuotientCompιLeft_commShift`: the identification of the
  left homotopy quotient composed with the inclusion of the left K-flat objects with the inclusion
  of the left K-flat complexes composed with the homotopy quotient is shift-compatible.
* `CochainComplex.KFlatBifunctor.kFlatQuotientCompQIsoAssocLeft` and `…_eq`: the left bridge with
  its two reassociations and the lift comparison written out, and the fact that it is the same
  isomorphism.
* `CochainComplex.KFlatBifunctor.kFlatQuotientCompQIsoLeft_commShift`: **the left bridge
  `kFlatQuotientLeft ⋙ kFlatQLeft ≅ kFlatComplexQLeft` is shift-compatible.**

## Implementation notes

Each declaration is the mirror of its counterpart in `BifunctorComplexModelsShift.lean`, for the
same reason recorded there: `CategoryTheory.NatTrans.CommShift` takes the
`CategoryTheory.Functor.CommShift` data of its source and target as instance arguments, and the
datum instance search finds for `kFlatQuotientLeft F ⋙ kFlatQLeft F` is
`CategoryTheory.Functor.CommShift.comp`, not the one the whiskering defining the bridge supplies.
Writing the bridge as a composite of four factors whose shift compatibility is an instance — two
associators, the lift comparison and `DerivedCategory.quotientCompQhIso` — makes
`infer_instance` succeed, and `kFlatQuotientCompQIsoAssocLeft_eq` records that the reassociated
composite is the bridge.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- The mirror of `kFlatQuotientCompι_commShift` in the first variable of `F`, by
`CategoryTheory.Functor.CommShift.ofComp_compatibility`. -/
theorem kFlatQuotientCompιLeft_commShift :
    letI := kFlatQuotientLeft_commShift F
    NatTrans.CommShift ((kFlatObjectsLeft F).liftCompιIso
      ((kFlatComplexesLeft F).ι ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (fun K ↦ K.2)).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]

/-- `kFlatQuotientCompQIsoLeft` with its two reassociations and the lift comparison written out,
so that every junction matches a factor whose shift compatibility is an instance.  This is the
mirror of `kFlatQuotientCompQIsoAssoc`. -/
def kFlatQuotientCompQIsoAssocLeft :
    kFlatQuotientLeft F ⋙ kFlatQLeft F ≅ kFlatComplexQLeft F :=
  (Functor.associator (kFlatQuotientLeft F) (kFlatObjectsLeft F).ι DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerRight ((kFlatObjectsLeft F).liftCompιIso
        ((kFlatComplexesLeft F).ι ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ))
        (fun K ↦ K.2)) DerivedCategory.Qh ≪≫
      Functor.associator (kFlatComplexesLeft F).ι
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft (kFlatComplexesLeft F).ι (DerivedCategory.quotientCompQhIso A)

omit [HasDerivedCategory B] [HasDerivedCategory D] in
/-- The reassociated left bridge is `kFlatQuotientCompQIsoLeft`: the two associators and the lift
comparison are the identity on every object. -/
theorem kFlatQuotientCompQIsoAssocLeft_eq :
    kFlatQuotientCompQIsoAssocLeft F = kFlatQuotientCompQIsoLeft F := by
  ext K
  have h : ((kFlatObjectsLeft F).liftCompιIso
      ((kFlatComplexesLeft F).ι ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (fun K ↦ K.2)).hom.app K = 𝟙 _ := rfl
  simp [kFlatQuotientCompQIsoAssocLeft, kFlatQuotientCompQIsoLeft, h]

omit [HasDerivedCategory B] [HasDerivedCategory D] in
/-- **The left bridge `kFlatQuotientLeft ⋙ kFlatQLeft ≅ kFlatComplexQLeft` is
shift-compatible.**  Each of the four factors of `kFlatQuotientCompQIsoAssocLeft` is: the two
associators by `CategoryTheory.NatTrans.CommShift.associator`, the lift comparison by
`kFlatQuotientCompιLeft_commShift`, and `DerivedCategory.quotientCompQhIso` by Mathlib. -/
theorem kFlatQuotientCompQIsoLeft_commShift :
    letI := kFlatQuotientLeft_commShift F
    NatTrans.CommShift (kFlatQuotientCompQIsoLeft F).hom ℤ := by
  let := kFlatQuotientLeft_commShift F
  let := kFlatQuotientCompιLeft_commShift F
  let : NatTrans.CommShift (kFlatQuotientCompQIsoAssocLeft F).hom ℤ := by
    unfold kFlatQuotientCompQIsoAssocLeft
    dsimp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
    infer_instance
  exact NatTrans.commShift_of_eq (congrArg Iso.hom (kFlatQuotientCompQIsoAssocLeft_eq F).symm)

end CochainComplex.KFlatBifunctor

end

end
