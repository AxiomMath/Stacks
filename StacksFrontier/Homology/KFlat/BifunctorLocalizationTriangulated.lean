module

public import StacksFrontier.Homology.KFlat.BifunctorLocalization
import StacksCore.Tactic.StacksAttribute

/-!
# Shift structures of the descended bifunctor

Declarations built on `StacksFrontier.Homology.KFlat.BifunctorLocalization`.

## Main results

* `kFlatToDerivedFlipObjIso`
* `kFlatToDerivedObjIso`
* `kFlatToDerivedFlipObjCommShift`
* `kFlatToDerivedObjCommShift`
* `kFlatToDerivedFlipObj_isTriangulated`
* `kFlatToDerivedObj_isTriangulated`
* `derivedBifunctorFlipObjCommShift`
* `derivedBifunctorObjCommShift`
* `derivedBifunctorFlipObj_isTriangulated`
* `derivedBifunctorObj_isTriangulated`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Pretriangulated

noncomputable section

/-- A functor isomorphic to a triangulated functor is triangulated for the transported shift
structure. -/
private theorem isTriangulated_ofIso {C E : Type*} [Category C] [Category E] [HasShift C ℤ]
    [HasShift E ℤ] [HasZeroObject C] [HasZeroObject E] [Preadditive C] [Preadditive E]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor E n).Additive]
    [Pretriangulated C] [Pretriangulated E] {G₁ G₂ : C ⥤ E} (e : G₁ ≅ G₂) [G₁.CommShift ℤ]
    [G₁.IsTriangulated] :
    letI := Functor.CommShift.ofIso e ℤ
    G₂.IsTriangulated := by
  let := Functor.CommShift.ofIso e ℤ
  have _ := Functor.CommShift.ofIso_compatibility e ℤ
  exact Functor.isTriangulated_of_iso e

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-! ### The descent to the derived categories -/

section DerivedDescent

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]

section Exactness

variable [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

attribute [local instance] kFlatObjects_isTriangulated kFlatObjectsLeft_isTriangulated

/-- `Tot(F(-, K₂))` on the left K-flat objects, read in `D(D)`, is `Φ^R_{K₂}` followed by `Qh`:
`homotopyBifunctorFlipIsoPhiR` restricted to the left K-flat objects. -/
noncomputable def kFlatToDerivedFlipObjIso (L : (kFlatObjects F).FullSubcategory) :
    (kFlatObjectsLeft F).ι ⋙
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR F L.obj.as ⋙ DerivedCategory.Qh ≅
      (kFlatToDerived F).flip.obj L :=
  Functor.isoWhiskerLeft (kFlatObjectsLeft F).ι
    (Functor.isoWhiskerRight (homotopyBifunctorFlipIsoPhiR F L.obj.as).symm
      (DerivedCategory.Qh (C := D)))

/-- `Tot(F(K₁, -))` on the K-flat objects, read in `D(D)`, is `Φ_{K₁}` followed by `Qh`. -/
noncomputable def kFlatToDerivedObjIso (K : (kFlatObjectsLeft F).FullSubcategory) :
    (kFlatObjects F).ι ⋙
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi F K.obj.as ⋙ DerivedCategory.Qh ≅
      (kFlatToDerived F).obj K :=
  Functor.isoWhiskerLeft (kFlatObjects F).ι
    (Functor.isoWhiskerRight (homotopyBifunctorObjIsoPhi F K.obj.as).symm
      (DerivedCategory.Qh (C := D)))

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- **The shift structure of `Tot(F(-, K₂))` on the left K-flat objects, for `K₂` K-flat**: the
Koszul-sign-free shift isomorphisms of total complexes in the first variable
(`Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR`, the descent of Mathlib's
`CochainComplex.mapBifunctorShift₁Iso`), transported along `kFlatToDerivedFlipObjIso`. -/
@[instance_reducible]
noncomputable def kFlatToDerivedFlipObjCommShift (L : (kFlatObjects F).FullSubcategory) :
    ((kFlatToDerived F).flip.obj L).CommShift ℤ :=
  letI := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR F L.obj.as
  Functor.CommShift.ofIso (kFlatToDerivedFlipObjIso F L) ℤ

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- **The shift structure of `Tot(F(K₁, -))` on the K-flat objects, for `K₁` left K-flat**: the
Koszul-sign shift isomorphisms of total complexes in the second variable
(`Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi`), transported along
`kFlatToDerivedObjIso`. -/
@[instance_reducible]
noncomputable def kFlatToDerivedObjCommShift (K : (kFlatObjectsLeft F).FullSubcategory) :
    ((kFlatToDerived F).obj K).CommShift ℤ :=
  letI := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi F K.obj.as
  Functor.CommShift.ofIso (kFlatToDerivedObjIso F K) ℤ

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- With `kFlatToDerivedFlipObjCommShift`, `Tot(F(-, K₂))` is a triangulated functor: it is
`Φ^R_{K₂}` (triangulated by Tag 0G6E) between the inclusion and `Qh`. -/
theorem kFlatToDerivedFlipObj_isTriangulated (L : (kFlatObjects F).FullSubcategory) :
    letI := kFlatToDerivedFlipObjCommShift F L
    ((kFlatToDerived F).flip.obj L).IsTriangulated := by
  let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR F L.obj.as
  have _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR_isTriangulated F L.obj.as
  exact isTriangulated_ofIso (kFlatToDerivedFlipObjIso F L)

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- With `kFlatToDerivedObjCommShift`, `Tot(F(K₁, -))` is a triangulated functor. -/
theorem kFlatToDerivedObj_isTriangulated (K : (kFlatObjectsLeft F).FullSubcategory) :
    letI := kFlatToDerivedObjCommShift F K
    ((kFlatToDerived F).obj K).IsTriangulated := by
  let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi F K.obj.as
  have _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated F K.obj.as
  exact isTriangulated_ofIso (kFlatToDerivedObjIso F K)

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
omit [HasDerivedCategory A] [HasDerivedCategory B]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
attribute [local instance] kFlatQuasiIso_hasLeftCalculusOfFractions
  kFlatQuasiIsoLeft_hasLeftCalculusOfFractions

omit [HasDerivedCategory A] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)] in
omit [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
attribute [local instance] kFlatQ_essSurj kFlatQLeft_essSurj

omit [HasDerivedCategory A] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)] in
omit [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
attribute [local instance] kFlatQ_mapArrow_essSurj kFlatQLeft_mapArrow_essSurj

/-- **The shift structure of `- ⊗ L` on `D(A)`**, for `L ∈ D(B)`: at a K-flat preimage `K` of
`L`, the descent along the left K-flat localization (Mathlib's `Functor.commShiftOfLocalization`)
of `kFlatToDerivedFlipObjCommShift`, transported along `L ≅ Q(K)`. -/
@[instance_reducible]
noncomputable def derivedBifunctorFlipObjCommShift (L : DerivedCategory B) :
    ((derivedBifunctor F).flip.obj L).CommShift ℤ :=
  letI := kFlatToDerivedFlipObjCommShift F ((kFlatQ F).objPreimage L)
  letI := CategoryTheory.Localization.Lifting₂.snd (kFlatQLeft F) (kFlatQ F)
    (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) (kFlatToDerived F) (derivedBifunctor F)
    ((kFlatQ F).objPreimage L)
  letI := Functor.commShiftOfLocalization (kFlatQLeft F) (kFlatQuasiIsoLeft F) ℤ
    ((kFlatToDerived F).flip.obj ((kFlatQ F).objPreimage L))
    ((derivedBifunctor F).flip.obj ((kFlatQ F).obj ((kFlatQ F).objPreimage L)))
  Functor.CommShift.ofIso ((derivedBifunctor F).flip.mapIso ((kFlatQ F).objObjPreimageIso L)) ℤ

/-- **The shift structure of `K ⊗ -` on `D(B)`**, for `K ∈ D(A)`: the mirror of
`derivedBifunctorFlipObjCommShift`, through a left K-flat preimage of `K`. -/
@[instance_reducible]
noncomputable def derivedBifunctorObjCommShift (K : DerivedCategory A) :
    ((derivedBifunctor F).obj K).CommShift ℤ :=
  letI := kFlatToDerivedObjCommShift F ((kFlatQLeft F).objPreimage K)
  letI := CategoryTheory.Localization.Lifting₂.fst (kFlatQLeft F) (kFlatQ F)
    (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) (kFlatToDerived F) (derivedBifunctor F)
    ((kFlatQLeft F).objPreimage K)
  letI := Functor.commShiftOfLocalization (kFlatQ F) (kFlatQuasiIso F) ℤ
    ((kFlatToDerived F).obj ((kFlatQLeft F).objPreimage K))
    ((derivedBifunctor F).obj ((kFlatQLeft F).obj ((kFlatQLeft F).objPreimage K)))
  Functor.CommShift.ofIso ((derivedBifunctor F).mapIso ((kFlatQLeft F).objObjPreimageIso K)) ℤ

/-- With `derivedBifunctorFlipObjCommShift`, tensoring in the left variable is a triangulated
functor. -/
theorem derivedBifunctorFlipObj_isTriangulated (L : DerivedCategory B) :
    letI := derivedBifunctorFlipObjCommShift F L
    ((derivedBifunctor F).flip.obj L).IsTriangulated := by
  let K := (kFlatQ F).objPreimage L
  let := kFlatToDerivedFlipObjCommShift F K
  have _ := kFlatToDerivedFlipObj_isTriangulated F K
  let := CategoryTheory.Localization.Lifting₂.snd (kFlatQLeft F) (kFlatQ F)
    (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) (kFlatToDerived F) (derivedBifunctor F) K
  let := Functor.commShiftOfLocalization (kFlatQLeft F) (kFlatQuasiIsoLeft F) ℤ
    ((kFlatToDerived F).flip.obj K) ((derivedBifunctor F).flip.obj ((kFlatQ F).obj K))
  have _ := Functor.isTriangulated_of_localization (kFlatQLeft F) (kFlatQuasiIsoLeft F)
    ((kFlatToDerived F).flip.obj K) ((derivedBifunctor F).flip.obj ((kFlatQ F).obj K))
  exact isTriangulated_ofIso ((derivedBifunctor F).flip.mapIso ((kFlatQ F).objObjPreimageIso L))

/-- With `derivedBifunctorObjCommShift`, tensoring in the right variable is a triangulated
functor. -/
theorem derivedBifunctorObj_isTriangulated (K : DerivedCategory A) :
    letI := derivedBifunctorObjCommShift F K
    ((derivedBifunctor F).obj K).IsTriangulated := by
  let K' := (kFlatQLeft F).objPreimage K
  let := kFlatToDerivedObjCommShift F K'
  have _ := kFlatToDerivedObj_isTriangulated F K'
  let := CategoryTheory.Localization.Lifting₂.fst (kFlatQLeft F) (kFlatQ F)
    (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) (kFlatToDerived F) (derivedBifunctor F) K'
  let := Functor.commShiftOfLocalization (kFlatQ F) (kFlatQuasiIso F) ℤ
    ((kFlatToDerived F).obj K') ((derivedBifunctor F).obj ((kFlatQLeft F).obj K'))
  have _ := Functor.isTriangulated_of_localization (kFlatQ F) (kFlatQuasiIso F)
    ((kFlatToDerived F).obj K') ((derivedBifunctor F).obj ((kFlatQLeft F).obj K'))
  exact isTriangulated_ofIso ((derivedBifunctor F).mapIso ((kFlatQLeft F).objObjPreimageIso K))

end Exactness

end DerivedDescent

end CochainComplex.KFlatBifunctor

end

end
