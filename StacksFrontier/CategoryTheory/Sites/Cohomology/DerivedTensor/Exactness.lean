module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Assembly
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product is exact in each variable

Let `(C, O)` be a ringed site. Tensoring in the derived category with a fixed object, in either
variable, is an exact functor of triangulated categories. This is the exactness assertion of
Stacks 06YU, and with it the derived tensor product exists in the full sense the tag states.

The proof reduces to Stacks 06YM. Fix the first variable at the class of a K-flat complex `A`.
The functor `A ⊗^L_O -` on `D(Mod(O))` is then the descent along `DerivedCategory.Qh` of the
functor `Tot(A ⊗_O -)` on the homotopy category, which 06YM shows is exact; and a functor
which factors an exact functor through a localization is itself exact (Stacks 05R7). Fixing
the second variable instead, the same argument runs along the localization of the K-flat
complexes onto the derived category. An arbitrary object of `D(Mod(O))` is isomorphic to the
class of a K-flat complex, by Stacks 06YS, so the general case follows by transport.

## Main results

* `Stacks.SheafOfModules.exists_commShift_isTriangulated_obj`: exactness in the second
  variable, the first being fixed.
* `Stacks.SheafOfModules.exists_commShift_isTriangulated_flip_obj`: exactness in the first
  variable, the second being fixed.

## Implementation notes

Identifying `A ⊗^L_O -` with the descent of `Tot(A ⊗_O -)` is a uniqueness-of-lifts argument:
both lift the same functor `Tot(A ⊗_O -)` followed by `DerivedCategory.Q` along the homotopy
quotient — the first because the derived tensor product is a descent along
`DerivedCategory.Q` in its second variable, the second by the factorisation isomorphism of
06YM. `CategoryTheory.Localization.liftNatIso` then identifies them.

The transport of exactness through a localization is
`CategoryTheory.Functor.isTriangulated_of_localization` together with
`CategoryTheory.Functor.commShiftOfLocalization`; the transport along an isomorphism of
functors is `CategoryTheory.Functor.CommShift.ofIso` and
`CategoryTheory.Functor.isTriangulated_of_iso`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 05R7](https://stacks.math.columbia.edu/tag/05R7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))]

attribute [local instance] kFlatQ_isLocalization derivedTensorBifunctorLifting

/-- Every object of the derived category is isomorphic to the class of a K-flat complex. -/
theorem exists_kFlat_iso
    (N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (_ : IsKFlat X.O A), Nonempty (DerivedCategory.Q.obj A ≅ N) := by
  refine ⟨kFlatRes X (DerivedCategory.Q.objPreimage N), isKFlat_kFlatRes X _, ⟨?_⟩⟩
  have : IsIso (DerivedCategory.Q.map (kFlatResMap X (DerivedCategory.Q.objPreimage N))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  exact asIso (DerivedCategory.Q.map (kFlatResMap X (DerivedCategory.Q.objPreimage N))) ≪≫
    DerivedCategory.Q.objObjPreimageIso N

/-- For a K-flat complex `A`, the functor `A ⊗^L_O -` on the derived category descends
`Tot(A ⊗_O -)` on the homotopy category along `DerivedCategory.Qh`. -/
@[instance_reducible]
def derivedTensorObjLifting
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsKFlat X.O A) :
    Localization.Lifting DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi (Stacks.SheafOfModules.Tensor.sheafTensor
        X.O) A ⋙
        DerivedCategory.Qh)
      ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)) := by
  letI := Localization.Lifting₂.fst (kFlatComplexQ X) DerivedCategory.Q
    (kFlatComplexQuasiIso X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (kFlatTensorToDerived X) (derivedTensorBifunctor X) (kFlatObj X A hA)
  letI : Localization.Lifting (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences _ (ComplexShape.up ℤ))
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q)
      (DerivedCategory.Qh ⋙ (derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _)
        ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)) ≪≫
      Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
        ((kFlatTensorToDerived X).obj (kFlatObj X A hA))
        ((derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj (kFlatObj X A hA)))⟩
  letI : Localization.Lifting (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences _ (ComplexShape.up ℤ))
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q)
      (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi (Stacks.SheafOfModules.Tensor.sheafTensor
        X.O) A ⋙
        DerivedCategory.Qh) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A)
        DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A)
        (DerivedCategory.quotientCompQhIso _)⟩
  exact ⟨Localization.liftNatIso (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences _ (ComplexShape.up ℤ))
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q)
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q) _ _ (Iso.refl _)
      |>.symm⟩

/-- **Exactness in the second variable, for a K-flat first factor.** The functor is the
descent of the exact functor `Tot(A ⊗_O -)` of Stacks 06YM, so Stacks 05R7 applies. -/
theorem exists_commShift_isTriangulated_obj_kFlat
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsKFlat X.O A) :
    ∃ s : ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)).CommShift ℤ,
      letI := s
      ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)).IsTriangulated := by
  let _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A
  have _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A
  let _ := derivedTensorObjLifting X A hA
  let _ := Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) ℤ
    (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi (Stacks.SheafOfModules.Tensor.sheafTensor
      X.O) A ⋙
      DerivedCategory.Qh)
    ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A))
  exact ⟨inferInstance, Functor.isTriangulated_of_localization DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) _ _⟩

/-- Exactness of a functor, together with a compatible shift commutation, transports along an
isomorphism of functors. -/
private theorem exists_commShift_isTriangulated_of_iso
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] {F G : C ⥤ D}
    (e : F ≅ G) (h : ∃ s : F.CommShift ℤ, letI := s; F.IsTriangulated) :
    ∃ s : G.CommShift ℤ, letI := s; G.IsTriangulated := by
  obtain ⟨_, _⟩ := h
  let _ := Functor.CommShift.ofIso e ℤ
  have _ := Functor.CommShift.ofIso_compatibility e ℤ
  exact ⟨inferInstance, Functor.isTriangulated_of_iso e⟩

/-- **Exactness of the derived tensor product in its second variable**: fixing the first
argument gives an exact functor of triangulated categories. -/
theorem exists_commShift_isTriangulated_obj
    (N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ s : ((derivedTensorBifunctor X).obj N).CommShift ℤ,
      letI := s; ((derivedTensorBifunctor X).obj N).IsTriangulated := by
  obtain ⟨A, hA, ⟨e⟩⟩ := exists_kFlat_iso X N
  exact exists_commShift_isTriangulated_of_iso ((derivedTensorBifunctor X).mapIso e)
    (exists_commShift_isTriangulated_obj_kFlat X A hA)

omit [HasDerivedCategory.{d}
  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))] in
/-- The quasi-isomorphisms between K-flat objects of the homotopy category admit a left
calculus of fractions, being the class generated by the acyclic K-flat objects. -/
theorem kFlatQuasiIso_hasLeftCalculusOfFractions :
    (kFlatQuasiIso.{c, u, u} X.O).HasLeftCalculusOfFractions := by
  have h : kFlatQuasiIso.{c, u, u} X.O =
      ((HomotopyCategory.subcategoryAcyclic
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inverseImage
          (kFlatObjects.{c, u, u} X.O).ι).trW := by
    ext Y Z f
    change HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)
      ((kFlatObjects X.O).ι.map f) ↔ _
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inverseImage_trW_iff
        (kFlatObjects X.O).ι f).symm
  rw [h]
  infer_instance

attribute [local instance] kFlatQuasiIso_hasLeftCalculusOfFractions

/-- The localization of the K-flat objects onto the derived category is essentially surjective
on arrows. -/
theorem kFlatQ_mapArrow_essSurj : (kFlatQ.{c, u, d} X).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow (kFlatQ X) (kFlatQuasiIso X.O)

attribute [local instance] kFlatQ_mapArrow_essSurj

/-- For any complex `B`, the functor `- ⊗^L_O B` on the derived category descends
`Tot(- ⊗_O B)` on the K-flat objects of the homotopy category along
`Stacks.SheafOfModules.kFlatQ`. -/
@[instance_reducible]
def derivedTensorFlipObjLifting
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    Localization.Lifting (kFlatQ.{c, u, d} X) (kFlatQuasiIso.{c, u, u} X.O)
      ((kFlatObjects.{c, u, u} X.O).ι ⋙
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
          DerivedCategory.Qh)
      ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B)) := by
  letI := Localization.Lifting₂.snd (kFlatComplexQ X) DerivedCategory.Q
    (kFlatComplexQuasiIso X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (kFlatTensorToDerived X) (derivedTensorBifunctor X) B
  letI : Localization.Lifting
      (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
      ((HomologicalComplex.homotopyEquivalences
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up
          ℤ)).inverseImage
          (kFlatComplexes X).ι)
      ((kFlatTensorToDerived X).flip.obj B)
      (kFlatQ.{c, u, d} X ⋙ (derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B)) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (ObjectProperty.complexSubcategoryQuotientCompIso (kFlatObjects.{c, u, u} X.O))
        ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B)) ≪≫
      Localization.Lifting.iso (kFlatComplexQ X) (kFlatComplexQuasiIso X)
        ((kFlatTensorToDerived X).flip.obj B)
        ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B))⟩
  letI : Localization.Lifting
      (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
      ((HomologicalComplex.homotopyEquivalences
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up
          ℤ)).inverseImage
          (kFlatComplexes X).ι)
      ((kFlatTensorToDerived X).flip.obj B)
      ((kFlatObjects.{c, u, u} X.O).ι ⋙
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
          DerivedCategory.Qh) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (ObjectProperty.liftCompιIso (kFlatObjects.{c, u, u} X.O) _ _)
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
          DerivedCategory.Qh) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (kFlatComplexes X).ι
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B) DerivedCategory.Qh ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj B)
            (DerivedCategory.quotientCompQhIso _))⟩
  exact ⟨Localization.liftNatIso
    (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
    ((HomologicalComplex.homotopyEquivalences
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up
        ℤ)).inverseImage
        (kFlatComplexes X).ι)
    ((kFlatTensorToDerived X).flip.obj B) ((kFlatTensorToDerived X).flip.obj B)
    _ _ (Iso.refl _) |>.symm⟩

/-- **Exactness in the first variable, for any second factor.** -/
theorem exists_commShift_isTriangulated_flip_obj_complex
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ s : ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B)).CommShift ℤ,
      letI := s
      ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B)).IsTriangulated := by
  let _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
  have _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR_isTriangulated
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
  let _ := derivedTensorFlipObjLifting X B
  let _ := Functor.commShiftOfLocalization (kFlatQ.{c, u, d} X) (kFlatQuasiIso X.O) ℤ
    ((kFlatObjects.{c, u, u} X.O).ι ⋙
      Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR (Stacks.SheafOfModules.Tensor.sheafTensor
        X.O) B ⋙
        DerivedCategory.Qh)
    ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B))
  exact ⟨inferInstance, Functor.isTriangulated_of_localization (kFlatQ.{c, u, d} X)
    (kFlatQuasiIso X.O) _ _⟩

/-- **Exactness of the derived tensor product in its first variable**: fixing the second
argument gives an exact functor of triangulated categories. -/
theorem exists_commShift_isTriangulated_flip_obj
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ s : ((derivedTensorBifunctor X).flip.obj M).CommShift ℤ,
      letI := s; ((derivedTensorBifunctor X).flip.obj M).IsTriangulated := by
  obtain ⟨B, _, ⟨e⟩⟩ := exists_kFlat_iso X M
  exact exists_commShift_isTriangulated_of_iso ((derivedTensorBifunctor X).flip.mapIso e)
    (exists_commShift_isTriangulated_flip_obj_complex X B)

end Stacks.SheafOfModules

end
