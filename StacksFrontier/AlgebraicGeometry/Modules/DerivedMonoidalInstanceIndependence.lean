module

public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.InstanceIndependence
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleTransport
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# Invertibility in the derived category does not depend on the chosen model

`HasDerivedCategory C` is a chosen localization of the cochain complexes at the
quasi-isomorphisms, so the monoidal structure of `D(A)` built from K-flat resolutions
(`CochainComplex.KFlatMonoidal.derivedMonoidal`) is a priori a different structure for each choice.
For an object represented by a complex `K`, invertibility is nevertheless the same condition at
every model: on K-flat complexes the derived tensor product is the image of the total tensor
product of complexes, so `Q K` is invertible exactly when there are K-flat complexes `P`, `P'`
with `Q P ≅ Q K`, `Q (P ⊗ P') ≅ Q 𝟙` and `Q (P' ⊗ P) ≅ Q 𝟙`, and isomorphisms between images of
complexes transport between models by `CategoryTheory.DerivedCategory.transferQObjIso`.

## Main results

* `CochainComplex.KFlatMonoidal.isInvertible_Q_iff`: the characterization above.
* `CochainComplex.KFlatMonoidal.isInvertible_Q_transfer`: invertibility of `Q K` transports
  between any two models.
* `AlgebraicGeometry.Scheme.Modules.isInvertible_Q_transfer`: the same for `D(𝒪_X)` with its
  monoidal structure `AlgebraicGeometry.Scheme.Modules.derivedMonoidal`.
* `AlgebraicGeometry.Scheme.Modules.isInvertible_standard_iff`: an object of `D(𝒪_X)` is
  invertible at the standard model exactly when it is invertible at the locally small model, the
  two models having the same objects.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe w w' v u

namespace CochainComplex.KFlatMonoidal



variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)

/-- **Invertibility of the image of a complex, through K-flat complexes.** `Q K` is invertible in
`D(A)` exactly when there are K-flat complexes `P` and `P'` with `Q P ≅ Q K` and with
`Q (P ⊗ P')` and `Q (P' ⊗ P)` both isomorphic to `Q 𝟙`. -/
theorem isInvertible_Q_iff [HasDerivedCategory.{w} A] (K : CochainComplex A ℤ) :
    letI := derivedMonoidal A hres
    IsInvertible (DerivedCategory.Q.obj K) ↔
      ∃ P P' : CochainComplex A ℤ, CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧
        CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P' ∧
        Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K) ∧
        Nonempty (DerivedCategory.Q.obj (P ⊗ P') ≅
          DerivedCategory.Q.obj (𝟙_ (CochainComplex A ℤ))) ∧
        Nonempty (DerivedCategory.Q.obj (P' ⊗ P) ≅
          DerivedCategory.Q.obj (𝟙_ (CochainComplex A ℤ))) := by
  let := derivedMonoidal A hres
  constructor
  · rintro ⟨h⟩
    obtain ⟨P, f, hP, hf⟩ := hres K
    obtain ⟨P', f', hP', hf'⟩ := hres (DerivedCategory.Q.objPreimage h.inv)
    let eP : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K := asIso (DerivedCategory.Q.map f)
    let eP' : DerivedCategory.Q.obj P' ≅ h.inv :=
      asIso (DerivedCategory.Q.map f') ≪≫ DerivedCategory.Q.objObjPreimageIso h.inv
    exact ⟨P, P', hP, hP', ⟨eP⟩,
      ⟨(derivedTensorIso A hres hP hP').symm ≪≫ tensorIso eP eP' ≪≫ h.isoLeft ≪≫
        derivedUnitIso A hres⟩,
      ⟨(derivedTensorIso A hres hP' hP).symm ≪≫ tensorIso eP' eP ≪≫ h.isoRight ≪≫
        derivedUnitIso A hres⟩⟩
  · rintro ⟨P, P', hP, hP', ⟨eP⟩, ⟨e₁⟩, ⟨e₂⟩⟩
    exact ⟨⟨DerivedCategory.Q.obj P',
      whiskerRightIso eP.symm _ ≪≫ derivedTensorIso A hres hP hP' ≪≫ e₁ ≪≫
        (derivedUnitIso A hres).symm,
      whiskerLeftIso _ eP.symm ≪≫ derivedTensorIso A hres hP' hP ≪≫ e₂ ≪≫
        (derivedUnitIso A hres).symm⟩⟩

/-- **Invertibility of the image of a complex does not depend on the model of `D(A)`**: if `Q K`
is invertible for one choice of `HasDerivedCategory A`, it is invertible for any other. -/
theorem isInvertible_Q_transfer (inst₁ : HasDerivedCategory.{w} A)
    (inst₂ : HasDerivedCategory.{w'} A) (K : CochainComplex A ℤ)
    (h : letI := inst₁; letI := derivedMonoidal A hres
      IsInvertible (DerivedCategory.Q.obj K)) :
    letI := inst₂; letI := derivedMonoidal A hres
    IsInvertible (DerivedCategory.Q.obj K) := by
  obtain ⟨P, P', hP, hP', ⟨eP⟩, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    (let := inst₁; isInvertible_Q_iff A hres K).1 h
  exact (let := inst₂; isInvertible_Q_iff A hres K).2
    ⟨P, P', hP, hP', ⟨DerivedCategory.transferQObjIso inst₁ inst₂ _ _ eP⟩,
      ⟨DerivedCategory.transferQObjIso inst₁ inst₂ _ _ e₁⟩,
      ⟨DerivedCategory.transferQObjIso inst₁ inst₂ _ _ e₂⟩⟩

end CochainComplex.KFlatMonoidal

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

/-- **Invertibility of the image of a complex of `O`-modules on a ringed site does not depend on
the model of `D(O)`**, for the monoidal structure of [Stacks, Tag 0FPT]. -/
theorem isInvertible_Q_transfer (inst₁ : HasDerivedCategory.{w} (Mod R))
    (inst₂ : HasDerivedCategory.{w'} (Mod R)) (K : Complexes R)
    (h : @MonoidalCategory.IsInvertible _ _ (@derivedMonoidal C _ J R _ _ inst₁)
      ((@DerivedCategory.Q (Mod R) _ _ inst₁).obj K)) :
    @MonoidalCategory.IsInvertible _ _ (@derivedMonoidal C _ J R _ _ inst₂)
      ((@DerivedCategory.Q (Mod R) _ _ inst₂).obj K) :=
  CochainComplex.KFlatMonoidal.isInvertible_Q_transfer (Mod R) (exists_kFlat_resolution R)
    inst₁ inst₂ K h

end Stacks.SheafOfModules.DerivedMonoidal

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- **Invertibility of the image of a complex of `𝒪_X`-modules does not depend on the model of
`D(𝒪_X)`**, for the monoidal structure `AlgebraicGeometry.Scheme.Modules.derivedMonoidal`. -/
theorem isInvertible_Q_transfer (inst₁ : HasDerivedCategory.{w} X.Modules)
    (inst₂ : HasDerivedCategory.{w'} X.Modules) (K : CochainComplex X.Modules ℤ)
    (h : @MonoidalCategory.IsInvertible _ _ (@derivedMonoidal X inst₁)
      ((@DerivedCategory.Q X.Modules _ _ inst₁).obj K)) :
    @MonoidalCategory.IsInvertible _ _ (@derivedMonoidal X inst₂)
      ((@DerivedCategory.Q X.Modules _ _ inst₂).obj K) :=
  Stacks.SheafOfModules.DerivedMonoidal.isInvertible_Q_transfer (C := X.Opens) X.sheaf
    inst₁ inst₂ K h

/-- Invertibility transports along isomorphisms with images of one complex at two models. -/
private theorem isInvertible_of_iso_Q_transfer (inst₁ : HasDerivedCategory.{w} X.Modules)
    (inst₂ : HasDerivedCategory.{w'} X.Modules) (K : CochainComplex X.Modules ℤ)
    (E₁ : @DerivedCategory X.Modules _ _ inst₁) (E₂ : @DerivedCategory X.Modules _ _ inst₂)
    (e₁ : (@DerivedCategory.Q X.Modules _ _ inst₁).obj K ≅ E₁)
    (e₂ : (@DerivedCategory.Q X.Modules _ _ inst₂).obj K ≅ E₂)
    (h : @MonoidalCategory.IsInvertible _ _ (@derivedMonoidal X inst₁) E₁) :
    @MonoidalCategory.IsInvertible _ _ (@derivedMonoidal X inst₂) E₂ :=
  @isInvertible_of_iso _ _ (@derivedMonoidal X inst₂) _ _ e₂
    (isInvertible_Q_transfer X inst₁ inst₂ K
      (@isInvertible_of_iso _ _ (@derivedMonoidal X inst₁) _ _ e₁.symm h))

/-- **An object of `D(𝒪_X)` is invertible at the standard model exactly when it is invertible at
the locally small model.** The two models have the same objects; an object is the image of a
complex in both, and invertibility of such an image is model independent
(`AlgebraicGeometry.Scheme.Modules.isInvertible_Q_transfer`). -/
theorem isInvertible_standard_iff (E : DerivedCategory X.Modules) :
    @MonoidalCategory.IsInvertible
        (@DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)) _
        (@derivedMonoidal X (HasDerivedCategory.standard _)) E ↔
      @MonoidalCategory.IsInvertible (DerivedCategory X.Modules) _ (derivedMonoidal X) E := by
  let C := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj C ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let e' : @Iso (@DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)) _
      ((@DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard _)).obj C) E :=
    (StacksDraft.DerivedModel.schemeModulesComparison X).inverse.mapIso e
  exact ⟨isInvertible_of_iso_Q_transfer X _ _ C _ _ e' e,
    isInvertible_of_iso_Q_transfer X _ _ C _ _ e e'⟩

end AlgebraicGeometry.Scheme.Modules

end
