module

public import StacksFrontier.Algebra.Homology.InternalHomComplex
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedBifunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure

/-!
# The derived tensor product commutes with direct sums

Let `(X, O_X)` be a ringed space and let `K` be an object of `D(O_X)`.  Then
`K ⊗^L_{O_X} -` and `- ⊗^L_{O_X} K` carry an arbitrary direct sum of `D(O_X)` to a direct sum:
the canonical cofan `(K ⊗^L A_i ⟶ K ⊗^L ⨁_i A_i)` is again a coproduct.  The monoidal
structure is the one of Tag 0FPT, `Stacks.Cohomology.MonoidalDerived`
`.derivedCategoryMonoidalCategory`, and the direct sums are the ones of Tag 0A5L at the
locally small model, `Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory`.

## Main definitions

* `CochainComplex.KFlatMonoidal.derivedTensorLeftLift`: for a K-flat complex `P`, the descent
  of `Q ∘ (P ⊗ -)` to `D(A)`.
* `CochainComplex.KFlatMonoidal.homotopyTensorLeftIso`: the isomorphism `[P] ⊗ [L] ≅ [P ⊗ L]`
  in `K(A)`, natural in the complex `L`.

## Main results

* `CategoryTheory.Localization.preservesColimitsOfShape_of_lifting`: coproduct preservation
  transports from a functor to its descent along a localization functor.
* `CochainComplex.KFlatMonoidal.derivedTensorLeftLiftIso`: the descent of `Q ∘ (P ⊗ -)` is
  `Q(P) ⊗ -`.
* `CochainComplex.KFlatMonoidal.preservesColimitsOfShape_tensorLeft`: the derived tensor product
  of a monoidal abelian category commutes with direct sums.
* `Stacks.SheafOfModules.DerivedMonoidal.preservesColimitsOfShape_derivedTensorLeft`: the same
  for the derived category of modules on a ringed site.
* `Stacks.Cohomology.MonoidalDerived.preservesCoproducts_derivedTensorLeft` and
  `preservesCoproducts_derivedTensorRight`: the same on a ringed space, in both variables.
* `Stacks.Cohomology.MonoidalDerived.isColimit_tensorLeft_mapCocone`: the cofan
  `(K ⊗^L A_i ⟶ K ⊗^L ⨁_i A_i)` is a coproduct.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0A5L](https://stacks.math.columbia.edu/tag/0A5L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization

universe w v u

namespace CategoryTheory.Localization

/-- If `G : D ⥤ D` lifts `F ⋙ L` along a localization functor `L : C ⥤ D`, and both `L` and `F`
preserve `J`-indexed coproducts, then so does `G`. -/
theorem preservesColimitsOfShape_of_lifting {C : Type*} [Category C] {D : Type*} [Category D]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] (F : C ⥤ C) (G : D ⥤ D)
    [Localization.Lifting L W (F ⋙ L) G] (J : Type*)
    [HasColimitsOfShape (Discrete J) C]
    [PreservesColimitsOfShape (Discrete J) L]
    [PreservesColimitsOfShape (Discrete J) F] :
    PreservesColimitsOfShape (Discrete J) G := by
  have hes : L.EssSurj := Localization.essSurj L W
  have e : L ⋙ G ≅ F ⋙ L := Localization.Lifting.iso L W (F ⋙ L) G
  refine ⟨fun {K} ↦ ?_⟩
  let K₀ : Discrete J ⥤ C := Discrete.functor fun j ↦ L.objPreimage (K.obj ⟨j⟩)
  have : PreservesColimit K₀ (L ⋙ G) := preservesColimit_of_natIso K₀ e.symm
  have : PreservesColimit (K₀ ⋙ L) G := preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves L (colimit.isColimit K₀))
    (isColimitOfPreserves (L ⋙ G) (colimit.isColimit K₀) :
      IsColimit (G.mapCocone (L.mapCocone (colimit.cocone K₀))))
  exact preservesColimit_of_iso_diagram G
    (Discrete.natIso fun j ↦ L.objObjPreimageIso (K.obj ⟨j.as⟩) : K₀ ⋙ L ≅ K)

end CategoryTheory.Localization

namespace CochainComplex.KFlatMonoidal

open CochainComplex.KFlatBifunctor

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

attribute [local instance] homotopyMonoidal homotopyBraided

/-- For a complex `P`, the isomorphism `[P] ⊗ [L] ≅ [P ⊗ L]` in `K(A)`, natural in the complex
`L`, with components `homotopyMu`. -/
def homotopyTensorLeftIso (P : CochainComplex A ℤ) :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        tensorLeft ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ≅
      tensorLeft P ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ) :=
  NatIso.ofComponents (fun L ↦ homotopyMu A P L)
    (fun {_ _} g ↦ homotopyMu_natural_right A P g)

section Descent

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  {P : CochainComplex A ℤ}

/-- For `P` K-flat, `Q ∘ (P ⊗ -)` inverts quasi-isomorphisms. -/
theorem tensorLeft_comp_Q_inverts
    (hP : CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P) :
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).IsInvertedBy
      (tensorLeft P ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have : QuasiIso ((tensorLeft P).map f) :=
    CochainComplex.KFlatBifunctor.quasiIso_of_kFlatLeft (curriedTensor A) P
      (kFlatLeft_of_kFlat A hP) f (by simpa using hf)
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map ((tensorLeft P).map f)))

/-- For `P` K-flat, the functor `D(A) ⥤ D(A)` induced by `Q ∘ (P ⊗ -)`. -/
def derivedTensorLeftLift (hP : CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P) :
    DerivedCategory A ⥤ DerivedCategory A :=
  Localization.lift (tensorLeft P ⋙ DerivedCategory.Q) (tensorLeft_comp_Q_inverts A hP)
    DerivedCategory.Q

/-- `derivedTensorLeftLift` lifts `Q ∘ (P ⊗ -)` along `Q`. -/
instance liftingDerivedTensorLeftLift
    (hP : CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P) :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      (tensorLeft P ⋙ DerivedCategory.Q) (derivedTensorLeftLift A hP) := by
  unfold derivedTensorLeftLift
  infer_instance

/-- The composite of `Qh : K(A) ⥤ D(A)` with `derivedTensorLeftLift` is isomorphic to
`[P] ⊗ -` followed by `Qh`. -/
def derivedTensorLeftLiftHomotopyIso
    (hP : CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P) :
    DerivedCategory.Qh (C := A) ⋙ derivedTensorLeftLift A hP ≅
      tensorLeft ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ⋙
        DerivedCategory.Qh := by
  letI : Localization.Lifting (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (tensorLeft P ⋙ DerivedCategory.Q)
      (DerivedCategory.Qh (C := A) ⋙ derivedTensorLeftLift A hP) :=
    ⟨Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) _ ≪≫
      Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
        (tensorLeft P ⋙ DerivedCategory.Q) (derivedTensorLeftLift A hP)⟩
  letI : Localization.Lifting (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (tensorLeft P ⋙ DerivedCategory.Q)
      (tensorLeft ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ⋙
        DerivedCategory.Qh) :=
    ⟨Functor.isoWhiskerRight (homotopyTensorLeftIso A P) DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft (tensorLeft P) (DerivedCategory.quotientCompQhIso A)⟩
  exact Localization.liftNatIso (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (tensorLeft P ⋙ DerivedCategory.Q) (tensorLeft P ⋙ DerivedCategory.Q) _ _ (Iso.refl _)

end Descent

section Comparison

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  [(kFlatQ (curriedTensor A)).IsLocalization (kFlatQuasiIso (curriedTensor A))]
  {P : CochainComplex A ℤ}

/-- Tensoring in `D(A)` with the image of a K-flat object `U` of `K(A)` lifts `U ⊗ -` along
`kFlatQ`. -/
@[instance_reducible]
def derivedLocalizedTensorLiftingObj (U : (kFlatObjects (curriedTensor A)).FullSubcategory) :
    Localization.Lifting (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
      (tensorLeft U ⋙ kFlatQ (curriedTensor A))
      ((derivedLocalizedTensor A).obj ((kFlatQ (curriedTensor A)).obj U)) :=
  inferInstanceAs (Localization.Lifting
    (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
      (kFlatQuasiIso (curriedTensor A)) (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))))
    (kFlatQuasiIso (curriedTensor A))
    (tensorLeft U ⋙ Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
      (kFlatQuasiIso (curriedTensor A)) (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))))
    ((Localization.Monoidal.tensorBifunctor (kFlatQ (curriedTensor A))
        (kFlatQuasiIso (curriedTensor A))
        (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))).obj
      ((Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
        (kFlatQuasiIso (curriedTensor A))
        (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))).obj U)))

/-- For `P` K-flat, `derivedTensorLeftLift` lifts tensoring with the class of `P` in the full
monoidal subcategory of K-flat objects of `K(A)` along `kFlatQ`. -/
@[instance_reducible]
def derivedTensorLeftLiftKFlatLifting
    (hP : CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P) :
    Localization.Lifting (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
      (tensorLeft (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P, hP⟩ :
          (kFlatObjects (curriedTensor A)).FullSubcategory) ⋙ kFlatQ (curriedTensor A))
      (derivedTensorLeftLift A hP) :=
  ⟨Functor.isoWhiskerLeft (kFlatObjects (curriedTensor A)).ι
    (derivedTensorLeftLiftHomotopyIso A hP) ≪≫ Iso.refl _⟩

/-- For `P` K-flat, the functor `derivedTensorLeftLift` induced by `Q ∘ (P ⊗ -)` is isomorphic to
tensoring in `D(A)` with the class of `P`. -/
def derivedTensorLeftLiftIso
    (hP : CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P) :
    derivedTensorLeftLift A hP ≅
      (derivedLocalizedTensor A).obj ((kFlatQ (curriedTensor A)).obj
        ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P, hP⟩) :=
  letI := derivedTensorLeftLiftKFlatLifting A hP
  letI := derivedLocalizedTensorLiftingObj A
    (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P, hP⟩ :
      (kFlatObjects (curriedTensor A)).FullSubcategory)
  Localization.liftNatIso (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
    (tensorLeft (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P, hP⟩ :
      (kFlatObjects (curriedTensor A)).FullSubcategory) ⋙ kFlatQ (curriedTensor A))
    (tensorLeft (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P, hP⟩ :
      (kFlatObjects (curriedTensor A)).FullSubcategory) ⋙ kFlatQ (curriedTensor A))
    _ _ (Iso.refl _)

/-- Tensoring in `D(A)` with the class of a K-flat complex preserves `J`-indexed coproducts. -/
theorem preservesColimitsOfShape_derivedLocalizedTensor_obj_Q
    (hP : CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P) (J : Type*)
    [HasColimitsOfShape (Discrete J) (CochainComplex A ℤ)]
    [PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := A))]
    [PreservesColimitsOfShape (Discrete J) (tensorLeft P)] :
    PreservesColimitsOfShape (Discrete J)
      ((derivedLocalizedTensor A).obj (DerivedCategory.Q.obj P)) := by
  let := derivedTensorLeftLiftKFlatLifting A hP
  have h : PreservesColimitsOfShape (Discrete J) (derivedTensorLeftLift A hP) :=
    Localization.preservesColimitsOfShape_of_lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (tensorLeft P)
      (derivedTensorLeftLift A hP) J
  have h' : PreservesColimitsOfShape (Discrete J)
      ((derivedLocalizedTensor A).obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P))) :=
    preservesColimitsOfShape_of_natIso (derivedTensorLeftLiftIso A hP)
  exact preservesColimitsOfShape_of_natIso
    ((derivedLocalizedTensor A).mapIso (derivedQIso A P))

end Comparison

section Coproducts

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]

/-- If every complex has a K-flat resolution, then for every `K` in `D(A)` the derived tensor
product `K ⊗ -` preserves `J`-indexed coproducts. -/
theorem preservesColimitsOfShape_tensorLeft
    (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)
    (K : DerivedCategory A) (J : Type*)
    [HasColimitsOfShape (Discrete J) (CochainComplex A ℤ)]
    [PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := A))]
    [∀ P : CochainComplex A ℤ, PreservesColimitsOfShape (Discrete J) (tensorLeft P)] :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := derivedMonoidal A hres
    PreservesColimitsOfShape (Discrete J) (tensorLeft K) := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  obtain ⟨P, f, hP, hf⟩ := hres (DerivedCategory.Q.objPreimage K)
  have e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have h := preservesColimitsOfShape_derivedLocalizedTensor_obj_Q A hP J
  exact preservesColimitsOfShape_of_natIso ((derivedLocalizedTensor A).mapIso e)

end Coproducts

end CochainComplex.KFlatMonoidal

namespace Stacks.SheafOfModules.DerivedMonoidal

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

universe d

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

/-- On the derived category of modules on a ringed site, `K ⊗^L -` preserves direct sums indexed
by a type in the universe of the site. -/
theorem preservesColimitsOfShape_derivedTensorLeft (K : DerivedModules R) (ι : Type u) :
    letI := derivedMonoidal R
    PreservesColimitsOfShape (Discrete ι) (tensorLeft K) := by
  let : ∀ P : CochainComplex (Mod R) ℤ,
      PreservesColimitsOfShape (Discrete ι) (tensorLeft P) := fun P ↦
    ((CochainComplex.internalHomAdjunction
      P).leftAdjoint_preservesColimits).preservesColimitsOfShape
  let : PreservesColimitsOfShape (Discrete ι) (DerivedCategory.Q (C := Mod R)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts (Mod R) ι
  exact CochainComplex.KFlatMonoidal.preservesColimitsOfShape_tensorLeft (Mod R)
    (exists_kFlat_resolution R) K ι

end Stacks.SheafOfModules.DerivedMonoidal

namespace Stacks.Cohomology.MonoidalDerived

open AlgebraicGeometry Stacks.SheafOfModules.DerivedMonoidal

universe d

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (Mod X.sheaf)]

/-- On a ringed space `X`, `K ⊗^L_{O_X} -` commutes with direct sums in `D(O_X)`, for the
monoidal structure of Tag 0FPT and the direct sums of Tag 0A5L. -/
theorem preservesCoproducts_derivedTensorLeft (K : DerivedModules X.sheaf) (ι : Type u) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    PreservesColimitsOfShape (Discrete ι) (MonoidalCategory.tensorLeft K) :=
  Stacks.SheafOfModules.DerivedMonoidal.preservesColimitsOfShape_derivedTensorLeft X.sheaf K ι

/-- On a ringed space `X`, `- ⊗^L_{O_X} K` commutes with direct sums in `D(O_X)`. -/
theorem preservesCoproducts_derivedTensorRight (K : DerivedModules X.sheaf) (ι : Type u) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategorySymmetricCategory.{u, d} X
    letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    PreservesColimitsOfShape (Discrete ι) (MonoidalCategory.tensorRight K) := by
  let := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
  let := Stacks.Cohomology.MonoidalDerived.derivedCategorySymmetricCategory.{u, d} X
  let := preservesCoproducts_derivedTensorLeft X K ι
  exact preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight K)

/-- For a family `A` of objects of `D(O_X)`, the cofan `(K ⊗^L_{O_X} A i ⟶ K ⊗^L_{O_X} ⨁_i A i)`
whose legs are `K ◁ ι_i` is a direct sum. -/
def isColimit_tensorLeft_mapCocone (K : DerivedModules X.sheaf) {ι : Type u}
    (A : ι → DerivedModules X.sheaf) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    IsColimit ((MonoidalCategory.tensorLeft K).mapCocone
      (colimit.cocone (Discrete.functor A))) := by
  letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
  letI : HasCoproducts.{u} (DerivedModules X.sheaf) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  letI := preservesCoproducts_derivedTensorLeft X K ι
  exact isColimitOfPreserves (MonoidalCategory.tensorLeft K)
    (colimit.isColimit (Discrete.functor A))

end Stacks.Cohomology.MonoidalDerived

end
