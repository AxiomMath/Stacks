module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.LeftResolution
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules
public import Mathlib.CategoryTheory.Localization.Bifunctor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Iso
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleKFlatComparison.KFlatHomotopyTensor
import all StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleKFlatComparison.KFlatHomotopyTensor

/-!
# The derived tensor product of inverse systems of modules

The derived tensor bifunctor on compatible module systems, its exactness and symmetry, its
comparison with the left derived functor of the total tensor product, the evaluation
comparisons at K-flat components, and Stacks 091H.
-/

open Stacks.HomologyColimit

/-! ### Construction of the derived tensor product -/

section Construction

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory Opposite
open scoped ZeroObject

universe u t w u₁ u₂ v₁ v₂

namespace ModuleSystemKFlatComparison

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] systemsMonoidalStruct systemsMonoidal liftedModuleSymmetric
  systemsSymmetric systemsMonoidalPreadditive systemsHasTensor

open CategoryTheory.LocalizerMorphism

/-- The total tensor functor on a componentwise K-flat homotopy object and an arbitrary
homotopy object, with values in the derived category. -/
private noncomputable abbrev resolvedTensor (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :
    (kFlatHomotopySystems.{u, t} A).FullSubcategory ⥤
      HomotopyCategory (Modules.{u, t} A) (.up ℤ) ⥤ DerivedCategory (Modules.{u, t} A) :=
  (kFlatHomotopySystems.{u, t} A).ι ⋙ homotopyTensor ⋙
    (CategoryTheory.Functor.whiskeringRight _ _ _).obj DerivedCategory.Qh

/-- A quasi-isomorphism of complexes becomes invertible in the derived category. -/
private lemma isIso_Qh_map_quotient_map {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory.{w} C] {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f)) :=
  (DerivedCategory.isIso_Qh_map_iff _).2 ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 ‹_›)

/-- Exactness (with a compatible shift structure) transfers along an isomorphism of functors. -/
private lemma exists_commShift_isTriangulated_of_iso {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory.{w} C] {F G : DerivedCategory C ⥤ DerivedCategory C} (e : F ≅ G)
    (h : ∃ c : F.CommShift ℤ, letI := c; F.IsTriangulated) :
    ∃ c : G.CommShift ℤ, letI := c; G.IsTriangulated := by
  obtain ⟨c, hc⟩ := h
  let := c
  have := hc
  let := CategoryTheory.Functor.CommShift.ofIso e ℤ
  have := CategoryTheory.Functor.CommShift.ofIso_compatibility e ℤ
  exact ⟨inferInstance, CategoryTheory.Functor.isTriangulated_of_iso e⟩

/-- The resolved tensor functor inverts quasi-isomorphisms in both variables. -/
private lemma resolvedTensor_inverts (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :
    MorphismProperty.IsInvertedBy₂
      ((HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).inverseImage
        (kFlatHomotopySystems.{u, t} A).ι)
      (HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)) (resolvedTensor A) := by
  intro X Y f hf
  obtain ⟨f₁, hf₁⟩ := (HomotopyCategory.quotient (Modules.{u, t} A) (.up ℤ)).map_surjective f.1.hom
  obtain ⟨f₂, hf₂⟩ := (HomotopyCategory.quotient (Modules.{u, t} A) (.up ℤ)).map_surjective f.2
  have h₁ : QuasiIso f₁ := (HomotopyCategory.quotient_map_mem_quasiIso_iff f₁).1
    (by rw [hf₁]; exact hf.1)
  have h₂ : QuasiIso f₂ := (HomotopyCategory.quotient_map_mem_quasiIso_iff f₂).1
    (by rw [hf₂]; exact hf.2)
  have := tensor_left_inverts A _ Y.1.property f₂
  have := tensor_right_inverts_between_kFlat A X.1.property Y.1.property f₁ X.2.as
  change IsIso (DerivedCategory.Qh.map
    (((homotopyTensor.map f.1.hom).app X.2)) ≫
      DerivedCategory.Qh.map ((homotopyTensor.obj Y.1.obj).map f.2))
  rw [← hf₁, ← hf₂]
  change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      ((TrightCochain X.2.as).map f₁)) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      ((TleftCochain Y.1.obj.as).map f₂)))
  have := isIso_Qh_map_quotient_map ((TrightCochain X.2.as).map f₁)
  have := isIso_Qh_map_quotient_map ((TleftCochain Y.1.obj.as).map f₂)
  infer_instance

/-- The derived tensor bifunctor of compatible systems of modules. -/
private noncomputable def tensorOnDerivedSystems (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :
    DerivedCategory (Modules.{u, t} A) ⥤ DerivedCategory (Modules.{u, t} A) ⥤ DerivedCategory
      (Modules.{u, t} A) := by
  have := kFlatHomotopySystems_isLocalization A
  exact Localization.lift₂ (resolvedTensor A) (resolvedTensor_inverts A)
    ((kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh) DerivedCategory.Qh

attribute [local instance] kFlatHomotopySystems_isLocalization

/-- The derived tensor bifunctor lifts tensoring a K-flat homotopy object. -/
private local instance tensorOnDerivedSystems_lifting (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :
    Localization.Lifting₂ ((kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh)
      DerivedCategory.Qh
      ((HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).inverseImage
        (kFlatHomotopySystems.{u, t} A).ι)
      (HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ))
      (resolvedTensor A) (tensorOnDerivedSystems A) := by
  dsimp only [tensorOnDerivedSystems]
  infer_instance

/-- Tensoring on the left by a resolved object is exact on the derived category. -/
private lemma tensorOnDerivedSystems_exact_right_resolved (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)]
    (K : (kFlatHomotopySystems.{u, t} A).FullSubcategory) :
    ∃ e : ((tensorOnDerivedSystems A).obj (DerivedCategory.Qh.obj K.obj)).CommShift ℤ,
      letI := e
      ((tensorOnDerivedSystems A).obj (DerivedCategory.Qh.obj K.obj)).IsTriangulated := by
  obtain ⟨e, he⟩ := TotalTensorComplex.tleft_isTriangulated K.obj.as
  let := e
  have := he
  let F : HomotopyCategory (Modules.{u, t} A) (.up ℤ) ⥤ DerivedCategory (Modules.{u, t} A) :=
    Tleft K.obj.as ⋙ DerivedCategory.Qh
  let F' := (tensorOnDerivedSystems A).obj (DerivedCategory.Qh.obj K.obj)
  let : F.CommShift ℤ := inferInstance
  have hF : F.IsTriangulated := inferInstance
  let : Localization.Lifting DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)) F F' :=
    Localization.Lifting₂.fst
    ((kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh) DerivedCategory.Qh
    ((HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).inverseImage
      (kFlatHomotopySystems.{u, t} A).ι)
    (HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ))
    (resolvedTensor A) (tensorOnDerivedSystems A) K
  let := CategoryTheory.Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)) ℤ F F'
  exact ⟨inferInstance, CategoryTheory.Functor.isTriangulated_of_precomp_iso
    (Localization.Lifting.iso DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)) F F')⟩

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring on the left by any derived object is exact. -/
private lemma tensorOnDerivedSystems_exact_right (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] (K : DerivedCategory (Modules.{u, t} A)) :
    ∃ e : ((tensorOnDerivedSystems A).obj K).CommShift ℤ,
      letI := e
      ((tensorOnDerivedSystems A).obj K).IsTriangulated := by
  let Q := (kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh
  have : Q.EssSurj := Localization.essSurj Q
    ((HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).inverseImage
      (kFlatHomotopySystems.{u, t} A).ι)
  obtain ⟨P, ⟨eP⟩⟩ := CategoryTheory.Functor.EssSurj.mem_essImage (F := Q) K
  exact exists_commShift_isTriangulated_of_iso ((tensorOnDerivedSystems A).mapIso eP)
    (tensorOnDerivedSystems_exact_right_resolved A P)

/-- Tensoring two componentwise K-flat homotopy objects. -/
private noncomputable abbrev resolvedTensorBoth (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :=
  resolvedTensor A ⋙ (CategoryTheory.Functor.whiskeringLeft _ _ _).obj (kFlatHomotopySystems.{u, t}
    A).ι

/-- The derived tensor bifunctor also lifts tensoring two resolved objects. -/
private local instance tensorOnDerivedSystems_liftingBoth (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :
    Localization.Lifting₂ ((kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh)
      ((kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh)
      ((HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).inverseImage
        (kFlatHomotopySystems.{u, t} A).ι)
      ((HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).inverseImage
        (kFlatHomotopySystems.{u, t} A).ι)
      (resolvedTensorBoth A) (tensorOnDerivedSystems A) where
  iso := CategoryTheory.Functor.isoWhiskerRight
    (Localization.Lifting₂.iso ((kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh)
      DerivedCategory.Qh
      ((HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).inverseImage
        (kFlatHomotopySystems.{u, t} A).ι)
      (HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ))
      (resolvedTensor A) (tensorOnDerivedSystems A))
    ((CategoryTheory.Functor.whiskeringLeft _ _ _).obj (kFlatHomotopySystems.{u, t} A).ι)

/-- The derived tensor product is symmetric. -/
private noncomputable def tensorOnDerivedSystemsSymmetry (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :
    tensorOnDerivedSystems A ≅ (tensorOnDerivedSystems A).flip :=
  Localization.lift₂NatIso
    ((kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh)
    ((kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh)
    ((HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).inverseImage
      (kFlatHomotopySystems.{u, t} A).ι)
    ((HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).inverseImage
      (kFlatHomotopySystems.{u, t} A).ι)
    (resolvedTensorBoth A) (resolvedTensorBoth A).flip
    (tensorOnDerivedSystems A) (tensorOnDerivedSystems A).flip
    (CategoryTheory.Functor.isoWhiskerRight
      (CategoryTheory.Functor.isoWhiskerLeft (kFlatHomotopySystems.{u, t} A).ι
        homotopyTensorSymmetry)
      ((CategoryTheory.Functor.whiskeringRight _ _ _).obj DerivedCategory.Qh ⋙
        (CategoryTheory.Functor.whiskeringLeft _ _ _).obj (kFlatHomotopySystems.{u, t} A).ι))

/-- Tensoring on the right by any derived object is exact, by symmetry. -/
private lemma tensorOnDerivedSystems_exact_left (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] (L : DerivedCategory (Modules.{u, t} A)) :
    ∃ e : ((tensorOnDerivedSystems A).flip.obj L).CommShift ℤ,
      letI := e
      ((tensorOnDerivedSystems A).flip.obj L).IsTriangulated := by
  exact exists_commShift_isTriangulated_of_iso ((tensorOnDerivedSystemsSymmetry A).app L)
    (tensorOnDerivedSystems_exact_right A L)

/-- A componentwise K-flat first argument computes the derived tensor product. -/
private noncomputable def tensorOnDerivedSystemsIso
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) [HasDerivedCategory.{w} (Modules.{u, t} A)]
    (M N : CochainComplex (Modules.{u, t} A) ℤ) (hM : HasKFlatComponents A M) :
    ((tensorOnDerivedSystems A).obj (DerivedCategory.Q.obj M)).obj (DerivedCategory.Q.obj N) ≅
      DerivedCategory.Q.obj ((TleftCochain M).obj N) :=
  ((tensorOnDerivedSystems A).mapIso
    ((DerivedCategory.quotientCompQhIso (Modules.{u, t} A)).app M).symm).app
      (DerivedCategory.Q.obj N) ≪≫
    ((tensorOnDerivedSystems A).obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj M))).mapIso
        ((DerivedCategory.quotientCompQhIso (Modules.{u, t} A)).app N).symm ≪≫
    ((Localization.Lifting₂.iso ((kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh)
      DerivedCategory.Qh
      ((HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).inverseImage
        (kFlatHomotopySystems.{u, t} A).ι)
      (HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ))
      (resolvedTensor A) (tensorOnDerivedSystems A)).app
        ⟨(HomotopyCategory.quotient _ _).obj M, hM⟩).app
          ((HomotopyCategory.quotient _ _).obj N) ≪≫
    (DerivedCategory.quotientCompQhIso (Modules.{u, t} A)).app ((TleftCochain M).obj N)

section LeftDerivedComparison

variable {C₁ C₂ H : Type*} [Category C₁] [Category C₂] [Category H]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (Φ : LocalizerMorphism W₁ W₂) [Φ.IsLeftDerivabilityStructure] (F : C₂ ⥤ H)

set_option backward.isDefEq.respectTransparency.types false in
/-- A left derivability structure detects pointwise left derivability on resolving objects. -/
private lemma hasPointwiseLeftDerivedFunctorAt_iff (X : C₁) :
    (Φ.functor ⋙ F).HasPointwiseLeftDerivedFunctorAt W₁ X ↔
      F.HasPointwiseLeftDerivedFunctorAt W₂ (Φ.functor.obj X) := by
  let e : W₂.Q.obj _ ≅ (Φ.localizedFunctor W₁.Q W₂.Q).obj _ :=
    ((Φ.catCommSq W₁.Q W₂.Q).iso).app X
  rw [F.hasPointwiseLeftDerivedFunctorAt_iff W₂.Q W₂ (Φ.functor.obj X),
    (Φ.functor ⋙ F).hasPointwiseLeftDerivedFunctorAt_iff W₁.Q W₁ X,
    TwoSquare.hasPointwiseRightKanExtensionAt_iff ((Φ.catCommSq W₁.Q W₂.Q).iso).inv,
    CategoryTheory.Functor.hasPointwiseRightKanExtensionAt_iff_of_iso W₂.Q F e]

set_option backward.isDefEq.respectTransparency false in
/-- The counit of a left derived functor is an isomorphism on resolving objects. -/
private lemma isIso_leftDerivedCounit_on_resolution (h : Φ.Derives F)
    {D : Type*} [Category D] (L : C₂ ⥤ D) [L.IsLocalization W₂]
    (LF : D ⥤ H) (α : L ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α W₂] (X : C₁) :
    IsIso (α.app (Φ.functor.obj X)) := by
  have := LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_derives Φ F h
  let E := (CategoryTheory.Functor.RightExtension.mk LF α).compTwoSquare
    ((Φ.catCommSq W₁.Q L).iso).inv
  have hE : E.left.IsLeftDerivedFunctor E.hom W₁ := ⟨
    ((LF.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor α W₂).compTwoSquare
      ((Φ.catCommSq W₁.Q L).iso).inv).isRightKanExtension⟩
  have hα : IsIso E.hom :=
    CategoryTheory.Functor.isIso_of_isLeftDerivedFunctor_of_inverts E.left E.hom h
  have hx : IsIso (E.hom.app X) := inferInstance
  change IsIso (𝟙 _ ≫ LF.map (((Φ.catCommSq W₁.Q L).iso).inv.app X) ≫
    𝟙 _ ≫ α.app (Φ.functor.obj X)) at hx
  simpa only [Category.id_comp, isIso_comp_left_iff] using hx

end LeftDerivedComparison

private abbrev kFlatLocalizer (A : ℕᵒᵖ ⥤ CommRingCat.{u}) :=
  LeftDerivedByResolutions.inclusionLocalizerMorphism
    (HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)) (kFlatHomotopySystems.{u, t} A)

private local instance kFlatLocalizer_leftDerivability (A : ℕᵒᵖ ⥤ CommRingCat.{u}) :
    (kFlatLocalizer A).IsLeftDerivabilityStructure := by
  have := kFlatHomotopySystems_hasLeftResolutions A
  exact LeftDerivedByResolutions.isLeftDerivabilityStructure_inclusionLocalizerMorphism _ _

private noncomputable abbrev homotopyTensorToDerived (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :=
  (homotopyTensor (C := Modules.{u, t} A)) ⋙
    (CategoryTheory.Functor.whiskeringRight _ _ _).obj DerivedCategory.Qh

private lemma kFlatLocalizer_derives_tensor (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :
    (kFlatLocalizer A).Derives (homotopyTensorToDerived A) := by
  intro X Y f hf
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  have h := resolvedTensor_inverts A ((f, 𝟙 N) : (X, N) ⟶ (Y, N))
    ⟨hf, (HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).id_mem N⟩
  change IsIso (((resolvedTensor A).map f).app N ≫ ((resolvedTensor A).obj Y).map (𝟙 N)) at h
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using h

private local instance homotopyTensorToDerived_hasPointwiseLeftDerivedFunctor
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) [HasDerivedCategory.{w} (Modules.{u, t} A)] :
    (homotopyTensorToDerived A).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)) :=
  LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_derives _ _
    (kFlatLocalizer_derives_tensor A)

private noncomputable abbrev tensorLeftDerived (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :=
  (homotopyTensorToDerived A).totalLeftDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ))

private noncomputable abbrev tensorLeftDerivedCounit (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :=
  (homotopyTensorToDerived A).totalLeftDerivedCounit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ))

private local instance tensorLeftDerivedCounit_isIso_on_kFlat
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) [HasDerivedCategory.{w} (Modules.{u, t} A)]
    (K : (kFlatHomotopySystems.{u, t} A).FullSubcategory) :
    IsIso ((tensorLeftDerivedCounit A).app K.obj) :=
  isIso_leftDerivedCounit_on_resolution (kFlatLocalizer A) (homotopyTensorToDerived A)
    (kFlatLocalizer_derives_tensor A) DerivedCategory.Qh
    (tensorLeftDerived A) (tensorLeftDerivedCounit A) K

private local instance tensorLeftDerived_lifting (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :
    Localization.Lifting ((kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh)
      ((HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).inverseImage
        (kFlatHomotopySystems.{u, t} A).ι)
      (resolvedTensor A) (tensorLeftDerived A) where
  iso := by
    have : IsIso (CategoryTheory.Functor.whiskerLeft (kFlatHomotopySystems.{u, t} A).ι
        (tensorLeftDerivedCounit A)) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun K => tensorLeftDerivedCounit_isIso_on_kFlat A K
    exact asIso (CategoryTheory.Functor.whiskerLeft (kFlatHomotopySystems.{u, t} A).ι
      (tensorLeftDerivedCounit A))

private noncomputable abbrev partialDerivedTensor (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :=
  tensorOnDerivedSystems A ⋙
    (CategoryTheory.Functor.whiskeringLeft _ _ _).obj DerivedCategory.Qh

private local instance partialDerivedTensor_lifting (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :
    Localization.Lifting ((kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh)
      ((HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).inverseImage
        (kFlatHomotopySystems.{u, t} A).ι)
      (resolvedTensor A) (partialDerivedTensor A) where
  iso := Localization.Lifting₂.iso ((kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh)
    DerivedCategory.Qh
    ((HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).inverseImage
      (kFlatHomotopySystems.{u, t} A).ι)
    (HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)) (resolvedTensor A)
    (tensorOnDerivedSystems A)

/-- The left derived tensor agrees with the tensor product obtained by localization. -/
private noncomputable def partialDerivedTensorIso (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] : partialDerivedTensor A ≅ tensorLeftDerived A :=
  Localization.liftNatIso ((kFlatHomotopySystems.{u, t} A).ι ⋙ DerivedCategory.Qh)
    ((HomotopyCategory.quasiIso (Modules.{u, t} A) (.up ℤ)).inverseImage
      (kFlatHomotopySystems.{u, t} A).ι)
    (resolvedTensor A) (resolvedTensor A) (partialDerivedTensor A) (tensorLeftDerived A)
    (Iso.refl _)

/-- The natural comparison from derived tensor products to tensor products of representatives. -/
private noncomputable def tensorHomotopyCounit (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :
    DerivedCategory.Qh ⋙ partialDerivedTensor A ⟶ homotopyTensorToDerived A :=
  CategoryTheory.Functor.whiskerLeft DerivedCategory.Qh (partialDerivedTensorIso A).hom ≫
    tensorLeftDerivedCounit A

private lemma tensorHomotopyCounit_isIso (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)]
    (K : (kFlatHomotopySystems.{u, t} A).FullSubcategory)
    (N : HomotopyCategory (Modules.{u, t} A) (.up ℤ)) :
    IsIso (((tensorHomotopyCounit A).app K.obj).app N) := by
  dsimp only [tensorHomotopyCounit, NatTrans.comp_app, CategoryTheory.Functor.whiskerLeft_app]
  infer_instance

set_option maxHeartbeats 800000 in
-- unfolding the evaluated tensor of K-flat components is expensive
-- (`whnf` times out at the default limit)
/-- At a fixed index, a quasi-isomorphism between K-flat components remains a
quasi-isomorphism after tensoring with any compatible complex. -/
private lemma quasiIso_evaluation_tensor_right
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ)
    {K M : CochainComplex (Modules.{u, t} A) ℤ} (f : K ⟶ M) [QuasiIso f]
    (hK : CochainComplex.KFlat ((evaluationComplex A n).obj K))
    (hM : CochainComplex.KFlat ((evaluationComplex A n).obj M)) (N : CochainComplex (Modules.{u, t}
      A) ℤ) :
    QuasiIso ((evaluationComplex A n).map ((TrightCochain N).map f)) := by
  have := quasiIso_evaluation A f n
  have hq : QuasiIso ((TrightCochain ((evaluationComplex A n).obj N)).map
      ((evaluationComplex A n).map f)) :=
    quasiIso_tright_map_between_kFlat ((evaluationComplex A n).map f)
      hK hM ((evaluationComplex A n).obj N)
  have h := evaluationTensorIso_naturality A n f (𝟙 N)
  change (evaluationTensorIso A n K N).hom ≫
    (evaluationComplex A n).map ((TrightCochain N).map f) =
      (TrightCochain ((evaluationComplex A n).obj N)).map ((evaluationComplex A n).map f) ≫
        (evaluationTensorIso A n M N).hom at h
  have hh : QuasiIso ((evaluationTensorIso A n K N).hom ≫
      (evaluationComplex A n).map ((TrightCochain N).map f)) := by
    rw [h]
    exact quasiIso_comp (hφ := hq)
      (hφ' := quasiIso_of_isIso (evaluationTensorIso A n M N).hom) _ _
  exact quasiIso_of_comp_left (hφφ' := hh) (evaluationTensorIso A n K N).hom _

attribute [local instance] HasDerivedCategory.standard

/-- A morphism is inverted after derived evaluation whenever its evaluated complex map
is a quasi-isomorphism. -/
private lemma isIso_evaluationDerived_map
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) [HasDerivedCategory.{w} (Modules.{u, t} A)] (n : ℕ)
    {K M : CochainComplex (Modules.{u, t} A) ℤ} (f : K ⟶ M)
    (hf : QuasiIso ((evaluationComplex A n).map f)) :
    IsIso ((PresheafOfModules.evaluation (A ⋙ forget₂ CommRingCat RingCat) (op
      n)).mapDerivedCategory.map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f))) := by
  let E := PresheafOfModules.evaluation (A ⋙ forget₂ CommRingCat RingCat) (op n)
  let e := CategoryTheory.Functor.isoWhiskerRight
    (DerivedCategory.quotientCompQhIso (Modules.{u, t} A)) E.mapDerivedCategory ≪≫
      E.mapDerivedCategoryFactors
  exact (NatIso.isIso_map_iff e f).2 (by
    change IsIso (DerivedCategory.Q.map ((evaluationComplex A n).map f))
    infer_instance)

/-- Evaluation of the natural tensor counit is invertible at a K-flat component. -/
private theorem isIso_evaluation_tensorHomotopyCounit
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) [HasDerivedCategory.{w} (Modules.{u, t} A)]
    (M N : CochainComplex (Modules.{u, t} A) ℤ) (n : ℕ)
    (hM : CochainComplex.KFlat ((evaluationComplex A n).obj M)) :
    IsIso ((PresheafOfModules.evaluation
      (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapDerivedCategory.map
        (((tensorHomotopyCounit A).app
          ((HomotopyCategory.quotient _ _).obj M)).app
            ((HomotopyCategory.quotient _ _).obj N))) := by
  obtain ⟨K, f, hf, _, hK⟩ := exists_surjective_kFlat_system_resolution A M
  let E := (PresheafOfModules.evaluation
    (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapDerivedCategory
  let q := HomotopyCategory.quotient (Modules.{u, t} A) (.up ℤ)
  have h := congrArg (fun t => E.map (t.app (q.obj N)))
    ((tensorHomotopyCounit A).naturality (q.map f))
  have htop := tensorHomotopyCounit_isIso A ⟨q.obj K, hK⟩ (q.obj N)
  have hright := isIso_evaluationDerived_map A n ((TrightCochain N).map f)
    (quasiIso_evaluation_tensor_right A n f (hK n) hM N)
  have hleft : IsIso (E.map (((tensorOnDerivedSystems A).map
      (DerivedCategory.Qh.map (q.map f))).app (DerivedCategory.Qh.obj (q.obj N)))) := by
    have := isIso_Qh_map_quotient_map f
    infer_instance
  dsimp only [NatTrans.comp_app, Functor.comp_map, Functor.whiskeringLeft_obj_map] at h
  rw [E.map_comp, E.map_comp] at h
  change E.map (((tensorOnDerivedSystems A).map (DerivedCategory.Qh.map (q.map f))).app
      (DerivedCategory.Qh.obj (q.obj N))) ≫
      E.map (((tensorHomotopyCounit A).app (q.obj M)).app (q.obj N)) =
    E.map (((tensorHomotopyCounit A).app (q.obj K)).app (q.obj N)) ≫
      E.map (DerivedCategory.Qh.map (q.map ((TrightCochain N).map f))) at h
  apply (isIso_comp_left_iff
    (E.map (((tensorOnDerivedSystems A).map (DerivedCategory.Qh.map (q.map f))).app
      (DerivedCategory.Qh.obj (q.obj N)))) _).1
  rw [h]
  infer_instance

/-- On representatives the derived tensor has a natural map to the total tensor. -/
private def tensorComplexCounit (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] :
    DerivedCategory.Q ⋙ tensorOnDerivedSystems A ⋙
      (Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q ⟶
    (totalTensorSystem A) ⋙ (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q := by
  let q := HomotopyCategory.quotient (Modules.{u, t} A) (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso (Modules.{u, t} A)
  let B := tensorOnDerivedSystems A
  let C := CochainComplex (Modules.{u, t} A) ℤ
  let D := DerivedCategory (Modules.{u, t} A)
  let W : (C ⥤ D) ⥤ (C ⥤ D) ⥤ (D ⥤ D ⥤ D) ⥤ C ⥤ C ⥤ D :=
    Functor.whiskeringLeft₂ D
  exact
    ((((W.mapIso e.symm).app DerivedCategory.Q).app B) ≪≫
      (((W.obj (q ⋙ DerivedCategory.Qh)).mapIso e.symm).app B)).hom ≫
    (((Functor.whiskeringLeft₂ _).obj q).obj q).map (tensorHomotopyCounit A) ≫
    Functor.whiskerLeft (totalTensorSystem A)
      ((Functor.whiskeringRight _ _ _).map e.hom)

/-- The comparison on representatives is invertible for a componentwise K-flat first factor. -/
private lemma tensorComplexCounit_isIso (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)]
    (M N : CochainComplex (Modules.{u, t} A) ℤ) (hM : HasKFlatComponents A M) :
    IsIso (((tensorComplexCounit A).app M).app N) := by
  have := tensorHomotopyCounit_isIso A
    ⟨(HomotopyCategory.quotient _ _).obj M, hM⟩ ((HomotopyCategory.quotient _ _).obj N)
  dsimp only [tensorComplexCounit, NatTrans.comp_app, Iso.trans_hom,
    Functor.whiskeringLeft₂, Functor.whiskeringLeft, Functor.whiskeringRight,
    Functor.mapIso, Iso.app, NatTrans.hcomp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj]
  infer_instance

/-- The representative comparison is invertible after evaluation at a K-flat component. -/
private lemma isIso_evaluation_tensorComplexCounit (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)]
    (M N : CochainComplex (Modules.{u, t} A) ℤ) (n : ℕ)
    (hM : CochainComplex.KFlat ((evaluationComplex A n).obj M)) :
    IsIso ((PresheafOfModules.evaluation
      (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapDerivedCategory.map
        (((tensorComplexCounit A).app M).app N)) := by
  have := isIso_evaluation_tensorHomotopyCounit A M N n hM
  -- Unfold at the level of `Modules A` only, so that the target derived category of the
  -- evaluation keeps its syntactic form (its `Category` instance is not re-synthesizable
  -- after `Functor.comp_obj` rewrites the ring).
  have key : ((tensorComplexCounit A).app M).app N =
      (((tensorOnDerivedSystems A).map
          ((DerivedCategory.quotientCompQhIso (Modules.{u, t} A)).symm.hom.app M)).app
            (DerivedCategory.Q.obj N) ≫
        ((tensorOnDerivedSystems A).obj (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (Modules.{u, t} A) (.up ℤ)).obj M))).map
            ((DerivedCategory.quotientCompQhIso (Modules.{u, t} A)).symm.hom.app N)) ≫
      ((tensorHomotopyCounit A).app
          ((HomotopyCategory.quotient (Modules.{u, t} A) (.up ℤ)).obj M)).app
            ((HomotopyCategory.quotient (Modules.{u, t} A) (.up ℤ)).obj N) ≫
        (DerivedCategory.quotientCompQhIso (Modules.{u, t} A)).hom.app
          (((totalTensorSystem A).obj M).obj N) := by
    dsimp only [tensorComplexCounit, NatTrans.comp_app, Iso.trans_hom,
      Functor.whiskeringLeft₂, Functor.whiskeringLeft, Functor.whiskeringRight,
      Functor.mapIso, Iso.app, NatTrans.hcomp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj]
  rw [key, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

set_option maxHeartbeats 800000 in
-- the evaluated monoidal structure on total complexes is expensive to unfold
-- (`whnf` times out at the default limit)
/-- Evaluation of total tensor is a natural isomorphism of bifunctors. -/
private def totalTensorEvaluationNatIso (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ) :
    evaluationComplex.{u, t} A n ⋙
      (curriedTensor (ModuleCat.{max u t} (A.obj (op n)))).map₂CochainComplex ⋙
        (Functor.whiskeringLeft _ _ _).obj (evaluationComplex A n) ≅
    totalTensorSystem A ⋙ (Functor.whiskeringRight _ _ _).obj (evaluationComplex A n) :=
  NatIso.ofComponents (fun M => NatIso.ofComponents
    (fun N => evaluationTensorIso A n M N) (fun {N N'} f => by
      have h := evaluationTensorIso_naturality A n (𝟙 M) f
      change (evaluationTensorIso A n M N).hom ≫
        (evaluationComplex A n).map ((TleftCochain M).map f) =
        (TleftCochain ((evaluationComplex A n).obj M)).map
          ((evaluationComplex A n).map f) ≫ (evaluationTensorIso A n M N').hom at h
      exact h.symm))
    (fun {M M'} f => by
      apply NatTrans.ext
      funext N
      have h := evaluationTensorIso_naturality A n f (𝟙 N)
      change (evaluationTensorIso A n M N).hom ≫
        (evaluationComplex A n).map ((TrightCochain N).map f) =
        (TrightCochain ((evaluationComplex A n).obj N)).map
          ((evaluationComplex A n).map f) ≫ (evaluationTensorIso A n M' N).hom at h
      exact h.symm)

/-- The evaluated comparison, natural even at representatives which are not K-flat. -/
private def evaluationTensorCounit (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)] (n : ℕ) :
    (DerivedCategory.Q ⋙ tensorOnDerivedSystems A ⋙
      (Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q) ⋙
        (Functor.whiskeringRight _ _ _).obj
          (PresheafOfModules.evaluation
            (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapDerivedCategory ⟶
    (evaluationComplex A n ⋙
      (curriedTensor (ModuleCat.{max u t} (A.obj (op n)))).map₂CochainComplex ⋙
        (Functor.whiskeringLeft _ _ _).obj (evaluationComplex A n)) ⋙
          (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q :=
  Functor.whiskerRight (tensorComplexCounit A)
    ((Functor.whiskeringRight _ _ _).obj
      (PresheafOfModules.evaluation
        (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapDerivedCategory) ≫
  Functor.whiskerLeft (totalTensorSystem A)
    ((Functor.whiskeringRight _ _ _).map
      (PresheafOfModules.evaluation
        (A ⋙ forget₂ CommRingCat RingCat) (op n)).mapDerivedCategoryFactors.hom) ≫
  (Functor.isoWhiskerRight (totalTensorEvaluationNatIso A n).symm
    ((Functor.whiskeringRight _ _ _).obj DerivedCategory.Q)).hom

private lemma evaluationTensorCounit_isIso (A : ℕᵒᵖ ⥤ CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules.{u, t} A)]
    (M N : CochainComplex (Modules.{u, t} A) ℤ) (n : ℕ)
    (hM : CochainComplex.KFlat ((evaluationComplex A n).obj M)) :
    IsIso (((evaluationTensorCounit A n).app M).app N) := by
  have := isIso_evaluation_tensorComplexCounit A M N n hM
  dsimp only [evaluationTensorCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.whiskeringRight_map_app_app,
    Functor.whiskeringRight_obj_map, Functor.isoWhiskerRight_hom]
  infer_instance

/-- The canonical symmetric and exact derived tensor product of inverse systems. -/
private noncomputable def derivedTensorProductConstruction
    (A : Functor ℕᵒᵖ CommRingCat.{u})
    [HasDerivedCategory.{w}
      (PresheafOfModules.{max u t} (A ⋙ forget₂ CommRingCat RingCat))] :
    DerivedTensorProduct.{u, t, w} A := by
  let leftShift := fun L => Classical.choose (tensorOnDerivedSystems_exact_left A L)
  let rightShift := fun K => Classical.choose (tensorOnDerivedSystems_exact_right A K)
  refine
    { tensor := tensorOnDerivedSystems A
      symmetry := tensorOnDerivedSystemsSymmetry A
      commShift_left := leftShift
      commShift_right := rightShift
      exact_left := fun L => Classical.choose_spec (tensorOnDerivedSystems_exact_left A L)
      exact_right := fun K => Classical.choose_spec (tensorOnDerivedSystems_exact_right A K)
      evaluationIso := fun M N n hM =>
        @asIso _ _ _ _ (((evaluationTensorCounit A n).app M).app N)
          (evaluationTensorCounit_isIso A M N n hM)
      evaluationIso_naturality_right := ?_
      evaluationIso_naturality_left := ?_
      totalTensorEvaluationIso := fun M N n => (evaluationTensorIso A n M N).symm
      totalTensorEvaluationIso_ι := ?_
      comparison := fun M N hM =>
        @asIso _ _ _ _ (((tensorComplexCounit A).app M).app N)
          (tensorComplexCounit_isIso A M N hM)
      comparison_naturality := ?_
      evaluationIso_eq_comparison := ?_ }
  · intro M N N' n hM f
    exact (((evaluationTensorCounit A n).app M).naturality f).symm
  · intro M M' N n hM hM' f
    exact (NatTrans.congr_app ((evaluationTensorCounit A n).naturality f) N).symm
  · intro M N n p q k h
    have hi := HomologicalComplex₂.TotalMap.ι_totalMapf
      (PresheafOfModules.evaluation.{max u t} (A ⋙ forget₂ CommRingCat RingCat) (op n))
      ((((curriedTensor (Modules.{u, t} A)).mapBifunctorHomologicalComplex
        (.up ℤ) (.up ℤ)).obj M).obj N) (c₁₂ := ComplexShape.up ℤ) k p q h
    change _ ≫ (evaluationTensorIso A n M N).hom.f k = _ at hi
    have hh := congrArg (fun f => f ≫ (evaluationTensorIso A n M N).inv.f k) hi
    simp only [Category.assoc, ← HomologicalComplex.comp_f,
      Iso.hom_inv_id, HomologicalComplex.id_f, Category.comp_id] at hh
    convert hh.symm using 1 <;> rfl
  · intro M M' N N' hM hM' f g
    have hr : ((tensorOnDerivedSystems A).obj (DerivedCategory.Q.obj M')).map
        (DerivedCategory.Q.map g) ≫ (((tensorComplexCounit A).app M').app N') =
        (((tensorComplexCounit A).app M').app N) ≫
          DerivedCategory.Q.map (((totalTensorSystem A).obj M').map g) :=
      ((tensorComplexCounit A).app M').naturality g
    have hl : ((tensorOnDerivedSystems A).map (DerivedCategory.Q.map f)).app
        (DerivedCategory.Q.obj N) ≫ (((tensorComplexCounit A).app M').app N) =
        (((tensorComplexCounit A).app M).app N) ≫
          DerivedCategory.Q.map (((totalTensorSystem A).map f).app N) :=
      NatTrans.congr_app ((tensorComplexCounit A).naturality f) N
    change ((tensorOnDerivedSystems A).map (DerivedCategory.Q.map f)).app
        (DerivedCategory.Q.obj N) ≫
      ((tensorOnDerivedSystems A).obj (DerivedCategory.Q.obj M')).map
        (DerivedCategory.Q.map g) ≫ (((tensorComplexCounit A).app M').app N') = _
    rw [hr, ← Category.assoc, hl, Category.assoc, ← DerivedCategory.Q.map_comp]
    rfl
  · intro M N hM n
    apply Iso.ext
    simp only [evaluationTensorCounit, Iso.trans_hom, Functor.mapIso_hom,
      asIso_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.whiskeringRight_map_app_app,
      Functor.whiskeringRight_obj_map, Functor.isoWhiskerRight_hom]
    rfl


end ModuleSystemKFlatComparison

end

end Construction

/-! ### Stacks 091H -/

section Main

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

universe u v w

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

attribute [local instance] HasDerivedCategory.standard

namespace ModuleSystemKFlatComparison

/-- **Stacks 091H.** The derived category of compatible module systems over an inverse system of
commutative rings has a canonical symmetric derived tensor product. A componentwise K-flat
representative computes the whole system by pointwise total tensor, compatibly with evaluation
at every index. The bifunctor is exact in each variable. -/
@[stacks 091H, no_expose]
public noncomputable def derivedTensorProduct
    (A : Functor ℕᵒᵖ CommRingCat.{u})
    [HasDerivedCategory.{w}
      (PresheafOfModules.{max u v} (A ⋙ forget₂ CommRingCat RingCat))] :
    DerivedTensorProduct A :=
  derivedTensorProductConstruction A

end ModuleSystemKFlatComparison

end

end Main
