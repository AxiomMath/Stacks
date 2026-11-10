module

public import StacksFrontier.RingTheory.LocalCohomology.BaseChangeGeneralSupport.Augmentation

/-!
# The base-change comparison for local cohomology with general support

Let `f : A →+* B` be a ring map and `T ⊆ Spec A`, with preimage `T' = (Spec f)⁻¹(T)`. This file
builds the degree-zero change-of-rings map `Γ_T(M) ⊗_A B ⟶ Γ_{T'}(M ⊗_A B)`, right derives it
on the degreewise model of extension of scalars when that functor is left exact, and transports
it to `derivedExtensionScalarsGeneral`, giving the canonical comparison
`derivedSectionsWithSupportInBaseChangeMap`, compatible with the augmentations and natural in
the support.

## Main definitions

* `Stacks.LocalCohomology.sectionsWithSupportInBaseChangeNatTrans` — the degree-zero
  change-of-rings map on supported sections.
* `Stacks.LocalCohomology.derivedSectionsWithSupportInBaseChangeMap` — its right derived
  functor, the canonical base-change comparison on the unbounded derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v uB w

namespace Stacks.LocalCohomology

section BaseChange

open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

variable {A : Type u} {B : Type uB} [CommRing A] [CommRing B]

/-- Extension of scalars is a left adjoint. -/
private theorem extendScalars_isLeftAdjoint (f : A →+* B) :
    (ModuleCat.extendScalars.{u, uB, max u uB v} f).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{max u v, u, uB} f).isLeftAdjoint

attribute [local instance] extendScalars_isLeftAdjoint

private theorem extendScalars_additive (f : A →+* B) :
    (ModuleCat.extendScalars.{u, uB, max u uB v} f).Additive :=
  CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by change CategoryTheory.Limits.PreservesFiniteColimits _; infer_instance)

attribute [local instance] extendScalars_additive

/-- **Flat extension of scalars is left exact.** -/
theorem preservesFiniteLimits_extendScalars_of_flat (f : A →+* B) (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f) := by
  let : Algebra A B := f.toAlgebra
  have : Module.Flat A B := hf
  refine (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (ModuleCat.extendScalars.{u, uB, max u uB v} f)).2 fun S hS ↦ ⟨?_, ?_⟩
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact Module.Flat.lTensor_exact B
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
  · rw [ModuleCat.mono_iff_injective]
    exact Module.Flat.lTensor_preserves_injective_linearMap S.f.hom
      ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)

/-- **Closed supports pull back to zero loci.** The preimage of `V(I)` under `Spec B → Spec A` is
the zero locus of the extended ideal `IB`. -/
theorem comap_preimage_zeroLocus_eq_map (f : A →+* B) (I : Ideal A) :
    (PrimeSpectrum.comap f) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (I.map f : Set B) := by
  ext q
  rw [Set.mem_preimage, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal,
    PrimeSpectrum.mem_zeroLocus]
  change I ≤ q.asIdeal.comap f ↔ I.map f ≤ q.asIdeal
  exact (Ideal.map_le_iff_le_comap (f := f) (I := I) (K := q.asIdeal)).symm

/-- **A supported section stays supported after extension of scalars.** If `x` has support in
`T`, then `b ⊗ x` has support in the preimage of `T`. -/
theorem tmul_mem_sectionsWithSupportIn (f : A →+* B) (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u uB v} A) (b : B) (x : sectionsWithSupportIn A T M) :
    (b ⊗ₜ[A,f] x.val : ↑((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj M)) ∈
      sectionsWithSupportIn B ((PrimeSpectrum.comap f) ⁻¹' T)
        ((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj M) := by
  let : Module A B := Module.compHom B f
  let : IsScalarTower A A B := IsScalarTower.left A
  let : IsScalarTower A A (↑M) := IsScalarTower.left A
  apply (mem_sectionsWithSupportIn_iff B
    ((PrimeSpectrum.comap f) ⁻¹' T) ((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj M)
    (b ⊗ₜ[A,f] x.val : ↑((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj M))).2
  have hx := (mem_sectionsWithSupportIn_iff A T (↑M) x.val).mp x.property
  have hmap : (Ideal.torsionOf A (↑M) x.val).map f ≤
      Ideal.torsionOf B ((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj M)
        (b ⊗ₜ[A,f] x.val :
          ↑((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj M)) := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_
    have hax : a • x.val = 0 := (Ideal.mem_torsionOf_iff _ _).mp ha
    refine (Ideal.mem_torsionOf_iff _ (f a)).mpr ?_
    refine (ModuleCat.ExtendScalars.smul_tmul f (f a) b x.val).trans ?_
    refine (TensorProduct.smul_tmul a b x.val).trans ?_
    exact (congrArg (TensorProduct.tmul A b) hax).trans (TensorProduct.tmul_zero _ _)
  calc
    PrimeSpectrum.zeroLocus
        (Ideal.torsionOf B ((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj M)
          (b ⊗ₜ[A,f] x.val :
            ↑((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj M)) : Set B) ⊆
      PrimeSpectrum.zeroLocus ((Ideal.torsionOf A (↑M) x.val).map f : Set B) :=
        PrimeSpectrum.zeroLocus_anti_mono_ideal hmap
    _ = (PrimeSpectrum.comap f) ⁻¹' PrimeSpectrum.zeroLocus
          (Ideal.torsionOf A (↑M) x.val : Set A) :=
      (comap_preimage_zeroLocus_eq_map f (Ideal.torsionOf A (↑M) x.val)).symm
    _ ⊆ (PrimeSpectrum.comap f) ⁻¹' T := Set.preimage_mono hx

/-- **The change-of-rings map on degree-zero supported sections.** -/
def sectionsWithSupportInBaseChangeNatTrans (f : A →+* B) (T : Set (PrimeSpectrum A)) :
    sectionsWithSupportInFunctor.{u, max uB v} A T ⋙
        ModuleCat.extendScalars.{u, uB, max u uB v} f ⟶
      ModuleCat.extendScalars.{u, uB, max u uB v} f ⋙
        sectionsWithSupportInFunctor.{uB, max u v} B ((PrimeSpectrum.comap f) ⁻¹' T) where
  app (M : ModuleCat.{max u uB v} A) := by
    let : Module A B := Module.compHom B f
    refine ModuleCat.ofHom
      (X := ↑((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj
        ((sectionsWithSupportInFunctor.{u, max uB v} A T).obj M)))
      (Y := ↥(sectionsWithSupportIn B ((PrimeSpectrum.comap f) ⁻¹' T)
        ((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj M)))
      (LinearMap.codRestrict _
        ((ModuleCat.extendScalars.{u, uB, max u uB v} f).map
          ((sectionsWithSupportInSubtype.{u, max uB v} A T).app M)).hom fun y ↦ ?_)
    induction y using TensorProduct.inductionOn with
    | tmul b x =>
        refine (ModuleCat.ExtendScalars.map_tmul f
          ((sectionsWithSupportInSubtype.{u, max uB v} A T).app M) b x) ▸ ?_
        exact tmul_mem_sectionsWithSupportIn f T M b x
    | add y z hy hz =>
        exact Eq.mpr
          (congrArg (fun w ↦ w ∈ sectionsWithSupportIn B ((PrimeSpectrum.comap f) ⁻¹' T)
              ((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj M))
            (((ModuleCat.extendScalars.{u, uB, max u uB v} f).map
              ((sectionsWithSupportInSubtype.{u, max uB v} A T).app M)).hom.map_add y z))
          ((sectionsWithSupportIn B ((PrimeSpectrum.comap f) ⁻¹' T)
            ((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj M)).add_mem hy hz)
  naturality {M N} q := by
    apply ModuleCat.hom_ext
    ext y
    apply Subtype.ext
    let E := ModuleCat.extendScalars.{u, uB, max u uB v} f
    have hη := (sectionsWithSupportInSubtype.{u, max uB v} A T).naturality q
    have hE := congrArg E.map hη
    have hval := congrArg (fun k ↦ k.hom y) hE
    rw [Functor.id_map] at hval
    change (E.map ((sectionsWithSupportInSubtype.{u, max uB v} A T).app N)).hom
        ((E.map ((sectionsWithSupportInFunctor.{u, max uB v} A T).map q)).hom y) =
      (E.map q).hom
        ((E.map ((sectionsWithSupportInSubtype.{u, max uB v} A T).app M)).hom y)
    simpa only [Functor.map_comp, Functor.map_id, Functor.id_obj, ModuleCat.hom_comp,
      LinearMap.comp_apply] using hval

/-- The degree-zero base-change map factors the inclusion of supported sections. -/
theorem sectionsWithSupportInBaseChangeNatTrans_subtype (f : A →+* B)
    (T : Set (PrimeSpectrum A)) :
    sectionsWithSupportInBaseChangeNatTrans.{u, v, uB} f T ≫
        whiskerLeft (ModuleCat.extendScalars.{u, uB, max u uB v} f)
          (sectionsWithSupportInSubtype.{uB, max u v} B
            ((PrimeSpectrum.comap f) ⁻¹' T)) =
      whiskerRight (sectionsWithSupportInSubtype.{u, max uB v} A T)
        (ModuleCat.extendScalars.{u, uB, max u uB v} f) := by
  ext M x
  rfl

/-- Widening the support is compatible with the inclusion into the ambient module. -/
theorem sectionsWithSupportInInclusion_comp_subtype_app {S T : Set (PrimeSpectrum A)}
    (h : S ⊆ T) (M : ModuleCat.{max u v} A) :
    (sectionsWithSupportInInclusion.{u, v} A h).app M ≫
        (sectionsWithSupportInSubtype.{u, v} A T).app M =
      (sectionsWithSupportInSubtype.{u, v} A S).app M :=
  ModuleCat.hom_ext <| Submodule.subtype_comp_inclusion
    (sectionsWithSupportIn A S M) (sectionsWithSupportIn A T M)
    (sectionsWithSupportIn_mono.{u, max u v} A h M)

/-- The degree-zero base-change map is natural in the support. -/
theorem sectionsWithSupportInBaseChangeNatTrans_support (f : A →+* B)
    {S T : Set (PrimeSpectrum A)} (h : S ⊆ T) :
    whiskerRight (sectionsWithSupportInInclusion.{u, max uB v} A h)
        (ModuleCat.extendScalars.{u, uB, max u uB v} f) ≫
        sectionsWithSupportInBaseChangeNatTrans.{u, v, uB} f T =
      sectionsWithSupportInBaseChangeNatTrans.{u, v, uB} f S ≫
        whiskerLeft (ModuleCat.extendScalars.{u, uB, max u uB v} f)
          (sectionsWithSupportInInclusion.{uB, max u v} B (Set.preimage_mono h)) := by
  have hiA := sectionsWithSupportInBaseChangeNatTrans_subtype.{u, v, uB} f T
  have hiS := sectionsWithSupportInBaseChangeNatTrans_subtype.{u, v, uB} f S
  ext M : 2
  have hmono : Mono ((sectionsWithSupportInSubtype.{uB, max u v} B
      ((PrimeSpectrum.comap f) ⁻¹' T)).app
        ((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj M)) := by
    rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  apply (cancel_mono ((sectionsWithSupportInSubtype.{uB, max u v} B
    ((PrimeSpectrum.comap f) ⁻¹' T)).app
      ((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj M))).mp
  have e1 := NatTrans.congr_app hiA M
  have e2 := NatTrans.congr_app hiS M
  have e3 := sectionsWithSupportInInclusion_comp_subtype_app.{u, max uB v} h M
  have e4 := sectionsWithSupportInInclusion_comp_subtype_app.{uB, max u v}
    (Set.preimage_mono h : (PrimeSpectrum.comap f) ⁻¹' S ⊆ (PrimeSpectrum.comap f) ⁻¹' T)
    ((ModuleCat.extendScalars.{u, uB, max u uB v} f).obj M)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at e1 e2
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Category.assoc]
  rw [e1, e4, e2, ← Functor.map_comp, e3]

section Exact

/-- Degreewise extension of scalars along a flat ring map, read on derived categories, is a left
adjoint; its right adjoint is restriction of scalars. -/
theorem mapDerivedCategory_isLeftAdjoint (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)] :
    (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory.IsLeftAdjoint :=
  (Adjunction.mapDerivedCategory
    (ModuleCat.extendRestrictScalarsAdj.{max u v, u, uB} f)).isLeftAdjoint

attribute [local instance] mapDerivedCategory_isLeftAdjoint

/-- For a flat ring map, derived extension of scalars is the degreewise functor read on derived
categories. -/
def derivedExtensionScalarsIsoMapDerivedCategory (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)] :
    (derivedExtensionScalarsGeneral.{u, v, uB} f).functor ≅
      (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory := by
  let F := ModuleCat.extendScalars.{u, uB, max u uB v} f
  let D := derivedExtensionScalarsGeneral.{u, v, uB} f
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{max u uB v} A) (ComplexShape.up ℤ))
    F.mapDerivedCategory F.mapDerivedCategoryFactors
  exact Functor.leftDerivedNatIso D.functor F.mapDerivedCategory D.comparison
    F.mapDerivedCategoryFactors.hom
    (HomologicalComplex.quasiIso (ModuleCat.{max u uB v} A) (ComplexShape.up ℤ)) (Iso.refl _)

/-- **Flat derived extension of scalars commutes with cohomology, naturally in the complex.**
This is the natural refinement of
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsHomologyIso`, which is stated one
object at a time. -/
def derivedExtensionScalarsHomologyNatIso (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)] (i : ℤ) :
    (derivedExtensionScalarsGeneral.{u, v, uB} f).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max u uB v} B) i ≅
      DerivedCategory.homologyFunctor (ModuleCat.{max u uB v} A) i ⋙
        ModuleCat.extendScalars.{u, uB, max u uB v} f :=
  Functor.isoWhiskerRight (derivedExtensionScalarsIsoMapDerivedCategory.{u, v, uB} f)
    (DerivedCategory.homologyFunctor (ModuleCat.{max u uB v} B) i) ≪≫
    StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (ModuleCat.extendScalars.{u, uB, max u uB v} f) i

/-- The base-change comparison on supported sections, read on homotopy categories. -/
def htpyBaseChange (f : A →+* B) (T : Set (PrimeSpectrum A)) :
    (sectionsWithSupportInFunctor.{u, max uB v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
          (ComplexShape.up ℤ) ⟶
      (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (sectionsWithSupportInFunctor.{uB, max u v} B
          ((PrimeSpectrum.comap f) ⁻¹' T)).mapHomotopyCategory (ComplexShape.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso (Iso.refl
      (sectionsWithSupportInFunctor.{u, max uB v} A T ⋙
        ModuleCat.extendScalars.{u, uB, max u uB v} f)) (ComplexShape.up ℤ)).hom ≫
    (sectionsWithSupportInBaseChangeNatTrans.{u, v, uB} f T).mapHomotopyCategory
      (ComplexShape.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl
      (ModuleCat.extendScalars.{u, uB, max u uB v} f ⋙
        sectionsWithSupportInFunctor.{uB, max u v} B
          ((PrimeSpectrum.comap f) ⁻¹' T))) (ComplexShape.up ℤ)).inv

/-- The homotopy-level base-change comparison factors the supported inclusion. -/
private lemma htpyBaseChange_subtype (f : A →+* B) (T : Set (PrimeSpectrum A)) :
    htpyBaseChange.{u, v, uB} f T ≫
        whiskerLeft ((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
            (ComplexShape.up ℤ))
          (homotopySectionsWithSupportInSubtype.{uB, max u v} B
            ((PrimeSpectrum.comap f) ⁻¹' T)) =
      whiskerRight (homotopySectionsWithSupportInSubtype.{u, max uB v} A T)
        ((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
          (ComplexShape.up ℤ)) := by
  ext K
  simp only [htpyBaseChange, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Category.assoc]
  change (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _ =
    (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _
  simp only [← Functor.map_comp]
  congr 1

/-- The homotopy-level base-change comparison is natural in the support. -/
private lemma htpyBaseChange_support (f : A →+* B) {S T : Set (PrimeSpectrum A)} (h : S ⊆ T) :
    whiskerRight
          ((sectionsWithSupportInInclusion.{u, max uB v} A h).mapHomotopyCategory
            (ComplexShape.up ℤ))
          ((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
            (ComplexShape.up ℤ)) ≫
        htpyBaseChange.{u, v, uB} f T =
      htpyBaseChange.{u, v, uB} f S ≫
        whiskerLeft ((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
            (ComplexShape.up ℤ))
          ((sectionsWithSupportInInclusion.{uB, max u v} B
            (Set.preimage_mono h)).mapHomotopyCategory (ComplexShape.up ℤ)) := by
  ext K
  simp only [htpyBaseChange, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Category.assoc]
  change (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _ =
    (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _
  change (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _ =
    (HomotopyCategory.quotient (ModuleCat.{max u uB v} B) (ComplexShape.up ℤ)).map _
  congr 1
  ext n x
  have hy := NatTrans.congr_app
    (sectionsWithSupportInBaseChangeNatTrans_support.{u, v, uB} f h) (K.as.X n)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hy
  exact congrArg (fun φ ↦ (ModuleCat.Hom.hom φ) x) hy

/-- The homotopy-level comparison defining the base-change map on the degreewise model of
derived extension of scalars. -/
def bcTau (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    (T : Set (PrimeSpectrum A)) :
    ((sectionsWithSupportInFunctor.{u, max uB v} A T).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙
        ((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory ⋙
          derivedSectionsWithSupportIn.{uB, max u v} B ((PrimeSpectrum.comap f) ⁻¹' T)) :=
  (Functor.associator _ _ _).hom ≫
    whiskerLeft ((sectionsWithSupportInFunctor.{u, max uB v} A T).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (htpyBaseChange.{u, v, uB} f T) DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft ((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (derivedSectionsWithSupportInUnit.{uB, max u v} B ((PrimeSpectrum.comap f) ⁻¹' T)) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight
      (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategoryFactorsh.inv
      (derivedSectionsWithSupportIn.{uB, max u v} B ((PrimeSpectrum.comap f) ⁻¹' T)) ≫
    (Functor.associator _ _ _).hom

/-- The base-change comparison for the degreewise model of derived extension of scalars, the
unique map compatible with the canonical derived units. -/
def derivedSectionsWithSupportInBaseChangeMapExact (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    (T : Set (PrimeSpectrum A)) :
    derivedSectionsWithSupportIn.{u, max uB v} A T ⋙
        (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory ⟶
      (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory ⋙
        derivedSectionsWithSupportIn.{uB, max u v} B ((PrimeSpectrum.comap f) ⁻¹' T) :=
  (derivedSectionsWithSupportIn.{u, max uB v} A T ⋙
      (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory).rightDerivedDesc
    (whiskerRight (derivedSectionsWithSupportInUnit.{u, max uB v} A T)
        (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso (ModuleCat.{max u uB v} A) (ComplexShape.up ℤ))
    ((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory ⋙
      derivedSectionsWithSupportIn.{uB, max u v} B ((PrimeSpectrum.comap f) ⁻¹' T))
    (bcTau.{u, v, uB} f T)

/-- The defining factorization of the base-change map on the degreewise model. -/
private lemma derivedSectionsWithSupportInBaseChangeMapExact_fac (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    (T : Set (PrimeSpectrum A)) :
    (whiskerRight (derivedSectionsWithSupportInUnit.{u, max uB v} A T)
        (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory ≫
      (Functor.associator _ _ _).hom) ≫
        whiskerLeft DerivedCategory.Qh
          (derivedSectionsWithSupportInBaseChangeMapExact.{u, v, uB} f T) =
      bcTau.{u, v, uB} f T :=
  Functor.rightDerived_fac _ _
    (HomotopyCategory.quasiIso (ModuleCat.{max u uB v} A) (ComplexShape.up ℤ)) _ _

/-- The base-change comparison of the degreewise model is compatible with the augmentations. -/
private lemma derivedSectionsWithSupportInBaseChangeMapExact_augmentation (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    (T : Set (PrimeSpectrum A)) :
    derivedSectionsWithSupportInBaseChangeMapExact.{u, v, uB} f T ≫
        whiskerLeft (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory
          (derivedSectionsWithSupportInAugmentation.{uB, max u v} B
            ((PrimeSpectrum.comap f) ⁻¹' T)) =
      whiskerRight (derivedSectionsWithSupportInAugmentation.{u, max uB v} A T)
        (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory := by
  have hinc : ∀ K, (htpyBaseChange.{u, v, uB} f T).app K ≫
      (homotopySectionsWithSupportInSubtype.{uB, max u v} B
        ((PrimeSpectrum.comap f) ⁻¹' T)).app
        (((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) =
      ((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
          (ComplexShape.up ℤ)).map
        ((homotopySectionsWithSupportInSubtype.{u, max uB v} A T).app K) :=
    fun K ↦ NatTrans.congr_app (htpyBaseChange_subtype.{u, v, uB} f T) K
  refine Functor.rightDerived_ext
    (derivedSectionsWithSupportIn.{u, max uB v} A T ⋙
      (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory)
    (whiskerRight (derivedSectionsWithSupportInUnit.{u, max uB v} A T)
        (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso (ModuleCat.{max u uB v} A) (ComplexShape.up ℤ)) _ _ _ ?_
  rw [whiskerLeft_comp, ← Category.assoc,
    derivedSectionsWithSupportInBaseChangeMapExact_fac.{u, v, uB} f T]
  ext K
  simp only [bcTau, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc]
  have s1 : (derivedSectionsWithSupportIn.{uB, max u v} B
        ((PrimeSpectrum.comap f) ⁻¹' T)).map
        ((Functor.mapDerivedCategoryFactorsh
          (ModuleCat.extendScalars.{u, uB, max u uB v} f)).inv.app K) ≫
        (derivedSectionsWithSupportInAugmentation.{uB, max u v} B
          ((PrimeSpectrum.comap f) ⁻¹' T)).app
          ((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory.obj
            (DerivedCategory.Qh.obj K)) =
      (derivedSectionsWithSupportInAugmentation.{uB, max u v} B
          ((PrimeSpectrum.comap f) ⁻¹' T)).app
          (DerivedCategory.Qh.obj
            (((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) ≫
        (Functor.mapDerivedCategoryFactorsh
          (ModuleCat.extendScalars.{u, uB, max u uB v} f)).inv.app K :=
    NatTrans.naturality _ _
  have s2 : (derivedSectionsWithSupportInUnit.{uB, max u v} B
        ((PrimeSpectrum.comap f) ⁻¹' T)).app
        (((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      (derivedSectionsWithSupportInAugmentation.{uB, max u v} B
          ((PrimeSpectrum.comap f) ⁻¹' T)).app
          (DerivedCategory.Qh.obj
            (((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map
        ((homotopySectionsWithSupportInSubtype.{uB, max u v} B
          ((PrimeSpectrum.comap f) ⁻¹' T)).app
          (((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K)) :=
    derivedSectionsWithSupportInUnit_augmentation.{uB, max u v} B
      ((PrimeSpectrum.comap f) ⁻¹' T) _
  have s4 : (Functor.mapDerivedCategoryFactorsh
        (ModuleCat.extendScalars.{u, uB, max u uB v} f)).hom.app
        (((sectionsWithSupportInFunctor.{u, max uB v} A T).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        (((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
            (ComplexShape.up ℤ)).map
          ((homotopySectionsWithSupportInSubtype.{u, max uB v} A T).app K)) =
      (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory.map
          (DerivedCategory.Qh.map
            ((homotopySectionsWithSupportInSubtype.{u, max uB v} A T).app K)) ≫
        (Functor.mapDerivedCategoryFactorsh
          (ModuleCat.extendScalars.{u, uB, max u uB v} f)).hom.app K :=
    (NatTrans.naturality _ _).symm
  have s5 : (Functor.mapDerivedCategoryFactorsh
        (ModuleCat.extendScalars.{u, uB, max u uB v} f)).hom.app K ≫
      (Functor.mapDerivedCategoryFactorsh
        (ModuleCat.extendScalars.{u, uB, max u uB v} f)).inv.app K =
      𝟙 ((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory.obj
        (DerivedCategory.Qh.obj K)) :=
    (Functor.mapDerivedCategoryFactorsh
      (ModuleCat.extendScalars.{u, uB, max u uB v} f)).hom_inv_id_app K
  rw [s1, reassoc_of% s2, ← Functor.map_comp_assoc, hinc K, reassoc_of% s4,
    s5, Category.comp_id, ← Functor.map_comp,
    derivedSectionsWithSupportInUnit_augmentation.{u, max uB v} A T K]

/-- The homotopy-level comparison `bcTau` is natural in the support. -/
private lemma bcTau_support (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    {S T : Set (PrimeSpectrum A)} (h : S ⊆ T) :
    whiskerRight (whiskerRight
          ((sectionsWithSupportInInclusion.{u, max uB v} A h).mapHomotopyCategory
            (ComplexShape.up ℤ)) DerivedCategory.Qh)
        (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory ≫
        bcTau.{u, v, uB} f T =
      bcTau.{u, v, uB} f S ≫
        whiskerLeft DerivedCategory.Qh (whiskerLeft
          (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory
          (derivedSectionsWithSupportInInclusion.{uB, max u v} B
            (Set.preimage_mono h))) := by
  have hbc : ∀ K, ((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
        (ComplexShape.up ℤ)).map
        (((sectionsWithSupportInInclusion.{u, max uB v} A h).mapHomotopyCategory
          (ComplexShape.up ℤ)).app K) ≫ (htpyBaseChange.{u, v, uB} f T).app K =
      (htpyBaseChange.{u, v, uB} f S).app K ≫
        ((sectionsWithSupportInInclusion.{uB, max u v} B
          (Set.preimage_mono h)).mapHomotopyCategory (ComplexShape.up ℤ)).app
          (((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) :=
    fun K ↦ NatTrans.congr_app (htpyBaseChange_support.{u, v, uB} f h) K
  have hunitB : ∀ X, (derivedSectionsWithSupportInUnit.{uB, max u v} B
        ((PrimeSpectrum.comap f) ⁻¹' S)).app X ≫
      (derivedSectionsWithSupportInInclusion.{uB, max u v} B
        (Set.preimage_mono h)).app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map
        (((sectionsWithSupportInInclusion.{uB, max u v} B
          (Set.preimage_mono h)).mapHomotopyCategory (ComplexShape.up ℤ)).app X) ≫
        (derivedSectionsWithSupportInUnit.{uB, max u v} B
          ((PrimeSpectrum.comap f) ⁻¹' T)).app X :=
    fun X ↦ NatTrans.congr_app
      (derivedSectionsWithSupportInInclusion_fac.{uB, max u v} B (Set.preimage_mono h)) X
  ext K
  simp only [bcTau, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  have s1 : (derivedSectionsWithSupportIn.{uB, max u v} B
        ((PrimeSpectrum.comap f) ⁻¹' S)).map
        ((Functor.mapDerivedCategoryFactorsh
          (ModuleCat.extendScalars.{u, uB, max u uB v} f)).inv.app K) ≫
        (derivedSectionsWithSupportInInclusion.{uB, max u v} B
          (Set.preimage_mono h)).app
          ((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory.obj
            (DerivedCategory.Qh.obj K)) =
      (derivedSectionsWithSupportInInclusion.{uB, max u v} B
          (Set.preimage_mono h)).app
          (DerivedCategory.Qh.obj
            (((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) ≫
        (derivedSectionsWithSupportIn.{uB, max u v} B
          ((PrimeSpectrum.comap f) ⁻¹' T)).map
          ((Functor.mapDerivedCategoryFactorsh
            (ModuleCat.extendScalars.{u, uB, max u uB v} f)).inv.app K) :=
    NatTrans.naturality _ _
  have s2 : (Functor.mapDerivedCategoryFactorsh
        (ModuleCat.extendScalars.{u, uB, max u uB v} f)).hom.app
        (((sectionsWithSupportInFunctor.{u, max uB v} A S).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        (((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapHomotopyCategory
            (ComplexShape.up ℤ)).map
          (((sectionsWithSupportInInclusion.{u, max uB v} A h).mapHomotopyCategory
            (ComplexShape.up ℤ)).app K)) =
      (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory.map
          (DerivedCategory.Qh.map
            (((sectionsWithSupportInInclusion.{u, max uB v} A h).mapHomotopyCategory
              (ComplexShape.up ℤ)).app K)) ≫
        (Functor.mapDerivedCategoryFactorsh
          (ModuleCat.extendScalars.{u, uB, max u uB v} f)).hom.app
          (((sectionsWithSupportInFunctor.{u, max uB v} A T).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) :=
    (NatTrans.naturality _ _).symm
  rw [s1, reassoc_of% hunitB, ← reassoc_of% s2, ← Functor.map_comp_assoc,
    hbc K, Functor.map_comp_assoc]

/-- The base-change comparison of the degreewise model is natural in the support. -/
private lemma derivedSectionsWithSupportInBaseChangeMapExact_support (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    {S T : Set (PrimeSpectrum A)} (h : S ⊆ T) :
    whiskerRight (derivedSectionsWithSupportInInclusion.{u, max uB v} A h)
        (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory ≫
        derivedSectionsWithSupportInBaseChangeMapExact.{u, v, uB} f T =
      derivedSectionsWithSupportInBaseChangeMapExact.{u, v, uB} f S ≫
        whiskerLeft (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory
          (derivedSectionsWithSupportInInclusion.{uB, max u v} B
            (Set.preimage_mono h)) := by
  have hfacS := derivedSectionsWithSupportInBaseChangeMapExact_fac.{u, v, uB} f S
  have hfacT := derivedSectionsWithSupportInBaseChangeMapExact_fac.{u, v, uB} f T
  have hsupp := bcTau_support.{u, v, uB} f h
  have hinclA := derivedSectionsWithSupportInInclusion_fac.{u, max uB v} A h
  refine Functor.rightDerived_ext
    (derivedSectionsWithSupportIn.{u, max uB v} A S ⋙
      (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory)
    (whiskerRight (derivedSectionsWithSupportInUnit.{u, max uB v} A S)
        (ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso (ModuleCat.{max u uB v} A) (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  have e1 := NatTrans.congr_app hfacS K
  have e2 := NatTrans.congr_app hfacT K
  have e3 := NatTrans.congr_app hsupp K
  have e4 := NatTrans.congr_app hinclA K
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp, Category.assoc] at e1 e2 e3 e4
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, e4, Functor.map_comp_assoc, e2, e3, reassoc_of% e1]

end Exact

section Canonical

/-- **The canonical base-change comparison for local cohomology with support in `T`.** It is the
unique map compatible with the canonical derived units; equivalently, the unique map compatible
with the augmentations to the identity. -/
def derivedSectionsWithSupportInBaseChangeMap (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    (T : Set (PrimeSpectrum A)) :
    derivedSectionsWithSupportIn.{u, max uB v} A T ⋙
        (derivedExtensionScalarsGeneral.{u, v, uB} f).functor ⟶
      (derivedExtensionScalarsGeneral.{u, v, uB} f).functor ⋙
        derivedSectionsWithSupportIn.{uB, max u v} B ((PrimeSpectrum.comap f) ⁻¹' T) :=
  whiskerLeft (derivedSectionsWithSupportIn.{u, max uB v} A T)
      (derivedExtensionScalarsIsoMapDerivedCategory.{u, v, uB} f).hom ≫
    derivedSectionsWithSupportInBaseChangeMapExact.{u, v, uB} f T ≫
    whiskerRight (derivedExtensionScalarsIsoMapDerivedCategory.{u, v, uB} f).inv
      (derivedSectionsWithSupportIn.{uB, max u v} B ((PrimeSpectrum.comap f) ⁻¹' T))

/-- **The canonical base-change comparison is compatible with the augmentations.** -/
theorem derivedSectionsWithSupportInBaseChangeMap_augmentation (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory (ModuleCat.{max u uB v} A)) :
    (derivedSectionsWithSupportInBaseChangeMap.{u, v, uB} f T).app K ≫
        (derivedSectionsWithSupportInAugmentation.{uB, max u v} B
          ((PrimeSpectrum.comap f) ⁻¹' T)).app
          ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K) =
      (derivedExtensionScalarsGeneral.{u, v, uB} f).functor.map
        ((derivedSectionsWithSupportInAugmentation.{u, max uB v} A T).app K) := by
  have haug := NatTrans.congr_app
    (derivedSectionsWithSupportInBaseChangeMapExact_augmentation.{u, v, uB} f T) K
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at haug
  simp only [derivedSectionsWithSupportInBaseChangeMap, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Category.assoc]
  have s1 : (derivedSectionsWithSupportIn.{uB, max u v} B
        ((PrimeSpectrum.comap f) ⁻¹' T)).map
        ((derivedExtensionScalarsIsoMapDerivedCategory.{u, v, uB} f).inv.app K) ≫
      (derivedSectionsWithSupportInAugmentation.{uB, max u v} B
        ((PrimeSpectrum.comap f) ⁻¹' T)).app
        ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K) =
      (derivedSectionsWithSupportInAugmentation.{uB, max u v} B
        ((PrimeSpectrum.comap f) ⁻¹' T)).app
        ((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory.obj K) ≫
        (derivedExtensionScalarsIsoMapDerivedCategory.{u, v, uB} f).inv.app K :=
    NatTrans.naturality _ _
  have s2 := NatTrans.naturality
    (derivedExtensionScalarsIsoMapDerivedCategory.{u, v, uB} f).hom
    ((derivedSectionsWithSupportInAugmentation.{u, max uB v} A T).app K)
  rw [s1, reassoc_of% haug, ← reassoc_of% s2, Iso.hom_inv_id_app, Category.comp_id]

/-- The canonical base-change comparison is natural in the support. -/
theorem derivedSectionsWithSupportInBaseChangeMap_support (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    {S T : Set (PrimeSpectrum A)} (h : S ⊆ T)
    (K : DerivedCategory (ModuleCat.{max u uB v} A)) :
    (derivedExtensionScalarsGeneral.{u, v, uB} f).functor.map
        ((derivedSectionsWithSupportInInclusion.{u, max uB v} A h).app K) ≫
        (derivedSectionsWithSupportInBaseChangeMap.{u, v, uB} f T).app K =
      (derivedSectionsWithSupportInBaseChangeMap.{u, v, uB} f S).app K ≫
        (derivedSectionsWithSupportInInclusion.{uB, max u v} B (Set.preimage_mono h)).app
          ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K) := by
  have hsupp := NatTrans.congr_app
    (derivedSectionsWithSupportInBaseChangeMapExact_support.{u, v, uB} f h) K
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hsupp
  simp only [derivedSectionsWithSupportInBaseChangeMap, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Category.assoc]
  have s1 := NatTrans.naturality
    (derivedExtensionScalarsIsoMapDerivedCategory.{u, v, uB} f).hom
    ((derivedSectionsWithSupportInInclusion.{u, max uB v} A h).app K)
  have s2 : (derivedSectionsWithSupportIn.{uB, max u v} B
        ((PrimeSpectrum.comap f) ⁻¹' S)).map
        ((derivedExtensionScalarsIsoMapDerivedCategory.{u, v, uB} f).inv.app K) ≫
      (derivedSectionsWithSupportInInclusion.{uB, max u v} B (Set.preimage_mono h)).app
        ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K) =
      (derivedSectionsWithSupportInInclusion.{uB, max u v} B (Set.preimage_mono h)).app
        ((ModuleCat.extendScalars.{u, uB, max u uB v} f).mapDerivedCategory.obj K) ≫
        (derivedSectionsWithSupportIn.{uB, max u v} B
          ((PrimeSpectrum.comap f) ⁻¹' T)).map
          ((derivedExtensionScalarsIsoMapDerivedCategory.{u, v, uB} f).inv.app K) :=
    NatTrans.naturality _ _
  rw [reassoc_of% s1, reassoc_of% hsupp, s2]

end Canonical

end BaseChange

end Stacks.LocalCohomology

end
