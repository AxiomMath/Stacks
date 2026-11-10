module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Injectives.Spaltenstein.Enlargement
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SectionsWithSupport

/-!
# The distinguished triangle for sections with support

Let `Z` be a closed subset of a ringed space `X`, and let `U = X ∖ Z`. Derived sections with
support in `Z`, derived global sections, and derived sections on `U` fit into a distinguished
triangle, naturally in the object of the *unbounded* derived category of modules on `X`.

## Main definitions

* `derivedSectionsWithSupportTriangle`: the triangle data, that is a natural connecting
  morphism `RΓ(U, -) ⟶ RΓ_Z(X, -)[1]` together with the distinguishedness of
  `RΓ_Z(X, -) ⟶ RΓ(X, -) ⟶ RΓ(U, -) ⟶ RΓ_Z(X, -)[1]` at every object.
* `derivedSectionsWithSupportBoundary`: the connecting morphism `RΓ(U, -) ⟶ RΓ_Z(X, -)[1]`.
* `derivedSectionsWithSupportTriangleAt`: the triangle at an object of the derived category.

## Main results

* `nonempty_sectionsWithSupportTriangleData`: the triangle data exists.
* `derivedSectionsWithSupportTriangleAt_distinguished`: the objectwise triangles are
  distinguished.

## References

* [Stacks Project, Tag 0G71](https://stacks.math.columbia.edu/tag/0G71)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.SectionsWithSupport

attribute [local instance] HasDerivedCategory.standard

/-! ### The chosen functorial K-injective resolution -/

/-- The chosen functorial K-injective resolution of complexes of modules on a ringed space. -/
private noncomputable def functorialKInjectiveResolution (X : RingedSpace.{u, u}) :
    Stacks.Injectives.FunctorialKInjectiveResolution (ModuleSheaves X) :=
  (Stacks.Injectives.exists_functorial_quasiIso_isKInjective (ModuleSheaves
    X)).some

/-- The functor sending a complex of modules to its chosen K-injective resolution. -/
private noncomputable def kInjectiveResolutionFunctor (X : RingedSpace.{u, u}) :
    CochainComplex (ModuleSheaves X) ℤ ⥤ CochainComplex (ModuleSheaves X) ℤ :=
  (functorialKInjectiveResolution X).functor

/-- The natural inclusion of a complex of modules into its chosen K-injective resolution. -/
private noncomputable def kInjectiveResolutionInclusion (X : RingedSpace.{u, u}) :
    Functor.id (CochainComplex (ModuleSheaves X) ℤ) ⟶ kInjectiveResolutionFunctor X :=
  (functorialKInjectiveResolution X).inclusion

private instance kInjectiveResolutionInclusion_quasiIso (X : RingedSpace.{u, u})
    (M : CochainComplex (ModuleSheaves X) ℤ) :
    QuasiIso ((kInjectiveResolutionInclusion X).app M) :=
  (functorialKInjectiveResolution X).quasiIso M

private instance kInjectiveResolutionFunctor_obj_X_injective (X : RingedSpace.{u, u})
    (M : CochainComplex (ModuleSheaves X) ℤ) (n : ℤ) :
    Injective (((kInjectiveResolutionFunctor X).obj M).X n) :=
  (functorialKInjectiveResolution X).injective M n

private instance kInjectiveResolutionFunctor_obj_isKInjective (X : RingedSpace.{u, u})
    (M : CochainComplex (ModuleSheaves X) ℤ) :
    ((kInjectiveResolutionFunctor X).obj M).IsKInjective :=
  (functorialKInjectiveResolution X).isKInjective M

/-! ### The short exact sequence on complexes with injective terms -/

/-- The short complex `Γ_Z(X, -) ⟶ Γ(X, -) ⟶ Γ(U, -)` of complexes of modules, applied
degreewise to a complex of module sheaves. -/
private noncomputable def sectionsWithSupportShortComplex
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    (I : CochainComplex (ModuleSheaves X) ℤ) :
    ShortComplex (CochainComplex (GlobalModules X) ℤ) := by
  letI : (kernel (restrictionToComplement X Z hZ)).PreservesZeroMorphisms :=
    sectionsWithSupport_preservesZeroMorphisms X Z hZ
  let f := NatTrans.mapHomologicalComplex
    (kernel.ι (restrictionToComplement X Z hZ)) (ComplexShape.up ℤ)
  let g := NatTrans.mapHomologicalComplex (restrictionToComplement X Z hZ)
    (ComplexShape.up ℤ)
  refine ShortComplex.mk (f.app I) (g.app I) ?_
  have hmap : NatTrans.mapHomologicalComplex
      (kernel.ι (restrictionToComplement X Z hZ)) (ComplexShape.up ℤ) ≫
      NatTrans.mapHomologicalComplex (restrictionToComplement X Z hZ)
        (ComplexShape.up ℤ) = 0 := by
    rw [← NatTrans.mapHomologicalComplex_comp, kernel.condition]
    ext K n x
    rfl
  simpa [f, g] using NatTrans.congr_app hmap I

/-- At an injective module sheaf, `Γ_Z(X, -) ⟶ Γ(X, -) ⟶ Γ(U, -)` is short exact. -/
private lemma sectionsWithSupport_module_shortExact
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    (I : ModuleSheaves X) [Injective I] :
    (ShortComplex.mk ((kernel.ι (restrictionToComplement X Z hZ)).app I)
      ((restrictionToComplement X Z hZ).app I) (by
        exact NatTrans.congr_app (kernel.condition
          (restrictionToComplement X Z hZ)) I)).ShortExact := by
  have hkernel := isLimitOfHasKernelOfPreservesLimit
    ((evaluation (ModuleSheaves X) (GlobalModules X)).obj I)
    (restrictionToComplement X Z hZ)
  exact { exact := ShortComplex.exact_of_f_is_kernel _ hkernel
          mono_f := inferInstance
          epi_g := epi_restrictionToComplement_app_of_injective X Z hZ I }

/-- At a complex with injective terms, `Γ_Z(X, -) ⟶ Γ(X, -) ⟶ Γ(U, -)` is short exact. -/
private lemma sectionsWithSupport_complex_shortExact
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    (I : CochainComplex (ModuleSheaves X) ℤ)
    [∀ n, Injective (I.X n)] : (sectionsWithSupportShortComplex X Z hZ I).ShortExact := by
  exact (HomologicalComplex.shortExact_iff_degreewise_shortExact _).2 fun n =>
    sectionsWithSupport_module_shortExact X Z hZ (I.X n)

/-- A morphism of complexes induces a morphism of the associated short complexes. -/
private def sectionsWithSupportShortComplexMap
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    {I J : CochainComplex (ModuleSheaves X) ℤ} (f : I ⟶ J) :
    sectionsWithSupportShortComplex X Z hZ I ⟶ sectionsWithSupportShortComplex X Z hZ J := by
  letI : (kernel (restrictionToComplement X Z hZ)).PreservesZeroMorphisms :=
    sectionsWithSupport_preservesZeroMorphisms X Z hZ
  let t₁ := (kernel (restrictionToComplement X Z hZ)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let t₂ := (SheafOfModules.evaluation (structureSheafRing X) (op ⊤))
      |>.mapHomologicalComplex (ComplexShape.up ℤ)
  let t₃ := (sectionsOnComplement X Z hZ).mapHomologicalComplex (ComplexShape.up ℤ)
  refine ShortComplex.homMk (t₁.map f) (t₂.map f) (t₃.map f) ?_ ?_
  · exact NatTrans.naturality
      (NatTrans.mapHomologicalComplex (kernel.ι (restrictionToComplement X Z hZ))
        (ComplexShape.up ℤ)) f
  · exact NatTrans.naturality
      (NatTrans.mapHomologicalComplex (restrictionToComplement X Z hZ)
        (ComplexShape.up ℤ)) f

/-! ### K-injective complexes with injective terms compute the derived category -/

/-- The K-injective complexes with injective terms, as a property of objects of the homotopy
category. -/
private abbrev kInjectiveObjects (X : RingedSpace.{u, u}) :
    ObjectProperty (HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ)) :=
  fun I => CochainComplex.IsKInjective I.as ∧ ∀ n, Injective (I.as.X n)

/-- The comparison functor from the K-injective complexes with injective terms to the
derived category. -/
private noncomputable abbrev kInjectiveQ (X : RingedSpace.{u, u}) :
    (kInjectiveObjects X).FullSubcategory ⥤ DerivedModuleSheaves X :=
  (kInjectiveObjects X).ι ⋙ DerivedCategory.Qh

private lemma kInjectiveQ_map_bijective (X : RingedSpace.{u, u})
    (I J : (kInjectiveObjects X).FullSubcategory) :
    Function.Bijective ((kInjectiveQ X).map : (I ⟶ J) → _) := by
  let _ : CochainComplex.IsKInjective J.1.as := J.property.1
  exact (CochainComplex.IsKInjective.Qh_map_bijective I.obj J.1.as).comp
    (Functor.FullyFaithful.ofFullyFaithful (kInjectiveObjects X).ι).homEquiv.bijective

private lemma kInjectiveQ_full (X : RingedSpace.{u, u}) : (kInjectiveQ X).Full where
  map_surjective := (kInjectiveQ_map_bijective X _ _).surjective

private lemma kInjectiveQ_faithful (X : RingedSpace.{u, u}) : (kInjectiveQ X).Faithful where
  map_injective h := (kInjectiveQ_map_bijective X _ _).injective h

private lemma kInjectiveQ_essSurj (X : RingedSpace.{u, u}) : (kInjectiveQ X).EssSurj where
  mem_essImage K := by
    let K₀ := DerivedCategory.Q.objPreimage K
    let I := (kInjectiveResolutionFunctor X).obj K₀
    exact ⟨⟨(HomotopyCategory.quotient _ _).obj I,
      kInjectiveResolutionFunctor_obj_isKInjective X K₀,
      kInjectiveResolutionFunctor_obj_X_injective X K₀⟩,
      ⟨(DerivedCategory.quotientCompQhIso (ModuleSheaves X)).app I ≪≫
        (asIso (DerivedCategory.Q.map ((kInjectiveResolutionInclusion X).app K₀))).symm ≪≫
        DerivedCategory.Q.objObjPreimageIso K⟩⟩

/-- The K-injective complexes with injective terms are equivalent to the unbounded derived
category. -/
private noncomputable def kInjectiveEquivalence (X : RingedSpace.{u, u}) :
    (kInjectiveObjects X).FullSubcategory ≌ DerivedModuleSheaves X := by
  haveI : (kInjectiveQ X).Full := kInjectiveQ_full X
  haveI : (kInjectiveQ X).Faithful := kInjectiveQ_faithful X
  haveI : (kInjectiveQ X).EssSurj := kInjectiveQ_essSurj X
  haveI : (kInjectiveQ X).IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact (kInjectiveQ X).asEquivalence

/-! ### Comparing the homotopy-category route with the complex-level route -/

/-- Applying an additive functor on homotopy categories and then localizing agrees with
applying it on complexes and then localizing. -/
private noncomputable def mapHomotopyQFunctorIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        F.mapHomotopyCategory (ComplexShape.up ℤ)) ⋙ DerivedCategory.Qh ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso B)

/-- The object component of `mapHomotopyQFunctorIso`. -/
private noncomputable def mapHomotopyQObjIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (mapHomotopyQFunctorIso F).app K

private lemma mapHomotopyQObjIso_naturality
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] {I J : CochainComplex A ℤ} (f : I ⟶ J) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) ≫
      (mapHomotopyQObjIso F J).hom =
    (mapHomotopyQObjIso F I).hom ≫
    DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
  (mapHomotopyQFunctorIso F).hom.naturality f

private lemma mapHomotopyQObjIso_hom_app
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) :
    (mapHomotopyQObjIso F K).hom =
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  simp [mapHomotopyQObjIso, mapHomotopyQFunctorIso]

private lemma mapHomotopyQObjIso_naturalityNatTrans
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (τ : F ⟶ G)
    (K : CochainComplex A ℤ) :
    DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
      (mapHomotopyQObjIso G K).hom =
    (mapHomotopyQObjIso F K).hom ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ
        (ComplexShape.up ℤ)).app K) := by
  let c := ComplexShape.up ℤ
  let qA := HomotopyCategory.quotient A c
  let qB := HomotopyCategory.quotient B c
  let τK := (NatTrans.mapHomologicalComplex τ c).app K
  have hFactors :
      (NatTrans.mapHomotopyCategory τ c).app (qA.obj K) ≫
          (G.mapHomotopyCategoryFactors c).hom.app K =
          (F.mapHomotopyCategoryFactors c).hom.app K ≫ qB.map τK := by
    dsimp [NatTrans.mapHomotopyCategory]
    change qB.map τK ≫ 𝟙 _ = 𝟙 _ ≫ qB.map τK
    cat_disch
  rw [mapHomotopyQObjIso_hom_app, mapHomotopyQObjIso_hom_app]
  calc
    _ = DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory τ c).app (qA.obj K) ≫
            (G.mapHomotopyCategoryFactors c).hom.app K) ≫
          (DerivedCategory.quotientCompQhIso B).hom.app
            ((G.mapHomologicalComplex c).obj K) := by
              simp only [Functor.map_comp]
              cat_disch
    _ = DerivedCategory.Qh.map
          ((F.mapHomotopyCategoryFactors c).hom.app K ≫ qB.map τK) ≫
          (DerivedCategory.quotientCompQhIso B).hom.app
            ((G.mapHomologicalComplex c).obj K) := by rw [hFactors]
    _ = _ := by
      have hcomp : DerivedCategory.Qh.map (qB.map τK) ≫
          (DerivedCategory.quotientCompQhIso B).hom.app
            ((G.mapHomologicalComplex c).obj K) =
        (DerivedCategory.quotientCompQhIso B).hom.app
            ((F.mapHomologicalComplex c).obj K) ≫ DerivedCategory.Q.map τK := by
        simpa only [Functor.comp_map] using
          (DerivedCategory.quotientCompQhIso B).hom.naturality τK
      rw [Functor.map_comp, Category.assoc, hcomp]
      cat_disch

/-! ### The connecting morphism on K-injective complexes -/

/-- Sections on the complement, restricted to the K-injective complexes with injective
terms. -/
private noncomputable abbrev supportOnComplementKI
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z) :=
  (kInjectiveObjects X).ι ⋙
    (sectionsOnComplement X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh

/-- Global sections, restricted to the K-injective complexes with injective terms. -/
private noncomputable abbrev globalSectionsKI (X : RingedSpace.{u, u}) :=
  (kInjectiveObjects X).ι ⋙
  Functor.mapHomotopyCategory
    (SheafOfModules.evaluation (structureSheafRing X) (op ⊤))
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Sections with support, restricted to the K-injective complexes with injective terms. -/
private noncomputable abbrev sectionsWithSupportKI
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z) :=
  (kInjectiveObjects X).ι ⋙
    (sectionsWithSupport X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh

/-- The naturality square for a connecting morphism conjugated by comparison isomorphisms. -/
private lemma boundary_naturality_aux {D : Type*} [Category* D] (S : D ⥤ D)
    {A₁ A₂ B₁ B₂ C₁ C₂ E₁ E₂ : D}
    (a : A₁ ⟶ A₂) (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂) (b : B₁ ⟶ B₂)
    (d₁ : B₁ ⟶ S.obj C₁) (d₂ : B₂ ⟶ S.obj C₂)
    (t : C₁ ⟶ C₂) (z₁ : C₁ ⟶ E₁) (z₂ : C₂ ⟶ E₂) (c : E₁ ⟶ E₂)
    (hu : a ≫ u₂ = u₁ ≫ b)
    (hd : d₁ ≫ S.map t = b ≫ d₂)
    (hz : t ≫ z₂ = z₁ ≫ c) :
    a ≫ u₂ ≫ d₂ ≫ S.map z₂ = (u₁ ≫ d₁ ≫ S.map z₁) ≫ S.map c := by
  rw [← Category.assoc, hu, Category.assoc, Category.assoc, ← Category.assoc b, ← hd,
    Category.assoc, Category.assoc, ← S.map_comp, hz, S.map_comp]

/-- Postcomposing with the shift of an isomorphism cancels the shift of its inverse. -/
private lemma comp_shift_map_inv_hom {D : Type*} [Category* D] (S : D ⥤ D)
    {A B C₁ C₂ : D} (u : A ⟶ B) (z : C₁ ≅ C₂) (d : B ⟶ S.obj C₂) :
    (u ≫ d ≫ S.map z.inv) ≫ S.map z.hom = u ≫ d := by
  rw [Category.assoc, Category.assoc, ← S.map_comp, z.inv_hom_id, S.map_id,
    Category.comp_id]

/-- Substituting one factorization of a composite for another, under a further
postcomposition. -/
private lemma comp_assoc_subst {D : Type*} [Category* D] {A B B' C E : D}
    {x : A ⟶ B} {y : B ⟶ C} {x' : A ⟶ B'} {y' : B' ⟶ C} (h : x ≫ y = x' ≫ y')
    (e : C ⟶ E) : x ≫ y ≫ e = x' ≫ y' ≫ e := by
  rw [← Category.assoc, h, Category.assoc]

/-- The connecting morphism of the short exact sequence of sections, on the K-injective
complexes with injective terms. -/
private noncomputable def sectionsWithSupportBoundaryOnKInjectives
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z) :
    supportOnComplementKI X Z hZ ⟶
      sectionsWithSupportKI X Z hZ ⋙ shiftFunctor (DerivedGlobalModules X) (1 : ℤ) := by
  refine { app := fun I => ?_, naturality := ?_ }
  · letI : ∀ n, Injective (I.1.as.X n) := I.property.2
    let K : CochainComplex (ModuleSheaves X) ℤ := CategoryTheory.Quotient.as I.1
    let hS := sectionsWithSupport_complex_shortExact X Z hZ K
    exact (mapHomotopyQObjIso (sectionsOnComplement X Z hZ) K).hom ≫
      DerivedCategory.triangleOfSESδ hS ≫
        (shiftFunctor (DerivedGlobalModules X) (1 : ℤ)).map
          (mapHomotopyQObjIso (sectionsWithSupport X Z hZ) K).inv
  · intro I J f
    rcases I with ⟨I, hI⟩
    rcases J with ⟨J, hJ⟩
    obtain ⟨f₀, hf₀⟩ :=
      (HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).map_surjective f.hom
    let K := I.as
    let L := J.as
    let _ : ∀ n, Injective (K.X n) := hI.2
    let _ : ∀ n, Injective (L.X n) := hJ.2
    let hSI := sectionsWithSupport_complex_shortExact X Z hZ K
    let hSJ := sectionsWithSupport_complex_shortExact X Z hZ L
    let φ := sectionsWithSupportShortComplexMap X Z hZ f₀
    let eU₁ := mapHomotopyQObjIso (sectionsOnComplement X Z hZ) K
    let eU₂ := mapHomotopyQObjIso (sectionsOnComplement X Z hZ) L
    let eZ₁ := mapHomotopyQObjIso (sectionsWithSupport X Z hZ) K
    let eZ₂ := mapHomotopyQObjIso (sectionsWithSupport X Z hZ) L
    have heU := mapHomotopyQObjIso_naturality (sectionsOnComplement X Z hZ) f₀
    have heZ := mapHomotopyQObjIso_naturality (sectionsWithSupport X Z hZ) f₀
    have heZ' : DerivedCategory.Q.map
          (((sectionsWithSupport X Z hZ).mapHomologicalComplex (ComplexShape.up ℤ)).map f₀) ≫
        eZ₂.inv = eZ₁.inv ≫
          ((sectionsWithSupport X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh).map ((HomotopyCategory.quotient _ _).map f₀) := by
      calc
        _ = eZ₁.inv ≫
            ((eZ₁.hom ≫ DerivedCategory.Q.map
              (((sectionsWithSupport X Z hZ).mapHomologicalComplex
                (ComplexShape.up ℤ)).map f₀)) ≫
              eZ₂.inv) := by simp [Category.assoc]
        _ = eZ₁.inv ≫
            ((((sectionsWithSupport X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              DerivedCategory.Qh).map ((HomotopyCategory.quotient _ _).map f₀) ≫ eZ₂.hom) ≫
              eZ₂.inv) := by rw [← heZ]
        _ = _ := by simp [Category.assoc]
    let _ : (kernel (restrictionToComplement X Z hZ)).PreservesZeroMorphisms :=
      sectionsWithSupport_preservesZeroMorphisms X Z hZ
    have hφ₁ : φ.τ₁ =
        (((kernel (restrictionToComplement X Z hZ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f₀) := rfl
    have hφ₁' : φ.τ₁ =
        (((sectionsWithSupport X Z hZ).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f₀) := by
      simpa [sectionsWithSupport] using hφ₁
    have hφ₃ : φ.τ₃ =
        (((sectionsOnComplement X Z hZ).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f₀) := rfl
    change ((sectionsOnComplement X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).map f.hom ≫ eU₂.hom ≫
          DerivedCategory.triangleOfSESδ hSJ ≫
            (shiftFunctor (DerivedGlobalModules X) (1 : ℤ)).map eZ₂.inv =
      (eU₁.hom ≫ DerivedCategory.triangleOfSESδ hSI ≫
        (shiftFunctor (DerivedGlobalModules X) (1 : ℤ)).map eZ₁.inv) ≫
        (shiftFunctor (DerivedGlobalModules X) (1 : ℤ)).map
          (((sectionsWithSupport X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh).map f.hom)
    have hu : ((sectionsOnComplement X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).map
            ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).map f₀) ≫
          eU₂.hom = eU₁.hom ≫ DerivedCategory.Q.map φ.τ₃ := by
      rw [hφ₃]; exact heU
    have hd : DerivedCategory.triangleOfSESδ hSI ≫
          (shiftFunctor (DerivedGlobalModules X) (1 : ℤ)).map
            (DerivedCategory.Q.map φ.τ₁) =
          DerivedCategory.Q.map φ.τ₃ ≫ DerivedCategory.triangleOfSESδ hSJ :=
      DerivedCategory.triangleOfSESδ_naturality hSI hSJ φ
    have hz : DerivedCategory.Q.map φ.τ₁ ≫ eZ₂.inv = eZ₁.inv ≫
          ((sectionsWithSupport X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh).map
              ((HomotopyCategory.quotient (ModuleSheaves X)
                (ComplexShape.up ℤ)).map f₀) := by
      rw [hφ₁']; exact heZ'
    rw [← hf₀]
    exact boundary_naturality_aux (shiftFunctor (DerivedGlobalModules X) (1 : ℤ))
      _ _ _ _ _ _ _ _ _ _ hu hd hz

/-! ### The canonical right derived functor and its value on K-injectives -/

/-- The quasi-isomorphisms in the homotopy category of module sheaves. -/
private abbrev quasiIsoOnHomotopy (X : RingedSpace.{u, u}) :=
  HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)

/-- The total right derived functor of a functor on the homotopy category. -/
private noncomputable def canonicalRightDerived
    (X : RingedSpace.{u, u})
    (F : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤ DerivedGlobalModules X)
    [F.HasRightDerivedFunctor (quasiIsoOnHomotopy X)] :=
  F.totalRightDerived DerivedCategory.Qh (quasiIsoOnHomotopy X)

/-- The unit of the total right derived functor. -/
private noncomputable def canonicalRightDerivedUnit
    (X : RingedSpace.{u, u})
    (F : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤ DerivedGlobalModules X)
    [F.HasRightDerivedFunctor (quasiIsoOnHomotopy X)] :
    F ⟶ DerivedCategory.Qh ⋙ canonicalRightDerived X F :=
  F.totalRightDerivedUnit DerivedCategory.Qh (quasiIsoOnHomotopy X)

private instance canonicalRightDerived_isRightDerivedFunctor
    (X : RingedSpace.{u, u})
    (F : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤ DerivedGlobalModules X)
    [F.HasRightDerivedFunctor (quasiIsoOnHomotopy X)] :
    (canonicalRightDerived X F).IsRightDerivedFunctor
      (canonicalRightDerivedUnit X F) (quasiIsoOnHomotopy X) :=
  inferInstanceAs ((F.totalRightDerived DerivedCategory.Qh
    (quasiIsoOnHomotopy X)).IsRightDerivedFunctor
      (F.totalRightDerivedUnit DerivedCategory.Qh (quasiIsoOnHomotopy X))
      (quasiIsoOnHomotopy X))

/-- Every complex of module sheaves admits a quasi-isomorphism into a K-injective complex. -/
private lemma exists_quasiIso_isKInjective (X : RingedSpace.{u, u})
    (K : CochainComplex (ModuleSheaves X) ℤ) :
    ∃ (J : CochainComplex (ModuleSheaves X) ℤ) (f : K ⟶ J), J.IsKInjective ∧ QuasiIso f :=
  ⟨(kInjectiveResolutionFunctor X).obj K, (kInjectiveResolutionInclusion X).app K,
    kInjectiveResolutionFunctor_obj_isKInjective X K,
    kInjectiveResolutionInclusion_quasiIso X K⟩

/-- The unit of the total right derived functor is an isomorphism at a K-injective
complex. -/
private lemma canonicalRightDerivedUnit_isIso
    (X : RingedSpace.{u, u})
    (F : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤ DerivedGlobalModules X)
    [F.HasRightDerivedFunctor (quasiIsoOnHomotopy X)]
    (I : CochainComplex (ModuleSheaves X) ℤ) (hI : I.IsKInjective) :
    IsIso ((canonicalRightDerivedUnit X F).app
      ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    F (exists_quasiIso_isKInjective X)).2 DerivedCategory.Qh (canonicalRightDerived X F)
      (canonicalRightDerivedUnit X F) I hI

/-- On the K-injective complexes with injective terms, the total right derived functor is
the functor itself. -/
private noncomputable def canonicalRightDerivedOnKInjectivesIso
    (X : RingedSpace.{u, u})
    (F : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤ DerivedGlobalModules X)
    [F.HasRightDerivedFunctor (quasiIsoOnHomotopy X)] :
    (kInjectiveQ X) ⋙ canonicalRightDerived X F ≅
      (kInjectiveObjects X).ι ⋙ F := by
  let η := Functor.whiskerLeft (kInjectiveObjects X).ι (canonicalRightDerivedUnit X F)
  have (I : (kInjectiveObjects X).FullSubcategory) : IsIso (η.app I) :=
    canonicalRightDerivedUnit_isIso X F I.1.as I.property.1
  exact NatIso.ofComponents (fun I => (asIso (η.app I)).symm) (by
    intro I J f
    apply (cancel_mono (η.app J)).1
    simp only [Category.assoc]
    rw [η.naturality f]
    simp)

/-- The total right derived functor is the one computed on K-injective complexes with
injective terms, transported along the equivalence. -/
private noncomputable def canonicalRightDerivedComparisonIso
    (X : RingedSpace.{u, u})
    (F : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤ DerivedGlobalModules X)
    [F.HasRightDerivedFunctor (quasiIsoOnHomotopy X)] :
    canonicalRightDerived X F ≅
      (kInjectiveEquivalence X).inverse ⋙ (kInjectiveObjects X).ι ⋙ F :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight ((kInjectiveEquivalence X).counitIso).symm
      (canonicalRightDerived X F) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (kInjectiveEquivalence X).inverse
      (canonicalRightDerivedOnKInjectivesIso X F)

/-- The component of `canonicalRightDerivedComparisonIso`, written out. -/
private lemma canonicalRightDerivedComparisonIso_hom_app
    (X : RingedSpace.{u, u})
    (F : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤ DerivedGlobalModules X)
    [F.HasRightDerivedFunctor (quasiIsoOnHomotopy X)]
    (K : DerivedModuleSheaves X) :
    (canonicalRightDerivedComparisonIso X F).hom.app K =
      (canonicalRightDerived X F).map ((kInjectiveEquivalence X).counitIso.inv.app K) ≫
        (canonicalRightDerivedOnKInjectivesIso X F).hom.app
          ((kInjectiveEquivalence X).inverse.obj K) := by
  simp only [canonicalRightDerivedComparisonIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.comp_obj,
    Functor.leftUnitor_inv_app, NatTrans.comp_app, Iso.symm_hom]
  cat_disch

/-- The functor computed on K-injective complexes with injective terms, as a candidate for
the right derived functor. -/
private noncomputable abbrev kInjectiveRightDerivedCandidate
    (X : RingedSpace.{u, u})
    (F : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤ DerivedGlobalModules X) :=
  (kInjectiveEquivalence X).inverse ⋙ (kInjectiveObjects X).ι ⋙ F

/-- The unit of the candidate. -/
private noncomputable def kInjectiveRightDerivedCandidateUnit
    (X : RingedSpace.{u, u})
    (F : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤ DerivedGlobalModules X)
    [F.HasRightDerivedFunctor (quasiIsoOnHomotopy X)] :
    F ⟶ DerivedCategory.Qh ⋙ kInjectiveRightDerivedCandidate X F :=
  canonicalRightDerivedUnit X F ≫
    Functor.whiskerLeft DerivedCategory.Qh
      (canonicalRightDerivedComparisonIso X F).hom

private lemma kInjectiveRightDerivedCandidate_isRightDerived
    (X : RingedSpace.{u, u})
    (F : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤ DerivedGlobalModules X)
    [F.HasRightDerivedFunctor (quasiIsoOnHomotopy X)] :
    (kInjectiveRightDerivedCandidate X F).IsRightDerivedFunctor
      (kInjectiveRightDerivedCandidateUnit X F) (quasiIsoOnHomotopy X) := by
  apply (Functor.isRightDerivedFunctor_iff_of_iso
    (canonicalRightDerivedUnit X F) (kInjectiveRightDerivedCandidateUnit X F)
    (quasiIsoOnHomotopy X) (canonicalRightDerivedComparisonIso X F)
    (by simp [kInjectiveRightDerivedCandidateUnit])).mp
  infer_instance

attribute [local instance] kInjectiveRightDerivedCandidate_isRightDerived

/-- The comparison isomorphism is natural: a natural transformation `τ` and a lift `δ` of it
to the total right derived functors become the whiskering of `τ`. -/
private lemma canonicalRightDerivedComparisonIso_naturality
    (X : RingedSpace.{u, u})
    (F G : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤
      DerivedGlobalModules X)
    [F.HasRightDerivedFunctor (quasiIsoOnHomotopy X)]
    [G.HasRightDerivedFunctor (quasiIsoOnHomotopy X)]
    (τ : F ⟶ G)
    (δ : canonicalRightDerived X F ⟶ canonicalRightDerived X G)
    (hδ : canonicalRightDerivedUnit X F ≫ Functor.whiskerLeft DerivedCategory.Qh δ =
      τ ≫ canonicalRightDerivedUnit X G) :
    δ ≫
      (canonicalRightDerivedComparisonIso X G).hom =
      (canonicalRightDerivedComparisonIso X F).hom ≫
      Functor.whiskerLeft ((kInjectiveEquivalence X).inverse ⋙
        (kInjectiveObjects X).ι) τ := by
  let E := kInjectiveEquivalence X
  let eF := canonicalRightDerivedOnKInjectivesIso X F
  let eG := canonicalRightDerivedOnKInjectivesIso X G
  have hE : Functor.whiskerLeft (kInjectiveQ X) δ ≫ eG.hom =
      eF.hom ≫ Functor.whiskerLeft (kInjectiveObjects X).ι τ := by
    ext I
    let ηF := Functor.whiskerLeft (kInjectiveObjects X).ι
      (canonicalRightDerivedUnit X F)
    let ηG := Functor.whiskerLeft (kInjectiveObjects X).ι
      (canonicalRightDerivedUnit X G)
    have : IsIso (ηF.app I) := canonicalRightDerivedUnit_isIso X F I.1.as I.property.1
    have : IsIso (ηG.app I) := canonicalRightDerivedUnit_isIso X G I.1.as I.property.1
    have hfac : ηF.app I ≫ δ.app ((kInjectiveQ X).obj I) =
        τ.app I.1 ≫ ηG.app I := NatTrans.congr_app hδ I.1
    change δ.app ((kInjectiveQ X).obj I) ≫ (asIso (ηG.app I)).inv =
      (asIso (ηF.app I)).inv ≫ τ.app I.1
    apply (cancel_epi (ηF.app I)).1
    apply (cancel_mono (ηG.app I)).1
    simpa [Category.assoc] using hfac
  ext K
  have hEi : δ.app ((kInjectiveQ X).obj (E.inverse.obj K)) ≫
      eG.hom.app (E.inverse.obj K) =
      eF.hom.app (E.inverse.obj K) ≫ τ.app (E.inverse.obj K).1 :=
    NatTrans.congr_app hE (E.inverse.obj K)
  change δ.app K ≫ (canonicalRightDerivedComparisonIso X G).hom.app K =
    (canonicalRightDerivedComparisonIso X F).hom.app K ≫ τ.app (E.inverse.obj K).1
  rw [canonicalRightDerivedComparisonIso_hom_app,
    canonicalRightDerivedComparisonIso_hom_app]
  calc
    δ.app K ≫ (canonicalRightDerived X G).map (E.counitIso.inv.app K) ≫
          eG.hom.app (E.inverse.obj K) =
        (canonicalRightDerived X F).map (E.counitIso.inv.app K) ≫
          δ.app (E.functor.obj (E.inverse.obj K)) ≫ eG.hom.app (E.inverse.obj K) :=
            comp_assoc_subst (δ.naturality (E.counitIso.inv.app K)).symm
              (eG.hom.app (E.inverse.obj K))
    _ = (canonicalRightDerived X F).map (E.counitIso.inv.app K) ≫
          eF.hom.app (E.inverse.obj K) ≫ τ.app (E.inverse.obj K).1 :=
            congrArg ((canonicalRightDerived X F).map (E.counitIso.inv.app K) ≫ ·) hEi
    _ = _ := (Category.assoc _ _ _).symm

/-- Any right derived functor is isomorphic to the candidate computed on K-injective
complexes with injective terms. -/
private noncomputable def rightDerivedToKInjectiveCandidateIso
    (X : RingedSpace.{u, u})
    (F : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤ DerivedGlobalModules X)
    (RF : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (quasiIsoOnHomotopy X)] :
    RF ≅ kInjectiveRightDerivedCandidate X F := by
  letI : F.HasRightDerivedFunctor (quasiIsoOnHomotopy X) :=
    Functor.HasRightDerivedFunctor.mk' RF α
  exact Functor.rightDerivedUnique RF (kInjectiveRightDerivedCandidate X F) α
    (kInjectiveRightDerivedCandidateUnit X F) (quasiIsoOnHomotopy X)

/-! ### The triangle on K-injective complexes -/

/-- On a K-injective complex with injective terms, the triangle of sections with support is
the canonical triangle of a short exact sequence of complexes, hence distinguished. -/
private lemma sectionsWithSupportTriangleOnKInjectives_distinguished
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    (I : (kInjectiveObjects X).FullSubcategory) :
    Triangle.mk
      ((Functor.whiskerLeft (kInjectiveObjects X).ι
        (Functor.whiskerRight
          ((show sectionsWithSupport X Z hZ ⟶
              SheafOfModules.evaluation
                (structureSheafRing X) (op ⊤) from
            kernel.ι (restrictionToComplement X Z hZ)).mapHomotopyCategory
              (ComplexShape.up ℤ)) DerivedCategory.Qh)).app I)
      ((Functor.whiskerLeft (kInjectiveObjects X).ι
        (Functor.whiskerRight
          ((restrictionToComplement X Z hZ).mapHomotopyCategory
            (ComplexShape.up ℤ)) DerivedCategory.Qh)).app I)
      ((sectionsWithSupportBoundaryOnKInjectives X Z hZ).app I) ∈
        distTriang (DerivedGlobalModules X) := by
  rcases I with ⟨I', hI'⟩
  cases I' with
  | mk K =>
      let I : (kInjectiveObjects X).FullSubcategory :=
        ⟨(HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).obj K, hI'⟩
      change Triangle.mk
          ((Functor.whiskerLeft (kInjectiveObjects X).ι
            (Functor.whiskerRight
              ((show sectionsWithSupport X Z hZ ⟶
                  SheafOfModules.evaluation
                    (structureSheafRing X) (op ⊤) from
                kernel.ι (restrictionToComplement X Z hZ)).mapHomotopyCategory
                  (ComplexShape.up ℤ)) DerivedCategory.Qh)).app I)
          ((Functor.whiskerLeft (kInjectiveObjects X).ι
            (Functor.whiskerRight
              ((restrictionToComplement X Z hZ).mapHomotopyCategory
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app I)
          ((sectionsWithSupportBoundaryOnKInjectives X Z hZ).app I) ∈ _
      let _ : ∀ n, Injective (K.X n) := hI'.2
      let _ : (kernel (restrictionToComplement X Z hZ)).Additive :=
        sectionsWithSupport_additive X Z hZ
      let hS := sectionsWithSupport_complex_shortExact X Z hZ K
      let T₀ := DerivedCategory.triangleOfSES hS
      let T := Triangle.mk
        ((Functor.whiskerLeft (kInjectiveObjects X).ι
          (Functor.whiskerRight
            ((show sectionsWithSupport X Z hZ ⟶
                SheafOfModules.evaluation
                  (structureSheafRing X) (op ⊤) from
              kernel.ι (restrictionToComplement X Z hZ)).mapHomotopyCategory
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app I)
        ((Functor.whiskerLeft (kInjectiveObjects X).ι
          (Functor.whiskerRight
            ((restrictionToComplement X Z hZ).mapHomotopyCategory
              (ComplexShape.up ℤ)) DerivedCategory.Qh)).app I)
        ((sectionsWithSupportBoundaryOnKInjectives X Z hZ).app I)
      let eZ := mapHomotopyQObjIso (kernel (restrictionToComplement X Z hZ)) K
      let eX := mapHomotopyQObjIso
        (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) K
      let eU := mapHomotopyQObjIso (sectionsOnComplement X Z hZ) K
      refine isomorphic_distinguished T₀ (DerivedCategory.triangleOfSES_distinguished hS) T ?_
      refine Triangle.isoMk T T₀ eZ eX eU ?_ ?_ ?_
      · exact mapHomotopyQObjIso_naturalityNatTrans
          (kernel.ι (restrictionToComplement X Z hZ)) K
      · exact mapHomotopyQObjIso_naturalityNatTrans
          (restrictionToComplement X Z hZ) K
      · exact comp_shift_map_inv_hom (shiftFunctor (DerivedGlobalModules X) (1 : ℤ))
          _ (mapHomotopyQObjIso (sectionsWithSupport X Z hZ) K) _

/-! ### The triangle for arbitrary right derived functors -/

/-- The isomorphism with the candidate is compatible with the unit of the candidate. -/
private lemma rightDerivedToKInjectiveCandidateIso_unit
    (X : RingedSpace.{u, u})
    (F : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤ DerivedGlobalModules X)
    (RF : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [F.HasRightDerivedFunctor (quasiIsoOnHomotopy X)]
    [RF.IsRightDerivedFunctor α (quasiIsoOnHomotopy X)] :
    α ≫ Functor.whiskerLeft DerivedCategory.Qh
      (rightDerivedToKInjectiveCandidateIso X F RF α).hom =
        kInjectiveRightDerivedCandidateUnit X F :=
  (Functor.rightDerivedNatTrans_fac RF (kInjectiveRightDerivedCandidate X F) α
    (kInjectiveRightDerivedCandidateUnit X F) (quasiIsoOnHomotopy X) (𝟙 F)).trans
      (Category.id_comp _)

/-- A natural transformation of right derived functors, compatible with `τ` through the units,
is compatible with `τ` through the isomorphisms with the candidates. -/
private lemma rightDerivedToKInjectiveCandidateIso_naturality
    (X : RingedSpace.{u, u})
    (F G : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤ DerivedGlobalModules X)
    (RF RG : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
    (αF : F ⟶ DerivedCategory.Qh ⋙ RF) (αG : G ⟶ DerivedCategory.Qh ⋙ RG)
    [F.HasRightDerivedFunctor (quasiIsoOnHomotopy X)]
    [G.HasRightDerivedFunctor (quasiIsoOnHomotopy X)]
    [RF.IsRightDerivedFunctor αF (quasiIsoOnHomotopy X)]
    [RG.IsRightDerivedFunctor αG (quasiIsoOnHomotopy X)]
    (τ : F ⟶ G) (ν : RF ⟶ RG)
    (hν : αF ≫ Functor.whiskerLeft DerivedCategory.Qh ν = τ ≫ αG) :
    ν ≫ (rightDerivedToKInjectiveCandidateIso X G RG αG).hom =
      (rightDerivedToKInjectiveCandidateIso X F RF αF).hom ≫
        Functor.whiskerLeft ((kInjectiveEquivalence X).inverse ⋙
          (kInjectiveObjects X).ι) τ := by
  let δ := Functor.rightDerivedNatTrans (canonicalRightDerived X F)
    (canonicalRightDerived X G) (canonicalRightDerivedUnit X F)
    (canonicalRightDerivedUnit X G) (quasiIsoOnHomotopy X) τ
  have hδ : canonicalRightDerivedUnit X F ≫ Functor.whiskerLeft DerivedCategory.Qh δ =
      τ ≫ canonicalRightDerivedUnit X G :=
    Functor.rightDerivedNatTrans_fac _ _ _ _ _ τ
  have hCmp := canonicalRightDerivedComparisonIso_naturality X F G τ δ hδ
  have hUnit : τ ≫ kInjectiveRightDerivedCandidateUnit X G =
      kInjectiveRightDerivedCandidateUnit X F ≫ Functor.whiskerLeft DerivedCategory.Qh
        (Functor.whiskerLeft ((kInjectiveEquivalence X).inverse ⋙
          (kInjectiveObjects X).ι) τ) := by
    change τ ≫ (canonicalRightDerivedUnit X G ≫ Functor.whiskerLeft DerivedCategory.Qh
        (canonicalRightDerivedComparisonIso X G).hom) =
      (canonicalRightDerivedUnit X F ≫ Functor.whiskerLeft DerivedCategory.Qh
        (canonicalRightDerivedComparisonIso X F).hom) ≫ Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerLeft ((kInjectiveEquivalence X).inverse ⋙
            (kInjectiveObjects X).ι) τ)
    rw [← Category.assoc, ← hδ, Category.assoc, Category.assoc,
      ← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp, hCmp]
  apply Functor.rightDerived_ext RF αF (quasiIsoOnHomotopy X)
  simp only [Functor.whiskerLeft_comp]
  rw [← Category.assoc, hν, Category.assoc, rightDerivedToKInjectiveCandidateIso_unit X G RG αG,
    hUnit, ← rightDerivedToKInjectiveCandidateIso_unit X F RF αF, Category.assoc]

/-- The triangle data, constructed from the comparison with the K-injective complexes with
injective terms. -/
private noncomputable def sectionsWithSupportTriangleData
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    (RΓZ RΓ RΓU : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
    (aZ : homotopyToDerived X (sectionsWithSupport X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓZ)
    (aX : homotopyToDerived X
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) ⟶
        DerivedCategory.Qh ⋙ RΓ)
    (aU : homotopyToDerived X (sectionsOnComplement X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓU)
    [RΓZ.IsRightDerivedFunctor aZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓ.IsRightDerivedFunctor aX
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :
    SectionsWithSupportTriangleData X RΓZ RΓ RΓU
      (derivedSupportInclusion X Z hZ RΓZ RΓ aZ aX)
      (derivedRestrictionToComplement X Z hZ RΓ RΓU aX aU) := by
  let FZ := homotopyToDerived X (sectionsWithSupport X Z hZ)
  let FX := homotopyToDerived X
    (SheafOfModules.evaluation (structureSheafRing X) (op ⊤))
  let FU := homotopyToDerived X (sectionsOnComplement X Z hZ)
  letI : FZ.HasRightDerivedFunctor (quasiIsoOnHomotopy X) :=
    Functor.HasRightDerivedFunctor.mk' RΓZ aZ
  letI : FX.HasRightDerivedFunctor (quasiIsoOnHomotopy X) :=
    Functor.HasRightDerivedFunctor.mk' RΓ aX
  letI : FU.HasRightDerivedFunctor (quasiIsoOnHomotopy X) :=
    Functor.HasRightDerivedFunctor.mk' RΓU aU
  let eZ := rightDerivedToKInjectiveCandidateIso X FZ RΓZ aZ
  let eX := rightDerivedToKInjectiveCandidateIso X FX RΓ aX
  let eU := rightDerivedToKInjectiveCandidateIso X FU RΓU aU
  letI : (kernel (restrictionToComplement X Z hZ)).Additive :=
    sectionsWithSupport_additive X Z hZ
  let ιZ : sectionsWithSupport X Z hZ ⟶
      SheafOfModules.evaluation (structureSheafRing X) (op ⊤) :=
    kernel.ι (restrictionToComplement X Z hZ)
  let τZX : FZ ⟶ FX := Functor.whiskerRight
    (ιZ.mapHomotopyCategory (ComplexShape.up ℤ)) DerivedCategory.Qh
  let τXU : FX ⟶ FU := Functor.whiskerRight
    ((restrictionToComplement X Z hZ).mapHomotopyCategory
      (ComplexShape.up ℤ)) DerivedCategory.Qh
  let cI : kInjectiveRightDerivedCandidate X FZ ⟶
      kInjectiveRightDerivedCandidate X FX :=
    Functor.whiskerLeft ((kInjectiveEquivalence X).inverse ⋙
      (kInjectiveObjects X).ι) τZX
  let cR : kInjectiveRightDerivedCandidate X FX ⟶
      kInjectiveRightDerivedCandidate X FU :=
    Functor.whiskerLeft ((kInjectiveEquivalence X).inverse ⋙
      (kInjectiveObjects X).ι) τXU
  let cB : kInjectiveRightDerivedCandidate X FU ⟶
      kInjectiveRightDerivedCandidate X FZ ⋙
        shiftFunctor (DerivedGlobalModules X) (1 : ℤ) :=
    Functor.whiskerLeft (kInjectiveEquivalence X).inverse
      (sectionsWithSupportBoundaryOnKInjectives X Z hZ)
  let boundary : RΓU ⟶ RΓZ ⋙ shiftFunctor (DerivedGlobalModules X) (1 : ℤ) :=
    eU.hom ≫ cB ≫
      (Functor.isoWhiskerRight eZ.symm (shiftFunctor (DerivedGlobalModules X) (1 : ℤ))).hom
  refine ⟨boundary, ?_⟩
  intro K
  have hiNat :
      derivedSupportInclusion X Z hZ RΓZ RΓ aZ aX ≫ eX.hom = eZ.hom ≫ cI :=
    rightDerivedToKInjectiveCandidateIso_naturality X FZ FX RΓZ RΓ aZ aX τZX _
      (derivedSupportInclusion_fac X Z hZ RΓZ RΓ aZ aX)
  have hrNat :
      derivedRestrictionToComplement X Z hZ RΓ RΓU aX aU ≫ eU.hom = eX.hom ≫ cR :=
    rightDerivedToKInjectiveCandidateIso_naturality X FX FU RΓ RΓU aX aU τXU _
      (derivedRestrictionToComplement_fac X Z hZ RΓ RΓU aX aU)
  let TC : Triangle (DerivedGlobalModules X) := Triangle.mk
    (cI.app K) (cR.app K) (cB.app K)
  have hTC : TC ∈ distTriang (DerivedGlobalModules X) := by
    have h := sectionsWithSupportTriangleOnKInjectives_distinguished X Z hZ
      ((kInjectiveEquivalence X).inverse.obj K)
    simpa [TC, cI, cR, cB, ιZ, kInjectiveObjects, FZ, FX, FU, τZX, τXU] using h
  refine isomorphic_distinguished TC hTC _ ?_
  refine Triangle.isoMk _ TC (eZ.app K) (eX.app K) (eU.app K) ?_ ?_ ?_
  · exact congrArg (fun η => η.app K) hiNat
  · exact congrArg (fun η => η.app K) hrNat
  · exact comp_shift_map_inv_hom (shiftFunctor (DerivedGlobalModules X) (1 : ℤ))
      (eU.hom.app K) (eZ.app K) (cB.app K)

/-- The triangle data for the two canonical transformations `derivedSupportInclusion` and
`derivedRestrictionToComplement` exists. -/
public theorem nonempty_sectionsWithSupportTriangleData
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    (RΓZ RΓ RΓU : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
    (aZ : homotopyToDerived X (sectionsWithSupport X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓZ)
    (aX : homotopyToDerived X
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) ⟶
        DerivedCategory.Qh ⋙ RΓ)
    (aU : homotopyToDerived X (sectionsOnComplement X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓU)
    [RΓZ.IsRightDerivedFunctor aZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓ.IsRightDerivedFunctor aX
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :
    Nonempty (SectionsWithSupportTriangleData X RΓZ RΓ RΓU
      (derivedSupportInclusion X Z hZ RΓZ RΓ aZ aX)
      (derivedRestrictionToComplement X Z hZ RΓ RΓU aX aU)) :=
  ⟨sectionsWithSupportTriangleData X Z hZ RΓZ RΓ RΓU aZ aX aU⟩

/-- Derived sections with support, global derived sections, and derived
sections on the open complement form a distinguished triangle, naturally in the object of
the unbounded derived category. -/
@[stacks 0G71]
public noncomputable def derivedSectionsWithSupportTriangle
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    (RΓZ RΓ RΓU : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
    (aZ : homotopyToDerived X (sectionsWithSupport X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓZ)
    (aX : homotopyToDerived X
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) ⟶
        DerivedCategory.Qh ⋙ RΓ)
    (aU : homotopyToDerived X (sectionsOnComplement X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓU)
    [RΓZ.IsRightDerivedFunctor aZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓ.IsRightDerivedFunctor aX
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :
    SectionsWithSupportTriangleData X RΓZ RΓ RΓU
      (derivedSupportInclusion X Z hZ RΓZ RΓ aZ aX)
      (derivedRestrictionToComplement X Z hZ RΓ RΓU aX aU) :=
  Classical.choice
    (nonempty_sectionsWithSupportTriangleData X Z hZ RΓZ RΓ RΓU aZ aX aU)

/-- The functorial connecting morphism in the triangle `derivedSectionsWithSupportTriangle`. -/
public noncomputable abbrev derivedSectionsWithSupportBoundary
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    (RΓZ RΓ RΓU : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
    (aZ : homotopyToDerived X (sectionsWithSupport X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓZ)
    (aX : homotopyToDerived X
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) ⟶
        DerivedCategory.Qh ⋙ RΓ)
    (aU : homotopyToDerived X (sectionsOnComplement X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓU)
    [RΓZ.IsRightDerivedFunctor aZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓ.IsRightDerivedFunctor aX
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :=
  (derivedSectionsWithSupportTriangle X Z hZ RΓZ RΓ RΓU aZ aX aU).boundary

/-- The triangle `derivedSectionsWithSupportTriangle` evaluated at a derived sheaf. -/
public noncomputable def derivedSectionsWithSupportTriangleAt
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    (RΓZ RΓ RΓU : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
    (aZ : homotopyToDerived X (sectionsWithSupport X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓZ)
    (aX : homotopyToDerived X
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) ⟶
        DerivedCategory.Qh ⋙ RΓ)
    (aU : homotopyToDerived X (sectionsOnComplement X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓU)
    [RΓZ.IsRightDerivedFunctor aZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓ.IsRightDerivedFunctor aX
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    (K : DerivedModuleSheaves X) : Triangle (DerivedGlobalModules X) :=
  Triangle.mk
    ((derivedSupportInclusion X Z hZ RΓZ RΓ aZ aX).app K)
    ((derivedRestrictionToComplement X Z hZ RΓ RΓU aX aU).app K)
    ((derivedSectionsWithSupportBoundary X Z hZ RΓZ RΓ RΓU aZ aX aU).app K)

/-- The objectwise triangle `derivedSectionsWithSupportTriangleAt` is distinguished. -/
public lemma derivedSectionsWithSupportTriangleAt_distinguished
    (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)
    (RΓZ RΓ RΓU : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
    (aZ : homotopyToDerived X (sectionsWithSupport X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓZ)
    (aX : homotopyToDerived X
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) ⟶
        DerivedCategory.Qh ⋙ RΓ)
    (aU : homotopyToDerived X (sectionsOnComplement X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓU)
    [RΓZ.IsRightDerivedFunctor aZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓ.IsRightDerivedFunctor aX
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    (K : DerivedModuleSheaves X) :
    derivedSectionsWithSupportTriangleAt X Z hZ RΓZ RΓ RΓU aZ aX aU K ∈
      distTriang (DerivedGlobalModules X) :=
  (derivedSectionsWithSupportTriangle X Z hZ RΓZ RΓ RΓU aZ aX aU).distinguished K

end Stacks.Cohomology.SectionsWithSupport
