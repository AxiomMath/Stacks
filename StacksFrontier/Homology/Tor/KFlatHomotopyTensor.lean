module

public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.CategoryTheory.Triangulated.Localization
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import StacksFrontier.Homology.KFlat.Basic
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TensorComplex.Monoidal

/-!
# The K-flat localization of the homotopy category, and the homotopy tensor product

For a commutative ring `R`, the K-flat complexes form a triangulated subcategory of the homotopy
category `K(R)` on which the tensor product is already homotopy-invariant, and inverting the
quasi-isomorphisms between K-flat complexes computes the derived category. This module collects
that substrate: the object property `KFlatObjects`, the localizer `kFlatLocalizer` together with
its left resolutions and the fact that it is a localized equivalence, and the tensor product
`homotopyTensor` on the K-flat part of the homotopy category with the lifting and braiding data
it carries.

Nothing here mentions a chosen model of the derived category: these are statements about the
homotopy category and about localizers, and they are the common input of every construction of a
derived tensor product, whichever model of `D(R)` that construction goes on to use.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory Functor

universe u v w

namespace CochainComplex.KFlatHomotopyTensor

/-- Cochain complexes of `R`-modules indexed by `ℤ`. -/
public abbrev C (R : Type u) [CommRing R] := CochainComplex (ModuleCat.{u} R) ℤ

/-- The homotopy category `K(R)` of cochain complexes of `R`-modules indexed by `ℤ`. -/
public abbrev KC (R : Type u) [CommRing R] :=
  HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)

/-- The K-flat objects of `K(R)`: those whose underlying complex is K-flat. -/
public abbrev KFlatObjects (R : Type u) [CommRing R] : ObjectProperty (KC R) :=
  fun K => CochainComplex.KFlat K.as

/-- The tensor unit of cochain complexes of `R`-modules is K-flat. -/
public lemma kFlat_unit {R : Type u} [CommRing R] :
    CochainComplex.KFlat (𝟙_ (C R)) := by
  intro M hM
  exact HomologicalComplex.Acyclic.of_iso (ρ_ M).symm hM

/-- The objects `K` of `K(R)` with `Tot(M ⊗ K)` acyclic: the inverse image of the acyclic
objects under `Tleft M`. -/
public abbrev AcyclicTensorPreimage {R : Type u} [CommRing R] (M : C R) :
    ObjectProperty (KC R) :=
  (HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} R)).inverseImage (Tleft M)

/-- An object of `K(R)` is K-flat if and only if it lies in `AcyclicTensorPreimage M` for every
acyclic complex `M`. -/
public lemma kFlat_iff_acyclicTensorPreimage {R : Type u} [CommRing R] (K : KC R) :
    KFlatObjects R K ↔
      ∀ M : C R, M.Acyclic → AcyclicTensorPreimage M K := by
  refine ⟨fun hK M hM => ?_, fun hK M hM =>
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 (hK M hM)⟩
  change HomotopyCategory.subcategoryAcyclic _ ((HomotopyCategory.quotient _ _).obj (M ⊗ K.as))
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hK M hM)

/-- The K-flat objects form a triangulated subcategory of `K(R)`. -/
public lemma kFlatObjects_isTriangulated {R : Type u} [CommRing R] :
    (KFlatObjects R).IsTriangulated := by
  have hT (M : C R) : (AcyclicTensorPreimage M).IsTriangulated := by
    obtain ⟨e, he⟩ := TotalTensorComplex.tleft_isTriangulated M
    let := e
    let := he
    infer_instance
  refine { exists_zero := ?_, isStableUnderShiftBy := ?_, ext₂' := ?_ }
  · have hZ : IsZero ((HomotopyCategory.quotient _ _).obj
        (HomologicalComplex.zero : C R)) :=
      (HomotopyCategory.quotient _ _).map_isZero HomologicalComplex.isZero_zero
    refine ⟨_, hZ, ?_⟩
    rw [kFlat_iff_acyclicTensorPreimage]
    intro M hM
    exact (AcyclicTensorPreimage M).prop_of_isZero hZ
  · intro n
    refine ⟨fun K hK => ?_⟩
    change KFlatObjects R (K⟦n⟧)
    rw [kFlat_iff_acyclicTensorPreimage] at hK ⊢
    intro M hM
    exact (AcyclicTensorPreimage M).le_shift n K (hK M hM)
  · intro T hTr h₁ h₃
    apply (KFlatObjects R).le_isoClosure
    rw [kFlat_iff_acyclicTensorPreimage] at h₁ h₃ ⊢
    intro M hM
    exact (AcyclicTensorPreimage M).ext_of_isTriangulatedClosed₂ T hTr
      (h₁ M hM) (h₃ M hM)

/-- The quasi-isomorphisms between K-flat objects of `K(R)`. -/
public abbrev KFlatQuasiIso (R : Type u) [CommRing R] :
    MorphismProperty (KFlatObjects R).FullSubcategory :=
  (HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).inverseImage
    (KFlatObjects R).ι

/-- The inclusion of the K-flat part of `K(R)`, as a localizer morphism from the
quasi-isomorphisms between K-flat objects to the quasi-isomorphisms of `K(R)`. -/
public def kFlatLocalizer (R : Type u) [CommRing R] :
    CategoryTheory.LocalizerMorphism (KFlatQuasiIso R)
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) where
  functor := (KFlatObjects R).ι
  map _ _ _ hf := hf

/-- Every object of `K(R)` has a left resolution by a K-flat object for `kFlatLocalizer`. -/
public lemma kFlatLocalizer_hasLeftResolutions {R : Type u} [CommRing R] :
    (kFlatLocalizer R).HasLeftResolutions := by
  intro X
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution K
  let X₁ : (KFlatObjects R).FullSubcategory :=
    ⟨(HomotopyCategory.quotient _ _).obj P, hP⟩
  let q : (kFlatLocalizer R).LeftResolution
      ((HomotopyCategory.quotient _ _).obj K) :=
    { X₁ := X₁
      w := (HomotopyCategory.quotient _ _).map f
      hw := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf }
  exact ⟨q⟩

/-- `kFlatLocalizer` is a localized equivalence: inverting the quasi-isomorphisms between K-flat
complexes computes the derived category. -/
public lemma kFlatLocalizer_isLocalizedEquivalence {R : Type u} [CommRing R] :
    (kFlatLocalizer R).IsLocalizedEquivalence := by
  let P := KFlatObjects R
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let : P.IsTriangulated := kFlatObjects_isTriangulated
  let H := HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0
  have hW : W.IsSaturated ∧ W.IsCompatibleWithTriangulation := by
    have hS : ∀ ⦃X Y : KC R⦄ (f : X ⟶ Y),
        W f ↔ ∀ i : ℤ, IsIso (H.map (f⟦i⟧')) := by
      intro X Y f
      let : H.ShiftSequence ℤ := CategoryTheory.Functor.ShiftSequence.tautological H ℤ
      dsimp [W]
      rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
      exact H.mem_homologicalKernel_trW_iff f
    exact CategoryTheory.Functor.isSaturated_and_isCompatibleWithTriangulation H W hS
  let : W.IsCompatibleWithTriangulation := hW.2
  have h :=
    P.isSaturated_and_isCompatibleWithTriangulation_inverseImage_ι_and_isLocalizedEquivalence W
      hW.1
  have hres : ({ functor := P.ι, map := le_rfl } :
      CategoryTheory.LocalizerMorphism (W.inverseImage P.ι) W).HasLeftResolutions :=
    kFlatLocalizer_hasLeftResolutions
  exact h.2.2 hres

/-- The tensor product of two homotopy equivalences of complexes is a homotopy equivalence. -/
public noncomputable def tensorHomotopyEquiv {R : Type u} [CommRing R]
    {K₁ K₂ L₁ L₂ : C R} (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    HomotopyEquiv (K₁ ⊗ K₂) (L₁ ⊗ L₂) where
  hom := e₁.hom ⊗ₘ e₂.hom
  inv := e₁.inv ⊗ₘ e₂.inv
  homotopyHomInvId := by
    rw [tensorHom_comp_tensorHom]
    exact (((HomologicalComplex.mapBifunctorMapHomotopy₁ e₁.homotopyHomInvId
        (e₂.hom ≫ e₂.inv) (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K₁) e₂.homotopyHomInvId
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ))).trans
      (Homotopy.ofEq (id_tensorHom_id K₁ K₂)))
  homotopyInvHomId := by
    rw [tensorHom_comp_tensorHom]
    exact (((HomologicalComplex.mapBifunctorMapHomotopy₁ e₁.homotopyInvHomId
        (e₂.inv ≫ e₂.hom) (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 L₁) e₂.homotopyInvHomId
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ))).trans
      (Homotopy.ofEq (id_tensorHom_id L₁ L₂)))

/-- The homotopy equivalences of cochain complexes of `R`-modules. -/
public abbrev homotopyEquivalences (R : Type u) [CommRing R] :
    MorphismProperty (C R) :=
  HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.up ℤ)

/-- The tensor product of complexes, followed by the quotient to `K(R)`, inverts homotopy
equivalences in each variable. -/
public lemma tensor_inverts_homotopyEquivalences₂ {R : Type u} [CommRing R] :
    MorphismProperty.IsInvertedBy₂ (homotopyEquivalences R) (homotopyEquivalences R)
      (curriedTensor (C R) ⋙
        (Functor.whiskeringRight _ _ _).obj
          (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))) := by
  rintro ⟨K₁, K₂⟩ ⟨L₁, L₂⟩ ⟨f, g⟩ ⟨hf, hg⟩
  obtain ⟨e₁, rfl⟩ := hf
  obtain ⟨e₂, rfl⟩ := hg
  have h : IsIso ((HomotopyCategory.quotient _ _).map (e₁.hom ⊗ₘ e₂.hom)) :=
    CategoryTheory.Localization.inverts (HomotopyCategory.quotient _ _)
    (homotopyEquivalences R) _ ⟨tensorHomotopyEquiv e₁ e₂, rfl⟩
  simpa [Functor.uncurry_obj_map, MonoidalCategory.tensorHom_def] using h

/-- The tensor product on the homotopy category `K(R)`, descended from the tensor product of
complexes along the quotient in each variable. -/
public noncomputable def homotopyTensor (R : Type u) [CommRing R] :
    KC R ⥤ KC R ⥤ KC R :=
  CategoryTheory.Localization.lift₂
    (curriedTensor (C R) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    tensor_inverts_homotopyEquivalences₂
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))

/-- The homotopy tensor product of the images of two complexes is the image of their tensor
product. -/
public noncomputable def homotopyTensorComparison {R : Type u} [CommRing R]
    (K L : C R) :
    ((homotopyTensor R).obj ((HomotopyCategory.quotient _ _).obj K)).obj
        ((HomotopyCategory.quotient _ _).obj L) ≅
      (HomotopyCategory.quotient _ _).obj (K ⊗ L) := by
  letI : CategoryTheory.Localization.Lifting₂
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (homotopyEquivalences R) (homotopyEquivalences R)
      (curriedTensor (C R) ⋙
        (Functor.whiskeringRight _ _ _).obj
          (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)))
      (homotopyTensor R) := by
    unfold homotopyTensor
    infer_instance
  exact ((CategoryTheory.Localization.Lifting₂.iso
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (homotopyEquivalences R) (homotopyEquivalences R)
      (curriedTensor (C R) ⋙
        (Functor.whiskeringRight _ _ _).obj
          (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)))
      (homotopyTensor R)).app K).app L

/-- `homotopyTensor` is the lift in two variables of the tensor product of complexes. -/
@[instance_reducible]
public noncomputable def homotopyTensorLifting (R : Type u) [CommRing R] :
    Localization.Lifting₂
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (homotopyEquivalences R) (homotopyEquivalences R)
      (curriedTensor (C R) ⋙ (Functor.whiskeringRight _ _ _).obj
        (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)))
      (homotopyTensor R) := by
  unfold homotopyTensor
  infer_instance

attribute [local instance] homotopyTensorLifting

/-- The braiding of `homotopyTensor`, descended from the braiding of the tensor product of
complexes. -/
public noncomputable def homotopyTensorBraiding (R : Type u) [CommRing R]
    [SymmetricCategory (C R)] : homotopyTensor R ≅ (homotopyTensor R).flip := by
  let Q := HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let F := curriedTensor (C R) ⋙ (Functor.whiskeringRight _ _ _).obj Q
  letI : Localization.Lifting₂ Q Q (homotopyEquivalences R) (homotopyEquivalences R)
      ((curriedTensor (C R)).flip ⋙ (Functor.whiskeringRight _ _ _).obj Q)
      (homotopyTensor R).flip :=
    Localization.Lifting₂.flip Q Q (homotopyEquivalences R) (homotopyEquivalences R)
      F (homotopyTensor R)
  exact Localization.lift₂NatIso Q Q (homotopyEquivalences R) (homotopyEquivalences R)
    _ _ _ _ (isoWhiskerRight (BraidedCategory.curriedBraidingNatIso (C R))
      ((Functor.whiskeringRight _ _ _).obj Q))

/-- Tensoring on the right with the image of `K` in `K(R)` is the functor `Tright K`. -/
public noncomputable def homotopyTensorRightIso {R : Type u} [CommRing R] (K : C R) :
    (homotopyTensor R).flip.obj ((HomotopyCategory.quotient _ _).obj K) ≅ Tright K := by
  let Q := HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let F := (curriedTensor (C R)).flip.obj K ⋙ Q
  letI : Localization.Lifting Q (homotopyEquivalences R) F (Tright K) :=
    ⟨NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)⟩
  letI : Localization.Lifting Q (homotopyEquivalences R) F
      ((homotopyTensor R).flip.obj (Q.obj K)) :=
    Localization.Lifting₂.snd Q Q (homotopyEquivalences R) (homotopyEquivalences R)
      (curriedTensor (C R) ⋙ (Functor.whiskeringRight _ _ _).obj Q) (homotopyTensor R) K
  exact Localization.liftNatIso Q (homotopyEquivalences R) F F _ _ (Iso.refl _)

attribute [local instance] HasDerivedCategory.standard

/-- A morphism of `K(R)` is a quasi-isomorphism if and only if its image in the derived category
is an isomorphism. -/
private lemma homotopy_quasiIso_iff_isIso_Qh {R : Type u} [CommRing R]
    {X Y : KC R} (f : X ⟶ Y) :
    HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ) f ↔
      IsIso ((DerivedCategory.Qh (C := ModuleCat.{u} R)).map f) :=
  (DerivedCategory.isIso_Qh_map_iff f).symm

/-- Tensoring on the right with a K-flat object of `K(R)` preserves quasi-isomorphisms. -/
public lemma homotopyTensor_right_preserves_quasiIso {R : Type u} [CommRing R]
    (K : KC R) (hK : KFlatObjects R K) {X Y : KC R} (f : X ⟶ Y)
    (hf : HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ) f) :
    HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (((homotopyTensor R).flip.obj K).map f) := by
  rw [homotopy_quasiIso_iff_isIso_Qh]
  exact (NatIso.isIso_map_iff
    (isoWhiskerRight (homotopyTensorRightIso K.as) (DerivedCategory.Qh (C := ModuleCat.{u} R))) f).2
    ((homotopy_quasiIso_iff_isIso_Qh _).1
      (CochainComplex.KFlat.kFlat_tright_preserves_quasiIso K.as hK _ hf))

/-- On images of complexes, `homotopyTensorBraiding` is the braiding of complexes conjugated by
`homotopyTensorComparison`. -/
public lemma homotopyTensorBraiding_app {R : Type u} [CommRing R]
    [SymmetricCategory (C R)] (K L : C R) :
    ((homotopyTensorBraiding R).hom.app ((HomotopyCategory.quotient _ _).obj K)).app
        ((HomotopyCategory.quotient _ _).obj L) =
      (homotopyTensorComparison K L).hom ≫
        (HomotopyCategory.quotient _ _).map (β_ K L).hom ≫
        (homotopyTensorComparison L K).inv := by
  simp [homotopyTensorBraiding, Localization.lift₂NatIso,
    Localization.lift₂NatTrans_app_app, homotopyTensorComparison, Localization.Lifting₂.flip]

end CochainComplex.KFlatHomotopyTensor

end
