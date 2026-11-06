module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Localization.OfQuotient
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Minus
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section

/-!
# Computing Tor: the derived tensor product on the bounded-above derived category

For a commutative ring `R` and an `R`-module `M`, tensoring with `M` admits a total left derived
functor on the bounded-above derived category of `R`-modules. This is the construction underlying
the Stacks Project section "Computing Tor": the derived tensor product `- ⊗ᴸ_R M` is computed by
replacing a bounded-above complex with a bounded-above complex of projectives.

## Main definitions

* `CochainComplex.ComputingTor.BoundedAboveComplex` is the category of bounded-above cochain
  complexes of `R`-modules.
* `CochainComplex.ComputingTor.boundedAboveQuotient` sends such a complex to the bounded-above
  derived category.
* `CochainComplex.ComputingTor.tensorComplex` is termwise tensor product with `M` on bounded-above
  complexes.
* `CochainComplex.ComputingTor.TotalDerivedTensor` packages a functor together with the comparison
  and universal property which characterize it as derived tensor product with `M`.

## Main results

* `CochainComplex.ComputingTor.derivedTensorProduct`: for every `R`-module `M` the total left
  derived tensor product `- ⊗ᴸ_R M : D⁻(R) ⟶ D⁻(R)` exists. Its functor field is the total left
  derived functor of termwise tensor product with `M` on bounded-above complexes.

## Implementation notes

The bounded-above derived category is Mathlib's `DerivedCategory.Minus`. The comparison natural
transformation and its right-Kan-extension property record the canonical and functorial character
of the derived tensor product, rather than merely choosing an endofunctor of this category.

The construction factors the localization `K⁻(R) ⥤ D⁻(R)` as the homotopy quotient
`boundedHomotopyQuotient` followed by `boundedHomotopyToDerived`. The first is a localization at
the homotopy equivalences (via a cylinder argument), the second at the quasi-isomorphisms (via
[Stacks, Tag 05RW]); composing them identifies `boundedAboveQuotient` as the localization at
quasi-isomorphisms. Existence of bounded-above projective resolutions
([Stacks, Tag 0646] (3)) makes `boundedHomotopyToDerived` a right adjoint, and the total left
derived functor is then obtained as a right Kan extension along its left adjoint, transported
across the localization.

## References

* [The Stacks Project, Tag 064G](https://stacks.math.columbia.edu/tag/064G)
-/

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace CochainComplex.ComputingTor

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [CommRing R]

/-- The category of bounded-above cochain complexes of `R`-modules. -/
@[ega "0 11.2.1" "special case"]
public abbrev BoundedAboveComplex :=
  (CochainComplex.minus (ModuleCat.{u} R)).FullSubcategory

/-- The localization functor from bounded-above complexes to the bounded-above derived category. -/
public def boundedAboveQuotient :
    BoundedAboveComplex (R := R) ⥤ DerivedCategory.Minus (ModuleCat.{u} R) :=
  DerivedCategory.TStructure.t.minus.lift
    ((CochainComplex.minus (ModuleCat.{u} R)).ι ⋙ DerivedCategory.Q)
    (fun X ↦ by
      obtain ⟨n, hn⟩ := X.property
      refine ⟨n, ?_⟩
      change (DerivedCategory.Q.obj X.1).IsLE n
      let : X.1.IsStrictlyLE n := hn
      infer_instance)

/-- Termwise tensor product with `M` preserves bounded-above cochain complexes. -/
public def tensorComplex (M : ModuleCat.{u} R) :
    BoundedAboveComplex (R := R) ⥤ BoundedAboveComplex (R := R) :=
  ObjectProperty.lift (CochainComplex.minus (ModuleCat.{u} R))
    ((CochainComplex.minus (ModuleCat.{u} R)).ι ⋙
      (tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun X ↦ by
      obtain ⟨n, hn⟩ := X.property
      refine ⟨n, ?_⟩
      rw [CochainComplex.isStrictlyLE_iff] at hn ⊢
      intro i hi
      exact (tensorRight M).map_isZero (hn i hi))

/-- A total derived tensor product with `M` on the bounded-above derived category.

The comparison is natural in the bounded-above complex, and its left-derived universal property
characterizes `functor` up to canonical isomorphism. -/
public structure TotalDerivedTensor (M : ModuleCat.{u} R) where
  /-- The functor `- ⊗ᴸ_R M : D⁻(R) ⟶ D⁻(R)`. -/
  functor : DerivedCategory.Minus (ModuleCat.{u} R) ⥤
    DerivedCategory.Minus (ModuleCat.{u} R)
  /-- The derived tensor product is additive. -/
  additive : functor.Additive
  /-- The comparison from derived tensor product to termwise tensor product. -/
  comparison : boundedAboveQuotient ⋙ functor ⟶
    tensorComplex M ⋙ boundedAboveQuotient
  /-- The bounded-above quotient realizes the localization at quasi-isomorphisms. -/
  isLocalization : boundedAboveQuotient.IsLocalization
    ((HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).inverseImage
      (CochainComplex.minus (ModuleCat.{u} R)).ι)
  /-- The comparison exhibits `functor` as the total left derived functor of tensoring with `M`. -/
  isLeftDerived : letI := isLocalization
    functor.IsLeftDerivedFunctor comparison
      ((HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).inverseImage
        (CochainComplex.minus (ModuleCat.{u} R)).ι)

attribute [instance] TotalDerivedTensor.additive

end

private theorem tensorComplex_additive {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) : (tensorComplex M).Additive := by
  dsimp [tensorComplex]
  infer_instance

private theorem acyclic_map_of_projective_bounded
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ)
    (n : ℤ) [K.IsStrictlyLE n] [∀ i, Projective (K.X i)] (hK : K.Acyclic) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  have : K.IsKProjective := CochainComplex.isKProjective_of_projective K n
  have hzero : Limits.IsZero ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) :=
    (HomotopyCategory.isZero_quotient_obj_iff K).2
      (CochainComplex.IsKProjective.nonempty_homotopy_zero (𝟙 K) hK)
  have hzero' := (F.mapHomotopyCategory (ComplexShape.up ℤ)).map_isZero hzero
  apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
  rw [HomotopyCategory.mem_subcategoryAcyclic_iff]
  intro i
  exact (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) i).map_isZero hzero'

private theorem acyclic_tensor_of_projective_bounded
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    [K.IsStrictlyLE n] [∀ i, Projective (K.X i)] (hK : K.Acyclic) :
    (((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic :=
  acyclic_map_of_projective_bounded (tensorRight M) K n hK

/-- An additive functor carries a quasi-isomorphism between bounded-above complexes of
projectives to a quasi-isomorphism. -/
private theorem quasiIso_map_of_projective_bounded
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    (F : A ⥤ B) [F.Additive] (K L : CochainComplex A ℤ)
    (nK nL : ℤ) [K.IsStrictlyLE nK] [L.IsStrictlyLE nL]
    [∀ i, Projective (K.X i)] [∀ i, Projective (L.X i)]
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have : K.IsKProjective := CochainComplex.isKProjective_of_projective K nK
  have : L.IsKProjective := CochainComplex.isKProjective_of_projective L nL
  have hf : HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ) f :=
    (CochainComplex.IsKProjective.quasiIso_iff f).1 inferInstance
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms] at hf
  have : IsIso ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) := hf
  apply homotopyEquivalences_le_quasiIso _ _ _
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms]
  exact (F.mapHomotopyCategory (ComplexShape.up ℤ)).map_isIso
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)

private lemma minus_cylinder {A : Type*} [Category A] [Preadditive A]
    [Limits.HasBinaryBiproducts A] (K : CochainComplex A ℤ)
    (hK : CochainComplex.minus A K) :
    CochainComplex.minus A (HomologicalComplex.cylinder K) := by
  obtain ⟨n, hn⟩ := hK
  refine ⟨n + 1, ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  dsimp [HomologicalComplex.cylinder]
  refine HomologicalComplex.homotopyCofiber.isZero_X _ _ ?_ (fun j hj ↦ ?_)
  · refine Limits.IsZero.of_iso ?_
      ((HomologicalComplex.eval A (ComplexShape.up ℤ) i).mapBiprod _ _)
    exact (Limits.biprod_isZero_iff _ _).2
      ⟨K.isZero_of_isStrictlyLE n i (by omega),
        K.isZero_of_isStrictlyLE n i (by omega)⟩
  · simp only [ComplexShape.up_Rel] at hj
    exact K.isZero_of_isStrictlyLE n j (by omega)

private abbrev boundedHomotopyProperty (A : Type*) [Category A] [Preadditive A] :
    ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)) :=
  (CochainComplex.minus A).strictMap (HomotopyCategory.quotient A (ComplexShape.up ℤ))

private def boundedHomotopyQuotient (A : Type*) [Category A] [Preadditive A] :
    (CochainComplex.minus A).FullSubcategory ⥤
      (boundedHomotopyProperty A).FullSubcategory :=
  ObjectProperty.lift (boundedHomotopyProperty A)
    ((CochainComplex.minus A).ι ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (fun X ↦ ⟨X.obj, X.property⟩)

private lemma boundedHomotopyProperty_quotient_obj_iff
    {A : Type*} [Category A] [Preadditive A] (K : CochainComplex A ℤ) :
    boundedHomotopyProperty A ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ↔
      CochainComplex.minus A K := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨K, h⟩⟩
  obtain ⟨L, hL, hEq⟩ := (ObjectProperty.strictMap_iff _ _ _).1 h
  obtain rfl : L = K := congrArg Quotient.as hEq
  exact hL

private theorem boundedHomotopyQuotient_full {A : Type*} [Category A] [Preadditive A] :
    (boundedHomotopyQuotient A).Full := by
  dsimp [boundedHomotopyQuotient]
  infer_instance

private theorem boundedHomotopyQuotient_essSurj {A : Type*} [Category A] [Preadditive A] :
    (boundedHomotopyQuotient A).EssSurj where
  mem_essImage X := by
    obtain ⟨K, hK⟩ := HomotopyCategory.quotient_obj_surjective X.obj
    have hKm : CochainComplex.minus A K :=
      (boundedHomotopyProperty_quotient_obj_iff K).1 (hK ▸ X.property)
    exact ⟨⟨K, hKm⟩, ⟨(boundedHomotopyProperty A).ι.preimageIso (eqToIso hK)⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
open HomologicalComplex in
set_option backward.defeqAttrib.useBackward true in
private theorem boundedHomotopyQuotient_isLocalization
    {A : Type*} [Category A] [Preadditive A] [Limits.HasZeroObject A]
    [Limits.HasBinaryBiproducts A] :
    (boundedHomotopyQuotient A).IsLocalization
      ((HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ)).inverseImage
        (CochainComplex.minus A).ι) := by
  have := boundedHomotopyQuotient_full (A := A)
  have := boundedHomotopyQuotient_essSurj (A := A)
  refine Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _
    (fun _ _ f hf ↦ by
      simpa [← isIso_iff_of_reflects_iso _ (boundedHomotopyProperty A).ι,
        ← HomotopyCategory.inverseImage_quotient_isomorphisms] using! hf) (by
      rintro K L f₀ f₁ hf
      obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjective f₀
      obtain ⟨f₁, rfl⟩ := ObjectProperty.homMk_surjective f₁
      replace hf := HomotopyCategory.homotopyOfEq f₀ f₁
        ((boundedHomotopyProperty A).ι.congr_map hf)
      exact ⟨K.obj.precylinder.toFullSubcategory (minus_cylinder K.obj K.property),
        HomotopicalAlgebra.Precylinder.LeftHomotopy.fullSubcategoryEquiv.symm
          { h := HomologicalComplex.cylinder.desc _ _ hf },
        ⟨HomologicalComplex.cylinder.homotopyEquiv _
          (fun n ↦ ⟨n - 1, by simp⟩), rfl⟩⟩)

private lemma boundedHomotopyProperty_Qh_minus
    {A : Type*} [Category A] [Abelian A] (X : HomotopyCategory A (ComplexShape.up ℤ))
    (hX : boundedHomotopyProperty A X) :
    DerivedCategory.TStructure.t.minus (DerivedCategory.Qh.obj X) := by
  obtain ⟨K : CochainComplex A ℤ, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨n, hn⟩ := (boundedHomotopyProperty_quotient_obj_iff K).1 hX
  have : K.IsStrictlyLE n := hn
  exact ⟨n, DerivedCategory.TStructure.t.isLE_of_iso
    ((DerivedCategory.quotientCompQhIso A).symm.app K) n⟩

private def boundedHomotopyToDerived (A : Type*) [Category A] [Abelian A] :
    (boundedHomotopyProperty A).FullSubcategory ⥤ DerivedCategory.Minus A :=
  DerivedCategory.TStructure.t.minus.lift
    ((boundedHomotopyProperty A).ι ⋙ DerivedCategory.Qh)
    (fun X ↦ boundedHomotopyProperty_Qh_minus X.obj X.property)

private lemma boundedHomotopyToDerived_isLocalization
    {A : Type*} [Category A] [Abelian A] :
    (boundedHomotopyToDerived A).IsLocalization
      ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage
        (boundedHomotopyProperty A).ι) := by
  obtain ⟨F, ⟨eF⟩, hF⟩ :=
    (HomotopyCategory.isSaturated_subcategoryAcyclic_inverseImage_and_quasiIso_and_isLocalization
      (A := A) (D := DerivedCategory.Minus A)).2.2.1
  have e : F ≅ boundedHomotopyToDerived A :=
    ((DerivedCategory.TStructure.t.minus).fullyFaithfulι.whiskeringRight _).preimageIso
      eF
  have := hF
  exact Functor.IsLocalization.of_iso _ e

private def boundedCompositeIso {A : Type*} [Category A] [Abelian A] :
    (boundedHomotopyQuotient A ⋙ boundedHomotopyToDerived A) ⋙
      DerivedCategory.Minus.ι ≅
    (CochainComplex.minus A).ι ⋙ DerivedCategory.Q := by
  calc
    _ ≅ ((CochainComplex.minus A).ι ⋙
        HomotopyCategory.quotient A (ComplexShape.up ℤ)) ⋙ DerivedCategory.Qh :=
      Iso.refl _
    _ ≅ (CochainComplex.minus A).ι ⋙ DerivedCategory.Q :=
      (Functor.associator _ _ _) ≪≫
        Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso A)

private def boundedCompositeToQuotientIso {R : Type u} [CommRing R] :
    boundedHomotopyQuotient (ModuleCat.{u} R) ⋙
      boundedHomotopyToDerived (ModuleCat.{u} R) ≅
      boundedAboveQuotient (R := R) :=
  ((DerivedCategory.TStructure.t.minus).fullyFaithfulι.whiskeringRight _).preimageIso
    (boundedCompositeIso ≪≫ (Iso.refl _))

private lemma boundedHomotopy_quasiIso_le_map {A : Type*} [Category A] [Abelian A] :
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage
      (boundedHomotopyProperty A).ι ≤
    ((HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).inverseImage
      (CochainComplex.minus A).ι).map (boundedHomotopyQuotient A) := by
  have := boundedHomotopyQuotient_full (A := A)
  have := boundedHomotopyQuotient_essSurj (A := A)
  intro X Y f hf
  let H := boundedHomotopyQuotient A
  let eX := H.objObjPreimageIso X
  let eY := H.objObjPreimageIso Y
  let g := H.preimage (eX.hom ≫ f ≫ eY.inv)
  have hg : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage
      (boundedHomotopyProperty A).ι (H.map g) := by
    show HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      ((boundedHomotopyProperty A).ι.map (H.map g))
    change HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      ((boundedHomotopyProperty A).ι.map f) at hf
    rw [show H.map g = eX.hom ≫ f ≫ eY.inv from H.map_preimage _]
    simpa only [Functor.map_comp, MorphismProperty.cancel_left_of_respectsIso,
      MorphismProperty.cancel_right_of_respectsIso] using hf
  have hg' : ((HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).inverseImage
      (CochainComplex.minus A).ι) g := by
    show HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
      ((CochainComplex.minus A).ι.map g)
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 hg
  exact ⟨_, _, g, hg', ⟨Arrow.isoMk' _ _ eX eY (by simp [g, H])⟩⟩

private theorem boundedAboveQuotient_isLocalization {R : Type u} [CommRing R] :
    (boundedAboveQuotient (R := R)).IsLocalization
      ((HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).inverseImage
        (CochainComplex.minus (ModuleCat.{u} R)).ι) := by
  let A := ModuleCat.{u} R
  let H := boundedHomotopyQuotient A
  let F := boundedHomotopyToDerived A
  let W₁ := (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ)).inverseImage
    (CochainComplex.minus A).ι
  let W₂ := (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage
    (boundedHomotopyProperty A).ι
  let W₃ := (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).inverseImage
    (CochainComplex.minus A).ι
  have : H.IsLocalization W₁ := boundedHomotopyQuotient_isLocalization
  have : F.IsLocalization W₂ := boundedHomotopyToDerived_isLocalization
  have hW₃ : W₃.IsInvertedBy (H ⋙ F) := by
    intro X Y f hf
    have hL : IsIso ((boundedAboveQuotient (R := R)).map f) := by
      have : IsIso (DerivedCategory.Minus.ι.map ((boundedAboveQuotient (R := R)).map f)) :=
        Localization.inverts DerivedCategory.Q
          (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) _ hf
      exact isIso_of_reflects_iso _ DerivedCategory.Minus.ι
    exact (NatIso.isIso_map_iff (boundedCompositeToQuotientIso (R := R)) f).2 hL
  have hW₁₃ : W₁ ≤ W₃ := fun _ _ _ hf ↦ homotopyEquivalences_le_quasiIso A _ _ hf
  have hW₂₃ : W₂ ≤ W₃.map H := boundedHomotopy_quasiIso_le_map
  have : (H ⋙ F).IsLocalization W₃ :=
    Functor.IsLocalization.comp H F W₁ W₂ W₃ hW₃ hW₁₃ hW₂₃
  exact Functor.IsLocalization.of_iso _ (boundedCompositeToQuotientIso (R := R))

private theorem boundedHomotopyToDerived_has_projective_representative
    {A : Type*} [Category A] [Abelian A] [EnoughProjectives A]
    (X : DerivedCategory.Minus A) :
    ∃ P : (boundedHomotopyProperty A).FullSubcategory,
      Nonempty ((boundedHomotopyToDerived A).obj P ≅ X) ∧
      ∀ Y : (boundedHomotopyProperty A).FullSubcategory,
        Function.Bijective ((boundedHomotopyToDerived A).map : (P ⟶ Y) → _) := by
  let L := boundedHomotopyToDerived A
  have := @Localization.essSurj _ _ _ _ L _ boundedHomotopyToDerived_isLocalization
  obtain ⟨Y, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := L) X
  obtain ⟨K, hK, hKY⟩ := (ObjectProperty.strictMap_iff _ _ _).1 Y.property
  obtain ⟨n, hn⟩ := hK
  obtain ⟨P, _⟩ := ProjectiveResolutionLemma.statement3 n K hn
  have := P.boundedAbove
  have := P.projective
  have := P.quasiIso
  have : P.complex.IsKProjective := CochainComplex.isKProjective_of_projective P.complex n
  let P' := (boundedHomotopyQuotient A).obj ⟨P.complex, n, P.boundedAbove⟩
  refine ⟨P', ⟨?_⟩, fun Z ↦ ?_⟩
  · exact (DerivedCategory.TStructure.t.minus).ι.preimageIso <|
      ((DerivedCategory.quotientCompQhIso A).app P.complex) ≪≫
      asIso (DerivedCategory.Q.map P.α) ≪≫
      ((DerivedCategory.quotientCompQhIso A).app K).symm ≪≫
      DerivedCategory.Qh.mapIso (eqToIso hKY) ≪≫
      (DerivedCategory.Minus.ι.mapIso e)
  · have hQ := CochainComplex.IsKProjective.Qh_map_bijective P.complex Z.obj
    refine ⟨fun f g h ↦ ?_, fun f ↦ ?_⟩
    · exact (boundedHomotopyProperty A).ι.map_injective
        (hQ.injective (DerivedCategory.Minus.ι.congr_map h))
    · obtain ⟨g, hg⟩ := hQ.surjective f.hom
      exact ⟨ObjectProperty.homMk g, DerivedCategory.Minus.ι.map_injective hg⟩

private theorem boundedHomotopyToDerived_isRightAdjoint
    {A : Type*} [Category A] [Abelian A] [EnoughProjectives A] :
    (boundedHomotopyToDerived A).IsRightAdjoint := by
  classical
  choose P e hP using boundedHomotopyToDerived_has_projective_representative (A := A)
  let e' (X) := (e X).some
  let E (X) (Y) : (P X ⟶ Y) ≃ (X ⟶ (boundedHomotopyToDerived A).obj Y) :=
    (Equiv.ofBijective _ (hP X Y)).trans ((e' X).homCongr (Iso.refl _))
  have hE : ∀ X Y Y' (g : Y ⟶ Y') (h : P X ⟶ Y),
      E X Y' (h ≫ g) = E X Y h ≫ (boundedHomotopyToDerived A).map g := by
    intros
    simp [E, Iso.homCongr, Functor.map_comp, Category.assoc]
  exact ⟨Adjunction.leftAdjointOfEquiv E hE, ⟨Adjunction.adjunctionOfEquivLeft E hE⟩⟩

private def boundedHomotopyTensor {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    (boundedHomotopyProperty (ModuleCat.{u} R)).FullSubcategory ⥤
      (boundedHomotopyProperty (ModuleCat.{u} R)).FullSubcategory :=
  ObjectProperty.lift _
    ((boundedHomotopyProperty (ModuleCat.{u} R)).ι ⋙
      (tensorRight M).mapHomotopyCategory (ComplexShape.up ℤ)) (fun X ↦ by
        obtain ⟨K, hK, hEq⟩ := (ObjectProperty.strictMap_iff _ _ _).1 X.property
        change boundedHomotopyProperty _
          (((tensorRight M).mapHomotopyCategory (ComplexShape.up ℤ)).obj X.obj)
        rw [← hEq]
        refine ⟨((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj K, ?_⟩
        obtain ⟨n, hn⟩ := hK
        refine ⟨n, ?_⟩
        rw [CochainComplex.isStrictlyLE_iff] at hn ⊢
        intro i hi
        exact (tensorRight M).map_isZero (hn i hi))

private def boundedHomotopyTensorIso {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    boundedHomotopyQuotient (ModuleCat.{u} R) ⋙
      (boundedHomotopyTensor M ⋙ boundedHomotopyToDerived (ModuleCat.{u} R)) ≅
    tensorComplex M ⋙ boundedAboveQuotient :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Iso.refl _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tensorComplex M) boundedCompositeToQuotientIso

private theorem isRightKanExtension_precomp_of_fullyFaithful
    {C B D E : Type*} [Category C] [Category B] [Category D] [Category E]
    (J : C ⥤ B) (hJ : ((Functor.whiskeringLeft C B E).obj J).FullyFaithful)
    {L : B ⥤ D} {F : B ⥤ E} {G : D ⥤ E} (α : L ⋙ G ⟶ F)
    [G.IsRightKanExtension α] :
    G.IsRightKanExtension ((Functor.associator J L G).hom ≫ Functor.whiskerLeft J α) := by
  classical
  let lift (s : Functor.RightExtension (J ⋙ L) (J ⋙ F)) : s.left ⟶ G :=
    G.liftOfIsRightKanExtension α s.left
      (hJ.preimage ((Functor.associator J L s.left).inv ≫ s.hom))
  have fac (s : Functor.RightExtension (J ⋙ L) (J ⋙ F)) :
      Functor.whiskerLeft (J ⋙ L) (lift s) ≫
        ((Functor.associator J L G).hom ≫ Functor.whiskerLeft J α) = s.hom := by
    have h := hJ.map_preimage ((Functor.associator J L s.left).inv ≫ s.hom)
    ext X
    have h' := congrArg (fun τ ↦ τ.app X) h
    simpa [lift] using (G.liftOfIsRightKanExtension_fac_app α s.left
      (hJ.preimage ((Functor.associator J L s.left).inv ≫ s.hom)) (J.obj X)).trans
        (by simpa using h')
  refine ⟨⟨Limits.IsTerminal.ofUniqueHom
    (fun s ↦ CostructuredArrow.homMk (lift s) (fac s)) ?_⟩⟩
  intro s m
  apply CostructuredArrow.ext
  apply G.hom_ext_of_isRightKanExtension α
  apply hJ.map_injective
  ext X
  calc
    _ = s.hom.app X := by simpa using congrArg (fun τ ↦ τ.app X) m.w
    _ = _ := by simpa using (congrArg (fun τ ↦ τ.app X) (fac s)).symm

private theorem nonempty_totalDerivedTensor {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) : Nonempty (TotalDerivedTensor M) := by
  classical
  let A := ModuleCat.{u} R
  let J := boundedHomotopyQuotient A
  let L := boundedHomotopyToDerived A
  let F := boundedHomotopyTensor M ⋙ L
  have : L.IsRightAdjoint := boundedHomotopyToDerived_isRightAdjoint
  let adj := Adjunction.ofIsRightAdjoint L
  have : L.Additive := by
    dsimp [L, boundedHomotopyToDerived]
    infer_instance
  have : L.leftAdjoint.Additive := adj.left_adjoint_additive
  have : (boundedHomotopyTensor M).Additive := by
    dsimp [boundedHomotopyTensor]
    infer_instance
  let G := L.leftAdjoint ⋙ F
  let α : L ⋙ G ⟶ F := (adj.whiskerLeft (DerivedCategory.Minus A)).counit.app F
  have : G.IsRightKanExtension α :=
    ⟨⟨mkTerminalOfRightAdjoint _ (adj.whiskerLeft (DerivedCategory.Minus A)) F⟩⟩
  let W := (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ)).inverseImage
    (CochainComplex.minus A).ι
  have : J.IsLocalization W := boundedHomotopyQuotient_isLocalization
  let β := (Functor.associator J L G).hom ≫ Functor.whiskerLeft J α
  have : G.IsRightKanExtension β := isRightKanExtension_precomp_of_fullyFaithful J
    (Localization.fullyFaithfulWhiskeringLeft J W _) α
  let E := (Functor.rightExtensionEquivalenceOfIso₁
      (boundedCompositeToQuotientIso (R := R)) (J ⋙ F)).trans
    (Functor.rightExtensionEquivalenceOfIso₂ boundedAboveQuotient
      (boundedHomotopyTensorIso M))
  let b := E.functor.obj (Functor.RightExtension.mk G β)
  have hb : b.IsUniversal :=
    (Limits.IsTerminal.isTerminalIffObj E.functor _).1
      (G.isUniversalOfIsRightKanExtension β)
  have := boundedAboveQuotient_isLocalization (R := R)
  exact
    ⟨{ functor := b.left
       additive := inferInstanceAs G.Additive
       comparison := b.hom
       isLocalization := inferInstance
       isLeftDerived := ⟨⟨⟨hb⟩⟩⟩ }⟩

section

variable {R : Type u} [CommRing R]

/-- **Stacks 064G.** For every `R`-module `M`, the total left derived tensor product
`- ⊗ᴸ_R M : D⁻(R) ⟶ D⁻(R)` exists. -/
@[stacks 064G]
public def derivedTensorProduct (M : ModuleCat.{u} R) : TotalDerivedTensor M :=
  Classical.choice (by exact nonempty_totalDerivedTensor M)

end

end CochainComplex.ComputingTor

end
