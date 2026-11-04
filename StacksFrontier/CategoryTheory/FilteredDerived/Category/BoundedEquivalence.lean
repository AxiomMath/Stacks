module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Opposite
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.Objects
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.Opposite
public import StacksFrontier.Homology.FilteredDerivedCategory.Triangulated

/-!
# Bounded filtered derived categories via filtered injectives and projectives

Let `A` be an abelian category. If `A` has enough injectives, the bounded below filtered
derived category `DF⁺(A)` is equivalent to the bounded below homotopy category of complexes
of filtered injective objects. Dually, if `A` has enough projectives, the bounded above
filtered derived category `DF⁻(A)` is equivalent to the bounded above homotopy category of
complexes of filtered projective objects.

## Main definitions

* `CategoryTheory.FilteredDerived.filteredProjectiveMinusC`: the bounded above complexes of
  finite filtered objects whose terms are filtered projective.
* `CategoryTheory.FilteredDerived.filteredProjectiveMinus`: the corresponding full
  subcategory of `K⁻(Fil^f(A))`.
* `CategoryTheory.FilteredDerived.filteredProjectiveMinusToDerivedMinus`: the canonical
  functor from it to `DF⁻(A)`.

## Main results

* `CochainComplex.FilteredDerivedCategory.toPlus` is the injective comparison functor and
  `CochainComplex.FilteredDerivedCategory.isEquivalence_isTriangulated_toPlus_and_squares`
  says that it is an equivalence when `A` has enough injectives.
* `CategoryTheory.FilteredDerived.filteredProjectiveMinusToDerivedMinus_isEquivalence`: the
  projective comparison functor is an equivalence when `A` has enough projectives.

## References

* [Stacks Project, Tag 03TB](https://stacks.math.columbia.edu/tag/03TB)
-/

add_to_stacks 03TB "injective case" CochainComplex.FilteredDerivedCategory.toPlus
add_to_stacks 03TB "injective equivalence"
  CochainComplex.FilteredDerivedCategory.isEquivalence_isTriangulated_toPlus_and_squares

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject Opposite

universe v u

namespace CategoryTheory.FilteredDerived

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Bounded-above complexes whose terms are filtered projective. -/
def filteredProjectiveMinusC : ObjectProperty
    (CochainComplex (FiniteFilteredObject A) ℤ) :=
  fun K => (∃ a : ℤ, K.IsStrictlyLE a) ∧
    ∀ n : ℤ, IsFilteredProjective (K.X n)

/-- The full subcategory of `K⁻(Fil^f(A))` represented by bounded-above complexes of
filtered projective objects. -/
def filteredProjectiveMinus : ObjectProperty
    (CochainComplex.FilteredDerivedCategory.Kminus (𝒜 := A)).FullSubcategory :=
  ((filteredProjectiveMinusC A).strictMap (HomotopyCategory.quotient _ _)).inverseImage
    (CochainComplex.FilteredDerivedCategory.Kminus (𝒜 := A)).ι

/-- The canonical functor from bounded-above complexes of filtered projectives to the
bounded-above filtered derived category. -/
noncomputable def filteredProjectiveMinusToDerivedMinus :
    (filteredProjectiveMinus A).FullSubcategory ⥤
      (CochainComplex.FilteredDerivedCategory.minus A).FullSubcategory :=
  (filteredProjectiveMinus A).ι ⋙ CochainComplex.FilteredDerivedCategory.Qminus

/-- The identity functor induces the identity on the homotopy category. -/
private noncomputable def homotopyIdIso (B : Type*) [Category B] [Preadditive B] :
    (𝟭 B).mapHomotopyCategory (.up ℤ) ≅ 𝟭 (HomotopyCategory B (.up ℤ)) :=
  CategoryTheory.Quotient.natIsoLift _
    (Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso B (.up ℤ))
      (HomotopyCategory.quotient B (.up ℤ)))

/-- An additive equivalence induces an equivalence on homotopy categories. -/
private noncomputable def mapHomotopyCategoryEquivalence
    {B D : Type*} [Category B] [Category D] [Preadditive B] [Preadditive D]
    (e : B ≌ D) [e.functor.Additive] :
    HomotopyCategory B (.up ℤ) ≌ HomotopyCategory D (.up ℤ) :=
  CategoryTheory.Equivalence.mk
    (e.functor.mapHomotopyCategory (.up ℤ))
    (e.inverse.mapHomotopyCategory (.up ℤ))
    ((Functor.mapHomotopyCategoryCompIso e.unitIso.symm (.up ℤ) ≪≫
      homotopyIdIso B).symm)
    (Functor.mapHomotopyCategoryCompIso e.counitIso (.up ℤ) ≪≫ homotopyIdIso D)

/-- A morphism of cochain complexes is a homotopy equivalence if and only if its image under
the opposite-complex equivalence is one. -/
private lemma homotopyEquivalences_opEquivalence_functor_map_iff
    {B : Type u} [Category.{v} B] [Preadditive B]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) :
    HomologicalComplex.homotopyEquivalences Bᵒᵖ (ComplexShape.up ℤ)
        ((CochainComplex.opEquivalence B).functor.map f.op) ↔
      HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ) f := by
  constructor
  · rintro ⟨e, he⟩
    let Φ := (CochainComplex.opEquivalence B).functor
    let g : L ⟶ K := (Φ.preimage e.inv).unop
    have hg : Φ.map g.op = e.inv := Φ.map_preimage e.inv
    refine ⟨{ hom := f, inv := g, homotopyHomInvId := ?_, homotopyInvHomId := ?_ }, rfl⟩
    · refine CochainComplex.homotopyOpEquiv.symm
        ((Homotopy.ofEq ?_).trans (e.homotopyInvHomId.trans (Homotopy.ofEq ?_)))
      · rw [op_comp, Φ.map_comp, hg, he]
      · simp
    · refine CochainComplex.homotopyOpEquiv.symm
        ((Homotopy.ofEq ?_).trans (e.homotopyHomInvId.trans (Homotopy.ofEq ?_)))
      · rw [op_comp, Φ.map_comp, hg, he]
      · simp
  · rintro ⟨e, rfl⟩
    let Φ := (CochainComplex.opEquivalence B).functor
    exact ⟨{ hom := Φ.map e.hom.op
             inv := Φ.map e.inv.op
             homotopyHomInvId := (Homotopy.ofEq (by rw [← Φ.map_comp]; rfl)).trans
               ((CochainComplex.homotopyOpEquiv e.homotopyInvHomId).trans
                 (Homotopy.ofEq (by simp)))
             homotopyInvHomId := (Homotopy.ofEq (by rw [← Φ.map_comp]; rfl)).trans
               ((CochainComplex.homotopyOpEquiv e.homotopyHomInvId).trans
                 (Homotopy.ofEq (by simp))) }, rfl⟩

/-- The quotient functor from cochain complexes of `Bᵒᵖ` to the opposite of the homotopy
category of `B`. -/
private noncomputable def homotopyOpQuotient
    (B : Type u) [Category.{v} B] [Preadditive B] :
    CochainComplex Bᵒᵖ ℤ ⥤ (HomotopyCategory B (.up ℤ))ᵒᵖ :=
  (CochainComplex.opEquivalence B).inverse ⋙ (HomotopyCategory.quotient B (.up ℤ)).op

/-- `CategoryTheory.FilteredDerived.homotopyOpQuotient` is a localization at the homotopy
equivalences. -/
private lemma homotopyOpQuotient_isLocalization
    (B : Type u) [Category.{v} B] [Preadditive B] [HasBinaryBiproducts B] :
    (homotopyOpQuotient B).IsLocalization
      (HomologicalComplex.homotopyEquivalences Bᵒᵖ (.up ℤ)) := by
  let opQuotient := homotopyOpQuotient B
  refine Functor.IsLocalization.of_equivalence_source
    (HomotopyCategory.quotient B (ComplexShape.up ℤ)).op
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ)).op
    opQuotient (HomologicalComplex.homotopyEquivalences Bᵒᵖ (ComplexShape.up ℤ))
    (CochainComplex.opEquivalence B) ?_ ?_ ?_
  · rintro ⟨K⟩ ⟨L⟩ f hf
    exact MorphismProperty.le_isoClosure _ _
      ((homotopyEquivalences_opEquivalence_functor_map_iff f.unop).2 hf)
  · rintro K L g hg
    have h : HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ)
        ((CochainComplex.opEquivalence B).inverse.map g).unop := by
      rw [← homotopyEquivalences_opEquivalence_functor_map_iff]
      have key : (CochainComplex.opEquivalence B).functor.map
          (((CochainComplex.opEquivalence B).inverse.map g).unop).op =
          (CochainComplex.opEquivalence B).counitIso.hom.app K ≫ g ≫
            (CochainComplex.opEquivalence B).counitIso.inv.app L := by simp
      rw [key]
      exact (MorphismProperty.arrow_mk_iso_iff _
        (Arrow.isoMk ((CochainComplex.opEquivalence B).counitIso.app K)
          ((CochainComplex.opEquivalence B).counitIso.app L) (by simp))).2 hg
    rw [← HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences] at h
    dsimp [opQuotient, homotopyOpQuotient]
    exact (inferInstance : IsIso ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
      ((CochainComplex.opEquivalence B).inverse.map g).unop).op)
  · exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CochainComplex.opEquivalence B).unitIso.symm _ ≪≫
      Functor.leftUnitor _

attribute [local instance] homotopyOpQuotient_isLocalization

/-- The opposite of the homotopy category of `B` is the homotopy category of `Bᵒᵖ`. -/
private noncomputable def homotopyOpEquivalence
    (B : Type u) [Category.{v} B] [Preadditive B] [HasBinaryBiproducts B] :
    (HomotopyCategory B (.up ℤ))ᵒᵖ ≌ HomotopyCategory Bᵒᵖ (.up ℤ) :=
  Localization.uniq (homotopyOpQuotient B) (HomotopyCategory.quotient Bᵒᵖ (.up ℤ))
    (HomologicalComplex.homotopyEquivalences Bᵒᵖ (.up ℤ))

/-- `CategoryTheory.FilteredDerived.homotopyOpEquivalence` is compatible with the quotient
functors from cochain complexes. -/
private noncomputable def homotopyOpEquivalenceFactors
    (B : Type u) [Category.{v} B] [Preadditive B] [HasBinaryBiproducts B] :
    (HomotopyCategory.quotient B (.up ℤ)).op ⋙ (homotopyOpEquivalence B).functor ≅
      (CochainComplex.opEquivalence B).functor ⋙
        HomotopyCategory.quotient Bᵒᵖ (.up ℤ) :=
  Functor.isoWhiskerRight
      ((CochainComplex.opEquivalence B).funInvIdAssoc
        (HomotopyCategory.quotient B (.up ℤ)).op).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Localization.compUniqFunctor
      (homotopyOpQuotient B) (HomotopyCategory.quotient Bᵒᵖ (.up ℤ))
      (HomologicalComplex.homotopyEquivalences Bᵒᵖ (.up ℤ)))

/-- Filtration duality on the homotopy categories of finite filtered objects. -/
private noncomputable def dualHomotopyEquivalence :
    (HomotopyCategory (FiniteFilteredObject A) (.up ℤ))ᵒᵖ ≌
      HomotopyCategory (FiniteFilteredObject Aᵒᵖ) (.up ℤ) :=
  have : (dualFiniteEquivalence A).functor.Additive := dualFiniteFunctor_additive A
  (homotopyOpEquivalence (FiniteFilteredObject A)).trans
    (mapHomotopyCategoryEquivalence (dualFiniteEquivalence A))

/-- Dualize the coefficients of a complex and reverse its cohomological grading. -/
private noncomputable def dualComplex
    (K : CochainComplex (FiniteFilteredObject A) ℤ) :
    CochainComplex (FiniteFilteredObject Aᵒᵖ) ℤ :=
  (dualFiniteFunctor A).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
    ((CochainComplex.opEquivalence (FiniteFilteredObject A)).functor.obj (op K))

/-- Opposite dualization turns a bounded-above complex into a bounded-below complex. -/
private theorem dualComplex_isStrictlyGE (K : CochainComplex (FiniteFilteredObject A) ℤ)
    (a : ℤ) [K.IsStrictlyLE a] : (dualComplex A K).IsStrictlyGE (-a) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  dsimp [dualComplex]
  show IsZero ((dualFiniteFunctor A).obj (Opposite.op (K.X (-i))))
  exact (dualFiniteFunctor A).map_isZero (K.isZero_of_isStrictlyLE a (-i) (by lia)).op

/-- The termwise dual of a filtered-projective complex has filtered-injective terms. -/
private theorem dualComplex_filteredInjective
    (K : CochainComplex (FiniteFilteredObject A) ℤ)
    (hK : ∀ n, IsFilteredProjective (K.X n)) :
    ∀ n p : ℤ, Injective ((FiniteFilteredObject.grP (𝒜 := Aᵒᵖ) p).obj
      ((dualComplex A K).X n)) :=
  fun n p ↦ (dualFinite_filteredInjective A (K.X (-n)) (hK (-n))).2 p

/-- A bounded-above filtered-projective complex dualizes to a bounded-below complex of
filtered-injective objects. -/
private theorem dualComplex_filteredInjectivePlusC
    (K : CochainComplex (FiniteFilteredObject A) ℤ)
    (hK : (∃ b : ℤ, K.IsStrictlyLE b) ∧
      ∀ n : ℤ, IsFilteredProjective (K.X n)) :
    CochainComplex.FilteredDerivedCategory.filteredInjectivePlusC Aᵒᵖ
      (dualComplex A K) := by
  show (∃ a, (dualComplex A K).IsStrictlyGE a) ∧
    ∀ n p, Injective ((FiniteFilteredObject.grP p).obj ((dualComplex A K).X n))
  obtain ⟨⟨b, hb⟩, hproj⟩ := hK
  exact ⟨⟨-b, dualComplex_isStrictlyGE A K b⟩,
    dualComplex_filteredInjective A K hproj⟩

/-- Filtration duality on the categories of complexes of finite filtered objects. -/
private noncomputable def dualComplexEquivalence :
    (CochainComplex (FiniteFilteredObject A) ℤ)ᵒᵖ ≌
      CochainComplex (FiniteFilteredObject Aᵒᵖ) ℤ :=
  have : (dualFiniteEquivalence A).functor.Additive := dualFiniteFunctor_additive A
  (CochainComplex.opEquivalence (FiniteFilteredObject A)).trans
    ((dualFiniteEquivalence A).mapHomologicalComplex (.up ℤ))

/-- Filtration duality shifts the graded pieces of a complex from `p` to `-p - 1`. -/
private noncomputable def dualComplexGrIso (p : ℤ) :
    (dualComplexEquivalence A).functor ⋙
        (FiniteFilteredObject.grP (𝒜 := Aᵒᵖ) p).mapHomologicalComplex (.up ℤ) ≅
      ((FiniteFilteredObject.grP (𝒜 := A) (-p - 1)).mapHomologicalComplex (.up ℤ)).op ⋙
        (CochainComplex.opEquivalence A).functor :=
  Functor.isoWhiskerLeft (CochainComplex.opEquivalence (FiniteFilteredObject A)).functor
    (NatIso.mapHomologicalComplex (dualGrNatIso A p) (.up ℤ))

/-- Filtration duality preserves and reflects filtered quasi-isomorphisms of complexes. -/
private lemma dualComplex_quasiIso_iff
    {K L : CochainComplex (FiniteFilteredObject A) ℤ} (f : K ⟶ L) :
    CochainComplex.filteredQuasiIsoC ((dualComplexEquivalence A).functor.map f.op) ↔
      CochainComplex.filteredQuasiIsoC f := by
  have h (p : ℤ) : QuasiIso
      (((FiniteFilteredObject.grP (𝒜 := Aᵒᵖ) p).mapHomologicalComplex (.up ℤ)).map
        ((dualComplexEquivalence A).functor.map f.op)) ↔
      QuasiIso
        (((FiniteFilteredObject.grP (𝒜 := A) (-p - 1)).mapHomologicalComplex (.up ℤ)).map f) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoOfNatIso (dualComplexGrIso A p) f.op)).trans
        (CochainComplex.quasiIso_opEquivalence_functor_map_iff _)
  refine ⟨fun hf p ↦ ?_, fun hf p ↦ (h p).2 (hf (-p - 1))⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℤ, p = -q - 1 := ⟨-p - 1, by lia⟩
  exact (h q).1 (hf q)

/-- Filtration duality on homotopy categories is compatible with the quotient functors. -/
private noncomputable def dualHomotopyFactors :
    (HomotopyCategory.quotient (FiniteFilteredObject A) (.up ℤ)).op ⋙
        (dualHomotopyEquivalence A).functor ≅
      (dualComplexEquivalence A).functor ⋙
        HomotopyCategory.quotient (FiniteFilteredObject Aᵒᵖ) (.up ℤ) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (homotopyOpEquivalenceFactors (FiniteFilteredObject A)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((dualFiniteFunctor A).mapHomotopyCategoryFactors (.up ℤ)) ≪≫
    (Functor.associator _ _ _).symm

/-- Filtration duality preserves and reflects filtered quasi-isomorphisms in the homotopy
category. -/
private lemma dualHomotopy_quasiIso_iff
    {K L : HomotopyCategory (FiniteFilteredObject A) (.up ℤ)} (f : K ⟶ L) :
    HomotopyCategory.filteredQuasiIso Aᵒᵖ
        ((dualHomotopyEquivalence A).functor.map f.op) ↔
      HomotopyCategory.filteredQuasiIso A f := by
  obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
  obtain ⟨L, rfl⟩ := L.quotient_obj_surjective
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
  exact ((HomotopyCategory.filteredQuasiIso Aᵒᵖ).arrow_mk_iso_iff
    (Arrow.isoOfNatIso (dualHomotopyFactors A) f.op)).trans
      ((CochainComplex.filteredQuasiIso_quotient_map_iff _).trans
        ((dualComplex_quasiIso_iff A f).trans
          (CochainComplex.filteredQuasiIso_quotient_map_iff f).symm))

/-- Precomposing a localization with an equivalence that matches the inverted morphism
classes gives a localization. -/
private lemma isLocalization_comp_equivalence
    {C D E : Type*} [Category C] [Category D] [Category E]
    (e : C ≌ D) (W : MorphismProperty C) (V : MorphismProperty D)
    [V.RespectsIso] (L : D ⥤ E) [L.IsLocalization V]
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), V (e.functor.map f) ↔ W f) :
    (e.functor ⋙ L).IsLocalization W :=
  Functor.IsLocalization.of_equivalence_source L V _ W e.symm
    (fun _ _ f hf ↦ MorphismProperty.le_isoClosure _ _
      ((h _).1 ((V.arrow_mk_iso_iff (Arrow.isoOfNatIso e.counitIso f)).2 hf)))
    (fun _ _ f hf ↦ Localization.inverts L V _ ((h f).2 hf)) (e.invFunIdAssoc L)

/-- The filtered derived category of `Aᵒᵖ` is a localization of the opposite homotopy
category of `A`. -/
private lemma dualHomotopyQ_isLocalization :
    ((dualHomotopyEquivalence A).functor ⋙
      CochainComplex.FilteredDerivedCategory.Qh (𝒜 := Aᵒᵖ)).IsLocalization
        (HomotopyCategory.filteredQuasiIso A).op :=
  isLocalization_comp_equivalence (dualHomotopyEquivalence A)
    (HomotopyCategory.filteredQuasiIso A).op (HomotopyCategory.filteredQuasiIso Aᵒᵖ)
    CochainComplex.FilteredDerivedCategory.Qh
    (fun _ _ f ↦ dualHomotopy_quasiIso_iff A f.unop)

attribute [local instance] dualHomotopyQ_isLocalization

/-- Filtration duality on the filtered derived categories. -/
private noncomputable def dualDerivedEquivalence :
    (CochainComplex.FilteredDerivedCategory A)ᵒᵖ ≌
      CochainComplex.FilteredDerivedCategory Aᵒᵖ :=
  Localization.uniq (CochainComplex.FilteredDerivedCategory.Qh (𝒜 := A)).op
    ((dualHomotopyEquivalence A).functor ⋙ CochainComplex.FilteredDerivedCategory.Qh)
    (HomotopyCategory.filteredQuasiIso A).op

/-- Filtration duality on the filtered derived categories is compatible with the localization
functors. -/
private noncomputable def dualDerivedFactors :
    (CochainComplex.FilteredDerivedCategory.Qh (𝒜 := A)).op ⋙
        (dualDerivedEquivalence A).functor ≅
      (dualHomotopyEquivalence A).functor ⋙ CochainComplex.FilteredDerivedCategory.Qh :=
  Localization.compUniqFunctor _ _ (HomotopyCategory.filteredQuasiIso A).op

/-- Bijectivity of the maps of a functor transports across a commuting square whose vertical
functors are full and faithful, respectively faithful. -/
private lemma map_bijective_of_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F : C ⥤ D) (G : C' ⥤ D') (E : C ⥤ C') (H : D ⥤ D')
    [E.Full] [E.Faithful] [H.Faithful]
    (e : F ⋙ H ≅ E ⋙ G) (X Y : C)
    (h : Function.Bijective (G.map : (E.obj X ⟶ E.obj Y) → _)) :
    Function.Bijective (F.map : (X ⟶ Y) → _) := by
  constructor
  · intro f g hfg
    apply E.map_injective
    apply h.1
    apply (cancel_epi (e.hom.app X)).1
    have hf := e.hom.naturality f
    have hg := e.hom.naturality g
    dsimp only [Functor.comp_map] at hf hg
    rw [← hf, ← hg]
    show H.map (F.map f) ≫ _ = H.map (F.map g) ≫ _
    rw [hfg]
  · intro f
    obtain ⟨g, hg⟩ := h.2 (e.inv.app X ≫ H.map f ≫ e.hom.app Y)
    obtain ⟨k, rfl⟩ := E.map_surjective g
    refine ⟨k, H.map_injective ?_⟩
    apply (cancel_mono (e.hom.app Y)).1
    show (F ⋙ H).map k ≫ _ = _
    rw [e.hom.naturality]
    show e.hom.app X ≫ G.map (E.map k) = _
    rw [hg]
    simp

/-- The localization functor is bijective on morphisms out of a bounded-above complex of
filtered projective objects. -/
@[sga "4½ Rapport 4.4" "more general"]
private lemma map_bijective_Qh_of_filteredProjective
    {K : CochainComplex (FiniteFilteredObject A) ℤ}
    (hK : filteredProjectiveMinusC A K)
    (Y : HomotopyCategory (FiniteFilteredObject A) (.up ℤ)) :
    Function.Bijective (CochainComplex.FilteredDerivedCategory.Qh.map :
      ((HomotopyCategory.quotient _ _).obj K ⟶ Y) → _) := by
  let X := (HomotopyCategory.quotient (FiniteFilteredObject A) (.up ℤ)).obj K
  have hi : CochainComplex.FilteredDerivedCategory.filteredInjectivePlus Aᵒᵖ
      ((HomotopyCategory.quotient _ _).obj (dualComplex A K)) :=
    ⟨_, dualComplex_filteredInjectivePlusC A K hK⟩
  have hr : (HomotopyCategory.filteredAcyclic Aᵒᵖ).rightOrthogonal
      ((dualHomotopyEquivalence A).functor.obj (op X)) :=
    ((HomotopyCategory.filteredAcyclic Aᵒᵖ).rightOrthogonal).prop_of_iso
      ((dualHomotopyFactors A).app (op K)).symm
      (CochainComplex.FilteredDerivedCategory.rightOrthogonal_of_filteredInjectivePlus hi)
  have hh := map_bijective_of_square
    (CochainComplex.FilteredDerivedCategory.Qh (𝒜 := A)).op
    (CochainComplex.FilteredDerivedCategory.Qh (𝒜 := Aᵒᵖ))
    (dualHomotopyEquivalence A).functor (dualDerivedEquivalence A).functor
    (dualDerivedFactors A) (op Y) (op X)
    (hr.map_bijective_of_isTriangulated CochainComplex.FilteredDerivedCategory.Qh _)
  refine ⟨fun f g h ↦ Quiver.Hom.op_inj (hh.1 (congrArg Quiver.Hom.op h)), fun f ↦ ?_⟩
  obtain ⟨g, hg⟩ := hh.2 f.op
  exact ⟨g.unop, congrArg Quiver.Hom.unop hg⟩

/-- The localization functor is bijective on morphisms out of an object of
`filteredProjectiveMinus`. -/
private lemma map_bijective_Qh_of_filteredProjectiveMinus
    (X : (filteredProjectiveMinus A).FullSubcategory)
    (Y : HomotopyCategory (FiniteFilteredObject A) (.up ℤ)) :
    Function.Bijective (CochainComplex.FilteredDerivedCategory.Qh.map :
      (X.obj.obj ⟶ Y) → _) := by
  obtain ⟨K, hK, hX⟩ := (ObjectProperty.strictMap_iff _ _ _).1 X.property
  change (HomotopyCategory.quotient _ _).obj K = X.obj.obj at hX
  rw [← hX]
  exact map_bijective_Qh_of_filteredProjective A hK Y

/-- The projective comparison functor is faithful. -/
private lemma filteredProjectiveMinusToDerivedMinus_faithful :
    (filteredProjectiveMinusToDerivedMinus A).Faithful where
  map_injective {X Y} f g h := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (map_bijective_Qh_of_filteredProjectiveMinus A X Y.obj.obj).1
      (congrArg (fun k ↦ k.hom) h)

attribute [local instance] filteredProjectiveMinusToDerivedMinus_faithful

/-- The projective comparison functor is full. -/
private lemma filteredProjectiveMinusToDerivedMinus_full :
    (filteredProjectiveMinusToDerivedMinus A).Full where
  map_surjective {X Y} f := by
    obtain ⟨g, hg⟩ := (map_bijective_Qh_of_filteredProjectiveMinus A X Y.obj.obj).2 f.hom
    exact ⟨ObjectProperty.homMk (ObjectProperty.homMk g), ObjectProperty.hom_ext _ hg⟩

attribute [local instance] filteredProjectiveMinusToDerivedMinus_full

/-- A complex whose dual is isomorphic to a bounded-below complex of filtered injectives is
itself a bounded-above complex of filtered projectives. -/
private lemma filteredProjectiveMinusC_of_dualComplex_iso
    (K : CochainComplex (FiniteFilteredObject A) ℤ)
    {I : CochainComplex (FiniteFilteredObject Aᵒᵖ) ℤ}
    (e : dualComplex A K ≅ I)
    (hI : CochainComplex.FilteredDerivedCategory.filteredInjectivePlusC Aᵒᵖ I) :
    filteredProjectiveMinusC A K := by
  obtain ⟨⟨a, ha⟩, hi⟩ := hI
  refine ⟨⟨-a, ?_⟩, ?_⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = -m := ⟨-n, by lia⟩
    have hz := (I.isZero_of_isStrictlyGE a m (by lia)).of_iso
      (HomologicalComplex.Hom.isoApp e m)
    exact (IsZero.of_full_of_faithful_of_isZero (dualFiniteEquivalence A).functor
      (op (K.X (-m))) hz).unop
  · intro n p
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = -m := ⟨-n, by lia⟩
    obtain ⟨q, rfl⟩ : ∃ q : ℤ, p = -q - 1 := ⟨-p - 1, by lia⟩
    have hj : Injective ((FilteredObject.gr q).obj
        (dualFilteredObject A (K.X (-m)).obj)) :=
      Injective.of_iso
        ((FiniteFilteredObject.grP q).mapIso (HomologicalComplex.Hom.isoApp e m)).symm
        (hi m q)
    exact Injective.projective_iff_injective_op.2
      (Injective.of_iso (dualGrIso A (K.X (-m)).obj q) hj)

/-- The projective comparison functor is essentially surjective when `A` has enough
projectives. -/
private lemma filteredProjectiveMinusToDerivedMinus_essSurj [EnoughProjectives A] :
    (filteredProjectiveMinusToDerivedMinus A).EssSurj where
  mem_essImage Y := by
    obtain ⟨X, hX, ⟨eX⟩⟩ :=
      CochainComplex.FilteredDerivedCategory.exists_Qh_obj_iso_of_minus Y.property
    obtain ⟨K, ⟨a, ha⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX
    let q := HomotopyCategory.quotient (FiniteFilteredObject A) (.up ℤ)
    let q' := HomotopyCategory.quotient (FiniteFilteredObject Aᵒᵖ) (.up ℤ)
    have hplus : HomotopyCategory.plus (FiniteFilteredObject Aᵒᵖ)
        (q'.obj (dualComplex A K)) :=
      (HomotopyCategory.plus_quotient_obj_iff _).2
        ⟨-a, dualComplex_isStrictlyGE A K a⟩
    let Z : (CochainComplex.FilteredDerivedCategory.plus Aᵒᵖ).FullSubcategory :=
      ⟨CochainComplex.FilteredDerivedCategory.Qh.obj (q'.obj (dualComplex A K)),
        CochainComplex.FilteredDerivedCategory.plus_Qh_obj_of_plus hplus⟩
    obtain ⟨J, ⟨eJ⟩⟩ := Functor.EssSurj.mem_essImage
      (F := CochainComplex.FilteredDerivedCategory.toPlus Aᵒᵖ) Z
    obtain ⟨I, hI, hJ⟩ := (ObjectProperty.strictMap_iff _ _ _).1 J.property
    let P := ((dualComplexEquivalence A).inverse.obj I).unop
    let eP : dualComplex A P ≅ I := (dualComplexEquivalence A).counitIso.app I
    have hP := filteredProjectiveMinusC_of_dualComplex_iso A P eP hI
    let P' : (filteredProjectiveMinus A).FullSubcategory :=
      ⟨⟨q.obj P, ⟨P, hP.1⟩⟩, ⟨P, hP⟩⟩
    let eI : CochainComplex.FilteredDerivedCategory.Qh.obj (q'.obj I) ≅
        CochainComplex.FilteredDerivedCategory.Qh.obj (q'.obj (dualComplex A K)) :=
      CochainComplex.FilteredDerivedCategory.Qh.mapIso (eqToIso hJ) ≪≫
        (CochainComplex.FilteredDerivedCategory.plus Aᵒᵖ).ι.mapIso eJ
    let eD : (dualDerivedEquivalence A).functor.obj
          (op (CochainComplex.FilteredDerivedCategory.Qh.obj (q.obj P))) ≅
        (dualDerivedEquivalence A).functor.obj (op Y.obj) :=
      (dualDerivedFactors A).app (op (q.obj P)) ≪≫
        CochainComplex.FilteredDerivedCategory.Qh.mapIso
          ((dualHomotopyFactors A).app (op P)) ≪≫
        CochainComplex.FilteredDerivedCategory.Qh.mapIso (q'.mapIso eP) ≪≫ eI ≪≫
        (CochainComplex.FilteredDerivedCategory.Qh.mapIso
          ((dualHomotopyFactors A).app (op K))).symm ≪≫
        ((dualDerivedFactors A).app (op (q.obj K))).symm ≪≫
        (dualDerivedEquivalence A).functor.mapIso eX.symm.op
    exact ⟨P', ⟨(CochainComplex.FilteredDerivedCategory.minus A).isoMk
      (((dualDerivedEquivalence A).functor.preimageIso eD).unop.symm)⟩⟩

attribute [local instance] filteredProjectiveMinusToDerivedMinus_essSurj

/-- The bounded-above filtered derived category is equivalent to the bounded-above homotopy
category of filtered projective objects. -/
@[stacks 03TB "projective case"]
theorem filteredProjectiveMinusToDerivedMinus_isEquivalence [EnoughProjectives A] :
    (filteredProjectiveMinusToDerivedMinus A).IsEquivalence :=
  {}

end CategoryTheory.FilteredDerived

end
