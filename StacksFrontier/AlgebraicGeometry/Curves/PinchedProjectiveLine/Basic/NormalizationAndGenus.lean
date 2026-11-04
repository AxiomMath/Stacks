module

public import StacksFrontier.AlgebraicGeometry.Curves.PinchedProjectiveLine.Basic.Properties
import all StacksFrontier.AlgebraicGeometry.Curves.PinchedProjectiveLine.Basic.Construction
import all StacksFrontier.AlgebraicGeometry.Curves.PinchedProjectiveLine.Basic.Properties
import all StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSections

/-!
# The pinched projective line: normalization, genus and the existence statement

The identification of the canonical normalization of the pinched projective line with the
projective line over `K`, the vanishing of its first cohomology and of its genus, and the
existence statement `AlgebraicGeometry.exists_pinchedProjectiveLine`
([Stacks Project, Tag 0DJC](https://stacks.math.columbia.edu/tag/0DJC)).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

attribute [local instance] isZariskiLocalAtSource_locallyOfFiniteType

attribute [local instance] isZariskiLocalAtSource_locallyQuasiFinite

attribute [local instance] pinchedChartA_isOpenImmersion

attribute [local instance] pinchedChartB_isOpenImmersion

attribute [local instance] pinchedCurve_isIntegral

attribute [local instance] pinchedCurve_compactSpace

attribute [local instance] pinchedStructureMorphism_locallyOfFiniteType

attribute [local instance] pinchedStructureMorphism_isSeparated

attribute [local instance] pinchedNormalizationMorphism_surjective

private theorem projectiveLine_isIntegral :
    IsIntegral (projectiveLine K) := by
  let D := projectiveLineGluingData K
  have : ∀ i : D.openCover.I₀, IsReduced (D.openCover.X i) := by
    change ∀ i : D.J, IsReduced (D.U i)
    rintro ⟨i⟩
    cases i <;> change IsReduced (Spec (.of (Polynomial K))) <;> infer_instance
  have : IsReduced (projectiveLine K) :=
    IsReduced.of_openCover _ D.openCover
  let i := projectiveLineXChart K
  let j := projectiveLineYChart K
  have hrange : ∀ f : Spec (.of (Polynomial K)) ⟶ projectiveLine K,
      IsIrreducible (Set.range f.base) := fun f => by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (Spec (.of (Polynomial K)))).image
        f.base f.continuous.continuousOn
  have hi := hrange i
  have hj := hrange j
  have hmeet : (Set.range i.base ∩ Set.range j.base).Nonempty := by
    let z : Spec (.of (LaurentPolynomial K)) := ⟨⊥, inferInstance⟩
    refine ⟨i (projectiveLinePuncturedChart K z),
      ⟨_, rfl⟩, ?_⟩
    refine ⟨projectiveLinePuncturedChart K
      ((projectiveLineInversionIso K).hom z), ?_⟩
    exact congrArg (fun f : Spec (.of (LaurentPolynomial K)) ⟶
      projectiveLine K => f z)
        (projectiveLineInversion_comp_charts K)
  have hirr := isIrreducible_union_of_isOpen hi hj
    i.isOpenEmbedding.isOpen_range j.isOpenEmbedding.isOpen_range hmeet
  have hcover : Set.range i.base ∪ Set.range j.base = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨⟨b⟩, y, rfl⟩ := D.ι_jointly_surjective x
    cases b
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr ⟨y, rfl⟩
  rw [hcover] at hirr
  have : IrreducibleSpace (projectiveLine K) :=
    (irreducibleSpace_def _).mpr hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

attribute [local instance] projectiveLine_isIntegral

private theorem projectiveLine_isNormal :
    IsNormal (projectiveLine K) := by
  let D := projectiveLineGluingData K
  refine (isNormal_iff_stalk_normal _).2 fun x => ?_
  obtain ⟨i, y, rfl⟩ := D.openCover.exists_eq x
  have hreg : IsRegularLocalRing ((D.openCover.X i).presheaf.stalk y) := by
    change IsRegularLocalRing ((D.U i).presheaf.stalk y)
    rcases i with ⟨i⟩
    cases i <;> exact regularLocalRing_spec_of_principal y
  let e := (asIso ((D.openCover.f i).stalkMap y)).commRingCatIsoToRingEquiv
  have : IsDomain ((D.openCover.X i).presheaf.stalk y) := by
    change IsDomain ((D.U i).presheaf.stalk y)
    rcases i with ⟨i⟩
    cases i <;>
      change IsDomain ((Spec (.of (Polynomial K))).presheaf.stalk y) <;>
      exact Function.Injective.isDomain
        (Spec.stalkIso (.of (Polynomial K)) y).commRingCatIsoToRingEquiv
        (Spec.stalkIso (.of (Polynomial K)) y).commRingCatIsoToRingEquiv.injective
  have : IsDomain ((projectiveLine K).presheaf.stalk
      (D.openCover.f i y)) := Function.Injective.isDomain e e.injective
  refine ⟨inferInstance, ?_⟩
  have : IsIntegrallyClosed ((D.openCover.X i).presheaf.stalk y) :=
    isIntegrallyClosed_of_isRegularLocalRing _
  exact IsIntegrallyClosed.of_equiv e.symm

attribute [local instance] projectiveLine_isSeparated

attribute [local instance] projectiveLine_locallyOfFiniteType

attribute [local instance] projectiveLine_isProper

/-- A property of morphisms local on the source, stable under composition and satisfied by finite
morphisms and open immersions, holds for the normalization morphism. -/
private theorem pinchedNormalizationMorphism_property [Module.Finite k K]
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P] [P.IsStableUnderComposition]
    (hfin : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f], P f)
    (hopen : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f], P f) :
    P (pinchedNormalizationMorphism k K).val := by
  apply IsZariskiLocalAtSource.of_openCover (P := P) (projectiveLineGluingData K).openCover
  rintro ⟨i⟩
  cases i
  · change P (projectiveLineXChart K ≫ _)
    rw [(pinchedNormalizationMorphism k K).property.1]
    have := isFinite_pinchedNormalizationAffineChart k K
    exact P.comp_mem _ _ (hfin _) (hopen _)
  · change P (projectiveLineYChart K ≫ _)
    rw [(pinchedNormalizationMorphism k K).property.2]
    exact hopen _

private theorem pinchedNormalizationMorphism_locallyOfFiniteType [Module.Finite k K] :
    LocallyOfFiniteType (pinchedNormalizationMorphism k K).val :=
  pinchedNormalizationMorphism_property k K @LocallyOfFiniteType (fun _ => inferInstance)
    fun _ => inferInstance

/- `genericPoints_map_of_openImmersion` stood here: the same statement as
`AlgebraicGeometry.mem_genericPoints_of_isOpenImmersion`,
`StacksFrontier/AlgebraicGeometry/NormalizationBaseChange/UniversalHomeomorphism.lean:58`,
which this module imports; it was `private` there, which is why this copy existed, and is
now public.

`isBirational_restrict` stood here too: the same statement as
`AlgebraicGeometry.isBirational_morphismRestrict`,
`StacksFrontier/AlgebraicGeometry/NormalizationBaseChange/UniversalHomeomorphism.lean:127`,
private there for the same reason and now public as well. Its proof used the deleted
`genericPoints_map_of_openImmersion` five times, which is why both copies went together. -/


/-- The normalization morphism of a normal scheme is an isomorphism.

This is the single direction of
[Stacks Project, Tag 0H7D](https://stacks.math.columbia.edu/tag/0H7D) used below. Tag 0H7D has
no formalization in this library yet, so the statement is kept private and untagged here;
DELETE this lemma and use the tagged equivalence as soon as 0H7D lands. -/
private theorem isIso_normalization_of_isNormal (Y : Scheme.{u})
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    [IsNormal Y] : IsIso (Scheme.normalization Y hY) := by
  have : IsNormal (Scheme.normalizationScheme Y hY) := Y.isNormal_normalizationScheme hY
  obtain ⟨s, hs, -⟩ := Scheme.existsUnique_lift_normalization hY (𝟙 Y) (by simp)
  obtain ⟨_, _, huniq⟩ := Scheme.existsUnique_lift_normalization hY
    (Scheme.normalization Y hY)
    (fun η => (Y.isBirational_normalization hY).bijOn.mapsTo η.2)
  exact ⟨⟨s, (huniq _ (by simp only [Category.assoc, hs, Category.comp_id])).trans
    (huniq (𝟙 _) (by simp)).symm, hs⟩⟩

private theorem exists_iso_normalization_of_integral_birational
    {X Y : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    (α : Y ⟶ X) [IsIntegralHom α] [IsNormal Y]
    (hcomponents : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents (α ⁻¹ᵁ U)).Finite)
    (hbirational : ∀ U : X.Opens, IsCompact (U : Set X) →
      IsBirational (α ∣_ U)) :
    ∃ e : Y ≅ Scheme.normalizationScheme X hX,
      e.hom ≫ Scheme.normalization X hX = α := by
  classical
  obtain ⟨hY', g, e, hg, he⟩ :=
    exists_normalizationFactorization_of_integral_of_birational
      hX α hcomponents hbirational
  have hhY : hY = hY' := Subsingleton.elim _ _
  have he' : e.hom ≫ Scheme.normalization Y hY = g := by
    simpa [hhY] using he
  have hnormY : IsIso (Scheme.normalization Y hY) :=
    isIso_normalization_of_isNormal Y hY
  let eY : Scheme.normalizationScheme Y hY ≅ Y := asIso (Scheme.normalization Y hY)
  let E : Y ≅ Scheme.normalizationScheme X hX := eY.symm ≪≫ e.symm
  refine ⟨E, ?_⟩
  dsimp [E, eY]
  calc
    (asIso (Scheme.normalization Y hY)).inv ≫ e.inv ≫
        Scheme.normalization X hX =
      (asIso (Scheme.normalization Y hY)).inv ≫ e.inv ≫ (g ≫ α) := by rw [← hg]
    _ = (asIso (Scheme.normalization Y hY)).inv ≫
        (e.inv ≫ g) ≫ α := by simp [Category.assoc]
    _ = (asIso (Scheme.normalization Y hY)).inv ≫
        (Scheme.normalization Y hY) ≫ α := by rw [← he', Iso.inv_hom_id_assoc]
    _ = α := by simp


private theorem finite_irreducibleComponents_open {Y : Scheme.{u}}
    [IrreducibleSpace Y] (U : Y.Opens) : (irreducibleComponents U).Finite := by
  classical
  cases isEmpty_or_nonempty U with
  | inl hU =>
    have : IsEmpty (irreducibleComponents U) :=
      ⟨fun C => isEmptyElim C.2.1.nonempty.some⟩
    exact Set.toFinite _
  | inr hU =>
    have : IrreducibleSpace U := by
      have : Nonempty (U : Set Y) := hU
      exact U.isOpen.isOpenEmbedding_subtypeVal.irreducibleSpace
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _

private theorem pinchedNormalizationMorphism_isFinite [Module.Finite k K] :
    IsFinite (pinchedNormalizationMorphism k K).val := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    (IsFinite.SpecMap_iff _).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)
  have : IsProper ((pinchedNormalizationMorphism k K).val ≫
      (pinchedStructureMorphism k K).val) := by
    rw [pinchedNormalizationMorphism_comp]
    infer_instance
  have := IsProper.of_comp (pinchedNormalizationMorphism k K).val
    (pinchedStructureMorphism k K).val
  have : LocallyQuasiFinite (pinchedNormalizationMorphism k K).val :=
    pinchedNormalizationMorphism_property k K @LocallyQuasiFinite (fun _ => inferInstance)
      fun _ => inferInstance
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

private theorem birational_of_common_open {Y Z W : Scheme.{u}}
    [IrreducibleSpace Y] [IrreducibleSpace Z] [IrreducibleSpace W]
    (f : Y ⟶ Z) (i : W ⟶ Y) (j : W ⟶ Z)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ f = j) :
    IsBirational f := by
  have hi := genericPoint_eq_of_isOpenImmersion i
  have hj := genericPoint_eq_of_isOpenImmersion j
  have hf : f (genericPoint Y) = genericPoint Z := by
    rw [← hi, ← hj]
    exact congrArg (fun g : W ⟶ Z => g (genericPoint W)) h
  constructor
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    exact Set.bijOn_singleton.mpr hf
  · intro x hx
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst x
    have hc : IsIso ((i ≫ f).stalkMap (genericPoint W)) := by rw [h]; infer_instance
    rw [Scheme.Hom.stalkMap_comp] at hc
    have : IsIso (f.stalkMap (i (genericPoint W)) ≫ i.stalkMap (genericPoint W)) := hc
    rw [← hi]
    exact IsIso.of_isIso_comp_right _ (i.stalkMap (genericPoint W))

private theorem pinchedNormalizationMorphism_normalization [Module.Finite k K] :
    ∃ e : projectiveLine K ≅
        Scheme.normalizationScheme (pinchedCurve k K)
          (fun U _ => pinchedCurve_finiteIrreducibleComponents k K U),
      (pinchedNormalizationMorphism k K).val = e.hom ≫
        Scheme.normalization (pinchedCurve k K)
          (fun U _ => pinchedCurve_finiteIrreducibleComponents k K U) := by
  have := projectiveLine_isNormal K
  have := pinchedNormalizationMorphism_isFinite k K
  have hb := birational_of_common_open (pinchedNormalizationMorphism k K).val
    (projectiveLineYChart K)
    (pinchedChartB k K) (pinchedNormalizationMorphism k K).property.2
  obtain ⟨e, he⟩ := exists_iso_normalization_of_integral_birational
    (fun U _ => pinchedCurve_finiteIrreducibleComponents k K U)
    (fun U _ => finite_irreducibleComponents_open U)
    (pinchedNormalizationMorphism k K).val
    (fun U _ => finite_irreducibleComponents_open _)
    (fun U _ => isBirational_morphismRestrict _ hb U)
  exact ⟨e, he.symm⟩

section

open Opposite TopologicalSpace

/-- The functor of sections over an open `U` of a scheme, typed as a functor out of the
category of modules on that scheme. Pinning this spelling is what lets the additivity and
exactness instances below be found at the use sites. -/
private noncomputable abbrev sectionsFunctor (X : Scheme.{u}) (U : X.Opens) :
    X.Modules ⥤ AddCommGrpCat := secF X.ringCatSheaf U

private theorem sectionsFunctor_additive (X : Scheme.{u}) (U : X.Opens) :
    (sectionsFunctor X U).Additive := ⟨by intro M N f g; rfl⟩

attribute [local instance] sectionsFunctor_additive

private theorem sectionsFunctor_preservesFiniteLimits (X : Scheme.{u}) (U : X.Opens) :
    PreservesFiniteLimits (sectionsFunctor X U) := by
  change PreservesFiniteLimits
    (SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙ forget₂ _ AddCommGrpCat)
  infer_instance

attribute [local instance] sectionsFunctor_preservesFiniteLimits

private theorem sectionsFunctor_preservesZeroMorphisms (X : Scheme.{u}) (U : X.Opens) :
    (sectionsFunctor X U).PreservesZeroMorphisms := inferInstance

attribute [local instance] sectionsFunctor_preservesZeroMorphisms

private theorem sectionsFunctor_preservesLimit_parallelPair (X : Scheme.{u}) (U : X.Opens)
    {A B : X.Modules} (f g : A ⟶ B) :
    PreservesLimit (parallelPair f g) (sectionsFunctor X U) := inferInstance

attribute [local instance] sectionsFunctor_preservesLimit_parallelPair

private theorem glue_two_sections {X : Scheme.{u}} (F : X.Modules)
    (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (a : F.presheaf.obj (op U)) (b : F.presheaf.obj (op V))
    (hab : F.presheaf.map (homOfLE inf_le_left).op a =
      F.presheaf.map (homOfLE inf_le_right).op b) :
    ∃ s : F.presheaf.obj (op ⊤),
      F.presheaf.map (homOfLE le_top).op s = a ∧
      F.presheaf.map (homOfLE le_top).op s = b := by
  let W : Bool → X.Opens := fun i => cond i V U
  let t : ∀ i, F.presheaf.obj (op (W i)) := fun i => by
    cases i
    · exact a
    · exact b
  have hw : (⊤ : X.Opens) ≤ ⨆ i, W i := by
    rw [iSup_bool_eq]
    simpa only [W, Bool.cond_true, Bool.cond_false, sup_comm] using hUV.ge
  have ht : TopCat.Presheaf.IsCompatible F.presheaf W t := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact hab
    · change F.presheaf.map (homOfLE _).op b = F.presheaf.map (homOfLE _).op a
      have h := congrArg (F.presheaf.map (eqToHom (inf_comm V U)).op) hab.symm
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at h
      convert h using 1 <;> congr 2
    · rfl
  obtain ⟨s, hs, _⟩ :=
    (TopCat.Sheaf.existsUnique_gluing' (F := ⟨F.presheaf, F.isSheaf⟩)
      W ⊤ (fun _ => homOfLE le_top) hw t ht)
  exact ⟨s, hs false, hs true⟩

private theorem sections_eq_of_two_restrictions {X : Scheme.{u}} (F : X.Modules)
    (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (a b : F.presheaf.obj (op ⊤))
    (hU : F.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a =
      F.presheaf.map (homOfLE le_top).op b)
    (hV : F.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op a =
      F.presheaf.map (homOfLE le_top).op b) : a = b :=
  TopCat.Sheaf.eq_of_locally_eq₂ (F := ⟨F.presheaf, F.isSheaf⟩)
    (homOfLE le_top) (homOfLE le_top) hUV.ge a b hU hV

private theorem sections_primitive_of_vanishing {X : Scheme.{u}}
    (F : X.Modules) (I : InjectiveResolution F) (U : X.Opens)
    (hU : IsZero (Hgroup X.ringCatSheaf U 1 F))
    (s : (I.cocomplex.X 1).presheaf.obj (op U))
    (hs : ((I.cocomplex.d 1 2).val.app (op U)) s = 0) :
    ∃ t : (I.cocomplex.X 0).presheaf.obj (op U),
      ((I.cocomplex.d 0 1).val.app (op U)) t = s := by
  have := sectionsFunctor_additive X U
  have he : (secCx X.ringCatSheaf I U).ExactAt 1 :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (hU.of_iso (I.isoRightDerivedObj (secF X.ringCatSheaf U) 1).symm)
  have he' := (HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)).mp he
  exact (ShortComplex.ab_exact_iff _).mp he' s hs

private theorem sections_primitive_zero {X : Scheme.{u}}
    (F : X.Modules) (I : InjectiveResolution F) (U : X.Opens)
    (s : (I.cocomplex.X 0).presheaf.obj (op U))
    (hs : ((I.cocomplex.d 0 1).val.app (op U)) s = 0) :
    ∃ t : F.presheaf.obj (op U), ((I.ι.f 0).val.app (op U)) t = s := by
  have := sectionsFunctor_additive X U
  have := sectionsFunctor_preservesFiniteLimits X U
  have he := I.exact₀.map_of_mono_of_preservesKernel (secF X.ringCatSheaf U)
    inferInstance inferInstance
  exact (ShortComplex.ab_exact_iff _).mp he s hs

private theorem hom_restrict {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G)
    {U V : X.Opens} (h : U ≤ V) (s : F.presheaf.obj (op V)) :
    f.val.app (op U) (F.presheaf.map (homOfLE h).op s) =
      G.presheaf.map (homOfLE h).op (f.val.app (op V) s) :=
  PresheafOfModules.naturality_apply f.val _ s

private theorem hom_sub {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) {U : X.Opens}
    (a b : F.presheaf.obj (op U)) :
    f.val.app (op U) (a - b) = f.val.app (op U) a - f.val.app (op U) b := map_sub _ a b

private theorem hom_add {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) {U : X.Opens}
    (a b : F.presheaf.obj (op U)) :
    f.val.app (op U) (a + b) = f.val.app (op U) a + f.val.app (op U) b := map_add _ a b

private theorem restrict_sub {X : Scheme.{u}} (F : X.Modules) {U V : X.Opens} (h : U ≤ V)
    (a b : F.presheaf.obj (op V)) :
    F.presheaf.map (homOfLE h).op (a - b) =
      F.presheaf.map (homOfLE h).op a - F.presheaf.map (homOfLE h).op b := map_sub _ a b

private theorem restrict_add {X : Scheme.{u}} (F : X.Modules) {U V : X.Opens} (h : U ≤ V)
    (a b : F.presheaf.obj (op V)) :
    F.presheaf.map (homOfLE h).op (a + b) =
      F.presheaf.map (homOfLE h).op a + F.presheaf.map (homOfLE h).op b := map_add _ a b

private theorem restrict_restrict {X : Scheme.{u}} (F : X.Modules)
    {U V W : X.Opens} (h : U ≤ V) (h' : V ≤ W)
    (s : F.presheaf.obj (op W)) :
    F.presheaf.map (homOfLE h).op (F.presheaf.map (homOfLE h').op s) =
      F.presheaf.map (homOfLE (h.trans h')).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private theorem hom_comp_zero_apply {X : Scheme.{u}} {F G H : X.Modules}
    (f : F ⟶ G) (g : G ⟶ H) (h : f ≫ g = 0)
    (U : X.Opens) (s : F.presheaf.obj (op U)) :
    g.val.app (op U) (f.val.app (op U) s) = 0 :=
  congrArg (fun a : F ⟶ H => a.val.app (op U) s) h

private theorem cohomology_one_vanishes_of_two_opens {X : Scheme.{u}}
    (F : X.Modules) (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (hU : IsZero (Hgroup X.ringCatSheaf U 1 F))
    (hV : IsZero (Hgroup X.ringCatSheaf V 1 F))
    (hadd : ∀ t : F.presheaf.obj (op (U ⊓ V)),
      ∃ (a : F.presheaf.obj (op U)) (b : F.presheaf.obj (op V)),
        F.presheaf.map (homOfLE inf_le_left).op a +
          F.presheaf.map (homOfLE inf_le_right).op b = t) :
    IsZero (Hgroup X.ringCatSheaf ⊤ 1 F) := by
  have := sectionsFunctor_additive X ⊤
  let I := injectiveResolution F
  let η : F ⟶ I.cocomplex.X 0 := I.ι.f 0
  have hη : η ≫ I.cocomplex.d 0 1 = 0 := I.ι_f_zero_comp_complex_d
  have he : (secCx X.ringCatSheaf I ⊤).ExactAt 1 := by
    apply (HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)).mpr
    apply (ShortComplex.ab_exact_iff _).mpr
    intro s hs
    change (I.cocomplex.d 1 2).val.app (op ⊤) s = 0 at hs
    have hres : ∀ W : X.Opens, (I.cocomplex.d 1 2).val.app (op W)
        ((I.cocomplex.X 1).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op s) = 0 := by
      intro W
      refine Eq.trans (hom_restrict (I.cocomplex.d 1 2) (show W ≤ ⊤ from le_top) s) ?_
      rw [hs]
      exact map_zero _
    obtain ⟨a, ha⟩ := sections_primitive_of_vanishing F I U hU
      ((I.cocomplex.X 1).presheaf.map (homOfLE le_top).op s) (hres U)
    obtain ⟨b, hb⟩ := sections_primitive_of_vanishing F I V hV
      ((I.cocomplex.X 1).presheaf.map (homOfLE le_top).op s) (hres V)
    let c := (I.cocomplex.X 0).presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op a -
      (I.cocomplex.X 0).presheaf.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op b
    have hc : (I.cocomplex.d 0 1).val.app (op (U ⊓ V)) c = 0 := by
      change (I.cocomplex.d 0 1).val.app (op (U ⊓ V))
          ((I.cocomplex.X 0).presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op a -
            (I.cocomplex.X 0).presheaf.map
              (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op b) = 0
      rw [hom_sub (I.cocomplex.d 0 1),
        hom_restrict (I.cocomplex.d 0 1) (show U ⊓ V ≤ U from inf_le_left) a,
        hom_restrict (I.cocomplex.d 0 1) (show U ⊓ V ≤ V from inf_le_right) b, ha, hb,
        restrict_restrict (I.cocomplex.X 1) (show U ⊓ V ≤ U from inf_le_left)
          (show U ≤ ⊤ from le_top) s,
        restrict_restrict (I.cocomplex.X 1) (show U ⊓ V ≤ V from inf_le_right)
          (show V ≤ ⊤ from le_top) s]
      exact sub_self _
    obtain ⟨t, ht⟩ := sections_primitive_zero F I (U ⊓ V) c hc
    change η.val.app (op (U ⊓ V)) t = c at ht
    obtain ⟨a₀, b₀, hab₀⟩ := hadd t
    let a' : (I.cocomplex.X 0).presheaf.obj (op U) :=
      a - (show (I.cocomplex.X 0).presheaf.obj (op U) from η.val.app (op U) a₀)
    let b' : (I.cocomplex.X 0).presheaf.obj (op V) :=
      b + (show (I.cocomplex.X 0).presheaf.obj (op V) from η.val.app (op V) b₀)
    have hmatch : (I.cocomplex.X 0).presheaf.map (homOfLE inf_le_left).op a' =
        (I.cocomplex.X 0).presheaf.map (homOfLE inf_le_right).op b' := by
      have h : η.val.app (op (U ⊓ V))
          (F.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op a₀ +
            F.presheaf.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op b₀) =
          η.val.app (op (U ⊓ V)) t := by rw [hab₀]
      rw [hom_add η, hom_restrict η (show U ⊓ V ≤ U from inf_le_left) a₀,
        hom_restrict η (show U ⊓ V ≤ V from inf_le_right) b₀, ht] at h
      change (I.cocomplex.X 0).presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op
          (a - (show (I.cocomplex.X 0).presheaf.obj (op U) from η.val.app (op U) a₀)) =
        (I.cocomplex.X 0).presheaf.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op
          (b + (show (I.cocomplex.X 0).presheaf.obj (op V) from η.val.app (op V) b₀))
      rw [restrict_sub (I.cocomplex.X 0) (show U ⊓ V ≤ U from inf_le_left),
        restrict_add (I.cocomplex.X 0) (show U ⊓ V ≤ V from inf_le_right)]
      dsimp only [c] at h
      apply sub_eq_iff_eq_add.mpr
      exact (sub_eq_iff_eq_add.mp h.symm).trans (by abel)
    obtain ⟨z, hzU, hzV⟩ := glue_two_sections (I.cocomplex.X 0) U V hUV a' b' hmatch
    refine ⟨z, ?_⟩
    change (I.cocomplex.d 0 1).val.app (op ⊤) z = s
    apply sections_eq_of_two_restrictions (I.cocomplex.X 1) U V hUV
    · refine Eq.trans
        (hom_restrict (I.cocomplex.d 0 1) (show U ≤ ⊤ from le_top) z).symm ?_
      rw [hzU]
      change (I.cocomplex.d 0 1).val.app (op U)
          (a - (show (I.cocomplex.X 0).presheaf.obj (op U) from η.val.app (op U) a₀)) = _
      rw [hom_sub (I.cocomplex.d 0 1), hom_comp_zero_apply _ _ hη, sub_zero, ha]
    · refine Eq.trans
        (hom_restrict (I.cocomplex.d 0 1) (show V ≤ ⊤ from le_top) z).symm ?_
      rw [hzV]
      change (I.cocomplex.d 0 1).val.app (op V)
          (b + (show (I.cocomplex.X 0).presheaf.obj (op V) from η.val.app (op V) b₀)) = _
      rw [hom_add (I.cocomplex.d 0 1), hom_comp_zero_apply _ _ hη, add_zero, hb]
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp he).of_iso
    (I.isoRightDerivedObj (secF X.ringCatSheaf ⊤) 1)

private lemma rightDerivedCompIsoOfPreservesHomology
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E] [HasInjectiveResolutions C]
    (G : C ⥤ D) [G.Additive] (T : D ⥤ E) [T.Additive] [T.PreservesHomology]
    (A : C) (n : ℕ) :
    Nonempty (((G ⋙ T).rightDerived n).obj A ≅ T.obj ((G.rightDerived n).obj A)) := by
  let I := injectiveResolution A
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  exact ⟨I.isoRightDerivedObj (G ⋙ T) n ≪≫
    (HomologicalComplex.homologyFunctor E _ n).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ T)) _).app I.cocomplex).symm ≪≫
    (K.sc n).mapHomologyIso T ≪≫
    T.mapIso (I.isoRightDerivedObj G n).symm⟩

private theorem genus_eq_zero_of_isZero_Hgroup {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ 1 (SheafOfModules.unit X.ringCatSheaf))) :
    genus f = 0 := by
  have : (moduleSpecΓFunctor (R := .of k)).Additive :=
    ⟨by intro M N φ ψ; ext x; rfl⟩
  let G := Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor
  let T := forget₂ (ModuleCat k) AddCommGrpCat
  obtain ⟨e⟩ := rightDerivedCompIsoOfPreservesHomology G T
    (SheafOfModules.unit X.ringCatSheaf) 1
  have hh : IsZero (((G ⋙ T).rightDerived 1).obj (SheafOfModules.unit X.ringCatSheaf)) := h
  have : Subsingleton (structureSheafCohomology f 1) :=
    AddCommGrpCat.subsingleton_of_isZero (hh.of_iso e.symm)
  exact Module.finrank_zero_of_subsingleton

private theorem pinchedStructureMorphism_genus :
    genus (pinchedStructureMorphism k K).val = 0 := by
  have : (SheafOfModules.unit (pinchedCurve k K).ringCatSheaf).IsQuasicoherent := inferInstance
  let i := pinchedChartA k K
  let j := pinchedChartB k K
  let U := i ''ᵁ ⊤
  let V := j ''ᵁ ⊤
  have hU : IsAffineOpen U := by simpa [U] using isAffineOpen_opensRange i
  have hV : IsAffineOpen V := by simpa [V] using isAffineOpen_opensRange j
  have hUV : U ⊔ V = ⊤ := by
    apply top_unique
    intro z _
    have hz : z ∈ Set.range i.base ∪ Set.range j.base :=
      Set.eq_univ_iff_forall.mp (pinchedCharts_cover k K) z
    simpa [U, V] using hz
  apply genus_eq_zero_of_isZero_Hgroup
  apply cohomology_one_vanishes_of_two_opens
    (SheafOfModules.unit (pinchedCurve k K).ringCatSheaf) U V hUV
  · exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen _ _ U hU 1 (by decide)
  · exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen _ _ V hV 1 (by decide)
  · have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (pinchedToLaurent k K))) :=
      isOpenImmersion_pinchedPuncturedChart k K
    have h : IsPullback (Spec.map (CommRingCat.ofHom (pinchedToLaurent k K)))
        (Spec.map (CommRingCat.ofHom (pinchedFromSecondChart K))) i j := by
      rw [pinchedFromSecondChart_spec]
      exact pinchedCharts_isPullback k K
    change ∀ t : Γ(pinchedCurve k K, U ⊓ V), ∃ a b,
      (pinchedCurve k K).presheaf.map (homOfLE inf_le_left).op a +
        (pinchedCurve k K).presheaf.map (homOfLE inf_le_right).op b = t
    refine sections_decomposition_of_affineCharts i j _ _ h fun t => ?_
    obtain ⟨a, b, hab⟩ := exists_pinched_add_invert_eq k K t
    exact ⟨a, b, hab.symm⟩

end

/-- **Stacks Project, Tag 0DJC.** For a nontrivial finite extension `K/k`, the pinched
projective line over `k`: a scheme with the prescribed affine gluing of `Spec A` to `Spec K[Y]`
along `Spec K[T, T⁻¹]`, with a single singular closed point at the contracted origin, with `k`
for its global functions, which is a proper curve of genus zero over `k`, and whose canonical
normalization is `ℙ¹_K`. -/
@[stacks 0DJC]
theorem exists_pinchedProjectiveLine [Module.Finite k K]
    (hK : 1 < Module.finrank k K) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
      (iA : Spec (.of (pinchedPolynomialRing k K)) ⟶ X)
      (iB : Spec (.of (Polynomial K)) ⟶ X)
      (ν : projectiveLine K ⟶ X)
      (xA : Spec (.of (pinchedPolynomialRing k K))),
      IsOpenImmersion iA ∧
      IsOpenImmersion iB ∧
      (iA ≫ f = Spec.map (CommRingCat.ofHom (pinchedPolynomialConstant k K))) ∧
      (iB ≫ f = Spec.map (CommRingCat.ofHom
        ((Polynomial.C : K →+* Polynomial K).comp (algebraMap k K)))) ∧
      (Set.range iA.base ∪ Set.range iB.base = Set.univ) ∧
      (let pA := pinchedPuncturedChart k K
       let pB := (projectiveLineInversionIso K).hom ≫
         projectiveLinePuncturedChart K
       ∃ (hglue : pA ≫ iA = pB ≫ iB),
         IsIso (pullback.lift pA pB hglue)) ∧
      (xA.asIdeal = (Ideal.span {(Polynomial.X : Polynomial K)}).comap
        (Subring.subtype (pinchedPolynomialRing k K))) ∧
      (singularLocus X = {iA.base xA}) ∧
      IsCurve k f ∧
      IsProper f ∧
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ∧
      genus f = 0 ∧
      (projectiveLineXChart K ≫ ν =
        pinchedNormalizationAffineChart k K ≫ iA) ∧
      (projectiveLineYChart K ≫ ν = iB) ∧
      (∃ hX : ∀ U : X.Opens, IsCompact (U : Set X) →
          (irreducibleComponents U).Finite,
        ∃ e : projectiveLine K ≅
          Scheme.normalizationScheme X hX,
          ν = e.hom ≫ Scheme.normalization X hX) := by
  suffices h :
      singularLocus (pinchedCurve k K) =
          {(pinchedChartA k K).base (pinchedOrigin k K)} ∧
      IsProper (pinchedStructureMorphism k K).val ∧
      genus (pinchedStructureMorphism k K).val = 0 ∧
      (∃ hX : ∀ U : (pinchedCurve k K).Opens, IsCompact (U : Set (pinchedCurve k K)) →
          (irreducibleComponents U).Finite,
        ∃ e : projectiveLine K ≅
          Scheme.normalizationScheme (pinchedCurve k K) hX,
          (pinchedNormalizationMorphism k K).val =
            e.hom ≫ Scheme.normalization (pinchedCurve k K) hX) by
    obtain ⟨hsing, hproper, hgenus, hnorm⟩ := h
    have hcurve : IsCurve k (pinchedStructureMorphism k K).val := {
      toIsVariety := {
        toIsIntegral := inferInstance
        toIsSeparated := inferInstance
        toLocallyOfFiniteType := inferInstance
        toQuasiCompact := inferInstance }
      topologicalKrullDim_eq_one := pinchedCurve_dimension k K }
    exact ⟨pinchedCurve k K, (pinchedStructureMorphism k K).val,
      pinchedChartA k K, pinchedChartB k K, (pinchedNormalizationMorphism k K).val,
      pinchedOrigin k K, inferInstance, inferInstance,
      (pinchedStructureMorphism k K).property.1,
      (pinchedStructureMorphism k K).property.2,
      pinchedCharts_cover k K,
      ⟨pinchedCharts_glue k K, pinchedCharts_lift_isIso k K⟩,
      pinchedOrigin_asIdeal k K, hsing, hcurve, hproper,
      pinchedStructureMorphism_globalSections k K, hgenus,
      (pinchedNormalizationMorphism k K).property.1,
      (pinchedNormalizationMorphism k K).property.2, hnorm⟩
  exact ⟨pinchedCurve_singularLocus k K hK, pinchedStructureMorphism_isProper k K,
    pinchedStructureMorphism_genus k K,
    fun U _ => pinchedCurve_finiteIrreducibleComponents k K U,
    pinchedNormalizationMorphism_normalization k K⟩

end AlgebraicGeometry

end
