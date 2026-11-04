module

public import StacksFrontier.AlgebraicGeometry.Curves.PinchedProjectiveLine.Basic.Construction
import all StacksFrontier.AlgebraicGeometry.Curves.PinchedProjectiveLine.Basic.Construction
import all StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSections

/-!
# The pinched projective line: geometric properties

Integrality, quasi-compactness, finite type and dimension one of the pinched projective line,
its global functions, separatedness and properness of its structure morphism, and its singular
locus. All declarations are private; they are used by
`AlgebraicGeometry.exists_pinchedProjectiveLine`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

attribute [local instance] isZariskiLocalAtSource_locallyOfFiniteType

attribute [local instance] isZariskiLocalAtSource_locallyQuasiFinite

private lemma isIrreducible_union_of_isOpen {T : Type*} [TopologicalSpace T]
    {s t : Set T} (hs : IsIrreducible s) (ht : IsIrreducible t)
    (hsopen : IsOpen s) (_htopen : IsOpen t) (hst : (s ∩ t).Nonempty) :
    IsIrreducible (s ∪ t) := by
  refine ⟨hs.nonempty.mono Set.subset_union_left, ?_⟩
  intro U V hU hV hUmeet hVmeet
  have hmeet : ∀ W : Set T, IsOpen W → ((s ∪ t) ∩ W).Nonempty →
      (s ∩ W).Nonempty := by
    intro W hW hmeet
    obtain ⟨x, hx, hxW⟩ := hmeet
    rcases hx with hx | hx
    · exact ⟨x, hx, hxW⟩
    · obtain ⟨y, hyt, hys, hyW⟩ :=
        ht.isPreirreducible s W hsopen hW (by simpa only [Set.inter_comm] using hst) ⟨x, hx, hxW⟩
      exact ⟨y, hys, hyW⟩
  exact (hs.isPreirreducible U V hU hV (hmeet U hU hUmeet)
    (hmeet V hV hVmeet)).mono (Set.inter_subset_inter_left _ Set.subset_union_left)

private theorem pinchedChartA_isOpenImmersion : IsOpenImmersion (pinchedChartA k K) :=
  (pinchedGluingData k K).ι_isOpenImmersion pinchedIndexA

attribute [local instance] pinchedChartA_isOpenImmersion

private theorem pinchedChartB_isOpenImmersion : IsOpenImmersion (pinchedChartB k K) :=
  (pinchedGluingData k K).ι_isOpenImmersion pinchedIndexB

attribute [local instance] pinchedChartB_isOpenImmersion

private theorem pinchedCurve_isIntegral : IsIntegral (pinchedCurve k K) := by
  let D := pinchedGluingData k K
  have : ∀ i : D.openCover.I₀, IsReduced (D.openCover.X i) := by
    change ∀ i : D.J, IsReduced (D.U i)
    rintro ⟨i⟩
    cases i <;> dsimp [D, pinchedGluingData, CategoryTheory.GlueData.ofGlueData',
      pinchedGluingData'] <;> infer_instance
  have : IsReduced (pinchedCurve k K) := IsReduced.of_openCover _ D.openCover
  have hA : IsIrreducible (Set.range (pinchedChartA k K).base) := by
    simpa only [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ
      (Spec (.of (pinchedPolynomialRing k K)))).image
      (pinchedChartA k K).base (pinchedChartA k K).continuous.continuousOn
  have hB : IsIrreducible (Set.range (pinchedChartB k K).base) := by
    simpa only [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ
      (Spec (.of (Polynomial K)))).image
      (pinchedChartB k K).base (pinchedChartB k K).continuous.continuousOn
  have hmeet : (Set.range (pinchedChartA k K).base ∩
      Set.range (pinchedChartB k K).base).Nonempty := by
    let z : Spec (.of (LaurentPolynomial K)) := ⟨⊥, inferInstance⟩
    refine ⟨(pinchedChartA k K) (pinchedPuncturedChart k K z),
      ⟨pinchedPuncturedChart k K z, rfl⟩,
      ((projectiveLineInversionIso K).hom ≫ projectiveLinePuncturedChart K) z, ?_⟩
    exact congrArg (fun f => (f : Spec (.of (LaurentPolynomial K)) ⟶ pinchedCurve k K) z)
      (pinchedCharts_glue k K).symm
  have hirr := isIrreducible_union_of_isOpen hA hB
    (pinchedChartA k K).isOpenEmbedding.isOpen_range
    (pinchedChartB k K).isOpenEmbedding.isOpen_range hmeet
  rw [pinchedCharts_cover] at hirr
  have : IrreducibleSpace (pinchedCurve k K) := (irreducibleSpace_def _).mpr hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

attribute [local instance] pinchedCurve_isIntegral

private theorem pinchedCurve_compactSpace : CompactSpace (pinchedCurve k K) := by
  let D := pinchedGluingData k K
  have : Finite D.openCover.I₀ := inferInstanceAs (Finite (ULift Bool))
  have : ∀ i : D.openCover.I₀, CompactSpace (D.openCover.X i) := by
    change ∀ i : D.J, CompactSpace (D.U i)
    rintro ⟨i⟩
    cases i
    · exact inferInstanceAs (CompactSpace (Spec (.of (pinchedPolynomialRing k K))))
    · exact inferInstanceAs (CompactSpace (Spec (.of (Polynomial K))))
  exact D.openCover.compactSpace

attribute [local instance] pinchedCurve_compactSpace

private theorem pinchedStructureMorphism_locallyOfFiniteType [Module.Finite k K] :
    LocallyOfFiniteType (pinchedStructureMorphism k K).val := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (pinchedGluingData k K).openCover
  rintro ⟨i⟩
  cases i
  · change LocallyOfFiniteType (pinchedChartA k K ≫ _)
    rw [(pinchedStructureMorphism k K).property.1]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  · change LocallyOfFiniteType (pinchedChartB k K ≫ _)
    rw [(pinchedStructureMorphism k K).property.2]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)

attribute [local instance] pinchedStructureMorphism_locallyOfFiniteType

private theorem pinchedCurve_finiteIrreducibleComponents [Module.Finite k K]
    (U : (pinchedCurve k K).Opens) : (irreducibleComponents U).Finite := by
  classical
  cases isEmpty_or_nonempty U with
  | inl hU =>
    have : IsEmpty (irreducibleComponents U) :=
      ⟨fun C => isEmptyElim C.2.1.nonempty.some⟩
    exact Set.toFinite _
  | inr hU =>
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _

private theorem topologicalKrullDim_le_of_openCover {Y : Scheme.{u}}
    (𝒰 : Y.OpenCover) (d : WithBot ℕ∞)
    (h : ∀ i, topologicalKrullDim (𝒰.X i) ≤ d) : topologicalKrullDim Y ≤ d := by
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  refine iSup_le fun y => ?_
  obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq y
  change ringKrullDim (Y.presheaf.stalk ((𝒰.f i) x)) ≤ d
  rw [(asIso ((𝒰.f i).stalkMap x)).commRingCatIsoToRingEquiv.ringKrullDim]
  exact (le_iSup (fun x : 𝒰.X i => ringKrullDim ((𝒰.X i).presheaf.stalk x)) x).trans
    ((topologicalKrullDim_eq_iSup_krullDimOfRing_stalk
      (𝒰.X i)).symm.le.trans (h i))

private theorem pinchedCurve_dimension [Module.Finite k K] :
    topologicalKrullDim (pinchedCurve k K) = 1 := by
  apply le_antisymm
  · apply topologicalKrullDim_le_of_openCover (pinchedGluingData k K).openCover
    rintro ⟨i⟩
    cases i
    · exact (topologicalKrullDim_spec_pinchedPolynomialRing k K).le
    · exact (topologicalKrullDim_spec_polynomial K).le
  · rw [← topologicalKrullDim_spec_polynomial K]
    exact (pinchedChartB k K).isOpenEmbedding.isInducing.topologicalKrullDim_le

private lemma gammaSpec_map_apply {R S : CommRingCat.{u}} (a : R ⟶ S)
    (s : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso S).hom ((Spec.map a).appTop s) =
      a ((Scheme.ΓSpecIso R).hom s) :=
  congrArg (fun g : Γ(Spec R, ⊤) ⟶ S => g.hom s)
    (Scheme.ΓSpecIso_naturality a)

private lemma constants_eval_chart {R : Type u} [CommRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) (i : Spec (.of R) ⟶ Y)
    (a : k →+* R) (hi : i ≫ f = Spec.map (CommRingCat.ofHom a)) (c : k) :
    (Scheme.ΓSpecIso (.of R)).hom
      (i.appTop (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) c)) = a c := by
  have he : ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫ i.appTop =
      CommRingCat.ofHom a ≫ (Scheme.ΓSpecIso (.of R)).inv := by
    simp [Category.assoc, ← Scheme.Hom.comp_appTop, hi,
      Scheme.ΓSpecIso_inv_naturality]
  have hv := congrArg (fun g : CommRingCat.of k ⟶ Γ(Spec (.of R), ⊤) => g.hom c) he
  change (Scheme.ΓSpecIso (.of R)).hom
    ((((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫ i.appTop) c) = _
  rw [hv]
  exact (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.apply_symm_apply (a c)

private theorem pinchedStructureMorphism_globalSections :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (pinchedStructureMorphism k K).val.appTop) := by
  let F := (Scheme.ΓSpecIso (.of k)).inv ≫ (pinchedStructureMorphism k K).val.appTop
  let ν := (pinchedNormalizationMorphism k K).val
  let P := projectiveLine K
  let G := (Scheme.ΓSpecIso (.of K)).inv ≫ (P ↘ Spec (.of K)).appTop
  have : IsIso G :=
    isIso_constantsToGlobalSections K
  have hAeval := constants_eval_chart k (pinchedStructureMorphism k K).val
    (pinchedChartA k K) (pinchedPolynomialConstant k K)
    (pinchedStructureMorphism k K).property.1
  have hBeval := constants_eval_chart k (pinchedStructureMorphism k K).val
    (pinchedChartB k K) ((Polynomial.C : K →+* Polynomial K).comp (algebraMap k K))
    (pinchedStructureMorphism k K).property.2
  change IsIso F
  apply (ConcreteCategory.isIso_iff_bijective F).mpr
  refine ⟨?_, ?_⟩
  · intro a b hab
    have he := congrArg (fun s => (Scheme.ΓSpecIso (.of (pinchedPolynomialRing k K))).hom
      ((pinchedChartA k K).appTop s)) hab
    rw [hAeval, hAeval] at he
    exact (pinchedPolynomialConstant k K).injective he
  · intro s
    obtain ⟨c, hc⟩ := ((ConcreteCategory.isIso_iff_bijective G).mp inferInstance).2
      (ν.appTop s)
    have hx := constants_eval_chart K (P ↘ Spec (.of K))
      (projectiveLineXChart K) Polynomial.C (projectiveLineXChart_comp_structureMorphism K) c
    have hy := constants_eval_chart K (P ↘ Spec (.of K))
      (projectiveLineYChart K) Polynomial.C (projectiveLineYChart_comp_structureMorphism K) c
    rw [hc] at hx hy
    have hA : ((Scheme.ΓSpecIso (.of (pinchedPolynomialRing k K))).hom
        ((pinchedChartA k K).appTop s)).val = Polynomial.C c := by
      have hcomp := congrArg (fun g : Spec (.of (Polynomial K)) ⟶ pinchedCurve k K =>
        (Scheme.ΓSpecIso (.of (Polynomial K))).hom (g.appTop s))
        (pinchedNormalizationMorphism k K).property.1
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hcomp
      rw [hx] at hcomp
      exact (gammaSpec_map_apply
        (CommRingCat.ofHom (Subring.subtype (pinchedPolynomialRing k K)))
        ((pinchedChartA k K).appTop s)).symm.trans hcomp.symm
    have hB : (Scheme.ΓSpecIso (.of (Polynomial K))).hom
        ((pinchedChartB k K).appTop s) = Polynomial.C c :=
      (congrArg (fun g : Spec (.of (Polynomial K)) ⟶ pinchedCurve k K =>
        (Scheme.ΓSpecIso (.of (Polynomial K))).hom (g.appTop s))
        (pinchedNormalizationMorphism k K).property.2).symm.trans hy
    have hcK : c ∈ (algebraMap k K).range := by
      have hm := ((Scheme.ΓSpecIso (.of (pinchedPolynomialRing k K))).hom
        ((pinchedChartA k K).appTop s)).property
      change Polynomial.evalRingHom (0 : K) _ ∈ (algebraMap k K).range at hm
      rw [hA] at hm
      simpa using hm
    obtain ⟨d, hd⟩ := hcK
    refine ⟨d, ?_⟩
    apply (pinchedGluingData k K).openCover.ext_elem
    rintro ⟨i⟩
    cases i
    · change (pinchedChartA k K).appTop (F d) = (pinchedChartA k K).appTop s
      apply (Scheme.ΓSpecIso (.of (pinchedPolynomialRing k K))).commRingCatIsoToRingEquiv.injective
      apply Subtype.ext
      change ((Scheme.ΓSpecIso (.of (pinchedPolynomialRing k K))).hom
        ((pinchedChartA k K).appTop (F d))).val =
        ((Scheme.ΓSpecIso (.of (pinchedPolynomialRing k K))).hom
          ((pinchedChartA k K).appTop s)).val
      dsimp only [F]
      rw [hAeval, hA]
      exact congrArg Polynomial.C hd
    · change (pinchedChartB k K).appTop (F d) = (pinchedChartB k K).appTop s
      apply (Scheme.ΓSpecIso (.of (Polynomial K))).commRingCatIsoToRingEquiv.injective
      change (Scheme.ΓSpecIso (.of (Polynomial K))).hom
        ((pinchedChartB k K).appTop (F d)) =
        (Scheme.ΓSpecIso (.of (Polynomial K))).hom ((pinchedChartB k K).appTop s)
      dsimp only [F]
      rw [hBeval, hB]
      exact congrArg Polynomial.C hd

private theorem openChart_restriction {A C Y : Scheme.{u}}
    (i : A ⟶ Y) (j : C ⟶ Y) (p : C ⟶ A)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (h : j = p ≫ i) (hle : j ''ᵁ ⊤ ≤ i ''ᵁ ⊤) :
    Y.presheaf.map (homOfLE hle).op ≫ (j.appIso ⊤).hom =
      (i.appIso ⊤).hom ≫ p.appTop := by
  simp only [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  rw [show p.appTop = p.appLE ⊤ ⊤ (by simp) by simp [Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]]
  subst j
  exact (p.appLE_comp_appLE i _ ⊤ ⊤ _ _).symm

private theorem openChart_intersection {A B C Y : Scheme.{u}}
    (i : A ⟶ Y) (j : B ⟶ Y) (p : C ⟶ A) (q : C ⟶ B)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion p]
    (h : IsPullback p q i j) :
    (p ≫ i) ''ᵁ ⊤ = (i ''ᵁ ⊤) ⊓ (j ''ᵁ ⊤) := by
  simp only [Scheme.Hom.image_top_eq_opensRange]
  apply TopologicalSpace.Opens.ext
  change Set.range (p ≫ i) = Set.range i ∩ Set.range j
  rw [← IsOpenImmersion.range_pullback_to_base_of_left i j]
  have he : p ≫ i = h.isoPullback.hom ≫ pullback.fst i j ≫ i := by simp
  rw [he, Scheme.Hom.comp_base]
  change Set.range ((pullback.fst i j ≫ i) ∘ h.isoPullback.hom) = _
  rw [Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]

private theorem sections_decomposition_of_affineCharts
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] {Y : Scheme.{u}}
    (i : Spec (.of A) ⟶ Y) (j : Spec (.of B) ⟶ Y)
    (p : A →+* C) (q : B →+* C)
    [IsOpenImmersion i] [IsOpenImmersion j]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom p))]
    (h : IsPullback (Spec.map (CommRingCat.ofHom p))
      (Spec.map (CommRingCat.ofHom q)) i j)
    (hadd : ∀ c : C, ∃ a b, p a + q b = c)
    (s : Γ(Y, (i ''ᵁ ⊤) ⊓ (j ''ᵁ ⊤))) :
    ∃ (a : Γ(Y, i ''ᵁ ⊤)) (b : Γ(Y, j ''ᵁ ⊤)),
      Y.presheaf.map (homOfLE inf_le_left).op a +
        Y.presheaf.map (homOfLE inf_le_right).op b = s := by
  let v := Spec.map (CommRingCat.ofHom p) ≫ i
  have hv : v = Spec.map (CommRingCat.ofHom q) ≫ j := h.w
  have hW : v ''ᵁ ⊤ = (i ''ᵁ ⊤) ⊓ (j ''ᵁ ⊤) := openChart_intersection i j _ _ h
  let eA : Γ(Y, i ''ᵁ ⊤) ≅ CommRingCat.of A := i.appIso ⊤ ≪≫ Scheme.ΓSpecIso (.of A)
  let eB : Γ(Y, j ''ᵁ ⊤) ≅ CommRingCat.of B := j.appIso ⊤ ≪≫ Scheme.ΓSpecIso (.of B)
  let eC : Γ(Y, (i ''ᵁ ⊤) ⊓ (j ''ᵁ ⊤)) ≅ CommRingCat.of C :=
    Y.presheaf.mapIso (eqToIso hW).op ≪≫ v.appIso ⊤ ≪≫ Scheme.ΓSpecIso (.of C)
  have hresA : Y.presheaf.map (homOfLE inf_le_left).op ≫ eC.hom =
      eA.hom ≫ CommRingCat.ofHom p := by
    dsimp only [eC, eA, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← Y.presheaf.map_comp]
    change Y.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op ≫ _ = _
    rw [← Category.assoc, openChart_restriction i v _ rfl]
    simp only [Category.assoc, Scheme.ΓSpecIso_naturality]
  have hresB : Y.presheaf.map (homOfLE inf_le_right).op ≫ eC.hom =
      eB.hom ≫ CommRingCat.ofHom q := by
    dsimp only [eC, eB, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← Y.presheaf.map_comp]
    change Y.presheaf.map (homOfLE (hW.le.trans inf_le_right)).op ≫ _ = _
    rw [← Category.assoc, openChart_restriction j v _ hv]
    simp only [Category.assoc, Scheme.ΓSpecIso_naturality]
  obtain ⟨a, b, hab⟩ := hadd (eC.hom s)
  refine ⟨eA.inv a, eB.inv b, ?_⟩
  apply eC.commRingCatIsoToRingEquiv.injective
  change eC.hom (_ + _) = _
  rw [map_add]
  have ha := congrArg (fun f : Γ(Y, i ''ᵁ ⊤) ⟶ CommRingCat.of C => f (eA.inv a)) hresA
  have hb := congrArg (fun f : Γ(Y, j ''ᵁ ⊤) ⟶ CommRingCat.of C => f (eB.inv b)) hresB
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at ha hb
  rwa [ha, hb]

open scoped TensorProduct in
private theorem sectionTensorMap_surjective_of_add
    {Y : Scheme.{u}} (U V : Y.Opens)
    (h : ∀ s : Γ(Y, U ⊓ V), ∃ (a : Γ(Y, U)) (b : Γ(Y, V)),
      Y.presheaf.map (homOfLE inf_le_left).op a +
        Y.presheaf.map (homOfLE inf_le_right).op b = s) :
    Function.Surjective (sectionTensorMap Y U V) := by
  intro s
  obtain ⟨a, b, hs⟩ := h s
  refine ⟨a ⊗ₜ[ℤ] 1 + 1 ⊗ₜ[ℤ] b, ?_⟩
  simpa [sectionTensorMap] using hs

open scoped TensorProduct in
private theorem sectionTensorMap_surjective_self {Y : Scheme.{u}} (U : Y.Opens) :
    Function.Surjective (sectionTensorMap Y U U) := by
  intro s
  refine ⟨(Y.presheaf.map (eqToHom (congrArg Opposite.op (inf_idem U)) ) s) ⊗ₜ[ℤ] 1, ?_⟩
  simp [sectionTensorMap, ← CommRingCat.comp_apply, ← Functor.map_comp]

private def pinchedFromSecondChart : Polynomial K →+* LaurentPolynomial K :=
  LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent

private theorem pinchedFromSecondChart_spec :
    Spec.map (CommRingCat.ofHom (pinchedFromSecondChart K)) =
      (projectiveLineInversionIso K).hom ≫
        projectiveLinePuncturedChart K := by
  change Spec.map (CommRingCat.ofHom (pinchedFromSecondChart K)) =
    Spec.map (CommRingCat.ofHom LaurentPolynomial.invert.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom Polynomial.toLaurent)
  rw [← Spec.map_comp]
  rfl

private theorem pinchedStructureMorphism_isSeparated :
    IsSeparated (pinchedStructureMorphism k K).val := by
  let i := pinchedChartA k K
  let j := pinchedChartB k K
  let U := i ''ᵁ ⊤
  let V := j ''ᵁ ⊤
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (pinchedToLaurent k K))) :=
    isOpenImmersion_pinchedPuncturedChart k K
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (pinchedFromSecondChart K))) := by
    rw [pinchedFromSecondChart_spec]
    infer_instance
  have h : IsPullback (Spec.map (CommRingCat.ofHom (pinchedToLaurent k K)))
      (Spec.map (CommRingCat.ofHom (pinchedFromSecondChart K))) i j := by
    rw [pinchedFromSecondChart_spec]
    exact pinchedCharts_isPullback k K
  have hU : IsAffineOpen U := by simpa [U] using isAffineOpen_opensRange i
  have hV : IsAffineOpen V := by simpa [V] using isAffineOpen_opensRange j
  have hUV : IsAffineOpen (U ⊓ V) := by
    rw [← openChart_intersection i j _ _ h]
    simpa only [Scheme.Hom.image_top_eq_opensRange] using isAffineOpen_opensRange
      (Spec.map (CommRingCat.ofHom (pinchedToLaurent k K)) ≫ i)
  have hsurj : Function.Surjective (sectionTensorMap (pinchedCurve k K) U V) :=
    sectionTensorMap_surjective_of_add U V <|
      sections_decomposition_of_affineCharts i j _ _ h fun c => by
        obtain ⟨a, b, hab⟩ := exists_pinched_add_invert_eq k K c
        exact ⟨a, b, hab.symm⟩
  have hsurj' : Function.Surjective (sectionTensorMap (pinchedCurve k K) V U) :=
    sectionTensorMap_surjective_of_add V U <|
      sections_decomposition_of_affineCharts j i _ _ h.flip fun c => by
        obtain ⟨a, b, hab⟩ := exists_pinched_add_invert_eq k K c
        exact ⟨b, a, (add_comm _ _).trans hab.symm⟩
  apply isSeparated_of_affine_intersections
  intro x y _
  have hcover : ∀ z : pinchedCurve k K, z ∈ U ∨ z ∈ V := by
    intro z
    have hz : z ∈ Set.range i.base ∪ Set.range j.base :=
      Set.eq_univ_iff_forall.mp (pinchedCharts_cover k K) z
    simpa [U, V] using hz
  rcases hcover x with hx | hx <;> rcases hcover y with hy | hy
  · refine ⟨U, U, ⊤, hx, hy, hU, hU, isAffineOpen_top _, by simp, by simp, ?_, ?_⟩
    · simpa using hU
    · exact sectionTensorMap_surjective_self U
  · exact ⟨U, V, ⊤, hx, hy, hU, hV, isAffineOpen_top _, by simp, by simp, hUV, hsurj⟩
  · exact ⟨V, U, ⊤, hx, hy, hV, hU, isAffineOpen_top _, by simp, by simp,
      by simpa only [inf_comm] using hUV, hsurj'⟩
  · refine ⟨V, V, ⊤, hx, hy, hV, hV, isAffineOpen_top _, by simp, by simp, ?_, ?_⟩
    · simpa using hV
    · exact sectionTensorMap_surjective_self V

attribute [local instance] pinchedStructureMorphism_isSeparated

private theorem valuation_exists_preimage_or_inverse
    {R L : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field L] [Algebra R L] [IsFractionRing R L] (t : L) :
    (∃ r : R, algebraMap R L r = t) ∨ (∃ r : R, algebraMap R L r = t⁻¹) := by
  rcases (ValuationRing.valuation R L).val_le_one_or_val_inv_le_one t with h | h
  · exact Or.inl ((ValuationRing.mem_integer_iff R L t).mp h)
  · exact Or.inr ((ValuationRing.mem_integer_iff R L t⁻¹).mp h)

private theorem polynomial_valuativeExtension {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of K)) (a b : Spec (.of (Polynomial K)) ⟶ Y)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom Polynomial.C))
    (hb : b ≫ f = Spec.map (CommRingCat.ofHom Polynomial.C))
    (hab : Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := K))) ≫ a =
      Spec.map (CommRingCat.ofHom (pinchedFromSecondChart K)) ≫ b)
    {R L : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (c : K →+* R) (φ : Polynomial K →+* L)
    (hc : φ.comp Polynomial.C = (algebraMap R L).comp c) :
    ∃ g : Spec (.of R) ⟶ Y,
      Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ g =
        Spec.map (CommRingCat.ofHom φ) ≫ a ∧
      g ≫ f = Spec.map (CommRingCat.ofHom c) := by
  let η := algebraMap R L
  by_cases ht : ∃ r : R, η r = φ Polynomial.X
  · obtain ⟨r, hr⟩ := ht
    let ψ := Polynomial.eval₂RingHom c r
    have hψ : η.comp ψ = φ := by
      apply Polynomial.ringHom_ext
      · intro x
        simpa [ψ, η] using (congrArg (fun h : K →+* L => h x) hc).symm
      · simpa [ψ] using hr
    refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ a, ?_, ?_⟩
    · rw [← Spec.map_comp_assoc]
      change Spec.map (CommRingCat.ofHom (η.comp ψ)) ≫ a = _
      rw [hψ]
    · rw [Category.assoc, ha, ← Spec.map_comp]
      congr 1
      ext x
      simp [ψ]
  · have ht0 : φ Polynomial.X ≠ 0 := fun h => ht ⟨0, by simp [h]⟩
    obtain ⟨r, hr⟩ := (valuation_exists_preimage_or_inverse (φ Polynomial.X)).resolve_left ht
    let φL : LaurentPolynomial K →+* L :=
      IsLocalization.Away.lift Polynomial.X (isUnit_iff_ne_zero.mpr ht0)
    have hφL (p : Polynomial K) : φL (Polynomial.toLaurent p) = φ p :=
      IsLocalization.Away.lift_eq _ _ p
    have hφLX : φL (LaurentPolynomial.T 1) = φ Polynomial.X := by
      simpa using hφL Polynomial.X
    have hφLC (x : K) : φL (LaurentPolynomial.C x) = η (c x) := by
      rw [← Polynomial.toLaurent_C, hφL]
      exact congrArg (fun h : K →+* L => h x) hc
    have hφLinv : φL (LaurentPolynomial.T (-1)) = (φ Polynomial.X)⁻¹ := by
      apply mul_left_cancel₀ ht0
      rw [mul_inv_cancel₀ ht0, ← hφLX, ← map_mul, ← LaurentPolynomial.T_add]
      norm_num
    let ψ := Polynomial.eval₂RingHom c r
    have hψ : η.comp ψ = φL.comp (pinchedFromSecondChart K) := by
      apply Polynomial.ringHom_ext
      · intro x
        simpa [ψ, pinchedFromSecondChart] using (hφLC x).symm
      · simpa [ψ, pinchedFromSecondChart, hφLinv] using hr
    refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ b, ?_, ?_⟩
    · calc
        Spec.map (CommRingCat.ofHom η) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ b =
            Spec.map (CommRingCat.ofHom (η.comp ψ)) ≫ b := by rw [← Spec.map_comp_assoc]; rfl
        _ = Spec.map (CommRingCat.ofHom φL) ≫
            Spec.map (CommRingCat.ofHom (pinchedFromSecondChart K)) ≫ b := by
          rw [hψ, ← Spec.map_comp_assoc]; rfl
        _ = Spec.map (CommRingCat.ofHom φL) ≫
            Spec.map (CommRingCat.ofHom Polynomial.toLaurent) ≫ a := by rw [hab]
        _ = Spec.map (CommRingCat.ofHom φ) ≫ a := by
          rw [← Spec.map_comp_assoc]
          congr 1
          exact Spec.map_inj.mpr (CommRingCat.hom_ext (RingHom.ext hφL))
    · rw [Category.assoc, hb, ← Spec.map_comp]
      congr 1
      ext x
      simp [ψ]

private theorem projectiveCharts_glue_symm :
    projectiveLinePuncturedChart K ≫
        projectiveLineYChart K =
      (projectiveLineInversionIso K).hom ≫
        projectiveLinePuncturedChart K ≫
          projectiveLineXChart K := by
  rw [← projectiveLineInversion_comp_charts, ← Category.assoc,
    ← Category.assoc, show (projectiveLineInversionIso K).hom ≫
      (projectiveLineInversionIso K).hom = 𝟙 _ from (projectiveLineInversionIso K).inv_hom_id]
  simp

private theorem pinchedNormalizationMorphism_surjective [Module.Finite k K] :
    Surjective (pinchedNormalizationMorphism k K).val := by
  refine ⟨fun x => ?_⟩
  have hx : x ∈ Set.range (pinchedChartA k K).base ∪ Set.range (pinchedChartB k K).base :=
    Set.eq_univ_iff_forall.mp (pinchedCharts_cover k K) x
  rcases hx with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · obtain ⟨p, rfl⟩ := (pinchedNormalizationAffineChart k K).surjective q
    exact ⟨projectiveLineXChart K p,
      congrArg (fun f : Spec (.of (Polynomial K)) ⟶ pinchedCurve k K => f p)
        (pinchedNormalizationMorphism k K).property.1⟩
  · exact ⟨projectiveLineYChart K q,
      congrArg (fun f : Spec (.of (Polynomial K)) ⟶ pinchedCurve k K => f q)
        (pinchedNormalizationMorphism k K).property.2⟩

attribute [local instance] pinchedNormalizationMorphism_surjective

private theorem pinchedNormalizationMorphism_comp :
    (pinchedNormalizationMorphism k K).val ≫ (pinchedStructureMorphism k K).val =
      (projectiveLine K ↘ Spec (.of K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  apply Multicoequalizer.hom_ext
    (I := (projectiveLineGluingData K).toGlueData.diagram)
  rintro ⟨i⟩
  cases i
  · change projectiveLineXChart K ≫ _ =
      projectiveLineXChart K ≫ _
    rw [← Category.assoc, (pinchedNormalizationMorphism k K).property.1,
      Category.assoc, (pinchedStructureMorphism k K).property.1,
      ← Category.assoc,
      projectiveLineXChart_comp_structureMorphism]
    simp only [pinchedNormalizationAffineChart, ← Spec.map_comp]
    rfl
  · change projectiveLineYChart K ≫ _ =
      projectiveLineYChart K ≫ _
    rw [← Category.assoc, (pinchedNormalizationMorphism k K).property.2,
      (pinchedStructureMorphism k K).property.2, ← Category.assoc,
      projectiveLineYChart_comp_structureMorphism,
      ← Spec.map_comp]
    rfl

private theorem fieldMorphism_factors_chart {L : Type u} [Field L]
    {Y Z : Scheme.{u}} (f : Spec (.of L) ⟶ Y) (i : Z ⟶ Y) [IsOpenImmersion i]
    (h : f (IsLocalRing.closedPoint L) ∈ Set.range i) :
    ∃ g : Spec (.of L) ⟶ Z, g ≫ i = f := by
  have hsub : Set.range f ⊆ Set.range i := by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    simpa only [hx] using h
  exact ⟨IsOpenImmersion.lift i f hsub, IsOpenImmersion.lift_fac i f hsub⟩

private theorem projectiveLine_compactSpace :
    CompactSpace (projectiveLine K) := by
  let D := projectiveLineGluingData K
  have : Finite D.openCover.I₀ := inferInstanceAs (Finite (ULift Bool))
  have : ∀ i : D.openCover.I₀, CompactSpace (D.openCover.X i) := by
    change ∀ i : D.J, CompactSpace (D.U i)
    rintro ⟨i⟩
    cases i <;> exact inferInstanceAs (CompactSpace (Spec (.of (Polynomial K))))
  exact D.openCover.compactSpace

private theorem pinchedStructureMorphism_isProper [Module.Finite k K] :
    IsProper (pinchedStructureMorphism k K).val := by
  have : UniversallyClosed
      (projectiveLine K ↘ Spec (.of K)) :=
    projectiveLine_universallyClosed K
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : UniversallyClosed
      ((pinchedNormalizationMorphism k K).val ≫ (pinchedStructureMorphism k K).val) := by
    rw [pinchedNormalizationMorphism_comp]
    infer_instance
  have : UniversallyClosed (pinchedStructureMorphism k K).val :=
    UniversallyClosed.of_comp_surjective (pinchedNormalizationMorphism k K).val _
  exact ⟨⟩

private theorem regularLocalRing_spec_of_principal {R : Type u} [CommRing R]
    [IsDomain R] [IsPrincipalIdealRing R] (x : Spec (.of R)) :
    IsRegularLocalRing ((Spec (.of R)).presheaf.stalk x) := by
  have : x.asIdeal.IsPrime := x.isPrime
  have : IsRegularLocalRing (Localization.AtPrime x.asIdeal) := inferInstance
  exact IsRegularLocalRing.of_ringEquiv (Spec.stalkIso (.of R) x).symm.commRingCatIsoToRingEquiv

private theorem regularLocalRing_of_openImmersion {Y Z : Scheme.{u}}
    (j : Y ⟶ Z) [IsOpenImmersion j] (y : Y)
    [IsRegularLocalRing (Y.presheaf.stalk y)] :
    IsRegularLocalRing (Z.presheaf.stalk (j y)) :=
  IsRegularLocalRing.of_ringEquiv (asIso (j.stalkMap y)).symm.commRingCatIsoToRingEquiv

/-- Regularity of the stalk of an open immersion's target descends to the source. -/
private theorem regularLocalRing_of_openImmersion_target {Y Z : Scheme.{u}}
    (j : Y ⟶ Z) [IsOpenImmersion j] (y : Y)
    [IsRegularLocalRing (Z.presheaf.stalk (j y))] :
    IsRegularLocalRing (Y.presheaf.stalk y) :=
  IsRegularLocalRing.of_ringEquiv (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv

private theorem pinchedAffine_regular_off_origin [Module.Finite k K]
    (q : Spec (.of (pinchedPolynomialRing k K))) (hq : q ≠ pinchedOrigin k K) :
    IsRegularLocalRing ((Spec (.of (pinchedPolynomialRing k K))).presheaf.stalk q) := by
  have hq' : q ∈ Set.range (pinchedPuncturedChart k K) := by
    rw [pinchedPuncturedChart_range]
    exact hq
  obtain ⟨z, rfl⟩ := hq'
  have := regularLocalRing_spec_of_principal (projectiveLinePuncturedChart K z)
  have := regularLocalRing_of_openImmersion_target (projectiveLinePuncturedChart K) z
  exact regularLocalRing_of_openImmersion (pinchedPuncturedChart k K) z

private theorem pinchedCurve_regular_off_origin [Module.Finite k K]
    (x : pinchedCurve k K) (hx : x ≠ (pinchedChartA k K) (pinchedOrigin k K)) :
    IsRegularLocalRing ((pinchedCurve k K).presheaf.stalk x) := by
  have hx' : x ∈ Set.range (pinchedChartA k K).base ∪ Set.range (pinchedChartB k K).base :=
    Set.eq_univ_iff_forall.mp (pinchedCharts_cover k K) x
  rcases hx' with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have := pinchedAffine_regular_off_origin k K q (fun h => hx (congrArg _ h))
    exact regularLocalRing_of_openImmersion (pinchedChartA k K) q
  · have := regularLocalRing_spec_of_principal q
    exact regularLocalRing_of_openImmersion (pinchedChartB k K) q

private theorem pinchedCurve_singularLocus [Module.Finite k K]
    (hK : 1 < Module.finrank k K) :
    singularLocus (pinchedCurve k K) =
      {(pinchedChartA k K).base (pinchedOrigin k K)} := by
  have hsing : ¬ IsRegularLocalRing ((pinchedCurve k K).presheaf.stalk
      ((pinchedChartA k K) (pinchedOrigin k K))) := by
    intro hreg
    apply not_isIntegrallyClosed_pinchedPolynomialRing k K hK
    apply IsIntegrallyClosed.of_localization_maximal
    intro p hp hmax
    let q : PrimeSpectrum (pinchedPolynomialRing k K) := ⟨p, hmax.isPrime⟩
    have hq : IsRegularLocalRing
        ((Spec (.of (pinchedPolynomialRing k K))).presheaf.stalk q) := by
      by_cases h : q = pinchedOrigin k K
      · rw [h]
        exact regularLocalRing_of_openImmersion_target (pinchedChartA k K) (pinchedOrigin k K)
      · exact pinchedAffine_regular_off_origin k K q h
    have : IsRegularLocalRing (Localization.AtPrime p) :=
      IsRegularLocalRing.of_ringEquiv
        (Spec.stalkIso (.of (pinchedPolynomialRing k K)) q).commRingCatIsoToRingEquiv
    exact isIntegrallyClosed_of_isRegularLocalRing _
  ext x
  change (¬ IsRegularLocalRing ((pinchedCurve k K).presheaf.stalk x)) ↔
    x = (pinchedChartA k K).base (pinchedOrigin k K)
  refine ⟨Not.imp_symm (pinchedCurve_regular_off_origin k K x), ?_⟩
  rintro rfl
  exact hsing

end AlgebraicGeometry

end
