module

public import StacksFrontier.Homology.DerivedComplete.CompletionSequences.SequenceData
import all StacksFrontier.Homology.DerivedComplete.CompletionSequences.SequenceData
public import StacksFrontier.Homology.DerivedComplete.CompletionSequences.KoszulTowerComparison
import all StacksFrontier.Homology.DerivedComplete.CompletionSequences.KoszulTowerComparison
public import StacksFrontier.Homology.DerivedComplete.CompletionSequences.ModuleCohomology
import all StacksFrontier.Homology.DerivedComplete.CompletionSequences.ModuleCohomology

/-!
# Principal completion sequences: truncation sequences and the main theorem

Triangulatedness of the derived-complete subcategory, the cohomology of the completed canonical
truncations of a derived object, the truncation short exact sequences, and Stacks 0BKG
(`derivedCompletion_principal_homology`).
-/

section

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Preadditive CategoryTheory.Linear DerivedCategory PrincipalTorsionTower

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CompletionSequences

open ZeroObject

private lemma principalComplete_isClosedUnderIsomorphisms (A : Type u) [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] (f : A) :
    (principalP A f : ObjectProperty (DerivedCategory (ModuleCat.{v} A))).IsClosedUnderIsomorphisms
      := by
  let C : ObjectProperty (ModuleCat.{v} A) :=
    fun M => IsDerivedCompleteModule (Ideal.span {f}) M
  have hc := AdicWeakSerre.derivedCompleteModules_isWeakSerreClass_and_homology_iff
    A (Ideal.span {f})
  have : C.IsWeakSerreClass := hc.1
  constructor
  intro X Y e hX
  apply (hc.2 Y).mp
  intro n
  exact C.prop_of_iso ((homology A n).mapIso e) ((hc.2 X).mpr hX n)

private lemma principalComplete_isTriangulated (A : Type u) [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] (f : A) :
    (principalP A f : ObjectProperty (DerivedCategory (ModuleCat.{v} A))).IsTriangulated := by
  let C : ObjectProperty (ModuleCat.{v} A) :=
    fun M => IsDerivedCompleteModule (Ideal.span {f}) M
  have hc := AdicWeakSerre.derivedCompleteModules_isWeakSerreClass_and_homology_iff
    A (Ideal.span {f})
  have : C.IsWeakSerreClass := hc.1
  refine { exists_zero := ?_, isStableUnderShiftBy := ?_, ext₂' := ?_ }
  · exact ⟨0, isZero_zero _, (hc.2 _).mp (fun n => C.prop_of_isZero (Functor.map_isZero _
    (isZero_zero _)))⟩
  · intro n
    constructor
    intro X hX
    exact isDerivedComplete_shift (Ideal.span {f}) hX n
  · intro T hT h₁ h₃
    refine ⟨T.obj₂, (hc.2 _).mp ?_, ⟨Iso.refl _⟩⟩
    intro n
    exact ObjectProperty.prop_mid_of_exact₄ C.prop_obj₂_of_exact
      (HomologySequence.δ_comp T hT (n - 1) n (by omega))
      (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero])
      (HomologySequence.comp_δ T hT n (n + 1))
      (HomologySequence.exact₁ T hT (n - 1) n (by omega))
      (HomologySequence.exact₂ T hT n)
      (HomologySequence.exact₃ T hT n (n + 1))
      ((hc.2 _).mpr h₃ (n - 1)) ((hc.2 _).mpr h₁ n)
      ((hc.2 _).mpr h₃ n) ((hc.2 _).mpr h₁ (n + 1))

private lemma completion_isTriangulated (A : Type u) [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] (f : A)
    (completion : DerivedCategory (ModuleCat.{v} A) ⥤ (principalP A f).FullSubcategory)
    (adj : completion ⊣ (principalP A f).ι) :
    ∃ h : (completion ⋙ (principalP A f).ι).CommShift ℤ,
      letI := h; (completion ⋙ (principalP A f).ι).IsTriangulated := by
  let := principalComplete_isClosedUnderIsomorphisms A f
  let := principalComplete_isTriangulated A f
  let := adj.leftAdjointCommShift ℤ
  let := adj.commShift_of_rightAdjoint ℤ
  let := adj.isTriangulated_leftAdjoint
  exact ⟨inferInstance, inferInstance⟩

private lemma homology_mor₁_isIso (A : Type u) [CommRing A]
    (T : Triangle (DerivedCategory (ModuleCat.{v} A))) (hT : T ∈ distTriang _) (r : ℤ)
    (h₀ : IsZero ((homology A (r - 1)).obj T.obj₃))
    (h₁ : IsZero ((homology A r).obj T.obj₃)) : IsIso ((homology A r).map T.mor₁) := by
  have : Mono ((homology A r).map T.mor₁) :=
    (HomologySequence.exact₁ T hT (r - 1) r (by omega)).mono_g_iff.mpr (h₀.eq_of_src _ _)
  have : Epi ((homology A r).map T.mor₁) :=
    (HomologySequence.exact₂ T hT r).epi_f_iff.mpr (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

private lemma homology_mor₂_isIso (A : Type u) [CommRing A]
    (T : Triangle (DerivedCategory (ModuleCat.{v} A))) (hT : T ∈ distTriang _) (r : ℤ)
    (h₀ : IsZero ((homology A r).obj T.obj₁))
    (h₁ : IsZero ((homology A (r + 1)).obj T.obj₁)) : IsIso ((homology A r).map T.mor₂) := by
  have : Mono ((homology A r).map T.mor₂) :=
    (HomologySequence.exact₂ T hT r).mono_g_iff.mpr (h₀.eq_of_src _ _)
  have : Epi ((homology A r).map T.mor₂) :=
    (HomologySequence.exact₃ T hT r (r + 1)).epi_f_iff.mpr (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

private lemma homology_truncIn_isIso (A : Type u) [CommRing A]
    (X : DerivedCategory (ModuleCat.{v} A)) (p r : ℤ) (hr : r ≤ p) :
    IsIso ((homology A r).map ((truncIn A p).app X)) := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{v} A)
  exact homology_mor₁_isIso A _ (t.triangleLEGE_distinguished p (p + 1) rfl X) r
    (DerivedCategory.isZero_of_isGE ((truncGE A (p + 1)).obj X) (p + 1) _ (by omega))
    (DerivedCategory.isZero_of_isGE ((truncGE A (p + 1)).obj X) (p + 1) _ (by omega))

private lemma homology_truncOut_isIso (A : Type u) [CommRing A]
    (X : DerivedCategory (ModuleCat.{v} A)) (p r : ℤ) (hr : p ≤ r) :
    IsIso ((homology A r).map ((truncOut A p).app X)) := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{v} A)
  exact homology_mor₂_isIso A _ (t.triangleLEGE_distinguished (p - 1) p (by omega) X) r
    (DerivedCategory.isZero_of_isLE ((truncLE A (p - 1)).obj X) (p - 1) _ (by omega))
    (DerivedCategory.isZero_of_isLE ((truncLE A (p - 1)).obj X) (p - 1) _ (by omega))

private noncomputable def pureDegreeComparison (A : Type u) [CommRing A]
    (X : DerivedCategory (ModuleCat.{v} A)) (p : ℤ) [X.IsGE p] [X.IsLE p]
    (M : ModuleCat.{v} A) (eH : (homology A p).obj X ≅ M) :
    {e : X ≅ (single A p).obj M //
      (homology A p).map e.hom ≫ (singleHomology A p M).hom = eH.hom} := by
  classical
  apply Classical.choice
  obtain ⟨M₀, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE X p
  let eH₀ := (homology A p).mapIso e ≪≫ singleHomology A p M₀
  refine ⟨⟨e ≪≫ (single A p).mapIso (eH₀.symm ≪≫ eH), ?_⟩⟩
  change (homology A p).map (e.hom ≫ (single A p).map (eH₀.inv ≫ eH.hom)) ≫ _ = _
  have hn : (homology A p).map ((single A p).map (eH₀.inv ≫ eH.hom)) ≫
      (singleHomology A p M).hom = (singleHomology A p M₀).hom ≫ eH₀.inv ≫ eH.hom :=
    (singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) p).hom.naturality _
  rw [Functor.map_comp, Category.assoc, hn]
  change (homology A p).map e.hom ≫ (singleHomology A p M₀).hom ≫ eH₀.inv ≫ eH.hom = _
  simp [eH₀]

private noncomputable def truncationLowerIso (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ) :
    {e : (truncGE A p).obj ((truncLE A p).obj K) ≅ (single A p).obj ((homology A p).obj K) //
      (homology A p).map ((truncOut A p).app ((truncLE A p).obj K)) ≫
        (homology A p).map e.hom ≫ (singleHomology A p ((homology A p).obj K)).hom =
          (homology A p).map ((truncIn A p).app K)} := by
  have := homology_truncOut_isIso A ((truncLE A p).obj K) p p le_rfl
  have := homology_truncIn_isIso A K p p le_rfl
  let eH : (homology A p).obj ((truncGE A p).obj ((truncLE A p).obj K)) ≅
      (homology A p).obj K := (asIso ((homology A p).map ((truncOut A p).app ((truncLE A p).obj
        K)))).symm ≪≫
    asIso ((homology A p).map ((truncIn A p).app K))
  let e := pureDegreeComparison A ((truncGE A p).obj ((truncLE A p).obj K)) p _ eH
  refine ⟨e.val, ?_⟩
  rw [e.property]
  simp [eH]

private noncomputable def truncationUpperIso (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ) :
    {e : (truncLE A (p + 1)).obj ((truncGE A (p + 1)).obj K) ≅
        (single A (p + 1)).obj ((homology A (p + 1)).obj K) //
      (homology A (p + 1)).map e.hom ≫ (singleHomology A (p + 1) ((homology A (p + 1)).obj K)).hom ≫
        (homology A (p + 1)).map ((truncOut A (p + 1)).app K) =
          (homology A (p + 1)).map ((truncIn A (p + 1)).app ((truncGE A (p + 1)).obj K))} := by
  have := homology_truncOut_isIso A K (p + 1) (p + 1) le_rfl
  have := homology_truncIn_isIso A ((truncGE A (p + 1)).obj K) (p + 1) (p + 1) le_rfl
  let eH := asIso ((homology A (p + 1)).map
      ((truncIn A (p + 1)).app ((truncGE A (p + 1)).obj K))) ≪≫
    (asIso ((homology A (p + 1)).map ((truncOut A (p + 1)).app K))).symm
  let e := pureDegreeComparison A ((truncLE A (p + 1)).obj ((truncGE A (p + 1)).obj K)) (p + 1) _ eH
  refine ⟨e.val, ?_⟩
  rw [reassoc_of% e.property]
  simp [eH]

private abbrev principalStageTriangle (A : Type u) [CommRing A]
    (f : A) (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) :=
  Triangle.mk (DerivedCategory.Q.map (f ^ (n + 1) • 𝟙 C))
    (DerivedCategory.Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 C)))
    (DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C))).mor₃

private lemma principalStage_homology_isZero (A : Type u) [CommRing A]
    (f : A) (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) (r : ℤ)
    (h₀ : IsZero ((homology A r).obj (DerivedCategory.Q.obj C)))
    (h₁ : IsZero ((homology A (r + 1)).obj (DerivedCategory.Q.obj C))) :
    IsZero ((homology A r).obj (principalStageTriangle A f C n).obj₃) :=
  (HomologySequence.exact₃ (principalStageTriangle A f C n)
    (DerivedCategory.mappingCone_triangle_distinguished _) r (r + 1)).isZero_of_both_isZero h₀ h₁

private lemma principalHomologyInclusion_epi (A : Type u) [CommRing A]
    (f : A) (C : CochainComplex (ModuleCat.{v} A) ℤ) (p : ℤ)
    (h : IsZero ((homology A (p + 1)).obj (DerivedCategory.Q.obj C))) (n : ℕ) :
    Epi ((homology A p).map (DerivedCategory.Q.map (principalComplexUnit A f C ≫
      Pi.π (fun n : ℕ => (principalComplexSystem A f C).obj ⟨n⟩) n))) := by
  rw [principalComplexUnit_π]
  exact (HomologySequence.exact₃ (principalStageTriangle A f C n)
      (DerivedCategory.mappingCone_triangle_distinguished _) p (p + 1)).epi_f_iff.mpr
    (h.eq_of_tgt _ _)

private lemma principalHomologyTransition_epi (A : Type u) [CommRing A]
    (f : A) (C : CochainComplex (ModuleCat.{v} A) ℤ) (p : ℤ)
    (h : IsZero ((homology A (p + 1)).obj (DerivedCategory.Q.obj C))) (n : ℕ) :
    Epi ((principalComplexSystem A f C ⋙ DerivedCategory.Q ⋙ homology A p).map
      (homOfLE (Nat.le_succ n)).op) := by
  have he := principalHomologyInclusion_epi A f C p h n
  have hd := (principalComplexUnit_difference A f C) =≫
    Pi.π (fun n : ℕ => (principalComplexSystem A f C).obj ⟨n⟩) n
  simp only [Category.assoc, complexDifference, Pi.lift_comp_π, comp_sub, zero_comp] at hd
  have hw := congrArg (fun g => (homology A p).map (DerivedCategory.Q.map g))
    (sub_eq_zero.mp hd).symm
  simp only [Functor.map_comp] at hw
  have he' : Epi ((homology A p).map (DerivedCategory.Q.map (principalComplexUnit A f C)) ≫
      (homology A p).map (DerivedCategory.Q.map
        (Pi.π (fun n : ℕ => (principalComplexSystem A f C).obj ⟨n⟩) n))) := by
    simpa only [Functor.map_comp] using he
  rw [← Category.assoc] at hw
  exact @epi_of_epi_fac _ _ _ _ _ _ _ _ he' hw

/-- The homology of the completion of `Q C` vanishes if the Milnor limit terms vanish. -/
private lemma completion_homology_isZero_of_limits (A : Type u) [CommRing A]
    (f : A) (F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A))
    (η : 𝟭 _ ⟶ F) (c : CompletionComparison A f F η)
    (X : DerivedCategory (ModuleCat.{v} A)) (C : CochainComplex (ModuleCat.{v} A) ℤ)
    (e : X ≅ DerivedCategory.Q.obj C) (r : ℤ)
    (h₁ : IsZero (firstDerivedLimit A
      (principalComplexSystem A f C ⋙ DerivedCategory.Q ⋙ homology A (r - 1))))
    (h₂ : IsZero (limit (principalComplexSystem A f C ⋙ DerivedCategory.Q ⋙ homology A r))) :
    IsZero ((homology A r).obj (F.obj X)) := by
  apply IsZero.of_iso _ ((homology A r).mapIso (F.mapIso e ≪≫ c.iso C))
  obtain ⟨i, q, w, hi, hq, hs⟩ := milnorTriangle_homology_shortExact A (principalComplexSystem A f
    C) r
  exact hs.exact.isZero_of_both_isZero h₁ h₂

private lemma completion_homology_isZero_above (A : Type u) [CommRing A]
    (f : A) (F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A))
    (η : 𝟭 _ ⟶ F) (c : CompletionComparison A f F η)
    (X : DerivedCategory (ModuleCat.{v} A)) (p r : ℤ) [X.IsLE p] (hr : p < r) :
    IsZero ((homology A r).obj (F.obj X)) := by
  obtain ⟨C, hC, ⟨e⟩⟩ := exists_iso_Q_obj_of_isLE X p
  refine completion_homology_isZero_of_limits A f F η c X C e r ?_ ?_
  · by_cases heq : r - 1 = p
    · have : Epi (moduleDifference A
        (principalComplexSystem A f C ⋙ DerivedCategory.Q ⋙ homology A (r - 1))) :=
        moduleDifference_epi A _ (principalHomologyTransition_epi A f C (r - 1)
          (DerivedCategory.isZero_of_isLE _ p _ (by omega)))
      exact isZero_cokernel_of_epi _
    · exact firstDerivedLimit_isZero A _ (fun n => principalStage_homology_isZero A f C n.unop (r -
      1)
        (DerivedCategory.isZero_of_isLE _ p _ (by omega))
        (DerivedCategory.isZero_of_isLE _ p _ (by omega)))
  · exact moduleLimit_isZero A _ (fun n => principalStage_homology_isZero A f C n.unop r
      (DerivedCategory.isZero_of_isLE _ p _ hr) (DerivedCategory.isZero_of_isLE _ p _ (by omega)))

private lemma completion_homology_isZero_below (A : Type u) [CommRing A]
    (f : A) (F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A))
    (η : 𝟭 _ ⟶ F) (c : CompletionComparison A f F η)
    (X : DerivedCategory (ModuleCat.{v} A)) (p r : ℤ) [X.IsGE p] (hr : r < p - 1) :
    IsZero ((homology A r).obj (F.obj X)) := by
  obtain ⟨C, hC, ⟨e⟩⟩ := exists_iso_Q_obj_of_isGE X p
  refine completion_homology_isZero_of_limits A f F η c X C e r ?_ ?_
  · exact firstDerivedLimit_isZero A _ (fun n => principalStage_homology_isZero A f C n.unop (r - 1)
      (DerivedCategory.isZero_of_isGE _ p _ (by omega))
      (DerivedCategory.isZero_of_isGE _ p _ (by omega)))
  · exact moduleLimit_isZero A _ (fun n => principalStage_homology_isZero A f C n.unop r
      (DerivedCategory.isZero_of_isGE _ p _ (by omega))
      (DerivedCategory.isZero_of_isGE _ p _ (by omega)))

private lemma completion_homology_truncOut_isIso (A : Type u) [CommRing A]
    (f : A) (F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A))
    (η : 𝟭 _ ⟶ F) (c : CompletionComparison A f F η) [F.CommShift ℤ] [F.IsTriangulated]
    (X : DerivedCategory (ModuleCat.{v} A)) (p r : ℤ) (hr : p ≤ r) :
    IsIso ((homology A r).map (F.map ((truncOut A p).app X))) := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{v} A)
  exact homology_mor₂_isIso A _
    (F.map_distinguished _ (t.triangleLEGE_distinguished (p - 1) p (by omega) X)) r
    (completion_homology_isZero_above A f F η c ((truncLE A (p - 1)).obj X) (p - 1) r (by omega))
    (completion_homology_isZero_above A f F η c ((truncLE A (p - 1)).obj X) (p - 1) (r + 1) (by
      omega))

private lemma completion_homology_truncIn_isIso (A : Type u) [CommRing A]
    (f : A) (F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A))
    (η : 𝟭 _ ⟶ F) (c : CompletionComparison A f F η) [F.CommShift ℤ] [F.IsTriangulated]
    (X : DerivedCategory (ModuleCat.{v} A)) (p r : ℤ) (hr : r < p) :
    IsIso ((homology A r).map (F.map ((truncIn A p).app X))) := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{v} A)
  exact homology_mor₁_isIso A _
    (F.map_distinguished _ (t.triangleLEGE_distinguished p (p + 1) rfl X)) r
    (completion_homology_isZero_below A f F η c ((truncGE A (p + 1)).obj X) (p + 1) (r - 1) (by
      omega))
    (completion_homology_isZero_below A f F η c ((truncGE A (p + 1)).obj X) (p + 1) r (by omega))

private noncomputable def principalTruncation (A : Type u) [CommRing A]
    (f : A) (F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A))
    (η : 𝟭 _ ⟶ F) (c : CompletionComparison A f F η) [F.CommShift ℤ] [F.IsTriangulated]
    (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ) : TruncationIdentifications A F K p where
  lower := (truncationLowerIso A K p).val
  lower_homology := (truncationLowerIso A K p).property
  upper := (truncationUpperIso A K p).val
  upper_homology := (truncationUpperIso A K p).property
  lower_isIso := by
    have := completion_homology_truncOut_isIso A f F η c ((truncLE A p).obj K) p p le_rfl
    rw [F.map_comp, (homology A p).map_comp]
    infer_instance
  upper_isIso := by
    have := completion_homology_truncIn_isIso A f F η c ((truncGE A (p + 1)).obj K) (p + 1) p (by
      omega)
    rw [F.map_comp, (homology A p).map_comp]
    infer_instance

private lemma truncationSequence_shortExact (A : Type u) [CommRing A]
    (f : A) (F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A))
    (η : 𝟭 _ ⟶ F) (c : CompletionComparison A f F η) [F.CommShift ℤ] [F.IsTriangulated]
    (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ)
    (t : TruncationIdentifications A F K p) (s : CompletionShift A F η)
    (e : (homology A (-1)).obj (F.obj ((single A 0).obj ((homology A (p + 1)).obj K))) ≅
      adicTateModule A ((homology A (p + 1)).obj K) f) :
    ∃ w : t.inclusion s ≫ t.projection f s e = 0,
      (ShortComplex.mk (t.inclusion s) (t.projection f s e) w).ShortExact := by
  let T := F.mapTriangle.obj
    ((DerivedCategory.TStructure.t (C := ModuleCat.{v} A)).triangleLEGE p (p + 1) rfl |>.obj K)
  have hT : T ∈ distTriang _ := F.map_distinguished _
    ((DerivedCategory.TStructure.t (C := ModuleCat.{v} A)).triangleLEGE_distinguished p (p + 1) rfl
      K)
  let a := (homology A p).map (F.map ((truncIn A p).app K))
  let b := (homology A p).map (F.map ((truncOut A (p + 1)).app K))
  have w : a ≫ b = 0 := by
    show (homology A p).map T.mor₁ ≫ (homology A p).map T.mor₂ = 0
    rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero]
  have hm : Mono a :=
    (HomologySequence.exact₁ T hT (p - 1) p (by omega)).mono_g_iff.mpr
      ((completion_homology_isZero_below A f F η c ((truncGE A (p + 1)).obj K)
        (p + 1) (p - 1) (by omega)).eq_of_src _ _)
  have he : Epi b :=
    (HomologySequence.exact₃ T hT p (p + 1)).epi_f_iff.mpr
      ((completion_homology_isZero_above A f F η c ((truncLE A p).obj K)
        p (p + 1) (by omega)).eq_of_tgt _ _)
  have hs : (ShortComplex.mk a b w).ShortExact :=
    { exact := HomologySequence.exact₂ T hT p, mono_f := hm, epi_g := he }
  let eL := (s.singleIso ((homology A p).obj K) p p 0 (by omega)).symm ≪≫
    (asIso ((homology A p).map (F.map ((truncOut A p).app ((truncLE A p).obj K) ≫
      t.lower.hom)))).symm
  let eR := (asIso ((homology A p).map (F.map (t.upper.inv ≫
      (truncIn A (p + 1)).app ((truncGE A (p + 1)).obj K))))).symm ≪≫
    s.singleIso ((homology A (p + 1)).obj K) (p + 1) p (-1) (by omega) ≪≫ e
  have w' : (eL.hom ≫ a) ≫ (b ≫ eR.hom) = 0 := by simp [Category.assoc, reassoc_of% w]
  have hs' : (ShortComplex.mk (eL.hom ≫ a) (b ≫ eR.hom) w').ShortExact := by
    apply ShortComplex.shortExact_of_iso _ hs
    exact ShortComplex.isoMk eL.symm (Iso.refl _) eR (by simp) (by simp)
  have hsign := shortExact_negOnePow_smul_right (eL.hom ≫ a) (b ≫ eR.hom) w' (p + 1) hs'
  have hw : t.inclusion s ≫ t.projection f s e = 0 := by
    show (eL.hom ≫ a) ≫ ((p + 1).negOnePow • (b ≫ eR.hom)) = 0
    rw [Linear.comp_units_smul, w', smul_zero]
  refine ⟨hw, ?_⟩
  exact hsign

private noncomputable def principalSequences (A : Type u) [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] (f : A)
    (completion : DerivedCategory (ModuleCat.{v} A) ⥤ (principalP A f).FullSubcategory)
    (adj : completion ⊣ (principalP A f).ι) :
    PrincipalCompletionSequences A f (completion ⋙ (principalP A f).ι) adj.unit := by
  classical
  apply Classical.choice
  obtain ⟨hF, htri⟩ := completion_isTriangulated A f completion adj
  let := hF
  let := htri
  let F := completion ⋙ (principalP A f).ι
  let c := principalComparison adj
  let s := completionShift adj
  let m := principalModuleSequence A f F adj.unit c
  let t := principalTruncation A f F adj.unit c
  have h (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ) :
      ∃ w : (t K p).inclusion s ≫
          (t K p).projection f s (m ((homology A (p + 1)).obj K)).tateIso = 0,
        (ShortComplex.mk ((t K p).inclusion s)
          ((t K p).projection f s (m ((homology A (p + 1)).obj K)).tateIso) w).ShortExact :=
    truncationSequence_shortExact A f F adj.unit c K p (t K p) s
      (m ((homology A (p + 1)).obj K)).tateIso
  exact ⟨{
    comparison := c
    shift := s
    moduleSequence := m
    truncation := t
    truncation_zero := fun K p => (h K p).choose
    truncation_shortExact := fun K p => (h K p).choose_spec }⟩
/-- The principal completion sequences and cohomology calculation, with the prescribed maps. -/
private theorem principalCompletionSolution
    (A : Type u) [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (f : A) :
    let I : Ideal A := Ideal.span {f}
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun L ↦ IsDerivedComplete I L
    ∀ (completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory)
      (adj : completion ⊣ P.ι),
      let completed := completion ⋙ P.ι
      ∃ S : PrincipalCompletionSequences A f completed adj.unit,
        (∀ M : ModuleCat.{v} A,
          let Mhat := completed.obj ((single A 0).obj M)
          let torsionRlim := moduleDerivedLimit A (powerTorsionSystem A M f)
          let quotientRlim := moduleDerivedLimit A (powerQuotientSystem A M f)
          ∃ (eT : FirstDerivedLimitComparison A (powerTorsionSystem A M f))
            (eQ : FirstDerivedLimitComparison A (powerQuotientSystem A M f)),
            IsDerivedLimit (powerTorsionSystem A M f ⋙ single A 0) torsionRlim ∧
            IsDerivedLimit (powerQuotientSystem A M f ⋙ single A 0) quotientRlim ∧
            Nonempty ((homology A (-1)).obj Mhat ≅ adicTateModule A M f) ∧
            (ShortComplex.mk (eT.iso.hom ≫ (S.moduleSequence M).inclusion)
              (S.moduleSequence M).projection
              (by rw [Category.assoc, (S.moduleSequence M).zero, comp_zero])).ShortExact ∧
            Nonempty ((homology A 1).obj Mhat ≅ (homology A 1).obj quotientRlim) ∧
            IsZero ((homology A 1).obj quotientRlim) ∧
            ∀ n : ℤ, n ≠ -1 → n ≠ 0 → IsZero ((homology A n).obj Mhat)) ∧
        ∀ (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ),
          (ShortComplex.mk ((S.truncation K p).inclusion S.shift)
            ((S.truncation K p).projection f S.shift
              (S.moduleSequence ((homology A (p + 1)).obj K)).tateIso)
            (S.truncation_zero K p)).ShortExact := by
  intro I P completion adj
  let S := principalSequences A f completion adj
  refine ⟨S, ?_, fun K p => S.truncation_shortExact K p⟩
  intro M
  let eT := firstDerivedLimitComparison A (powerTorsionSystem A M f)
  let eQ := firstDerivedLimitComparison A (powerQuotientSystem A M f)
  have hQ := quotientDerivedLimit_homology_isZero A f M
  have hM := moduleCompletion_homology_isZero A f _ adj.unit S.comparison M
  refine ⟨eT, eQ, moduleDerivedLimit_isDerivedLimit A _, moduleDerivedLimit_isDerivedLimit A _,
    ⟨(S.moduleSequence M).tateIso⟩, (S.moduleSequence M).shortExact_derivedLimit eT,
    ?_, hQ, hM⟩
  exact ⟨(hM 1 (by omega) (by omega)).isoZero ≪≫ hQ.isoZero.symm⟩

end CompletionSequences
end

end

section

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Preadditive CategoryTheory.Linear DerivedCategory PrincipalTorsionTower

universe u v w x

namespace CompletionSequences

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0BKG.** The two principal-completion short exact sequences, with their
canonical maps. `S` records the fixed mapping-cocone model, its comparison with the
completion unit, and the normalized truncation maps. The remaining clauses retain all
cohomology calculations, including both derived-limit realizations and the degree-one
vanishing for the quotient system. -/
@[stacks 0BKG]
public theorem derivedCompletion_principal_homology
    (A : Type u) [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (f : A) :
    let I : Ideal A := Ideal.span {f}
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun L ↦ IsDerivedComplete I L
    ∀ (completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory)
      (adj : completion ⊣ P.ι),
      let completed := completion ⋙ P.ι
      ∃ S : PrincipalCompletionSequences A f completed adj.unit,
        (∀ M : ModuleCat.{v} A,
          let Mhat := completed.obj ((single A 0).obj M)
          let torsionRlim := moduleDerivedLimit A (powerTorsionSystem A M f)
          let quotientRlim := moduleDerivedLimit A (powerQuotientSystem A M f)
          ∃ (eT : FirstDerivedLimitComparison A (powerTorsionSystem A M f))
            (eQ : FirstDerivedLimitComparison A (powerQuotientSystem A M f)),
            IsDerivedLimit (powerTorsionSystem A M f ⋙ single A 0) torsionRlim ∧
            IsDerivedLimit (powerQuotientSystem A M f ⋙ single A 0) quotientRlim ∧
            Nonempty ((homology A (-1)).obj Mhat ≅ adicTateModule A M f) ∧
            (ShortComplex.mk (eT.iso.hom ≫ (S.moduleSequence M).inclusion)
              (S.moduleSequence M).projection
              (by rw [Category.assoc, (S.moduleSequence M).zero, comp_zero])).ShortExact ∧
            Nonempty ((homology A 1).obj Mhat ≅ (homology A 1).obj quotientRlim) ∧
            IsZero ((homology A 1).obj quotientRlim) ∧
            ∀ n : ℤ, n ≠ -1 → n ≠ 0 → IsZero ((homology A n).obj Mhat)) ∧
        ∀ (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ),
          (ShortComplex.mk ((S.truncation K p).inclusion S.shift)
            ((S.truncation K p).projection f S.shift
              (S.moduleSequence ((homology A (p + 1)).obj K)).tateIso)
            (S.truncation_zero K p)).ShortExact := by
  exact principalCompletionSolution A f

end CompletionSequences
end

end
