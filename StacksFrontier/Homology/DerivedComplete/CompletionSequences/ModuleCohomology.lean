module

public import StacksFrontier.Homology.DerivedComplete.CompletionSequences.SequenceData

/-!
# Principal completion sequences: cohomology of a completed module

Cohomology of the Milnor triangle, the torsion and quotient stages of a module, the
first-derived-limit comparisons, and the module short exact sequence and vanishing results
for the derived completion of a module at a principal ideal.
-/

section

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Preadditive CategoryTheory.Linear DerivedCategory PrincipalTorsionTower

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CompletionSequences

private noncomputable def complexHomologyProductIso
    (A : Type u) [CommRing A] (X : ℕ → CochainComplex (ModuleCat.{v} A) ℤ) (r : ℤ) :
    (homology A r).obj (DerivedCategory.Q.obj (∏ᶜ X)) ≅
      ∏ᶜ fun n : ℕ => (homology A r).obj (DerivedCategory.Q.obj (X n)) := by
  have := Stacks.DerivedProducts.preservesLimitsOfShape_homologyFunctor (A := ModuleCat.{v} A) (I :=
    ℕ) r
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q ⋙ homology A r) :=
    preservesLimitsOfShape_of_natIso (homologyFunctorFactors (ModuleCat.{v} A) r).symm
  exact PreservesProduct.iso (DerivedCategory.Q ⋙ homology A r) X

@[reassoc]
private lemma complexHomologyProductIso_π
    (A : Type u) [CommRing A] (X : ℕ → CochainComplex (ModuleCat.{v} A) ℤ) (r : ℤ) (n : ℕ) :
    (complexHomologyProductIso A X r).hom ≫
        Pi.π (fun n : ℕ => (homology A r).obj (DerivedCategory.Q.obj (X n))) n =
      (homology A r).map (DerivedCategory.Q.map (Pi.π X n)) :=
  piComparison_comp_π (DerivedCategory.Q ⋙ homology A r) X n

private lemma complexHomologyProductIso_difference
    (A : Type u) [CommRing A] (E : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ) (r : ℤ) :
    (homology A r).map (DerivedCategory.Q.map (complexDifference A E)) ≫
        (complexHomologyProductIso A (fun n : ℕ => E.obj ⟨n⟩) r).hom =
      (complexHomologyProductIso A (fun n : ℕ => E.obj ⟨n⟩) r).hom ≫
        moduleDifference A (E ⋙ DerivedCategory.Q ⋙ homology A r) := by
  apply Pi.hom_ext
  intro n
  simp only [moduleDifference, Category.assoc, complexHomologyProductIso_π]
  rw [← Functor.map_comp, ← Functor.map_comp]
  simp [complexDifference, Functor.comp_obj, Functor.comp_map,
    complexHomologyProductIso_π, complexHomologyProductIso_π_assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma milnorTriangle_homology_shortExact
    (A : Type u) [CommRing A] (E : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ) (r : ℤ) :
    let T := milnorTriangle A E
    let e := complexHomologyProductIso A (fun n : ℕ => E.obj ⟨n⟩) (r - 1)
    ∃ (i : firstDerivedLimit A (E ⋙ DerivedCategory.Q ⋙ homology A (r - 1)) ⟶
        (homology A r).obj T.obj₁)
      (q : (homology A r).obj T.obj₁ ⟶ limit (E ⋙ DerivedCategory.Q ⋙ homology A r))
      (w : i ≫ q = 0),
      e.hom ≫ cokernel.π (moduleDifference A (E ⋙ DerivedCategory.Q ⋙ homology A (r - 1))) ≫ i =
          (homology A 0).homologySequenceδ T (r - 1) r (by omega) ∧
        (∀ n : ℕ, q ≫ limit.π (E ⋙ DerivedCategory.Q ⋙ homology A r) ⟨n⟩ =
          (homology A r).map (T.mor₁ ≫ DerivedCategory.Q.map
            (Pi.π (fun n : ℕ => E.obj ⟨n⟩) n))) ∧
        (ShortComplex.mk i q w).ShortExact := by
  intro T e₁
  let H := homology A r
  let H₁ := homology A (r - 1)
  let e₀ := complexHomologyProductIso A (fun n : ℕ => E.obj ⟨n⟩) r
  let δ₁ := moduleDifference A (E ⋙ DerivedCategory.Q ⋙ H₁)
  let δ₀ := moduleDifference A (E ⋙ DerivedCategory.Q ⋙ H)
  have hd₁ : H₁.map T.mor₂ ≫ e₁.hom = e₁.hom ≫ δ₁ :=
    complexHomologyProductIso_difference A E (r - 1)
  have hd₀ : H.map T.mor₂ ≫ e₀.hom = e₀.hom ≫ δ₀ :=
    complexHomologyProductIso_difference A E r
  have hT : T ∈ distTriang _ := milnorTriangle_distinguished A E
  let c := HomologySequence.δ T (r - 1) r (by omega)
  have hc : δ₁ ≫ e₁.inv ≫ c = 0 := by
    rw [← cancel_epi e₁.hom, ← Category.assoc, ← hd₁]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, comp_zero]
    exact HomologySequence.comp_δ T hT (r - 1) r (by omega)
  have had : T.mor₁ ≫ T.mor₂ = 0 := comp_distTriang_mor_zero₁₂ T hT
  have hca : c ≫ H.map T.mor₁ = 0 :=
    HomologySequence.δ_comp T hT (r - 1) r (by omega)
  have ha : (H.map T.mor₁ ≫ e₀.hom) ≫ δ₀ = 0 := by
    rw [Category.assoc, ← hd₀, ← Category.assoc, ← H.map_comp]
    rw [had, H.map_zero, zero_comp]
  let i := cokernel.desc δ₁ (e₁.inv ≫ c) hc
  let q₀ := kernel.lift δ₀ (H.map T.mor₁ ≫ e₀.hom) ha
  let eLim : limit (E ⋙ DerivedCategory.Q ⋙ H) ≅ kernel δ₀ :=
    (inverseSystemLimitKernelForkIsLimit (E ⋙ DerivedCategory.Q ⋙ H)).conePointUniqueUpToIso
      (limit.isLimit _)
  let q := q₀ ≫ eLim.inv
  have heLim : eLim.hom ≫ kernel.ι δ₀ =
      Pi.lift (fun n : ℕ => limit.π (E ⋙ DerivedCategory.Q ⋙ H) ⟨n⟩) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  have hq : q ≫ Pi.lift (fun n : ℕ => limit.π (E ⋙ DerivedCategory.Q ⋙ H) ⟨n⟩) =
      H.map T.mor₁ ≫ e₀.hom := by
    rw [← heLim]
    simp [q, q₀]
  have hi : cokernel.π δ₁ ≫ i = e₁.inv ≫ c := cokernel.π_desc _ _ _
  have hqn (n : ℕ) : q ≫ limit.π (E ⋙ DerivedCategory.Q ⋙ H) ⟨n⟩ =
      H.map T.mor₁ ≫ H.map (DerivedCategory.Q.map (Pi.π (fun n : ℕ => E.obj ⟨n⟩) n)) := by
    have h := congrArg (fun f => f ≫
      Pi.π (fun n : ℕ => H.obj (DerivedCategory.Q.obj (E.obj ⟨n⟩))) n) hq
    simpa only [H, Functor.comp_obj, Category.assoc, Pi.lift_comp_π, e₀,
      complexHomologyProductIso_π] using h
  have hiq : i ≫ q = 0 := by
    rw [← cancel_epi (cokernel.π δ₁)]
    apply limit.hom_ext
    intro n
    simp only [Category.assoc, hqn n.unop, reassoc_of% hi, zero_comp, comp_zero]
    rw [← Category.assoc c, hca]
    simp
  have hprev : (ShortComplex.mk δ₁ (e₁.inv ≫ c) hc).Exact := by
    apply ShortComplex.exact_of_iso _ (HomologySequence.exact₃ T hT (r - 1) r (by omega))
    exact ShortComplex.isoMk e₁ e₁ (Iso.refl _) (by simpa [H₁] using hd₁.symm) (by simp [c])
  have hcurr : (ShortComplex.mk (H.map T.mor₁ ≫ e₀.hom) δ₀ ha).Exact := by
    apply ShortComplex.exact_of_iso _ (HomologySequence.exact₂ T hT r)
    exact ShortComplex.isoMk (Iso.refl _) e₀ e₀ (by simp [H]) (by simpa [H] using hd₀.symm)
  have : Mono i := hprev.mono_cokernelDesc
  have : Epi q₀ := hcurr.epi_kernelLift
  have : Epi q := by dsimp [q]; infer_instance
  refine ⟨i, q, hiq, ?_, ?_, ?_⟩
  · change e₁.hom ≫ cokernel.π δ₁ ≫ i = c
    rw [hi, Iso.hom_inv_id_assoc]
  · intro n
    simpa only [Functor.map_comp] using hqn n
  · refine { exact := ?_, mono_f := inferInstance, epi_g := inferInstance }
    let S := ShortComplex.mk i (H.map T.mor₁) (by
      rw [← cancel_epi (cokernel.π δ₁), ← Category.assoc, hi]
      simp only [Category.assoc, hca, comp_zero])
    let φ : ShortComplex.mk c (H.map T.mor₁) hca ⟶ S :=
      { τ₁ := e₁.hom ≫ cokernel.π δ₁
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [S, i]
        comm₂₃ := by simp [S] }
    have hS : S.Exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp
        (HomologySequence.exact₁ T hT (r - 1) r (by omega))
    let ψ : ShortComplex.mk i q hiq ⟶ S :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := eLim.hom ≫ kernel.ι δ₀ ≫ e₀.inv
        comm₁₂ := by simp [S]
        comm₂₃ := by simp [S, q, q₀] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr hS

private lemma single_homology_isZero (A : Type u) [CommRing A]
    (M : ModuleCat.{v} A) (i j : ℤ) (h : i ≠ j) :
    IsZero ((homology A i).obj ((single A j).obj M)) := by
  rcases lt_or_gt_of_ne h with h | h
  · exact DerivedCategory.isZero_of_isGE _ j i h
  · exact DerivedCategory.isZero_of_isLE _ j i h

private lemma powerMultiplication_eq_smul_id (A : Type u) [CommRing A]
    (M : ModuleCat.{v} A) (a : A) : powerMultiplication A M a = a • 𝟙 M := by
  ext x
  rfl

private lemma moduleCone_homology_mor₂_epi (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) (n : ℕ) :
    Epi ((homology A 0).map (moduleConeTriangle A f M n).mor₂) :=
  (HomologySequence.exact₃ _ (DerivedCategory.mappingCone_triangle_distinguished _) 0
    1).epi_f_iff.mpr ((single_homology_isZero A M 1 0 (by omega)).eq_of_tgt _ _)

private lemma moduleCone_homology_mor₁ (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) (n : ℕ) :
    (homology A 0).map (moduleConeTriangle A f M n).mor₁ ≫ (singleHomology A 0 M).hom =
      (singleHomology A 0 M).hom ≫ powerMultiplication A M (f ^ (n + 1)) := by
  have h : (CochainComplex.singleFunctor (ModuleCat.{v} A) 0).map
      (powerMultiplication A M (f ^ (n + 1))) = f ^ (n + 1) • 𝟙 (moduleComplex A M) := by
    rw [powerMultiplication_eq_smul_id, Functor.map_smul, CategoryTheory.Functor.map_id]
  have hn := (singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).hom.naturality
    (powerMultiplication A M (f ^ (n + 1)))
  change (homology A 0).map (DerivedCategory.Q.map _) ≫ _ = _ at hn
  rw [h] at hn
  exact hn

set_option backward.isDefEq.respectTransparency false in
private lemma moduleTorsionStage_kernel (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) (n : ℕ) :
    let T := moduleConeTriangle A f M n
    let a := HomologySequence.δ T (-1) 0 ≫ (singleHomology A 0 M).hom
    ∃ h : a ≫ powerMultiplication A M (f ^ (n + 1)) = 0,
      Nonempty (IsLimit (KernelFork.ofι a h)) := by
  intro T a
  have hT : T ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished _
  have ha : a ≫ powerMultiplication A M (f ^ (n + 1)) = 0 := by
    dsimp only [a]
    rw [Category.assoc, ← moduleCone_homology_mor₁, ← Category.assoc,
      HomologySequence.δ_comp T hT (-1) 0, zero_comp]
  let S := ShortComplex.mk a (powerMultiplication A M (f ^ (n + 1))) ha
  have he : S.Exact := by
    apply ShortComplex.exact_of_iso _ (HomologySequence.exact₁ T hT (-1) 0)
    exact ShortComplex.isoMk (Iso.refl _) (singleHomology A 0 M) (singleHomology A 0 M)
      (by simp [S, a]) (by exact (moduleCone_homology_mor₁ A f M n).symm)
  have hm : Mono (HomologySequence.δ T (-1) 0) :=
    (HomologySequence.exact₃ T hT (-1) 0).mono_g_iff.mpr
      ((single_homology_isZero A M (-1) 0 (by omega)).eq_of_src _ _)
  have : Mono S.f :=
    inferInstanceAs (Mono (HomologySequence.δ T (-1) 0 ≫ (singleHomology A 0 M).hom))
  exact ⟨ha, ⟨he.fIsKernel⟩⟩

private noncomputable def moduleTorsionStageIso (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) (n : ℕ) :
    (homology A (-1)).obj (moduleConeTriangle A f M n).obj₃ ≅
      kernel (powerMultiplication A M (f ^ (n + 1))) :=
  (moduleTorsionStage_kernel A f M n).choose_spec.some.conePointUniqueUpToIso
    (limit.isLimit _)

@[reassoc]
private lemma moduleTorsionStageIso_ι (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) (n : ℕ) :
    (moduleTorsionStageIso A f M n).hom ≫ kernel.ι (powerMultiplication A M (f ^ (n + 1))) =
      (homology A 0).homologySequenceδ (moduleConeTriangle A f M n) (-1) 0 (by omega) ≫
        (singleHomology A 0 M).hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

set_option backward.isDefEq.respectTransparency false in
private lemma moduleQuotientStage_cokernel (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) (n : ℕ) :
    let T := moduleConeTriangle A f M n
    let b := (singleHomology A 0 M).inv ≫ (homology A 0).map T.mor₂
    ∃ h : powerMultiplication A M (f ^ (n + 1)) ≫ b = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ b h)) := by
  intro T b
  have hT : T ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished _
  have hm : powerMultiplication A M (f ^ (n + 1)) ≫ (singleHomology A 0 M).inv =
      (singleHomology A 0 M).inv ≫ (homology A 0).map T.mor₁ := by
    rw [← cancel_epi (singleHomology A 0 M).hom, ← Category.assoc,
      ← moduleCone_homology_mor₁]
    simp only [Functor.comp_obj, Functor.id_obj, Iso.app_hom, Iso.app_inv, Category.assoc,
      Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, T]
    exact Category.comp_id _
  have hb : powerMultiplication A M (f ^ (n + 1)) ≫ b = 0 := by
    dsimp only [b]
    rw [← Category.assoc, hm, Category.assoc, ← Functor.map_comp,
      comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero, comp_zero]
  let S := ShortComplex.mk (powerMultiplication A M (f ^ (n + 1))) b hb
  have he : S.Exact := by
    apply ShortComplex.exact_of_iso _ (HomologySequence.exact₂ T hT 0)
    exact ShortComplex.isoMk (singleHomology A 0 M) (singleHomology A 0 M) (Iso.refl _)
      (by exact (moduleCone_homology_mor₁ A f M n).symm) (by simp [S, b])
  have := moduleCone_homology_mor₂_epi A f M n
  have : Epi S.g :=
    inferInstanceAs (Epi ((singleHomology A 0 M).inv ≫ (homology A 0).map T.mor₂))
  exact ⟨hb, ⟨he.gIsCokernel⟩⟩

private noncomputable def moduleQuotientStageIso (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) (n : ℕ) :
    (homology A 0).obj (moduleConeTriangle A f M n).obj₃ ≅
      cokernel (powerMultiplication A M (f ^ (n + 1))) :=
  (moduleQuotientStage_cokernel A f M n).choose_spec.some.coconePointUniqueUpToIso
    (colimit.isColimit _)

@[reassoc]
private lemma moduleQuotientStageIso_π (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) (n : ℕ) :
    (singleHomology A 0 M).inv ≫ (homology A 0).map (moduleConeTriangle A f M n).mor₂ ≫
        (moduleQuotientStageIso A f M n).hom =
      cokernel.π (powerMultiplication A M (f ^ (n + 1))) :=
  by
    rw [← Category.assoc]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (moduleQuotientStage_cokernel A f M n).choose_spec.some
      (colimit.isColimit _) WalkingParallelPair.one

private noncomputable def moduleConeTransition (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) (n : ℕ) :
    moduleConeTriangle A f M (n + 1) ⟶ moduleConeTriangle A f M n :=
  DerivedCategory.Q.mapTriangle.map
    (CochainComplex.mappingCone.triangleMap _ _ (f • 𝟙 (moduleComplex A M)) (𝟙 _)
      (by simp [comp_smul, smul_smul, pow_succ', mul_comm]))

set_option backward.isDefEq.respectTransparency false in
private lemma moduleTorsionStageIso_naturality (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) (n : ℕ) :
    (moduleTower A f M ⋙ DerivedCategory.Q ⋙ homology A (-1)).map
        (homOfLE (Nat.le_succ n)).op ≫ (moduleTorsionStageIso A f M n).hom =
      (moduleTorsionStageIso A f M (n + 1)).hom ≫ powerTorsionTransition A M f n := by
  apply (cancel_mono (kernel.ι (powerMultiplication A M (f ^ (n + 1))))).1
  simp only [Category.assoc, moduleTorsionStageIso_ι, powerTorsionTransition_ι,
    moduleTorsionStageIso_ι_assoc]
  have h := (homology A 0).homologySequenceδ_naturality (moduleConeTransition A f M n)
    (-1) 0 (by omega)
  have hs : (homology A 0).map (moduleConeTransition A f M n).hom₁ ≫
      (singleHomology A 0 M).hom =
        (singleHomology A 0 M).hom ≫ powerMultiplication A M f := by
    have hh := moduleCone_homology_mor₁ A f M 0
    change (homology A 0).map (DerivedCategory.Q.map (f ^ (0 + 1) • 𝟙 _)) ≫ _ = _ at hh
    simpa only [moduleConeTransition, CochainComplex.mappingCone.triangleMap_hom₁,
      Functor.mapTriangle_map_hom₁, Nat.zero_add, pow_one] using hh
  simp only [homology, shift_homologyFunctor] at h
  rw [← hs, ← reassoc_of% h]
  congr 2
  dsimp [moduleTower, principalComplexSystem, moduleConeTransition]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

private noncomputable def moduleTorsionIso (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) :
    moduleTower A f M ⋙ DerivedCategory.Q ⋙ homology A (-1) ≅ powerTorsionSystem A M f := by
  let e : moduleTower A f M ⋙ DerivedCategory.Q ⋙ homology A (-1) ⟶ powerTorsionSystem A M f :=
    NatTrans.ofOpSequence (fun n => (moduleTorsionStageIso A f M n).hom) (fun n => by
      rw [powerTorsionSystem_map_succ]
      exact moduleTorsionStageIso_naturality A f M n)
  exact NatIso.ofComponents (fun n => moduleTorsionStageIso A f M n.unop)
    (fun h => e.naturality h)

set_option backward.isDefEq.respectTransparency false in
private lemma moduleQuotientStageIso_naturality (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) (n : ℕ) :
    (moduleTower A f M ⋙ DerivedCategory.Q ⋙ homology A 0).map
        (homOfLE (Nat.le_succ n)).op ≫ (moduleQuotientStageIso A f M n).hom =
      (moduleQuotientStageIso A f M (n + 1)).hom ≫ powerQuotientTransition A M f n := by
  have := moduleCone_homology_mor₂_epi A f M (n + 1)
  apply (cancel_epi ((singleHomology A 0 M).inv ≫
    (homology A 0).map (moduleConeTriangle A f M (n + 1)).mor₂)).1
  simp only [Category.assoc]
  rw [reassoc_of% (moduleQuotientStageIso_π A f M (n + 1)),
    π_powerQuotientTransition]
  have h := (moduleConeTransition A f M n).comm₂
  have h₂ : (moduleConeTransition A f M n).hom₂ = 𝟙 _ := by
    change DerivedCategory.Q.map (𝟙 (moduleComplex A M)) = 𝟙 _
    exact DerivedCategory.Q.map_id _
  rw [h₂, Category.id_comp] at h
  have hm : (moduleConeTriangle A f M (n + 1)).mor₂ ≫
      DerivedCategory.Q.map ((moduleTower A f M).map (homOfLE (Nat.le_succ n)).op) =
        (moduleConeTriangle A f M n).mor₂ := by
    simpa [moduleConeTransition, moduleTower, principalComplexSystem,
      Functor.ofOpSequence_map_homOfLE_succ, CategoryTheory.Functor.map_id] using h
  change (singleHomology A 0 M).inv ≫ (homology A 0).map _ ≫
      (homology A 0).map _ ≫ _ = _
  rw [← Functor.map_comp_assoc, hm, moduleQuotientStageIso_π]

private noncomputable def moduleQuotientIso (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) :
    moduleTower A f M ⋙ DerivedCategory.Q ⋙ homology A 0 ≅ powerQuotientSystem A M f := by
  let e : moduleTower A f M ⋙ DerivedCategory.Q ⋙ homology A 0 ⟶ powerQuotientSystem A M f :=
    NatTrans.ofOpSequence (fun n => (moduleQuotientStageIso A f M n).hom) (fun n => by
      rw [powerQuotientSystem_map_succ]
      exact moduleQuotientStageIso_naturality A f M n)
  exact NatIso.ofComponents (fun n => moduleQuotientStageIso A f M n.unop)
    (fun h => e.naturality h)

public lemma moduleDifference_naturality (A : Type u) [CommRing A]
    {E E' : ℕᵒᵖ ⥤ ModuleCat.{v} A} (e : E ≅ E') :
    moduleDifference A E ≫ (Pi.mapIso (fun n : ℕ => e.app ⟨n⟩)).hom =
      (Pi.mapIso (fun n : ℕ => e.app ⟨n⟩)).hom ≫ moduleDifference A E' := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.mapIso_hom_π, moduleDifference,
    Pi.lift_comp_π_assoc, Pi.lift_comp_π, comp_sub, sub_comp, Pi.mapIso_hom_π_assoc]
  simp only [Iso.app_hom]
  rw [e.hom.naturality]

public noncomputable def firstDerivedLimitIso (A : Type u) [CommRing A]
    {E E' : ℕᵒᵖ ⥤ ModuleCat.{v} A} (e : E ≅ E') :
    firstDerivedLimit A E ≅ firstDerivedLimit A E' :=
  cokernel.mapIso _ _ (Pi.mapIso (fun n : ℕ => e.app ⟨n⟩))
    (Pi.mapIso (fun n : ℕ => e.app ⟨n⟩)) (moduleDifference_naturality A e)

@[reassoc]
public lemma firstDerivedLimitIso_π (A : Type u) [CommRing A]
    {E E' : ℕᵒᵖ ⥤ ModuleCat.{v} A} (e : E ≅ E') :
    cokernel.π (moduleDifference A E) ≫ (firstDerivedLimitIso A e).hom =
      (Pi.mapIso (fun n : ℕ => e.app ⟨n⟩)).hom ≫ cokernel.π (moduleDifference A E') := by
  exact cokernel.π_desc _ _ _

private lemma moduleProduct_isZero (A : Type u) [CommRing A]
    (E : ℕᵒᵖ ⥤ ModuleCat.{v} A) (h : ∀ n, IsZero (E.obj n)) :
    IsZero (moduleProduct A E) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Pi.hom_ext
  intro n
  exact (h ⟨n⟩).eq_of_tgt _ _

private lemma moduleLimit_isZero (A : Type u) [CommRing A]
    (E : ℕᵒᵖ ⥤ ModuleCat.{v} A) (h : ∀ n, IsZero (E.obj n)) :
    IsZero (limit E) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply limit.hom_ext
  intro n
  exact (h n).eq_of_tgt _ _

private lemma firstDerivedLimit_isZero (A : Type u) [CommRing A]
    (E : ℕᵒᵖ ⥤ ModuleCat.{v} A) (h : ∀ n, IsZero (E.obj n)) :
    IsZero (firstDerivedLimit A E) := by
  have hp := moduleProduct_isZero A E h
  have : Epi (moduleDifference A E) := ⟨fun _ _ _ => hp.eq_of_src _ _⟩
  exact isZero_cokernel_of_epi _

private lemma moduleCone_homology_isZero (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) (n : ℕ) (r : ℤ) (hr : r ≠ -1) (hr' : r ≠ 0) :
    IsZero ((homology A r).obj (moduleConeTriangle A f M n).obj₃) := by
  exact (HomologySequence.exact₃ _ (DerivedCategory.mappingCone_triangle_distinguished _)
    r (r + 1)).isZero_of_both_isZero (single_homology_isZero A M r 0 hr')
      (single_homology_isZero A M (r + 1) 0 (by omega))

private noncomputable def moduleTateComparison (A : Type u) [CommRing A]
    (f : A) (F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A))
    (η : 𝟭 _ ⟶ F) (c : CompletionComparison A f F η) (M : ModuleCat.{v} A) :
    { e : (homology A (-1)).obj (F.obj ((single A 0).obj M)) ≅ adicTateModule A M f //
      ∀ n : ℕ, e.hom ≫ limit.π (powerTorsionSystem A M f) ⟨n⟩ =
        (homology A (-1)).map ((c.iso (moduleComplex A M)).hom ≫
          (milnorTriangle A (moduleTower A f M)).mor₁ ≫ DerivedCategory.Q.map
            (Pi.π (fun n : ℕ => (moduleTower A f M).obj ⟨n⟩) n)) ≫
              (moduleTorsionIso A f M).hom.app ⟨n⟩ } := by
  classical
  apply Classical.choice
  obtain ⟨i, q, w, hi, hq, hs⟩ := milnorTriangle_homology_shortExact A (moduleTower A f M) (-1)
  have hz : IsZero (firstDerivedLimit A
      (moduleTower A f M ⋙ DerivedCategory.Q ⋙ homology A (-1 - 1))) :=
    firstDerivedLimit_isZero A _ (fun n => moduleCone_homology_isZero A f M n.unop _
      (by omega) (by omega))
  have : IsIso q := hs.isIso_g_iff.mpr hz
  refine ⟨⟨(homology A (-1)).mapIso (c.iso (moduleComplex A M)) ≪≫ asIso q ≪≫
      lim.mapIso (moduleTorsionIso A f M), ?_⟩⟩
  intro n
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Category.assoc,
    lim_map, limMap_π, reassoc_of% (hq n), Functor.map_comp]

private lemma productIso_cokernel_firstDerivedLimitIso (A : Type u) [CommRing A]
    {E E' : ℕᵒᵖ ⥤ ModuleCat.{v} A} (e : E ≅ E') {P : ModuleCat.{v} A}
    (eP : P ≅ moduleProduct A E) {Z : ModuleCat.{v} A} (g : firstDerivedLimit A E ⟶ Z) :
    (eP ≪≫ Pi.mapIso (fun n : ℕ => e.app ⟨n⟩)).hom ≫ cokernel.π (moduleDifference A E') ≫
      (firstDerivedLimitIso A e).inv ≫ g = eP.hom ≫ cokernel.π (moduleDifference A E) ≫ g := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [← firstDerivedLimitIso_π_assoc, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def principalModuleSequence (A : Type u) [CommRing A]
    (f : A) (F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A))
    (η : 𝟭 _ ⟶ F) (c : CompletionComparison A f F η) (M : ModuleCat.{v} A) :
    ModuleCompletionSequence A f F η c M := by
  classical
  apply Classical.choice
  obtain ⟨i, q, w, hi, hq, hs⟩ := milnorTriangle_homology_shortExact A (moduleTower A f M) 0
  let eT := moduleTorsionIso A f M
  let eQ := moduleQuotientIso A f M
  let eP := complexHomologyProductIso A (fun n : ℕ => (moduleTower A f M).obj ⟨n⟩) (-1)
  let eD := firstDerivedLimitIso A eT
  let eL := lim.mapIso eQ
  let eC := (homology A 0).mapIso (c.iso (moduleComplex A M))
  let i' := eD.inv ≫ i ≫ eC.inv
  let q' := eC.hom ≫ q ≫ eL.hom
  have w' : i' ≫ q' = 0 := by simp [i', q', reassoc_of% w]
  refine ⟨{
    torsionIso := eT
    quotientIso := eQ
    torsionIso_ι := fun n => moduleTorsionStageIso_ι A f M n
    π_quotientIso := fun n => moduleQuotientStageIso_π A f M n
    productIso := eP ≪≫ Pi.mapIso (fun n : ℕ => eT.app ⟨n⟩)
    productIso_π := ?_
    tateIso := (moduleTateComparison A f F η c M).val
    tateIso_π := (moduleTateComparison A f F η c M).property
    inclusion := i'
    projection := q'
    connecting_inclusion := ?_
    projection_π := ?_
    zero := w'
    shortExact := ?_ }⟩
  · intro n
    simp only [Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π,
      complexHomologyProductIso_π_assoc, eP, Iso.app_hom]
  · exact (productIso_cokernel_firstDerivedLimitIso A eT eP (i ≫ eC.inv)).trans
      ((reassoc_of% hi) eC.inv)
  · intro n
    simp only [q', eL, Functor.mapIso_hom, Category.assoc, lim_map, limMap_π,
      reassoc_of% (hq n), eC, Functor.map_comp]
  · apply ShortComplex.shortExact_of_iso _ hs
    exact ShortComplex.isoMk eD eC.symm eL (by simp [i']) (by simp [q'])

private noncomputable def moduleSingleHomologyIso (A : Type u) [CommRing A]
    (E : ℕᵒᵖ ⥤ ModuleCat.{v} A) :
    E ⋙ CochainComplex.singleFunctor (ModuleCat.{v} A) 0 ⋙ DerivedCategory.Q ⋙ homology A 0 ≅ E :=
  Functor.isoWhiskerLeft E (singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0)

private noncomputable def firstDerivedLimitComparison (A : Type u) [CommRing A]
    (E : ℕᵒᵖ ⥤ ModuleCat.{v} A) : FirstDerivedLimitComparison A E := by
  classical
  apply Classical.choice
  let C := E ⋙ CochainComplex.singleFunctor (ModuleCat.{v} A) 0
  obtain ⟨i, q, w, hi, hq, hs⟩ := milnorTriangle_homology_shortExact A C 1
  let e := moduleSingleHomologyIso A E
  let eD := firstDerivedLimitIso A e
  let eP := complexHomologyProductIso A (fun n : ℕ => C.obj ⟨n⟩) 0
  have hz : IsZero (limit (C ⋙ DerivedCategory.Q ⋙ homology A 1)) :=
    moduleLimit_isZero A _ (fun n => single_homology_isZero A (E.obj n) 1 0 (by omega))
  have : IsIso i := hs.isIso_f_iff.mpr hz
  refine ⟨{
    productIso := eP ≪≫ Pi.mapIso (fun n : ℕ => e.app ⟨n⟩)
    productIso_π := ?_
    iso := (asIso i).symm ≪≫ eD
    connecting_iso := ?_ }⟩
  · intro n
    simp only [Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π,
      complexHomologyProductIso_π_assoc, eP]
    rfl
  · exact (productIso_cokernel_firstDerivedLimitIso A e eP i).trans hi

private lemma moduleDifference_epi (A : Type u) [CommRing A]
    (E : ℕᵒᵖ ⥤ ModuleCat.{v} A) (h : ∀ n, Epi (E.map (homOfLE (Nat.le_succ n)).op)) :
    Epi (moduleDifference A E) := by
  let X := fun n : ℕ => E.obj ⟨n⟩
  let t := fun n : ℕ => E.map (homOfLE (Nat.le_succ n)).op
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro y
  obtain ⟨x, hx⟩ := Stacks.InverseSystem.surjective_pi_sub_shift (fun n => t n)
    (fun n => (ModuleCat.epi_iff_surjective (t n)).mp (h n))
    ((ModuleCat.piIsoPi X).hom y)
  refine ⟨(ModuleCat.piIsoPi X).inv x, ?_⟩
  apply (ModuleCat.piIsoPi X).toLinearEquiv.injective
  funext n
  change ((moduleDifference A E ≫ Pi.π X n) ((ModuleCat.piIsoPi X).inv x)) = _
  rw [moduleDifference, Pi.lift_comp_π]
  change (Pi.π X n) ((ModuleCat.piIsoPi X).inv x) -
    (t n) ((Pi.π X (n + 1)) ((ModuleCat.piIsoPi X).inv x)) =
      (ModuleCat.piIsoPi X).hom y n
  rw [ModuleCat.piIsoPi_inv_kernel_ι_apply, ModuleCat.piIsoPi_inv_kernel_ι_apply]
  exact congrFun hx n

private lemma quotient_firstDerivedLimit_isZero (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) : IsZero (firstDerivedLimit A (powerQuotientSystem A M f)) := by
  have : Epi (moduleDifference A (powerQuotientSystem A M f)) :=
    moduleDifference_epi A _ (fun n => by
      rw [powerQuotientSystem_map_succ]
      have hπ : Epi (cokernel.π (powerMultiplication A M (f ^ (n + 1)))) := inferInstance
      exact @epi_of_epi_fac _ _ _ _ _ _ _ _ hπ (π_powerQuotientTransition A M f n))
  exact isZero_cokernel_of_epi _

private lemma quotientDerivedLimit_homology_isZero (A : Type u) [CommRing A]
    (f : A) (M : ModuleCat.{v} A) :
    IsZero ((homology A 1).obj (moduleDerivedLimit A (powerQuotientSystem A M f))) :=
  (quotient_firstDerivedLimit_isZero A f M).of_iso
    (firstDerivedLimitComparison A (powerQuotientSystem A M f)).iso

private lemma moduleCompletion_homology_isZero (A : Type u) [CommRing A]
    (f : A) (F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A))
    (η : 𝟭 _ ⟶ F) (c : CompletionComparison A f F η) (M : ModuleCat.{v} A)
    (r : ℤ) (hr : r ≠ -1) (hr' : r ≠ 0) :
    IsZero ((homology A r).obj (F.obj ((single A 0).obj M))) := by
  apply IsZero.of_iso _ ((homology A r).mapIso (c.iso (moduleComplex A M)))
  obtain ⟨i, q, w, hi, hq, hs⟩ := milnorTriangle_homology_shortExact A (moduleTower A f M) r
  apply hs.exact.isZero_of_both_isZero
  · by_cases h : r = 1
    · subst r
      exact (quotient_firstDerivedLimit_isZero A f M).of_iso
        (firstDerivedLimitIso A (moduleQuotientIso A f M))
    · exact firstDerivedLimit_isZero A _ (fun n =>
        moduleCone_homology_isZero A f M n.unop _ (by omega) (by omega))
  · exact moduleLimit_isZero A _ (fun n => moduleCone_homology_isZero A f M n.unop r hr hr')

end CompletionSequences
end

end
