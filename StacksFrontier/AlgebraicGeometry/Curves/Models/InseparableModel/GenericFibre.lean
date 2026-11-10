module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.Regular
public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.ChartGenericFibre
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreFiltration
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RationalPointSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModulePoints
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# A regular model with an inseparable component: the generic fibre

The generic fibre `X_K` of the model of `Stacks.Models.InseparableModel` is a smooth projective
curve over `K` with `H⁰(X_K, 𝒪) = K`.

## Main results

* `Stacks.Models.InseparableModel.isCurve_genericFibre`: `X_K` is a curve over `K`.
* `Stacks.Models.InseparableModel.smooth_genericFibre`: `X_K` is smooth over `K`.
* `Stacks.Models.InseparableModel.isHProjective_genericFibre`: `X_K` is H-projective over `K`.
* `Stacks.Models.InseparableModel.isIso_globalSections_genericFibre`: `H⁰(X_K, 𝒪) = K`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace Stacks.Models.InseparableModel

/-- The generic fibre `X_K`. -/
abbrev genericFibre : Scheme := pullback X_to_R (Spec.map (CommRingCat.ofHom (algebraMap R K)))

/-- The structure morphism `X_K ⟶ Spec K`. -/
abbrev genericFibreToK : genericFibre ⟶ Spec (.of K) := pullback.snd _ _

/-! ### The charts of the generic fibre -/

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projection `X_K ⟶ X`. -/
private abbrev genericFibreToX : genericFibre ⟶ XR := pullback.fst _ _

/-- The chart of `X_K` over the chart `D₊(z)` of `X`. -/
private abbrev chartK (c : Fin 3) : Scheme := pullback genericFibreToX (chartι c)

/-- The open immersion of a chart of `X_K`. -/
private abbrev chartKι (c : Fin 3) : chartK c ⟶ genericFibre := pullback.fst _ _

private instance isIso_ofHom_chartEquiv (c : Fin 3) :
    IsIso (CommRingCat.ofHom (chartEquiv c).toRingHom) :=
  ⟨⟨CommRingCat.ofHom (chartEquiv c).symm.toRingHom,
    CommRingCat.hom_ext (RingHom.ext fun r => (chartEquiv c).symm_apply_apply r),
    CommRingCat.hom_ext (RingHom.ext fun r => (chartEquiv c).apply_symm_apply r)⟩⟩

private theorem isPullback_chartK (c : Fin 3) :
    IsPullback (chartKι c ≫ genericFibreToK)
      (pullback.snd genericFibreToX (chartι c) ≫
        Spec.map (CommRingCat.ofHom (chartEquiv c).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (chartRing c)))) := by
  have h := (IsPullback.paste_vert (IsPullback.of_hasPullback genericFibreToX (chartι c)).flip
    (IsPullback.of_hasPullback X_to_R (Spec.map (CommRingCat.ofHom (algebraMap R K))))).flip
  rw [chartι_comp_X_to_R, awayBase_eq,
    CommRingCat.ofHom_comp (algebraMap R (chartRing c)) (chartEquiv c).toRingHom,
    Spec.map_comp] at h
  refine h.of_iso (Iso.refl _) (Iso.refl _)
    (asIso (Spec.map (CommRingCat.ofHom (chartEquiv c).toRingHom))) (Iso.refl _) ?_ ?_ ?_ ?_ <;>
    simp

/-- **A chart of `X_K` is `Spec (K ⊗_R R[s][T] ⧸ (x T - y))` over `Spec K`.** -/
private noncomputable def chartKIso (c : Fin 3) :
    chartK c ≅ Spec (.of (K ⊗[R] chartRing c)) :=
  (isPullback_chartK c).isoPullback ≪≫ pullbackSpecIso R K (chartRing c)

private theorem chartKIso_hom_comp (c : Fin 3) :
    (chartKIso c).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] chartRing c))) =
      chartKι c ≫ genericFibreToK := by
  rw [chartKIso, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst',
    IsPullback.isoPullback_hom_fst]

private instance (c : Fin 3) : IsDomain (K ⊗[R] chartRing c) := isDomain_tensor_chartRing c

private instance isIntegral_chartK (c : Fin 3) : IsIntegral (chartK c) :=
  haveI : Nonempty (chartK c) := ⟨(chartKIso c).inv (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _)⟩
  isIntegral_of_isOpenImmersion (chartKIso c).hom

private theorem iSup_opensRange_chartKι : ⨆ c, (chartKι c).opensRange = ⊤ := by
  simp only [Scheme.Hom.opensRange_pullbackFst, opensRange_chartι]
  rw [← Scheme.Hom.preimage_iSup, iSup_basicOpen_chartVar, Scheme.Hom.preimage_top]

private theorem exists_chartKι_eq (x : genericFibre) : ∃ c y, chartKι c y = x := by
  have hx : x ∈ (⊤ : genericFibre.Opens) := trivial
  rw [← iSup_opensRange_chartKι, TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨c, y, hy⟩ := hx
  exact ⟨c, y, hy⟩

/-! ### A point lying on all three charts -/

/-- The values `(π, 1 - t, π, 1 - t)` of the coordinates at an `R`-point of `X`. -/
private def ptVal : Fin 4 → R := ![π, 1 - tR, π, 1 - tR]

private theorem ptVal_ne_zero (i : Fin 4) : ptVal i ≠ 0 := by
  have hπ : π ≠ 0 := irreducible_π.ne_zero
  have ht : (1 : R) - tR ≠ 0 := by
    intro h
    have h' := congrArg (PowerSeries.constantCoeff (R := k)) h
    simp only [map_sub, map_one, tR, PowerSeries.constantCoeff_C, map_zero] at h'
    exact pow_two_ne_t 1 (by rw [one_pow]; exact (sub_eq_zero.mp h'))
  fin_cases i <;> simp [ptVal, hπ, ht]

/-- Evaluation of `A` at the point `(π, 1 - t, π, 1 - t)`. -/
private def ptEval : A →+* R :=
  Ideal.Quotient.lift J.toIdeal (MvPolynomial.eval ptVal) (by
    intro a ha
    change a ∈ Ideal.span gens at ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro q (rfl | rfl | rfl) <;>
        simp [q₀, q₁, q₂, ptVal] <;> ring
    · simp
    · intro x y _ _ hx hy; simp [hx, hy]
    · intro r x _ hx; simp [hx])

private theorem ptEval_zA (i : Fin 4) : ptEval (zA i) = ptVal i := by
  simp [ptEval, zA]

private theorem isLocalizationElem_ne_zero (c : Fin 3) :
    HomogeneousLocalization.Away.isLocalizationElem (zA_mem (chartVar 0)) (zA_mem (chartVar c))
      ≠ 0 := by
  intro h
  have h' := congrArg HomogeneousLocalization.val h
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at h'
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := h'
  have := congrArg ptEval hm
  simp only [map_mul, map_pow, ptEval_zA, map_zero] at this
  exact mul_ne_zero (pow_ne_zero _ (ptVal_ne_zero _)) (pow_ne_zero _ (ptVal_ne_zero _)) this

private instance : IsDomain (Away 0) :=
  haveI := isDomain_chartRing 0
  (chartEquiv 0).symm.injective.isDomain _

/-- The generic point of the chart `D₊(z₀₀)`. -/
private def chartZeroPt : Spec (.of (Away 0)) := ⟨⊥, Ideal.isPrime_bot⟩

private theorem chartι_chartZeroPt_mem (c : Fin 3) :
    chartι 0 chartZeroPt ∈ Set.range (chartι c) := by
  have h : chartZeroPt ∈ chartι 0 ⁻¹ᵁ Proj.basicOpen grading (zA (chartVar c)) := by
    rw [chartι, Proj.awayι_preimage_basicOpen grading (zA_mem (chartVar 0)) Nat.one_pos
      (zA_mem (chartVar c)) Nat.one_pos]
    exact isLocalizationElem_ne_zero c
  rw [← opensRange_chartι] at h
  exact h

private theorem exists_mem_range_chartKι :
    ∃ z : genericFibre, ∀ c, z ∈ Set.range (chartKι c) := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := X_to_R)
    (g := Spec.map (CommRingCat.ofHom (algebraMap R K))) (chartι 0 chartZeroPt)
    (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K)) (by
      rw [← Scheme.Hom.comp_apply, chartι_comp_X_to_R]
      refine PrimeSpectrum.ext ?_
      change Ideal.comap (awayBase 0) ⊥ = Ideal.comap (algebraMap R K) ⊥
      rw [← RingHom.ker_eq_comap_bot, ← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K),
        (RingHom.injective_iff_ker_eq_bot _).mp]
      intro a b hab
      rw [← chartEquiv_algebraMap, ← chartEquiv_algebraMap] at hab
      exact injective_algebraMap_chartRing 0 ((chartEquiv 0).injective hab))
  refine ⟨z, fun c => ?_⟩
  rw [IsOpenImmersion.range_pullbackFst]
  change genericFibreToX z ∈ Set.range (chartι c)
  rw [hz]
  exact chartι_chartZeroPt_mem c

/-! ### The generic fibre -/

/-- The open cover of `X_K` by its three charts. -/
private def chartCover : genericFibre.OpenCover :=
  Scheme.Cover.mkOfCovers (Fin 3) chartK chartKι exists_chartKι_eq

private instance isReduced_genericFibre : IsReduced genericFibre :=
  haveI : ∀ i : chartCover.I₀, IsReduced (chartCover.X i) := fun (c : Fin 3) =>
    isReduced_of_isIntegral (X := chartK c)
  IsReduced.of_openCover (𝒰 := chartCover)

private instance irreducibleSpace_genericFibre : IrreducibleSpace genericFibre := by
  obtain ⟨z, hz⟩ := exists_mem_range_chartKι
  have hirr (c : Fin 3) : IsIrreducible (Set.range (chartKι c)) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (chartK c)).image _
      (chartKι c).continuous.continuousOn
  have hsub (c : Fin 3) : Set.range (chartKι c) ⊆ closure (Set.range (chartKι 0)) :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen (hirr c).2
      (chartKι 0).isOpenEmbedding.isOpen_range ⟨z, hz c, hz 0⟩).trans
      (closure_mono Set.inter_subset_right)
  have huniv : closure (Set.range (chartKι 0)) = Set.univ :=
    Set.eq_univ_of_forall fun x => by
      obtain ⟨c, y, rfl⟩ := exists_chartKι_eq x
      exact hsub c ⟨y, rfl⟩
  rw [irreducibleSpace_def, Set.top_eq_univ, ← huniv]
  exact (hirr 0).closure

/-- The generic fibre `X_K` is an integral scheme. -/
instance isIntegral_genericFibre : IsIntegral genericFibre :=
  isIntegral_of_irreducibleSpace_of_isReduced _

private theorem topologicalKrullDim_range_chartKι (c : Fin 3) :
    topologicalKrullDim (Set.range (chartKι c)) = 1 := by
  rw [← IsHomeomorph.topologicalKrullDim_eq _
      (chartKι c).isOpenEmbedding.isEmbedding.toHomeomorph.isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ (chartKIso c).hom.homeomorph.isHomeomorph]
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans
    (ringKrullDim_tensor_chartRing c)

/-- The generic fibre `X_K` has Krull dimension `1`. -/
theorem topologicalKrullDim_genericFibre : topologicalKrullDim genericFibre = 1 := by
  refine le_antisymm ?_ ?_
  · rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    refine iSup_le fun x => ?_
    obtain ⟨c, y, rfl⟩ := exists_chartKι_eq x
    unfold TopologicalSpace.localKrullDim
    exact iInf_le_of_le (Set.range (chartKι c)) (iInf_le_of_le
      (chartKι c).isOpenEmbedding.isOpen_range (iInf_le_of_le (Set.mem_range_self y)
        (topologicalKrullDim_range_chartKι c).le))
  · rw [← topologicalKrullDim_range_chartKι 0]
    exact topologicalKrullDim_subspace_le _ _

/-- The structure morphism `X_K ⟶ Spec K` is proper. -/
instance isProper_genericFibreToK : IsProper genericFibreToK := by
  infer_instance

/-- The generic fibre `X_K` is a curve over `K`. -/
instance isCurve_genericFibre : IsCurve K genericFibreToK :=
  { toIsVariety := { }
    topologicalKrullDim_eq_one := topologicalKrullDim_genericFibre }

/-- The structure morphism `X_K ⟶ Spec K` is smooth. -/
instance smooth_genericFibre : Smooth genericFibreToK := by
  let : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover chartCover fun (c : Fin 3) => ?_
  change Smooth (chartKι c ≫ genericFibreToK)
  rw [← chartKIso_hom_comp]
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] chartRing c)))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr (smooth_tensor_chartRing c))
  infer_instance

/-- The structure morphism `X_K ⟶ Spec K` is H-projective. -/
theorem isHProjective_genericFibre : Stacks.HProjective.IsHProjective genericFibreToK :=
  (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper (f := genericFibreToK)).mpr
    ⟨Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral genericFibreToK
      topologicalKrullDim_genericFibre, inferInstance⟩

/-- The `K`-point of `X_K` given by the section of the model. -/
private def genericFibreSection : Spec (.of K) ⟶ genericFibre :=
  pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ modelSection) (𝟙 _)
    (by rw [Category.assoc, modelSection_comp_X_to_R, Category.comp_id, Category.id_comp])

/-- The map `K ⟶ Γ(X_K, 𝒪)` induced by the structure morphism is an isomorphism. -/
instance isIso_globalSections_genericFibre :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ genericFibreToK.appTop) :=
  isIso_globalSections_of_isField_of_isRationalPoint genericFibreToK
    (isField_globalSections_of_connectedSpace K genericFibreToK) _
    (isRationalPoint_base_of_comp_eq_id genericFibreToK
      (p := genericFibreSection) (pullback.lift_snd _ _ _)
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K))

end Stacks.Models.InseparableModel
