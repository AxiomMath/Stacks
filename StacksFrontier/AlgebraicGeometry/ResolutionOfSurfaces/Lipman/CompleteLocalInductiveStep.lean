module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.ModificationDegree
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.CompletionLocalDegree
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteLocalInduction
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties

/-!
# The inductive step of Tag 0BGN

Let `B → A` be a finite injective map of Noetherian complete local normal domains with `A` of
dimension two, and suppose `Spec B` has a resolution of singularities `Y ⟶ Spec B`. The proof of
[Stacks, Tag 0BGN] considers the normalization `X` of `Y ×_{Spec B} Spec A`: a normal
modification of `Spec A`, finite over `Y`, with finitely many singular points. At a singular
point `x` over `y ∈ Y` the completion of `𝒪_{X, x}` is finite over the regular complete local
ring `𝒪_{Y, y}^∧` of degree at most `[A : B]`, so has a resolution by normalized blowups by the
induction hypothesis; it descends to `𝒪_{X, x}` ([Stacks, Tags 0BGA and 0BG6]), and the local
resolutions assemble to one of `Spec A`.

## Main results

* `AlgebraicGeometry.exists_isResolution_of_intermediate_step`: the inductive step, the input
  `hstep` of `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_spec_of_isAdicComplete_of_inputs`.

## References

* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
* [Stacks Project, Tag 07N9](https://stacks.math.columbia.edu/tag/07N9)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- A morphism of integral schemes carrying the generic point to the generic point is dominant. -/
theorem isDominant_of_map_genericPoint {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y) : IsDominant f := by
  refine ⟨?_⟩
  rw [denseRange_iff_closure_range]
  refine Set.eq_univ_of_univ_subset ?_
  rw [← (genericPoint_spec Y)]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, h⟩)

/-- **Along a dominant morphism locally of finite type of integral schemes with algebraic
function field extension, the local rings do not grow in dimension** ([Stacks, Tag 02JU]). -/
theorem ringKrullDim_stalk_le_of_isAlgebraic {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    [IsLocallyNoetherian X] (h : Z ⟶ X) [LocallyOfFiniteType h] [IsDominant h]
    (halg : letI := (functionFieldMap h).toAlgebra
      Algebra.IsAlgebraic X.functionField Z.functionField) (z : Z) :
    ringKrullDim (Z.presheaf.stalk z) ≤ ringKrullDim (X.presheaf.stalk (h.base z)) := by
  have H := ringKrullDim_stalk_add_trdeg_residueField_le h z
  let : Algebra X.functionField Z.functionField := h.functionFieldMap.hom.toAlgebra
  have halg' : Algebra.IsAlgebraic X.functionField Z.functionField := by
    convert halg using 2
    exact (functionFieldMap_eq_hom_functionFieldMap h).symm
  rw [trdeg_eq_zero_iff.mpr halg'] at H
  simp only [map_zero, Nat.cast_zero, add_zero] at H
  exact le_trans (le_add_of_nonneg_right (by positivity)) H

/-- **The inductive step of the proof of [Stacks, Tag 0BGN].** Let `B → A` be a finite
injective map of Noetherian complete local normal domains with `A` of dimension two. If `Spec B`
has a resolution of singularities, and every Noetherian complete local normal domain `C` of
dimension two finite over a regular complete local ring `R` of dimension two with
`[C : R] ≤ [A : B]` has a resolution by normalized blowups, then `Spec A` has a resolution of
singularities. -/
theorem exists_isResolution_of_intermediate_step (B A : Type u) [CommRing B] [CommRing A]
    [IsNoetherianRing B] [IsLocalRing B] [IsNormalDomain B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] [IsNoetherianRing A] [IsLocalRing A]
    [IsNormalDomain A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Algebra B A]
    [Module.Finite B A] [FaithfulSMul B A] (hdimA : ringKrullDim A = 2)
    (hB : ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of B)), IsResolution g)
    (hsmaller : ∀ (R C : Type u) [CommRing R] [IsRegularLocalRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [CommRing C] [IsNoetherianRing C]
      [IsLocalRing C] [IsNormalDomain C] [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
      [Algebra R C] [Module.Finite R C] [FaithfulSMul R C], ringKrullDim R = 2 →
      Module.finrank R C ≤ Module.finrank B A → HasResolutionByNormalizedBlowUps (Spec (.of C))) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f := by
  obtain ⟨Y, g, hg⟩ := hB
  have hgmod : IsModification g := hg.isModification
  obtain ⟨X, f, π, hf, hXn, hπ, hcomm⟩ := exists_normal_modification_finite_over B A g hgmod
  have := hXn
  have : IsFinite π := hπ
  have : IsIntegral Y := hgmod.source_isIntegral
  have : IsIntegral X := hf.source_isIntegral
  have : IsProper f := hf.isProper
  have : IsProper g := hgmod.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  -- dimensions
  have hdimSA : topologicalKrullDim (Spec (.of A)) = ((2 : ℕ) : WithBot ℕ∞) :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans hdimA
  have hdimSB : topologicalKrullDim (Spec (.of B)) = ((2 : ℕ) : WithBot ℕ∞) :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B).trans
      ((Algebra.IsIntegral.ringKrullDim_eq B A).trans hdimA)
  have hdimX : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_eq_of_isModification f hf).trans hdimSA
  have hdimY : topologicalKrullDim Y = ((2 : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_eq_of_isModification g hgmod).trans hdimSB
  -- dominance and the degree of `π`
  have : IsDominant f := hf.isBirational.isDominant
  have : IsDominant g := hgmod.isBirational.isDominant
  let q : Spec (.of A) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom (algebraMap B A))
  have : IsDominant q := by
    refine isDominant_of_map_genericPoint q ?_
    rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext (Ideal.ext fun b => ?_)
    show b ∈ Ideal.comap (algebraMap B A) ⊥ ↔ b ∈ (⊥ : Ideal B)
    rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_bot,
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective B A)]
  have : IsDominant π := by
    refine isDominant_of_map_genericPoint π ?_
    have h1 : g.base (π.base (genericPoint X)) = genericPoint (Spec (.of B)) := by
      rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply,
        genericPoint_eq_of_isDominant f, genericPoint_eq_of_isDominant q]
    exact eq_genericPoint_of_map_eq_genericPoint_of_dim_eq g g.isClosedMap hdimY hdimSB h1
  have hdeg : letI := (functionFieldMap π).toAlgebra
      Module.finrank Y.functionField X.functionField = Module.finrank B A := by
    rw [finrank_functionField_eq_of_square π g f q hcomm hf.isBirational hgmod.isBirational]
    exact finrank_functionField_specMap B A
  have hpos : 0 < Module.finrank B A := by
    let := FractionRing.liftAlgebra B (FractionRing A)
    have : FiniteDimensional (FractionRing B) (FractionRing A) :=
      Stacks.ResolutionOfSurfaces.finiteDimensional_fractionRing B A
    rw [← IsFractionRing.finrank_eq B (FractionRing B) A (FractionRing A)]
    exact Module.finrank_pos
  have halg : let := (functionFieldMap π).toAlgebra
      Algebra.IsAlgebraic Y.functionField X.functionField := by
    let := (functionFieldMap π).toAlgebra
    have : Module.Finite Y.functionField X.functionField :=
      Module.finite_of_finrank_pos (hdeg ▸ hpos)
    infer_instance
  -- the singular locus
  have hAexc : IsExcellent A := (isExcellent_of_standard_classes_and_finiteType.{u, u}).2.1 A
  have hsing := finite_singularLocus_of_locallyOfFiniteType_of_isExcellent hAexc f hdimX.le
  refine exists_isResolution_of_isModification_of_singularLocus A f hf hdimA hsing
    fun x hx => ?_
  -- the local rings at `x` and at `y = π x`
  let O := X.presheaf.stalk x
  have : IsNormalDomain O := ⟨IsNormal.stalk_isDomain _, IsNormal.stalk_normal _⟩
  have hOexc : IsExcellent O := isExcellent_stalk_of_locallyOfFiniteType hAexc f x
  have hOdim : ringKrullDim O = 2 :=
    ringKrullDim_stalk_eq_two_of_mem_singularLocus X hdimX.le x hx
  have hOnormal : IsNormalRing (AdicCompletion (maximalIdeal O) O) :=
    isNormalRing_adicCompletion_of_isExcellent_of_isNormalRing O hOexc
      (IsNormalRing.of_isIntegrallyClosed O)
  obtain ⟨hdomC, hicC⟩ := hOnormal.of_isLocalRing
  let y := π.base x
  have : IsRegularLocalRing (Y.presheaf.stalk y) :=
    hg.source_isRegular.isRegularLocalRing_stalk y
  have hYdim : ringKrullDim (Y.presheaf.stalk y) = 2 := by
    refine le_antisymm ?_ (hOdim ▸ ringKrullDim_stalk_le_of_isAlgebraic π halg x)
    rw [ringKrullDim_stalk_eq_coheight]
    have hc := Order.coheight_le_krullDim y
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))] at hc
    exact hc.trans hdimY.le
  -- an affine open around `y` and its preimage
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hV : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  have hxV : x ∈ π ⁻¹ᵁ U := hyU
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨x, hxV⟩⟩
  let D := Γ(Y, U)
  let E := Γ(X, π ⁻¹ᵁ U)
  have : IsNoetherianRing D := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Algebra D E := (π.app U).hom.toAlgebra
  have : Module.Finite D E := RingHom.finite_algebraMap.mp (π.finite_app U hU)
  have : FaithfulSMul D E := by
    refine (faithfulSMul_iff_algebraMap_injective D E).mpr fun d₁ d₂ hd => ?_
    apply Scheme.germToFunctionField_injective Y U
    apply (functionFieldMap π).injective
    rw [functionFieldMap_eq_hom_functionFieldMap,
      π.functionFieldMap_germToFunctionField (U := U) (V := π ⁻¹ᵁ U) le_rfl,
      π.functionFieldMap_germToFunctionField (U := U) (V := π ⁻¹ᵁ U) le_rfl]
    simp only [Scheme.Hom.appLE, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
    exact congrArg _ hd
  -- the primes of `y` and `x`, and the local rings as localizations
  let pY := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal
  let qX := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : qX.LiesOver pY := by
    refine ⟨?_⟩
    have h := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (f := π) U hU (π ⁻¹ᵁ U) hV le_rfl hxV)
    rw [← π.app_eq_appLE] at h
    exact h.symm
  let Dp := Y.presheaf.stalk y
  let : Algebra D Dp := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hyU⟩
  have : IsLocalization.AtPrime Dp pY := hU.isLocalization_stalk ⟨y, hyU⟩
  let : Algebra E O := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have : IsLocalization.AtPrime O qX := hV.isLocalization_stalk ⟨x, hxV⟩
  let : Algebra Dp O := (π.stalkMap x).hom.toAlgebra
  let : Algebra D O := ((algebraMap E O).comp (algebraMap D E)).toAlgebra
  have : IsScalarTower D E O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower D Dp O := IsScalarTower.of_algebraMap_eq fun d =>
    (Scheme.Hom.germ_stalkMap_apply π U x hyU d).symm
  have : IsLocalHom (algebraMap Dp O) := inferInstanceAs (IsLocalHom (π.stalkMap x).hom)
  have hdim : ringKrullDim O = ringKrullDim Dp := hOdim.trans hYdim.symm
  have : IsRegularLocalRing (AdicCompletion (maximalIdeal Dp) Dp) :=
    isRegularLocalRing_iff_adicCompletion_maximalIdeal.mp inferInstance
  have : IsDomain (AdicCompletion (maximalIdeal Dp) Dp) := IsRegularLocalRing.isDomain _
  have : IsDomain (AdicCompletion (maximalIdeal O) O) := hdomC
  obtain ⟨hfin, hfaith, hle⟩ :=
    finite_faithfulSMul_finrank_le_adicCompletion_of_isLocalization D E pY qX Dp O hdim
  let := adicCompletionLocalAlgebra Dp O
  have hsec : Module.finrank D E = Module.finrank B A :=
    (finrank_sections_eq_finrank_functionField π U hU hV).trans hdeg
  have : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal Dp) Dp))
      (AdicCompletion (maximalIdeal Dp) Dp) :=
      AdicCompletion.isAdicComplete_of_fg (maximalIdeal Dp).fg_of_isNoetherianRing
  have : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal O) O))
      (AdicCompletion (maximalIdeal O) O) :=
      AdicCompletion.isAdicComplete_of_fg (maximalIdeal O).fg_of_isNoetherianRing
  have : IsNormalDomain (AdicCompletion (maximalIdeal O) O) := ⟨hdomC, hicC⟩
  have hR2 : ringKrullDim (AdicCompletion (maximalIdeal Dp) Dp) = 2 := by
    rw [IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal, hYdim]
  have hres := hsmaller (AdicCompletion (maximalIdeal Dp) Dp) (AdicCompletion (maximalIdeal O) O)
    hR2 (hle.trans hsec.le)
  exact hasResolutionByNormalizedBlowUps_of_adicCompletion O hOnormal
    IsNagataRing.of_isPrecomplete_maximalIdeal hres

end AlgebraicGeometry

end
