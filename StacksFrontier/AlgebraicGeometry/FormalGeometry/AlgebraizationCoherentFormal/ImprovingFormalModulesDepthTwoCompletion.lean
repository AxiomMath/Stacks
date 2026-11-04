module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthTwoAffine
public import StacksFrontier.RingTheory.LocalCohomology.CompletionTorsionComparison
public import StacksFrontier.RingTheory.LocalCohomology.FormalTorsionProZero
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantConsequences
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProIsoTransfer
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphismInterleaving
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphismSymm
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantNoetherianCompletion

/-!
# The local cohomology of the depth-one sections, read over the completion

Keep the notation of `ImprovingFormalModulesDepthTwoAffine.lean`: `U` is an affine open of `X`
with ring `A₀ = Γ(X, U)` and ideal `I₀ = ℐ(U)`, `(𝒢ₙ)` a model of the depth-one quotients
`(ℱ'ₙ)` in `Coh(X, ℐ)`, and `M_𝒢 = lim Γ(U, 𝒢ₙ)`. Let `A` be the `I₀`-adic completion of `A₀` and
`M_A` the `I₀`-adic completion of `M_𝒢`, a module over `A`.

Theorem [Stacks, Tag 0EIE] is stated over `A`, for the inverse system
`{H¹_{T'_A}(M_A / Iⁿ M_A)}`. The third paragraph of the proof of [Stacks, Tag 0EJF] reads it
over `A₀` for the system `{H¹_{T'}(M'ₙ)}`, `M'ₙ = Γ(U, ℱ'ₙ)`. This file is that reading: the two
systems are related by

* the pro-isomorphism `(M'ₙ) ≅ (Γ(U, 𝒢ₙ))` given by the model,
* the identifications `Γ(U, 𝒢ₙ) = M_𝒢/I₀^{n+1}M_𝒢 = M_A / (I₀A)^{n+1} M_A`, the latter because
  `M_𝒢` is complete,
* the comparison of local cohomology over `A₀` and over `A` for modules killed by a power of
  `I₀` (`Stacks.LocalCohomology.completionTorsionLocalCohomologyNatIso`),

so that essential constancy of the system over `A` gives essential constancy of the system over
`A₀`.

## Main results

* `Stacks.Algebraization.modelProIso`: the pro-isomorphism `(M'ₙ) ≅ (Γ(U, 𝒢ₙ))`.
* `Stacks.Algebraization.isEssentiallyConstantPro_localCohomologyOne_depthOneSections`: the
  transfer of essential constancy.

## References

* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open InverseSequence

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
  (hdual : HasDualizingComplexOnAffineCover X) (F : Stacks.Coherent.CoherentAdicSystems I)
  {T T' : Set X} (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
  (hTY : T ⊆ I.support) (hTT' : T' ⊆ T)
  (himm : ∀ x x' : X, x ∈ I.support → IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T)
  {U : X.Opens} (hU : IsAffineOpen U) (Mo : DepthOneAdicModel F hT)

/-! ### The pro-isomorphism given by the model -/

variable (U) in
/-- **The pro-isomorphism `(Γ(U, ℱ'ₙ)) ≅ (Γ(U, 𝒢ₙ))` given by a model of the depth-one
quotients.** -/
public def modelProIso :
    ProIso (improvedSystem T hT F.obj ⋙ sectionsOver U) (Mo.G.obj ⋙ sectionsOver U) where
  α := Mo.μ
  β := id
  αmono := Mo.monotone_μ
  βmono := monotone_id
  αle := Mo.le_μ
  βle _ := le_rfl
  φ m := (sectionsOver U).map (Mo.π m)
  ψ m := (sectionsOver U).map (Mo.κ.app (op m))
  φnat {m m'} h := by
    change (sectionsOver U).map ((improvedSystem T hT F.obj).map (homOfLE (Mo.monotone_μ h)).op) ≫
      (sectionsOver U).map (Mo.π m) =
      (sectionsOver U).map (Mo.π m') ≫ (sectionsOver U).map (Mo.G.obj.map (homOfLE h).op)
    rw [← Functor.map_comp, ← Functor.map_comp, Mo.map_π h]
  ψnat {m m'} h := by
    change (sectionsOver U).map (Mo.G.obj.map (homOfLE h).op) ≫
      (sectionsOver U).map (Mo.κ.app (op m)) =
      (sectionsOver U).map (Mo.κ.app (op m')) ≫
        (sectionsOver U).map ((improvedSystem T hT F.obj).map (homOfLE h).op)
    rw [← Functor.map_comp, ← Functor.map_comp, Mo.κ.naturality]
  ψφ m := by
    change (sectionsOver U).map (Mo.π m) ≫ (sectionsOver U).map (Mo.κ.app (op m)) =
      (sectionsOver U).map ((improvedSystem T hT F.obj).map _)
    rw [← Functor.map_comp, Mo.π_κ m]
  φψ m := by
    change (sectionsOver U).map (Mo.κ.app (op (Mo.μ m))) ≫ (sectionsOver U).map (Mo.π m) =
      (sectionsOver U).map (Mo.G.obj.map _)
    rw [← Functor.map_comp, Mo.κ_π m]

/-! ### The levels of `M_𝒢` as levels of its completion -/

section Completion

variable (G : Stacks.Coherent.CoherentAdicSystems I)

include hU in
/-- `M_𝒢` is `I₀`-adically complete. -/
theorem isAdicComplete_formalSectionsOver :
    IsAdicComplete (I.ideal ⟨U, hU⟩) (formalSectionsOver G U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  refine Stacks.Coherent.moduleLimit_isAdicComplete _ (fun k => ?_) (fun k => ?_)
    (Ideal.fg_of_isNoetherianRing _)
  · have : Epi (G.obj.map (homOfLE (Nat.le_succ k)).op) := G.property.epi_map_succ k
    have : ∀ k, (G.obj.obj (op k)).IsQuasicoherent := fun _ =>
      (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
    exact Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X _ U hU
  · exact Stacks.Coherent.adicInverseSystem_transition_ker (adicInverseSystemOf G) ⟨U, hU⟩ k

variable (U) in
/-- The completion `M_A` of `M_𝒢`, as a module over the completion of `Γ(X, U)`. -/
public abbrev completedFormalSections : Type u :=
  AdicCompletion (I.ideal ⟨U, hU⟩) (formalSectionsOver G U)

/-- The tower `n ↦ M_A / (I₀A)ⁿ M_A` of modules over the completion. -/
public abbrev completedFormalSectionsTower :
    ℕᵒᵖ ⥤ ModuleCat.{u} (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) :=
  Stacks.LocalCohomology.idealPowerQuotientTower.{u, u}
    ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))))
    (ModuleCat.of _ (completedFormalSections U hU G))

include hU in
omit [AlgebraicGeometry.IsNoetherian X] in
/-- The `I₀`-adic filtration of `M_A` read over `Γ(X, U)` is the `I₀A`-adic one. -/
theorem restrictScalars_pow_smul_top_completed (k : ℕ) :
    ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) ^ k •
        (⊤ : Submodule (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
          (completedFormalSections U hU G))).restrictScalars Γ(X, U) =
      I.ideal ⟨U, hU⟩ ^ k • (⊤ : Submodule Γ(X, U) (completedFormalSections U hU G)) := by
  ext p
  exact Stacks.LocalCohomology.mem_pow_smul_top_iff_mem_map_pow_smul_top _ k p

/-- The identification `M_𝒢 ≅ M_A`. -/
public def formalSectionsEquivCompleted :
    formalSectionsOver G U ≃ₗ[Γ(X, U)] completedFormalSections U hU G :=
  haveI := isAdicComplete_formalSectionsOver hU G
  AdicCompletion.ofLinearEquiv (I.ideal ⟨U, hU⟩) (formalSectionsOver G U)

variable (U) in
/-- The restriction of scalars from the completion to `Γ(X, U)`. -/
public abbrev resCompletion :
    ModuleCat.{u} (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) ⥤ ModuleCat.{u} Γ(X, U) :=
  ModuleCat.restrictScalars.{u} (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))

/-- The submodule `(I₀A)^k M_A`. -/
public abbrev completedLevelSubmodule (k : ℕ) :
    Submodule (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (completedFormalSections U hU G) :=
  (I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) ^ k •
    (⊤ : Submodule (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (completedFormalSections U hU G))

/-- The map `M_𝒢 → M_A / (I₀A)^k M_A`, `Γ(X, U)`-linear. -/
public def toCompletedLevel (k : ℕ) :
    formalSectionsOver G U →ₗ[Γ(X, U)]
      (resCompletion U hU).obj ((completedFormalSectionsTower hU G).obj (op k)) where
  toFun x := Submodule.Quotient.mk (p := completedLevelSubmodule hU G k)
    (formalSectionsEquivCompleted hU G x)
  map_add' x y := by
    rw [map_add]
    rfl
  map_smul' r x := by
    rw [LinearEquiv.map_smul]
    change Submodule.Quotient.mk (p := completedLevelSubmodule hU G k)
      (r • formalSectionsEquivCompleted hU G x) =
      (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) r) •
        Submodule.Quotient.mk (p := completedLevelSubmodule hU G k)
          (formalSectionsEquivCompleted hU G x)
    rw [← Submodule.Quotient.mk_smul, algebraMap_smul]

/-- An element of `M_𝒢` maps to zero in `M_A / (I₀A)^k M_A` if and only if it lies in
`I₀^k M_𝒢`. -/
theorem toCompletedLevel_eq_zero_iff (k : ℕ) (x : formalSectionsOver G U) :
    toCompletedLevel hU G k x = 0 ↔
      x ∈ I.ideal ⟨U, hU⟩ ^ k • (⊤ : Submodule Γ(X, U) (formalSectionsOver G U)) := by
  show Submodule.Quotient.mk (p := completedLevelSubmodule hU G k)
    (formalSectionsEquivCompleted hU G x) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero,
    Stacks.LocalCohomology.mem_pow_smul_top_iff_mem_map_pow_smul_top]
  have hmap : (I.ideal ⟨U, hU⟩ ^ k • (⊤ : Submodule Γ(X, U) (formalSectionsOver G U))).map
      (formalSectionsEquivCompleted hU G).toLinearMap =
      I.ideal ⟨U, hU⟩ ^ k • (⊤ : Submodule Γ(X, U) (completedFormalSections U hU G)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  rw [← hmap, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

/-- The levels `M_𝒢 / I₀^k M_𝒢 ≅ M_A / (I₀A)^k M_A` over `Γ(X, U)`. -/
public def levelCompletedEquiv (k : ℕ) :
    (formalSectionsOver G U ⧸ I.ideal ⟨U, hU⟩ ^ k •
        (⊤ : Submodule Γ(X, U) (formalSectionsOver G U))) ≃ₗ[Γ(X, U)]
      (resCompletion U hU).obj ((completedFormalSectionsTower hU G).obj (op k)) :=
  LinearEquiv.ofBijective
    ((I.ideal ⟨U, hU⟩ ^ k • (⊤ : Submodule Γ(X, U) (formalSectionsOver G U))).liftQ
      (toCompletedLevel hU G k) (fun x hx => (toCompletedLevel_eq_zero_iff hU G k x).2 hx))
    ⟨by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro q hq
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
      exact (Submodule.Quotient.mk_eq_zero _).2 ((toCompletedLevel_eq_zero_iff hU G k x).1 hq),
    by
      intro y
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
      refine ⟨Submodule.Quotient.mk ((formalSectionsEquivCompleted hU G).symm z), ?_⟩
      change Submodule.Quotient.mk (p := completedLevelSubmodule hU G k)
        (formalSectionsEquivCompleted hU G ((formalSectionsEquivCompleted hU G).symm z)) = _
      rw [LinearEquiv.apply_symm_apply]
      rfl⟩

/-- `levelCompletedEquiv` sends the class of `x` to `toCompletedLevel hU G k x`. -/
theorem levelCompletedEquiv_mk (k : ℕ) (x : formalSectionsOver G U) :
    levelCompletedEquiv hU G k (Submodule.Quotient.mk x) = toCompletedLevel hU G k x :=
  rfl

/-- **The levels of the sections of `𝒢` are the levels of `M_A`**, naturally in `n`. -/
public def sectionsCompletedTowerIso :
    G.obj ⋙ sectionsOver U ≅ (InverseSequence.ProIso.succFunctor.op ⋙
      completedFormalSectionsTower hU G) ⋙ resCompletion U hU :=
  NatIso.ofComponents
    (fun n => ((levelEquiv G hU n.unop).symm.trans
      (levelCompletedEquiv hU G (n.unop + 1))).toModuleIso)
    (fun {m n} f => by
      apply ModuleCat.hom_ext
      refine (LinearMap.cancel_right (surjective_limitπ_formalSectionsOver G hU m.unop)).1 ?_
      refine LinearMap.ext fun x => ?_
      have h1 : (levelEquiv G hU m.unop).symm (limit.π (G.obj ⋙ sectionsOver U) (op m.unop) x) =
          Submodule.Quotient.mk x := (levelEquiv G hU m.unop).symm_apply_eq.2 rfl
      have h2 : (G.obj ⋙ sectionsOver U).map f (limit.π (G.obj ⋙ sectionsOver U) m x) =
          limit.π (G.obj ⋙ sectionsOver U) n x := by
        rw [← ConcreteCategory.comp_apply, limit.w]
      have h3 : (levelEquiv G hU n.unop).symm (limit.π (G.obj ⋙ sectionsOver U) n x) =
          Submodule.Quotient.mk x := (levelEquiv G hU n.unop).symm_apply_eq.2 rfl
      change levelCompletedEquiv hU G (n.unop + 1) ((levelEquiv G hU n.unop).symm
          ((G.obj ⋙ sectionsOver U).map f (limit.π (G.obj ⋙ sectionsOver U) m x))) =
        ((InverseSequence.ProIso.succFunctor.op ⋙ completedFormalSectionsTower hU G) ⋙
          resCompletion U hU).map f (levelCompletedEquiv hU G (m.unop + 1)
            ((levelEquiv G hU m.unop).symm (limit.π (G.obj ⋙ sectionsOver U) (op m.unop) x)))
      rw [h2, h3, h1]
      rfl)

end Completion

/-! ### The transfer of essential constancy -/

section Transfer

/-- The first terms of the short exact sequences of sections are the sections of `ℱ'ₙ`. -/
public def sectionsShortComplexSystemπ₁Iso :
    sectionsShortComplexSystem hdual F hT hT' hTY himm U ⋙ ShortComplex.π₁ ≅
      improvedSystem T hT F.obj ⋙ sectionsOver U :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

include hU in
omit [AlgebraicGeometry.IsNoetherian X] in
/-- If `T'` lies in the support of `I`, then the primes of `Γ(X, U)` with points in `T'` lie in the
zero locus of `I₀`. -/
theorem primesIn_subset_zeroLocus (hT'Y : T' ⊆ I.support) :
    primesIn hU T' ⊆ PrimeSpectrum.zeroLocus (I.ideal ⟨U, hU⟩ : Set Γ(X, U)) := by
  intro p hp
  have h := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := ⟨U, hU⟩)
    (fromSpec_mem hU p)).1 (hT'Y hp)
  rw [Scheme.mem_zeroLocus_iff] at h
  rw [PrimeSpectrum.mem_zeroLocus]
  intro a ha
  have h2 : p ∉ PrimeSpectrum.basicOpen a := fun hp =>
    h a ha (show p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a by rwa [hU.fromSpec_preimage_basicOpen])
  simpa [PrimeSpectrum.mem_basicOpen] using h2

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The ideal `(I₀A)^(n+1)` annihilates the level `M_A / (I₀A)^(n+1) M_A`. -/
theorem pow_smul_top_completedTower_eq_bot (G : Stacks.Coherent.CoherentAdicSystems I)
    (n : ℕᵒᵖ) :
    (I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) ^
        (n.unop + 1) • (⊤ : Submodule (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
          ((InverseSequence.ProIso.succFunctor.op ⋙ completedFormalSectionsTower hU G).obj n)) =
      ⊥ := by
  refine eq_bot_iff.2 (Submodule.smul_le.2 fun a ha q _ => ?_)
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (completedLevelSubmodule hU G (n.unop + 1)) q
  rw [Submodule.mem_bot]
  show a • Submodule.Quotient.mk (p := completedLevelSubmodule hU G (n.unop + 1)) y = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

include hTT' in
/-- **The transfer of essential constancy from the completion.** If the system
`{H¹_{T'_A}(M_A/(I₀A)ⁿM_A)}` over the completion `A` of `Γ(X, U)` is essentially constant, then so
is the system `{H¹_{T'}(Γ(U, ℱ'ₙ))}` over `Γ(X, U)`. -/
public theorem isEssentiallyConstantPro_localCohomologyOne_depthOneSections
    (hT'Y : T' ⊆ I.support)
    (hR : letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
      ringKrullDim Γ(X, U) < ⊤)
    (hA : ringKrullDim (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) < ⊤)
    (hess : letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
      CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro
        (completedFormalSectionsTower hU Mo.G ⋙
          Stacks.LocalCohomology.localCohomologyWithSupportInModuleFunctor.{u, u}
            (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
            ((PrimeSpectrum.comap (algebraMap Γ(X, U)
              (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))) ⁻¹' primesIn hU T') 1)) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro
      (sectionsShortComplexSystem hdual F hT hT' hTY himm U ⋙ ShortComplex.π₁ ⋙
        Stacks.LocalCohomology.localCohomologyWithSupportInModuleFunctor.{u, u} Γ(X, U)
          (primesIn hU T') 1) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  set LA := Stacks.LocalCohomology.localCohomologyWithSupportInModuleFunctor.{u, u}
    (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
    ((PrimeSpectrum.comap (algebraMap Γ(X, U)
      (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))) ⁻¹' primesIn hU T') 1
  set LR := Stacks.LocalCohomology.localCohomologyWithSupportInModuleFunctor.{u, u} Γ(X, U)
    (primesIn hU T') 1
  set D := InverseSequence.ProIso.succFunctor.op ⋙ completedFormalSectionsTower hU Mo.G
  have h1 : CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro (D ⋙ LA) :=
    CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro.of_proIso
      (InverseSequence.ProIso.shiftSucc _) hess
  have h2 : CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro
      (D ⋙ LA ⋙ resCompletion U hU) := h1.comp (resCompletion U hU)
  have h3 : CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro
      (D ⋙ resCompletion U hU ⋙ LR) :=
    h2.of_iso (Stacks.LocalCohomology.completionTorsionLocalCohomologyNatIso (I.ideal ⟨U, hU⟩)
      hR hA (primesIn hU T') (stableUnderSpecialization_primesIn hU hT')
      (primesIn_subset_zeroLocus hU hT'Y) D
      (fun j => ⟨j.unop + 1, pow_smul_top_completedTower_eq_bot hU Mo.G j⟩) 1)
  have h4 : CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro
      (Mo.G.obj ⋙ sectionsOver U ⋙ LR) :=
    h3.of_iso (Functor.isoWhiskerRight (sectionsCompletedTowerIso hU Mo.G) LR).symm
  have h5 : CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro
      ((improvedSystem T hT F.obj ⋙ sectionsOver U) ⋙ LR) :=
    CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro.of_proIso
      ((modelProIso F hT U Mo).whiskerRight LR).symm h4
  exact h5.of_iso (Functor.isoWhiskerRight
    (sectionsShortComplexSystemπ₁Iso hdual F hT hT' hTY himm) LR).symm

end Transfer

end Stacks.Algebraization

end
