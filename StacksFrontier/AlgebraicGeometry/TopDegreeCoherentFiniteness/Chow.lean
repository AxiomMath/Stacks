module
import all StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersectionLeadingTerm
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSite
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleAffineBaseTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.TensorPowerTensor
public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.FreeMap
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.ProperMapping.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.CompositionPermanence
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleImplications.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleTwistVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersectionLeadingTerm
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension
public import StacksFrontier.Topology.Dimension.NowhereDense
public import StacksFrontier.Topology.Sheaves.Modules.SupportSection
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors

public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Refinements
public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.ConfinedDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericIdealCoproduct
public import StacksFrontier.AlgebraicGeometry.LeraySectionsCollapse.OverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.PseudoMorphism
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowTwist
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Segre.ChartSurjective
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.Support
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EmbeddedPointStep
public import StacksFrontier.AlgebraicGeometry.Variety.ImageDimension
public import StacksFrontier.Topology.Sheaves.Modules.SupportCoproduct

/-!
# Top-degree cohomology of the structure sheaf of a variety, by Chow's lemma

This is the variety step of the induction in the source's proof of [Stacks, Tag 0A3M]. Let
`Z` be an integral scheme, separated and of finite type over a field `k`, of dimension at most
`n + 1`, and suppose that `H^n(W, 𝒢)` is finite-dimensional for every coherent `𝒢` on every
separated scheme `W` of finite type over `k` of dimension at most `n`. Then `H^{n+1}(Z, 𝒪_Z)` is
finite-dimensional.

The argument is the source's.

* **Chow's lemma** ([Stacks, Tags 0200] and [0201]) gives a proper surjective `ρ : Y ⟶ Z`, an
  isomorphism above a dense open `U ⊆ Z` with `ρ⁻¹(U)` dense in `Y`, and an immersion
  `j : Y ⟶ ℙᴺ_k` over `k`. So `dim Y ≤ dim Z`.
* `ℒ = j^* 𝒪(1)` is ample relative to `Y ⟶ Spec k` ([Stacks, Tag 01VT]), hence relative to `ρ`
  ([Stacks, Tag 0C4L]), and [Stacks, Tag 02O1] chooses a power with
  `Rᵖ ρ_* (𝒪_Y ⊗ ℒ^{⊗ n₀}) = 0` for `p > 0`. With `ℳ = 𝒪_Y ⊗ ℒ^{⊗ n₀}` the Leray collapse
  ([Stacks, Tag 01F4]) gives `H^{n+1}(Z, ρ_* ℳ) ≅ H^{n+1}(Y, ℳ)`.
* `ℳ` is the restriction of `𝒪 ⊗ ℒ̄^{⊗ n₀}` on the closure `Z̄` of `Y` in `ℙᴺ_k`, a proper
  scheme of dimension at most `n + 1`. Its top cohomology there is finite-dimensional
  ([Stacks, Tag 02O6]) and surjects onto that on the open `Y` ([Stacks, Tag 0A3G] (2)).
* The coherent `𝒢 = ρ_* ℳ` ([Stacks, Tag 02O5]) has the generic point in its support. A finite
  sum of copies of a coherent ideal `ℐ` maps into `𝒢` by a monomorphism which is an isomorphism
  near the generic point ([Stacks, Tag 01YE]); the cokernels of `⊕ ℐ ⟶ 𝒢` and of `ℐ ⟶ 𝒪_Z` are
  supported in dimension at most `n`, so the induction hypothesis and the long exact sequence
  carry finiteness from `𝒢` to `⊕ ℐ`, to its summand `ℐ`, and to `𝒪_Z`.

The source instead chooses a section `𝒪_Z ⟶ 𝒢` that is nonzero at the generic point; the
ideal-sum dévissage avoids having to produce a global section.

## Main results

* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_unit_of_isIntegral`

## References

* [Stacks Project, Tag 0A3M](https://stacks.math.columbia.edu/tag/0A3M)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple Stacks.AmpleProjectiveImmersion

universe u

namespace AlgebraicGeometry

/-- A scheme quasi-compact and locally of finite type over a field is Noetherian. -/
private theorem isNoetherian_of_quasiCompact_of_locallyOfFiniteType (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [LocallyOfFiniteType f] :
    IsNoetherian X := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := (quasiCompact_iff_compactSpace f).mp inferInstance
  exact ⟨⟩

/-- The cokernel sequence of a monomorphism is short exact. -/
private theorem shortExact_cokernelSequence {C : Type*} [Category C] [Abelian C] {A B : C}
    (f : A ⟶ B) [Mono f] : (ShortComplex.cokernelSequence f).ShortExact :=
  { exact := ShortComplex.cokernelSequence_exact f
    mono_f := by dsimp [ShortComplex.cokernelSequence]; infer_instance
    epi_g := by change Epi (cokernel.π f); exact coequalizer.π_epi }

/-- If `ρ : Y ⟶ Z` is an isomorphism above an open `U` whose preimage is scheme-theoretically
dense in `Y`, then `dim Y ≤ dim Z`. -/
private theorem topologicalKrullDim_le_of_isIso_morphismRestrict (k : Type u) [Field k]
    {Y Z : Scheme.{u}} (ρ : Y ⟶ Z) (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType ρ]
    [LocallyOfFiniteType g] [TopologicalSpace.NoetherianSpace Y] (U : Z.Opens)
    [IsIso (ρ ∣_ U)] (hU : Scheme.Opens.IsSchemeTheoreticallyDense (ρ ⁻¹ᵁ U)) :
    topologicalKrullDim Y ≤ topologicalKrullDim Z := by
  have hden : Dense ((ρ ⁻¹ᵁ U : Y.Opens) : Set Y) := dense_of_isSchemeTheoreticallyDense _ hU
  have : TopologicalSpace.NoetherianSpace (ρ ⁻¹ᵁ U).toScheme :=
    (ρ ⁻¹ᵁ U).ι.isOpenEmbedding.isInducing.noetherianSpace
  have hcl := topologicalKrullDim_closure_range_le k (ρ ⁻¹ᵁ U).ι
    ((ρ ⁻¹ᵁ U).ι ≫ ρ ≫ g) (ρ ≫ g) rfl
  rw [Scheme.Opens.range_ι, hden.closure_eq, topologicalKrullDim_univ] at hcl
  refine hcl.trans ?_
  have : IsOpenImmersion ((ρ ⁻¹ᵁ U).ι ≫ ρ) := by
    rw [← morphismRestrict_ι]
    infer_instance
  exact ((ρ ⁻¹ᵁ U).ι ≫ ρ).isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- For `Y` of finite type over `k` with `dim Y ≤ n + 1` and an immersion `j : Y ⟶ ℙᴺ_k` over `k`,
every twist `𝒪_Y ⊗ ℒ^{⊗ n₀}` of `ℒ ≅ j^* 𝒪(1)` has finite-dimensional `H^{n+1}`. -/
private theorem finiteDimensional_cohomologyOverField_tensorPowModule_of_isImmersion (k : Type u)
    [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [QuasiCompact f] [LocallyOfFiniteType f]
    (N : ℕ) (j : Y ⟶ ProjectiveSpace N (Spec (.of k))) [IsImmersion j]
    (hj : j ≫ (ProjectiveSpace N (Spec (.of k)) ↘ Spec (.of k)) = f) (L : Y.Modules)
    [IsInvertibleModule Y L]
    (hL : (Scheme.Modules.pullback (Y := projectiveSpaceOver N (Spec (.of k))) j).obj
      (projectiveSpaceTwistingSheaf N (Spec (.of k))) ≅ L) (n n₀ : ℕ)
    (hdim : topologicalKrullDim Y ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    FiniteDimensional k (cohomologyOverField k f (Stacks.RelativeVeryAmple.tensorModules Y
      (unitModule Y) (tensorPowModule Y L (n₀ : ℤ))) (n + 1)) := by
  let P := ProjectiveSpace N (Spec (.of k))
  have : IsProper (P ↘ Spec (.of k)) := isProper_projectiveSpaceOver N _
  have : IsNoetherian Y := isNoetherian_of_quasiCompact_of_locallyOfFiniteType k f
  let Zb := j.image
  let ι : Zb ⟶ P := j.imageι
  let j₀ : Y ⟶ Zb := j.toImage
  have hj₀ι : j₀ ≫ ι = j := Scheme.Hom.toImage_imageι j
  let gb : Zb ⟶ Spec (.of k) := ι ≫ (P ↘ Spec (.of k))
  have : IsProper gb := inferInstance
  have : IsNoetherian Zb := isNoetherian_of_quasiCompact_of_locallyOfFiniteType k gb
  have hdimZb : topologicalKrullDim Zb ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by
    have h := topologicalKrullDim_closure_range_le k j f (P ↘ Spec (.of k)) hj
    have hrange : (closure (Set.range j.base) : Set P) = Set.range ι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
    rw [hrange, topologicalKrullDim_range_eq] at h
    exact h.trans hdim
  have hj₀gb : j₀ ≫ gb = f := by
    change j₀ ≫ ι ≫ (P ↘ Spec (.of k)) = f
    rw [← Category.assoc, hj₀ι, hj]
  let j' : Y ⟶ projectiveSpaceOver N (Spec (.of k)) := j
  let ι' : Zb ⟶ projectiveSpaceOver N (Spec (.of k)) := ι
  let M : Y.Modules :=
    Stacks.RelativeVeryAmple.tensorModules Y (unitModule Y) (tensorPowModule Y L (n₀ : ℤ))
  let Lb : Zb.Modules :=
    (Scheme.Modules.pullback ι').obj (projectiveSpaceTwistingSheaf N (Spec (.of k)))
  let Mb : Zb.Modules :=
    Stacks.RelativeVeryAmple.tensorModules Zb (unitModule Zb) (tensorPowModule Zb Lb (n₀ : ℤ))
  have : (unitModule Zb).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Zb
  have : Mb.IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible Zb
      (unitModule Zb) (tensorPowModule Zb Lb (n₀ : ℤ))
  have hres := finiteDimensional_cohomologyOverField_pullback_of_isOpenImmersion k gb j₀ Mb n
    hdimZb (finiteDimensional_cohomologyOverField_of_isProper k gb Mb (n + 1))
  rw [hj₀gb] at hres
  have hres' : FiniteDimensional k (cohomologyOverField k f
      ((RingedSpaceModuleAdjunction.modulePullback j₀.toLRSHom.toShHom).obj Mb) (n + 1)) := hres
  have hj₀ι' : j₀ ≫ ι' = j' := hj₀ι
  have eL' : (Scheme.Modules.pullback j₀).obj Lb ≅ L :=
    (Scheme.Modules.pullbackComp j₀ ι').app _ ≪≫ eqToIso (by rw [hj₀ι']) ≪≫ hL
  have eL : (RingedSpaceModuleAdjunction.modulePullback j₀.toLRSHom.toShHom).obj Lb ≅ L := eL'
  have e : (RingedSpaceModuleAdjunction.modulePullback j₀.toLRSHom.toShHom).obj Mb ≅ M :=
    pullbackTensorModulesIso j₀ (unitModule Zb) (tensorPowModule Zb Lb (n₀ : ℤ)) ≪≫
      tensorModulesMapIso Y (Stacks.RelativeAmple.pullbackUnitModuleIso j₀)
        (pullbackTensorPowModuleIso j₀ Lb n₀ ≪≫ tensorPowModuleIsoOfIso Y _ L eL n₀)
  exact Module.Finite.equiv (cohomologyOverFieldIso k f e (n + 1)).toLinearEquiv

/-- On an integral `Z` of finite type over `k` with `dim Z ≤ n + 1`, a coherent module whose
support misses the generic point has support of dimension at most `n`. -/
private theorem topologicalKrullDim_supp_le_of_genericPoint_notMem (k : Type u) [Field k]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g] [IsIntegral Z] (n : ℕ)
    (hdim : topologicalKrullDim Z ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) (Q : Z.Modules)
    (hQ : Q.IsCoherent) (hξQ : genericPoint Z ∉ _root_.SheafOfModules.supp Q) :
    topologicalKrullDim (_root_.SheafOfModules.supp Q) ≤ (n : WithBot ℕ∞) := by
  have : IrreducibleSpace Z := irreducibleSpace_of_isIntegral Z
  have hclosed := Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp_of_isCoherent Q hQ
  have hne : _root_.SheafOfModules.supp Q ≠ Set.univ :=
    fun h => hξQ (h ▸ Set.mem_univ (genericPoint Z))
  have hlt : topologicalKrullDim (_root_.SheafOfModules.supp Q) < (n : WithBot ℕ∞) + 1 := by
    exact_mod_cast (topologicalKrullDim_lt_of_isClosed_ne_univ hclosed hne
      (topologicalKrullDim_lt_top_of_isIntegral k g (𝟙 Z))).trans_le hdim
  exact (ENat.WithBot.lt_add_one_iff (n := topologicalKrullDim (_root_.SheafOfModules.supp Q))
    (m := n)).1 hlt

/-- A retract of a module whose cohomology over `k` is finite-dimensional in degree `n` has
finite-dimensional cohomology over `k` in degree `n`. -/
private theorem finiteDimensional_cohomologyOverField_of_retraction (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {F G : X.Modules} (i : F ⟶ G) (p : G ⟶ F)
    (hip : i ≫ p = 𝟙 F) (n : ℕ) (h : FiniteDimensional k (cohomologyOverField k f G n)) :
    FiniteDimensional k (cohomologyOverField k f F n) := by
  have hcomp : cohomologyOverFieldMap k f i n ≫ cohomologyOverFieldMap k f p n = 𝟙 _ := by
    rw [← cohomologyOverFieldMap_comp, hip, cohomologyOverFieldMap_id]
  exact FiniteDimensional.of_injective (cohomologyOverFieldMap k f i n).hom
    (Function.LeftInverse.injective (g := (cohomologyOverFieldMap k f p n).hom)
      fun a => LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcomp) a)

/-- Let `Z` be integral, separated and of finite type over `k` with `dim Z ≤ n + 1`, and assume
the induction hypothesis in dimension `n`. If a coherent `𝒢` with the generic point in its
support has finite-dimensional `H^{n+1}`, then so does `𝒪_Z`. -/
private theorem finiteDimensional_cohomologyOverField_unit_of_genericPoint_mem_supp (k : Type u)
    [Field k] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [QuasiCompact g] [LocallyOfFiniteType g]
    [IsSeparated g] [IsIntegral Z] (n : ℕ)
    (hdim : topologicalKrullDim Z ≤ ((n + 1 : ℕ) : WithBot ℕ∞))
    (IH : ∀ {W : Scheme.{u}} (h : W ⟶ Spec (.of k)), QuasiCompact h → LocallyOfFiniteType h →
      IsSeparated h → topologicalKrullDim W ≤ (n : WithBot ℕ∞) →
      ∀ G : W.Modules, G.IsCoherent → FiniteDimensional k (cohomologyOverField k h G n))
    (G : Z.Modules) [G.IsCoherent] (hξG : genericPoint Z ∈ _root_.SheafOfModules.supp G)
    (hFG : FiniteDimensional k (cohomologyOverField k g G (n + 1))) :
    FiniteDimensional k (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) (n + 1)) := by
  classical
  have : IsNoetherian Z := isNoetherian_of_quasiCompact_of_locallyOfFiniteType k g
  obtain ⟨r, I, hI, β, hβ, V, hξV, hβV⟩ :=
    Stacks.AlgebraicGeometry.IrreducibleDevissage.exists_idealCoproduct_mono_isIso_near_genericPoint
      G (genericPoint Z) (genericPoint_spec Z)
  have := hI
  let S₁ := ShortComplex.cokernelSequence β
  have hS₁ : S₁.ShortExact := shortExact_cokernelSequence β
  have hξQ₁ : genericPoint Z ∉ _root_.SheafOfModules.supp S₁.X₃ :=
    Stacks.AlgebraicGeometry.ConfinedDevissage.notMem_supp_cokernel_of_isIso_restrict β V hβV _
      hξV
  have : (∐ fun _ : Fin r => I.toSheafOfModules).IsCoherent :=
    (_root_.SheafOfModules.isCoherent_iff _).2
      (Stacks.SheafOfModules.isCoherent_sigma _ fun _ =>
        (_root_.SheafOfModules.isCoherent_iff _).1 hI)
  have hQ₁ : S₁.X₃.IsCoherent := _root_.SheafOfModules.cokernel_isCoherent β
  have hfinSum : FiniteDimensional k (cohomologyOverField k g S₁.X₁ (n + 1)) :=
    finiteDimensional_cohomologyOverField_one_of_shortExact_succ k g hS₁ n
      (finiteDimensional_cohomologyOverField_of_topologicalKrullDim_supp_le k g S₁.X₃ n
        (topologicalKrullDim_supp_le_of_genericPoint_notMem k g n hdim _ hQ₁ hξQ₁) IH) hFG
  obtain ⟨j₁, hj₁⟩ :
      ∃ j₁ : Fin r, genericPoint Z ∈ _root_.SheafOfModules.supp I.toSheafOfModules :=
    (AlgebraicGeometry.SheafOfModules.mem_supp_coproduct_iff
      (fun _ : Fin r => I.toSheafOfModules) _).1
      (((Set.mem_union _ _ _).1 (supp_subset_union_of_shortExact S₁ hS₁ hξG)).resolve_right hξQ₁)
  have hret := Sigma.ι_comp_desc (f := fun _ : Fin r => I.toSheafOfModules)
    (Pi.single j₁ (𝟙 I.toSheafOfModules)) j₁
  rw [Pi.single_eq_same] at hret
  let S₂ := ShortComplex.cokernelSequence I.ι
  have hS₂ : S₂.ShortExact := shortExact_cokernelSequence I.ι
  have : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Z
  have hQ₂ : S₂.X₃.IsCoherent := _root_.SheafOfModules.cokernel_isCoherent I.ι
  have hξQ₂ : genericPoint Z ∉ _root_.SheafOfModules.supp S₂.X₃ :=
    _root_.AlgebraicGeometry.notMem_supp_cokernel_genericPoint I.ι inferInstance hj₁
  have := finiteDimensional_of_isZero k
    (isZero_cohomologyOverField_of_topologicalKrullDim_supp_le k g S₂.X₃
      (topologicalKrullDim_supp_le_of_genericPoint_notMem k g n hdim _ hQ₂ hξQ₂)
      (Nat.lt_succ_self n))
  have : FiniteDimensional k (cohomologyOverField k g S₂.X₁ (n + 1)) :=
    finiteDimensional_cohomologyOverField_of_retraction k g _ _ hret (n + 1) hfinSum
  obtain ⟨-, -, hex, -⟩ := exists_cohomologyOverField_longExactSequence k g hS₂
  exact Module.finiteDimensional_of_exact (cohomologyOverFieldMap k g S₂.f (n + 1)).hom
    (cohomologyOverFieldMap k g S₂.g (n + 1)).hom (hex (n + 1))

/-- If `ρ : Y ⟶ Z` is an isomorphism above a dense open of the integral scheme `Z` and `ℳ` is
invertible on `Y`, then the generic point of `Z` lies in the support of `ρ_* ℳ`. -/
private theorem genericPoint_mem_supp_pushforward {Y Z : Scheme.{u}} [IsIntegral Z] (ρ : Y ⟶ Z)
    (U : Z.Opens) (hU : Dense (U : Set Z)) [IsIso (ρ ∣_ U)] (M : Y.Modules)
    [IsInvertibleModule Y M] [((Scheme.Modules.pushforward ρ).obj M).IsQuasicoherent] :
    genericPoint Z ∈ _root_.SheafOfModules.supp ((Scheme.Modules.pushforward ρ).obj M) := by
  have hgen : IsGenericPoint (genericPoint Z) (Set.range (𝟙 Z : Z ⟶ Z).base) := by
    simpa using genericPoint_spec Z
  have h := ProperCoherenceWitness.supp_pushforward_chowTwist (𝟙 Z) ρ U hU M hgen
  rw [Category.comp_id] at h
  rw [h]
  exact ⟨genericPoint Z, rfl⟩

/-- **The variety step of [Stacks, Tag 0A3M].** Let `Z` be an integral scheme, separated and of
finite type over a field `k`, with `dim Z ≤ n + 1`, and suppose (the induction hypothesis) that
`H^n(W, 𝒢)` is finite-dimensional for every coherent `𝒢` on every separated scheme `W` of finite
type over `k` with `dim W ≤ n`. Then `H^{n+1}(Z, 𝒪_Z)` is finite-dimensional. -/
theorem finiteDimensional_cohomologyOverField_unit_of_isIntegral (k : Type u) [Field k]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [QuasiCompact g] [LocallyOfFiniteType g]
    [IsSeparated g] [IsIntegral Z] (n : ℕ)
    (hdim : topologicalKrullDim Z ≤ ((n + 1 : ℕ) : WithBot ℕ∞))
    (IH : ∀ {W : Scheme.{u}} (h : W ⟶ Spec (.of k)), QuasiCompact h → LocallyOfFiniteType h →
      IsSeparated h → topologicalKrullDim W ≤ (n : WithBot ℕ∞) →
      ∀ G : W.Modules, G.IsCoherent → FiniteDimensional k (cohomologyOverField k h G n)) :
    FiniteDimensional k (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) (n + 1)) := by
  -- `Z` is Noetherian
  have : IsNoetherian Z := isNoetherian_of_quasiCompact_of_locallyOfFiniteType k g
  /- Step 1: Chow's lemma, with `ρ⁻¹(U)` scheme-theoretically dense. -/
  obtain ⟨N, X', π, i, U, hπ, -, hi, hcomm, hU, hiso⟩ := hasDenseChowModification g
  have := hπ
  have := hi
  obtain ⟨Y, ρ, j, hρ, -, hj, hcomm', -, hρU, hYdense⟩ :=
    exists_isSchemeTheoreticallyDense_chowModification g π i U hcomm hU hiso
  have := hρ
  have := hj
  have : IsIso (ρ ∣_ U) := hρU
  have : IsNoetherian Y := isNoetherian_of_quasiCompact_of_locallyOfFiniteType k (ρ ≫ g)
  /- Step 4: `ℒ = j^* 𝒪(1)`, ample relative to `ρ`. -/
  let j' : Y ⟶ projectiveSpaceOver N (Spec (.of k)) := j
  let L : Y.Modules :=
    (Scheme.Modules.pullback j').obj (projectiveSpaceTwistingSheaf N (Spec (.of k)))
  have hLamp : Stacks.RelativeAmple.IsRelativelyAmple (ρ ≫ g) L :=
    Stacks.ProjectiveSpace.isRelativelyAmple_of_exists_hasImmersionTwistOver (ρ ≫ g) L
      inferInstance ⟨1, le_rfl, N, j', hj, hcomm'.symm, ⟨tensorPowModuleOneIso Y L⟩⟩
  have hLρ : Stacks.RelativeAmple.IsRelativelyAmple ρ L :=
    Stacks.RelativeAmpleCompositionPermanence.isRelativelyAmple_of_comp ρ g L hLamp
      inferInstance
  /- Step 5: [Stacks, Tag 02O1] — a twist `ℳ` with no higher direct images along `ρ`. -/
  have : (unitModule Y).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Y
  open Stacks.AlgebraicGeometry.AmpleTwistAcyclicity in
  obtain ⟨n₀, hn₀⟩ :=
    exists_isZero_rightDerivedPlus_pushforward_tensorPowModule ρ (unitModule Y) L hLρ
  let M : Y.Modules :=
    Stacks.RelativeVeryAmple.tensorModules Y (unitModule Y) (tensorPowModule Y L (n₀ : ℤ))
  have : M.IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible Y
      (unitModule Y) (tensorPowModule Y L (n₀ : ℤ))
  have : IsInvertibleModule Y M :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules Y (unitModule Y)
      (tensorPowModule Y L (n₀ : ℤ))
  /- Steps 6-8: `𝒢 = ρ_* ℳ` is coherent ([Stacks, Tag 02O5]); the Leray collapse along `ρ` and
  the finiteness of `H^{n+1}(Y, ℳ)` give that of `H^{n+1}(Z, 𝒢)`, which passes to `𝒪_Z`. -/
  let G : Z.Modules := (Scheme.Modules.pushforward ρ).obj M
  have : G.IsCoherent := ProperCoherenceWitness.isCoherent_pushforward ρ M
  have : G.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).1
  exact finiteDimensional_cohomologyOverField_unit_of_genericPoint_mem_supp k g n hdim IH G
    (genericPoint_mem_supp_pushforward ρ U hU M)
    (finiteDimensional_cohomologyOverField_of_pushforward_of_isZero k ρ g M
      (fun q hq => hn₀ n₀ q le_rfl hq) (n + 1)
      (finiteDimensional_cohomologyOverField_tensorPowModule_of_isImmersion k (ρ ≫ g) N j
        hcomm'.symm L (Iso.refl _) n n₀
        ((topologicalKrullDim_le_of_isIso_morphismRestrict k ρ g U hYdense).trans hdim)))

end AlgebraicGeometry

end
