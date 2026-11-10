module

public import StacksFrontier.AlgebraicGeometry.Curves.RegularSectionGeneration.Dimension
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusGoesDown
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SectionMultiplicationExtension
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.TwistGeneration
public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.TwistShift

/-!
# Cohomology of the cokernels of multiplication by a regular section

On a proper scheme `X` of dimension at most one over a field `k`, let `σ` be a regular section of
an invertible `ℒ`. The cokernels `quot σ n` are coherent with support of dimension at most zero, so
by [Stacks, Tag 0AYT] (3) they have no higher cohomology. The long exact sequences of
`0 ⟶ ℒ^{⊗ n} ⟶ ℒ^{⊗ 1 + n} ⟶ quot σ n ⟶ 0` then give the cohomological statements of the first
paragraph of the proof of [Stacks, Tag 0E8V].

## Main results

* `Stacks.RegularSectionGeneration.isZero_cohomologyOverField_one_natTensorPow`:
  `H¹(X, ℒ^{⊗ n}) = 0` for every `n ≥ 1`, from `H¹(X, ℒ) = 0`.
* `Stacks.RegularSectionGeneration.exists_comp_cokernelπ_eq`: global sections of `quot σ n` lift
  to `ℒ^{⊗ 1 + n}` when `H¹(X, ℒ^{⊗ n}) = 0`.
* `Stacks.RegularSectionGeneration.exists_eq_comp_mulMap`: a section of `ℒ^{⊗ 1 + n}` vanishing
  in `quot σ n` is a multiple of `σ`.
* `Stacks.RegularSectionGeneration.exists_comp_quotMap_eq`: multiplication by a second section
  `t`, nonvanishing on the support of the cokernels, is surjective on their global sections.

## References

* [Stacks Project, Tag 0E8V](https://stacks.math.columbia.edu/tag/0E8V)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Ample
open Stacks.GradedSections (powSections mulMap mul)
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.RegularSectionGeneration

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}}

/-! ### Sections as morphisms out of the unit -/

/-- **Surjectivity on `H⁰` gives surjectivity on morphisms out of the unit.** -/
theorem exists_comp_eq_of_surjective_cohomologyOverFieldMap (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) {F G : X.Modules} (φ : F ⟶ G)
    (h : Function.Surjective (cohomologyOverFieldMap k f φ 0)) (γ : 𝟙_ X.Modules ⟶ G) :
    ∃ β : 𝟙_ X.Modules ⟶ F, β ≫ φ = γ := by
  obtain ⟨b, hb⟩ := h ((cohomologyOverFieldZeroEquivSections k f G).symm
    (Stacks.SectionProduct.globalSection X G γ))
  refine ⟨(Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X F).symm
    (cohomologyOverFieldZeroEquivSections k f F b), ?_⟩
  apply (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X G).injective
  change Stacks.SectionProduct.globalSection X G _ = Stacks.SectionProduct.globalSection X G γ
  rw [Stacks.SectionProduct.globalSection_comp]
  have h1 : Stacks.SectionProduct.globalSection X F
      ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X F).symm
        (cohomologyOverFieldZeroEquivSections k f F b)) =
      cohomologyOverFieldZeroEquivSections k f F b :=
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X F).apply_symm_apply _
  rw [h1, ← cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap, hb,
    Equiv.apply_symm_apply]

variable (L : X.Modules) [IsInvertibleModule X L] (σ : powSections L 1)

/-- **The short exact sequence `0 ⟶ ℒ^{⊗ n} ⟶ ℒ^{⊗ 1 + n} ⟶ quot σ n ⟶ 0`.** -/
theorem shortExact_quot [Mono σ] (n : ℕ) :
    (ShortComplex.mk (mulMap σ n) (cokernel.π (mulMap σ n)) (cokernel.condition _)).ShortExact :=
  have := mono_mulMap σ n
  .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

/-- **A morphism into `ℒ^{⊗ 1 + n}` killed by the projection to `quot σ n` is a multiple
of `σ`.** -/
theorem exists_eq_comp_mulMap [Mono σ] (n : ℕ) (τ : 𝟙_ X.Modules ⟶ natTensorPow L (1 + n))
    (hτ : τ ≫ cokernel.π (mulMap σ n) = 0) : ∃ ρ : powSections L n, τ = ρ ≫ mulMap σ n :=
  have := mono_mulMap σ n
  ⟨(shortExact_quot L σ n).exact.lift τ hτ, ((shortExact_quot L σ n).exact.lift_f τ hτ).symm⟩

/-- A morphism out of the unit into the third term of a short exact sequence lifts to the middle
term when `H¹` of the first term vanishes. -/
private theorem exists_comp_eq_of_shortExact_isZero (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h : IsZero (cohomologyOverField k f S.X₁ (0 + 1))) (γ : 𝟙_ X.Modules ⟶ S.X₃) :
    ∃ τ : 𝟙_ X.Modules ⟶ S.X₂, τ ≫ S.g = γ :=
  exists_comp_eq_of_surjective_cohomologyOverFieldMap k f _
    (surjective_cohomologyOverFieldMap_g_of_isZero_succ_X₁ k f hS 0 h) γ

/-! ### On a proper scheme of dimension one over a field -/

section Proper

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]

include f in
/-- A scheme proper over a field is locally Noetherian. -/
theorem isLocallyNoetherian_of_isProper : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian f

include f in
/-- A scheme proper over a field has a Noetherian underlying space. -/
theorem noetherianSpace_of_isProper : TopologicalSpace.NoetherianSpace X := by
  have := isLocallyNoetherian_of_isProper k f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  exact AlgebraicGeometry.IsNoetherian.noetherianSpace

include f in
/-- The tensor powers of an invertible module on a proper scheme over a field are coherent. -/
theorem isCoherent_natTensorPow (n : ℕ) : (natTensorPow L n).IsCoherent := by
  have := isLocallyNoetherian_of_isProper k f
  rw [← Stacks.SectionRingProjTheta.twistPow_unit L n]
  exact Stacks.AlgebraicGeometry.ProperAmpleCohomology.isCoherent_twistPow (𝟙_ X.Modules) L
    (Stacks.AlgebraicGeometry.ProperAmpleCohomology.isCoherent_tensorUnit X) n

include f in
/-- The cokernels of multiplication by a section are coherent. -/
theorem isCoherent_quot (n : ℕ) : (quot σ n).IsCoherent :=
  AlgebraicGeometry.isCoherent_cokernel_of_isCoherent (isCoherent_natTensorPow L k f n)
    (isCoherent_natTensorPow L k f (1 + n)) _

include f in
/-- **A coherent module supported inside the support of `quot σ 1` has no higher cohomology.** -/
theorem isZero_cohomologyOverField_of_supp_subset [Mono σ] (hdim : topologicalKrullDim X ≤ 1)
    (F : X.Modules) (hFc : F.IsCoherent)
    (hF : SheafOfModules.supp F ⊆ SheafOfModules.supp (quot σ 1)) (i : ℕ) (hi : 0 < i) :
    IsZero (cohomologyOverField k f F i) := by
  have := hFc
  have := isLocallyNoetherian_of_isProper k f
  have := noetherianSpace_of_isProper k f
  have hfin : (natTensorPow L (1 + 1)).IsFiniteType :=
    have := isCoherent_natTensorPow L k f (1 + 1)
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).2
  have h1 := topologicalKrullDim_supp_quot_le_zero L hdim σ hfin (le_refl 1)
  refine isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k f F ?_ i hi
  exact ((Topology.IsEmbedding.inclusion hF).isInducing.topologicalKrullDim_le).trans h1

omit [IsProper f] in
include f in
/-- **The middle term of a short exact sequence has vanishing `Hⁱ` when the outer terms do.** -/
theorem isZero_cohomologyOverField_X₂ {S : ShortComplex X.Modules} (hS : S.ShortExact) (i : ℕ)
    (h₁ : IsZero (cohomologyOverField k f S.X₁ i)) (h₃ : IsZero (cohomologyOverField k f S.X₃ i)) :
    IsZero (cohomologyOverField k f S.X₂ i) := by
  obtain ⟨_, _, hfg, _, _⟩ := exists_cohomologyOverField_longExactSequence k f hS
  have s₁ := ModuleCat.subsingleton_of_isZero h₁
  have s₃ := ModuleCat.subsingleton_of_isZero h₃
  have : Subsingleton (cohomologyOverField k f S.X₂ i) := ⟨fun a b => by
    obtain ⟨a', ha'⟩ := (hfg i a).mp (Subsingleton.elim _ _)
    obtain ⟨b', hb'⟩ := (hfg i b).mp (Subsingleton.elim _ _)
    rw [← ha', ← hb', Subsingleton.elim a' b']⟩
  exact ModuleCat.isZero_of_subsingleton _

include f in
/-- **`H¹(X, ℒ^{⊗ n}) = 0` for every `n ≥ 1`**, from `H¹(X, ℒ) = 0`, by induction along the
sequences `0 ⟶ ℒ^{⊗ n} ⟶ ℒ^{⊗ n + 1} ⟶ quot σ n ⟶ 0`, whose third terms have no higher
cohomology. -/
theorem isZero_cohomologyOverField_one_natTensorPow [Mono σ] (hdim : topologicalKrullDim X ≤ 1)
    (hH1 : IsZero (cohomologyOverField k f L 1)) :
    ∀ n : ℕ, IsZero (cohomologyOverField k f (natTensorPow L (n + 1)) 1)
  | 0 => hH1.of_iso (cohomologyOverFieldIso k f (λ_ L) 1)
  | n + 1 => by
    have ih := isZero_cohomologyOverField_one_natTensorPow hdim hH1 n
    have hQ : IsZero (cohomologyOverField k f (quot σ (n + 1)) 1) :=
      isZero_cohomologyOverField_of_supp_subset L σ k f hdim _ (isCoherent_quot L σ k f (n + 1))
        (supp_quot_subset_one σ (by omega)) 1 Nat.one_pos
    have h := isZero_cohomologyOverField_X₂ k f (shortExact_quot L σ (n + 1)) 1 ih hQ
    exact h.of_iso (cohomologyOverFieldIso k f
      (eqToIso (congrArg (natTensorPow L) (by omega : n + 1 + 1 = 1 + (n + 1)))) 1)

omit [IsProper f] in
include f in
/-- **Every morphism `𝒪_X ⟶ quot σ n` lifts to `ℒ^{⊗ 1 + n}`** when `H¹(X, ℒ^{⊗ n}) = 0`. -/
theorem exists_comp_cokernelπ_eq [Mono σ] (n : ℕ)
    (hn : IsZero (cohomologyOverField k f (natTensorPow L n) 1))
    (γ : 𝟙_ X.Modules ⟶ quot σ n) :
    ∃ τ : powSections L (1 + n), τ ≫ cokernel.π (mulMap σ n) = γ :=
  exists_comp_eq_of_shortExact_isZero k f (shortExact_quot L σ n) hn γ

include f in
/-- **Multiplication by `t` is surjective on global sections of the cokernels**, as soon as it is
an epimorphism of sheaves (`epi_quotMap`): its kernel is coherent and supported inside the support
of `quot σ 1`, so it has no `H¹`. -/
theorem exists_comp_quotMap_eq [Mono σ] (hdim : topologicalKrullDim X ≤ 1) {e : ℕ}
    (t : powSections L e) {a : ℕ} (ha : 1 ≤ a)
    (hepi : ∀ x, x ∈ Stacks.AmpleFiniteAvoidance.nvLocus L t ∨
      x ∉ SheafOfModules.supp (quot σ (e + a)))
    (γ : 𝟙_ X.Modules ⟶ quot σ (e + a)) :
    ∃ δ : 𝟙_ X.Modules ⟶ quot σ a, δ ≫ quotMap σ t a = γ := by
  have := epi_quotMap σ t a hepi
  have hKc : (kernel (quotMap σ t a)).IsCoherent :=
    AlgebraicGeometry.isCoherent_kernel_of_isCoherent (isCoherent_quot L σ k f a)
      (isCoherent_quot L σ k f (e + a)) _
  have hKs : SheafOfModules.supp (kernel (quotMap σ t a)) ⊆ SheafOfModules.supp (quot σ 1) := by
    intro x hx
    refine supp_quot_subset_one σ ha ?_
    by_contra hxa
    have hsub := ModuleCat.subsingleton_of_isZero
      ((AlgebraicGeometry.Scheme.Modules.notMem_supp_iff_isZero_stalk _ x).mp hxa)
    exact AlgebraicGeometry.notMem_supp_kernel_of_injective_mapFun _ x
      (fun p q _ => @Subsingleton.elim _ hsub p q) hx
  have hK : IsZero (cohomologyOverField k f (kernel (quotMap σ t a)) (0 + 1)) :=
    isZero_cohomologyOverField_of_supp_subset L σ k f hdim _ hKc hKs 1 Nat.one_pos
  exact exists_comp_eq_of_shortExact_isZero k f
    (.mk' (ShortComplex.exact_kernel _) inferInstance inferInstance) hK γ

end Proper

end Stacks.RegularSectionGeneration

end
