module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomologyAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowGroupCanonicalIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupMapOfSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinDivisorKeyFormulaCarrier
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackSquareCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinMemberRuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardGenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardSectionDivisorDimensionDrop
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinCommutativity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemePreimageModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackValue
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionOfGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionSheafModuleMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue

/-!
# Stacks 0ERC over the constructed Chow groups

A part of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinBivariantClass`: proper pushforward
along a closed immersion is the pushforward of the localization sequence, Stacks 0ERC over the
constructed Chow groups, and the bookkeeping of proper pushforwards of classes used for axiom (3)
of Stacks 0ERJ.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] pointTopology

/-! ### Proper pushforward along a closed immersion -/

section ClosedImmersion

variable (D : BaseSpaceDimensionSituation.{u})

/-- The degree of Stacks 0EP1 along a closed immersion is `1`: the integral closed image is the
image, which has the same δ-dimension, and the residue field extension is trivial. -/
private theorem properCycleDegree_eq_one_of_isClosedImmersion {A B : D.Ambient}
    (sB : B ⟶ D.space) (hB : D.IsGood sB) {f : A ⟶ B}
    (hf : IsClosedImmersion D.site D.base D.base_mem f) (hA : D.IsGood (f ≫ sB))
    (V : IntegralClosedSubspace D.site D.base D.base_mem A) :
    properCycleDegree D (f ≫ sB) hA sB hB f V = 1 := by
  have hdim : deltaDimension D sB (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
        hB.1 (D.isDecentSpace_of_isGood sB hB) f V) = deltaDimension D (f ≫ sB) V := by
    rw [IntegralClosedSubspace.closureImage_eq_pushforward D.site D.base D.base_mem hB.1 hA.1
      (D.isDecentSpace_of_isGood sB hB) hf V]
    exact IntegralClosedSubspace.deltaDimension_pushforward D sB hB.2.2 hB.1 hA.1
      (D.isDecentSpace_of_isGood sB hB) hf V
  have hone : functionFieldDegree D (f ≫ sB) hA sB hB f V = 1 :=
    IntegralClosedSubspace.degreeOverClosureImage_eq_one_of_isClosedImmersion D.site D.base
      D.base_mem hB.1 (D.isDecentSpace_of_isGood sB hB) (D.isDecentSpace_of_isGood _ hA) hf V
  rw [properCycleDegree, ite_eq_left hdim, hone, Nat.cast_one]

open scoped Classical in
/-- The multiplicity of Stacks 0EP1 along a closed immersion is the indicator of the image. -/
private theorem properCycleMult_of_isClosedImmersion {A B : D.Ambient} (sB : B ⟶ D.space)
    (hB : D.IsGood sB) {f : A ⟶ B} (hf : IsClosedImmersion D.site D.base D.base_mem f)
    (hA : D.IsGood (f ≫ sB)) (V : IntegralClosedSubspace D.site D.base D.base_mem A)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem B) :
    properCycleMult D (f ≫ sB) hA sB hB f V Z =
      if IntegralClosedSubspace.pushforward D.site D.base D.base_mem hB.1 hA.1
          (D.isDecentSpace_of_isGood sB hB) hf V = Z then 1 else 0 := by
  rw [properCycleMult, properCycleDegree_eq_one_of_isClosedImmersion D sB hB hf hA V,
    IntegralClosedSubspace.closureImage_eq_pushforward D.site D.base D.base_mem hB.1 hA.1
      (D.isDecentSpace_of_isGood sB hB) hf V]

/-- **Proper pushforward along a closed immersion is the pushforward of the localization
sequence.**  For a closed immersion `f : A ⟶ B` over the base, the pushforward of `k`-cycles of
Stacks 0EP1 along `f` carries the coefficient at an integral closed subspace of `A` to the
coefficient at its image and vanishes elsewhere, so it is
`AlgebraicGeometry.Space.cycleGroupClosedPushforward`.  This is
`AlgebraicGeometry.Space.properCyclePushforward_ι_eq_cycleGroupClosedPushforward` for any closed
immersion, not only the inclusion of a closed subspace. -/
theorem properCyclePushforward_eq_cycleGroupClosedPushforward {A B : D.Ambient}
    (sA : A ⟶ D.space) (hA : D.IsGood sA) (sB : B ⟶ D.space) (hB : D.IsGood sB) {f : A ⟶ B}
    (hf : IsClosedImmersion D.site D.base D.base_mem f) (hfB : f ≫ sB = sA)
    (hqc : IsQuasiCompact D.site D.base D.base_mem f) (k : ℤ) (c : CycleGroup D sA k) :
    properCyclePushforward D sA hA sB hB hfB hqc k c =
      cycleGroupClosedPushforward D hB.1 hA.1 (D.isDecentSpace_of_isGood sB hB) hf sB hB.2.2 sA
        hfB k c := by
  classical
  subst hfB
  refine Subtype.ext (funext fun Z => ?_)
  change properCyclePushforwardCoeff D (f ≫ sB) hA sB hB f c.1 Z =
    cycleClosedPushforward D hB.1 hA.1 (D.isDecentSpace_of_isGood sB hB) hf c.1 Z
  by_cases hex : ∃ V, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hB.1 hA.1
      (D.isDecentSpace_of_isGood sB hB) hf V = Z
  · obtain ⟨V₀, rfl⟩ := hex
    rw [cycleClosedPushforward_apply_pushforward, properCyclePushforwardCoeff]
    refine (finsum_eq_single _ V₀ ?_).trans ?_
    · intro V hV
      rw [properCycleMult_of_isClosedImmersion D sB hB hf hA V, ite_eq_right fun h => hV
        (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hB.1 hA.1
          (D.isDecentSpace_of_isGood sB hB) hf h), mul_zero]
    · rw [properCycleMult_of_isClosedImmersion D sB hB hf hA V₀, ite_eq_left rfl, mul_one]
  · rw [cycleClosedPushforward_apply_of_forall_ne D hB.1 hA.1 (D.isDecentSpace_of_isGood sB hB)
      hf c.1 Z fun V hV => hex ⟨V, hV⟩, properCyclePushforwardCoeff]
    refine finsum_eq_zero_of_forall_eq_zero fun V => ?_
    rw [properCycleMult_of_isClosedImmersion D sB hB hf hA V, ite_eq_right fun h => hex ⟨V, h⟩,
      mul_zero]

end ClosedImmersion

/-! ### Stacks 0ERC over the constructed Chow groups -/

section GysinComm

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (σ : L.sections)
    (hL : IsInvertibleSheaf D p hp L)
    (N : Modules.{u, u} D.site D.base D.base_mem X hp.1) (τ : N.sections)
    (hN : IsInvertibleSheaf D p hp N) (k : ℤ)

/-- `E = Z(σ) ⊆ X`. -/
local notation "𝔼σ" => vanishingLocus D p hp L σ
/-- The inclusion `E ⟶ X` as a morphism of algebraic spaces. -/
local notation "𝕢" => ObjectProperty.homMk (Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ)))
/-- `𝒩|_E`. -/
local notation "ℕE" => pullbackSheaf D p hp
  (Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ)) ≫ p)
  (isGood_vanishingLocus D p hp L σ)
  (ObjectProperty.homMk (Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ)))) N
/-- `τ|_E`. -/
local notation "τE" => pullbackGlobalSection D p hp
  (Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ)) ≫ p)
  (isGood_vanishingLocus D p hp L σ)
  (ObjectProperty.homMk (Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ)))) N τ
/-- `Z(τ|_E) ⊆ E`. -/
local notation "ℤ₁" => vanishingLocus D (Subfunctor.ι (Subtype.val (vanishingLocus D p hp L σ)) ≫ p)
  (isGood_vanishingLocus D p hp L σ) ℕE τE

/-- `D' = Z(τ) ⊆ X`. -/
local notation "𝔽τ" => vanishingLocus D p hp N τ
/-- The inclusion `D' ⟶ X` as a morphism of algebraic spaces. -/
local notation "𝕣" => ObjectProperty.homMk (Subfunctor.ι (Subtype.val (vanishingLocus D p hp N τ)))
/-- `ℒ|_{D'}`. -/
local notation "𝕃F" => pullbackSheaf D p hp
  (Subfunctor.ι (Subtype.val (vanishingLocus D p hp N τ)) ≫ p)
  (isGood_vanishingLocus D p hp N τ)
  (ObjectProperty.homMk (Subfunctor.ι (Subtype.val (vanishingLocus D p hp N τ)))) L
/-- `σ|_{D'}`. -/
local notation "σF" => pullbackGlobalSection D p hp
  (Subfunctor.ι (Subtype.val (vanishingLocus D p hp N τ)) ≫ p)
  (isGood_vanishingLocus D p hp N τ)
  (ObjectProperty.homMk (Subfunctor.ι (Subtype.val (vanishingLocus D p hp N τ)))) L σ
/-- `Z(σ|_{D'}) ⊆ D'`. -/
local notation "ℤ₂" => vanishingLocus D (Subfunctor.ι (Subtype.val (vanishingLocus D p hp N τ)) ≫ p)
  (isGood_vanishingLocus D p hp N τ) 𝕃F σF

include hL hN in
/-- **Stacks 0ERC on cycles, read on `Z(σ|_{D'})`.**  For `α ∈ Z_{k+2}(X)` and any proper
`h : Z(τ|_D) ⟶ Z(σ|_{D'})` over `X`, the classes of `h_*((j')^* i^* α)` and of `j^*(i')^* α`
agree in `CH_k(Z(σ|_{D'}))`.  Over `X` the map `h` is the identification
`AlgebraicGeometry.Space.vanishingLocusIntersectionComparison` of the two readings of `D ∩ D'`,
the inclusions being monomorphisms; along that closed immersion proper pushforward is the
pushforward of the localization sequence, and the statement is Stacks 0ERC over the
constructed Chow groups,
`AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_gysinCycleMap_comm`. -/
theorem chowClassCanonical_properCyclePushforward_gysin_gysin_eq
    (h : (ℤ₁).1.toFunctor ⟶ (ℤ₂).1.toFunctor)
    (hh : h ≫ (ℤ₂).1.ι ≫ (𝔽τ).1.ι = (ℤ₁).1.ι ≫ (𝔼σ).1.ι)
    (hhp : IsProper D.site D.base D.base_mem h) (α : CycleGroup D p (k + 1 + 1)) :
    chowClassCanonical.{u + 1} D ((ℤ₂).1.ι ≫ (𝔽τ).1.ι ≫ p)
        (isGood_vanishingLocus D _ (isGood_vanishingLocus D p hp N τ) 𝕃F σF) k
        (properCyclePushforward D ((ℤ₁).1.ι ≫ (𝔼σ).1.ι ≫ p)
          (isGood_vanishingLocus D _ (isGood_vanishingLocus D p hp L σ) ℕE τE)
          ((ℤ₂).1.ι ≫ (𝔽τ).1.ι ≫ p)
          (isGood_vanishingLocus D _ (isGood_vanishingLocus D p hp N τ) 𝕃F σF)
          (by simpa only [Category.assoc] using congrArg (· ≫ p) hh) hhp.2.1.2 k
          (gysinCycleMap D ((𝔼σ).1.ι ≫ p) ℤ₁
            (isGood_vanishingLocus D _ (isGood_vanishingLocus D p hp L σ) ℕE τE) k
            (sectionGysinRule D ((𝔼σ).1.ι ≫ p) (isGood_vanishingLocus D p hp L σ) ℕE τE k
              (isInvertibleSheaf_pullbackSheaf D p hp _ _ _ N hN))
            (gysinCycleMap D p 𝔼σ (isGood_vanishingLocus D p hp L σ) (k + 1)
              (sectionGysinRule D p hp L σ (k + 1) hL) α))) =
      chowClassCanonical.{u + 1} D ((ℤ₂).1.ι ≫ (𝔽τ).1.ι ≫ p)
        (isGood_vanishingLocus D _ (isGood_vanishingLocus D p hp N τ) 𝕃F σF) k
        (gysinCycleMap D ((𝔽τ).1.ι ≫ p) ℤ₂
          (isGood_vanishingLocus D _ (isGood_vanishingLocus D p hp N τ) 𝕃F σF) k
          (sectionGysinRule D ((𝔽τ).1.ι ≫ p) (isGood_vanishingLocus D p hp N τ) 𝕃F σF k
            (isInvertibleSheaf_pullbackSheaf D p hp _ _ _ L hL))
          (gysinCycleMap D p 𝔽τ (isGood_vanishingLocus D p hp N τ) (k + 1)
            (sectionGysinRule D p hp N τ (k + 1) hN) α)) := by
  have he : h = vanishingLocusIntersectionComparison D p hp σ τ hL hN :=
    (cancel_mono ((ℤ₂).1.ι ≫ (𝔽τ).1.ι)).1
      (hh.trans (vanishingLocusIntersectionComparison_comp_ι D p hp σ τ hL hN).symm)
  have hci : IsClosedImmersion D.site D.base D.base_mem h :=
    he ▸ isClosedImmersion_vanishingLocusIntersectionComparison D p hp σ τ hL hN
  rw [properCyclePushforward_eq_cycleGroupClosedPushforward D _ _ _ _ hci]
  have H := chowClassCanonical_gysinCycleMap_gysinCycleMap_comm.{u + 1, u} D p hp σ τ hL hN k α
  subst he
  exact H

include hL hN in
/-- The two readings `Z(τ|_D)` and `Z(σ|_{D'})` of `D ∩ D'` are identified over `X`, by
`AlgebraicGeometry.Space.vanishingLocusIntersectionComparison`. -/
theorem exists_gysinComm_hom :
    ∃ h : (ℤ₁).1.toFunctor ⟶ (ℤ₂).1.toFunctor,
      h ≫ (ℤ₂).1.ι ≫ (𝔽τ).1.ι = (ℤ₁).1.ι ≫ (𝔼σ).1.ι ∧ IsProper D.site D.base D.base_mem h :=
  ⟨vanishingLocusIntersectionComparison D p hp σ τ hL hN,
    vanishingLocusIntersectionComparison_comp_ι D p hp σ τ hL hN,
    isProper_of_isIso D.site D.base D.base_mem
      (vanishingLocusIntersectionComparison D p hp σ τ hL hN)⟩

end GysinComm

/-! ### Stacks 0ERJ (3) for the Gysin class of Stacks 0ERP -/

section GysinAssembly

variable (D : BaseSpaceDimensionSituation.{u})

/-- **Bookkeeping of proper pushforwards of classes along a composite.**  If `[c_* x] = [y]`, then
`[(c ≫ b)_* x] = [b_* y]` (Stacks 0EQC and Stacks 0EP2). -/
private theorem chowClassCanonical_properCyclePushforward_of_comp {A B T : D.Ambient}
    (sA : A ⟶ D.space) (sB : B ⟶ D.space) (sT : T ⟶ D.space) (hA : D.IsGood sA)
    (hB : D.IsGood sB) (hT : D.IsGood sT) {b : B ⟶ T} {c : A ⟶ B} (hbB : b ≫ sT = sB)
    (hcB : c ≫ sB = sA) (hb : IsProper D.site D.base D.base_mem b)
    (hc : IsProper D.site D.base D.base_mem c) (k : ℤ) (x : CycleGroup D sA k)
    (y : CycleGroup D sB k)
    (hxy : chowClassCanonical.{u + 1} D sB hB k
        (properCyclePushforward D sA hA sB hB hcB hc.2.1.2 k x) =
      chowClassCanonical.{u + 1} D sB hB k y) :
    chowClassCanonical.{u + 1} D sT hT k
        (properCyclePushforward D sA hA sT hT (by rw [Category.assoc, hbB, hcB])
          (isProper_comp D.site D.base D.base_mem hA.1 hB.1 hT.1 c b hc hb).2.1.2 k x) =
      chowClassCanonical.{u + 1} D sT hT k
        (properCyclePushforward D sB hB sT hT hbB hb.2.1.2 k y) := by
  rw [← chowGroupCanonicalProperPushforward_chowClassCanonical D sB hB sT hT hbB hb k y, ← hxy,
    chowGroupCanonicalProperPushforward_chowClassCanonical,
    properCyclePushforward_comp D sA sB sT hA hB hT hcB hbB hc hb]

/-- **Bookkeeping of proper pushforwards of classes, read through a monomorphism.**  If `ε ≫ a`
and `δ ≫ b` agree after a monomorphism `m₀` (both read off through `F ⟶ Y`), `[ε_* x₁] = [x₂]`
and `δ_* x₁ = x₁'`, then `[a_* x₂] = [b_* x₁']` (Stacks 0EQC and Stacks 0EP2). -/
theorem chowClassCanonical_properCyclePushforward_of_comp_eq_comp_of_mono
    {S S' A T Y F : D.Ambient} (sS : S ⟶ D.space) (sS' : S' ⟶ D.space) (sA : A ⟶ D.space)
    (sT : T ⟶ D.space) (hS : D.IsGood sS) (hS' : D.IsGood sS') (hA : D.IsGood sA)
    (hT : D.IsGood sT) {ε : S ⟶ A} {a : A ⟶ T} {δ : S ⟶ S'} {b : S' ⟶ T} (m₀ : T ⟶ Y)
    [Mono m₀] (hεB : ε ≫ sA = sS) (haB : a ≫ sT = sA) (hδB : δ ≫ sS' = sS)
    (hbB : b ≫ sT = sS') (hεp : IsProper D.site D.base D.base_mem ε)
    (hap : IsProper D.site D.base D.base_mem a) (hδp : IsProper D.site D.base D.base_mem δ)
    (hbp : IsProper D.site D.base D.base_mem b) {ιA : A ⟶ F} {ιF : F ⟶ Y} {ιS : S ⟶ F}
    {ιS' : S' ⟶ F} (ha : a ≫ m₀ = ιA ≫ ιF) (hε : ε ≫ ιA = ιS) (hδ : δ ≫ ιS' = ιS)
    (hb : b ≫ m₀ = ιS' ≫ ιF) (k : ℤ) (x₁ : CycleGroup D sS k) (x₂ : CycleGroup D sA k)
    (x₁' : CycleGroup D sS' k)
    (h₁ : chowClassCanonical.{u + 1} D sA hA k
        (properCyclePushforward D sS hS sA hA hεB hεp.2.1.2 k x₁) =
      chowClassCanonical.{u + 1} D sA hA k x₂)
    (h₂ : properCyclePushforward D sS hS sS' hS' hδB hδp.2.1.2 k x₁ = x₁') :
    chowClassCanonical.{u + 1} D sT hT k
        (properCyclePushforward D sA hA sT hT haB hap.2.1.2 k x₂) =
      chowClassCanonical.{u + 1} D sT hT k
        (properCyclePushforward D sS' hS' sT hT hbB hbp.2.1.2 k x₁') := by
  have hmap : ε ≫ a = δ ≫ b := by
    rw [← cancel_mono m₀]
    simp only [Category.assoc, ha, reassoc_of% hε, hb, reassoc_of% hδ]
  exact (chowClassCanonical_properCyclePushforward_of_comp D sS sA sT hS hA hT haB hεB hap hεp k
    x₁ x₂ h₁).symm.trans
    ((congrArg (chowClassCanonical.{u + 1} D sT hT k)
      (properCyclePushforward_congr D sS hS sT hT hmap _ _ _ _ k x₁)).trans
    (chowClassCanonical_properCyclePushforward_of_comp D sS sS' sT hS hS' hT hbB hδB hbp hδp k x₁
      x₁' (congrArg (chowClassCanonical.{u + 1} D sS' hS' k) h₂)))

/-- **Bookkeeping of proper pushforwards of classes along a composite.**  If `[h_* x₁'] = [z]`
and `[w] = [e_* z]`, then `j' = h ≫ e ≫ ψ` is proper, agrees with `ιS' ≫ ιF` after `m₀` when the
pieces do, and `[j'_* x₁'] = [ψ_* w]` (Stacks 0EQC and Stacks 0EP2). -/
theorem chowClassCanonical_properCyclePushforward_comp_comp_of_mono
    {S' C H T Y F Z : D.Ambient} (sS' : S' ⟶ D.space) (sC : C ⟶ D.space) (sH : H ⟶ D.space)
    (sT : T ⟶ D.space) (hS' : D.IsGood sS') (hC : D.IsGood sC) (hH : D.IsGood sH)
    (hT : D.IsGood sT) {h : S' ⟶ C} {e : C ⟶ H} {ψ : H ⟶ T} (m₀ : T ⟶ Y)
    (hhB : h ≫ sC = sS') (heB : e ≫ sH = sC) (hψB : ψ ≫ sT = sH)
    (hhp : IsProper D.site D.base D.base_mem h) (hep : IsProper D.site D.base D.base_mem e)
    (hψp : IsProper D.site D.base D.base_mem ψ) {ιS' : S' ⟶ F} {ιF : F ⟶ Y} {ιC : C ⟶ Z}
    {ιZ : Z ⟶ Y} {ιH : H ⟶ Z} (hh : h ≫ ιC ≫ ιZ = ιS' ≫ ιF) (he : e ≫ ιH = ιC)
    (hψ : ψ ≫ m₀ = ιH ≫ ιZ) (k : ℤ) (x₁' : CycleGroup D sS' k) (z : CycleGroup D sC k)
    (w : CycleGroup D sH k)
    (h₃ : chowClassCanonical.{u + 1} D sC hC k
        (properCyclePushforward D sS' hS' sC hC hhB hhp.2.1.2 k x₁') =
      chowClassCanonical.{u + 1} D sC hC k z)
    (h₄ : chowClassCanonical.{u + 1} D sH hH k w =
      chowClassCanonical.{u + 1} D sH hH k
        (properCyclePushforward D sC hC sH hH heB hep.2.1.2 k z)) :
    ∃ (j' : S' ⟶ T) (hj'B : j' ≫ sT = sS') (hj' : IsProper D.site D.base D.base_mem j')
      (_ : j' ≫ m₀ = ιS' ≫ ιF),
      chowClassCanonical.{u + 1} D sT hT k
          (properCyclePushforward D sS' hS' sT hT hj'B hj'.2.1.2 k x₁') =
        chowClassCanonical.{u + 1} D sT hT k
          (properCyclePushforward D sH hH sT hT hψB hψp.2.1.2 k w) := by
  have heψB : (e ≫ ψ) ≫ sT = sC := by rw [Category.assoc, hψB, heB]
  have heψp := isProper_comp D.site D.base D.base_mem hC.1 hH.1 hT.1 e ψ hep hψp
  have hheψB : (h ≫ e ≫ ψ) ≫ sT = sS' := by rw [Category.assoc, heψB, hhB]
  have hheψp := isProper_comp D.site D.base D.base_mem hS'.1 hC.1 hT.1 h (e ≫ ψ) hhp heψp
  refine ⟨h ≫ e ≫ ψ, hheψB, hheψp, ?_, ?_⟩
  · simp only [Category.assoc, hψ, reassoc_of% he, hh]
  exact (chowClassCanonical_properCyclePushforward_of_comp D sS' sC sT hS' hC hT heψB hhB heψp hhp
    k x₁' z h₃).trans
    (chowClassCanonical_properCyclePushforward_of_comp D sC sH sT hC hH hT hψB heB hψp hep k z w
      h₄.symm)

/-- **The Gysin cycle of a pulled-back pair does not see how the structure morphism is written.**
For two equal structure morphisms `s₁ = s₂` of `Y''` and `q : Y'' ⟶ Y`, the vanishing loci of
`q^*(𝒩, τ)` over `s₁` and over `s₂` are included in one another over `Y''`, and the inclusion
carries the Gysin cycle of Stacks 0ER1 over `s₁` to the one over `s₂`. -/
theorem exists_properCyclePushforward_gysinCycleMap_structure_eq {Y Y'' : D.Ambient}
    (s : Y ⟶ D.space) (hs : D.IsGood s) (N : Modules.{u, u} D.site D.base D.base_mem Y hs.1)
    (τ : N.sections) (hN : IsInvertibleSheaf D s hs N) (q : Y'' ⟶ Y) (s₁ s₂ : Y'' ⟶ D.space)
    (h₁ : D.IsGood s₁) (h₂ : D.IsGood s₂) (h : s₁ = s₂) (k : ℤ) (x₁ : CycleGroup D s₁ (k + 1))
    (x₂ : CycleGroup D s₂ (k + 1)) (hx : HEq x₁ x₂) :
    ∃ (δ : (vanishingLocus D s₁ h₁ (pullbackSheaf D s hs s₁ h₁ (ObjectProperty.homMk q) N)
          (pullbackGlobalSection D s hs s₁ h₁ (ObjectProperty.homMk q) N τ)).1.toFunctor ⟶
        (vanishingLocus D s₂ h₂ (pullbackSheaf D s hs s₂ h₂ (ObjectProperty.homMk q) N)
          (pullbackGlobalSection D s hs s₂ h₂ (ObjectProperty.homMk q) N τ)).1.toFunctor)
      (hδ : δ ≫ (vanishingLocus D s₂ h₂ (pullbackSheaf D s hs s₂ h₂ (ObjectProperty.homMk q) N)
          (pullbackGlobalSection D s hs s₂ h₂ (ObjectProperty.homMk q) N τ)).1.ι =
        (vanishingLocus D s₁ h₁ (pullbackSheaf D s hs s₁ h₁ (ObjectProperty.homMk q) N)
          (pullbackGlobalSection D s hs s₁ h₁ (ObjectProperty.homMk q) N τ)).1.ι)
      (hδp : IsProper D.site D.base D.base_mem δ),
      properCyclePushforward D
          ((vanishingLocus D s₁ h₁ (pullbackSheaf D s hs s₁ h₁ (ObjectProperty.homMk q) N)
            (pullbackGlobalSection D s hs s₁ h₁ (ObjectProperty.homMk q) N τ)).1.ι ≫ s₁)
          (isGood_vanishingLocus D s₁ h₁ _ _)
          ((vanishingLocus D s₂ h₂ (pullbackSheaf D s hs s₂ h₂ (ObjectProperty.homMk q) N)
            (pullbackGlobalSection D s hs s₂ h₂ (ObjectProperty.homMk q) N τ)).1.ι ≫ s₂)
          (isGood_vanishingLocus D s₂ h₂ _ _) (by rw [← Category.assoc δ, hδ, ← h]) hδp.2.1.2 k
          (gysinCycleMap D s₁
            (vanishingLocus D s₁ h₁ (pullbackSheaf D s hs s₁ h₁ (ObjectProperty.homMk q) N)
              (pullbackGlobalSection D s hs s₁ h₁ (ObjectProperty.homMk q) N τ))
            (isGood_vanishingLocus D s₁ h₁ _ _) k
            (sectionGysinRule D s₁ h₁ _ _ k
              (isInvertibleSheaf_pullbackSheaf D s hs s₁ h₁ (ObjectProperty.homMk q) N hN)) x₁) =
        gysinCycleMap D s₂
          (vanishingLocus D s₂ h₂ (pullbackSheaf D s hs s₂ h₂ (ObjectProperty.homMk q) N)
            (pullbackGlobalSection D s hs s₂ h₂ (ObjectProperty.homMk q) N τ))
          (isGood_vanishingLocus D s₂ h₂ _ _) k
          (sectionGysinRule D s₂ h₂ _ _ k
            (isInvertibleSheaf_pullbackSheaf D s hs s₂ h₂ (ObjectProperty.homMk q) N hN)) x₂ := by
  subst h
  obtain rfl := eq_of_heq hx
  exact ⟨𝟙 _, Category.id_comp _, isProper_of_isIso D.site D.base D.base_mem _,
    properCyclePushforward_id D _ _ _ k _⟩

end GysinAssembly

end AlgebraicGeometry.Space

end
