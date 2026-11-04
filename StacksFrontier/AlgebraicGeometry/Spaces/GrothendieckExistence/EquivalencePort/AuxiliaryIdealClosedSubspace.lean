module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.AuxiliaryIdealAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCoherentEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.IdealQuotientPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.FormalFunctionsProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CompletionFullyFaithfulProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Reading hypothesis (1) of Stacks 08BC on the closed subspaces `X_e`

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over `Spec A`.  Direct image along `i`
commutes with reduction modulo the powers of `I 𝒪`
(`AlgebraicGeometry.Space.C1573.pushforwardBaseQuotientIso`), detects annihilation by them, and
preserves and reflects support proper over `Spec A`.  When `Z` is cut out by `𝓚^e`, these
facts turn the hypothesis that completion along `I 𝒪_Z` is an equivalence into
`AlgebraicGeometry.Space.C1573.KTorsionEssSurj`.

## Main results

* `AlgebraicGeometry.Space.C1573.kTorsionEssSurj_of_essSurj`: if completion along `I 𝒪_Z` is
  essentially surjective for the closed subspace `Z` cut out by `𝓚^e`, then every coherent adic
  system on `X` with proper support whose terms are killed by `𝓚^e` is a completion.
* `AlgebraicGeometry.Space.C1573.essImage_completionFunctorProperOver_of_auxiliaryIdeal`:
  Stacks 08BC.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
attribute [local instance] pointTopology

section Generic

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- **`𝓘^k` annihilates `M` exactly when `M ⟶ M / 𝓘^k M` is an isomorphism.** -/
theorem C1573.isPowAnnihilated_iff_isIso_projection (k : ℕ) (M : Modules.{u, u} B S hS F hF) :
    IsPowAnnihilated B S hS F hF 𝓘 k M ↔
      IsIso (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k M) := by
  refine ⟨fun h => isIso_π_idealPowerMultiple_of_eq_bot B S hS F hF 𝓘 k M
    ((idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 k M).2 h), fun h => ?_⟩
  have hι : (idealPowerSubsheaf B S hS F hF 𝓘 k M).ι = 0 :=
    (cancel_mono (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k M)).1
      ((cokernel.condition _).trans zero_comp.symm)
  exact (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 k M).1
    ((submodule_ι_eq_zero_iff B S hS F hF _).1 hι)

end Generic

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {Z X : AlgebraicSpaces B (Spec (.of A)) hA} (i : Z ⟶ X)
  (hi : IsClosedImmersion B (Spec (.of A)) hA i.hom)

section Support

variable (f : X ⟶ schemeSpace (baseObject A B hA))
  (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)

include hi hf in
/-- If `f : X ⟶ Spec A` is locally of finite type and `i : Z ⟶ X` is a closed immersion, then
`i ≫ f` is locally of finite type. -/
theorem C1573.isLocallyOfFiniteType_closedImmersion_comp :
    IsLocallyOfFiniteType B (Spec (.of A)) hA (i ≫ f).hom :=
  isLocallyOfFiniteType_comp B (Spec (.of A)) hA Z.2 X.2 (schemeSpace (baseObject A B hA)).2
    i.hom f.hom
    (isLocallyOfFiniteType_of_isClosedImmersion B (Spec (.of A)) hA i.hom hi) hf

include hi in
/-- **Direct image along a closed immersion preserves support proper over `Spec A`.** -/
theorem C1573.hasProperSupport_modulePushforward (G : Modules.{u, u} B (Spec (.of A)) hA Z.1 Z.2)
    (hGcl : IsClosed (supportOfSheaf B (Spec (.of A)) hA Z.1 ((SheafOfModules.toSheaf _).obj G)))
    (h : HasProperSupport B (Spec (.of A)) hA Z.2 (schemeSpace (baseObject A B hA)).2 (i ≫ f).hom
      (isLocallyOfFiniteType_closedImmersion_comp i hi f hf) ((SheafOfModules.toSheaf _).obj G)) :
    HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj ((modulePushforward B (Spec (.of A)) hA i).obj G)) := by
  have hsupp := supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion B (Spec (.of A)) hA
    i hi G hGcl
  obtain ⟨hcl, hp⟩ := h
  have hp' := isProperOver_image_of_universallyClosed B (Spec (.of A)) hA Z.2 X.2
    (schemeSpace (baseObject A B hA)).2 i.hom f.hom
    (universallyClosed_of_isClosedImmersion B (Spec (.of A)) hA Z.2 X.2 i.hom hi)
    (isLocallyOfFiniteType_closedImmersion_comp i hi f hf) hf _ hcl hp
  unfold HasProperSupport
  rw [hsupp]
  exact ⟨_, hp'⟩

include hi in
/-- **Direct image along a closed immersion reflects support proper over `Spec A`.** -/
theorem C1573.hasProperSupport_of_modulePushforward (G : Modules.{u, u} B (Spec (.of A)) hA Z.1 Z.2)
    (hGcl : IsClosed (supportOfSheaf B (Spec (.of A)) hA Z.1 ((SheafOfModules.toSheaf _).obj G)))
    (h : HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj ((modulePushforward B (Spec (.of A)) hA i).obj G))) :
    HasProperSupport B (Spec (.of A)) hA Z.2 (schemeSpace (baseObject A B hA)).2 (i ≫ f).hom
      (isLocallyOfFiniteType_closedImmersion_comp i hi f hf)
      ((SheafOfModules.toSheaf _).obj G) := by
  have hsupp := supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion B (Spec (.of A)) hA
    i hi G hGcl
  obtain ⟨hcl, hp⟩ := h
  have hpre := isProperOver_preimage_of_isProper B (Spec (.of A)) hA Z.2 X.2
    (schemeSpace (baseObject A B hA)).2 i.hom f.hom
    (isProper_of_isClosedImmersion B (Spec (.of A)) hA Z.2 X.2 i.hom hi)
    (isLocallyOfFiniteType_closedImmersion_comp i hi f hf) hf _ hcl hp
  refine ⟨hGcl, isProperOver_of_subset B (Spec (.of A)) hA Z.2 (schemeSpace (baseObject A B hA)).2
    _ _ _ _ hGcl _ ?_ hpre⟩
  intro p hp
  rw [Set.mem_preimage, hsupp]
  exact ⟨p, hp, rfl⟩

end Support

section KernelIdeal

variable (K : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1
        X.2).O))).Submodule) (e : ℕ)
  (hker : SheafOfModules.kerIdeal (structureSharp B (Spec (.of A)) hA i) =
    idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K e (SheafOfModules.unit _))

include hker in
/-- A module annihilated by the ideal `𝓚^e` cutting out `Z` is annihilated by `𝓚^e` on every
chart. -/
theorem C1573.isPowAnnihilated_of_annihilatedByKerIdeal
    (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (hM : AnnihilatedByKerIdeal B (Spec (.of A)) hA i M) :
    IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K e M := by
  intro U r hr x
  refine hM (op U) r ?_ x
  rw [hker]
  refine le_idealPowerSubsheaf_obj B (Spec (.of A)) hA X.1 X.2 K e (SheafOfModules.unit _) U ?_
  nth_rewrite 1 [← mul_one r]
  exact Submodule.smul_mem_smul hr Submodule.mem_top

include hker in
/-- **A module annihilated by `𝓚^e` on every chart is annihilated by the ideal `𝓚^e` cutting out
`Z`**, for `𝓚` quasi-coherent: over an affine chart the sections of `𝓚^e` are `𝓚(U)^e`. -/
theorem C1573.annihilatedByKerIdeal_of_isPowAnnihilated
    (hK : K.toSheafOfModules.IsQuasicoherentOnSite)
    (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (hM : IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K e M) :
    AnnihilatedByKerIdeal B (Spec (.of A)) hA i M := by
  suffices h : ∀ (U : SmallEtale B (Spec (.of A)) hA X.1)
      (a : chartRing B (Spec (.of A)) hA X.1 X.2 U),
      a ∈ (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K e (SheafOfModules.unit _)).obj (op U) →
        ∀ m : M.val.obj (op U), a • m = 0 by
    intro U a ha m
    rw [hker] at ha
    exact h U.unop a ha m
  intro U a ha m
  have hunit := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B (Spec (.of A)) hA X.1 X.2 _
    (SheafOfModules.isQuasicoherentOnSite_unit _)
  have hKc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B (Spec (.of A)) hA X.1 X.2 _ hK
  have key : ∀ (V : (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).C) (g : V ⟶ U),
      IsAffine (chartScheme V) → M.val.map g.op (a • m) = M.val.map g.op 0 := fun V g hV => by
    rw [map_zero]
    refine (PresheafOfModules.map_smul M.val g.op a m).trans ?_
    have ha' := (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K e
      (SheafOfModules.unit _)).map_mem g.op ha
    rw [idealPowerMultiple_eq_idealPowSubmodule] at ha'
    have ha'' : _ ∈ chartSubmodule B (Spec (.of A)) hA X.1 X.2
        (idealPowSubmodule K e (SheafOfModules.unit _)) V := ha'
    rw [chartSubmodule_idealPowSubmodule_eq_of_isAffine B (Spec (.of A)) hA X.1 X.2 K _ hunit hKc
      e hV] at ha''
    have h3 : _ ∈ chartSectionIdeal B (Spec (.of A)) hA X.1 X.2 K V ^ e •
        (⊤ : Ideal (chartRing B (Spec (.of A)) hA X.1 X.2 V)) := ha''
    rw [smul_eq_mul, Ideal.mul_top] at h3
    exact hM V _ h3 _
  exact SmallEtale.C1573.eq_of_forall_isAffine B (Spec (.of A)) hA X.1 X.2
    (Stacks.SheafOfModules.ImageSubsheaf.isSheaf_forget M) key

end KernelIdeal

section Quotient

variable [IsNoetherianRing A] (I : Ideal A)

/-- **`i_* (M / I^k M) ≅ (i_* M) / I^k (i_* M)`.** -/
def C1573.pushforwardBaseQuotientIso (M : Modules.{u, u} B (Spec (.of A)) hA Z.1 Z.2) (k : ℕ) :
    (modulePushforward B (Spec (.of A)) hA i).obj
        (smallEtaleAdicQuotient B (Spec (.of A)) hA Z.1 Z.2 (baseIdealSubmodule Z.1 Z.2 I) k M) ≅
      smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) k
        ((modulePushforward B (Spec (.of A)) hA i).obj M) :=
  (modulePushforward B (Spec (.of A)) hA i).mapIso (baseIdealQuotientIso M I k) ≪≫
    pushforwardIdealQuotientIso i hi M (exists_generators_pow I k).choose_spec.choose
      (exists_generators_pow I k).choose_spec.choose_spec ≪≫
    (baseIdealQuotientIso ((modulePushforward B (Spec (.of A)) hA i).obj M) I k).symm

/-- The direct image of the projection `M ⟶ M / I^k M` followed by `pushforwardBaseQuotientIso`
is the projection `i_* M ⟶ (i_* M) / I^k (i_* M)`. -/
@[reassoc]
theorem C1573.map_projection_pushforwardBaseQuotientIso_hom
    (M : Modules.{u, u} B (Spec (.of A)) hA Z.1 Z.2) (k : ℕ) :
    (modulePushforward B (Spec (.of A)) hA i).map
        (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA Z.1 Z.2 (baseIdealSubmodule Z.1 Z.2 I)
          k M) ≫
      (pushforwardBaseQuotientIso i hi I M k).hom =
    smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) k
      ((modulePushforward B (Spec (.of A)) hA i).obj M) := by
  simp only [pushforwardBaseQuotientIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Functor.map_comp,
    smallEtaleAdicQuotientProjection_baseIdealQuotientIso_hom, ← Category.assoc,
    pushforward_map_idealQuotientπ_pushforwardIdealQuotientIso_hom, Iso.comp_inv_eq,
    smallEtaleAdicQuotientProjection_baseIdealQuotientIso_hom]

include hi in
/-- **`I^k 𝒪_X` annihilates `i_* M` exactly when `I^k 𝒪_Z` annihilates `M`.** -/
theorem C1573.isPowAnnihilated_modulePushforward_iff
    (M : Modules.{u, u} B (Spec (.of A)) hA Z.1 Z.2) (k : ℕ) :
    IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) k
        ((modulePushforward B (Spec (.of A)) hA i).obj M) ↔
      IsPowAnnihilated B (Spec (.of A)) hA Z.1 Z.2 (baseIdealSubmodule Z.1 Z.2 I) k M := by
  rw [isPowAnnihilated_iff_isIso_projection, isPowAnnihilated_iff_isIso_projection,
    ← map_projection_pushforwardBaseQuotientIso_hom i hi I M k, isIso_comp_right_iff]
  exact ⟨fun _ => (fullyFaithfulModulePushforward B (Spec (.of A)) hA i hi).isIso_of_isIso_map _,
    fun _ => inferInstance⟩

/-- `pushforwardBaseQuotientIso` commutes with the transition maps
`M / I^(k+1) M ⟶ M / I^k M` and `(i_* M) / I^(k+1) (i_* M) ⟶ (i_* M) / I^k (i_* M)`. -/
@[reassoc]
theorem C1573.map_transition_pushforwardBaseQuotientIso_hom
    (M : Modules.{u, u} B (Spec (.of A)) hA Z.1 Z.2) (k : ℕ) :
    (modulePushforward B (Spec (.of A)) hA i).map
        (smallEtaleAdicQuotientTransition B (Spec (.of A)) hA Z.1 Z.2 (baseIdealSubmodule Z.1 Z.2 I)
          k M) ≫
      (pushforwardBaseQuotientIso i hi I M k).hom =
    (pushforwardBaseQuotientIso i hi I M (k + 1)).hom ≫
      smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) k
        ((modulePushforward B (Spec (.of A)) hA i).obj M) := by
  have h1 := map_projection_pushforwardBaseQuotientIso_hom i hi I M (k + 1)
  rw [← Iso.eq_comp_inv] at h1
  refine (cancel_epi (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2
      (baseIdealSubmodule X.1 X.2 I) (k + 1) ((modulePushforward B (Spec (.of A)) hA i).obj M) ≫
        (pushforwardBaseQuotientIso i hi I M (k + 1)).inv)).1 ?_
  rw [← h1, ← Functor.map_comp_assoc, smallEtaleAdicQuotientProjection_comp_transition,
    map_projection_pushforwardBaseQuotientIso_hom,
    map_projection_pushforwardBaseQuotientIso_hom_assoc,
    smallEtaleAdicQuotientProjection_comp_transition]

end Quotient

section Descent

variable [IsNoetherianRing A] (I : Ideal A)
  (E : ℕᵒᵖ ⥤ Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
  (G : ℕ → CoherentModules.{u, u} B (Spec (.of A)) hA Z.1 Z.2)
  (θ : ∀ n, (modulePushforward B (Spec (.of A)) hA i).obj (G n).obj ≅ E.obj (op n))

/-- The transition maps of a system on `X` read on modules `G_n` on `Z` with `i_* G_n ≅ E_n`. -/
def C1573.descendTransition (n : ℕ) : (G (n + 1)).obj ⟶ (G n).obj :=
  (fullyFaithfulModulePushforward B (Spec (.of A)) hA i hi).preimage
    ((θ (n + 1)).hom ≫ E.map (homOfLE (Nat.le_add_right n 1)).op ≫ (θ n).inv)

/-- The direct image of `descendTransition` at `n` is `θ_(n+1) ≫ (E_(n+1) ⟶ E_n) ≫ θ_n⁻¹`. -/
theorem C1573.map_descendTransition (n : ℕ) :
    (modulePushforward B (Spec (.of A)) hA i).map (descendTransition i hi E G θ n) =
      (θ (n + 1)).hom ≫ E.map (homOfLE (Nat.le_add_right n 1)).op ≫ (θ n).inv :=
  (fullyFaithfulModulePushforward B (Spec (.of A)) hA i hi).map_preimage _

/-- **The system `(G_n)` on `Z`** with `i_* G_n ≅ E_n`. -/
def C1573.descendSystem : ℕᵒᵖ ⥤ Modules.{u, u} B (Spec (.of A)) hA Z.1 Z.2 :=
  Functor.ofOpSequence (X := fun n => (G n).obj) (descendTransition i hi E G θ)

/-- The map `G_(n+1) ⟶ G_n` of `descendSystem` is `descendTransition` at `n`. -/
theorem C1573.descendSystem_map_succ (n : ℕ) :
    (descendSystem i hi E G θ).map (homOfLE (Nat.le_add_right n 1)).op =
      descendTransition i hi E G θ n :=
  Functor.ofOpSequence_map_homOfLE_succ (X := fun n => (G n).obj) _ n

/-- `i_* (G_n) ⟶ (E_n)` as inverse systems; it is an isomorphism. -/
def C1573.descendSystemHom :
    descendSystem i hi E G θ ⋙ modulePushforward B (Spec (.of A)) hA i ⟶ E :=
  NatTrans.ofOpSequence (fun n => (θ n).hom) fun n =>
    (congrArg (· ≫ (θ n).hom) ((congrArg (modulePushforward B (Spec (.of A)) hA i).map
      (descendSystem_map_succ i hi E G θ n)).trans (map_descendTransition i hi E G θ n))).trans
      ((Category.assoc _ _ _).trans (congrArg ((θ (n + 1)).hom ≫ ·) ((Category.assoc _ _ _).trans
        ((congrArg (E.map (homOfLE (Nat.le_add_right n 1)).op ≫ ·) (θ n).inv_hom_id).trans
          (Category.comp_id _)))))

/-- The component of `descendSystemHom` at `n` is `θ_n`. -/
theorem C1573.descendSystemHom_app (n : ℕ) :
    (descendSystemHom i hi E G θ).app (op n) = (θ n).hom :=
  rfl

/-- `descendSystemHom : i_* (G_n) ⟶ (E_n)` is an isomorphism of inverse systems. -/
theorem C1573.isIso_descendSystemHom : IsIso (descendSystemHom i hi E G θ) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun n => (θ n.unop).isIso_hom

/-- **`(G_n)` is a coherent `I 𝒪_Z`-adic system** when `(E_n)` is a coherent `I 𝒪_X`-adic
system. -/
theorem C1573.isCoherentAdicSystem_descendSystem
    (hE : IsCoherentAdicSystem B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) E) :
    IsCoherentAdicSystem B (Spec (.of A)) hA Z.1 Z.2 (baseIdealSubmodule Z.1 Z.2 I)
      (descendSystem i hi E G θ) := by
  have hann : ∀ n,
      IsPowAnnihilated B (Spec (.of A)) hA Z.1 Z.2 (baseIdealSubmodule Z.1 Z.2 I) (n + 1)
        (G n).obj := fun n =>
    (isPowAnnihilated_modulePushforward_iff i hi I _ (n + 1)).1
      (isPowAnnihilated_of_iso B (Spec (.of A)) hA X.1 X.2 _ (θ n).symm (n + 1)
        ((idealPowerMultiple_eq_bot_iff B (Spec (.of A)) hA X.1 X.2 _ _ _).1 (hE.2.1 n)))
  refine ⟨fun n => (G n).property,
    fun n => (idealPowerMultiple_eq_bot_iff B (Spec (.of A)) hA Z.1 Z.2 _ _ _).2 (hann n),
    fun n => ?_⟩
  let L := smallEtaleAdicQuotientLift B (Spec (.of A)) hA Z.1 Z.2 (baseIdealSubmodule Z.1 Z.2 I)
    (n + 1) (descendTransition i hi E G θ n) (hann n)
  have hL : smallEtaleAdicQuotientProjection B (Spec (.of A)) hA Z.1 Z.2
      (baseIdealSubmodule Z.1 Z.2 I) (n + 1) (G (n + 1)).obj ≫ L =
        descendTransition i hi E G θ n :=
    smallEtaleAdicQuotientProjection_lift B (Spec (.of A)) hA Z.1 Z.2 _ (n + 1) _ (hann n)
  obtain ⟨e', he'⟩ := hE.2.2 n
  have he'' : smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2
      (baseIdealSubmodule X.1 X.2 I) (n + 1) (E.obj (op (n + 1))) ≫ e'.hom =
        E.map (homOfLE (Nat.le_add_right n 1)).op := he'
  have : Epi ((modulePushforward B (Spec (.of A)) hA i).map
      (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA Z.1 Z.2 (baseIdealSubmodule Z.1 Z.2 I)
        (n + 1) (G (n + 1)).obj)) := by
    have h := map_projection_pushforwardBaseQuotientIso_hom i hi I (G (n + 1)).obj (n + 1)
    rw [← Iso.eq_comp_inv] at h
    rw [h]
    exact epi_comp _ _
  let c := pushforwardBaseQuotientIso i hi I (G (n + 1)).obj (n + 1) ≪≫
    (smallEtaleAdicQuotientFunctor B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
      (n + 1)).mapIso (θ (n + 1)) ≪≫ e' ≪≫ (θ n).symm
  have key : (modulePushforward B (Spec (.of A)) hA i).map L = c.hom := by
    refine (cancel_epi ((modulePushforward B (Spec (.of A)) hA i).map
      (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA Z.1 Z.2 (baseIdealSubmodule Z.1 Z.2 I)
        (n + 1) (G (n + 1)).obj))).1 ?_
    show _ = _ ≫ (pushforwardBaseQuotientIso i hi I (G (n + 1)).obj (n + 1)).hom ≫
      smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        (n + 1) (θ (n + 1)).hom ≫ e'.hom ≫ (θ n).inv
    rw [← Functor.map_comp, hL, map_descendTransition,
      map_projection_pushforwardBaseQuotientIso_hom_assoc,
      smallEtaleAdicQuotientProjection_mapOfHom_assoc]
    exact congrArg ((θ (n + 1)).hom ≫ ·) ((congrArg (· ≫ (θ n).inv) he''.symm).trans
      (Category.assoc _ _ _))
  have : IsIso ((modulePushforward B (Spec (.of A)) hA i).map L) := by
    rw [key]
    exact c.isIso_hom
  have hLiso : IsIso L :=
    (fullyFaithfulModulePushforward B (Spec (.of A)) hA i hi).isIso_of_isIso_map L
  exact ⟨@asIso _ _ _ _ L hLiso, hL.trans (descendSystem_map_succ i hi E G θ n).symm⟩

end Descent

section Transport

variable (I : Ideal A) [IsNoetherianRing A] [IsAdicComplete I A]
  [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA Z.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))]

/-- The direct image of a coherent module on `Z`, as a coherent module on `X`. -/
def C1573.pushforwardCoherentModule (G : CoherentModules.{u, u} B (Spec (.of A)) hA Z.1 Z.2) :
    CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2 :=
  ⟨(modulePushforward B (Spec (.of A)) hA i).obj G.obj,
    isCoherent_modulePushforward_of_isClosedImmersion B (Spec (.of A)) hA
      (Fact.out : HasEtaleLocalProperty B (Spec (.of A)) hA X.1
        (fun V : Scheme.{u} => IsLocallyNoetherian V)) i hi G.obj G.property⟩

/-- The inverse of `pushforwardBaseQuotientIso` commutes with the transition maps
`(i_* M) / I^(k+1) (i_* M) ⟶ (i_* M) / I^k (i_* M)` and `M / I^(k+1) M ⟶ M / I^k M`. -/
theorem C1573.transition_pushforwardBaseQuotientIso_inv
    (M : Modules.{u, u} B (Spec (.of A)) hA Z.1 Z.2) (k : ℕ) :
    smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) k
        ((modulePushforward B (Spec (.of A)) hA i).obj M) ≫
      (pushforwardBaseQuotientIso i hi I M k).inv =
    (pushforwardBaseQuotientIso i hi I M (k + 1)).inv ≫
      (modulePushforward B (Spec (.of A)) hA i).map
        (smallEtaleAdicQuotientTransition B (Spec (.of A)) hA Z.1 Z.2 (baseIdealSubmodule Z.1 Z.2 I)
          k M) := by
  rw [Iso.comp_inv_eq, Category.assoc, map_transition_pushforwardBaseQuotientIso_hom,
    Iso.inv_hom_id_assoc]

/-- **The completion of `i_* M` along `I 𝒪_X` is the direct image of the completion of `M` along
`I 𝒪_Z`**, as inverse systems. -/
def C1573.pushforwardCompletionHom (M : Modules.{u, u} B (Spec (.of A)) hA Z.1 Z.2) :
    adicQuotientSystem B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        ((modulePushforward B (Spec (.of A)) hA i).obj M) ⟶
      adicQuotientSystem B (Spec (.of A)) hA Z.1 Z.2 (baseIdealSubmodule Z.1 Z.2 I) M ⋙
        modulePushforward B (Spec (.of A)) hA i :=
  NatTrans.ofOpSequence (fun n => (pushforwardBaseQuotientIso i hi I M (n + 1)).inv) fun n => by
    change (adicQuotientSystem B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        ((modulePushforward B (Spec (.of A)) hA i).obj M)).map (homOfLE (Nat.le_add_right n 1)).op ≫
          (pushforwardBaseQuotientIso i hi I M (n + 1)).inv =
      (pushforwardBaseQuotientIso i hi I M (n + 1 + 1)).inv ≫
        (modulePushforward B (Spec (.of A)) hA i).map
          ((adicQuotientSystem B (Spec (.of A)) hA Z.1 Z.2 (baseIdealSubmodule Z.1 Z.2 I) M).map
            (homOfLE (Nat.le_add_right n 1)).op)
    rw [adicQuotientSystem_map_succ, adicQuotientSystem_map_succ]
    exact transition_pushforwardBaseQuotientIso_inv i hi I M (n + 1)

/-- The component of `pushforwardCompletionHom` at `n` is the inverse of
`pushforwardBaseQuotientIso` at `n + 1`. -/
theorem C1573.pushforwardCompletionHom_app (M : Modules.{u, u} B (Spec (.of A)) hA Z.1 Z.2)
    (n : ℕ) :
    (pushforwardCompletionHom i hi I M).app (op n) =
      (pushforwardBaseQuotientIso i hi I M (n + 1)).inv :=
  rfl

/-- `pushforwardCompletionHom` is an isomorphism of inverse systems. -/
theorem C1573.isIso_pushforwardCompletionHom (M : Modules.{u, u} B (Spec (.of A)) hA Z.1 Z.2) :
    IsIso (pushforwardCompletionHom i hi I M) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun (n : ℕᵒᵖ) =>
    (pushforwardBaseQuotientIso i hi I M (n.unop + 1)).symm.isIso_hom

variable (f : X ⟶ schemeSpace (baseObject A B hA))
  (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
  (K : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1
        X.2).O))).Submodule) (hK : K.toSheafOfModules.IsQuasicoherentOnSite) (e : ℕ)
  (hker : SheafOfModules.kerIdeal (structureSharp B (Spec (.of A)) hA i) =
    idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K e (SheafOfModules.unit _))

include hker hK in
/-- **Hypothesis (1) of Stacks 08BC on `X_e`, read on `X`.**  If `i : Z ⟶ X` is the closed
subspace cut out by `𝓚^e` and completion along `I 𝒪_Z` is essentially surjective onto the
coherent adic systems with support proper over `Spec A`, then every such system on `X` whose
terms are annihilated by `𝓚^e` is the completion of a coherent module with proper support
annihilated by `𝓚^e`. -/
theorem C1573.kTorsionEssSurj_of_essSurj
    (hess : (completionFunctorProperOver B (Spec (.of A)) hA Z.1 (schemeSpace (baseObject A B hA)).1
      Z.2 (schemeSpace (baseObject A B hA)).2 (i ≫ f).hom
      (isLocallyOfFiniteType_closedImmersion_comp i hi f hf) (baseIdealSubmodule Z.1 Z.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := Z.1) (hX := Z.2) I)).EssSurj) :
    KTorsionEssSurj X I f hf K e := by
  intro E' hE'p hE'K
  have hann : ∀ n, AnnihilatedByKerIdeal B (Spec (.of A)) hA i (E'.obj.obj (op n)) := fun n =>
    annihilatedByKerIdeal_of_isPowAnnihilated i K e hker hK _ (hE'K n)
  have hLNZ : HasEtaleLocalProperty B (Spec (.of A)) hA Z.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V) := Fact.out
  choose G hG hθ using fun n => exists_isCoherent_modulePushforward_iso_of_annihilatedByKerIdeal
    B (Spec (.of A)) hA hLNZ i hi _ (E'.property.1 n) (hann n)
  let Gc : ℕ → CoherentModules.{u, u} B (Spec (.of A)) hA Z.1 Z.2 := fun n => ⟨G n, hG n⟩
  let θ : ∀ n, (modulePushforward B (Spec (.of A)) hA i).obj (Gc n).obj ≅ E'.obj.obj (op n) :=
    fun n => (hθ n).some
  have hD := isCoherentAdicSystem_descendSystem i hi I E'.obj Gc θ E'.property
  have hD0 : HasProperSupport B (Spec (.of A)) hA Z.2 (schemeSpace (baseObject A B hA)).2
      (i ≫ f).hom (isLocallyOfFiniteType_closedImmersion_comp i hi f hf)
      ((SheafOfModules.toSheaf _).obj (Gc 0).obj) := by
    refine hasProperSupport_of_modulePushforward i hi f hf (Gc 0).obj
      (isClosed_supportOfSheaf_coherent Z (Gc 0)) ?_
    unfold HasProperSupport
    rw [supportOfSheaf_eq_of_iso B (Spec (.of A)) hA X (θ 0)]
    exact hE'p
  let D : CoherentAdicSystemsProperOver B (Spec (.of A)) hA Z.2 (schemeSpace (baseObject A B hA)).2
      (i ≫ f).hom (isLocallyOfFiniteType_closedImmersion_comp i hi f hf)
      (baseIdealSubmodule Z.1 Z.2 I) :=
    ⟨⟨descendSystem i hi E'.obj Gc θ, hD⟩, hD0⟩
  let F := completionFunctorProperOver B (Spec (.of A)) hA Z.1 (schemeSpace (baseObject A B hA)).1
      Z.2 (schemeSpace (baseObject A B hA)).2 (i ≫ f).hom
      (isLocallyOfFiniteType_closedImmersion_comp i hi f hf) (baseIdealSubmodule Z.1 Z.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := Z.1) (hX := Z.2) I)
  let G'' := F.objPreimage D
  let ψ' : adicQuotientSystem B (Spec (.of A)) hA Z.1 Z.2 (baseIdealSubmodule Z.1 Z.2 I)
      G''.obj.obj ≅ descendSystem i hi E'.obj Gc θ :=
    (ObjectProperty.ι _).mapIso ((ObjectProperty.ι _).mapIso (F.objObjPreimageIso D))
  refine ⟨pushforwardCoherentModule i hi G''.obj, ?_, ?_, ⟨ObjectProperty.isoMk _ ?_⟩⟩
  · exact hasProperSupport_modulePushforward i hi f hf G''.obj.obj
      (isClosed_supportOfSheaf_coherent Z G''.obj) G''.property
  · exact isPowAnnihilated_of_annihilatedByKerIdeal i K e hker _
      (annihilatedByKerIdeal_modulePushforward B (Spec (.of A)) hA i _)
  · exact @asIso _ _ _ _ (pushforwardCompletionHom i hi I G''.obj.obj)
        (isIso_pushforwardCompletionHom i hi I G''.obj.obj) ≪≫
      Functor.isoWhiskerRight ψ' (modulePushforward B (Spec (.of A)) hA i) ≪≫
      @asIso _ _ _ _ (descendSystemHom i hi E'.obj Gc θ) (isIso_descendSystemHom i hi E'.obj Gc θ)

end Transport

section Registered

/-- In Situation 08B7 the algebraic space `X` is Noetherian: it is quasi-compact and
quasi-separated, being of finite type and separated over the affine Noetherian scheme `Spec A`,
and locally Noetherian, being locally of finite type over it. -/
theorem C1573.isNoetherian_of_isFiniteType_baseObject [IsNoetherianRing A]
    (X : AlgebraicSpaces B (Spec (.of A)) hA) (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsFiniteType B (Spec (.of A)) hA f.hom) (hsep : IsSeparated B (Spec (.of A)) hA f.hom) :
    IsNoetherian B (Spec (.of A)) hA B.contains_terminal X.1 :=
  have hAff : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseObject A B hA)) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  ⟨isQuasiCompactSpace_source_of_isQuasiCompact B (Spec (.of A)) hA
      (schemeSpace (baseObject A B hA)).2
      (isQuasiCompactSpace_yoneda_of_isAffine B (Spec (.of A)) hA (baseObject A B hA) hAff) hf.2,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (Spec (.of A)) hA B.contains_terminal X.2
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (Spec (.of A)) hA
        (yoneda.obj (baseObject A B hA)) B.contains_terminal
        ⟨baseObject A B hA, inferInstance, ⟨Functor.RepresentableBy.yoneda (baseObject A B hA)⟩⟩)
      (isQuasiSeparated_of_isSeparated B (Spec (.of A)) hA hsep),
    (fact_isLocallyNoetherian_of_baseObject X f hf.1).out⟩

/-- **Stacks 08BC.**  In Situation 08B7 — `A` Noetherian and `I`-adically complete,
`f : X ⟶ Spec A` of finite type and separated, `𝓘 = I 𝒪_X` — let `𝓚 ⊆ 𝒪_X` be a
quasi-coherent sheaf of ideals and `(F_n)` an object of
`Coh_{support proper over A}(X, 𝓘)`.  Assume

1. for every `e ≥ 1`, the closed subspace `X_e` cut out by `𝓚^e` is such that completion along
   `𝓘_e = I 𝒪_{X_e}` is an equivalence
   `Coh_{support proper over A}(𝒪_{X_e}) ≌ Coh_{support proper over A}(X_e, 𝓘_e)`, and
2. there are an object `𝓗` of `Coh_{support proper over A}(𝒪_X)` and a map
   `α : (F_n) ⟶ 𝓗^∧` whose kernel and cokernel are annihilated by a power of `𝓚`.

Then `(F_n)` is in the essential image of the completion functor of Stacks 08B8.

The closed subspace `X_e` of (1) is given as a closed immersion `i : Z ⟶ X` whose ideal sheaf
`ker(𝒪_X ⟶ i_* 𝒪_Z)` is `𝓚^e`. -/
theorem C1573.essImage_completionFunctorProperOver_of_auxiliaryIdeal [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A] (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsFiniteType B (Spec (.of A)) hA f.hom)
    (hsep : IsSeparated B (Spec (.of A)) hA f.hom)
    (K : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1
        X.2).O))).Submodule) (hK : K.toSheafOfModules.IsQuasicoherentOnSite)
    (h1 : ∀ e : ℕ, 0 < e → ∃ (Z : AlgebraicSpaces B (Spec (.of A)) hA) (i : Z ⟶ X)
      (hi : IsClosedImmersion B (Spec (.of A)) hA i.hom),
      SheafOfModules.kerIdeal (structureSharp B (Spec (.of A)) hA i) =
        idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K e (SheafOfModules.unit _) ∧
      letI := fact_isLocallyNoetherian_of_baseObject Z (i ≫ f)
        (isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1)
      (completionFunctorProperOver B (Spec (.of A)) hA Z.1 (schemeSpace (baseObject A B hA)).1
        Z.2 (schemeSpace (baseObject A B hA)).2 (i ≫ f).hom
        (isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1) (baseIdealSubmodule Z.1 Z.2 I)
        (isQuasicoherentOnSite_baseIdealSubmodule (X := Z.1) (hX := Z.2) I)).IsEquivalence)
    (E : CoherentAdicSystemsProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2
      f.hom hf.1 (baseIdealSubmodule X.1 X.2 I))
    (H : CoherentModulesProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2
      f.hom hf.1)
    (α : E ⟶ letI := fact_isLocallyNoetherian_of_baseObject X f hf.1
      (completionFunctorProperOver B (Spec (.of A)) hA X.1 (schemeSpace (baseObject A B hA)).1 X.2
        (schemeSpace (baseObject A B hA)).2 f.hom hf.1 (baseIdealSubmodule X.1 X.2 I)
        (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).obj H)
    (hα : IsSystemKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K α.hom.hom) :
    letI := fact_isLocallyNoetherian_of_baseObject X f hf.1
    (completionFunctorProperOver B (Spec (.of A)) hA X.1 (schemeSpace (baseObject A B hA)).1 X.2
      (schemeSpace (baseObject A B hA)).2 f.hom hf.1 (baseIdealSubmodule X.1 X.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).essImage E := by
  let := fact_isLocallyNoetherian_of_baseObject X f hf.1
  have hKe : ∀ e, KTorsionEssSurj X I f hf.1 K (e + 1) := fun e => by
    obtain ⟨Z, i, hi, hker, hEq⟩ := h1 (e + 1) (Nat.succ_pos e)
    let := fact_isLocallyNoetherian_of_baseObject Z (i ≫ f)
      (isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1)
    exact kTorsionEssSurj_of_essSurj i hi I f hf.1 K hK (e + 1) hker inferInstance
  exact essImage_completionFunctorProperOver_of_kTorsionEssSurj hK B.contains_terminal
    (isNoetherian_of_isFiniteType_baseObject X f hf hsep) hKe E H.obj H.property α.hom hα

end Registered

end AlgebraicGeometry.Space

end
