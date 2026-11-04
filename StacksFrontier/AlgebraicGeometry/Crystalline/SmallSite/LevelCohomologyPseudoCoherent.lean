module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.Algebra.Homology.PseudoCoherentNilpotentModels
public import StacksFrontier.Algebra.Homology.PseudoCoherentNoetherianModels
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigLevelLift
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.ChangeBaseCrystals
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialBaseCohomologyFinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialBaseLevel
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerIdealPow
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeNilpotentSmooth
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusDerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusSemilinearAction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureMorphism

/-!
# The crystalline cohomology of a finite level is pseudo-coherent

Let `(p, (S, I, γ), X)` be a global crystalline situation with affine base, `A = Γ(S, 𝒪_S)`
Noetherian, and let `e` be a finite divided power level, `S_e = Spec(A/p^eA)`.  The cohomology
`RΓ(CRIS(X/S_e), N_e)` of a crystal is pseudo-coherent over `Γ(S_e, 𝒪) = A/p^eA` as soon as its
derived base change to the closed fibre `S₀ = Spec(A/I)` is computed by `RΓ(CRIS(X/S₀), N₀)`
and the latter is bounded above with finite cohomology modules: the ring map
`Γ(S_e, 𝒪) → Γ(S₀, 𝒪)` is surjective with nilpotent kernel, and pseudo-coherence lifts along such
a map ([Stacks, Tag 0H76],
`StacksDraft.PseudoCoherence.isPseudoCoherentIn_totalDerivedExtensionScalars_iff`),
while over the Noetherian ring `Γ(S₀, 𝒪)` boundedness and finiteness of cohomology is
pseudo-coherence ([Stacks, Tag 066E],
`StacksDraft.PseudoCoherence.isPseudoCoherentIn_of_boundedAbove_finite_homology`).

## Main results

* `...SmallSite.isPseudoCoherentIn_of_isIso_derivedBaseChangeTensorAdjunction_homEquiv_symm` —
  the abstract reduction, along any change of divided power base whose ring map is surjective
  with nilpotent kernel.
* `...surjective_baseChangeRingHom_trivialBaseToLevel` and
  `...isNilpotent_ker_baseChangeRingHom_trivialBaseToLevel` — `Γ(S_e, 𝒪) → Γ(S₀, 𝒪)` is
  surjective with nilpotent kernel, `A` Noetherian.
* `...isPseudoCoherentIn_levelCohomology_of_baseChange` — the level cohomology is pseudo-coherent,
  given the base change isomorphism to `S₀` and the finiteness over `S₀`.
* `...SmallSite.isPseudoCoherentIn_levelCohomology` — **the cohomology `RΓ(CRIS(X/S_e), N_e)` of a
  crystal in finite locally free modules is pseudo-coherent**, `A` Noetherian and `X ⟶ S₀` proper
  and smooth; the two inputs are supplied by
  `...SmallSite.isIso_baseChange_of_isNilpotent_smooth` and
  `...CechEnvelope.moduleFinite_and_bounded_homology_trivialBaseSituation`.

## References

* [Stacks Project, Tag 0H76](https://stacks.math.columbia.edu/tag/0H76)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wA wA' wB

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

section Abstract

variable {S S' : GlobalCrystallineSituation.{u}}
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA'} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **Pseudo-coherence from a base change isomorphism to a Noetherian base along a surjection with
nilpotent kernel.**  Let `f : S ⟶ S'` be a change of divided power base whose ring map
`A' = Γ(S', 𝒪) → A = Γ(S, 𝒪)` is surjective with nilpotent kernel, `A` Noetherian.  If
`φ : K ⟶ res_* L` has an invertible adjoint transpose `K ⊗^L_{A'} A ⟶ L` and `L` is bounded above
with finite cohomology modules, then `K` is pseudo-coherent. -/
theorem isPseudoCoherentIn_of_isIso_derivedBaseChangeTensorAdjunction_homEquiv_symm
    (f : S.S ⟶ S'.S) (hf : Function.Surjective (baseChangeRingHom f))
    (hnil : IsNilpotent (RingHom.ker (baseChangeRingHom f))) [IsNoetherianRing Γ(S.S.scheme, ⊤)]
    {K : DerivedCategory (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))}
    {L : DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))}
    (φ : K ⟶ (ModuleCat.restrictScalars (baseChangeRingHom f)).mapDerivedCategory.obj L)
    (hφ : IsIso (((derivedBaseChangeTensorAdjunction f).homEquiv _ _).symm φ))
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) i).obj L))
    (hfin : ∀ i : ℤ, Module.Finite Γ(S.S.scheme, ⊤)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) i).obj L)) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentIn K := by
  have hL : StacksDraft.PseudoCoherence.IsPseudoCoherentIn L :=
    StacksDraft.PseudoCoherence.isPseudoCoherentIn_of_boundedAbove_finite_homology L hb hfin
  have hDK : StacksDraft.PseudoCoherence.IsPseudoCoherentIn ((derivedBaseChangeTensor f).obj K) :=
    hL.ofIso (@asIso _ _ _ _ _ hφ).symm
  exact (StacksDraft.PseudoCoherence.isPseudoCoherentIn_totalDerivedExtensionScalars_iff hf hnil
    (derivedBaseChangeTensorBundle f) K).1 hDK

end Abstract

section Level

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme] {e : ℕ} (he : S.IsLevel e)

/-- **`p^e` vanishes on the level `S_e = Spec(A/p^eA)`.** -/
theorem natCast_pow_eq_zero_level :
    ((S.p : ℕ) : Γ((S.levelSituation he).S.scheme, ⊤)) ^ e = 0 := by
  have h0 : ((S.p : ℕ) : pAdicLevelRing S.baseIdeal S.baseDividedPowers S.p he) ^ e = 0 := by
    change ((S.p : ℕ) : Γ(S.S.scheme, ⊤) ⧸ DividedPowers.pAdicIdeal (A := Γ(S.S.scheme, ⊤)) S.p ^
      e) ^ e = 0
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
      DividedPowers.pAdicIdeal, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of
    (pAdicLevelRing S.baseIdeal S.baseDividedPowers S.p he))).inv.hom h0
  rwa [map_pow, map_natCast, map_zero] at h

/-- The divided power morphism `S_e ⟶ S` is a closed immersion. -/
instance isClosedImmersion_levelProj_hom : IsClosedImmersion (S.levelProj he).hom := by
  have : IsIso S.baseSpecIso.hom.hom :=
    ⟨⟨S.baseSpecIso.inv.hom, by
        rw [← DividedPowerScheme.Hom.comp_hom, Iso.hom_inv_id, DividedPowerScheme.Hom.id_hom],
      by rw [← DividedPowerScheme.Hom.comp_hom, Iso.inv_hom_id, DividedPowerScheme.Hom.id_hom]⟩⟩
  change IsClosedImmersion ((pAdicLevelSchemeProj S.baseIdeal S.baseDividedPowers S.p he).hom ≫
    S.baseSpecIso.hom.hom)
  infer_instance

/-- The ring map on global sections of a composite of divided power morphisms is the composite of
the ring maps. -/
theorem baseChangeRingHom_comp_dp {S₁ S₂ S₃ : GlobalCrystallineSituation.{u}} (f : S₁.S ⟶ S₂.S)
    (g : S₂.S ⟶ S₃.S) :
    baseChangeRingHom (S := S₁) (S' := S₃) (f ≫ g) =
      (baseChangeRingHom (S := S₁) (S' := S₂) f).comp
        (baseChangeRingHom (S := S₂) (S' := S₃) g) := by
  simp only [baseChangeRingHom, DividedPowerScheme.Hom.comp_hom, op_comp, Functor.map_comp,
    CommRingCat.hom_comp]
  rfl

/-- The ring map on global sections of the closed fibre inclusion is surjective. -/
private theorem surjective_baseChangeRingHom_closedFiberToBaseHom :
    Function.Surjective (baseChangeRingHom (S := trivialBaseSituation S) (S' := S)
      (closedFiberToBaseHom S)) :=
  (DividedPowerScheme.closedFiberι S.S).app_surjective ⊤ (isAffineOpen_top _)

/-- The ring maps `Γ(S_e) → Γ(S₀)` and `A → Γ(S_e)` compose to the ring map `A → Γ(S₀)`. -/
private theorem baseChangeRingHom_trivialBaseToLevel_comp_levelProj :
    (baseChangeRingHom (S := trivialBaseSituation S) (S' := S.levelSituation he)
      (trivialBaseToLevel he)).comp
      (baseChangeRingHom (S := S.levelSituation he) (S' := S) (S.levelProj he)) =
    baseChangeRingHom (S := trivialBaseSituation S) (S' := S) (closedFiberToBaseHom S) := by
  rw [← baseChangeRingHom_comp_dp, trivialBaseToLevel_comp_levelProj]

/-- The ring of global sections of `S₀` is Noetherian when `A` is. -/
private theorem isNoetherianRing_trivialBaseSituation [IsNoetherianRing Γ(S.S.scheme, ⊤)] :
    IsNoetherianRing Γ((trivialBaseSituation S).S.scheme, ⊤) :=
  isNoetherianRing_of_surjective _ _ _ (surjective_baseChangeRingHom_closedFiberToBaseHom S)

/-- The closed fibre of `S` is affine. -/
private theorem isAffine_closedFiber : IsAffine (DividedPowerScheme.closedFiber S.S) :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine
    (DividedPowerScheme.closedFiberPresentation S.S).ι).1

/-- `X` is separated and quasi-compact when `X ⟶ S₀` is proper. -/
private theorem isSeparated_and_compactSpace_source [IsProper S.toClosedFiber] :
    S.X.IsSeparated ∧ CompactSpace S.X := by
  have := isAffine_closedFiber S
  refine ⟨⟨?_⟩, QuasiCompact.compactSpace_of_compactSpace S.toClosedFiber⟩
  rw [show terminal.from S.X = S.toClosedFiber ≫ terminal.from _ from
    (terminal.comp_from _).symm]
  infer_instance

/-- **`Γ(S_e, 𝒪) → Γ(S₀, 𝒪)` is surjective**: composed with `A → Γ(S_e, 𝒪)` it is `A → A/I`. -/
theorem surjective_baseChangeRingHom_trivialBaseToLevel :
    Function.Surjective (baseChangeRingHom (S := trivialBaseSituation S)
      (S' := S.levelSituation he) (trivialBaseToLevel he)) := by
  have hs := surjective_baseChangeRingHom_closedFiberToBaseHom S
  rw [← baseChangeRingHom_trivialBaseToLevel_comp_levelProj S he, RingHom.coe_comp] at hs
  exact Function.Surjective.of_comp hs

/-- **`Γ(S_e, 𝒪) → Γ(S₀, 𝒪)` has nilpotent kernel** when `A` is Noetherian: its kernel is the image
of `I`, and some power of `I` lies in `p^eA`, which vanishes in `Γ(S_e, 𝒪)`. -/
theorem isNilpotent_ker_baseChangeRingHom_trivialBaseToLevel [IsNoetherianRing Γ(S.S.scheme, ⊤)] :
    IsNilpotent (RingHom.ker (baseChangeRingHom (S := trivialBaseSituation S)
      (S' := S.levelSituation he) (trivialBaseToLevel he))) := by
  set κ := baseChangeRingHom (S := trivialBaseSituation S) (S' := S.levelSituation he)
    (trivialBaseToLevel he)
  set π := baseChangeRingHom (S := S.levelSituation he) (S' := S) (S.levelProj he)
  have hπ : Function.Surjective π := (S.levelProj he).hom.app_surjective ⊤ (isAffineOpen_top _)
  have h := baseChangeRingHom_trivialBaseToLevel_comp_levelProj S he
  have hker : RingHom.ker (κ.comp π) = S.baseIdeal := by
    rw [h]
    exact ((DividedPowerScheme.ideal_obj_eq_ker_ideal_closedFiberι S.S
      ⟨⊤, isAffineOpen_top _⟩).trans (Scheme.Hom.ker_apply _ _)).symm
  have hkerκ : RingHom.ker κ = S.baseIdeal.map π := by
    rw [← hker, ← RingHom.comap_ker, Ideal.map_comap_of_surjective π hπ]
  obtain ⟨M, hM⟩ := S.baseDividedPowers.exists_pow_le_span_pow_of_noetherian
    (p := S.p) (Nat.Prime.pos (Fact.out : S.p.Prime)) e
  refine ⟨M, ?_⟩
  rw [hkerκ, ← Ideal.map_pow, Ideal.zero_eq_bot, eq_bot_iff]
  refine (Ideal.map_mono hM).trans ?_
  rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast, Ideal.span_le,
    Set.singleton_subset_iff, natCast_pow_eq_zero_level S he]
  exact Submodule.zero_mem _

/-- **The map on closed fibres of `S₀ ⟶ S_e` is an isomorphism**: followed by the closed-fibre
map of `S_e ⟶ S`, a monomorphism, it is the identification of the closed fibre of `(S₀, 0, 0)`
with `S₀`. -/
instance isIso_closedFiberMap_trivialBaseToLevel :
    IsIso (DividedPowerScheme.closedFiberMap (trivialBaseToLevel he)) := by
  have h : DividedPowerScheme.closedFiberMap (trivialBaseToLevel he) ≫
      DividedPowerScheme.closedFiberMap (S.levelProj he) =
        (trivialClosedFiberIso (DividedPowerScheme.closedFiber S.S)).hom := by
    rw [← DividedPowerScheme.closedFiberMap_comp, trivialBaseToLevel_comp_levelProj,
      closedFiberMap_closedFiberToBaseHom]
  have : IsIso (DividedPowerScheme.closedFiberMap (trivialBaseToLevel he) ≫
      DividedPowerScheme.closedFiberMap (S.levelProj he)) := by
    rw [h]
    exact Iso.isIso_hom _
  have : IsSplitEpi (DividedPowerScheme.closedFiberMap (S.levelProj he)) :=
    IsSplitEpi.mk' ⟨inv (DividedPowerScheme.closedFiberMap (trivialBaseToLevel he) ≫
      DividedPowerScheme.closedFiberMap (S.levelProj he)) ≫
        DividedPowerScheme.closedFiberMap (trivialBaseToLevel he), by simp⟩
  have : IsIso (DividedPowerScheme.closedFiberMap (S.levelProj he)) :=
    isIso_of_mono_of_isSplitEpi _
  exact IsIso.of_isIso_comp_right _ (DividedPowerScheme.closedFiberMap (S.levelProj he))

/-- **The square of closed fibres of `(S₀ ⟶ S_e, 𝟙_X)` is a pullback square**: `X/S₀` is the base
change of `X/S_e` along `S₀ ⟶ S_e`, the map on closed fibres being an isomorphism. -/
theorem isPullback_trivialBaseToLevel :
    IsPullback (𝟙 S.X) (trivialBaseSituation S).toClosedFiber (S.levelSituation he).toClosedFiber
      (DividedPowerScheme.closedFiberMap (trivialBaseToLevel he)) :=
  IsPullback.of_horiz_isIso ⟨by
    rw [S.trivialBaseToLevel_condition he]⟩

/-- The map on closed fibres of an isomorphism of divided power schemes is an isomorphism. -/
instance isIso_closedFiberMap_of_isIso {Y Z : DividedPowerScheme.{u}} (i : Y ⟶ Z) [IsIso i] :
    IsIso (DividedPowerScheme.closedFiberMap i) :=
  ⟨⟨DividedPowerScheme.closedFiberMap (inv i), by
      rw [← DividedPowerScheme.closedFiberMap_comp, IsIso.hom_inv_id,
        DividedPowerScheme.closedFiberMap_id],
    by rw [← DividedPowerScheme.closedFiberMap_comp, IsIso.inv_hom_id,
        DividedPowerScheme.closedFiberMap_id]⟩⟩

/-- `X ⟶ S₀` is smooth for `X/S₀` when it is for `X/S`. -/
instance smooth_trivialBaseSituation_toClosedFiber [Smooth S.toClosedFiber] :
    Smooth (trivialBaseSituation S).toClosedFiber :=
  MorphismProperty.comp_mem @Smooth _ _ ‹_›
    (inferInstanceAs (Smooth (trivialClosedFiberIso (DividedPowerScheme.closedFiber S.S)).inv))

/-- `X ⟶ S₀` is proper for `X/S₀` when it is for `X/S`. -/
instance isProper_trivialBaseSituation_toClosedFiber [IsProper S.toClosedFiber] :
    IsProper (trivialBaseSituation S).toClosedFiber :=
  MorphismProperty.comp_mem @IsProper _ _ ‹_›
    (inferInstanceAs (IsProper (trivialClosedFiberIso (DividedPowerScheme.closedFiber S.S)).inv))

/-- `X ⟶ (S_e)₀` is smooth for `X/S_e` when `X ⟶ S₀` is for `X/S`. -/
instance smooth_levelSituation_toClosedFiber [Smooth S.toClosedFiber] :
    Smooth (S.levelSituation he).toClosedFiber := by
  change Smooth ((S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap S.baseSpecIso.inv) ≫ _)
  infer_instance

/-- `X ⟶ (S_e)₀` is proper for `X/S_e` when `X ⟶ S₀` is for `X/S`. -/
instance isProper_levelSituation_toClosedFiber [IsProper S.toClosedFiber] :
    IsProper (S.levelSituation he).toClosedFiber := by
  change IsProper ((S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap S.baseSpecIso.inv) ≫ _)
  infer_instance

variable [HasDerivedCategory.{wB} (BigModuleSheaf (S.levelSituation he))]
  [HasDerivedCategory.{wB} (BigModuleSheaf (trivialBaseSituation S))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ((S.levelSituation he).S.scheme, ⊤))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ((trivialBaseSituation S).S.scheme, ⊤))]

/-- The restriction to `CRIS(X/S₀)` of a sheaf of modules on `CRIS(X/S_e)`, along `S₀ ⟶ S_e` and
the identity of `X`. -/
abbrev trivialBaseLevelPullback :
    BigModuleSheaf (S.levelSituation he) ⥤ BigModuleSheaf (trivialBaseSituation S) :=
  changeBaseBigModulePullback (trivialBaseSituation S) (S.levelSituation he)
    (trivialBaseToLevel he) (𝟙 S.X) (S.trivialBaseToLevel_condition he)

omit [HasDerivedCategory.{wB} (BigModuleSheaf (S.levelSituation he))]
  [HasDerivedCategory.{wB} (BigModuleSheaf (trivialBaseSituation S))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ((S.levelSituation he).S.scheme, ⊤))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ((trivialBaseSituation S).S.scheme, ⊤))] in
/-- **The restriction to `S₀` of `N_e`, for a sheaf of modules `N` on `CRIS(X/S)` at the module
universe `u`, is the universe lift of a sheaf of modules on `CRIS(X/S₀)`**, on the nose. -/
theorem trivialBaseLevelPullback_levelPullback_bigModuleULift
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) :
    (trivialBaseLevelPullback S he).obj ((S.levelPullback he).obj ((bigModuleULift S).obj N)) =
      (bigModuleULift (trivialBaseSituation S)).obj
        ((changeBaseModulePullback (trivialBaseSituation S) (S.levelSituation he)
          (trivialBaseToLevel he) (𝟙 S.X) (S.trivialBaseToLevel_condition he)).obj
          ((changeBaseModulePullback (S.levelSituation he) S (S.levelProj he) (𝟙 S.X)
            (S.levelProj_condition he)).obj N)) := by
  have h₁ := congrArg (fun F ↦ F.obj N) (bigModuleULift_comp_changeBaseBigModulePullback
    (S.levelSituation he) S (S.levelProj he) (𝟙 S.X) (S.levelProj_condition he))
  have h₂ := congrArg (fun F ↦ F.obj ((changeBaseModulePullback (S.levelSituation he) S
      (S.levelProj he) (𝟙 S.X) (S.levelProj_condition he)).obj N))
    (bigModuleULift_comp_changeBaseBigModulePullback (trivialBaseSituation S) (S.levelSituation he)
      (trivialBaseToLevel he) (𝟙 S.X) (S.trivialBaseToLevel_condition he))
  simp only [Functor.comp_obj] at h₁ h₂
  rw [h₂, h₁]

omit [HasDerivedCategory.{wB} (BigModuleSheaf (S.levelSituation he))]
  [HasDerivedCategory.{wB} (BigModuleSheaf (trivialBaseSituation S))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ((S.levelSituation he).S.scheme, ⊤))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ((trivialBaseSituation S).S.scheme, ⊤))] in
/-- **The restriction to `S₀` of `N_e` is a crystal in finite locally free modules** when `N`
is. -/
theorem isFiniteLocallyFreeQuasicoherentCrystal_trivialBaseLevel
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (hN : GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal N) :
    GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal
      ((changeBaseModulePullback (trivialBaseSituation S) (S.levelSituation he)
          (trivialBaseToLevel he) (𝟙 S.X) (S.trivialBaseToLevel_condition he)).obj
          ((changeBaseModulePullback (S.levelSituation he) S (S.levelProj he) (𝟙 S.X)
            (S.levelProj_condition he)).obj N)) :=
  hN.changeBaseModulePullback.changeBaseModulePullback

/-- **The cohomology of a finite level is pseudo-coherent, given the base change to `S₀` and the
finiteness over `S₀`.**  For a sheaf of modules `N` on `CRIS(X/S)`, write `N_e` and `N₀` for its
restrictions to `CRIS(X/S_e)` and `CRIS(X/S₀)`.  If the base change map
`RΓ(CRIS(X/S_e), N_e) ⊗^L_{Γ(S_e)} Γ(S₀) ⟶ RΓ(CRIS(X/S₀), N₀)` is an isomorphism and
`RΓ(CRIS(X/S₀), N₀)` is bounded above with finite cohomology modules, then `RΓ(CRIS(X/S_e), N_e)`
is pseudo-coherent over `Γ(S_e, 𝒪)`, `A` being Noetherian. -/
theorem isPseudoCoherentIn_levelCohomology_of_baseChange [IsNoetherianRing Γ(S.S.scheme, ⊤)]
    (N : BigModuleSheaf S)
    (hBC : IsIso (((derivedBaseChangeTensorAdjunction (trivialBaseToLevel he)).homEquiv _ _).symm
      (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap (trivialBaseToLevel he)
        (𝟙 S.X) (S.trivialBaseToLevel_condition he) ((S.levelPullback he).obj N)))))
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} Γ((trivialBaseSituation S).S.scheme, ⊤)) i).obj
          (DerivedCategory.Plus.ι.obj ((derivedBigModuleGlobalSections (trivialBaseSituation S)).obj
            ((trivialBaseLevelPullback S he).obj ((S.levelPullback he).obj N))))))
    (hfin : ∀ i : ℤ, Module.Finite Γ((trivialBaseSituation S).S.scheme, ⊤)
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} Γ((trivialBaseSituation S).S.scheme, ⊤)) i).obj
          (DerivedCategory.Plus.ι.obj ((derivedBigModuleGlobalSections (trivialBaseSituation S)).obj
            ((trivialBaseLevelPullback S he).obj ((S.levelPullback he).obj N)))))) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentIn
      (DerivedCategory.Plus.ι.obj ((derivedBigModuleGlobalSections (S.levelSituation he)).obj
        ((S.levelPullback he).obj N))) := by
  have := isNoetherianRing_trivialBaseSituation S
  exact isPseudoCoherentIn_of_isIso_derivedBaseChangeTensorAdjunction_homEquiv_symm
    (trivialBaseToLevel he) (surjective_baseChangeRingHom_trivialBaseToLevel S he)
    (isNilpotent_ker_baseChangeRingHom_trivialBaseToLevel S he) _ hBC hb hfin

/-- **The base change isomorphism from `S_e` to `S₀`** for a crystal in finite locally free modules
on `CRIS(X/S)`, `X ⟶ S₀` proper and smooth: the instance of
`...SmallSite.isIso_baseChange_of_isNilpotent_smooth` at the pullback square
`isPullback_trivialBaseToLevel`, `p` being nilpotent on both `S₀` and `S_e`. -/
theorem isIso_baseChange_trivialBaseToLevel [IsProper S.toClosedFiber] [Smooth S.toClosedFiber]
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (hN : GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal N) :
    IsIso (((derivedBaseChangeTensorAdjunction (trivialBaseToLevel he)).homEquiv _ _).symm
      (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap (trivialBaseToLevel he)
        (𝟙 S.X) (S.trivialBaseToLevel_condition he)
          ((S.levelPullback he).obj ((bigModuleULift S).obj N))))) := by
  have := isAffine_closedFiber S
  obtain ⟨_, _⟩ := isSeparated_and_compactSpace_source S
  have : IsAffine (S.levelSituation he).S.scheme :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of
      (pAdicLevelRing S.baseIdeal S.baseDividedPowers S.p he))))
  have hp : IsNilpotent ((trivialBaseSituation S).p : Γ((trivialBaseSituation S).S.scheme, ⊤)) :=
    ⟨e, S.natCast_pow_eq_zero_closedFiber he⟩
  have hp' : IsNilpotent ((S.levelSituation he).p : Γ((S.levelSituation he).S.scheme, ⊤)) :=
    ⟨e, natCast_pow_eq_zero_level S he⟩
  have h := isIso_baseChange_of_isNilpotent_smooth (S := trivialBaseSituation S)
    (S' := S.levelSituation he) (trivialBaseToLevel he) (𝟙 S.X)
    (S.trivialBaseToLevel_condition he) (isPullback_trivialBaseToLevel S he) hp hp'
    inferInstance _ (hN.changeBaseModulePullback (f := S.levelProj he) (g := 𝟙 S.X)
      (h := S.levelProj_condition he))
  exact h

/-- **The cohomology of a finite level is pseudo-coherent, given the finiteness over `S₀`.**  For
a crystal `N` in finite locally free modules on `CRIS(X/S)`, `A` Noetherian and `X ⟶ S₀` proper
and smooth, `RΓ(CRIS(X/S_e), N_e)` is pseudo-coherent over `Γ(S_e, 𝒪)` as soon as
`RΓ(CRIS(X/S₀), N₀)` is bounded above with finite cohomology modules over `Γ(S₀, 𝒪)`. -/
theorem isPseudoCoherentIn_levelCohomology_of_finite [IsNoetherianRing Γ(S.S.scheme, ⊤)]
    [IsProper S.toClosedFiber] [Smooth S.toClosedFiber]
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (hN : GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal N)
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} Γ((trivialBaseSituation S).S.scheme, ⊤)) i).obj
          (DerivedCategory.Plus.ι.obj ((derivedBigModuleGlobalSections (trivialBaseSituation S)).obj
            ((trivialBaseLevelPullback S he).obj
              ((S.levelPullback he).obj ((bigModuleULift S).obj N)))))))
    (hfin : ∀ i : ℤ, Module.Finite Γ((trivialBaseSituation S).S.scheme, ⊤)
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} Γ((trivialBaseSituation S).S.scheme, ⊤)) i).obj
          (DerivedCategory.Plus.ι.obj ((derivedBigModuleGlobalSections (trivialBaseSituation S)).obj
            ((trivialBaseLevelPullback S he).obj
              ((S.levelPullback he).obj ((bigModuleULift S).obj N))))))) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentIn
      (DerivedCategory.Plus.ι.obj ((derivedBigModuleGlobalSections (S.levelSituation he)).obj
        ((S.levelPullback he).obj ((bigModuleULift S).obj N)))) :=
  isPseudoCoherentIn_levelCohomology_of_baseChange S he _
    (isIso_baseChange_trivialBaseToLevel S he hN) hb hfin

end Level

/-- **The crystalline cohomology of a finite level is pseudo-coherent.**  Let `(p, (S, I, γ), X)`
be a global crystalline situation with affine base, `A = Γ(S, 𝒪_S)` Noetherian and `X ⟶ S₀`
proper and smooth, let `e` be a finite divided power level and `N` a crystal in finite locally
free modules on `CRIS(X/S)`.  Then `RΓ(CRIS(X/S_e), N_e)` is a pseudo-coherent object of the
derived category of `Γ(S_e, 𝒪) = A/p^eA`-modules.

Its derived base change to `Γ(S₀, 𝒪) = A/I` is `RΓ(CRIS(X/S₀), N₀)`
(`...SmallSite.isIso_baseChange_trivialBaseToLevel`), which is bounded above with finite
cohomology modules
(`...CechEnvelope.moduleFinite_and_bounded_homology_trivialBaseSituation`); and
`Γ(S_e, 𝒪) → Γ(S₀, 𝒪)` is surjective with nilpotent kernel. -/
theorem isPseudoCoherentIn_levelCohomology {S : GlobalCrystallineSituation.{u}}
    [IsAffine S.S.scheme] [IsNoetherianRing Γ(S.S.scheme, ⊤)] [IsProper S.toClosedFiber]
    [Smooth S.toClosedFiber] {e : ℕ} (he : S.IsLevel e)
    [HasDerivedCategory.{wB} (BigModuleSheaf (S.levelSituation he))]
    [HasDerivedCategory.{wB} (BigModuleSheaf (trivialBaseSituation S))]
    [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ((S.levelSituation he).S.scheme, ⊤))]
    [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ((trivialBaseSituation S).S.scheme, ⊤))]
    (N : SheafOfModules.{u} (crystallineStructureSheaf S))
    (hN : GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal N) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentIn
      (DerivedCategory.Plus.ι.obj ((derivedBigModuleGlobalSections (S.levelSituation he)).obj
        ((S.levelPullback he).obj ((bigModuleULift S).obj N)))) := by
  have := isAffine_closedFiber S
  obtain ⟨_, _⟩ := isSeparated_and_compactSpace_source S
  have := isNoetherianRing_trivialBaseSituation S
  have : IsProper (sourceToBase (trivialBaseSituation S)) :=
    MorphismProperty.comp_mem @IsProper _ _ inferInstance
      (inferInstanceAs (IsProper (DividedPowerScheme.closedFiberι
        (trivialDividedPowerScheme (DividedPowerScheme.closedFiber S.S)))))
  have hp : IsNilpotent ((trivialBaseSituation S).p : Γ((trivialBaseSituation S).S.scheme, ⊤)) :=
    ⟨e, S.natCast_pow_eq_zero_closedFiber he⟩
  have hfin := CechEnvelope.moduleFinite_and_bounded_homology_trivialBaseSituation S hp
    inferInstance _ (isFiniteLocallyFreeQuasicoherentCrystal_trivialBaseLevel S he hN)
  rw [← trivialBaseLevelPullback_levelPullback_bigModuleULift S he N] at hfin
  exact isPseudoCoherentIn_levelCohomology_of_finite S he hN hfin.1 hfin.2

end Crystalline.GlobalCrystallineSituation.SmallSite
