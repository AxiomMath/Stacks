module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialBaseLevel
public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusTwistStability
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeArrow07QCModelTransport
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeArrow07QCReduction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeNilpotentSmooth
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BoundednessReduction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisCohomologyLevelsPseudoCoherent

/-!
# Arrow 1 of [Stacks, Tag 07N5] at the finite levels `S_e`

Let `T` be a Frobenius crystal situation over the affine base `S = Spec(A)` and `e ≠ 0` a finite
divided power level (`(p^e) ⊆ I` preserved by `γ`). This file supplies the concrete finite-level
data that `...SmallSite.isIso_baseChangeArrow07QC_of_levels_of_isAdicComplete` takes:

* `S_N = X/S_e` and `S'_N = X^{(1)}/S_e`, the level situations of `X/S` and of `X^{(1)}/S` (the
  same base);
* `ι = S_e ⟶ S` and `ι' = S_e ⟶ S` the level projections, with `g = g' = 𝟙`;
* `σ_N : S_e ⟶ S_e`, the factorization of `S_e ⟶ S ⟶ S` (`Spec(σ)`) through `S_e`, which exists
  because `σ(p) = p` makes `p^e` vanish on the source, with `g_σ = (X^{(1)} ⟶ X)`;

and checks the commutations and the ring facts: `A ⟶ Γ(S_e, ⊤)` is surjective with kernel
`(p^e)`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.frobeniusLevelSigma`: `σ_N`.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.isIso_baseChangeArrow07QC_of_levelInputs`:
  arrow 1 is an isomorphism, given pseudo-coherence and the three level base change
  isomorphisms at one level `e ≠ 0`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wS wB wA

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (T : Crystalline.FCrystalSituation.{u})

/-- A level of `X/S` is a level of `X^{(1)}/S`, the two having the same divided power base. -/
theorem twistIsLevel {e : ℕ} (he : T.global.IsLevel e) : T.frobeniusTwistSituation.IsLevel e :=
  he

/-- **`p^e` vanishes on the global sections of a level `S_e`.** -/
theorem natCast_pow_eq_zero_levelSituation (S : GlobalCrystallineSituation.{u})
    [IsAffine S.S.scheme] {e : ℕ} (he : S.IsLevel e) :
    ((S.p : ℕ) : Γ((S.levelSituation he).S.scheme, ⊤)) ^ e = 0 := by
  apply (S.levelSectionsEquiv he).injective
  rw [map_pow, map_natCast, map_zero, ← map_natCast (Ideal.Quotient.mk _), ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem, Crystalline.IsPAdicLevel.pAdicIdeal_pow_eq]
  exact Ideal.mem_span_singleton_self _

/-- **The ring map `A ⟶ Γ(S_e, ⊤)` is surjective.** -/
theorem surjective_baseChangeRingHom_levelProj (S : GlobalCrystallineSituation.{u})
    [IsAffine S.S.scheme] {e : ℕ} (he : S.IsLevel e) :
    Function.Surjective (baseChangeRingHom (S.levelProj he)) := by
  intro y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (S.levelSectionsEquiv he y)
  refine ⟨a, (S.levelSectionsEquiv he).injective ?_⟩
  rw [levelSectionsEquiv_baseChangeRingHom_levelProj, ha]

/-- **The kernel of `A ⟶ Γ(S_e, ⊤)` is `(p^e)`.** -/
theorem ker_baseChangeRingHom_levelProj (S : GlobalCrystallineSituation.{u})
    [IsAffine S.S.scheme] {e : ℕ} (he : S.IsLevel e) :
    RingHom.ker (baseChangeRingHom (S.levelProj he)) =
      Ideal.span {((S.p : ℕ) : Γ(S.S.scheme, ⊤)) ^ e} := by
  ext a
  rw [RingHom.mem_ker, ← Crystalline.IsPAdicLevel.pAdicIdeal_pow_eq,
    ← Ideal.Quotient.eq_zero_iff_mem, ← levelSectionsEquiv_baseChangeRingHom_levelProj S he,
    map_eq_zero_iff _ (S.levelSectionsEquiv he).injective]

/-- **A nonzero finite divided power level exists** ([Stacks, Tag 07MV]): `p ∈ I`, so `p` is
nilpotent modulo `I` and every sufficiently large exponent is a level. -/
theorem exists_isLevel_ne_zero : ∃ e : ℕ, T.global.IsLevel e ∧ e ≠ 0 := by
  have hmem : ((T.global.p : ℕ) : Γ(T.global.S.scheme, ⊤)) ∈ T.global.baseIdeal := T.prime_mem
  have hp : IsNilpotent (Ideal.Quotient.mk T.global.baseIdeal
      ((T.global.p : ℕ) : Γ(T.global.S.scheme, ⊤))) :=
    ⟨1, by rwa [pow_one, Ideal.Quotient.eq_zero_iff_mem]⟩
  obtain ⟨N, hN⟩ := Crystalline.exists_forall_isPAdicLevel T.global.baseIdeal
    T.global.baseDividedPowers T.global.p hp
  exact ⟨N + 1, hN (N + 1) (Nat.le_succ N), Nat.succ_ne_zero N⟩

/-- `Spec(σ)`, read as a morphism from the base of `X^{(1)}/S` to that of `X/S`. -/
def twistSpecSigma : T.frobeniusTwistSituation.S ⟶ T.global.S :=
  T.specSigma

/-- The closed-fibre square of `(Spec(σ), X^{(1)} ⟶ X)`, at `twistSpecSigma`. -/
theorem twistToClosedFiber_comp_closedFiberMap_twistSpecSigma :
    T.frobeniusTwistSituation.toClosedFiber ≫
        DividedPowerScheme.closedFiberMap (twistSpecSigma T) =
      T.twistProjection ≫ T.global.toClosedFiber :=
  T.twistToClosedFiber_comp_closedFiberMap_specSigma

/-- **The level-`e` Frobenius `σ_N : S_e ⟶ S_e`**: the factorization through `S_e` of
`S_e ⟶ S ⟶ S`, the second map being `Spec(σ)`. -/
def frobeniusLevelSigma {e : ℕ} (he : T.global.IsLevel e) :
    (T.frobeniusTwistSituation.levelSituation (twistIsLevel T he)).S ⟶
      (T.global.levelSituation he).S :=
  T.global.levelLift he (T.frobeniusTwistSituation.levelProj (twistIsLevel T he) ≫ twistSpecSigma T)
    (natCast_pow_eq_zero_levelSituation T.frobeniusTwistSituation (twistIsLevel T he))

/-- `σ_N` lies over `Spec(σ)`: `σ_N ≫ ι = ι' ≫ Spec(σ)`. -/
theorem frobeniusLevelSigma_comp_levelProj {e : ℕ} (he : T.global.IsLevel e) :
    frobeniusLevelSigma T he ≫ T.global.levelProj he =
      T.frobeniusTwistSituation.levelProj (twistIsLevel T he) ≫ twistSpecSigma T :=
  T.global.levelLift_comp_levelProj he _ _

/-- The projection `X^{(1)} ⟶ X`, read between the schemes of the two level situations. -/
def frobeniusLevelTwistProjection {e : ℕ} (he : T.global.IsLevel e) :
    (T.frobeniusTwistSituation.levelSituation (twistIsLevel T he)).X ⟶
      (T.global.levelSituation he).X :=
  T.twistProjection

/-- The closed fibre of a level situation `S_e` maps to that of `S` compatibly with `S_e ⟶ S`. -/
private theorem toClosedFiber_levelSituation_comp_closedFiberMap_levelProj
    (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme] {e : ℕ} (he : S.IsLevel e) :
    (S.levelSituation he).toClosedFiber ≫ DividedPowerScheme.closedFiberMap (S.levelProj he) =
      S.toClosedFiber :=
  (S.levelProj_condition he).trans (Category.id_comp _)

/-- The level Frobenius `σ_N` and `Spec(σ)` agree on closed fibres after `S_e ⟶ S`. -/
private theorem closedFiberMap_frobeniusLevelSigma_comp_levelProj {e : ℕ}
    (he : T.global.IsLevel e) :
    DividedPowerScheme.closedFiberMap (frobeniusLevelSigma T he) ≫
        DividedPowerScheme.closedFiberMap (T.global.levelProj he) =
      DividedPowerScheme.closedFiberMap (T.frobeniusTwistSituation.levelProj (twistIsLevel T he))
        ≫ DividedPowerScheme.closedFiberMap (twistSpecSigma T) := by
  rw [← DividedPowerScheme.closedFiberMap_comp, frobeniusLevelSigma_comp_levelProj,
    DividedPowerScheme.closedFiberMap_comp]

/-- **The closed-fibre square of `(σ_N, X^{(1)} ⟶ X)` commutes.** -/
theorem frobeniusLevelSigma_condition {e : ℕ} (he : T.global.IsLevel e) :
    (T.frobeniusTwistSituation.levelSituation (twistIsLevel T he)).toClosedFiber ≫
        DividedPowerScheme.closedFiberMap (frobeniusLevelSigma T he) =
      frobeniusLevelTwistProjection T he ≫ (T.global.levelSituation he).toClosedFiber := by
  refine (cancel_mono (DividedPowerScheme.closedFiberMap (T.global.levelProj he))).mp ?_
  rw [Category.assoc, closedFiberMap_frobeniusLevelSigma_comp_levelProj, ← Category.assoc,
    toClosedFiber_levelSituation_comp_closedFiberMap_levelProj, Category.assoc,
    toClosedFiber_levelSituation_comp_closedFiberMap_levelProj]
  exact twistToClosedFiber_comp_closedFiberMap_twistSpecSigma T

/-- **The map on closed fibres of `S_e ⟶ S` is an isomorphism**: it is a monomorphism, and
`S₀ ⟶ S_e ⟶ S` identifies the closed fibre of `(S₀, 0, 0)` with `S₀`. -/
instance isIso_closedFiberMap_levelProj (S : GlobalCrystallineSituation.{u})
    [IsAffine S.S.scheme] {e : ℕ} (he : S.IsLevel e) :
    IsIso (DividedPowerScheme.closedFiberMap (S.levelProj he)) := by
  have h : DividedPowerScheme.closedFiberMap (trivialBaseToLevel he) ≫
      DividedPowerScheme.closedFiberMap (S.levelProj he) =
        (trivialClosedFiberIso (DividedPowerScheme.closedFiber S.S)).hom := by
    rw [← DividedPowerScheme.closedFiberMap_comp, trivialBaseToLevel_comp_levelProj,
      closedFiberMap_closedFiberToBaseHom]
  have : IsSplitEpi (DividedPowerScheme.closedFiberMap (S.levelProj he)) :=
    IsSplitEpi.mk' ⟨(trivialClosedFiberIso (DividedPowerScheme.closedFiber S.S)).inv ≫
      DividedPowerScheme.closedFiberMap (trivialBaseToLevel he),
        (Category.assoc _ _ _).trans ((congrArg _ h).trans (Iso.inv_hom_id _))⟩
  exact isIso_of_mono_of_isSplitEpi _

/-- The Frobenius twist square, at `twistSpecSigma`: `X^{(1)} = X ×_{S₀, F} S₀`. -/
theorem isPullback_twistSpecSigma :
    IsPullback T.twistProjection T.frobeniusTwistSituation.toClosedFiber T.global.toClosedFiber
      (DividedPowerScheme.closedFiberMap (twistSpecSigma T)) := by
  have h := T.isPullback_frobeniusTwist
  rwa [← T.closedFiberMap_specSigma] at h

/-- **The level-`e` Frobenius twist square is a pullback**: `X^{(1)} = X ×_{S_{e,0}, σ_N} S_{e,0}`
on the closed fibres of the levels, the closed fibre of `S_e` being that of `S`. -/
theorem isPullback_frobeniusLevelTwist {e : ℕ} (he : T.global.IsLevel e) :
    IsPullback (frobeniusLevelTwistProjection T he)
      (T.frobeniusTwistSituation.levelSituation (twistIsLevel T he)).toClosedFiber
      (T.global.levelSituation he).toClosedFiber
      (DividedPowerScheme.closedFiberMap (frobeniusLevelSigma T he)) := by
  have h₁ := toClosedFiber_levelSituation_comp_closedFiberMap_levelProj T.frobeniusTwistSituation
    (twistIsLevel T he)
  have h₂ := toClosedFiber_levelSituation_comp_closedFiberMap_levelProj T.global he
  have h₃ := closedFiberMap_frobeniusLevelSigma_comp_levelProj T he
  refine (isPullback_twistSpecSigma T).of_iso (Iso.refl _) (Iso.refl _)
    (asIso (DividedPowerScheme.closedFiberMap
      (T.frobeniusTwistSituation.levelProj (twistIsLevel T he)))).symm
    (asIso (DividedPowerScheme.closedFiberMap (T.global.levelProj he))).symm ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact ((IsIso.comp_inv_eq _).mpr h₁.symm).trans (Category.id_comp _).symm
  · exact ((IsIso.comp_inv_eq _).mpr h₂.symm).trans (Category.id_comp _).symm
  · exact (IsIso.comp_inv_eq _).mpr (by
      rw [Category.assoc, h₃, Iso.symm_hom, asIso_inv, IsIso.inv_hom_id_assoc])

/-! ### Arrow 1 from the inputs at one level -/

section Inputs

variable [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]

/-- **Arrow 1 of the proof of [Stacks, Tag 07N5] is an isomorphism, given its inputs at one
level.** Let `A` be `p`-adically complete, `e ≠ 0` a finite divided power level and `S_e` the
corresponding level, with the level-`e` Frobenius `σ_N` of `frobeniusLevelSigma`. If

* (P1) `RΓ(Cris(X/S), E)` and `RΓ(Cris(X^{(1)}/S), E^{(1)})` are pseudo-coherent,
* (P2) the base change maps `RΓ(CRIS(X/S), E) ⊗^L_A A/p^e ⟶ RΓ(CRIS(X/S_e), E_e)` and
  `RΓ(CRIS(X^{(1)}/S), E^{(1)}) ⊗^L_A A/p^e ⟶ RΓ(CRIS(X^{(1)}/S_e), E^{(1)}_e)` are
  isomorphisms, and
* (P3) the base change map `RΓ(CRIS(X/S_e), E_e) ⊗^L_{A/p^e, σ} A/p^e ⟶
  RΓ(CRIS(X^{(1)}/S_e), E_e^{(1)})` along `(σ_N, X^{(1)} ⟶ X)` is an isomorphism,

then `baseChangeArrow07QC T E` is an isomorphism. -/
theorem isIso_baseChangeArrow07QC_of_levelInputs
    (hcomplete : IsAdicComplete (Ideal.span {(T.global.p : Γ(T.global.S.scheme, ⊤))})
      Γ(T.global.S.scheme, ⊤))
    (E : Crystalline.FCrystal T) {e : ℕ} (he : T.global.IsLevel e) (he0 : e ≠ 0)
    [HasDerivedCategory.{wB} (BigModuleSheaf (T.global.levelSituation he))]
    [HasDerivedCategory.{wB}
      (BigModuleSheaf (T.frobeniusTwistSituation.levelSituation (twistIsLevel T he)))]
    [HasDerivedCategory.{wA}
      (ModuleCat.{u + 1} Γ((T.global.levelSituation he).S.scheme, ⊤))]
    [HasDerivedCategory.{wA} (ModuleCat.{u + 1}
      Γ((T.frobeniusTwistSituation.levelSituation (twistIsLevel T he)).S.scheme, ⊤))]
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherentIn
      (DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections T.global (toSmallFCrystal E))))
    (hL : StacksDraft.PseudoCoherence.IsPseudoCoherentIn
      (DerivedCategory.Plus.ι.obj (twistDerivedGlobalSectionsPlus T E.crystal)))
    (hX : IsIso (((derivedBaseChangeTensorAdjunction (T.global.levelProj he)).homEquiv _
      _).symm (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
        (T.global.levelProj he) (𝟙 _) (T.global.levelProj_condition he)
          ((bigModuleULift T.global).obj E.crystal)))))
    (hX1 : IsIso (((derivedBaseChangeTensorAdjunction
      (T.frobeniusTwistSituation.levelProj (twistIsLevel T he))).homEquiv _ _).symm
      (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
        (T.frobeniusTwistSituation.levelProj (twistIsLevel T he)) (𝟙 _)
        (T.frobeniusTwistSituation.levelProj_condition (twistIsLevel T he))
        ((sigmaBigModulePullback T).obj ((bigModuleULift T.global).obj E.crystal))))))
    (hσN : IsIso (((derivedBaseChangeTensorAdjunction (frobeniusLevelSigma T he)).homEquiv _
      _).symm (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
        (frobeniusLevelSigma T he) (frobeniusLevelTwistProjection T he)
        (frobeniusLevelSigma_condition T he)
        ((changeBaseBigModulePullback (T.global.levelSituation he) T.global (T.global.levelProj he)
          (𝟙 _) (T.global.levelProj_condition he)).obj
            ((bigModuleULift T.global).obj E.crystal)))))) :
    IsIso (baseChangeArrow07QC T E) :=
  isIso_baseChangeArrow07QC_of_levels_of_isAdicComplete T E (T.global.levelProj he) (𝟙 _)
    (T.global.levelProj_condition he) (frobeniusLevelSigma T he)
    (frobeniusLevelTwistProjection T he) (frobeniusLevelSigma_condition T he)
    (T.frobeniusTwistSituation.levelProj (twistIsLevel T he)) (𝟙 _)
    (T.frobeniusTwistSituation.levelProj_condition (twistIsLevel T he))
    (frobeniusLevelSigma_comp_levelProj T he)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (surjective_baseChangeRingHom_levelProj T.frobeniusTwistSituation (twistIsLevel T he))
    e he0 hcomplete
    (ker_baseChangeRingHom_levelProj T.frobeniusTwistSituation (twistIsLevel T he))
    hK hL hX hX1 hσN

/-- `isIso_baseChangeArrow07QC_of_levelInputs` with (P1) on the big crystalline sites: the
pseudo-coherence of `RΓ(CRIS(X/S), E)` and of `RΓ(CRIS(X^{(1)}/S), E^{(1)})`, which the small-site
complexes inherit through `...SmallSite.derivedRestrictModuleGlobalSectionsULiftIso`. -/
theorem isIso_baseChangeArrow07QC_of_bigLevelInputs
    (hcomplete : IsAdicComplete (Ideal.span {(T.global.p : Γ(T.global.S.scheme, ⊤))})
      Γ(T.global.S.scheme, ⊤))
    (E : Crystalline.FCrystal T) {e : ℕ} (he : T.global.IsLevel e) (he0 : e ≠ 0)
    [HasDerivedCategory.{wB} (BigModuleSheaf (T.global.levelSituation he))]
    [HasDerivedCategory.{wB}
      (BigModuleSheaf (T.frobeniusTwistSituation.levelSituation (twistIsLevel T he)))]
    [HasDerivedCategory.{wA}
      (ModuleCat.{u + 1} Γ((T.global.levelSituation he).S.scheme, ⊤))]
    [HasDerivedCategory.{wA} (ModuleCat.{u + 1}
      Γ((T.frobeniusTwistSituation.levelSituation (twistIsLevel T he)).S.scheme, ⊤))]
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherentIn (DerivedCategory.Plus.ι.obj
      ((derivedBigModuleGlobalSections T.global).obj ((bigModuleULift T.global).obj E.crystal))))
    (hL : StacksDraft.PseudoCoherence.IsPseudoCoherentIn (DerivedCategory.Plus.ι.obj
      ((derivedBigModuleGlobalSections T.frobeniusTwistSituation).obj
        ((sigmaBigModulePullback T).obj ((bigModuleULift T.global).obj E.crystal)))))
    (hX : IsIso (((derivedBaseChangeTensorAdjunction (T.global.levelProj he)).homEquiv _
      _).symm (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
        (T.global.levelProj he) (𝟙 _) (T.global.levelProj_condition he)
          ((bigModuleULift T.global).obj E.crystal)))))
    (hX1 : IsIso (((derivedBaseChangeTensorAdjunction
      (T.frobeniusTwistSituation.levelProj (twistIsLevel T he))).homEquiv _ _).symm
      (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
        (T.frobeniusTwistSituation.levelProj (twistIsLevel T he)) (𝟙 _)
        (T.frobeniusTwistSituation.levelProj_condition (twistIsLevel T he))
        ((sigmaBigModulePullback T).obj ((bigModuleULift T.global).obj E.crystal))))))
    (hσN : IsIso (((derivedBaseChangeTensorAdjunction (frobeniusLevelSigma T he)).homEquiv _
      _).symm (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
        (frobeniusLevelSigma T he) (frobeniusLevelTwistProjection T he)
        (frobeniusLevelSigma_condition T he)
        ((changeBaseBigModulePullback (T.global.levelSituation he) T.global (T.global.levelProj he)
          (𝟙 _) (T.global.levelProj_condition he)).obj
            ((bigModuleULift T.global).obj E.crystal)))))) :
    IsIso (baseChangeArrow07QC T E) :=
  isIso_baseChangeArrow07QC_of_levelInputs T hcomplete E he he0
    (hK.ofIso (DerivedCategory.Plus.ι.mapIso
      (derivedRestrictModuleGlobalSectionsULiftIso T.global E.crystal)))
    (hL.ofIso (DerivedCategory.Plus.ι.mapIso
      (derivedRestrictModuleGlobalSectionsULiftIso T.frobeniusTwistSituation
        (T.sigmaModulePullback.obj E.crystal))))
    hX hX1 hσN

end Inputs

/-! ### Arrow 1 in the standard models, from the level inputs -/

section Standard

attribute [local instance 1100] HasDerivedCategory.standard

/-- **The level input (P1) + (P2)**, in the standard models: for a global crystalline situation
with affine Noetherian `p`-adically complete base and `X ⟶ S₀` proper and smooth, and a crystal
`N` in finite locally free modules, `RΓ(CRIS(X/S), N)` is pseudo-coherent and, at every level
`N₀ > 0`, the base change map `RΓ(CRIS(X/S), N) ⊗^L_A Γ(S_{N₀}, ⊤) ⟶ RΓ(CRIS(X/S_{N₀}), N_{N₀})`
is an isomorphism. -/
def CrisLevelsInput07QC : Prop :=
  ∀ (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme],
    IsNoetherianRing Γ(S.S.scheme, ⊤) →
    IsAdicComplete (Ideal.span {(S.p : Γ(S.S.scheme, ⊤))}) Γ(S.S.scheme, ⊤) →
    IsProper S.toClosedFiber → Smooth S.toClosedFiber →
    ∀ N : SheafOfModules.{u} (crystallineStructureSheaf S),
      GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal N →
      ∀ {N₀ : ℕ} (h₀ : S.IsLevel N₀), 0 < N₀ →
        StacksDraft.PseudoCoherence.IsPseudoCoherentIn (DerivedCategory.Plus.ι.obj
          ((derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N))) ∧
        IsIso (((derivedBaseChangeTensorAdjunction (S.levelProj h₀)).homEquiv _ _).symm
          (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap (S.levelProj h₀)
            (𝟙 S.X) (S.levelProj_condition h₀) ((bigModuleULift S).obj N))))

/-- **The level input (P3)**, in the standard models: at every level `e`, for `X ⟶ S₀` proper
and smooth, the base change map along the level Frobenius `(σ_N, X^{(1)} ⟶ X)`,
`RΓ(CRIS(X/S_e), E_e) ⊗^L_{A/p^e, σ} A/p^e ⟶ RΓ(CRIS(X^{(1)}/S_e), E_e^{(1)})`, is an
isomorphism. -/
def FrobeniusLevelBaseChangeInput07QC : Prop :=
  ∀ (T : Crystalline.FCrystalSituation.{u}) (E : Crystalline.FCrystal T) {e : ℕ}
    (he : T.global.IsLevel e), IsProper T.global.toClosedFiber →
      Smooth T.global.toClosedFiber →
      IsIso (((derivedBaseChangeTensorAdjunction (frobeniusLevelSigma T he)).homEquiv _
        _).symm (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap
          (frobeniusLevelSigma T he) (frobeniusLevelTwistProjection T he)
          (frobeniusLevelSigma_condition T he)
          ((changeBaseBigModulePullback (T.global.levelSituation he) T.global
            (T.global.levelProj he) (𝟙 _) (T.global.levelProj_condition he)).obj
              ((bigModuleULift T.global).obj E.crystal)))))

/-- **The base `S_e` of a level situation is affine**, being `Spec(A/p^eA)`. -/
instance isAffine_levelSituation_S (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme]
    {e : ℕ} (he : S.IsLevel e) : IsAffine (S.levelSituation he).S.scheme :=
  inferInstanceAs (IsAffine (Spec _))

/-- **`X` is a separated quasi-compact scheme** when `X ⟶ S₀` is proper over an affine base. -/
theorem isSeparated_and_compactSpace_of_isProper (S : GlobalCrystallineSituation.{u})
    [IsAffine S.S.scheme] (hproper : IsProper S.toClosedFiber) :
    S.X.IsSeparated ∧ CompactSpace S.X := by
  have := isAffine_closedFiber_of_isAffine S ‹_›
  refine ⟨⟨?_⟩, QuasiCompact.compactSpace_of_compactSpace S.toClosedFiber⟩
  rw [Subsingleton.elim (terminal.from S.X) (S.toClosedFiber ≫ terminal.from _)]
  infer_instance

/-- **The level input (P3) from the base change theorem for `p` nilpotent and smooth `X'`**,
whose statement is the hypothesis `hbcn`: the level Frobenius square is a pullback of closed fibres
(`isPullback_frobeniusLevelTwist`), `p` is nilpotent on both levels, `X ⟶ S_{e,0}` is smooth and
`X` is separated and quasi-compact, and the pullback of `E` to `X/S_e` is a crystal in finite
locally free modules. -/
theorem frobeniusLevelBaseChangeInput07QC_of_bcn
    (hbcn : ∀ {S S' : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
      [IsAffine S'.S.scheme] (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
      (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber),
      IsPullback g S.toClosedFiber S'.toClosedFiber (DividedPowerScheme.closedFiberMap f) →
      IsNilpotent (S.p : Γ(S.S.scheme, ⊤)) → IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤)) →
      Smooth S'.toClosedFiber → ∀ [S'.X.IsSeparated] [CompactSpace S'.X]
      (N' : SheafOfModules.{u} (crystallineStructureSheaf S')),
      GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal N' →
      IsIso (((derivedBaseChangeTensorAdjunction f).homEquiv _ _).symm
        (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap f g h
          ((bigModuleULift S').obj N'))))) :
    FrobeniusLevelBaseChangeInput07QC.{u} := by
  intro T E e he hproper hsmooth
  have := hsmooth
  obtain ⟨hsep, hcpt⟩ := isSeparated_and_compactSpace_of_isProper T.global hproper
  exact hbcn (frobeniusLevelSigma T he) (frobeniusLevelTwistProjection T he)
    (frobeniusLevelSigma_condition T he) (isPullback_frobeniusLevelTwist T he)
    ⟨e, natCast_pow_eq_zero_levelSituation T.frobeniusTwistSituation (twistIsLevel T he)⟩
    ⟨e, natCast_pow_eq_zero_levelSituation T.global he⟩ inferInstance
    ((changeBaseModulePullback (T.global.levelSituation he) T.global (T.global.levelProj he)
      (𝟙 _) (T.global.levelProj_condition he)).obj E.crystal)
    (E.isFiniteLocallyFreeQuasicoherentCrystal.changeBaseModulePullback)

/-- **The level input (P3) holds**: it is `frobeniusLevelBaseChangeInput07QC_of_bcn` at the base
change theorem `...SmallSite.isIso_baseChange_of_isNilpotent_smooth` ([Stacks, Tag 07MU] for `p`
nilpotent). -/
theorem frobeniusLevelBaseChangeInput07QC : FrobeniusLevelBaseChangeInput07QC.{u} :=
  frobeniusLevelBaseChangeInput07QC_of_bcn fun f g h hpb hp hp' hsm _ _ N' hN' =>
    isIso_baseChange_of_isNilpotent_smooth f g h hpb hp hp' hsm N' hN'

/-- **Arrow 1 of the proof of [Stacks, Tag 07N5] is an isomorphism, in the standard models, from
the two level inputs.** -/
theorem isIso_baseChangeArrow07QC_of_inputs (h1 : CrisLevelsInput07QC.{u})
    (h3 : FrobeniusLevelBaseChangeInput07QC.{u})
    (hnoeth : IsNoetherianRing ↥Γ(T.global.S.scheme, ⊤))
    (hcomplete : IsAdicComplete (Ideal.span {(T.global.p : Γ(T.global.S.scheme, ⊤))})
      ↥Γ(T.global.S.scheme, ⊤))
    (hproper : IsProper T.global.toClosedFiber) (hsmooth : Smooth T.global.toClosedFiber)
    (E : Crystalline.FCrystal T) : IsIso (baseChangeArrow07QC T E) := by
  obtain ⟨e, he, he0⟩ := exists_isLevel_ne_zero T
  have hA := h1 T.global hnoeth hcomplete hproper hsmooth E.crystal
    E.isFiniteLocallyFreeQuasicoherentCrystal he (Nat.pos_of_ne_zero he0)
  have hB := h1 T.frobeniusTwistSituation hnoeth hcomplete
    (T.isProper_frobeniusTwist_toClosedFiber hproper)
    (T.smooth_frobeniusTwist_toClosedFiber hsmooth) (T.sigmaModulePullback.obj E.crystal)
    E.isFiniteLocallyFreeQuasicoherentCrystal_sigmaModulePullback (twistIsLevel T he)
    (Nat.pos_of_ne_zero he0)
  exact isIso_baseChangeArrow07QC_of_bigLevelInputs T hcomplete E he he0 hA.1 hB.1 hA.2 hB.2
    (h3 T E he hproper hsmooth)

/-- **Arrow 1 of the proof of [Stacks, Tag 07N5] is an isomorphism, in the standard models, from
the level input (P1) + (P2) alone**, (P3) being `frobeniusLevelBaseChangeInput07QC`. -/
theorem isIso_baseChangeArrow07QC_of_crisLevelsInput (h1 : CrisLevelsInput07QC.{u})
    (hnoeth : IsNoetherianRing ↥Γ(T.global.S.scheme, ⊤))
    (hcomplete : IsAdicComplete (Ideal.span {(T.global.p : Γ(T.global.S.scheme, ⊤))})
      ↥Γ(T.global.S.scheme, ⊤))
    (hproper : IsProper T.global.toClosedFiber) (hsmooth : Smooth T.global.toClosedFiber)
    (E : Crystalline.FCrystal T) : IsIso (baseChangeArrow07QC T E) :=
  isIso_baseChangeArrow07QC_of_inputs T h1 frobeniusLevelBaseChangeInput07QC hnoeth hcomplete
    hproper hsmooth E

end Standard

/-! ### Arrow 1 at arbitrary models -/

section Models

variable [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]

/-- `isIso_baseChangeArrow07QC_of_crisLevelsInput` at the models of the derived categories in
scope, by the model transport `isIso_baseChangeArrow07QC_iff_standard`. -/
theorem isIso_baseChangeArrow07QC_of_crisLevelsInput_models (h1 : CrisLevelsInput07QC.{u})
    (hnoeth : IsNoetherianRing ↥Γ(T.global.S.scheme, ⊤))
    (hcomplete : IsAdicComplete (Ideal.span {(T.global.p : Γ(T.global.S.scheme, ⊤))})
      ↥Γ(T.global.S.scheme, ⊤))
    (hproper : IsProper T.global.toClosedFiber) (hsmooth : Smooth T.global.toClosedFiber)
    (E : Crystalline.FCrystal T) : IsIso (baseChangeArrow07QC T E) :=
  (isIso_baseChangeArrow07QC_iff_standard T E).2
    (isIso_baseChangeArrow07QC_of_crisLevelsInput T h1 hnoeth hcomplete hproper hsmooth E)

end Models

end Crystalline.GlobalCrystallineSituation.SmallSite

end
