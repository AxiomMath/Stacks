module

public import StacksFrontier.AlgebraicGeometry.Algebraization.ChartLevelLocalization
public import StacksFrontier.AlgebraicGeometry.Algebraization.ChartPrimeCompletedStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteModuleModelStalk
public import StacksFrontier.RingTheory.AdicCompletion.SemilinearOfLevels
public import StacksFrontier.RingTheory.AdicCompletion.IteratedMvPolynomial

/-!
# The completed stalk of a finite module model as the completion of the chart vertex at `𝔮`

Fix an algebraization situation with `X = Spec(A)`, a finite module model `(M_n)` with its
coherent adic system `(ℱ_n)` on `U`, a point `y ∈ U ∩ Y` over the prime `𝔭` of `A`, a chart
`f ∉ 𝔭`, the completed chart ring `B = (A_f)^∧_I` and the prime `𝔮` of `B` over `𝔭 A_f`. Let `N`
be a `B`-module whose levels `N / Iⁿ⁺¹N` are identified, compatibly, with the localized model
`(M_n)_f` (the chart vertex of the source), and let `N_𝔮` be a localization of `N` at `𝔮`.

This file identifies the completed stalk `ℱ_y^∧` with the `I`-adic completion of `N_𝔮`, lying
over an identification `𝒪_{U,y}^∧ ≅ (B_𝔮)^∧` of the rings. Level by level both sides are
localizations of `M_n` at `A ∖ 𝔭`: the stalk side by
`Stacks.Algebraization.isLocalizedModule_restrictedTildeSystemToStalk` and the identification of
the levels of the formal stalk with the stalks (`formalStalkQuotientEquivStalk`), the chart side by
`Stacks.Algebraization.isLocalizedModule_chartLevelMap`. Uniqueness of localizations gives
`A`-linear identifications of the levels, compatible with the transitions, and they assemble
into the comparison of completions; semilinearity is
`AdicCompletion.addEquivOfQuotientEquiv_smul_of_levels`, the scalars of `𝒪_{U,y}` being
fractions of elements of `A`.

This is the module half of reading the depth inequalities of Stacks 0EJ3 at `y` over the local
ring `B_𝔮` of the chart, in the per-point paragraph of the proof of Stacks 0EHK.

## Main results

* `Stacks.Algebraization.completedStalkChartAddEquiv` — `ℱ_y^∧ ≅ (N_𝔮)^∧`.
* `Stacks.Algebraization.completedStalkChartAddEquiv_smul` — it lies over any ring comparison
  computed level by level by `A`-algebra maps.
* `Stacks.Algebraization.exists_completedLocalRing_chartRingEquiv` — such a ring comparison
  `𝒪_{U,y}^∧ ≅ (B_𝔮)^∧`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModuleSkyscraper

universe u

namespace Stacks.Algebraization

section FormalStalkLevels

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {J : X.IdealSheafData}
  (G : Stacks.Coherent.CoherentAdicSystems J) (x : X)

/-- The level identification of the formal stalk is the limit projection. -/
theorem formalStalkQuotientEquivStalk_apply_mk (n : ℕ) (z : formalStalk G x) :
    formalStalkQuotientEquivStalk G x n (Submodule.Quotient.mk z) =
      (limit.π (G.obj ⋙ modulesStalkFunctor X x) (op n)).hom
        (formalStalkEquivModuleStalkLimit G x z) :=
  rfl

/-- **The level identifications of the formal stalk are compatible with the transition maps.** -/
theorem formalStalkQuotientEquivStalk_transitionMap {m n : ℕ} (h : m ≤ n)
    (z : formalStalk G x ⧸ (IdealSheafData.stalk J x ^ (n + 1) •
      (⊤ : Submodule (X.presheaf.stalk x) (formalStalk G x)))) :
    formalStalkQuotientEquivStalk G x m
        (AdicCompletion.transitionMap (IdealSheafData.stalk J x) (formalStalk G x)
          (Nat.succ_le_succ h) z) =
      ((modulesStalkFunctor X x).map (G.obj.map (homOfLE h).op)).hom
        (formalStalkQuotientEquivStalk G x n z) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change formalStalkQuotientEquivStalk G x m (Submodule.Quotient.mk z) = _
  rw [formalStalkQuotientEquivStalk_apply_mk, formalStalkQuotientEquivStalk_apply_mk]
  rw [← limit.w (G.obj ⋙ modulesStalkFunctor X x) (homOfLE h).op]
  rfl

end FormalStalkLevels

/-- The level-zero quotient of a module is zero. -/
theorem subsingleton_quotient_idealPow_zero_smul_top {R : Type*} [CommRing R] (I : Ideal R)
    (X : Type*) [AddCommGroup X] [Module R X] :
    Subsingleton (X ⧸ (I ^ 0 • (⊤ : Submodule R X))) := by
  rw [Submodule.Quotient.subsingleton_iff, pow_zero, Ideal.one_eq_top, Submodule.top_smul]

section Chart

variable (S : AlgebraizationSituation.{u}) (y : S.U.toScheme) (f : S.A)
  (hf : f ∉ (underlyingPrime S y).asIdeal) (hI : S.I ≤ (underlyingPrime S y).asIdeal)

variable [(chartPrimeOfPoint S y f).IsPrime]

variable (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)
  {N : Type u} [AddCommGroup N]
  [Module (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
    (Localization.Away f)) N]
  [Module S.A N] [Module (Localization.Away f) N] [IsScalarTower S.A (Localization.Away f) N]
  [IsScalarTower (Localization.Away f)
    (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)) N]
  [IsScalarTower S.A
    (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)) N]
  (Rq : Type u) [CommRing Rq]
  [Algebra (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
    (Localization.Away f)) Rq]
  [Algebra S.A Rq]
  [IsScalarTower S.A
    (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)) Rq]
  [IsLocalization (adicPrimeOver (S.I.map (algebraMap S.A (Localization.Away f)))
    (Ideal.map_mono hI)).asIdeal.primeCompl Rq]
  {Nq : Type u} [AddCommGroup Nq]
  [Module (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
    (Localization.Away f)) Nq]
  [Module Rq Nq]
  [IsScalarTower (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
    (Localization.Away f)) Rq Nq]
  [Module S.A Nq] [IsScalarTower S.A Rq Nq]
  [IsScalarTower S.A
    (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)) Nq]
  (fq : N →ₗ[AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
    (Localization.Away f)] Nq)
  [IsLocalizedModule (adicPrimeOver (S.I.map (algebraMap S.A (Localization.Away f)))
    (Ideal.map_mono hI)).asIdeal.primeCompl fq]
  (e : ∀ n : ℕ, LocalizedModule (Submonoid.powers f) (M.obj (op n)) ≃ₗ[Localization.Away f]
    (N ⧸ (((S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap
      (Localization.Away f) (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
        (Localization.Away f)))) ^ (n + 1) •
      (⊤ : Submodule (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
        (Localization.Away f)) N))))

include hf in
/-- **The chart side of each level is a localization at the complement of the prime under
`y`**: the composite `M_n → (M_n)_f ≅ N / Iⁿ⁺¹N → N_𝔮 / Iⁿ⁺¹N_𝔮`. -/
theorem isLocalizedModule_chartSideLevelMap (n : ℕ) :
    IsLocalizedModule (underlyingPrime S y).asIdeal.primeCompl
      (chartLevelMap f (S.I.map (algebraMap S.A (Localization.Away f))) (Ideal.map_mono hI)
        (n + 1) (e n) Rq fq) := by
  have h := isLocalizedModule_chartLevelMap f (S.I.map (algebraMap S.A (Localization.Away f)))
    (Ideal.fg_of_isNoetherianRing _) (Ideal.map_mono hI) (n + 1) (e n) Rq fq
  have hT : chartBaseCompl f (p := chartPrimeOfPoint S y f) =
      (underlyingPrime S y).asIdeal.primeCompl := by
    ext a
    change a ∉ _ ↔ a ∉ _
    rw [comap_chartPrimeOfPoint S y f hf]
  exact hT ▸ h

omit [IsScalarTower S.A
    (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)) Rq] in
/-- The chart side of the levels is compatible with the transition maps. -/
theorem transitionMap_chartLevelMap
    (he : ∀ {m n : ℕ} (h : m ≤ n) (z : LocalizedModule (Submonoid.powers f) (M.obj (op n))),
      AdicCompletion.transitionMap _ N (Nat.succ_le_succ h) (e n z) =
        e m (LocalizedModule.map (Submonoid.powers f) (M.map (homOfLE h).op).hom z))
    {m n : ℕ} (h : m ≤ n) (x : M.obj (op n)) :
    AdicCompletion.transitionMap _ Nq (Nat.succ_le_succ h)
        (chartLevelMap f (S.I.map (algebraMap S.A (Localization.Away f))) (Ideal.map_mono hI)
          (n + 1) (e n) Rq fq x) =
      chartLevelMap f (S.I.map (algebraMap S.A (Localization.Away f))) (Ideal.map_mono hI)
        (m + 1) (e m) Rq fq ((M.map (homOfLE h).op).hom x) := by
  change AdicCompletion.transitionMap _ Nq (Nat.succ_le_succ h) (levelLocalizationMap _ _ Rq fq
      (n + 1) (e n (LocalizedModule.mk x 1))) =
    levelLocalizationMap _ _ Rq fq (m + 1)
      (e m (LocalizedModule.mk ((M.map (homOfLE h).op).hom x) 1))
  rw [transitionMap_levelLocalizationMap, he, LocalizedModule.map_mk]

variable [Algebra S.A (S.U.toScheme.presheaf.stalk y)]
  (halg : algebraMap S.A (S.U.toScheme.presheaf.stalk y) = baseToPointStalk S y)
  (hM : IsFiniteModuleModel S M)
  [Module S.A (formalStalk (coherentAdicSystemOfFiniteModuleModel S M hM) y)]
  [IsScalarTower S.A (S.U.toScheme.presheaf.stalk y)
    (formalStalk (coherentAdicSystemOfFiniteModuleModel S M hM) y)]

include halg in
/-- The level identification of the formal stalk, as an `A`-linear equivalence onto the stalk
with its `A`-module structure through `baseToPointStalk`. -/
def formalStalkLevelEquiv (n : ℕ) :
    (formalStalk (coherentAdicSystemOfFiniteModuleModel S M hM) y ⧸
        (IdealSheafData.stalk (idealOnOpen S) y ^ (n + 1) •
          (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            (formalStalk (coherentAdicSystemOfFiniteModuleModel S M hM) y)))) ≃ₗ[S.A]
      (ModuleCat.restrictScalars.{u} (baseToPointStalk S y)).obj
        ((modulesStalkFunctor S.U.toScheme y).obj ((restrictedTildeSystem S M).obj (op n))) where
  toFun z := formalStalkQuotientEquivStalk (coherentAdicSystemOfFiniteModuleModel S M hM) y n z
  invFun w := (formalStalkQuotientEquivStalk (coherentAdicSystemOfFiniteModuleModel S M hM) y
    n).symm w
  map_add' _ _ := map_add _ _ _
  map_smul' a z := by
    rw [RingHom.id_apply, ← algebraMap_smul (S.U.toScheme.presheaf.stalk y) a z, map_smul, halg]
    rfl
  left_inv z := LinearEquiv.symm_apply_apply _ z
  right_inv w := LinearEquiv.apply_symm_apply _ w

include hf in
/-- The identification of the level-`n + 1` stalk with the chart side, by uniqueness of
localizations: both are localizations of `M_n` at the complement of the prime under `y`. -/
def stalkChartLevelIso (n : ℕ) :
    (ModuleCat.restrictScalars.{u} (baseToPointStalk S y)).obj
        ((modulesStalkFunctor S.U.toScheme y).obj ((restrictedTildeSystem S M).obj (op n))) ≃ₗ[S.A]
      (Nq ⧸ (((S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap
        (Localization.Away f) (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
          (Localization.Away f)))).map (algebraMap _ Rq) ^ (n + 1) • (⊤ : Submodule Rq Nq))) :=
  haveI := isLocalizedModule_chartSideLevelMap S y f hf hI M Rq fq e n
  haveI := isLocalizedModule_restrictedTildeSystemToStalk S y M (op n)
  IsLocalizedModule.linearEquiv (underlyingPrime S y).asIdeal.primeCompl
    ((restrictedTildeSystemToStalk S y M).app (op n)).hom
    (chartLevelMap f (S.I.map (algebraMap S.A (Localization.Away f))) (Ideal.map_mono hI)
      (n + 1) (e n) Rq fq)

omit [Algebra S.A (S.U.toScheme.presheaf.stalk y)] in
include hf in
/-- On the image of a section of `M_n` in the stalk, `stalkChartLevelIso` is the chart-side
level map applied to that section. -/
theorem stalkChartLevelIso_apply (n : ℕ) (x : M.obj (op n)) :
    stalkChartLevelIso S y f hf hI M Rq fq e n
        (((restrictedTildeSystemToStalk S y M).app (op n)).hom x) =
      chartLevelMap f (S.I.map (algebraMap S.A (Localization.Away f))) (Ideal.map_mono hI)
        (n + 1) (e n) Rq fq x := by
  have := isLocalizedModule_chartSideLevelMap S y f hf hI M Rq fq e n
  have := isLocalizedModule_restrictedTildeSystemToStalk S y M (op n)
  exact IsLocalizedModule.linearEquiv_apply _ _ _ x

omit [Algebra S.A (S.U.toScheme.presheaf.stalk y)] in
include hf in
/-- The identifications of the stalks with the chart side are compatible with the transition
maps. -/
theorem stalkChartLevelIso_naturality
    (he : ∀ {m n : ℕ} (h : m ≤ n) (z : LocalizedModule (Submonoid.powers f) (M.obj (op n))),
      AdicCompletion.transitionMap _ N (Nat.succ_le_succ h) (e n z) =
        e m (LocalizedModule.map (Submonoid.powers f) (M.map (homOfLE h).op).hom z))
    {m n : ℕ} (h : m ≤ n) (w : (ModuleCat.restrictScalars.{u} (baseToPointStalk S y)).obj
        ((modulesStalkFunctor S.U.toScheme y).obj ((restrictedTildeSystem S M).obj (op n)))) :
    AdicCompletion.transitionMap _ Nq (Nat.succ_le_succ h)
        (stalkChartLevelIso S y f hf hI M Rq fq e n w) =
      stalkChartLevelIso S y f hf hI M Rq fq e m
        (((modulesStalkFunctor S.U.toScheme y).map
          ((restrictedTildeSystem S M).map (homOfLE h).op)).hom w) := by
  have := isLocalizedModule_chartSideLevelMap S y f hf hI M Rq fq e m
  have := isLocalizedModule_restrictedTildeSystemToStalk S y M (op n)
  have key := IsLocalizedModule.ext (underlyingPrime S y).asIdeal.primeCompl
    ((restrictedTildeSystemToStalk S y M).app (op n)).hom
    (IsLocalizedModule.map_units (chartLevelMap f (S.I.map (algebraMap S.A (Localization.Away f)))
      (Ideal.map_mono hI) (m + 1) (e m) Rq fq))
    (j := ((AdicCompletion.transitionMap _ Nq (Nat.succ_le_succ h)).restrictScalars S.A) ∘ₗ
      (stalkChartLevelIso S y f hf hI M Rq fq e n).toLinearMap)
    (k := (stalkChartLevelIso S y f hf hI M Rq fq e m).toLinearMap ∘ₗ
      ((ModuleCat.restrictScalars.{u} (baseToPointStalk S y)).map
        ((modulesStalkFunctor S.U.toScheme y).map
          ((restrictedTildeSystem S M).map (homOfLE h).op))).hom) (by
      ext x
      have hnat := congrArg (fun φ => φ.hom x)
        ((restrictedTildeSystemToStalk S y M).naturality (homOfLE h).op)
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hnat ⊢
      rw [LinearEquiv.coe_coe, stalkChartLevelIso_apply]
      change _ = stalkChartLevelIso S y f hf hI M Rq fq e m
        ((((restrictedTildeSystem S M ⋙ modulesStalkFunctor S.U.toScheme y ⋙
          ModuleCat.restrictScalars.{u} (baseToPointStalk S y)).map (homOfLE h).op).hom)
            (((restrictedTildeSystemToStalk S y M).app (op n)).hom x))
      rw [← hnat, stalkChartLevelIso_apply]
      exact transitionMap_chartLevelMap S y f hI M Rq fq e he h x)
  exact congrArg (fun φ => φ w) key


include hf halg in
/-- **The levels of the completed stalk are the levels of the completed chart vertex at `𝔮`**,
`A`-linearly. -/
def completedStalkChartLevelEquiv : ∀ n : ℕ,
    (formalStalk (coherentAdicSystemOfFiniteModuleModel S M hM) y ⧸
        (IdealSheafData.stalk (idealOnOpen S) y ^ n •
          (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            (formalStalk (coherentAdicSystemOfFiniteModuleModel S M hM) y)))) ≃ₗ[S.A]
      (Nq ⧸ (((S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap
        (Localization.Away f) (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
          (Localization.Away f)))).map (algebraMap _ Rq) ^ n • (⊤ : Submodule Rq Nq)))
  | 0 =>
    haveI := subsingleton_quotient_idealPow_zero_smul_top
      (IdealSheafData.stalk (idealOnOpen S) y)
      (formalStalk (coherentAdicSystemOfFiniteModuleModel S M hM) y)
    haveI := subsingleton_quotient_idealPow_zero_smul_top
      (((S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap
        (Localization.Away f) (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
          (Localization.Away f)))).map (algebraMap _ Rq)) Nq
    LinearEquiv.ofSubsingleton _ _
  | n + 1 => (formalStalkLevelEquiv S y M halg hM n).trans
      (stalkChartLevelIso S y f hf hI M Rq fq e n)

include hf halg in
/-- The level identifications are compatible with the transition maps. -/
theorem completedStalkChartLevelEquiv_transitionMap
    (he : ∀ {m n : ℕ} (h : m ≤ n) (z : LocalizedModule (Submonoid.powers f) (M.obj (op n))),
      AdicCompletion.transitionMap _ N (Nat.succ_le_succ h) (e n z) =
        e m (LocalizedModule.map (Submonoid.powers f) (M.map (homOfLE h).op).hom z))
    {m n : ℕ} (h : m ≤ n) (x : formalStalk (coherentAdicSystemOfFiniteModuleModel S M hM) y ⧸
        (IdealSheafData.stalk (idealOnOpen S) y ^ n •
          (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            (formalStalk (coherentAdicSystemOfFiniteModuleModel S M hM) y)))) :
    AdicCompletion.transitionMap _ Nq h
        ((completedStalkChartLevelEquiv S y f hf hI M Rq fq e halg hM n).toAddEquiv x) =
      (completedStalkChartLevelEquiv S y f hf hI M Rq fq e halg hM m).toAddEquiv
        (AdicCompletion.transitionMap _ _ h x) := by
  rcases m with _ | m
  · exact (subsingleton_quotient_idealPow_zero_smul_top _ Nq).elim _ _
  rcases n with _ | n
  · omega
  have h' : m ≤ n := Nat.le_of_succ_le_succ h
  change AdicCompletion.transitionMap _ Nq (Nat.succ_le_succ h')
      (stalkChartLevelIso S y f hf hI M Rq fq e n (formalStalkLevelEquiv S y M halg hM n x)) =
    stalkChartLevelIso S y f hf hI M Rq fq e m (formalStalkLevelEquiv S y M halg hM m
      (AdicCompletion.transitionMap _ _ (Nat.succ_le_succ h') x))
  rw [stalkChartLevelIso_naturality S y f hf hI M Rq fq e he h']
  congr 1
  exact (formalStalkQuotientEquivStalk_transitionMap
    (coherentAdicSystemOfFiniteModuleModel S M hM) y h' x).symm

variable (he : ∀ {m n : ℕ} (h : m ≤ n) (z : LocalizedModule (Submonoid.powers f) (M.obj (op n))),
      AdicCompletion.transitionMap _ N (Nat.succ_le_succ h) (e n z) =
        e m (LocalizedModule.map (Submonoid.powers f) (M.map (homOfLE h).op).hom z))

include hf halg in
/-- **The completed stalk of the coherent adic system of a finite module model at `y` is the
completion of the chart vertex localized at `𝔮`**, as an additive equivalence assembled from the
`A`-linear identifications of the levels. -/
def completedStalkChartAddEquiv :
    completedStalk (idealOnOpen S) (coherentAdicSystemOfFiniteModuleModel S M hM) y ≃+
      AdicCompletion (((S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap
        (Localization.Away f) (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
          (Localization.Away f)))).map (algebraMap _ Rq)) Nq :=
  AdicCompletion.addEquivOfQuotientEquiv _ _
    (fun n => (completedStalkChartLevelEquiv S y f hf hI M Rq fq e halg hM n).toAddEquiv)
    (fun h x => completedStalkChartLevelEquiv_transitionMap S y f hf hI M Rq fq e halg hM he h x)

include hf halg in
/-- **The comparison lies over any ring comparison computed level by level by `A`-algebra
maps.** -/
theorem completedStalkChartAddEquiv_smul
    (σ : completedLocalRing (idealOnOpen S) y →
      AdicCompletion (((S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap
        (Localization.Away f) (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
          (Localization.Away f)))).map (algebraMap _ Rq)) Rq)
    (ψ : ∀ n : ℕ, (S.U.toScheme.presheaf.stalk y ⧸
        IdealSheafData.stalk (idealOnOpen S) y ^ n) →ₐ[S.A]
      (Rq ⧸ (((S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap
        (Localization.Away f) (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
          (Localization.Away f)))).map (algebraMap _ Rq)) ^ n))
    (hσ : ∀ (n : ℕ) (r : completedLocalRing (idealOnOpen S) y),
      AdicCompletion.evalₐ _ n (σ r) = ψ n (AdicCompletion.evalₐ _ n r))
    (r : completedLocalRing (idealOnOpen S) y)
    (x : completedStalk (idealOnOpen S) (coherentAdicSystemOfFiniteModuleModel S M hM) y) :
    completedStalkChartAddEquiv S y f hf hI M Rq fq e halg hM he (r • x) =
      σ r • completedStalkChartAddEquiv S y f hf hI M Rq fq e halg hM he x := by
  refine AdicCompletion.addEquivOfQuotientEquiv_smul_of_levels _ _
    (completedStalkChartLevelEquiv S y f hf hI M Rq fq e halg hM)
    (fun h x => completedStalkChartLevelEquiv_transitionMap S y f hf hI M Rq fq e halg hM he h x)
    σ ψ hσ (fun r => ?_) r x
  have := isLocalization_pointStalk S y halg
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj (underlyingPrime S y).asIdeal.primeCompl r
  refine ⟨a, s, by rw [mul_comm]; exact has, ?_⟩
  have hs : algebraMap S.A (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
      (Localization.Away f)) s ∈ (adicPrimeOver (S.I.map (algebraMap S.A (Localization.Away f)))
        (Ideal.map_mono hI)).asIdeal.primeCompl := by
    intro hmem
    have h2 := (algebraMap_mem_adicPrimeOver_iff f (S.I.map (algebraMap S.A (Localization.Away f)))
      (Ideal.map_mono hI) (s : S.A)).mp hmem
    rw [comap_chartPrimeOfPoint S y f hf] at h2
    exact s.2 h2
  rw [IsScalarTower.algebraMap_apply S.A (AdicCompletion (S.I.map (algebraMap S.A
    (Localization.Away f))) (Localization.Away f)) Rq]
  exact IsLocalization.map_units Rq ⟨_, hs⟩

omit [(chartPrimeOfPoint S y f).IsPrime] in
/-- An ideal is its own image under the identity equivalence. -/
theorem ideal_eq_map_refl {R : Type*} [CommRing R] {A' : Type*} [CommRing A'] [Algebra A' R]
    {I J : Ideal R} (h : J = I) : J = I.map ((AlgEquiv.refl : R ≃ₐ[A'] R) : R →+* R) := by
  rw [h]
  exact (Ideal.map_id I).symm

variable [Algebra (Localization.Away f) (S.U.toScheme.presheaf.stalk y)]
  [IsScalarTower S.A (Localization.Away f) (S.U.toScheme.presheaf.stalk y)]
  [Algebra (Localization.Away f) Rq]
  [IsScalarTower (Localization.Away f)
    (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)) Rq]
  [IsScalarTower S.A (Localization.Away f) Rq]

omit [IsScalarTower S.A
    (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)) Rq]
  [IsLocalization (adicPrimeOver (S.I.map (algebraMap S.A (Localization.Away f)))
    (Ideal.map_mono hI)).asIdeal.primeCompl Rq] in
include hf hI halg in
/-- **The ring comparison `𝒪_{U,y}^∧ ≅ (B_𝔮)^∧` with its levels**: an `A`-algebra equivalence
whose level-`n` reductions are `A`-algebra maps. It is
`Stacks.Algebraization.adicCompletionLocalizationAlgEquiv` at the chart ring, with the ideals
respelled. -/
theorem exists_completedLocalRing_chartRingEquiv
    [IsLocalization (adicPrimeOver (S.I.map (algebraMap S.A (Localization.Away f)))
      (Ideal.map_mono hI)).asIdeal.primeCompl Rq] :
    ∃ (σ : completedLocalRing (idealOnOpen S) y ≃ₐ[S.A]
        AdicCompletion (((S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap
          (Localization.Away f) (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
            (Localization.Away f)))).map (algebraMap _ Rq)) Rq)
      (ψ : ∀ n : ℕ, (S.U.toScheme.presheaf.stalk y ⧸
          IdealSheafData.stalk (idealOnOpen S) y ^ n) →ₐ[S.A]
        (Rq ⧸ (((S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap
          (Localization.Away f) (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
            (Localization.Away f)))).map (algebraMap _ Rq)) ^ n)),
      ∀ (n : ℕ) (r : completedLocalRing (idealOnOpen S) y),
        AdicCompletion.evalₐ _ n (σ r) = ψ n (AdicCompletion.evalₐ _ n r) := by
  have := isLocalization_chartPrimeOfPoint S y f halg hf
  have hfg : (S.I.map (algebraMap S.A (Localization.Away f))).FG := Ideal.fg_of_isNoetherianRing _
  have h1 : (S.I.map (algebraMap S.A (Localization.Away f))).map
      (algebraMap (Localization.Away f) (S.U.toScheme.presheaf.stalk y)) =
      IdealSheafData.stalk (idealOnOpen S) y :=
    map_map_chartIdeal_eq_stalk_idealOnOpen S y f halg
  have h2 : ((S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap (Localization.Away f)
      (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)))).map
        (algebraMap _ Rq) = (S.I.map (algebraMap S.A (Localization.Away f))).map
          (algebraMap (Localization.Away f) Rq) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let c₁ := AdicCompletion.congrAlgEquiv (A := S.A)
    (AlgEquiv.refl : S.U.toScheme.presheaf.stalk y ≃ₐ[S.A] _) (ideal_eq_map_refl h1)
  let φ := (adicCompletionLocalizationAlgEquiv (S.I.map (algebraMap S.A (Localization.Away f)))
    hfg (Ideal.map_mono hI) (S.U.toScheme.presheaf.stalk y) Rq).restrictScalars S.A
  let c₂ := AdicCompletion.congrAlgEquiv (A := S.A) (AlgEquiv.refl : Rq ≃ₐ[S.A] Rq)
    (ideal_eq_map_refl h2)
  let q₁ := AdicCompletion.congrQuotientEquiv (A := S.A)
    (AlgEquiv.refl : S.U.toScheme.presheaf.stalk y ≃ₐ[S.A] _) (ideal_eq_map_refl h1)
  let q₂ := AdicCompletion.congrQuotientEquiv (A := S.A) (AlgEquiv.refl : Rq ≃ₐ[S.A] Rq)
    (ideal_eq_map_refl h2)
  refine ⟨(c₁.trans φ).trans c₂, fun n =>
    ((q₂ n).toAlgHom.comp
      ((levelAlgEquivPow (S.I.map (algebraMap S.A (Localization.Away f))) hfg (Ideal.map_mono hI)
        (S.U.toScheme.presheaf.stalk y) Rq n).restrictScalars S.A).toAlgHom).comp
      (q₁ n).toAlgHom, fun n r => ?_⟩
  have e₂ := AdicCompletion.evalₐ_adicCompletionAlgEquivOfQuotientEquiv _ _ q₂
    (AdicCompletion.congrQuotientEquiv_factorPow _ (ideal_eq_map_refl h2)) n (φ (c₁ r))
  have e₁ := AdicCompletion.evalₐ_adicCompletionAlgEquivOfQuotientEquiv _ _ q₁
    (AdicCompletion.congrQuotientEquiv_factorPow _ (ideal_eq_map_refl h1)) n r
  have eφ := evalₐ_adicCompletionLocalizationAlgEquiv (S.I.map (algebraMap S.A
    (Localization.Away f))) hfg (Ideal.map_mono hI) (S.U.toScheme.presheaf.stalk y) Rq n (c₁ r)
  change AdicCompletion.evalₐ _ n (c₂ (φ (c₁ r))) = _
  refine e₂.trans ?_
  change AdicCompletion.congrQuotientEquiv _ _ n (AdicCompletion.evalₐ _ n
    (adicCompletionLocalizationAlgEquiv (S.I.map (algebraMap S.A (Localization.Away f))) hfg
      (Ideal.map_mono hI) (S.U.toScheme.presheaf.stalk y) Rq (c₁ r))) = _
  rw [eφ, show AdicCompletion.evalₐ _ n (c₁ r) = _ from e₁]
  rfl

end Chart

end Stacks.Algebraization

end
