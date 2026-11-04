module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkModuleComparison
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkChartComparison
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.RingTheory.AdicCompletion.IteratedMvPolynomial
public import StacksFrontier.RingTheory.AdicCompletion.SemilinearOfLevels

/-!
# The completed stalk at a point of an affine open, as a completed localization

Let `X` be a locally Noetherian scheme, `ℐ` an ideal sheaf, `(ℱₙ)` an object of `Coh(X, ℐ)`, and
`U` an affine open with ring `R = Γ(X, U)` and ideal `I₀ = ℐ(U)`. Let `A = R^∧` be the
`I₀`-adic completion and `L` an `R`-module with `L/I₀ⁿ⁺¹L ≅ Γ(U, ℱₙ)` compatibly; put
`M = L^∧`. At a point `x ∈ U ∩ V(ℐ)` with prime `𝔭 ⊆ R`, and the prime `𝔮 ⊆ A` above it
containing `I₀A`, this file identifies

* the completed local ring `𝒪_{X,x}^∧` with the `I₀`-adic completion of `A_𝔮`, and
* the completed stalk `ℱ_x^∧` with the `I₀`-adic completion of `M_𝔮`, lying over it.

Level by level both sides are localizations at `𝔭` of `R/I₀ⁿ` and of `L/I₀ⁿL ≅ Γ(U, ℱₙ₋₁)`:
the stalk side because the stalks of a quasi-coherent module on an affine open are localizations
of its sections, the completed side by `Stacks.Algebraization.adicCompletionLocalizationAlgEquiv`
and `Stacks.Algebraization.isLocalizedModule_levelLocalizationMapCompletion`.

## Main definitions

* `Stacks.Algebraization.completedLocalRingAffineOpenAlgEquiv` — `𝒪_{X,x}^∧ ≅ (A_𝔮)^∧`.

## References

* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF), whose proof reads the
  conditions on completed stalks over the completed affine ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace Stacks.Algebraization

section Ring

variable {X : Scheme.{u}} (I : X.IdealSheafData) {U : X.Opens} (hU : IsAffineOpen U)
  [IsNoetherianRing Γ(X, U)] (x : U)
  (hIx : I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf x).asIdeal)

/-- The ideal of the completed affine ring above the point `x`: the prime of the
`I₀`-adic completion of `Γ(X, U)` over the prime of `x`. -/
abbrev affineOpenCompletedPrime : PrimeSpectrum (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) :=
  adicPrimeOver (I.ideal ⟨U, hU⟩) hIx

variable (q : PrimeSpectrum (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))
  (hq : q = affineOpenCompletedPrime I hU x hIx)

omit [IsNoetherianRing Γ(X, U)] in
include hq in
/-- The localization at a prime equal to the prime above `x` is a localization at the prime
above `x`. -/
theorem isLocalization_atPrime_affineOpenCompletedPrime :
    IsLocalization (affineOpenCompletedPrime I hU x hIx).asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal) := by
  subst hq
  infer_instance

omit [IsNoetherianRing Γ(X, U)] in
/-- The stalk of `ℐ` at a point of `U` is the extension of `ℐ(U)`. -/
theorem stalk_eq_map_algebraMap_stalk :
    IdealSheafData.stalk I x.1 =
      (I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) (X.presheaf.stalk x.1)) :=
  IdealSheafData.stalk_eq_map_germ I x.1 ⟨U, hU⟩ x.2

omit [IsNoetherianRing Γ(X, U)] in
/-- The extension of `ℐ(U)` to the completion and then to the localization at `𝔮` is its
extension to the localization. -/
theorem map_map_completedPrime_localization :
    ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))).map
        (algebraMap (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
          (Localization.AtPrime q.asIdeal)) =
      (I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U)
        (Localization.AtPrime q.asIdeal)) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- **The completed local ring at a point of an affine open is the completed localization of
the completed affine ring**: `𝒪_{X,x}^∧ ≅ (A_𝔮)^∧`, the completions being along `ℐ_x` and along
`I₀A_𝔮`, as `Γ(X, U)`-algebras. -/
def completedLocalRingAffineOpenAlgEquiv :
    completedLocalRing I x.1 ≃ₐ[Γ(X, U)]
      AdicCompletion ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U)
          (Localization.AtPrime q.asIdeal)))
        (Localization.AtPrime q.asIdeal) :=
  haveI := hU.isLocalization_stalk x
  haveI := isLocalization_atPrime_affineOpenCompletedPrime I hU x hIx q hq
  (AdicCompletion.congrAlgEquiv (A := Γ(X, U))
    (AlgEquiv.refl : X.presheaf.stalk x.1 ≃ₐ[Γ(X, U)] _)
    (ideal_eq_map_refl (stalk_eq_map_algebraMap_stalk I hU x).symm)).trans
  (adicCompletionLocalizationAlgEquiv (I.ideal ⟨U, hU⟩)
    (Ideal.fg_of_isNoetherianRing _) hIx (X.presheaf.stalk x.1)
    (Localization.AtPrime q.asIdeal))

/-- The levels of `completedLocalRingAffineOpenAlgEquiv`, as `Γ(X, U)`-algebra maps. -/
def completedLocalRingAffineOpenLevel (n : ℕ) :
    (X.presheaf.stalk x.1 ⧸ IdealSheafData.stalk I x.1 ^ n) →ₐ[Γ(X, U)]
      (Localization.AtPrime q.asIdeal ⧸
        ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U)
          (Localization.AtPrime q.asIdeal))) ^ n) :=
  haveI := hU.isLocalization_stalk x
  haveI := isLocalization_atPrime_affineOpenCompletedPrime I hU x hIx q hq
  AlgHom.comp
    (levelAlgEquivPow (I.ideal ⟨U, hU⟩) (Ideal.fg_of_isNoetherianRing _) hIx
      (X.presheaf.stalk x.1)
      (Localization.AtPrime q.asIdeal) n).toAlgHom
    (Ideal.quotientEquivAlgOfEq Γ(X, U)
      (congrArg (· ^ n) (stalk_eq_map_algebraMap_stalk I hU x))).toAlgHom

/-- `completedLocalRingAffineOpenAlgEquiv` is computed level by level by
`completedLocalRingAffineOpenLevel`. -/
theorem evalₐ_completedLocalRingAffineOpenAlgEquiv (n : ℕ) (r : completedLocalRing I x.1) :
    AdicCompletion.evalₐ ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U)
        (Localization.AtPrime q.asIdeal))) n
        (completedLocalRingAffineOpenAlgEquiv I hU x hIx q hq r) =
      completedLocalRingAffineOpenLevel I hU x hIx q hq n
        (AdicCompletion.evalₐ (IdealSheafData.stalk I x.1) n r) := by
  have := hU.isLocalization_stalk x
  have := isLocalization_atPrime_affineOpenCompletedPrime I hU x hIx q hq
  let c₁ := AdicCompletion.congrAlgEquiv (A := Γ(X, U))
    (AlgEquiv.refl : X.presheaf.stalk x.1 ≃ₐ[Γ(X, U)] _)
    (ideal_eq_map_refl (stalk_eq_map_algebraMap_stalk I hU x).symm)
  have e₁ : AdicCompletion.evalₐ ((I.ideal ⟨U, hU⟩).map
        (algebraMap Γ(X, U) (X.presheaf.stalk x.1))) n (c₁ r) =
      Ideal.quotientEquivAlgOfEq Γ(X, U)
        (congrArg (· ^ n) (stalk_eq_map_algebraMap_stalk I hU x))
        (AdicCompletion.evalₐ (IdealSheafData.stalk I x.1) n r) := by
    refine (AdicCompletion.evalₐ_adicCompletionAlgEquivOfQuotientEquiv _ _ _ _ n r).trans ?_
    obtain ⟨r₀, hr₀⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (IdealSheafData.stalk I x.1) n r)
    rw [← hr₀]
    rfl
  have h1 := evalₐ_adicCompletionLocalizationAlgEquiv (I.ideal ⟨U, hU⟩)
    (Ideal.fg_of_isNoetherianRing _) hIx (X.presheaf.stalk x.1)
    (Localization.AtPrime q.asIdeal) n (c₁ r)
  exact h1.trans (congrArg (levelRingEquivPow (I.ideal ⟨U, hU⟩)
    (Ideal.fg_of_isNoetherianRing _) hIx (X.presheaf.stalk x.1)
    (Localization.AtPrime q.asIdeal) n) e₁)

end Ring

section Module

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {I : X.IdealSheafData} {U : X.Opens}
  (hU : IsAffineOpen U) [IsNoetherianRing Γ(X, U)] (F : Stacks.Coherent.CoherentAdicSystems I)
  {L : Type u} [AddCommGroup L] [Module Γ(X, U) L]
  (ε : ∀ n : ℕ, (L ⧸ (I.ideal ⟨U, hU⟩ ^ (n + 1) • (⊤ : Submodule Γ(X, U) L))) ≃ₗ[Γ(X, U)]
    Γ(F.obj.obj (op n), U))
  (x : U) (hIx : I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf x).asIdeal)
  (q : PrimeSpectrum (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))
  (hq : q = affineOpenCompletedPrime I hU x hIx)

omit [IsLocallyNoetherian X] [IsNoetherianRing Γ(X, U)] in
include hq in
/-- The localization of `M` at a prime equal to the prime above `x` is a localization at the
prime above `x`. -/
theorem isLocalizedModule_atPrime_affineOpenCompletedPrime :
    IsLocalizedModule (affineOpenCompletedPrime I hU x hIx).asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (AdicCompletion (I.ideal ⟨U, hU⟩) L)) := by
  subst hq
  infer_instance

/-- The localization `M_𝔮` of `M = L^∧` at the prime of the completed affine ring above `x`. -/
abbrev affineOpenLocalizedCompletion :=
  LocalizedModule q.asIdeal.primeCompl
    (AdicCompletion (I.ideal ⟨U, hU⟩) L)

/-- The stalk at `x` of the `n`-th term of the system, as a `Γ(X, U)`-module through the germ
map. -/
abbrev affineOpenStalkLevel (n : ℕ) :=
  (ModuleCat.restrictScalars (X.presheaf.germ U x.1 x.2).hom).obj
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x.1).obj (F.obj.obj (op n)))

/-- The germ map of the `n`-th term on sections over `U`, as a `Γ(X, U)`-linear map. -/
def affineOpenSectionGerm (n : ℕ) :
    Γ(F.obj.obj (op n), U) →ₗ[Γ(X, U)] affineOpenStalkLevel F x n where
  toFun s := ((F.obj.obj (op n)).presheaf.germ U x.1 x.2).hom s
  map_add' _ _ := map_add _ _ _
  map_smul' r s := germ_smul x.1 U x.2 r s

omit [IsLocallyNoetherian X] [IsNoetherianRing Γ(X, U)] in
/-- **The stalk of a term at a point of `U` is the localization of its sections over `U`.** -/
theorem isLocalizedModule_affineOpenSectionGerm (n : ℕ) :
    IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl (affineOpenSectionGerm F x n) := by
  have : (F.obj.obj (op n)).IsQuasicoherent := F.property.isQuasicoherent n
  refine ⟨fun a => ?_, fun m => ?_, fun {s t} h => ?_⟩
  · have hu := Stacks.ModuleStalkSpecialization.isUnit_smul_stalk (F.obj.obj (op n)) hU x.2 a
    exact hu
  · obtain ⟨s, c, hc, hcm⟩ :=
      Stacks.ModuleStalkSpecialization.exists_germ_smul_eq_germ (F.obj.obj (op n)) hU x.2 m
    exact ⟨⟨s, ⟨c, hc⟩⟩, hcm⟩
  · obtain ⟨c, hc, hct⟩ :=
      Stacks.ModuleStalkSpecialization.exists_smul_eq_of_germ_eq (F.obj.obj (op n)) hU x.2 s t h
    exact ⟨⟨c, hc⟩, hct⟩

/-- The level map `L ⧸ I₀ⁿ⁺¹L → M_𝔮 ⧸ I₀ⁿ⁺¹M_𝔮`, a localization at the prime of `x`. -/
abbrev affineOpenCompletedLevelMap (n : ℕ) :=
  haveI := isLocalization_atPrime_affineOpenCompletedPrime I hU x hIx q hq
  haveI := isLocalizedModule_atPrime_affineOpenCompletedPrime hU x hIx q hq (L := L)
  levelLocalizationMapCompletion (I.ideal ⟨U, hU⟩) (Ideal.fg_of_isNoetherianRing _) hIx
    (Localization.AtPrime q.asIdeal)
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl
      (AdicCompletion (I.ideal ⟨U, hU⟩) L)) (n + 1)

/-- The stalk of the `n`-th term identified with the level `n + 1` of `M_𝔮`: both are
localizations of `L ⧸ I₀ⁿ⁺¹L ≅ Γ(U, ℱₙ)` at the prime of `x`. -/
def affineOpenStalkLevelEquiv (n : ℕ) :
    affineOpenStalkLevel F x n ≃ₗ[Γ(X, U)]
      (affineOpenLocalizedCompletion hU q (L := L) ⧸
        ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U)
          (Localization.AtPrime q.asIdeal)) ^ (n + 1) •
          (⊤ : Submodule (Localization.AtPrime q.asIdeal)
            (affineOpenLocalizedCompletion hU q (L := L))))) :=
  haveI := isLocalizedModule_affineOpenSectionGerm hU F x n
  haveI : IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl
      (affineOpenSectionGerm F x n ∘ₗ (ε n).toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right _ _ _
  IsLocalizedModule.linearEquiv (hU.primeIdealOf x).asIdeal.primeCompl
    (affineOpenSectionGerm F x n ∘ₗ (ε n).toLinearMap)
    (affineOpenCompletedLevelMap hU x hIx q hq (L := L) n)

omit [IsLocallyNoetherian X] in
/-- The completed level maps are compatible with the transition maps. -/
theorem transitionMap_affineOpenCompletedLevelMap {m n : ℕ} (h : m ≤ n)
    (z : L ⧸ (I.ideal ⟨U, hU⟩ ^ (n + 1) • (⊤ : Submodule Γ(X, U) L))) :
    AdicCompletion.transitionMap _ (affineOpenLocalizedCompletion hU q (L := L))
        (Nat.succ_le_succ h) (affineOpenCompletedLevelMap hU x hIx q hq (L := L) n z) =
      affineOpenCompletedLevelMap hU x hIx q hq (L := L) m
        (AdicCompletion.transitionMap _ L (Nat.succ_le_succ h) z) := by
  have := isLocalization_atPrime_affineOpenCompletedPrime I hU x hIx q hq
  have := isLocalizedModule_atPrime_affineOpenCompletedPrime hU x hIx q hq (L := L)
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    exact (congrArg (AdicCompletion.transitionMap _ _ (Nat.succ_le_succ h))
      (levelLocalizationMapCompletion_mk _ _ hIx _ _ (n + 1) z)).trans
      ((transitionMap_mk_eq_mk _ _ _ _).trans
        ((levelLocalizationMapCompletion_mk _ _ hIx _ _ (m + 1) z).symm.trans
          (congrArg (affineOpenCompletedLevelMap hU x hIx q hq (L := L) m)
            (transitionMap_mk_eq_mk _ L (Nat.succ_le_succ h) z).symm)))

variable (hε : ∀ {m n : ℕ} (h : m ≤ n)
  (z : L ⧸ (I.ideal ⟨U, hU⟩ ^ (n + 1) • (⊤ : Submodule Γ(X, U) L))),
  (F.obj.map (homOfLE h).op).app U (ε n z) =
    ε m (AdicCompletion.transitionMap _ L (Nat.succ_le_succ h) z))

omit [IsLocallyNoetherian X] in
include hε in
/-- **The stalk identifications are compatible with the transition maps.** -/
theorem affineOpenStalkLevelEquiv_naturality {m n : ℕ} (h : m ≤ n)
    (w : affineOpenStalkLevel F x n) :
    AdicCompletion.transitionMap _ (affineOpenLocalizedCompletion hU q (L := L))
        (Nat.succ_le_succ h) (affineOpenStalkLevelEquiv hU F ε x hIx q hq n w) =
      affineOpenStalkLevelEquiv hU F ε x hIx q hq m
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x.1).map
          (F.obj.map (homOfLE h).op)).hom w) := by
  have loc : ∀ k, IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl
      (affineOpenSectionGerm F x k ∘ₗ (ε k).toLinearMap) := fun k => by
    have := isLocalizedModule_affineOpenSectionGerm hU F x k
    exact IsLocalizedModule.of_linearEquiv_right _ _ _
  have apply_eq : ∀ (k : ℕ) z, affineOpenStalkLevelEquiv hU F ε x hIx q hq k
      (affineOpenSectionGerm F x k (ε k z)) =
        affineOpenCompletedLevelMap hU x hIx q hq (L := L) k z := fun k z => by
    have := loc k
    exact IsLocalizedModule.linearEquiv_apply _ _ _ z
  have := loc n
  let stalkMap : affineOpenStalkLevel F x n →ₗ[Γ(X, U)] affineOpenStalkLevel F x m :=
    ((ModuleCat.restrictScalars (X.presheaf.germ U x.1 x.2).hom).map
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x.1).map
        (F.obj.map (homOfLE h).op))).hom
  have key : ((AdicCompletion.transitionMap _ (affineOpenLocalizedCompletion hU q (L := L))
        (Nat.succ_le_succ h)).restrictScalars Γ(X, U)) ∘ₗ
        (affineOpenStalkLevelEquiv hU F ε x hIx q hq n).toLinearMap =
      (affineOpenStalkLevelEquiv hU F ε x hIx q hq m).toLinearMap ∘ₗ stalkMap := by
    refine IsLocalizedModule.linearMap_ext (hU.primeIdealOf x).asIdeal.primeCompl
      (affineOpenSectionGerm F x n ∘ₗ (ε n).toLinearMap)
      (affineOpenCompletedLevelMap hU x hIx q hq (L := L) m) ?_
    refine LinearMap.ext fun z => ?_
    have h2 : stalkMap (affineOpenSectionGerm F x n (ε n z)) =
        affineOpenSectionGerm F x m (ε m (AdicCompletion.transitionMap _ L
          (Nat.succ_le_succ h) z)) :=
      (modulesStalkFunctor_map_germ (F.obj.map (homOfLE h).op) x.1 U x.2 (ε n z)).trans
        (congrArg ((F.obj.obj (op m)).presheaf.germ U x.1 x.2).hom (hε h z))
    exact (congrArg (AdicCompletion.transitionMap _ _ (Nat.succ_le_succ h)) (apply_eq n z)).trans
      ((transitionMap_affineOpenCompletedLevelMap hU x hIx q hq h z).trans
        ((apply_eq m _).symm.trans
          (congrArg (affineOpenStalkLevelEquiv hU F ε x hIx q hq m) h2.symm)))
  exact LinearMap.congr_fun key w

variable [Module Γ(X, U) (formalStalk F x.1)]
  [IsScalarTower Γ(X, U) (X.presheaf.stalk x.1) (formalStalk F x.1)]

/-- The level identification of the formal stalk with the stalk of a term, as a
`Γ(X, U)`-linear equivalence. -/
def formalStalkAffineLevelEquiv (n : ℕ) :
    (formalStalk F x.1 ⧸ (IdealSheafData.stalk I x.1 ^ (n + 1) •
        (⊤ : Submodule (X.presheaf.stalk x.1) (formalStalk F x.1)))) ≃ₗ[Γ(X, U)]
      affineOpenStalkLevel F x n where
  toFun z := formalStalkQuotientEquivStalk F x.1 n z
  invFun w := (formalStalkQuotientEquivStalk F x.1 n).symm w
  map_add' _ _ := map_add _ _ _
  map_smul' a z := by
    rw [RingHom.id_apply, ← algebraMap_smul (X.presheaf.stalk x.1) a z, map_smul]
    rfl
  left_inv z := LinearEquiv.symm_apply_apply _ z
  right_inv w := LinearEquiv.apply_symm_apply _ w

/-- **The levels of the completed stalk are the levels of `M_𝔮`**, `Γ(X, U)`-linearly. -/
def completedStalkAffineOpenLevelEquiv : ∀ n : ℕ,
    (formalStalk F x.1 ⧸ (IdealSheafData.stalk I x.1 ^ n •
        (⊤ : Submodule (X.presheaf.stalk x.1) (formalStalk F x.1)))) ≃ₗ[Γ(X, U)]
      (affineOpenLocalizedCompletion hU q (L := L) ⧸
        ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U)
          (Localization.AtPrime q.asIdeal)) ^ n •
          (⊤ : Submodule (Localization.AtPrime q.asIdeal)
            (affineOpenLocalizedCompletion hU q (L := L)))))
  | 0 =>
    haveI := subsingleton_quotient_idealPow_zero_smul_top (IdealSheafData.stalk I x.1)
      (formalStalk F x.1)
    haveI := subsingleton_quotient_idealPow_zero_smul_top
      ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U)
        (Localization.AtPrime q.asIdeal)))
      (affineOpenLocalizedCompletion hU q (L := L))
    LinearEquiv.ofSubsingleton _ _
  | n + 1 =>
    (formalStalkAffineLevelEquiv F x n).trans (affineOpenStalkLevelEquiv hU F ε x hIx q hq n)

include hε in
/-- The level identifications are compatible with the transition maps. -/
theorem completedStalkAffineOpenLevelEquiv_transitionMap {m n : ℕ} (h : m ≤ n)
    (z : formalStalk F x.1 ⧸ (IdealSheafData.stalk I x.1 ^ n •
        (⊤ : Submodule (X.presheaf.stalk x.1) (formalStalk F x.1)))) :
    AdicCompletion.transitionMap _ (affineOpenLocalizedCompletion hU q (L := L)) h
        ((completedStalkAffineOpenLevelEquiv hU F ε x hIx q hq n).toAddEquiv z) =
      (completedStalkAffineOpenLevelEquiv hU F ε x hIx q hq m).toAddEquiv
        (AdicCompletion.transitionMap _ _ h z) := by
  rcases m with _ | m
  · have := subsingleton_quotient_idealPow_zero_smul_top
      ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U)
        (Localization.AtPrime q.asIdeal)))
      (affineOpenLocalizedCompletion hU q (L := L))
    exact Subsingleton.elim _ _
  rcases n with _ | n
  · omega
  have h' : m ≤ n := Nat.le_of_succ_le_succ h
  show AdicCompletion.transitionMap _ _ (Nat.succ_le_succ h')
      (affineOpenStalkLevelEquiv hU F ε x hIx q hq n (formalStalkAffineLevelEquiv F x n z)) =
    affineOpenStalkLevelEquiv hU F ε x hIx q hq m (formalStalkAffineLevelEquiv F x m
      (AdicCompletion.transitionMap _ _ (Nat.succ_le_succ h') z))
  rw [affineOpenStalkLevelEquiv_naturality hU F ε x hIx q hq hε h']
  exact congrArg (affineOpenStalkLevelEquiv hU F ε x hIx q hq m)
    (formalStalkQuotientEquivStalk_transitionMap F x.1 h' z).symm

include hε in
/-- **The completed stalk at a point of an affine open is the completion of `M_𝔮`**, as an
additive equivalence assembled from the `Γ(X, U)`-linear identifications of the levels. -/
def completedStalkAffineOpenAddEquiv :
    completedStalk I F x.1 ≃+
      AdicCompletion ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U)
          (Localization.AtPrime q.asIdeal)))
        (affineOpenLocalizedCompletion hU q (L := L)) :=
  AdicCompletion.addEquivOfQuotientEquiv _ _
    (fun n => (completedStalkAffineOpenLevelEquiv hU F ε x hIx q hq n).toAddEquiv)
    (fun h z => completedStalkAffineOpenLevelEquiv_transitionMap hU F ε x hIx q hq hε h z)

include hε in
/-- **The comparison of completed stalks lies over the comparison of completed local rings.** -/
theorem completedStalkAffineOpenAddEquiv_smul (r : completedLocalRing I x.1)
    (z : completedStalk I F x.1) :
    completedStalkAffineOpenAddEquiv hU F ε x hIx q hq hε (r • z) =
      completedLocalRingAffineOpenAlgEquiv I hU x hIx q hq r •
        completedStalkAffineOpenAddEquiv hU F ε x hIx q hq hε z := by
  have := hU.isLocalization_stalk x
  have := isLocalization_atPrime_affineOpenCompletedPrime I hU x hIx q hq
  refine AdicCompletion.addEquivOfQuotientEquiv_smul_of_levels _ _
    (completedStalkAffineOpenLevelEquiv hU F ε x hIx q hq)
    (fun h z => completedStalkAffineOpenLevelEquiv_transitionMap hU F ε x hIx q hq hε h z)
    (completedLocalRingAffineOpenAlgEquiv I hU x hIx q hq)
    (completedLocalRingAffineOpenLevel I hU x hIx q hq)
    (evalₐ_completedLocalRingAffineOpenAlgEquiv I hU x hIx q hq) (fun r => ?_) r z
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj (hU.primeIdealOf x).asIdeal.primeCompl r
  refine ⟨a, s, by rw [mul_comm]; exact has, ?_⟩
  have hs : algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) s ∈
      q.asIdeal.primeCompl := by
    intro hmem
    have h2 : (s : Γ(X, U)) ∈ (affineOpenCompletedPrime I hU x hIx).asIdeal.comap
        (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) := by
      rw [← hq]; exact hmem
    rw [comap_adicPrimeOver] at h2
    exact s.2 h2
  rw [IsScalarTower.algebraMap_apply Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
    (Localization.AtPrime q.asIdeal)]
  exact IsLocalization.map_units _ ⟨_, hs⟩

end Module

end Stacks.Algebraization

end
