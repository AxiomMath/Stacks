module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyIdealQuotientBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.FormalFunctionsAdicLimitUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageGeometricStalkCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperHigherDirectImageCoherent

/-!
# The theorem on formal functions at a geometric point

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over a scheme `S` with `Y` locally
Noetherian, let `F` be a coherent `𝒪_X`-module and let `ȳ` be a geometric point of `Y`.  Let
`A = 𝒪_{Y, ȳ}` be the étale local ring at `ȳ`, with maximal ideal `𝔪`, and consider the
infinitesimal neighbourhoods

`X_n = Spec (A / 𝔪 ⁿ) ×_Y X`

of the geometric fibre, with `F_n` the pullback of `F`.  [Stacks, Tag 08B1] says that

`(R ᵖ f_* F)_ȳ ^∧ ≅ lim_n H ᵖ (X_n, F_n)`.

The proof is the source's.  Flat base change along `Spec A ⟶ Y`
(`AlgebraicGeometry.Space.geometricStalkCohomologyLinearEquiv`) identifies the stalk with
`H ᵖ (X', F')` for `X' = Spec A ×_Y X`; the theorem on formal functions for the proper morphism
`X' ⟶ Spec A` ([Stacks, Tag 08AZ], `AlgebraicGeometry.Space.C1573.formalFunctionsEquivOfIsAffine`)
computes its `𝔪`-adic completion as `lim_n H ᵖ (X', F' / 𝔪 ⁿ F')`; and
`H ᵖ (X', F' / 𝔪 ⁿ F') = H ᵖ (X_n, F_n)` because `X_n = Spec (A / 𝔪 ⁿ) ×_{Spec A} X'`
(`AlgebraicGeometry.Space.cohomologyIdealQuotientBaseChangeEquiv`).

## Main definitions

* `Stacks.AdicTowerComparison.CompletionIsoLimitOfQuotientsOverCompletion`: the maps
  `ρ n : M ⟶ P n` assemble into an isomorphism `M ^∧ ≅ lim_n P n` of `A ^∧`-modules.
* `AlgebraicGeometry.Space.geometricInfinitesimalNeighbourhood`: `X_n = Spec (A / 𝔪 ⁿ) ×_Y X`.
* `AlgebraicGeometry.Space.geometricInfinitesimalNeighbourhoodModule`: `F_n`.
* `AlgebraicGeometry.Space.geometricInfinitesimalNeighbourhoodCohomology`: `H ᵖ (X_n, F_n)`.
* `AlgebraicGeometry.Space.geometricInfinitesimalNeighbourhoodTransition` and
  `AlgebraicGeometry.Space.geometricInfinitesimalNeighbourhoodProj`: the maps
  `H ᵖ (X_n, F_n) ⟶ H ᵖ (X_m, F_m)` for `m ≤ n` and `(R ᵖ f_* F)_ȳ ⟶ H ᵖ (X_n, F_n)`.

## Main results

* `AlgebraicGeometry.Space.completionIsoLimitOfQuotientsOverCompletion_geometricStalk`:
  **[Stacks, Tag 08B1]**, the isomorphism `(R ᵖ f_* F)_ȳ ^∧ ≅ lim_n H ᵖ (X_n, F_n)` of modules
  over the completion of the étale local ring.
* `AlgebraicGeometry.Space.completionIsoLimitOfQuotients_geometricStalk`: the same, as the
  property `Stacks.AdicTowerComparison.CompletionIsoLimitOfQuotients` of the tower.
* `Stacks.AdicTowerComparison.towerLimitAdicSMul`: the action of `A ^∧` on the limit of a tower
  whose `n`-th term is killed by `I ⁿ`.
* `AlgebraicGeometry.Space.isPullback_geometricInfinitesimalNeighbourhood`: `X_n` is the fibre
  product of `f` and `Spec (𝒪_{Y, ȳ} / 𝔪 ⁿ) ⟶ Y`.
* `Stacks.AdicTowerComparison.CompletionIsoLimitOfQuotients.of_linearEquiv_of_towerEquiv`: the
  property transports along isomorphisms of the module and of the tower.

## Implementation notes

The étale local ring `𝒪_{Y, ȳ}` is a colimit over a category living in `Type (u + 1)`; its
spectrum is formed through the model of it in `Type u`
(`AlgebraicGeometry.Space.etaleLocalRingModel`, [Stacks, Tag 04KF]), as the object
`AlgebraicGeometry.Space.etaleLocalRingSpecObject` of the site.  All modules are taken over the
ring `R = Γ(Spec 𝒪_{Y, ȳ}, 𝒪)` of its functions, which is identified with `𝒪_{Y, ȳ}` by
`AlgebraicGeometry.Space.etaleLocalRingSpecFunctionsEquiv`; the stalk `(R ᵖ f_* F)_ȳ` is an
`R`-module through that identification, and `R` is a Noetherian local ring whose completion is
`𝒪_{Y, ȳ} ^∧`.  The neighbourhood `X_n` is formed as `Spec (R / 𝔪 ⁿ) ×_{Spec R} X'`.

The transition map `H ᵖ (X_n, F_n) ⟶ H ᵖ (X_m, F_m)` is the one induced by `F' / 𝔪 ⁿ F' ⟶
F' / 𝔪 ᵐ F'` under the identifications `H ᵖ (X_k, F_k) = H ᵖ (X', F' / 𝔪 ᵏ F')`, which is how the
source's proof reads the limit.

## References

* [Stacks Project, Tag 08B1](https://stacks.math.columbia.edu/tag/08B1)
* [Stacks Project, Tag 08AZ](https://stacks.math.columbia.edu/tag/08AZ)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.AdicTowerComparison Stacks.IntertwinedFiltration

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace Stacks.AdicTowerComparison

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- **The property transports along an isomorphism of the module being completed.**  If the maps
`ρ n : N ⟶ Q n` assemble into an isomorphism `N ^∧_I ≅ lim_n Q n` and `Φ : N ≅ M`, then the maps
`ρ n ∘ Φ⁻¹ : M ⟶ Q n` assemble into an isomorphism `M ^∧_I ≅ lim_n Q n`. -/
theorem CompletionIsoLimitOfQuotients.of_linearEquiv {I : Ideal A} {N : Type*} [AddCommGroup N]
    [Module A N] {Q : ℕ → Type*} [∀ n, AddCommGroup (Q n)] [∀ n, Module A (Q n)]
    {U : ∀ m n : ℕ, m ≤ n → Q n →ₗ[A] Q m} {ρ : ∀ n, N →ₗ[A] Q n}
    (h : CompletionIsoLimitOfQuotients I N Q U ρ) (Φ : N ≃ₗ[A] M) :
    CompletionIsoLimitOfQuotients I M Q U (fun n => ρ n ∘ₗ Φ.symm.toLinearMap) := by
  obtain ⟨e, he⟩ := h
  refine ⟨((AdicCompletion.congr I Φ.symm).restrictScalars A).trans e, fun n x => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, AdicCompletion.congr_apply,
    AdicCompletion.map_of, he]
  rfl

/-- **The property transports along isomorphisms of the module and of the tower.**  If the maps
`ρ n : N ⟶ Q n` assemble into an isomorphism `N ^∧_I ≅ lim_n Q n`, then for `Φ : N ≅ M` and
`e n : Q n ≅ P n` the maps `e n ∘ ρ n ∘ Φ⁻¹` assemble into an isomorphism
`M ^∧_I ≅ lim_n P n`, the tower `P` carrying the transported transition maps. -/
theorem CompletionIsoLimitOfQuotients.of_linearEquiv_of_towerEquiv {I : Ideal A} {N : Type*}
    [AddCommGroup N] [Module A N] {Q : ℕ → Type*} [∀ n, AddCommGroup (Q n)] [∀ n, Module A (Q n)]
    {P : ℕ → Type*} [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
    {U : ∀ m n : ℕ, m ≤ n → Q n →ₗ[A] Q m} {ρ : ∀ n, N →ₗ[A] Q n}
    (h : CompletionIsoLimitOfQuotients I N Q U ρ) (Φ : N ≃ₗ[A] M) (e : ∀ n, Q n ≃ₗ[A] P n) :
    CompletionIsoLimitOfQuotients I M P
      (fun m n h => (e m).toLinearMap ∘ₗ U m n h ∘ₗ (e n).symm.toLinearMap)
      (fun n => (e n).toLinearMap ∘ₗ ρ n ∘ₗ Φ.symm.toLinearMap) :=
  (h.of_linearEquiv Φ).of_towerIso e (fun m n h x => by simp) (fun n x => rfl)

/-! ### The action of the completion on a limit of a tower -/

section AdicSMul

variable {I : Ideal A} {P : ℕ → Type*} [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  {T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m}

/-- The action of `A ⧸ I ⁿ` on an element `x` of a module killed by `I ⁿ`. -/
def quotientSMulOfAnnihilated (n : ℕ) (hann : ∀ a ∈ I ^ n, ∀ x : P n, a • x = 0) (x : P n) :
    A ⧸ (I ^ n • ⊤ : Submodule A A) →ₗ[A] P n :=
  Submodule.liftQ _ (LinearMap.toSpanSingleton A (P n) x) fun a ha => by
    simpa using hann a (by simpa [smul_eq_mul, Ideal.mul_top] using ha) x

/-- The action of `A ⧸ I ⁿ` on `x` sends the class of `a` to `a • x`. -/
@[simp]
theorem quotientSMulOfAnnihilated_mk (n : ℕ) (hann : ∀ a ∈ I ^ n, ∀ x : P n, a • x = 0)
    (x : P n) (a : A) :
    quotientSMulOfAnnihilated n hann x (Submodule.Quotient.mk a) = a • x :=
  rfl

/-- **The action of the completion `A ^∧ = lim_n A ⧸ I ⁿ` on the limit of a tower whose `n`-th
term is killed by `I ⁿ`**: an element `α = (α_n)_n` acts on the `n`-th component through
`α_n ∈ A ⧸ I ⁿ`. -/
def towerLimitAdicSMul (hann : ∀ n, ∀ a ∈ I ^ n, ∀ x : P n, a • x = 0) (α : AdicCompletion I A)
    (x : towerLimit P T) : towerLimit P T :=
  ⟨fun n => quotientSMulOfAnnihilated n (hann n) ((x : ∀ k, P k) n)
    (AdicCompletion.eval I A n α), by
    intro m n h
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I A n α)
    have hm : AdicCompletion.eval I A m α = Submodule.Quotient.mk a := by
      rw [AdicCompletion.eval_apply] at ha
      rw [AdicCompletion.eval_apply, ← AdicCompletion.transitionMap_comp_eval_apply I A h α, ← ha]
      rfl
    change T m n h (quotientSMulOfAnnihilated n (hann n) ((x : ∀ k, P k) n)
      (AdicCompletion.eval I A n α)) = quotientSMulOfAnnihilated m (hann m) ((x : ∀ k, P k) m)
      (AdicCompletion.eval I A m α)
    rw [← ha, hm, quotientSMulOfAnnihilated_mk, quotientSMulOfAnnihilated_mk, map_smul,
      towerLimit_compat x m n h]⟩

/-- The `n`-th component of `α • x` is the action of the `n`-th component of `α`, an element of
`A ⧸ I ⁿ`, on the `n`-th component of `x`. -/
theorem towerLimit_proj_towerLimitAdicSMul (hann : ∀ n, ∀ a ∈ I ^ n, ∀ x : P n, a • x = 0)
    (α : AdicCompletion I A) (x : towerLimit P T) (n : ℕ) :
    towerLimit.proj n (towerLimitAdicSMul hann α x) =
      quotientSMulOfAnnihilated n (hann n) (towerLimit.proj n x) (AdicCompletion.eval I A n α) :=
  rfl

/-- A linear map `M ^∧ ⟶ lim_n P n` induced levelwise by maps `M ⧸ I ⁿ M ⟶ P n` is linear over
the completion `A ^∧`. -/
theorem map_adicSMul_of_levelwise (hann : ∀ n, ∀ a ∈ I ^ n, ∀ x : P n, a • x = 0)
    (e : AdicCompletion I M →ₗ[A] towerLimit P T)
    (g : ∀ n, M ⧸ (I ^ n • ⊤ : Submodule A M) →ₗ[A] P n)
    (he : ∀ w n, towerLimit.proj n (e w) = g n (w.val n)) (α : AdicCompletion I A)
    (w : AdicCompletion I M) : e (α • w) = towerLimitAdicSMul hann α (e w) := by
  refine Subtype.ext (funext fun n => ?_)
  change towerLimit.proj n (e (α • w)) = towerLimit.proj n (towerLimitAdicSMul hann α (e w))
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I A n α)
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (w.val n)
  rw [towerLimit_proj_towerLimitAdicSMul, he, he, AdicCompletion.smul_eval, ← hy,
    ← AdicCompletion.eval_apply, ← ha, quotientSMulOfAnnihilated_mk, ← map_smul]
  rfl

/-- **The maps `ρ n : M ⟶ P n` assemble into an isomorphism `M ^∧_I ≅ lim_n P n` of
`A ^∧`-modules**, the completion `A ^∧` acting on the limit through `A ^∧ ⟶ A ⧸ I ⁿ`
(`Stacks.AdicTowerComparison.towerLimitAdicSMul`).  This strengthens
`Stacks.AdicTowerComparison.CompletionIsoLimitOfQuotients` by the linearity over `A ^∧`. -/
def CompletionIsoLimitOfQuotientsOverCompletion (I : Ideal A) (M : Type*) [AddCommGroup M]
    [Module A M] (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
    (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m) (ρ : ∀ n, M →ₗ[A] P n)
    (hann : ∀ n, ∀ a ∈ I ^ n, ∀ x : P n, a • x = 0) : Prop :=
  ∃ e : AdicCompletion I M ≃ₗ[A] towerLimit P T,
    (∀ (n : ℕ) (x : M), towerLimit.proj n (e (AdicCompletion.of I M x)) = ρ n x) ∧
      ∀ (α : AdicCompletion I A) (w : AdicCompletion I M),
        e (α • w) = towerLimitAdicSMul hann α (e w)

/-- An isomorphism `M ^∧_I ≅ lim_n P n` linear over `A ^∧` is in particular one of `A`-modules:
the property `Stacks.AdicTowerComparison.CompletionIsoLimitOfQuotients` forgets the linearity
over the completion. -/
theorem CompletionIsoLimitOfQuotientsOverCompletion.completionIsoLimitOfQuotients {I : Ideal A}
    {T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m} {ρ : ∀ n, M →ₗ[A] P n}
    {hann : ∀ n, ∀ a ∈ I ^ n, ∀ x : P n, a • x = 0}
    (h : CompletionIsoLimitOfQuotientsOverCompletion I M P T ρ hann) :
    CompletionIsoLimitOfQuotients I M P T ρ :=
  let ⟨e, he, _⟩ := h
  ⟨e, he⟩

/-- **The theorem on formal functions with its `A ^∧`-module structure, transported.**  Let
`E : N ^∧ ≅ lim_n Q n` be induced levelwise by `ρ n : N ⟶ Q n`, let `Φ : N ≅ M` and
`e n : Q n ≅ P n`, the `P n` being killed by `I ⁿ`.  Then the maps `e n ∘ ρ n ∘ Φ⁻¹` assemble into
an isomorphism `M ^∧ ≅ lim_n P n` which is linear over `A ^∧`. -/
theorem completionIsoLimitOfQuotientsOverCompletion_of_linearEquiv {N : Type*} [AddCommGroup N]
    [Module A N] {Q : ℕ → Type*} [∀ n, AddCommGroup (Q n)] [∀ n, Module A (Q n)]
    {U : ∀ m n : ℕ, m ≤ n → Q n →ₗ[A] Q m} (ρ : ∀ n, N →ₗ[A] Q n)
    (hker : ∀ n, I ^ n • (⊤ : Submodule A N) ≤ LinearMap.ker (ρ n))
    (E : AdicCompletion I N ≃ₗ[A] towerLimit Q U)
    (hE : ∀ w n, ((E w : towerLimit Q U) : ∀ k, Q k) n =
      Stacks.IntertwinedFiltration.C1573.adicQuotientMap Q ρ I hker n (w.val n))
    (Φ : N ≃ₗ[A] M) (e : ∀ n, Q n ≃ₗ[A] P n) (hann : ∀ n, ∀ a ∈ I ^ n, ∀ x : P n, a • x = 0) :
    CompletionIsoLimitOfQuotientsOverCompletion I M P
      (fun m n h => (e m).toLinearMap ∘ₗ U m n h ∘ₗ (e n).symm.toLinearMap)
      (fun n => (e n).toLinearMap ∘ₗ ρ n ∘ₗ Φ.symm.toLinearMap) hann := by
  let e' := ((AdicCompletion.congr I Φ.symm).restrictScalars A).trans
    (E.trans (towerLimitCongr Q P U
      (fun m n h => (e m).toLinearMap ∘ₗ U m n h ∘ₗ (e n).symm.toLinearMap) e
      (fun m n h x => by simp)))
  have hlev : ∀ (w : AdicCompletion I M) (n : ℕ), towerLimit.proj n (e' w) =
      ((e n).toLinearMap ∘ₗ Stacks.IntertwinedFiltration.C1573.adicQuotientMap Q ρ I hker n ∘ₗ
        LinearMap.reduceModIdeal (I ^ n) Φ.symm.toLinearMap) (w.val n) := by
    intro w n
    change e n (((E (AdicCompletion.map I Φ.symm.toLinearMap w) : towerLimit Q U) :
      ∀ k, Q k) n) = _
    rw [hE, AdicCompletion.map_val_apply]
    rfl
  refine ⟨e', fun n x => ?_, map_adicSMul_of_levelwise hann e'.toLinearMap _ hlev⟩
  rw [hlev]
  rfl

end AdicSMul

end Stacks.AdicTowerComparison

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y) (y : GeometricPoint B S hS Y.1)
  (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))

/-! ### The ring of functions on `Spec 𝒪_{Y, ȳ}` -/

/-- The ring `R = Γ(Spec 𝒪_{Y, ȳ}, 𝒪)` is local, being isomorphic to the étale local ring
`𝒪_{Y, ȳ}`. -/
instance isLocalRing_etaleLocalRingSpecFunctions :
    IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj (etaleLocalRingSpecObject (y := y) hY), ⊤) :=
  have := isLocalRing_etaleLocalRing B S hS Y.1 Y.2 y
  have : Nontrivial Γ((BigFppfOver.toScheme B S hS).obj
      (etaleLocalRingSpecObject (y := y) hY), ⊤) :=
    (etaleLocalRingSpecFunctionsEquiv y hY).toEquiv.nontrivial
  IsLocalRing.of_surjective' (etaleLocalRingSpecFunctionsEquiv y hY).symm.toRingHom
    (etaleLocalRingSpecFunctionsEquiv y hY).symm.surjective

/-- The ring `R = Γ(Spec 𝒪_{Y, ȳ}, 𝒪)` is Noetherian, being isomorphic to the étale local ring
`𝒪_{Y, ȳ}` of the locally Noetherian `Y`. -/
theorem isNoetherianRing_etaleLocalRingSpecFunctions :
    IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj
      (etaleLocalRingSpecObject (y := y) hY), ⊤) :=
  have := isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS Y.1 Y.2 hY y
  isNoetherianRing_of_ringEquiv _ (etaleLocalRingSpecFunctionsEquiv y hY).symm

/-! ### The base change `X' = Spec 𝒪_{Y, ȳ} ×_Y X` -/

/-- The projection `X' = Spec 𝒪_{Y, ȳ} ×_Y X ⟶ Spec 𝒪_{Y, ȳ}`. -/
abbrev geometricBaseChangeFst :
    geometricBaseChange f y hY ⟶ schemeSpace (etaleLocalRingSpecObject (y := y) hY) :=
  pullback.fst (schemeSpaceMap (etaleLocalRingSpecToChart (y := y) hY))
    (geometricChartProjection f y)

variable {f}

/-- The projection `U₀ ×_Y X ⟶ U₀` over the chosen affine neighbourhood `U₀` of `ȳ` is proper, as
a base change of `f`. -/
theorem isProper_geometricChartProjection (hf : IsProper B S hS f.hom) :
    IsProper B S hS (geometricChartProjection f y).hom :=
  isProper_of_isPullback B S hS
    (chartBaseChangeSpace B S hS f (affineEtaleNeighborhood Y y).chart).2
    X.2 (isAlgebraicSpace_yoneda B S hS _) Y.2
    (isPullback_chartBaseChangeProjection B S hS f (affineEtaleNeighborhood Y y).chart).flip hf

/-- `X' ⟶ Spec 𝒪_{Y, ȳ}` is proper, as a base change of `f`. -/
theorem isProper_geometricBaseChangeFst (hf : IsProper B S hS f.hom) :
    IsProper B S hS (geometricBaseChangeFst f y hY).hom :=
  isProper_of_isPullback B S hS (geometricBaseChange f y hY).2
    (chartBaseChangeSpace B S hS f (affineEtaleNeighborhood Y y).chart).2
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
    (AlgebraicSpaces.isPullback_hom _ _ _ (IsPullback.of_hasPullback
      (schemeSpaceMap (etaleLocalRingSpecToChart (y := y) hY)) (geometricChartProjection f y))).flip
    (isProper_geometricChartProjection y hf)

/-- The source of a morphism locally of finite type to a locally Noetherian scheme has the
locally Noetherian étale local property, as a `Fact` for the pullback of coherent modules. -/
private theorem fact_hasEtaleLocalProperty_isLocallyNoetherian {Z : AlgebraicSpaces B S hS}
    {W : BigFppfOver B S hS} [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W)]
    (g : Z ⟶ schemeSpace W) (hg : IsLocallyOfFiniteType B S hS g.hom) :
    Fact (HasEtaleLocalProperty B S hS Z.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) :=
  ⟨isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Z.2 (isAlgebraicSpace_yoneda B S hS W)
    g.hom hg (hasEtaleLocalProperty_of_representable B S hS _ _ _ (Iso.refl _) inferInstance)⟩

/-- The pullback `F'` of a coherent module to `X' = Spec 𝒪_{Y, ȳ} ×_Y X` is coherent. -/
theorem isCoherent_geometricBaseChangeModule (hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) :
    IsCoherent B S hS _ _ (geometricBaseChangeModule f y hY F) := by
  let V := (affineEtaleNeighborhood Y y).chart
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj V)) := isLocallyNoetherian_chart B S hS hY V
  have := fact_hasEtaleLocalProperty_isLocallyNoetherian
    (W := (SmallEtale.toOver B S hS Y.1).obj V) (chartBaseChangeProjection B S hS f V)
    (isProper_geometricChartProjection y hf).2.1.1
  have hG : IsCoherent B S hS _ _ ((chartBaseChangeModulePullback B S hS f V).obj F) :=
    isCoherent_of_iso B S hS _
      ((modulePullbackIsoEtaleModulePullback B S hS (chartBaseChangeInclusion B S hS f V)
        (isEtale_chartBaseChangeInclusion B S hS f V)).app F)
      (isCoherent_modulePullback B S hS (chartBaseChangeInclusion B S hS f V) F hF)
  have := isNoetherianRing_etaleLocalRingModel (y := y) hY
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
      (etaleLocalRingSpecObject (y := y) hY)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec _))
  have := fact_hasEtaleLocalProperty_isLocallyNoetherian (geometricBaseChangeFst f y hY)
    (isProper_geometricBaseChangeFst y hY hf).2.1.1
  exact isCoherent_modulePullback B S hS _ _ hG

/-- The pullback `F'` of a quasi-coherent module to `X' = Spec 𝒪_{Y, ȳ} ×_Y X` is
quasi-coherent. -/
theorem isQuasicoherentOnSite_geometricBaseChangeModule (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    (geometricBaseChangeModule f y hY F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
    (isQuasicoherentOnSite_etaleModulePullback B S hS
      (chartBaseChangeInclusion B S hS f (affineEtaleNeighborhood Y y).chart)
      (isEtale_chartBaseChangeInclusion B S hS f (affineEtaleNeighborhood Y y).chart) F hF)

/-! ### The infinitesimal neighbourhoods `X_n` -/

variable (f)

/-- **The `n`-th infinitesimal neighbourhood `X_n = Spec (𝒪_{Y, ȳ} / 𝔪 ⁿ) ×_Y X`** of the
geometric fibre, formed as `Spec (R / 𝔪 ⁿ) ×_{Spec R} X'` with `R = Γ(Spec 𝒪_{Y, ȳ}, 𝒪)`. -/
abbrev geometricInfinitesimalNeighbourhood (n : ℕ) : AlgebraicSpaces B S hS :=
  idealQuotientBaseChange B S hS (maximalIdeal Γ((BigFppfOver.toScheme B S hS).obj
    (etaleLocalRingSpecObject (y := y) hY), ⊤) ^ n) (geometricBaseChangeFst f y hY)

/-- The pullback `F_n` of `F` to the infinitesimal neighbourhood `X_n`. -/
abbrev geometricInfinitesimalNeighbourhoodModule (F : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    Modules.{u, u} B S hS (geometricInfinitesimalNeighbourhood f y hY n).1
      (geometricInfinitesimalNeighbourhood f y hY n).2 :=
  idealQuotientBaseChangeModule B S hS _ (geometricBaseChangeFst f y hY)
    (geometricBaseChangeModule f y hY F)

/-- **`X_n` is the fibre product `Spec (𝒪_{Y, ȳ} / 𝔪 ⁿ) ×_Y X`**: the square formed by
`X_n ⟶ X`, `X_n ⟶ Spec (R / 𝔪 ⁿ)`, `f` and the composite `c_n : Spec (R / 𝔪 ⁿ) ⟶ Spec R ⟶ U₀ ⟶ Y`
is cartesian. -/
theorem isPullback_geometricInfinitesimalNeighbourhood (n : ℕ) :
    IsPullback
      (pullback.snd (schemeSpaceMap (idealQuotientSpecMap B S hS
          (maximalIdeal Γ((BigFppfOver.toScheme B S hS).obj
            (etaleLocalRingSpecObject (y := y) hY), ⊤) ^ n))) (geometricBaseChangeFst f y hY) ≫
        pullback.snd (schemeSpaceMap (etaleLocalRingSpecToChart (y := y) hY))
          (geometricChartProjection f y) ≫
        chartBaseChangeInclusion B S hS f (affineEtaleNeighborhood Y y).chart)
      (pullback.fst (schemeSpaceMap (idealQuotientSpecMap B S hS
          (maximalIdeal Γ((BigFppfOver.toScheme B S hS).obj
            (etaleLocalRingSpecObject (y := y) hY), ⊤) ^ n))) (geometricBaseChangeFst f y hY))
      f
      (schemeSpaceMap (idealQuotientSpecMap B S hS (maximalIdeal Γ((BigFppfOver.toScheme
          B S hS).obj (etaleLocalRingSpecObject (y := y) hY), ⊤) ^ n)) ≫
        schemeSpaceMap (etaleLocalRingSpecToChart (y := y) hY) ≫
        chartToSpace B S hS Y (affineEtaleNeighborhood Y y).chart) :=
  (IsPullback.of_hasPullback _ _).flip.paste_horiz ((IsPullback.of_hasPullback _ _).flip.paste_horiz
    (isPullback_chartBaseChangeInclusion B S hS f (affineEtaleNeighborhood Y y).chart))

/-- `H ᵖ (X_n, F_n)`, as a module over `R = Γ(Spec 𝒪_{Y, ȳ}, 𝒪)` acting through
`X_n ⟶ Spec (R / 𝔪 ⁿ)`. -/
abbrev geometricInfinitesimalNeighbourhoodCohomology (F : Modules.{u, u} B S hS X.1 X.2) (p n : ℕ) :
    ModuleCat.{u + 1} Γ((BigFppfOver.toScheme B S hS).obj
      (etaleLocalRingSpecObject (y := y) hY), ⊤) :=
  cohomologyRes (idealQuotientBaseChangeRingHom B S hS _ (geometricBaseChangeFst f y hY)) p
    (geometricInfinitesimalNeighbourhoodModule f y hY F n)

/-- `H ᵖ (X', F' / 𝔪 ⁿ F') ≅ H ᵖ (X_n, F_n)`. -/
def geometricInfinitesimalNeighbourhoodCohomologyEquiv (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (p n : ℕ) :
    C1573.cohomologyIdealQuotient
        (baseFunctionsToGlobalSections B S hS (geometricBaseChangeFst f y hY))
        (geometricBaseChangeModule f y hY F) (maximalIdeal _) p n ≃ₗ[Γ((BigFppfOver.toScheme
          B S hS).obj (etaleLocalRingSpecObject (y := y) hY), ⊤)]
      geometricInfinitesimalNeighbourhoodCohomology f y hY F p n :=
  cohomologyIdealQuotientBaseChangeEquiv B S hS _ (geometricBaseChangeFst f y hY)
    (geometricBaseChangeModule f y hY F) (isQuasicoherentOnSite_geometricBaseChangeModule y hY F hF)
    p

/-- The transition map `H ᵖ (X_n, F_n) ⟶ H ᵖ (X_m, F_m)` for `m ≤ n`, induced by
`F' / 𝔪 ⁿ F' ⟶ F' / 𝔪 ᵐ F'`. -/
def geometricInfinitesimalNeighbourhoodTransition (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (p : ℕ) (m n : ℕ) (h : m ≤ n) :
    geometricInfinitesimalNeighbourhoodCohomology f y hY F p n →ₗ[Γ((BigFppfOver.toScheme
      B S hS).obj (etaleLocalRingSpecObject (y := y) hY), ⊤)]
      geometricInfinitesimalNeighbourhoodCohomology f y hY F p m :=
  (geometricInfinitesimalNeighbourhoodCohomologyEquiv f y hY F hF p m).toLinearMap ∘ₗ
    C1573.cohomologyIdealQuotientTr _ _ _ p h ∘ₗ
    (geometricInfinitesimalNeighbourhoodCohomologyEquiv f y hY F hF p n).symm.toLinearMap

/-- The map `(R ᵖ f_* F)_ȳ ⟶ H ᵖ (X_n, F_n)`. -/
def geometricInfinitesimalNeighbourhoodProj (hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (p n : ℕ) :
    (ModuleCat.restrictScalars (etaleLocalRingSpecFunctionsEquiv y hY).toRingHom).obj
      (geometricModuleStalk B S hS Y y (moduleHigherPushforward B S hS f F p)) →ₗ[Γ(
      (BigFppfOver.toScheme B S hS).obj (etaleLocalRingSpecObject (y := y) hY), ⊤)]
      geometricInfinitesimalNeighbourhoodCohomology f y hY F p n :=
  haveI := hF
  (geometricInfinitesimalNeighbourhoodCohomologyEquiv f y hY F hF p n).toLinearMap ∘ₗ
    C1573.cohomologyIdealQuotientProj _ _ _ p n ∘ₗ
    (geometricStalkCohomologyLinearEquiv y hY hf.2.1.2 (isQuasiSeparated_of_isSeparated B S hS hf.1)
      F p).symm.toLinearMap

/-- **The theorem on formal functions at a geometric point**, as a property of the tower: the
`R`-module isomorphism of `completionIsoLimitOfQuotientsOverCompletion_geometricStalk` (which
also records its linearity over the completion).

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with `Y` locally Noetherian, let
`F` be a coherent `𝒪_X`-module, `ȳ` a geometric point of `Y`, and let
`X_n = Spec (𝒪_{Y, ȳ} / 𝔪 ⁿ) ×_Y X` be the infinitesimal neighbourhoods of the geometric fibre,
with `F_n` the pullback of `F`.  Then the maps `(R ᵖ f_* F)_ȳ ⟶ H ᵖ (X_n, F_n)` assemble into an
isomorphism

`(R ᵖ f_* F)_ȳ ^∧ ≅ lim_n H ᵖ (X_n, F_n)`

of modules over `R = Γ(Spec 𝒪_{Y, ȳ}, 𝒪) ≅ 𝒪_{Y, ȳ}`, the completion being taken with respect
to the maximal ideal. -/
theorem completionIsoLimitOfQuotients_geometricStalk (hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) (p : ℕ) :
    CompletionIsoLimitOfQuotients (maximalIdeal Γ((BigFppfOver.toScheme B S hS).obj
        (etaleLocalRingSpecObject (y := y) hY), ⊤))
      ((ModuleCat.restrictScalars (etaleLocalRingSpecFunctionsEquiv y hY).toRingHom).obj
        (geometricModuleStalk B S hS Y y (moduleHigherPushforward B S hS f F p)))
      (fun n => geometricInfinitesimalNeighbourhoodCohomology f y hY F p n)
      (geometricInfinitesimalNeighbourhoodTransition f y hY F hF.toIsQuasicoherentOnSite p)
      (geometricInfinitesimalNeighbourhoodProj f y hY hf F hF.toIsQuasicoherentOnSite p) := by
  have := isNoetherianRing_etaleLocalRingSpecFunctions y hY
  have : IsCoherent B S hS _ _ (geometricBaseChangeModule f y hY F) :=
    isCoherent_geometricBaseChangeModule y hY hf F hF
  have h08AZ : CompletionIsoLimitOfQuotients _ _ _ _
      (C1573.cohomologyIdealQuotientProj (baseFunctionsToGlobalSections B S hS
        (geometricBaseChangeFst f y hY)) (geometricBaseChangeModule f y hY F) (maximalIdeal _) p) :=
    ⟨C1573.formalFunctionsEquivOfIsAffine (RingEquiv.refl _) (geometricBaseChangeFst f y hY)
      (isProper_geometricBaseChangeFst y hY hf) _ (fun _ => rfl) _ _ p, fun _ _ => rfl⟩
  exact h08AZ.of_linearEquiv_of_towerEquiv (geometricStalkCohomologyLinearEquiv y hY hf.2.1.2
      (isQuasiSeparated_of_isSeparated B S hS hf.1) F p)
    (geometricInfinitesimalNeighbourhoodCohomologyEquiv f y hY F hF.toIsQuasicoherentOnSite p)

/-- **`𝔪 ⁿ` kills `H ᵖ (X_n, F_n)`**, `X_n` living over `Spec (R / 𝔪 ⁿ)`. -/
theorem geometricInfinitesimalNeighbourhoodCohomology_smul_eq_zero
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (p n : ℕ)
    (a : Γ((BigFppfOver.toScheme B S hS).obj (etaleLocalRingSpecObject (y := y) hY), ⊤))
    (ha : a ∈ maximalIdeal _ ^ n) (x : geometricInfinitesimalNeighbourhoodCohomology f y hY F p n) :
    a • x = 0 := by
  rw [← (geometricInfinitesimalNeighbourhoodCohomologyEquiv f y hY F hF p n).apply_symm_apply x,
    ← map_smul]
  have h := C1573.pow_smul_top_cohomologyIdealQuotient (baseFunctionsToGlobalSections B S hS
    (geometricBaseChangeFst f y hY)) (geometricBaseChangeModule f y hY F) (maximalIdeal _) p n
  rw [(Submodule.eq_bot_iff _).1 h _ (Submodule.smul_mem_smul ha Submodule.mem_top), map_zero]

/-- **The theorem on formal functions at a geometric point, [Stacks, Tag 08B1].**

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with `Y` locally Noetherian, let
`F` be a coherent `𝒪_X`-module, `ȳ` a geometric point of `Y`, and let
`X_n = Spec (𝒪_{Y, ȳ} / 𝔪 ⁿ) ×_Y X` be the infinitesimal neighbourhoods of the geometric fibre
(`AlgebraicGeometry.Space.isPullback_geometricInfinitesimalNeighbourhood`), with `F_n` the
pullback of `F`.  Then

`(R ᵖ f_* F)_ȳ ^∧ ≅ lim_n H ᵖ (X_n, F_n)`

as modules over `𝒪_{Y, ȳ} ^∧`: there is an isomorphism of modules over
`R = Γ(Spec 𝒪_{Y, ȳ}, 𝒪) ≅ 𝒪_{Y, ȳ}` from the `𝔪`-adic completion of the stalk to the limit,
whose `n`-th component on the image of the stalk is the map `(R ᵖ f_* F)_ȳ ⟶ H ᵖ (X_n, F_n)`, and
which is linear over the completion `R ^∧`, acting on `lim_n H ᵖ (X_n, F_n)` through
`R ^∧ ⟶ R / 𝔪 ⁿ`. -/
@[stacks 08B1]
theorem completionIsoLimitOfQuotientsOverCompletion_geometricStalk (hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) (p : ℕ) :
    CompletionIsoLimitOfQuotientsOverCompletion (maximalIdeal Γ((BigFppfOver.toScheme B S hS).obj
        (etaleLocalRingSpecObject (y := y) hY), ⊤))
      ((ModuleCat.restrictScalars (etaleLocalRingSpecFunctionsEquiv y hY).toRingHom).obj
        (geometricModuleStalk B S hS Y y (moduleHigherPushforward B S hS f F p)))
      (fun n => geometricInfinitesimalNeighbourhoodCohomology f y hY F p n)
      (geometricInfinitesimalNeighbourhoodTransition f y hY F hF.toIsQuasicoherentOnSite p)
      (geometricInfinitesimalNeighbourhoodProj f y hY hf F hF.toIsQuasicoherentOnSite p)
      (geometricInfinitesimalNeighbourhoodCohomology_smul_eq_zero f y hY F
        hF.toIsQuasicoherentOnSite p) := by
  have := isNoetherianRing_etaleLocalRingSpecFunctions y hY
  have : IsCoherent B S hS _ _ (geometricBaseChangeModule f y hY F) :=
    isCoherent_geometricBaseChangeModule y hY hf F hF
  have : F.IsQuasicoherentOnSite := hF.toIsQuasicoherentOnSite
  exact completionIsoLimitOfQuotientsOverCompletion_of_linearEquiv _ _ _
    (C1573.formalFunctionsEquivOfIsAffine_apply (RingEquiv.refl _) (geometricBaseChangeFst f y hY)
      (isProper_geometricBaseChangeFst y hY hf) _ (fun _ => rfl)
      (geometricBaseChangeModule f y hY F) (maximalIdeal _) p)
    (geometricStalkCohomologyLinearEquiv y hY hf.2.1.2
      (isQuasiSeparated_of_isSeparated B S hS hf.1) F p)
    (geometricInfinitesimalNeighbourhoodCohomologyEquiv f y hY F hF.toIsQuasicoherentOnSite p) _

end AlgebraicGeometry.Space

/-! ## The theorem on formal functions over `Spec A`

[Stacks, Tag 08AY], [Stacks, Tag 08AZ] and [Stacks, Tag 08B0], in Situation 08AV, are proved in
the files `CohomologyAdicUniformBoundsSpace.lean` and `FormalFunctionsAdicLimitUnconditional.lean`
of `StacksFrontier/AlgebraicGeometry/Spaces/GrothendieckExistence/HomBijection/` (namespace
`AlgebraicGeometry.Space.C1573`), on which the geometric-point form above rests. -/

add_to_stacks 08AY "clause (1)"
  AlgebraicGeometry.Space.C1573.exists_ker_cohomologyIdealQuotientProj_le
add_to_stacks 08AY "clause (3)"
  AlgebraicGeometry.Space.C1573.exists_range_cohomologyIdealQuotientTr_eq
add_to_stacks 08AY "clause (2)"
  AlgebraicGeometry.Space.C1573.isMittagLefflerCategorical_cohomologyIdealQuotientTower
add_to_stacks 08AZ "the isomorphism of limits" AlgebraicGeometry.Space.C1573.formalFunctionsEquiv
add_to_stacks 08AZ "the isomorphism is the one defined by the system of maps"
  AlgebraicGeometry.Space.C1573.formalFunctionsEquiv_apply
add_to_stacks 08AZ "the isomorphism is a homeomorphism for the limit topologies"
  AlgebraicGeometry.Space.C1573.isHomeomorph_formalFunctionsEquiv
add_to_stacks 08B0 AlgebraicGeometry.Space.C1573.bijective_cohomologyToIdealQuotientLimit

end
