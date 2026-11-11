module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.RingTheory.AdicCompletion.IntertwinedFiltrationEventualRange

/-!
# Towers of quotients, and the stalk of a higher direct image at a geometric point

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `ℱ` be an
`𝒪_X`-module and let `ȳ` be a geometric point of `Y`.  Write `A = 𝒪_{Y, ȳ}` for the étale
local ring at `ȳ` and `𝔪 = 𝔪_ȳ` for its maximal ideal.  This file sets up the vocabulary in which
the theorem on formal functions at a geometric point, [Stacks, Tag 08B1], is stated: the stalk
`M = (R ᵖ f_* ℱ)_ȳ` of a higher direct image, and the property
`Stacks.AdicTowerComparison.CompletionIsoLimitOfQuotients` of a tower `P` of `A`-modules with
maps `π n : M ⟶ P n`, that the `π n` assemble into an isomorphism `M ^∧_𝔪 ≅ lim_n P n` — the
shape of the conclusion of [Stacks, Tag 08AZ].

[Stacks, Tag 08B1] itself is
`AlgebraicGeometry.Space.completionIsoLimitOfQuotientsOverCompletion_geometricStalk`, in
`StacksFrontier/AlgebraicGeometry/Spaces/FormalFunctionsGeometricStalkLimit.lean`, where the
infinitesimal neighbourhoods `X_n = Spec (A/𝔪 ⁿ) ×_Y X` are constructed and the isomorphism is
proved, linear over `A ^∧`, from [Stacks, Tag 08AZ]
(`AlgebraicGeometry.Space.C1573.formalFunctionsEquivOfIsAffine`).

## Main definitions

* `Stacks.AdicTowerComparison.CompletionIsoLimitOfQuotients` — the shape of the conclusion of
  [Stacks, Tag 08AZ]: the maps `ρ n : M ⟶ Q n` assemble into an isomorphism `M ^∧_I ≅ lim_n Q n`.
* `AlgebraicGeometry.Space.moduleHigherPushforward` — `R ᵖ f_* ℱ`, the `p`-th higher direct
  image of an `𝒪_X`-module along a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.moduleHigherPushforwardGeometricStalk` — its stalk `(R ᵖ f_* ℱ)_ȳ`
  at a geometric point, as a module over the étale local ring there.
* `AlgebraicGeometry.Space.geometricMaximalIdeal` — the maximal ideal `𝔪_ȳ` of `𝒪_{Y, ȳ}`.

## Main results

* `Stacks.AdicTowerComparison.towerLimitCongr` — an isomorphism of towers induces an
  isomorphism of their limits.
* `Stacks.AdicTowerComparison.CompletionIsoLimitOfQuotients.of_towerIso` — the property
  transports along an isomorphism of towers compatible with the projections.
* `Stacks.AdicTowerComparison.completionIsoLimitOfQuotients_of_bounds` — the property follows
  from bounds on the kernels of the projections and the stabilization of the images of the
  transition maps, the shape of [Stacks, Tag 08AY].
* `AlgebraicGeometry.Space.pow_smul_top_le_ker_of_pow_smul_top_eq_bot` — if `𝔪 ⁿ` annihilates
  `P n`, then `𝔪 ⁿ M ⊆ ker (π n)`.
* `AlgebraicGeometry.Space.completionIsoLimitOfQuotients_geometricStalk_of_towerIso` and
  `AlgebraicGeometry.Space.completionIsoLimitOfQuotients_geometricStalk_of_bounds` — the two
  lemmas above specialized to an arbitrary tower under the stalk `(R ᵖ f_* ℱ)_ȳ`.

## References

* [Stacks Project, Tag 08B1](https://stacks.math.columbia.edu/tag/08B1)
* [Stacks Project, Tag 08AY](https://stacks.math.columbia.edu/tag/08AY)
* [Stacks Project, Tag 08AZ](https://stacks.math.columbia.edu/tag/08AZ)
* [Stacks Project, Tag 08AH](https://stacks.math.columbia.edu/tag/08AH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

/-! ### Towers of quotients and adic completions -/

namespace Stacks.AdicTowerComparison

open Stacks.IntertwinedFiltration

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- **The shape of the conclusion of [Stacks, Tag 08AZ], and of [Stacks, Tag 08B1].**

For an `A`-module `M`, an ideal `I ⊆ A`, a tower `Q` of `A`-modules with transition maps `U` and
compatible maps `ρ n : M ⟶ Q n`, this says that the `ρ n` assemble into an isomorphism
`M ^∧_I ≅ lim_n Q n`: there is an isomorphism of `A`-modules whose `n`-th component carries the
image of `x ∈ M` in the completion to `ρ n x`.

The source phrases this as "the system of maps `M/I ⁿ M ⟶ Q n` define an isomorphism of
limits"; since each `M/I ⁿ M ⟶ Q n` is induced by `ρ n`, that is the condition stated here.
Neither the homeomorphism for the limit topologies nor `A ^∧`-linearity is part of this
property. -/
def CompletionIsoLimitOfQuotients (I : Ideal A) (M : Type*) [AddCommGroup M] [Module A M]
    (Q : ℕ → Type*) [∀ n, AddCommGroup (Q n)] [∀ n, Module A (Q n)]
    (U : ∀ m n : ℕ, m ≤ n → Q n →ₗ[A] Q m) (ρ : ∀ n, M →ₗ[A] Q n) : Prop :=
  ∃ e : AdicCompletion I M ≃ₗ[A] towerLimit Q U,
    ∀ (n : ℕ) (x : M), towerLimit.proj n (e (AdicCompletion.of I M x)) = ρ n x

/-- **An isomorphism of towers induces an isomorphism of their limits.**

If `e n : Q n ≅ P n` are isomorphisms of `A`-modules commuting with the transition maps of the
two towers, then the limits of the towers are isomorphic, by applying `e` componentwise. -/
def towerLimitCongr (Q : ℕ → Type*) [∀ n, AddCommGroup (Q n)] [∀ n, Module A (Q n)]
    (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
    (U : ∀ m n : ℕ, m ≤ n → Q n →ₗ[A] Q m) (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m)
    (e : ∀ n, Q n ≃ₗ[A] P n)
    (he : ∀ (m n : ℕ) (h : m ≤ n) (x : Q n), T m n h (e n x) = e m (U m n h x)) :
    towerLimit Q U ≃ₗ[A] towerLimit P T where
  toFun x := ⟨fun n => e n ((x : ∀ k, Q k) n), by
    intro m n h
    rw [he m n h, towerLimit_compat x m n h]⟩
  map_add' _ _ := Subtype.ext (funext fun n => map_add (e n) _ _)
  map_smul' _ _ := Subtype.ext (funext fun n => map_smul (e n) _ _)
  invFun x := ⟨fun n => (e n).symm ((x : ∀ k, P k) n), by
    intro m n h
    refine (e m).injective ?_
    rw [← he m n h, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      towerLimit_compat x m n h]⟩
  left_inv x := Subtype.ext (funext fun n => (e n).symm_apply_apply _)
  right_inv x := Subtype.ext (funext fun n => (e n).apply_symm_apply _)

@[simp]
theorem towerLimitCongr_proj (Q : ℕ → Type*) [∀ n, AddCommGroup (Q n)] [∀ n, Module A (Q n)]
    (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
    (U : ∀ m n : ℕ, m ≤ n → Q n →ₗ[A] Q m) (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m)
    (e : ∀ n, Q n ≃ₗ[A] P n)
    (he : ∀ (m n : ℕ) (h : m ≤ n) (x : Q n), T m n h (e n x) = e m (U m n h x))
    (n : ℕ) (x : towerLimit Q U) :
    towerLimit.proj n (towerLimitCongr Q P U T e he x) = e n (towerLimit.proj n x) :=
  rfl

/-- **The conclusion of [Stacks, Tag 08AZ] transports along an isomorphism of towers.**

If the maps `ρ n : M ⟶ Q n` assemble into an isomorphism `M ^∧_I ≅ lim_n Q n`, and `e n` is an
isomorphism of towers `Q ≅ P` carrying `ρ n` to `π n`, then the `π n` assemble into an
isomorphism `M ^∧_I ≅ lim_n P n`.

This is the step by which [Stacks, Tag 08B1] is deduced from [Stacks, Tag 08AZ]: there `Q n` is
the cohomology of the adic quotient on the base change over the local ring and `P n` is the
cohomology on the infinitesimal neighbourhood, and `e` is the identification of the two. -/
theorem CompletionIsoLimitOfQuotients.of_towerIso {I : Ideal A}
    {Q : ℕ → Type*} [∀ n, AddCommGroup (Q n)] [∀ n, Module A (Q n)]
    {P : ℕ → Type*} [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
    {U : ∀ m n : ℕ, m ≤ n → Q n →ₗ[A] Q m} {T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m}
    {ρ : ∀ n, M →ₗ[A] Q n} {π : ∀ n, M →ₗ[A] P n}
    (h : CompletionIsoLimitOfQuotients I M Q U ρ) (e : ∀ n, Q n ≃ₗ[A] P n)
    (he : ∀ (m n : ℕ) (h : m ≤ n) (x : Q n), T m n h (e n x) = e m (U m n h x))
    (hπ : ∀ (n : ℕ) (x : M), π n x = e n (ρ n x)) :
    CompletionIsoLimitOfQuotients I M P T π := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g.trans (towerLimitCongr Q P U T e he), fun n x => ?_⟩
  rw [LinearEquiv.trans_apply, towerLimitCongr_proj, hg n x, hπ n x]

/-- **The conclusion of [Stacks, Tag 08AZ] from the bounds of [Stacks, Tag 08AY].**

With `K n = ker (π n)`, the bounds `I ⁿ M ⊆ K n` and `K n ⊆ I ^ (n - c) M` for `n ≥ c`, together
with the stabilization `im (Q k ⟶ Q n) = im (π n)` for `k` beyond a level `c₂ ≥ n` depending on
`n`, make the `K`-filtration cofinal in the `I`-adic one and identify `lim_n Q n` with
`lim_n M/K n`.  That argument is
`Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange`; this restates its
conclusion as `CompletionIsoLimitOfQuotients`, the comparison being the one assembled from the
`π n` by `Stacks.Cohomology.FormalFunctions.formalFunctionsEquiv_proj_of`'s argument. -/
theorem completionIsoLimitOfQuotients_of_bounds (I : Ideal A) (c : ℕ)
    (Q : ℕ → Type*) [∀ n, AddCommGroup (Q n)] [∀ n, Module A (Q n)]
    (U : ∀ m n : ℕ, m ≤ n → Q n →ₗ[A] Q m) (ρ : ∀ n, M →ₗ[A] Q n)
    (hρ : ∀ (m n : ℕ) (h : m ≤ n), (U m n h).comp (ρ n) = ρ m)
    (hker : ∀ n, I ^ n • (⊤ : Submodule A M) ≤ LinearMap.ker (ρ n))
    (hker' : ∀ n, c ≤ n → LinearMap.ker (ρ n) ≤ I ^ (n - c) • (⊤ : Submodule A M))
    (hrange : ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
      LinearMap.range (U n k h) = LinearMap.range (ρ n)) :
    CompletionIsoLimitOfQuotients I M Q U ρ :=
  ⟨adicCompletionEquivTowerLimitOfEventualRange Q U ρ I c hρ hker hker' hrange, fun _ _ => rfl⟩

end Stacks.AdicTowerComparison

namespace AlgebraicGeometry.Space

open Stacks.AdicTowerComparison Stacks.IntertwinedFiltration

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The stalk of a higher direct image at a geometric point -/

/-- The `p`-th higher direct image `R ᵖ f_* ℱ` of an `𝒪_X`-module along a morphism of algebraic
spaces, the `p`-th right derived functor of the direct image `f_*` of [Stacks, Tag 03LU].

The injective resolutions used to form it are those of
`AlgebraicGeometry.Space.hasInjectiveResolutions_modules`; the object produced does not depend
on them, so the instance is introduced by `have`. -/
noncomputable def moduleHigherPushforward {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.obj X.property) (p : ℕ) :
    Modules.{u, u} B S hS Y.obj Y.property :=
  have := hasInjectiveResolutions_modules B S hS X.obj X.property
  ((modulePushforward B S hS f).rightDerived p).obj F

/-- The stalk `(R ᵖ f_* ℱ)_ȳ` of a higher direct image at a geometric point of the target, as a
module over the étale local ring `𝒪_{Y, ȳ}` of [Stacks, Tag 04KG]. -/
noncomputable def moduleHigherPushforwardGeometricStalk {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.obj X.property) (p : ℕ)
    (y : GeometricPoint B S hS Y.obj) :
    ModuleCat (etaleLocalRing B S hS Y.obj y) :=
  geometricModuleStalk B S hS Y y (moduleHigherPushforward B S hS f F p)

/-- The maximal ideal `𝔪_ȳ` of the étale local ring of an algebraic space at a geometric point.
That the étale local ring is local is [Stacks, Tag 08AH],
`AlgebraicGeometry.Space.isLocalRing_etaleLocalRing`. -/
noncomputable def geometricMaximalIdeal (Y : AlgebraicSpaces B S hS)
    (y : GeometricPoint B S hS Y.obj) : Ideal (etaleLocalRing B S hS Y.obj y) :=
  have := isLocalRing_etaleLocalRing B S hS Y.obj Y.property y
  IsLocalRing.maximalIdeal (etaleLocalRing B S hS Y.obj y)

/-! ### The theorem on formal functions at a geometric point -/

section FormalFunctions

variable {B S hS} {Y : AlgebraicSpaces B S hS} {y : GeometricPoint B S hS Y.obj}

/-- **The sentence "`𝔪 ⁿ M ⊆ K n` because the `n`-th term is killed by `𝔪 ⁿ`" of the proof of
[Stacks, Tag 08B1].**

If the `n`-th power of the maximal ideal at `ȳ` annihilates the `n`-th term of the tower, then
it annihilates the image of the `n`-th projection, so `𝔪 ⁿ M` lies in the kernel of that
projection.  For the tower of the source, `P n = H ᵖ (X_n, ℱ_n)` with `X_n` an algebraic space
over `Spec (𝒪_{Y, ȳ}/𝔪 ⁿ)`, the annihilation holds. -/
theorem pow_smul_top_le_ker_of_pow_smul_top_eq_bot {M : Type*} [AddCommGroup M]
    [Module (etaleLocalRing B S hS Y.obj y) M] (P : ℕ → Type*) [∀ n, AddCommGroup (P n)]
    [∀ n, Module (etaleLocalRing B S hS Y.obj y) (P n)]
    (π : ∀ n, M →ₗ[etaleLocalRing B S hS Y.obj y] P n) (n : ℕ)
    (hann : geometricMaximalIdeal B S hS Y y ^ n •
      (⊤ : Submodule (etaleLocalRing B S hS Y.obj y) (P n)) = ⊥) :
    geometricMaximalIdeal B S hS Y y ^ n •
        (⊤ : Submodule (etaleLocalRing B S hS Y.obj y) M) ≤ LinearMap.ker (π n) := by
  refine Submodule.smul_le.2 fun α hα x _ => ?_
  rw [LinearMap.mem_ker, map_smul]
  have hmem : α • π n x ∈ geometricMaximalIdeal B S hS Y y ^ n •
      (⊤ : Submodule (etaleLocalRing B S hS Y.obj y) (P n)) :=
    Submodule.smul_mem_smul hα Submodule.mem_top
  rw [hann] at hmem
  simpa using hmem

/-- **Transport of the comparison along an isomorphism of towers, under the stalk
`(R ᵖ f_* ℱ)_ȳ`.**

Let `M = (R ᵖ f_* ℱ)_ȳ` and `𝔪` the maximal ideal of `𝒪_{Y, ȳ}`.  If the maps `ρ n : M ⟶ Q n`
assemble into an isomorphism `M ^∧_𝔪 ≅ lim_n Q n`, and `e` is an isomorphism of towers `Q ≅ P`
carrying `ρ n` to `π n`, then the `π n` assemble into an isomorphism `M ^∧_𝔪 ≅ lim_n P n`.  The
theorem on formal functions at `ȳ`, [Stacks, Tag 08B1], is
`AlgebraicGeometry.Space.completionIsoLimitOfQuotientsOverCompletion_geometricStalk`. -/
theorem completionIsoLimitOfQuotients_geometricStalk_of_towerIso
    {X : AlgebraicSpaces B S hS} (f : X ⟶ Y) (_hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.obj X.property)
    (_hF : IsCoherent B S hS X.obj X.property F) (p : ℕ)
    (Q : ℕ → Type*) [∀ n, AddCommGroup (Q n)]
    [∀ n, Module (etaleLocalRing B S hS Y.obj y) (Q n)]
    (U : ∀ m n : ℕ, m ≤ n → Q n →ₗ[etaleLocalRing B S hS Y.obj y] Q m)
    (ρ : ∀ n, moduleHigherPushforwardGeometricStalk B S hS f F p y
      →ₗ[etaleLocalRing B S hS Y.obj y] Q n)
    (P : ℕ → Type*) [∀ n, AddCommGroup (P n)]
    [∀ n, Module (etaleLocalRing B S hS Y.obj y) (P n)]
    (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[etaleLocalRing B S hS Y.obj y] P m)
    (π : ∀ n, moduleHigherPushforwardGeometricStalk B S hS f F p y
      →ₗ[etaleLocalRing B S hS Y.obj y] P n)
    (hQ : CompletionIsoLimitOfQuotients (geometricMaximalIdeal B S hS Y y)
      (moduleHigherPushforwardGeometricStalk B S hS f F p y) Q U ρ)
    (e : ∀ n, Q n ≃ₗ[etaleLocalRing B S hS Y.obj y] P n)
    (he : ∀ (m n : ℕ) (h : m ≤ n) (x : Q n), T m n h (e n x) = e m (U m n h x))
    (hπ : ∀ (n : ℕ) (x : moduleHigherPushforwardGeometricStalk B S hS f F p y),
      π n x = e n (ρ n x)) :
    CompletionIsoLimitOfQuotients (geometricMaximalIdeal B S hS Y y)
      (moduleHigherPushforwardGeometricStalk B S hS f F p y) P T π :=
  hQ.of_towerIso e he hπ

/-- **The comparison from bounds on a tower under the stalk `(R ᵖ f_* ℱ)_ȳ`.**

Let `M = (R ᵖ f_* ℱ)_ȳ`, `𝔪` the maximal ideal of `𝒪_{Y, ȳ}`, and `P` a tower with compatible
maps `π n : M ⟶ P n` such that `𝔪 ⁿ` annihilates `P n`, `ker (π n) ⊆ 𝔪 ^ (n - c) M` for `n ≥ c`,
and for each `n` the images of the transition maps into `P n` equal the image of `π n` from some
level `c₂ ≥ n` on (the shape of clauses (1) and (3) of [Stacks, Tag 08AY]).  Then the `π n`
assemble into an isomorphism `M ^∧_𝔪 ≅ lim_n P n`, by
`Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange`.  The theorem on formal
functions at `ȳ`, [Stacks, Tag 08B1], is
`AlgebraicGeometry.Space.completionIsoLimitOfQuotientsOverCompletion_geometricStalk`. -/
theorem completionIsoLimitOfQuotients_geometricStalk_of_bounds
    {X : AlgebraicSpaces B S hS} (f : X ⟶ Y) (_hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.obj X.property)
    (_hF : IsCoherent B S hS X.obj X.property F) (p : ℕ) (c : ℕ)
    (P : ℕ → Type*) [∀ n, AddCommGroup (P n)]
    [∀ n, Module (etaleLocalRing B S hS Y.obj y) (P n)]
    (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[etaleLocalRing B S hS Y.obj y] P m)
    (π : ∀ n, moduleHigherPushforwardGeometricStalk B S hS f F p y
      →ₗ[etaleLocalRing B S hS Y.obj y] P n)
    (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m)
    (hann : ∀ n, geometricMaximalIdeal B S hS Y y ^ n •
      (⊤ : Submodule (etaleLocalRing B S hS Y.obj y) (P n)) = ⊥)
    (hker : ∀ n : ℕ, c ≤ n → LinearMap.ker (π n) ≤
      geometricMaximalIdeal B S hS Y y ^ (n - c) •
        (⊤ : Submodule (etaleLocalRing B S hS Y.obj y)
          (moduleHigherPushforwardGeometricStalk B S hS f F p y)))
    (hrange : ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
      LinearMap.range (T n k h) = LinearMap.range (π n)) :
    CompletionIsoLimitOfQuotients (geometricMaximalIdeal B S hS Y y)
      (moduleHigherPushforwardGeometricStalk B S hS f F p y) P T π :=
  completionIsoLimitOfQuotients_of_bounds (geometricMaximalIdeal B S hS Y y) c P T π hπ
    (fun n => pow_smul_top_le_ker_of_pow_smul_top_eq_bot P π n (hann n)) hker hrange

end FormalFunctions

end AlgebraicGeometry.Space

end
