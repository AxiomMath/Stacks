module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.RingTheory.AdicCompletion.IntertwinedFiltrationEventualRange

/-!
# The theorem on formal functions at a geometric point of an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `ℱ` be an
`𝒪_X`-module and let `ȳ` be a geometric point of `Y`.  Write `A = 𝒪_{Y, ȳ}` for the étale
local ring at `ȳ` and `𝔪 = 𝔪_ȳ` for its maximal ideal, and put

* `M = (R ᵖ f_* ℱ)_ȳ`, the stalk at `ȳ` of the `p`-th higher direct image, an `A`-module;
* `P n = H ᵖ (X_n, ℱ_n)`, the cohomology of `ℱ_n = i_n ^* ℱ` on the `n`-th infinitesimal
  neighbourhood `X_n = Spec (A/𝔪 ⁿ) ×_Y X` of the geometric fibre, with transition maps `T`
  induced by the closed immersions `X_n ⟶ X_k` and restriction maps `π n : M ⟶ P n`.

[Stacks, Tag 08B1] says that the `π n` assemble into an isomorphism `M ^∧_𝔪 ≅ lim_n P n`.  That
property of a tower-with-projections is
`Stacks.AdicTowerComparison.CompletionIsoLimitOfQuotients`, and it is also the shape of the
conclusion of [Stacks, Tag 08AZ], the theorem on formal functions for algebraic spaces, which
08B1 is a reformulation of.

Two routes to it are given, differing in which input is carried:

* `AlgebraicGeometry.Space.completionIsoLimitOfQuotients_geometricStalk_of_towerIso` carries
  [Stacks, Tag 08AZ] itself as one named hypothesis `h08AZ`, for the tower
  `Q n = H ᵖ (X', ℱ'/𝔪 ⁿ ℱ')` on the base change `X' = Spec A ×_Y X` that 08AZ is stated for,
  together with the identification of that tower with the source's own tower `P` — which is the
  combination of [Stacks, Tag 073K] and [Stacks, Tag 07UH] used by the last two sentences of the
  source's proof — and proves 08B1 from them.
* `AlgebraicGeometry.Space.completionIsoLimitOfQuotients_geometricStalk_of_bounds` instead
  carries clauses (1) and (3) of [Stacks, Tag 08AY] for the tower `P` and *derives* the
  comparison, through
  `Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange`.

Only the isomorphism of `A`-modules is in question.  [Stacks, Tag 08AZ], and hence
[Stacks, Tag 08B1], also asserts it to be a homeomorphism for the limit topologies and the
module structure to be one over `A ^∧`; no statement below claims either refinement.

## Main definitions

* `Stacks.AdicTowerComparison.CompletionIsoLimitOfQuotients` — the shape of the conclusion of
  [Stacks, Tag 08AZ] and of [Stacks, Tag 08B1]: the maps `ρ n : M ⟶ Q n` assemble into an
  isomorphism `M ^∧_I ≅ lim_n Q n`.
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
* `AlgebraicGeometry.Space.pow_smul_top_le_ker_of_pow_smul_top_eq_bot` — if `𝔪 ⁿ` annihilates
  `P n`, then `𝔪 ⁿ M ⊆ ker (π n)`.  This is the sentence "`𝔪 ⁿ M ⊆ K n` because the `n`-th term
  is killed by `𝔪 ⁿ`" of the source's argument, and `𝔪 ⁿ` does annihilate `H ᵖ (X_n, ℱ_n)`
  because `X_n` lives over `Spec (A/𝔪 ⁿ)`.
* `AlgebraicGeometry.Space.completionIsoLimitOfQuotients_geometricStalk_of_towerIso` and
  `AlgebraicGeometry.Space.completionIsoLimitOfQuotients_geometricStalk_of_bounds` — the two
  routes to [Stacks, Tag 08B1] described above.

## Implementation notes

### What is carried, and why

The source's proof is a reformulation.  Flat base change along `Spec 𝒪_{Y, ȳ} ⟶ Y`
([Stacks, Tag 073K], clause (1)) identifies `M` with `H ᵖ (X', ℱ')` for the base change
`X' = Spec 𝒪_{Y, ȳ} ×_Y X`; the Leray spectral sequence for the closed immersions `X_n ⟶ X'`
together with [Stacks, Tag 07UH] identifies `P n = H ᵖ (X_n, ℱ_n)` with
`Q n = H ᵖ (X', ℱ'/𝔪 ⁿ ℱ')`; and the theorem on formal functions for algebraic spaces,
[Stacks, Tag 08AZ], computes the completion of `H ᵖ (X', ℱ')` as `lim_n Q n`.  None of the three
is available in this repository:

* [Stacks, Tag 08AZ] is not formalized — no declaration in the library carries that tag —
  and neither is its input [Stacks, Tag 08AY] nor the coherence [Stacks, Tag 08AR];
* of [Stacks, Tag 073K] only the base change map whose invertibility clause (1) asserts is
  constructed, in `StacksFrontier/AlgebraicGeometry/Spaces/CohomologyFlatBaseChange.lean`, whose own
  implementation notes record that neither clause is proved;
* [Stacks, Tag 07UH] is formalized in
  `StacksFrontier/AlgebraicGeometry/Spaces/FiniteDirectImageCoherence.lean` only with its
  étale-affine case carried as the hypothesis `h03DW`, and the Leray comparison for a closed
  immersion that the source combines it with has no formalization here.

Accordingly the first route carries [Stacks, Tag 08AZ] as the single named hypothesis `h08AZ`,
in the shape of its own conclusion — `Stacks.AdicTowerComparison.CompletionIsoLimitOfQuotients`
for the tower `Q` and the projections `ρ` — and carries the identification of `Q` with `P` as a
levelwise isomorphism compatible with the transitions and the projections.  What is proved is
the transport of the conclusion along that identification, which is the content of the last two
sentences of the source's proof.  The second route carries instead clauses (1) and (3) of
[Stacks, Tag 08AY], in the very shape that tag is formalized in as
`Stacks.AdicCohomologyBound.ker_le_pow_smul_top` and
`Stacks.AdicCohomologyBound.exists_range_transition_eq_range_proj`, and *derives* the comparison
from the limit argument
`Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange`, with the third
hypothesis of that engine proved here from the annihilation of `P n` by `𝔪 ⁿ`.

### Why the tower is data

The system `P` is data rather than a construction because the infinitesimal neighbourhoods `X_n`
cannot be formed in this development: `AlgebraicGeometry.Space.etaleLocalRing` is a colimit over
the category of small étale neighbourhoods, whose objects live in `Type (u + 1)`, so it is a
`CommRingCat.{u + 1}` and `Spec (𝒪_{Y, ȳ}/𝔪 ⁿ)` is a `Scheme.{u + 1}` — not an object of a
`BigFppfSite.{u}`, hence not a base for an algebraic space over `S`.  Building the `X_n` needs
[Stacks, Tag 04KF] to replace `𝒪_{Y, ȳ}` by an isomorphic ring in `Type u` presented by a scheme
chart, which is `AlgebraicGeometry.Space.strictHenselizationEquivEtaleLocalRing`, and then the
membership of each `Spec (A/𝔪 ⁿ)` in the site; that is a separate piece of work and is not done
here.  The same obstruction is why no `𝒪_{Y, ȳ} ^∧`-module structure on `lim_n P n` is
available: it would have to come from the action of the functions on `Spec (A/𝔪 ⁿ)` on
`H ᵖ (X_n, ℱ_n)` through `f_n`.  The scheme-level [Stacks, Tag 02OC] in this repository,
`Stacks.Cohomology.FormalFunctions.formalFunctionsEquiv`, is stated with the same restriction.

### The standing hypotheses of the source

The situation of [Stacks, Tag 08AZ] is [Stacks, Tag 08AV]: a Noetherian ring `A`, an ideal
`I ⊆ A`, a proper morphism `X ⟶ Spec A` of algebraic spaces and a coherent `𝒪_X`-module.  The
hypotheses of [Stacks, Tag 08B1] — `Y` locally Noetherian, `f` proper, `ℱ` coherent — are
exactly what puts the base change `X' ⟶ Spec 𝒪_{Y, ȳ}` in that situation: the étale local ring
of a locally Noetherian algebraic space at a geometric point is Noetherian and local by
[Stacks, Tag 08AH], properness is stable under base change, and coherence is preserved by the
pullback along `X' ⟶ X`.  That is the whole role of the three hypotheses in the source's proof,
so, as in the scheme-level `Stacks.Cohomology.FormalFunctions.formalFunctionsEquiv`, properness
and coherence appear below only as the unused arguments `_hf` and `_hF`, recording which
statement is being proved, and Noetherianness of `Y` does not appear at all — the Noetherian
local ring step is already available as
`AlgebraicGeometry.Space.isNoetherianRing_etaleLocalRing` and
`AlgebraicGeometry.Space.isLocalRing_etaleLocalRing` and is not restated here.

## References

* [Stacks Project, Tag 08B1](https://stacks.math.columbia.edu/tag/08B1)
* [Stacks Project, Tag 08AV](https://stacks.math.columbia.edu/tag/08AV)
* [Stacks Project, Tag 08AY](https://stacks.math.columbia.edu/tag/08AY)
* [Stacks Project, Tag 08AZ](https://stacks.math.columbia.edu/tag/08AZ)
* [Stacks Project, Tag 08AH](https://stacks.math.columbia.edu/tag/08AH)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
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

/-- **[Stacks, Tag 08B1]**, granted [Stacks, Tag 08AZ], and for the `𝒪_{Y, ȳ}`-module
isomorphism only.

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over a scheme `S` with `Y` locally
Noetherian, let `ℱ` be a coherent `𝒪_X`-module and let `ȳ` be a geometric point of `Y`.  Write
`𝔪` for the maximal ideal of `𝒪_{Y, ȳ}` and `M = (R ᵖ f_* ℱ)_ȳ`.  Let `P` be the tower
`n ↦ H ᵖ (X_n, ℱ_n)` of the source, with transition maps `T` and restriction maps `π`.  Then the
`π n` assemble into an isomorphism `M ^∧_𝔪 ≅ lim_n H ᵖ (X_n, ℱ_n)`.

Carried: the tower `Q` of [Stacks, Tag 08AZ] — the cohomology `H ᵖ (X', ℱ'/𝔪 ⁿ ℱ')` on the base
change `X' = Spec 𝒪_{Y, ȳ} ×_Y X` — with its projections `ρ` out of `M`, the conclusion of
[Stacks, Tag 08AZ] for it as the single hypothesis `h08AZ`, and the identification `e` of `Q`
with `P`, which is the combination of [Stacks, Tag 073K] and [Stacks, Tag 07UH] that the
source's last two sentences perform.  Proved: that these give the statement.  See the
implementation notes of this file for why each of the three is unavailable here, and for the two
refinements of the source's conclusion — the homeomorphism of limit topologies and
`𝒪_{Y, ȳ} ^∧`-linearity — that are **not** claimed. -/
@[stacks 08B1 "the restriction maps assemble into an isomorphism (R^p f_* ℱ)_ȳ^∧ ≅ \
lim_n H^p(X_n, ℱ_n) of 𝒪_{Y,ȳ}-modules, granted Tag 08AZ, which is absent from this \
repository: 08AZ's own conclusion for the tower H^p(X', ℱ'/𝔪^n ℱ') is the hypothesis h08AZ, \
and its identification with the tower H^p(X_n, ℱ_n) -- Tag 073K clause (1) plus Tag 07UH and \
Leray, none of them proved here -- is the hypothesis e. The tower is data because the X_n need \
Tag 04KF to be formed at the universe of the site. Neither the homeomorphism of limit \
topologies nor 𝒪_{Y,ȳ}^∧-linearity is asserted"]
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
    (h08AZ : CompletionIsoLimitOfQuotients (geometricMaximalIdeal B S hS Y y)
      (moduleHigherPushforwardGeometricStalk B S hS f F p y) Q U ρ)
    (e : ∀ n, Q n ≃ₗ[etaleLocalRing B S hS Y.obj y] P n)
    (he : ∀ (m n : ℕ) (h : m ≤ n) (x : Q n), T m n h (e n x) = e m (U m n h x))
    (hπ : ∀ (n : ℕ) (x : moduleHigherPushforwardGeometricStalk B S hS f F p y),
      π n x = e n (ρ n x)) :
    CompletionIsoLimitOfQuotients (geometricMaximalIdeal B S hS Y y)
      (moduleHigherPushforwardGeometricStalk B S hS f F p y) P T π :=
  h08AZ.of_towerIso e he hπ

/-- **[Stacks, Tag 08B1]**, granted the bounds of [Stacks, Tag 08AY] for the tower of the
source, and for the `𝒪_{Y, ȳ}`-module isomorphism only.

The second route of this file: rather than carrying the conclusion of [Stacks, Tag 08AZ] and
transporting it, carry for the tower `P = H ᵖ (X_n, ℱ_n)` itself the two bounds that
[Stacks, Tag 08AY] provides — clause (1), a bound `ker (π n) ⊆ 𝔪 ^ (n - c) M` for `n ≥ c`, and
clause (3), that for each `n` the images of the transition maps into `P n` are the image of
`π n` from some level `c₂ ≥ n` on — and derive the comparison from the commutative-algebra core
`Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange`.  The two carried
hypotheses are exactly those two clauses, in the shape
`Stacks.AdicCohomologyBound.ker_le_pow_smul_top` and
`Stacks.AdicCohomologyBound.exists_range_transition_eq_range_proj` state them; in particular the
level in clause (3) depends on `n` and is not tied to `c`.  The remaining hypothesis of the core,
`𝔪 ⁿ M ⊆ ker (π n)`, is deduced here from the annihilation `hann` of `H ᵖ (X_n, ℱ_n)` by `𝔪 ⁿ`,
which holds because `X_n` lives over `Spec (𝒪_{Y, ȳ}/𝔪 ⁿ)`. -/
@[stacks 08B1 "the same conclusion by the second route: the bounds Tag 08AY supplies for the \
tower H^p(X_n, ℱ_n) are carried as h08AY_ker and h08AY_range, which are now exactly 08AY \
clauses (1) and (3) -- clause (3) with the per-n level the source states, not a uniform shift \
-- and the comparison is DERIVED from them; the annihilation hypothesis hann discharges the \
third input of the limit argument. Same two refinements not asserted as in the first route"]
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
    (h08AY_ker : ∀ n : ℕ, c ≤ n → LinearMap.ker (π n) ≤
      geometricMaximalIdeal B S hS Y y ^ (n - c) •
        (⊤ : Submodule (etaleLocalRing B S hS Y.obj y)
          (moduleHigherPushforwardGeometricStalk B S hS f F p y)))
    (h08AY_range : ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
      LinearMap.range (T n k h) = LinearMap.range (π n)) :
    CompletionIsoLimitOfQuotients (geometricMaximalIdeal B S hS Y y)
      (moduleHigherPushforwardGeometricStalk B S hS f F p y) P T π :=
  completionIsoLimitOfQuotients_of_bounds (geometricMaximalIdeal B S hS Y y) c P T π hπ
    (fun n => pow_smul_top_le_ker_of_pow_smul_top_eq_bot P π n (hann n)) h08AY_ker h08AY_range

end FormalFunctions

end AlgebraicGeometry.Space

end
