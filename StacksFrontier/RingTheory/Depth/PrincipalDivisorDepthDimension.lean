module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Support
public import StacksFrontier.RingTheory.Catenary.Localization
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksCore.Tactic.StacksAttribute

/-!
# The depth-dimension bounds along a principal divisor

Let `(A, 𝔪)` be a Noetherian local ring and let `f ∈ 𝔪` be a nonzerodivisor.  Hypotheses (5)
and (6) of [Stacks, Tag 0DXU] are the two bounds

* (5) `depth((A/f)_𝔭) + dim(A/𝔭) > 1` for every `𝔭 ∈ V(f)` other than `𝔪`;
* (6) `depth(A_𝔭) + dim(A/𝔭) > 3` for every `𝔭 ∉ V(f)` with `V(𝔭) ∩ V(f) ≠ {𝔪}`;

and the last part of the proof of that tag consumes them in three steps.  Fix a prime
`𝔮 ∈ V(f)` other than `𝔪`.  Then:

* the dual Ext modules `H^{-1}(ω^•_{A_𝔮})` and `H^{-2}(ω^•_{A_𝔮})` that the proof has to kill
  are finite modules supported in primes whose depth plus dimension is at most `3`, and (6)
  says every such prime contains `f`, so `f` is nilpotent on them;
* a finite module on which `f` is nilpotent has `fⁿ : N/fN → N/f^{n+1}N` zero for `n` large,
  which is the vanishing the proof asks for;
* `A_𝔮` has depth at least `1` because `f` is a nonzerodivisor, and depth at least `2` when
  `dim(A/𝔮) = 1`, by (5) and the same nonzerodivisor property; these are what make
  `H^0(ω^•_{A_𝔮})`, and in the second case also `H^{-1}(ω^•_{A_𝔮})`, vanish.

This file proves those three steps.

## Main definitions

* `Stacks.RingTheory.PrincipalDivisorDepth.DepthDimOnDivisor` — hypothesis (5).
* `Stacks.RingTheory.PrincipalDivisorDepth.DepthDimOffDivisor` — hypothesis (6).
* `Stacks.RingTheory.PrincipalDivisorDepth.mulPowQuotSMulTop` — multiplication by `fⁿ`, as a
  map `N ⧸ fN → N ⧸ f^{n+1}N`.
* `Stacks.RingTheory.PrincipalDivisorDepth.localizedQuotientEquiv` — the identification
  `(A/fA)_𝔭 = A_𝔭/fA_𝔭` under which hypothesis (5) is read.

## Main results

* `Stacks.RingTheory.PrincipalDivisorDepth.mem_of_depth_add_ringKrullDim_le_three` — under (6),
  a prime `𝔭 ⊆ 𝔮` with `depth(A_𝔭) + dim(A/𝔭) ≤ 3` contains `f`.
* `Stacks.RingTheory.PrincipalDivisorDepth.exists_mulPowQuotSMulTop_eq_zero_of_depthDimOffDivisor`
  — under (6), for a finite module supported in such primes the maps
  `fⁿ : N/fN → N/f^{n+1}N` vanish for all large `n`.
* `Stacks.RingTheory.PrincipalDivisorDepth.one_le_depth_localization` — `depth(A_𝔮) ≥ 1`
  because `f` is a nonzerodivisor.
* `Stacks.RingTheory.PrincipalDivisorDepth.two_le_depth_localization_of_depthDimOnDivisor` —
  `depth(A_𝔮) ≥ 2` when `dim(A/𝔮) = 1`, from (5) and `f` a nonzerodivisor.
* `Stacks.RingTheory.PrincipalDivisorDepth.ringKrullDim_quotient_eq_ringKrullDim_localization_add`
  — `dim(A/𝔭) = dim((A/𝔭)_𝔮) + dim(A/𝔮)` over a universally catenary `A`, the source's
  `dim((A/𝔭)_𝔮) = dim(A/𝔭) - 2`.
* `Stacks.RingTheory.PrincipalDivisorDepth.depth_add_ringKrullDim_quotient_le` — the support
  bound of [Stacks, Tag 0DWZ], stated over `A_𝔮`, read back as the bound over `A` that
  hypothesis (6) constrains.

## Implementation notes

The two bounds compare `ℕ∞`-valued depths with `WithBot ℕ∞`-valued Krull dimensions, so the
depth is coerced into `WithBot ℕ∞`; the coercion keeps `⊤`, which genuinely occurs (the depth of
the zero module), and the dimension term never contributes `⊥` because `A/𝔭` is nonzero.  The
single prime `𝔪` is written `IsLocalRing.closedPoint A`, and `V(𝔭) ∩ V(f)` is the set of primes
containing both; comparing that set with `{𝔪}` is the source's `V(𝔭) ∩ V(f) ≠ {𝔪}`.

Hypothesis (5) mentions the local ring `(A/fA)_𝔭`.  It is spelled here as the localization at
`𝔭` of the `A`-module `A/fA`, whose depth is taken over `A_𝔭` along the maximal ideal; depth
along an ideal depends on the ideal only through its action, so this is the depth of `(A/fA)_𝔭`
as a module over itself.  `localizedQuotientEquiv` identifies that module with `A_𝔭/fA_𝔭`,
which is the form in which "divide by a nonzerodivisor and the depth drops by one"
([Stacks, Tag 090R], `Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append`)
applies, and `depth_localizedModule_quotient_eq` transports the depth across it.

The nilpotence of `f` on a finite module supported inside `V(f)` is read off the description of
the support as the zero locus of the annihilator, so no Noetherian hypothesis beyond finiteness
of the module is needed for it.

### What is not proved here

This file does **not** prove [Stacks, Tag 0DXU].  Its conclusion — that `(ℱₙ)` extends
canonically to `X`, and is the completion of a coherent `𝒪_U`-module when `A` is complete — is
reached in the source by verifying conditions (a), (b) and (c) of [Stacks, Tag 0EHH].  Of those,
**two are available from the tag's hypotheses and one is not**, as follows.

* Condition (b) is available.  The short exact sequences `0 → ℱₙ → ℱ_{n+1} → ℱ₁ → 0` that
  hypotheses (3) and (4) produce are
  `Stacks.Algebraization.hasPrincipalShortExactSequences_of_locallyFree`
  (`…/CompletionCriteria/PrincipalShortExactSequences.lean`), proved from exactly those two
  hypotheses, and condition (b) itself is then
  `Stacks.Algebraization.adicModuleTopology_limitGlobalSections`.
* Condition (c) is available.  [Stacks, Tag 0BK3] is proved in full as
  `Stacks.LocalCohomology.isCoherent_pushforward_iff_forall_two_le_ringKrullDim`
  (`…/LocalCohomology/PushforwardCoherence/KollarCriterionAssembled.lean`) — the
  contrapositive one-point forms of `CoherentPushforwardCriterion/` are partial registrations of
  the same tag, not the whole of it — and its ring-theoretic counterpart, the equivalence of the
  finiteness of `H^i_T(M)` for `i ≤ s` with `depth(M_𝔭) + dim((A/𝔭)_𝔮) > s`, is
  `Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_iff_depth_add_dim`
  ([Stacks, Tag 0EFD]).  Hypothesis (5), at the primes of `V(f)` other than `𝔪`, is that
  inequality at `s = 1`, which is the finiteness of `H⁰(U, ℱₙ)` the source cites Local
  Cohomology, Proposition 51.8.7 for; and
  `Stacks.Algebraization.finite_globalSections_of_shortExactSequences` propagates it from `ℱ₁`
  to every `ℱₙ`.
* Condition (a) is what remains, and both conclusions of the tag now follow from it alone.
  Its weaker form suffices:
  `Stacks.Cohomology.InverseSystems.isMittagLefflerCategorical_of_finite_cohomology_image`
  ([Stacks, Tag 0DXG]) asks only that the image of `H¹(U, ℱₙ) → H¹(U, ℱ₁)` have finite length
  for some `n`, which is the source's own reduction, and
  `Stacks.Algebraization.canonicallyExtends_and_isCompletion_of_isFiniteLength_range` derives
  the tag's two conclusions from hypotheses (1)–(5) together with that finite length.  So the
  whole of what is still owed is one Lean proposition: the finite length of the image of

    `H¹(U, ℱₙ) ⟶ H¹(U, ℱ₁)`

  for some `n`, in the `Stacks.Algebraization.openCohomologyFunctor` spelling.

  The source's route to it is the dual computation, and these of its steps are available.  The
  identification of `H¹(U, −~)` with `H²_𝔞(−)` as a natural transformation — not merely object
  by object — is `Stacks.Algebraization.openCohomologyLocalCohomologyNatIso`, and its companion
  in the same namespace,
  `Algebraization.isFiniteLength_range_openCohomology_of_isFiniteLength_range_localCohomology`,
  turns the whole of what is owed into the statement about local cohomology:

    `∃ n, IsFiniteLength A (im(H²_𝔪(Mₙ) ⟶ H²_𝔪(M₁)))` for `Mₙ = H⁰(U, ℱₙ)`.

  That step needs `(H⁰(U, ℱₙ)~)|_U ≅ ℱₙ` naturally in `n`, which is
  `Stacks.Algebraization.tildeGlobalSectionsRestrictIso` ([Stacks, Tag 0EIR]), and no comparison of stalks is needed to use it.  The source's reduction of that
  statement to a vanishing after localization is
  `Stacks.LocalCohomology.isFiniteLength_range_of_forall_exists_smul_eq_zero`.  Matlis duality in
  the direction that returns from the dual to the module is
  `Stacks.Algebraization.isFiniteLength_of_isFiniteLength_matlisDual` and
  `Stacks.Algebraization.isFiniteLength_range_of_isFiniteLength_range_lcomp`.  The localization
  `ω^•_{A_𝔮} = (ω^•_A)_𝔮[dim(A/𝔮)]` is [Stacks, Tag 0A7Z],
  `Dualizing.isNormalizedDualizingComplex_localizationAtPrime_shift`.  The long exact sequence
  of `Ext^*_{A_𝔮}(A_𝔮/f^n, ω^•_{A_𝔮})` is `Dualizing.exact_extConnecting_extFromQuotient`,
  `Dualizing.exact_extFromQuotient_lsmul` and `Dualizing.exact_lsmul_extConnecting`.  The last
  step itself is `Dualizing.extQuotPow_eq_zero` with its two hypotheses discharged by
  `Dualizing.extQuotPow_eq_zero_of_le_depth_of_pow_smul_eq_zero` in the cases `dim(A/𝔮) = 2`
  and `dim(A/𝔮) = 1`, and by `Dualizing.subsingleton_moduleExtInto_of_pos` when
  `dim(A/𝔮) ≥ 3`; the depth bounds it needs are `one_le_depth_localization` and
  `two_le_depth_localization_of_depthDimOnDivisor` below, and the nilpotence of `f` is
  `exists_mulPowQuotSMulTop_eq_zero_of_depthDimOffDivisor`, whose support hypothesis is reached
  from [Stacks, Tag 0DWZ] part (4) over `A_𝔮` through
  `ringKrullDim_quotient_eq_ringKrullDim_localization_add` and
  `depth_add_ringKrullDim_quotient_le` below.

  The dual computation is now carried out in full.  The localization of the `Ext` *map* is
  `Dualizing.localizedExtLinearEquivOfDerivedHom_naturality`, natural in the module, and

    `Stacks.Algebraization.exists_isFiniteLength_range_extPrecompGlobalSections`
    (`…/CompletionCriteria/PrincipalExtImageFiniteLength.lean`)

  proves, from hypotheses (1)–(6) and nothing else, that for some `n` the image of

    `Ext^{-2}_A(M₀, ω^•_A) ⟶ Ext^{-2}_A(Mₙ, ω^•_A)`

  has finite length.  The three cases on `dim(A/𝔮)` are
  `Dualizing.exists_forall_ext_precomp_localized_eq_zero`; one index serves every prime at once
  by the ascending chain condition on the kernels
  (`Stacks.LocalCohomology.exists_isFiniteLength_range_of_forall_exists_smul_eq_zero`), which is
  what the source gets from its Lemma 52.5.2.

  The local structure that hypothesis (4) gives at a prime `𝔮 ∈ V(f) ∖ {𝔪}` is available too, as
  `Stacks.Algebraization.exists_linearEquiv_quotSMulTop_localizedModule_globalSectionsSystem` and
  `Stacks.Algebraization.surjective_and_ker_localizedModule_map_globalSectionsSystem`
  (`…/CompletionCriteria/PrincipalLocalFreeStructure.lean`).  A rank and a basis compatible with the
  transition maps are **not needed**.  It is enough that `(Mₙ)_𝔮` be free over
  `A_𝔮/f^{n+1}` of *some* finite rank and that `(Mₙ)_𝔮 ⟶ (M₀)_𝔮` be surjective with kernel
  `f(Mₙ)_𝔮`, because two surjections out of one module with one kernel differ by an isomorphism
  of their targets (`Dualizing.ext_precomp_eq_zero_of_isoQuotPow`).  Reading the stalk statements
  back over `A` needed a comparison between the stalk of `M^~|_U` at a point of `U` and
  `LocalizedModule 𝔮ᶜ M` that is **natural in `M`**: the objectwise
  `Stacks.Algebraization.exists_addEquiv_localizedModule_stalk_restrict_tilde` is an `∃` and
  loses the witness, so it cannot transport a statement about a map.  That comparison is
  `Stacks.Algebraization.localizedModuleStalkEquiv` with
  `Stacks.Algebraization.localizedModuleStalkEquiv_naturality`.

  What remains is one step: local duality in its Ext form naturally in the *module*, carrying a
  **finite length** and not merely a vanishing.
  `Dualizing.LocalDuality.exists_natural_extToMatlisDualMap` is pinned and natural, so it does
  carry images, giving
  `Submodule.map μ (im of the Ext map) = Submodule.map (lcomp E (H²_𝔪 map)) (range μ)`; but `μ` is
  the `H⁰` of the completion unit, which is only *injective*
  (`AdicCompletionCohomology.injective_homology_derivedCompletionUnit`) and *surjective modulo
  `𝔪`* (`Stacks.Algebraization.range_homologyMap_derivedCompletionUnit_sup_smul_eq_top`).  Those
  two settle the vanishing transport —
  `Dualizing.LocalDuality.homologyMap_localCohomology_eq_zero_of_forall_comp_eq_zero` takes a
  vanishing to a vanishing, and
  `Stacks.LocalCohomology.eq_zero_of_forall_mem_comp_eq_zero_of_sup_eq_top` is vanishing on both
  sides — but **not** a finite-length transport, because
  `Stacks.Algebraization.isFiniteLength_range_of_isFiniteLength_range_lcomp` asks for the *whole*
  range of the dualized map, and what the density statement delivers is a submodule whose
  quotient is `𝔪`-divisible.  So the missing proposition is either the finite-length analogue of
  that detection theorem, or surjectivity of `μ` — equivalently [Stacks, Tag 0A06] pinned to the
  completion unit in surjective form, upgrading `⊔ 𝔪 • ⊤ = ⊤` to `= ⊤`.  Over an `𝔪`-adically
  complete `A` the obstruction disappears, the unit at a bounded complex with finite cohomology
  being invertible there; so a base change of the finite-length statement along `A → Â` — local
  cohomology and `Ext` of finite modules both commute with it, and finite length of an
  `𝔪`-power-torsion module is the same over `A` and over `Â` — is a second route, and it does not
  need hypotheses (5) and (6) transferred to `Â`.

## References

* [Stacks Project, Tag 0DXU](https://stacks.math.columbia.edu/tag/0DXU)
* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ), the support and depth
  description of the dual Ext modules.
* [Stacks Project, Tag 090R](https://stacks.math.columbia.edu/tag/090R), depth modulo a
  nonzerodivisor.
* [Stacks Project, Tag 0EHH](https://stacks.math.columbia.edu/tag/0EHH), the criterion the tag's
  proof verifies.
-/

@[expose] public section

universe u

open IsLocalRing
open scoped Pointwise

namespace Stacks.RingTheory.PrincipalDivisorDepth

variable {A : Type u} [CommRing A]

/-- The local ring `A_𝔭` at a prime of `A`. -/
local notation "A[" p "]" => Localization.AtPrime (PrimeSpectrum.asIdeal p)

/-- **Hypothesis (5) of [Stacks, Tag 0DXU].** For every prime `𝔭` containing `f` and different
from the maximal ideal, `depth((A/fA)_𝔭) + dim(A/𝔭) > 1`.  The local ring `(A/fA)_𝔭` is written
as the localization at `𝔭` of the `A`-module `A/fA`; `localizedQuotientEquiv` identifies it with
`A_𝔭/fA_𝔭`. -/
abbrev DepthDimOnDivisor [IsLocalRing A] (f : A) : Prop :=
  ∀ p : PrimeSpectrum A, f ∈ p.asIdeal → p ≠ closedPoint A →
    (1 : WithBot ℕ∞) <
      (Module.depth A[p] (maximalIdeal A[p])
          (LocalizedModule.AtPrime p.asIdeal (A ⧸ Ideal.span {f})) : WithBot ℕ∞) +
        ringKrullDim (A ⧸ p.asIdeal)

/-- **Hypothesis (6) of [Stacks, Tag 0DXU].** For every prime `𝔭` not containing `f` whose
closed fibre `V(𝔭) ∩ V(f)` is not the single closed point, `depth(A_𝔭) + dim(A/𝔭) > 3`. -/
abbrev DepthDimOffDivisor [IsLocalRing A] (f : A) : Prop :=
  ∀ p : PrimeSpectrum A, f ∉ p.asIdeal →
    {r : PrimeSpectrum A | p.asIdeal ≤ r.asIdeal ∧ f ∈ r.asIdeal} ≠ {closedPoint A} →
    (3 : WithBot ℕ∞) <
      (Module.depth A[p] (maximalIdeal A[p]) A[p] : WithBot ℕ∞) + ringKrullDim (A ⧸ p.asIdeal)

/-! ### Hypothesis (6) places the relevant primes in `V(f)` -/

/-- **Stacks Project, Tag 0DXU (hypothesis (6) confines the support to `V(f)`).** Let `f` be an
element of a local ring `A` satisfying hypothesis (6), and let `𝔮` be a prime containing `f` and
different from the maximal ideal.  Then every prime `𝔭 ⊆ 𝔮` with
`depth(A_𝔭) + dim(A/𝔭) ≤ 3` contains `f`.

This is the source's "condition (6) tells us these primes are contained in `V(f)`", used twice:
for `dim(A/𝔮) = 2` with the primes of `depth(A_𝔭) + dim((A/𝔭)_𝔮) ≤ 1` supporting
`H^{-1}(ω^•_{A_𝔮})`, and for `dim(A/𝔮) = 1` with the primes of
`depth(A_𝔭) + dim((A/𝔭)_𝔮) ≤ 2` supporting `H^{-2}(ω^•_{A_𝔮})`.  In both cases
`dim(A/𝔭) = dim((A/𝔭)_𝔮) + dim(A/𝔮)`, so the two support conditions read
`depth(A_𝔭) + dim(A/𝔭) ≤ 3`, which is the single bound used here; `𝔮` itself is the point of
`V(𝔭) ∩ V(f)` other than `𝔪` that lets (6) apply. -/
@[stacks 0DXU "the step of the proof deducing from hypothesis (6) that a prime below a point \
of V(f) other than the closed point, whose depth plus dimension is at most 3, contains f — the \
source's 'condition (6) tells us these primes are contained in V(f)'"]
theorem mem_of_depth_add_ringKrullDim_le_three [IsLocalRing A] {f : A}
    (h6 : DepthDimOffDivisor f) {q p : PrimeSpectrum A} (hfq : f ∈ q.asIdeal)
    (hqm : q ≠ closedPoint A) (hpq : p.asIdeal ≤ q.asIdeal)
    (hle : (Module.depth A[p] (maximalIdeal A[p]) A[p] : WithBot ℕ∞) +
        ringKrullDim (A ⧸ p.asIdeal) ≤ 3) :
    f ∈ p.asIdeal := by
  by_contra hfp
  refine absurd hle (not_le.mpr (h6 p hfp ?_))
  intro hset
  have hmem : q ∈ {r : PrimeSpectrum A | p.asIdeal ≤ r.asIdeal ∧ f ∈ r.asIdeal} := ⟨hpq, hfq⟩
  rw [hset] at hmem
  exact hqm hmem

/-! ### The vanishing of multiplication by a power of `f` -/

/-- A finite module supported inside `V(f)` is annihilated by a power of `f`: the support is the
zero locus of the annihilator, so `f` lies in the radical of the annihilator. -/
theorem exists_pow_smul_eq_zero_of_support_subset {N : Type*} [AddCommGroup N] [Module A N]
    [Module.Finite A N] {f : A}
    (h : Module.support A N ⊆ PrimeSpectrum.zeroLocus (Ideal.span {f})) :
    ∃ c : ℕ, ∀ x : N, f ^ c • x = 0 := by
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at h
  obtain ⟨c, hc⟩ := h (Ideal.mem_span_singleton_self f)
  exact ⟨c, fun x => Module.mem_annihilator.mp hc x⟩

/-- Multiplication by `fⁿ`, as an `A`-linear map `N ⧸ fN → N ⧸ f^{n+1}N`.  This is the map the
source writes `f^{n-1} : H/fH → H/fⁿH`. -/
def mulPowQuotSMulTop (f : A) (N : Type u) [AddCommGroup N] [Module A N] (n : ℕ) :
    QuotSMulTop f N →ₗ[A] QuotSMulTop (f ^ (n + 1)) N :=
  Submodule.mapQ _ _ (LinearMap.lsmul A N (f ^ n)) (by
    intro x hx
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x f ⊤).mp hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ (f ^ (n + 1)) ⊤).mpr
      ⟨y, Submodule.mem_top, ?_⟩
    rw [LinearMap.lsmul_apply, smul_smul, pow_succ])

/-- `mulPowQuotSMulTop f N n` sends the class of `x` in `N ⧸ fN` to the class of `fⁿ • x` in
`N ⧸ f^{n+1}N`. -/
@[simp]
theorem mulPowQuotSMulTop_mk (f : A) {N : Type u} [AddCommGroup N] [Module A N] (n : ℕ) (x : N) :
    mulPowQuotSMulTop f N n (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (f ^ n • x) : QuotSMulTop (f ^ (n + 1)) N) := rfl

/-- If `f^c` annihilates `N` then `fⁿ : N ⧸ fN → N ⧸ f^{n+1}N` is zero for every `n ≥ c`. -/
theorem mulPowQuotSMulTop_eq_zero {f : A} {N : Type u} [AddCommGroup N] [Module A N] {c : ℕ}
    (hc : ∀ x : N, f ^ c • x = 0) {n : ℕ} (hn : c ≤ n) :
    mulPowQuotSMulTop f N n = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mulPowQuotSMulTop_mk, LinearMap.zero_apply]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h0 : f ^ (c + d) • y = 0 := by
    rw [pow_add, mul_comm (f ^ c) (f ^ d), mul_smul, hc, smul_zero]
  rw [h0]
  exact Submodule.Quotient.mk_zero _

/-- **Stacks Project, Tag 0DXU (the vanishing for `n` large enough).** Let `f` be an element of
a local ring `A` satisfying hypothesis (6), let `𝔮` be a prime containing `f` and different from
the maximal ideal, and let `N` be a finite `A`-module every prime of whose support lies below
`𝔮` and has `depth(A_𝔭) + dim(A/𝔭) ≤ 3`.  Then the maps `fⁿ : N ⧸ fN → N ⧸ f^{n+1}N` vanish for
all large `n`.

This is the conclusion of both of the source's two remaining cases.  There `N` is
`H^{-1}(ω^•_{A_𝔮})` when `dim(A/𝔮) = 2` and `H^{-2}(ω^•_{A_𝔮})` when `dim(A/𝔮) = 1`, each a
finite module whose support [Stacks, Tag 0DWZ] describes by a depth-plus-dimension bound; the
hypothesis (6) step `mem_of_depth_add_ringKrullDim_le_three` puts that support inside `V(f)`,
which makes `f` nilpotent on `N`, and the source's "thus the desired vanishing for `n` large
enough" is the vanishing below. -/
@[stacks 0DXU "the step of the proof concluding, for a finite module whose support hypothesis \
(6) places in V(f), that multiplication by fⁿ from N/fN to N/f^(n+1)N vanishes for all large n \
— the source's 'thus the desired vanishing for n large enough', in both the dim(A/q) = 2 and \
the dim(A/q) = 1 case"]
theorem exists_mulPowQuotSMulTop_eq_zero_of_depthDimOffDivisor [IsLocalRing A] {f : A}
    (h6 : DepthDimOffDivisor f) {q : PrimeSpectrum A} (hfq : f ∈ q.asIdeal)
    (hqm : q ≠ closedPoint A) (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hsupp : ∀ p ∈ Module.support A N, p.asIdeal ≤ q.asIdeal ∧
      (Module.depth A[p] (maximalIdeal A[p]) A[p] : WithBot ℕ∞) +
        ringKrullDim (A ⧸ p.asIdeal) ≤ 3) :
    ∃ c : ℕ, ∀ n, c ≤ n → mulPowQuotSMulTop f N n = 0 := by
  obtain ⟨c, hc⟩ := exists_pow_smul_eq_zero_of_support_subset (f := f) (N := N) fun p hp => by
    obtain ⟨hpq, hle⟩ := hsupp p hp
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem]
    exact mem_of_depth_add_ringKrullDim_le_three h6 hfq hqm hpq hle
  exact ⟨c, fun n hn => mulPowQuotSMulTop_eq_zero hc hn⟩

/-! ### `(A/fA)_𝔭 = A_𝔭/fA_𝔭` -/

/-- The localization at `𝔭` of the submodule `fA ⊆ A` is the submodule `fA_𝔭 ⊆ A_𝔭`. -/
theorem localized'_span_singleton (f : A) (p : PrimeSpectrum A) :
    (Ideal.span {f} : Submodule A A).localized' A[p] p.asIdeal.primeCompl
        (Algebra.linearMap A A[p]) =
      (algebraMap A A[p] f) • (⊤ : Submodule A[p] A[p]) := by
  rw [Submodule.localized'_eq_span, ← Submodule.ideal_span_singleton_smul,
    Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro - ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
    exact Ideal.mem_span_singleton.mpr ⟨algebraMap A A[p] c, by simp⟩
  · rintro - rfl
    exact Submodule.subset_span ⟨f, Ideal.mem_span_singleton_self f, rfl⟩

/-- The identification `(A/fA)_𝔭 = A_𝔭/fA_𝔭`: the localization of `A/fA` at `𝔭` is the quotient
of `A_𝔭` by `fA_𝔭`.  Both are localizations at `𝔭` of the `A`-module `A/fA`, the second by
`Submodule.toLocalizedQuotient'`, so they agree. -/
noncomputable def localizedQuotientEquiv (f : A) (p : PrimeSpectrum A) :
    LocalizedModule.AtPrime p.asIdeal (A ⧸ Ideal.span {f}) ≃ₗ[A[p]]
      QuotSMulTop (algebraMap A A[p] f) A[p] :=
  have := IsLocalization.linearMap_compatibleSMul (S := A[p]) p.asIdeal.primeCompl
  ((IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (A ⧸ Ideal.span {f}))
      ((Ideal.span {f} : Submodule A A).toLocalizedQuotient' A[p] p.asIdeal.primeCompl
        (Algebra.linearMap A A[p]))).restrictScalars A[p]).trans
    (Submodule.quotEquivOfEq _ _ (localized'_span_singleton f p))

/-- The depth of `(A/fA)_𝔭` is the depth of `A_𝔭/fA_𝔭`, the two being isomorphic. -/
theorem depth_localizedModule_quotient_eq (f : A) (p : PrimeSpectrum A) :
    Module.depth A[p] (maximalIdeal A[p])
        (LocalizedModule.AtPrime p.asIdeal (A ⧸ Ideal.span {f})) =
      Module.depth A[p] (maximalIdeal A[p]) (QuotSMulTop (algebraMap A A[p] f) A[p]) :=
  Module.depth_eq_depth_of_linearEquiv _ (localizedQuotientEquiv f p)

/-! ### The depth of `A_𝔮` at a point of `V(f)` -/

/-- A nonzerodivisor of `A` is a nonzerodivisor of every localization `A_𝔭`. -/
theorem isSMulRegular_localization {f : A} (hf : f ∈ nonZeroDivisors A) (p : PrimeSpectrum A) :
    IsSMulRegular A[p] (algebraMap A A[p] f) := by
  refine IsSMulRegular.of_isLocalization (p := p.asIdeal.primeCompl) _ (fun x y hxy => ?_)
  simp only [smul_eq_mul] at hxy
  refine sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hf).1 (x - y) ?_)
  rw [mul_sub, hxy, sub_self]

/-- Dividing `A_𝔮` by the nonzerodivisor `f ∈ 𝔮` lowers its depth by exactly one. -/
private theorem depth_quotSMulTop_add_one_eq_depth_localization [IsNoetherianRing A] {f : A}
    (hf : f ∈ nonZeroDivisors A) {q : PrimeSpectrum A} (hfq : f ∈ q.asIdeal) :
    Module.depth A[q] (maximalIdeal A[q]) (QuotSMulTop (algebraMap A A[q] f) A[q]) + 1 =
      Module.depth A[q] (maximalIdeal A[q]) A[q] :=
  (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
    (maximalIdeal A[q]) A[q]).1 _
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff A[q] q.asIdeal f).mpr hfq)
    (isSMulRegular_localization hf q)

/-- **Stacks Project, Tag 0DXU (`depth(A_𝔮) ≥ 1` because `f` is a nonzerodivisor).** For `f` a
nonzerodivisor of a Noetherian ring `A` and `𝔮` a prime containing `f`, the local ring `A_𝔮` has
depth at least one.

This is the source's "`H^0(ω^•_{A_𝔮}) = 0` because `depth(A_𝔮) ≥ 1` as `f` is a
nonzerodivisor", the input to the case `dim(A/𝔮) = 2`: the image of `f` in `A_𝔮` lies in the
maximal ideal and is still a nonzerodivisor, so it is a regular sequence of length one, and
[Stacks, Tag 090R] gives `depth(A_𝔮) = depth(A_𝔮/fA_𝔮) + 1 ≥ 1`. -/
@[stacks 0DXU "the step of the proof asserting that A_q has depth at least 1 for a prime q \
containing the nonzerodivisor f, which is what makes H^0 of the dualizing complex of A_q vanish \
in the case dim(A/q) = 2"]
theorem one_le_depth_localization [IsNoetherianRing A] {f : A} (hf : f ∈ nonZeroDivisors A)
    {q : PrimeSpectrum A} (hfq : f ∈ q.asIdeal) :
    1 ≤ Module.depth A[q] (maximalIdeal A[q]) A[q] := by
  rw [← depth_quotSMulTop_add_one_eq_depth_localization hf hfq]
  exact le_add_self

/-- If `A_𝔮/fA_𝔮` has depth at least one then `A_𝔮` has depth at least two. -/
theorem two_le_depth_localization [IsNoetherianRing A] {f : A} (hf : f ∈ nonZeroDivisors A)
    {q : PrimeSpectrum A} (hfq : f ∈ q.asIdeal)
    (h : 1 ≤ Module.depth A[q] (maximalIdeal A[q]) (QuotSMulTop (algebraMap A A[q] f) A[q])) :
    2 ≤ Module.depth A[q] (maximalIdeal A[q]) A[q] := by
  rw [← depth_quotSMulTop_add_one_eq_depth_localization hf hfq]
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ _ := add_le_add h le_rfl

/-- **Stacks Project, Tag 0DXU (`depth(A_𝔮) ≥ 2` when `dim(A/𝔮) = 1`).** Let `f` be a
nonzerodivisor of a Noetherian local ring `A` satisfying hypothesis (5), and let `𝔮` be a prime
containing `f`, different from the maximal ideal, with `dim(A/𝔮) = 1`.  Then `A_𝔮` has depth at
least two.

This is the source's "if `dim(A/𝔮) = 1`, then condition (5) combined with the fact that `f` is a
nonzerodivisor insures that `A_𝔮` has depth at least `2`", which is what makes both
`H^0(ω^•_{A_𝔮})` and `H^{-1}(ω^•_{A_𝔮})` vanish in that case.  Hypothesis (5) at `𝔮` reads
`depth((A/fA)_𝔮) + 1 > 1`, so `(A/fA)_𝔮 = A_𝔮/fA_𝔮` has depth at least one, and
[Stacks, Tag 090R] adds the one coming from the nonzerodivisor `f`. -/
@[stacks 0DXU "the step of the proof asserting that A_q has depth at least 2 when \
dim(A/q) = 1, deduced from hypothesis (5) at q together with f being a nonzerodivisor"]
theorem two_le_depth_localization_of_depthDimOnDivisor [IsNoetherianRing A] [IsLocalRing A]
    {f : A} (hf : f ∈ nonZeroDivisors A) (h5 : DepthDimOnDivisor f) {q : PrimeSpectrum A}
    (hfq : f ∈ q.asIdeal) (hqm : q ≠ closedPoint A)
    (hdim : ringKrullDim (A ⧸ q.asIdeal) = 1) :
    2 ≤ Module.depth A[q] (maximalIdeal A[q]) A[q] := by
  refine two_le_depth_localization hf hfq ?_
  have h := h5 q hfq hqm
  rw [hdim, depth_localizedModule_quotient_eq] at h
  rcases eq_or_ne (Module.depth A[q] (maximalIdeal A[q])
    (QuotSMulTop (algebraMap A A[q] f) A[q])) 0 with h0 | h0
  · rw [h0] at h
    simp at h
  · exact ENat.one_le_iff_ne_zero.mpr h0

/-! ### The dimension formula along a pair of primes -/

/-- **The dimension of `A ⧸ 𝔭` splits at a prime `𝔮 ⊇ 𝔭`.**  Over a Noetherian local universally
catenary ring, for primes `𝔭 ⊆ 𝔮`,

  `dim(A/𝔭) = dim((A/𝔭)_𝔮) + dim(A/𝔮)`.

This is the source's "`dim((A/𝔭)_𝔮) = dim(A/𝔭) - 2`" of [Stacks, Tag 0DXU], where `𝔮` runs over
the primes of `V(f)` with `dim(A/𝔮) = 2`; the general identity is what carries a support bound
expressed over `A_𝔮` back to the bound over `A` that hypothesis (6) constrains.

The quotient `A/𝔭` is a Noetherian local domain, so `⊥` is its only minimal prime and its
spectrum is trivially equidimensional; catenarity of `A/𝔭` makes coheight drop by exactly one
along covering pairs, and `FlatLocalCatenary.height_add_coheight_eq` then says that
`height(Q) + coheight(Q) = coheight(⊥) = dim(A/𝔭)` for `Q` the image of `𝔮`.  The height of `Q`
is the dimension of `(A/𝔭)_𝔮` and its coheight is `dim(A/𝔮)`. -/
@[ega "IV 10.7.2" "more general"]
theorem ringKrullDim_quotient_eq_ringKrullDim_localization_add [IsNoetherianRing A] [IsLocalRing A]
    (hcat : Ring.IsUniversallyCatenary A) (p q : Ideal A) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q)
    [hQp : (q.map (Ideal.Quotient.mk p)).IsPrime] :
    ringKrullDim (A ⧸ p) =
      ringKrullDim (Localization.AtPrime (q.map (Ideal.Quotient.mk p))) +
        ringKrullDim (A ⧸ q) := by
  have : Nontrivial (A ⧸ p) := Submodule.Quotient.nontrivial_iff.mpr ‹p.IsPrime›.ne_top
  have : IsLocalRing (A ⧸ p) :=
    .of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType A (A ⧸ p) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A p) Ideal.Quotient.mk_surjective
  have hcatD : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum (A ⧸ p)) :=
    Ring.isCatenary_iff_isCatenarySpace_primeSpectrum.mp (hcat (A ⧸ p))
  have hequi : SpecEquidimensional (A ⧸ p) := by
    intro r hr s hs
    rw [IsDomain.minimalPrimes_eq_singleton_bot] at hr hs
    rw [hr, hs]
  have hbot : (⊥ : Ideal (A ⧸ p)) ∈ minimalPrimes (A ⧸ p) := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot]; rfl
  have hkey := FlatLocalCatenary.height_add_coheight_eq
    (FlatLocalCatenary.coheight_covBy_of_isCatenarySpace hcatD) hequi
    (⟨q.map (Ideal.Quotient.mk p), hQp⟩ : PrimeSpectrum (A ⧸ p))
    (⟨⊥, inferInstance⟩ : PrimeSpectrum (A ⧸ p)) hbot
  -- the coheight of `⊥` is `dim(A/𝔭)`
  have hbotdim : (Order.coheight (⟨⊥, inferInstance⟩ : PrimeSpectrum (A ⧸ p)) : WithBot ℕ∞) =
      ringKrullDim (A ⧸ p) := by
    rw [coheight_eq_ringKrullDim_quotient]
    exact ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (A ⧸ p))
  -- the coheight of the image of `𝔮` is `dim(A/𝔮)`
  have hQdim : (Order.coheight (⟨q.map (Ideal.Quotient.mk p), hQp⟩ : PrimeSpectrum (A ⧸ p))
      : WithBot ℕ∞) = ringKrullDim (A ⧸ q) := by
    rw [coheight_eq_ringKrullDim_quotient]
    exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hpq)
  -- the height of the image of `𝔮` is `dim((A/𝔭)_𝔮)`
  have hQheight : (Order.height (⟨q.map (Ideal.Quotient.mk p), hQp⟩ : PrimeSpectrum (A ⧸ p))
      : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime (q.map (Ideal.Quotient.mk p))) := by
    rw [← PrimeSpectrum.height_eq_orderHeight]
    exact (IsLocalization.AtPrime.ringKrullDim_eq_height (q.map (Ideal.Quotient.mk p)) _).symm
  rw [← hbotdim, ← hQdim, ← hQheight, ← WithBot.coe_add, hkey]

/-- **The support bound of [Stacks, Tag 0DWZ] over `A_𝔮`, read back over `A`.**  If
`depth(A_𝔭) + dim((A/𝔭)_𝔮) ≤ s` and `dim(A/𝔮) = d`, then `depth(A_𝔭) + dim(A/𝔭) ≤ s + d`.

This is the step of the proof of [Stacks, Tag 0DXU] that turns the depth-plus-dimension bound in
which [Stacks, Tag 0DWZ] describes the support of `H^{-1}(ω^•_{A_𝔮})` and `H^{-2}(ω^•_{A_𝔮})`
into the single bound `depth(A_𝔭) + dim(A/𝔭) ≤ 3` that hypothesis (6) refutes off `V(f)`: at
`dim(A/𝔮) = 2` the source's bound is `≤ 1` and at `dim(A/𝔮) = 1` it is `≤ 2`, and both become
`≤ 3`. -/
theorem depth_add_ringKrullDim_quotient_le [IsNoetherianRing A] [IsLocalRing A]
    (hcat : Ring.IsUniversallyCatenary A) (p q : Ideal A) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q)
    [hQp : (q.map (Ideal.Quotient.mk p)).IsPrime] (s d : ℕ)
    (hd : ringKrullDim (A ⧸ q) = (d : WithBot ℕ∞))
    (hle : (Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p) : WithBot ℕ∞) +
        ringKrullDim (Localization.AtPrime (q.map (Ideal.Quotient.mk p))) ≤ (s : WithBot ℕ∞)) :
    (Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) : WithBot ℕ∞) + ringKrullDim (A ⧸ p) ≤
      ((s + d : ℕ) : WithBot ℕ∞) := by
  rw [ringKrullDim_quotient_eq_ringKrullDim_localization_add hcat p q hpq, hd,
    ← add_assoc, Nat.cast_add]
  exact add_le_add hle le_rfl

end Stacks.RingTheory.PrincipalDivisorDepth

end
