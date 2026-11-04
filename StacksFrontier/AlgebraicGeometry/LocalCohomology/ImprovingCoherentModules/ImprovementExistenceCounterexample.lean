module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModulesStalkSequenceColimit
public import StacksFrontier.Algebra.Module.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaConicIntersection
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.Improvement
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenaryExamples
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Specialization
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.FormalFibres.SerreConditionOne
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.MvPolynomial.VariablesRegular
public import StacksFrontier.RingTheory.Depth.FlatFibreAssociatedPrime
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Depth.Nakayama
public import StacksFrontier.RingTheory.Depth.ShortExact
public import StacksFrontier.RingTheory.Regular.AscentAlongRegularRingHom
public import StacksFrontier.RingTheory.RegularLocalRing.MaximalCohenMacaulay
public import StacksFrontier.RingTheory.Serre.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The obstruction refuting the existence clause of [Stacks, Tag 0DX5]

The existence assertion of [Stacks, Tag 0DX5] — that every coherent module `F` on a Noetherian,
universally catenary scheme with `(S₁)` formal fibres admits a map `F → F''` which is an
isomorphism on stalks off a closed subset `Z`, surjective with target of depth one at the points
of `Z` reached by an immediate specialization from an associated point outside `Z`, and of depth
at least two at the remaining points of `Z` — is false. A counterexample is
`X = Spec k[u, v, w]`, `Z = V(u, v)` and `F = (u, v)~ ⊕ (k[u, v, w]/(u, w))~`; the prose argument
is recorded in the module
`StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ImprovementExistence`,
and the sharp criterion under which the assertion *does* hold is
`AlgebraicGeometry.existsUnique_improvement_of_disjoint_closure_lowDepthNotReached`.

This module proves that refutation unconditionally: its ring-theoretic heart, then the statement
about `AlgebraicGeometry.IsImprovement` itself, and then the five facts about `k[u, v, w]` that
instantiate it. Write `𝔭 = (u, v)`, so that
`R = k[u, v, w]_𝔭` is a two-dimensional regular local ring and `F_𝔭` is its maximal ideal `𝔪`
(the second summand dies at `𝔭` because `w ∉ 𝔭`). Condition (2) of the source at the closed point
`(u, v, w)` localizes to a surjection `𝔪 ↠ F''_𝔭`, while condition (3) at `𝔭`, which is *not*
reached from outside `Z`, demands `depth F''_𝔭 ≥ 2 = dim R`. The two are incompatible:

* a module of depth `dim R` over a regular local ring is free ([Stacks, Tag 00NT], available here
  as `regular_mcm_free`), and
* the maximal ideal of a regular local ring of dimension at least two admits no surjection onto a
  nonzero free module, because such a surjection splits the inclusion `𝔪 ⊆ R` and a split ideal is
  principal, whereas `𝔪` needs `dim R` generators.

The same obstruction can be read off the depth alone: `depth_𝔪(𝔪) = 1` whenever `R` has positive
depth, so `𝔪` itself already violates condition (3) at `𝔭`.

## Main results

* `Stacks.ImprovementCounterexample.isPrincipal_of_linearMap_eq_one`: an ideal carrying a linear
  map to the ring which hits `1` is principal.
* `Stacks.ImprovementCounterexample.not_isPrincipal_maximalIdeal`: the maximal ideal of a regular
  local ring of dimension at least two is not principal.
* `Stacks.ImprovementCounterexample.not_surjective_of_free`: over a regular local ring of
  dimension at least two there is no surjection from the maximal ideal onto a nonzero free module.
* `Stacks.ImprovementCounterexample.depth_maximalIdeal_eq_one`: the maximal ideal of a Noetherian
  local ring of positive depth has depth exactly one as a module.
* `Stacks.ImprovementCounterexample.not_exists_two_le_depth_quotient_maximalIdeal`: the
  incompatibility itself — over a regular local ring of dimension two, no quotient of the maximal
  ideal has depth at least two. This is the obstruction the three conditions of the source run
  into at `𝔭`.
* `Stacks.ImprovementCounterexample.associatedPrimes_prod_quotient_eq`: the associated primes of
  `I ⊕ R/𝔮` over a Noetherian domain are `{(0), 𝔮}`, which is the computation placing the
  associated points of `F` off `Z` in the counterexample.
* `Stacks.ImprovementCounterexample.epi_stalkFunctor_map_of_specializes`: epimorphy of a stalk map
  of `𝒪_X`-modules with quasi-coherent target transports to every generalization of the point.
  This is what carries condition (2) from the closed point to `𝔭`.
* `Stacks.ImprovementCounterexample.nontrivial_stalk_of_specializes`: a nontrivial stalk stays
  nontrivial at a specialization, which is what keeps the target from vanishing at `𝔭`.
* `Stacks.ImprovementCounterexample.not_isImprovement_of_linearEquiv_maximalIdeal`: **the
  refutation at the scheme level.** No map out of `F` is an improvement along `Z`, given the three
  points `(0) ⤳ 𝔭 ⤳ (u, v, w)` of the counterexample, the regularity and dimension of `𝒪_{X,𝔭}`,
  the identification `F_𝔭 ≅ 𝔪_𝔭` and the nonvanishing of `F` at the generic point.
* `Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf`: **the refutation,
  unconditionally.** For `X = Spec k[u, v, w]`, `Z = V(u, v)` and
  `F = (u, v)~ ⊕ (k[u, v, w]/(u, w))~` there is no `G` and no `F ⟶ G` which is an improvement of
  `F` along `Z`.
* `Stacks.ImprovementCounterexample.isCoherent_cexSheaf`,
  `Stacks.ImprovementCounterexample.isClosed_cexZ`,
  `Stacks.ImprovementCounterexample.isUniversallyCatenary_cexScheme` and
  `Stacks.ImprovementCounterexample.hasSerreCondition_one_formalFibres_cexScheme`: `F` is
  coherent, `Z` is closed, `X` is universally catenary and the local rings of `X` have `(S₁)`
  formal fibres — four of the five hypotheses the source places on its data, the fifth being
  Noetherianity of `X`, which is an instance. They are witnessed so that the refutation is one of
  the source's own assertion rather than of a strengthening of it; see "Which of the source's
  hypotheses are witnessed here" below.

The five facts instantiating the scheme-level statement at `k[u, v, w]` are

* `Stacks.ImprovementCounterexample.cexPt_mem_cexZ` and
  `Stacks.ImprovementCounterexample.cexPt_notMem_cexZ`: which of the three points lie in
  `Z = V(u, v)`.
* `Stacks.ImprovementCounterexample.isAssociatedPoint_cexSheaf_iff`: `Ass(F) = {(0), (u, w)}`,
  and from it `Stacks.ImprovementCounterexample.reachedFromOutside_cexSheaf_uvw` and
  `Stacks.ImprovementCounterexample.not_reachedFromOutside_cexSheaf_uv`.
* `Stacks.ImprovementCounterexample.isRegularLocalRing_stalk_cexPt` and
  `Stacks.ImprovementCounterexample.ringKrullDim_stalk_cexPt`: the local ring at the prime
  generated by a set of variables is regular of dimension the size of that set.
* `Stacks.ImprovementCounterexample.linearEquiv_stalk_cexSheaf_maximalIdeal`: `F_𝔭 ≅ 𝔪_𝔭`.
* `Stacks.ImprovementCounterexample.nontrivial_stalk_cexSheaf_generic`: `F_{(0)} ≠ 0`.

The ring theory of `k[u, v, w]` these rest on is

* `Stacks.ImprovementCounterexample.height_span_image_X`: the height of the ideal generated by a
  finite set of variables of a polynomial ring over a Noetherian domain is the size of that set.
  Primality of that ideal is `Stacks.Examples.HironakaConicIntersection.isPrime_span_image_X`.
* `Stacks.ImprovementCounterexample.covBy_varPrime_uw_uvw`: `(u, w) ⋖ (u, v, w)`.
* `Stacks.ImprovementCounterexample.isLocalizedModule_comp_fst`: a summand annihilated by an
  element outside the prime does not survive localization.

## Implementation notes

The splitting argument is the one-line identity `b = a · f(b)` for `b` in an ideal `I` carrying
`f : I →ₗ[R] R` with `f(a) = 1`, valid because `b • a = a • b` inside `I`; no domain hypothesis and
no choice of a complement are needed. Non-principality of `𝔪` is read off the definition of
`IsRegularLocalRing`, through `IsLocalRing.finrank_cotangentSpace_le_one_iff` and
`IsRegularLocalRing.iff_finrank_cotangentSpace`.

`depth_𝔪(𝔪) = 1` is the second and third inequalities of [Stacks, Tag 00LX]
(`Module.min_depth_le_depth_of_exact`) applied to `0 → 𝔪 → R → R/𝔪 → 0`, together with
`depth_𝔪(R/𝔪) = 0`, which is `Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes` and
`associatedPrimes.eq_singleton_of_isPrimary`.

Freeness of a depth-two module is `regular_mcm_free`, whose maximal Cohen–Macaulay hypothesis is
phrased by a regular sequence of length `dim R`; the sequence is produced from the depth by part
(2) of [Stacks, Tag 090R], `Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append`,
started at the empty sequence.

**Transporting condition (2) down to a generalization.** The conditions of
`AlgebraicGeometry.IsImprovement` are stated on `TopCat.Presheaf.stalkFunctor Ab`, and Mathlib's
`TopCat.Presheaf.stalkSpecializes_stalkFunctor_map` is the naturality square for exactly that
functor against the comparison of stalks at a specialization. Together with
`Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes`, which exhibits the
stalk at a generalization as a localization, it turns surjectivity at a point into surjectivity at
every generalization: divide a preimage by the scalar that the localization produces, which is a
unit in the local ring at the generalization. Mathlib's `⤳` has the generalization on the left, so
the specialization used here is `𝔭 ⤳ (u, v, w)`.

**Two spellings of the module structure on a stalk.** `AlgebraicGeometry.IsImprovement` states its
depth conditions against `PresheafOfModules.instModuleCarrier…`, the Mathlib instance on
`TopCat.Presheaf.stalk F.val.presheaf x`, while the localization results are stated against
`Stacks.ModuleStalkSpecialization.stalkModule`, the same term read on
`AlgebraicGeometry.Scheme.Modules.presheaf`. The two are definitionally equal but neither
spelling's instance is found by search for the other, so the stalk map is assembled here as a
linear map in the second spelling, its semilinearity taken from
`Stacks.ModuleSkyscraper.modulesStalkFunctor` — the `ModuleCat`-valued stalk functor, whose action
on morphisms is `AlgebraicGeometry.stalkMapLinear` by `rfl`. That is the only crossing, and it is
the reason the `let`-bound linear maps appear in the two proofs below.

**Why nontriviality has to be imported from the generic point.** This library gives a vanishing
module depth `⊤`, so condition (3) holds at `𝔭` for a trivial reason as soon as `F''_𝔭 = 0`; a
statement of the refutation without a nonvanishing input is therefore false. The input used is
condition (1) at the generic point `(0) ∉ Z`, where the map is an isomorphism on stalks, carried to
`𝔭` by [Stacks, Tag 05AC] (`AlgebraicGeometry.Scheme.Modules.stableUnderSpecialization_supp`).

**The ideals generated by variables.** `(u)`, `(u, v)`, `(u, w)` and `(u, v, w)` are the ideals
`Ideal.span (MvPolynomial.X '' ↑s)` for `s : Finset (Fin 3)`. Primality is
`Stacks.Examples.HironakaConicIntersection.isPrime_span_image_X`, which reads it off the kernel
of the retraction killing the variables in `s`, and is not reproved here. The height is `s.card`:
at most by Krull's height theorem (`Ideal.height_le_card_of_mem_minimalPrimes_span`), and at
least by the chain of the initial segments of `s`, each inclusion strict because a variable
outside `s` is outside the ideal (`MvPolynomial.mem_ideal_span_X_image`).

That gives the covering `(u, w) ⋖ (u, v, w)` — a prime strictly between would have height at
least `2 + 1` and at most `3 - 1` — and hence the immediacy of that specialization through
`immediateSpec_iff_covby`, which reduces `IsImmediateSpecialization` on a prime spectrum to the
covering relation. Non-immediacy of `(0) ⤳ (u, v)` is the chain `(0) ⊊ (u) ⊊ (u, v)`.

**Points of `Spec R` versus primes of `R`.** Instance search cannot see a term of
`PrimeSpectrum R` as a point of the carrier of `Spec R` without unfolding `Spec`, so the stalk
statements are phrased with `Stacks.ImprovementCounterexample.cexPt`, the point named at the
scheme's own type, and the ideal statements with
`Stacks.ImprovementCounterexample.varPrime`. For the same reason the order on `PrimeSpectrum R`
and the specialization order on the carrier of `Spec R`, definitionally the same but two
distinct instances, are bridged by
`Stacks.ImprovementCounterexample.not_isImmediateSpecialization_of_lt_of_lt` and
`Stacks.ImprovementCounterexample.asIdeal_le_asIdeal_of_isImmediateSpecialization`.

**How `F_𝔭 ≅ 𝔪_𝔭` is obtained.** `AlgebraicGeometry.StructureSheaf.toStalkₗ` presents `F_𝔭` as
the localization of `(u, v) ⊕ k[u, v, w]/(u, w)` at `𝔭`,
`AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk` presents `𝒪_{X,𝔭}` as the
localization of `k[u, v, w]`, and `Submodule.toLocalized'` presents the localization of the ideal
`(u, v)` inside it, which is `𝔭 · 𝒪_{X,𝔭} = 𝔪_𝔭` by `IsLocalization.map_under`. The
projection killing the second summand is again a localization map because `w ∉ 𝔭` annihilates
`k[u, v, w]/(u, w)` (`Stacks.ImprovementCounterexample.isLocalizedModule_comp_fst`), so
`IsLocalizedModule.linearEquiv` identifies the two localizations, and the resulting
`k[u, v, w]`-linear isomorphism is automatically `𝒪_{X,𝔭}`-linear by
`LinearEquiv.extendScalarsOfIsLocalization`. The scalar tower that needs is `rfl`: the
`k[u, v, w]`-action on the stalk of `M~` is by definition the `𝒪_{X,𝔭}`-action along
`AlgebraicGeometry.StructureSheaf.toStalk`.

`Ass(F) = {(0), (u, w)}` is `associatedPrimes_prod_quotient_eq` carried to the sheaf by the
affine comparison of [Stacks, Tag 02OK], `Stacks.LocalCohomology.isAssociatedPoint_tilde_iff`,
with the two spellings of an associated prime reconciled by
`Stacks.Depth.isAssociatedPrimeStacks_iff_mem_associatedPrimes`.

Nothing here is tagged. These lemmas show that the existence clause of [Stacks, Tag 0DX5] fails
as stated. Its corrected form, at exactly the source's hypotheses, is registered in
`CorrectedImprovement.lean` of this directory as
`AlgebraicGeometry.exists_isImprovement_iff_two_le_depth_depthOneQuotient` (existence holds if and
only if the depth-one quotient has depth two at the points generalizing a reached point without
being one, which fails here at `(u, v)`) and
`AlgebraicGeometry.existsUnique_isCorrectedImprovement` (the conditions corrected at those points,
existence and uniqueness).

## Which of the source's hypotheses are witnessed here

The refutation theorem below is unconditional: it quantifies over all `G` and all `F ⟶ G` and
assumes nothing. What needs separate checking is the *other* direction — that `X`, `Z` and `F` are
a legitimate instance of [Stacks, Tag 0DX5], so that what is refuted is the source's assertion at
the source's own hypotheses. All five are machine-checked:

* **`F` coherent** — `Stacks.ImprovementCounterexample.isCoherent_cexSheaf`.
* **`Z` closed** — `Stacks.ImprovementCounterexample.isClosed_cexZ`.
* **`X` Noetherian** — `IsNoetherian (cexScheme k)`, by instance search.
* **`X` universally catenary** —
  `Stacks.ImprovementCounterexample.isUniversallyCatenary_cexScheme`.
* **the local rings of `X` have `(S₁)` formal fibres** —
  `Stacks.ImprovementCounterexample.hasSerreCondition_one_formalFibres_cexScheme`, stated in the
  shape every consumer in this library takes it, the `hFibres` binder of the sharp true form
  `AlgebraicGeometry.existsUnique_improvement_of_disjoint_closure_lowDepthNotReached` among them.

Both of the last two come from one input, `Stacks.ImprovementCounterexample.isExcellent_cexRing`:
`k[u, v, w]` is a finite-type algebra over a field, hence excellent ([Stacks, Tag 07QW]), and an
excellent ring is universally catenary and a G-ring. Universal catenarity of the *scheme* is then
`AlgebraicGeometry.Scheme.isUniversallyCatenary_spec`; `Spec` of a Noetherian universally
catenary ring is universally catenary, which is the affine case of [Stacks, Tag 02JB] part (1).

The `(S₁)` formal fibres run through `hasSerreCondition_one_formalFibres_of_isGRing_localization`,
added to `StacksFrontier.RingTheory.FormalFibres.SerreConditionOne` for this: being a G-ring is
geometric regularity of the formal fibres of each localization ([Stacks, Tag 07GH] through
`Stacks.GRing.formalFibersHaveAt_iff_isRegularRingHom`), a geometrically regular fibre is regular
when the test extension is the residue field itself, and a regular ring satisfies every `(Sₙ)`
(`HasSerreCondition.of_isRegularRing`). Before this, every result in that file merely
*propagated* the condition — along an essentially-finite-type map, along a surjection, through the
axioms of [Stacks, Tag 0BIV] — and nothing established it for a concrete ring.

No computation of `AlgebraicGeometry.Scheme.completedLocalRing` at a point of an affine scheme is
needed to cross from the ring statement to the scheme one. That constant is by definition the
adic completion of the stalk at its maximal ideal, so the scheme-level hypothesis *is* the
ring-level statement at the stalk; all that is required is the stalk's presentation as a
localization, which is Mathlib's `AlgebraicGeometry.Spec.stalkIso`, and the ring-level lemma takes
that isomorphism as an argument rather than demanding `IsGRing` of the stalk itself.

## The source's own proof, checked against this refutation

Two objections could rescue [Stacks, Tag 0DX5]'s existence clause, and both were checked against
the source text rather than against a paraphrase of it.

*Does clause (2) assert `depth = 1` or `depth ≥ 1`?*  The source asserts EQUALITY:
"is surjective and `depth(F''_x) = 1`", with the inequality appearing only in clause (3).
`AlgebraicGeometry.IsImprovement` matches this, with `= (1 : ℕ∞)` in clause (2) and
`(2 : ℕ∞) ≤ _` in clause (3).  The refutation is unaffected either way, because it consumes only
the surjectivity half of clause (2) and derives its contradiction from clause (3).

*Does the source derive 0DX5 from [Stacks, Tag 0EI3] or [Stacks, Tag 0EI4], perhaps with a subset
`T'` for which those lemmas' immediate-specialization hypotheses hold?*  No.  Neither tag is used
in the proof; 0EI3 appears on the page only as the next-lemma link and 0EI4 not at all.  The cited
inputs are Tags 0DX3, 0E9I, 0DWY, 0AWB, 0DX4 and 0338.  So there is no alternative choice of
subset that evades the counterexample.

The source's existence argument instead takes `Ass(F') = {x_1, …, x_n}`, lets `Z_{i,j}` be the
irreducible components of `Z ∩ Y_i` with `Y_i` the closure of `x_i`, and for those with
`d_{i,j} = 1` invokes Tag 0DWY for a neighbourhood `V_{i,j}` on which the depth is at least two at
the nearby points *of `Z_{i,j}`*; it then removes all of `Z ∩ V_{i,j}`.  That is precisely the step
this module refutes: the removal is blind to the generic points of the *other* components, and in
the counterexample `(u, v)` lies on a component with `d = 2`, is a generalization of the `d = 1`
point `(u, v, w)`, and so lies in every neighbourhood of it.

## References

* [Stacks Project, Tag 0DX5](https://stacks.math.columbia.edu/tag/0DX5)
* [Stacks Project, Tag 00NT](https://stacks.math.columbia.edu/tag/00NT)
* [Stacks Project, Tag 00LX](https://stacks.math.columbia.edu/tag/00LX)
* [Stacks Project, Tag 090R](https://stacks.math.columbia.edu/tag/090R)
* [Stacks Project, Tag 05AC](https://stacks.math.columbia.edu/tag/05AC)
* [Stacks Project, Tag 02OK](https://stacks.math.columbia.edu/tag/02OK)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 02JB](https://stacks.math.columbia.edu/tag/02JB)
* [Stacks Project, Tag 0BIV](https://stacks.math.columbia.edu/tag/0BIV)
* [Stacks Project, Tag 07GH](https://stacks.math.columbia.edu/tag/07GH)
* [Stacks Project, Tag 07QW](https://stacks.math.columbia.edu/tag/07QW)
-/

@[expose] public section

open CategoryTheory IsLocalRing TopologicalSpace
open AlgebraicGeometry Stacks.ModuleStalkSpecialization
open scoped TensorProduct

universe u

namespace Stacks.ImprovementCounterexample

/-! ### An ideal with a linear retraction is principal -/

/-- **An ideal carrying a linear map onto a unit is principal.** Let `I` be an ideal of a
commutative ring `R` and let `f : I →ₗ[R] R` take the value `1` at `a ∈ I`. Then `I = (a)`.

For `b ∈ I` the elements `b • a` and `a • b` of `I` coincide, so `b = f (b • a) = a · f b`. In
particular an ideal whose inclusion into `R` splits is principal. -/
theorem isPrincipal_of_linearMap_eq_one {R : Type*} [CommRing R] (I : Ideal R)
    (f : I →ₗ[R] R) (a : I) (ha : f a = 1) : I = Ideal.span {(a : R)} := by
  apply le_antisymm
  · intro b hb
    have hcomm : (b : R) • a = (a : R) • (⟨b, hb⟩ : I) := by
      apply Subtype.ext
      simp [mul_comm]
    have h1 : f ((b : R) • a) = b := by rw [map_smul, ha, smul_eq_mul, mul_one]
    rw [hcomm, map_smul, smul_eq_mul] at h1
    exact Ideal.mem_span_singleton'.mpr ⟨f ⟨b, hb⟩, (mul_comm _ _).trans h1⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact a.2

/-! ### The maximal ideal of a regular local ring of dimension at least two -/

/-- **The maximal ideal of a regular local ring of dimension at least two is not principal.**
A regular local ring has `dim R` as the minimal number of generators of its maximal ideal, which
`IsLocalRing.finrank_cotangentSpace_le_one_iff` bounds by `1` as soon as the maximal ideal is
principal. -/
theorem not_isPrincipal_maximalIdeal {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim R) : ¬ (maximalIdeal R).IsPrincipal := by
  intro hprin
  have hfin : (maximalIdeal R).spanFinrank ≤ 1 := by
    rcases eq_or_ne (maximalIdeal R) ⊥ with hbot | hbot
    · rw [hbot]
      simp
    · exact ((Submodule.spanFinrank_eq_one_iff _).mpr ⟨hprin, hbot⟩).le
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal] at hdim
  have h2 : 2 ≤ (maximalIdeal R).spanFinrank := by exact_mod_cast hdim
  omega

/-- **No surjection from the maximal ideal onto a nonzero free module.** Over a regular local ring
of dimension at least two, a surjection from the maximal ideal onto a nonzero free module would,
composed with a coordinate of a basis, split the inclusion `𝔪 ⊆ R`, making `𝔪` principal. -/
theorem not_surjective_of_free {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim R) {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Free R N] [Nontrivial N] (f : (maximalIdeal R) →ₗ[R] N) :
    ¬ Function.Surjective f := by
  intro hf
  classical
  obtain ⟨i⟩ := (Module.Free.chooseBasis R N).index_nonempty
  obtain ⟨a, ha⟩ := hf (Module.Free.chooseBasis R N i)
  have h1 : ((Module.Free.chooseBasis R N).coord i).comp f a = 1 := by
    simp [ha]
  exact not_isPrincipal_maximalIdeal hdim
    ⟨(a : R), isPrincipal_of_linearMap_eq_one _ (((Module.Free.chooseBasis R N).coord i).comp f)
      a h1⟩

/-! ### The depth of the maximal ideal as a module -/

/-- **The maximal ideal of a Noetherian local ring of positive depth has depth one.** The short
exact sequence `0 → 𝔪 → R → R/𝔪 → 0` and [Stacks, Tag 00LX] bound `depth_𝔪(𝔪)` above and below by
`1`, since `depth_𝔪(R/𝔪) = 0`. -/
theorem depth_maximalIdeal_eq_one {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (h : 1 ≤ Module.depth R (maximalIdeal R) R) :
    Module.depth R (maximalIdeal R) (maximalIdeal R) = 1 := by
  have hres : Module.depth R (maximalIdeal R) (R ⧸ maximalIdeal R) = 0 := by
    rw [Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes,
      associatedPrimes.eq_singleton_of_isPrimary
        (maximalIdeal.isMaximal R).isPrime.isPrimary, Set.mem_singleton_iff]
    exact (Ideal.IsPrime.radical (maximalIdeal.isMaximal R).isPrime).symm
  obtain ⟨-, h2, h3⟩ :=
    Module.min_depth_le_depth_of_exact (maximalIdeal R)
      (LinearMap.exact_subtype_mkQ (R := R) (N := R) (maximalIdeal R))
      (Submodule.injective_subtype (maximalIdeal R)) (Submodule.mkQ_surjective (maximalIdeal R))
  rw [hres] at h2 h3
  refine le_antisymm ?_ ?_
  · rcases min_le_iff.mp h2 with hc | hc
    · exact absurd (h.trans hc) (by simp)
    · exact tsub_eq_zero_iff_le.mp (le_zero_iff.mp hc)
  · refine le_trans ?_ h3
    rw [zero_add, le_min_iff]
    exact ⟨h, le_rfl⟩

/-- **The maximal ideal of a regular local ring of positive dimension has depth one.** The
self-depth of a regular local ring is its dimension, so
`Stacks.ImprovementCounterexample.depth_maximalIdeal_eq_one` applies. -/
theorem depth_maximalIdeal_eq_one_of_isRegularLocalRing {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R) :
    Module.depth R (maximalIdeal R) (maximalIdeal R) = 1 := by
  have := IsRegularLocalRing.toIsNoetherian (R := R)
  refine depth_maximalIdeal_eq_one ?_
  rw [← depth_eq_ringKrullDim_of_isRegularLocalRing R] at hdim
  exact_mod_cast hdim

/-! ### The incompatibility of the two conditions -/

/-- **No quotient of the maximal ideal of a two-dimensional regular local ring has depth two.**
This is the obstruction refuting the existence clause of [Stacks, Tag 0DX5]: at the point `𝔭` of
the counterexample the source's condition (2) supplies a surjection from `𝔪 = F_𝔭` onto `F''_𝔭`
and its condition (3) demands `depth F''_𝔭 ≥ 2`.

A finite module of depth at least `2 = dim R` is maximal Cohen–Macaulay, hence free by
[Stacks, Tag 00NT]; and `Stacks.ImprovementCounterexample.not_surjective_of_free` rules out a
surjection from `𝔪` onto a nonzero free module. -/
theorem not_exists_two_le_depth_quotient_maximalIdeal {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (hdim : ringKrullDim R = (2 : WithBot ℕ∞)) {N : Type u} [AddCommGroup N]
    [Module R N] [Module.Finite R N] [Nontrivial N] (f : (maximalIdeal R) →ₗ[R] N)
    (hf : Function.Surjective f) (hdepth : 2 ≤ Module.depth R (maximalIdeal R) N) : False := by
  have := IsRegularLocalRing.toIsNoetherian (R := R)
  have hsmul : maximalIdeal R • (⊤ : Submodule R N) ≠ ⊤ :=
    Module.maximalIdeal_smul_top_ne_top N
  -- the depth is exactly two
  have hle : (Module.depth R (maximalIdeal R) N : WithBot ℕ∞) ≤ (2 : WithBot ℕ∞) := by
    refine le_trans (Module.depth_le_supportDim R (maximalIdeal R) N hsmul) ?_
    exact le_trans (Module.supportDim_le_ringKrullDim R N) (le_of_eq hdim)
  have hdep : Module.depth R (maximalIdeal R) N = 2 := by
    refine le_antisymm ?_ hdepth
    have h22 : ((2 : ℕ∞) : WithBot ℕ∞) = (2 : WithBot ℕ∞) := by norm_num
    exact WithBot.coe_le_coe.mp (h22 ▸ hle)
  -- a regular sequence of length two, witnessing maximal Cohen-Macaulayness
  obtain ⟨ss, hmem, hreg, hlen⟩ :=
    (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append (maximalIdeal R) N).2
      hsmul [] (by simp) (RingTheory.Sequence.IsRegular.nil R N)
  simp only [List.nil_append] at hreg hlen
  have hfree : Module.Free R N :=
    regular_mcm_free R N ⟨ss, hmem, hreg, by
      rw [hdim]
      rw [hdep] at hlen
      have : ss.length = 2 := by exact_mod_cast hlen
      rw [this]
      rfl⟩
  exact not_surjective_of_free (le_of_eq hdim.symm) f hf

/-! ### The associated primes of the module of the counterexample -/

/-- **The associated primes of `I ⊕ R/𝔮`.** Over a Noetherian domain, for a nonzero ideal `I` and
a prime `𝔮`, the associated primes of `I ⊕ R/𝔮` are `(0)` and `𝔮`.

This is the computation `Ass(F) = {(0), (u, w)}` of the counterexample, which places the
associated points of `F` outside `Z = V(u, v)` and so makes `F` its own depth-one quotient along
`Z`. The ideal `I`, being a submodule of `R`, is torsion-free, so `(0)` is its only associated
prime by [Stacks, Tag 0AUV]; and `𝔮` is the only associated prime of `R/𝔮`. -/
theorem associatedPrimes_prod_quotient_eq {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊥) (q : Ideal R) [hq : q.IsPrime] :
    associatedPrimes R (↥I × (R ⧸ q)) = {⊥, q} := by
  have hne : Nontrivial ↥I := by
    obtain ⟨x, hxI, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    exact ⟨⟨⟨x, hxI⟩, 0, by simpa using hx⟩⟩
  have h1 : associatedPrimes R ↥I = {⊥} := by
    have htfae := isTorsionFree_iff_finiteFreeEmbedding_iff_associatedPrimes_iff_propertyS1
      (R := R) (M := ↥I)
    exact htfae.2.1.mp (htfae.1.mp inferInstance)
  have h2 : associatedPrimes R (R ⧸ q) = {q} := by
    rw [associatedPrimes.eq_singleton_of_isPrimary hq.isPrimary, hq.radical]
  rw [associatedPrimes.prod, h1, h2, Set.singleton_union]

/-! ### Transporting the two conditions to a generalization -/

/-- The stalk map of `φ` at `x`, as a linear map over the local ring (see the implementation
notes). -/
private noncomputable def stalkMapLinearMap {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G)
    (x : X) :
    letI := stalkModule F x
    letI := stalkModule G x
    F.presheaf.stalk x →ₗ[X.presheaf.stalk x] G.presheaf.stalk x :=
  letI := stalkModule F x
  letI := stalkModule G x
  { toFun := (TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf
    map_add' := map_add _
    map_smul' := ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map φ).hom.map_smul }

/-- **Epimorphy on a stalk transports to a generalization.** Let `φ : F ⟶ G` be a map of
`𝒪_X`-modules with `G` quasi-coherent and let `y ⤳ x`, so that `y` is a generalization of `x`.
If `φ` is an epimorphism on the stalk at `x` then it is one on the stalk at `y`.

The stalk at `y` is the localization of the stalk at `x`
(`Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes`), so an element of
`G_y` is `s⁻¹ • m` for `m` in the image of `G_x` and `s` a scalar whose image in `𝒪_{X,y}` is a
unit; a preimage of `m` is moved to `y` and divided by `s`. That the two operations commute is
Mathlib's naturality square `TopCat.Presheaf.stalkSpecializes_stalkFunctor_map`.

This is the step that carries condition (2) of [Stacks, Tag 0DX5] from the closed point
`(u, v, w)` of the counterexample — where it holds, that point being reached from the associated
point `(u, w)` — to the generic point `(u, v)` of `Z`, where condition (3) is in force. -/
theorem epi_stalkFunctor_map_of_specializes {X : Scheme.{u}} {F G : X.Modules}
    [G.IsQuasicoherent] (φ : F ⟶ G) {x y : X} (h : y ⤳ x)
    (hepi : Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf)) :
    Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map φ.mapPresheaf) := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let := stalkModule F x
  let := stalkModule F y
  let := stalkModule G x
  let := stalkModule G y
  let := stalkSpecializesModule F h
  let := stalkSpecializesModule G h
  have := isLocalizedModule_atPrime_stalkSpecializes G h
  let ψx := stalkMapLinearMap φ x
  let ψy := stalkMapLinearMap φ y
  have hx : Function.Surjective ψx := (AddCommGrpCat.epi_iff_surjective _).mp hepi
  have key : ∀ n : G.presheaf.stalk y, ∃ m : F.presheaf.stalk y, ψy m = n := by
    intro n
    obtain ⟨⟨m, s⟩, hms⟩ :=
      IsLocalizedModule.surj
        ((maximalIdeal (X.presheaf.stalk y)).under
          (X.presheaf.stalk x)).primeCompl (stalkSpecializesₗ G h) n
    obtain ⟨m', hm'⟩ := hx m
    have hsu : IsUnit ((X.presheaf.stalkSpecializes h).hom (s : X.presheaf.stalk x)) := by
      rw [← notMem_maximalIdeal]
      exact s.2
    obtain ⟨v, hv⟩ := hsu
    have hnat : ψy (stalkSpecializesₗ F h m') = stalkSpecializesₗ G h (ψx m') :=
      ConcreteCategory.congr_hom
        (TopCat.Presheaf.stalkSpecializes_stalkFunctor_map φ.mapPresheaf h) m'
    have hsn : (v : X.presheaf.stalk y) • n = stalkSpecializesₗ G h m := by
      rw [hv]
      exact hms
    refine ⟨((v⁻¹ : (X.presheaf.stalk y)ˣ) : X.presheaf.stalk y) • stalkSpecializesₗ F h m', ?_⟩
    rw [map_smul, hnat, hm', ← hsn, ← mul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul]
  rw [AddCommGrpCat.epi_iff_surjective]
  exact key

/-- **A nontrivial stalk stays nontrivial at a specialization.** This is
`AlgebraicGeometry.Scheme.Modules.stableUnderSpecialization_supp` — [Stacks, Tag 05AC] — read
through `SheafOfModules.mem_supp_iff_nontrivial_stalk`.

It supplies the nontriviality that the refutation needs at the generic point of `Z`: without it
the target could vanish there, and a vanishing module has depth `⊤`, so condition (3) would hold
for a trivial reason. -/
theorem nontrivial_stalk_of_specializes {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {x y : X} (h : y ⤳ x) (hy : Nontrivial (F.presheaf.stalk y)) :
    Nontrivial (F.presheaf.stalk x) :=
  (SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mp
    (Scheme.Modules.stableUnderSpecialization_supp X F h
      ((SheafOfModules.mem_supp_iff_nontrivial_stalk F y).mpr hy))

/-! ### The refutation at the scheme level -/

/-- **The obstruction at a single point.** Let `φ : F ⟶ G` be a map of `𝒪_X`-modules with `G`
coherent, and let `η ⤳ p ⤳ q` be points such that `φ` is an isomorphism on the stalk at `η` and
an epimorphism on the stalk at `q`, the local ring at `p` is regular of dimension two,
`F_p ≅ 𝔪_p` and `F_η ≠ 0`. Then `G_p` does not have depth at least two.

The epimorphism at `q` transports to `p` by
`Stacks.ImprovementCounterexample.epi_stalkFunctor_map_of_specializes`, and the isomorphism at `η`
makes `G_p` nonzero by `Stacks.ImprovementCounterexample.nontrivial_stalk_of_specializes`; so
`G_p` is a finite nonzero quotient of `𝔪_p`, which cannot have depth two by
`Stacks.ImprovementCounterexample.not_exists_two_le_depth_quotient_maximalIdeal`. -/
theorem not_two_le_depth_stalk_of_linearEquiv_maximalIdeal {X : Scheme.{u}}
    {F G : X.Modules} [G.IsCoherent] (φ : F ⟶ G) {p q η : X} (hpq : p ⤳ q) (hηp : η ⤳ p)
    (hiso : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} η).map φ.mapPresheaf))
    (hepiq : Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} q).map φ.mapPresheaf))
    [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = (2 : WithBot ℕ∞))
    (hFη : Nontrivial (F.presheaf.stalk η))
    (e : letI := stalkModule F p
      F.presheaf.stalk p ≃ₗ[X.presheaf.stalk p] (maximalIdeal (X.presheaf.stalk p))) :
    letI := stalkModule G p
    ¬ (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk p)
      (maximalIdeal (X.presheaf.stalk p)) (G.presheaf.stalk p) := by
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  let := stalkModule F p
  let := stalkModule G p
  let := stalkModule F η
  let := stalkModule G η
  -- the isomorphism at the generic point makes the target's stalk there nontrivial
  have hGη : Nontrivial (G.presheaf.stalk η) := by
    let qη := (TopCat.Presheaf.stalkFunctor Ab.{u} η).map φ.mapPresheaf
    have hbij := (ConcreteCategory.isIso_iff_bijective qη).mp hiso
    obtain ⟨a, b, hab⟩ := hFη
    exact ⟨qη a, qη b, fun hc => hab (hbij.1 hc)⟩
  have : Nontrivial (G.presheaf.stalk p) := nontrivial_stalk_of_specializes G hηp hGη
  -- the epimorphism at `q` transports to the generalization `p`
  have hepi : Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} p).map φ.mapPresheaf) :=
    epi_stalkFunctor_map_of_specializes φ hpq hepiq
  let ψ := stalkMapLinearMap φ p
  have hψ : Function.Surjective ψ := (AddCommGrpCat.epi_iff_surjective _).mp hepi
  have hsurj : Function.Surjective (ψ ∘ₗ e.symm.toLinearMap) := by
    rw [LinearMap.coe_comp]
    exact hψ.comp e.symm.surjective
  -- a finite nonzero quotient of the maximal ideal has depth below two
  intro hdepth
  have : G.IsFiniteType := ‹G.IsCoherent›.isFiniteType
  have : Module.Finite (X.presheaf.stalk p) (G.presheaf.stalk p) :=
    SheafOfModules.finite_stalk X.sheaf G p
  exact not_exists_two_le_depth_quotient_maximalIdeal hdim (ψ ∘ₗ e.symm.toLinearMap) hsurj hdepth

/-- **The existence clause of [Stacks, Tag 0DX5] fails.** Let `Z ⊆ X` be a subset, `φ : F ⟶ G` a
map of `𝒪_X`-modules and `η`, `p`, `q` three points with

* `η ∉ Z` and `η ⤳ p ⤳ q`, with `p, q ∈ Z`;
* `q` reached from outside `Z` for `F`, and `p` not;
* `𝒪_{X,p}` regular local of dimension two, `F_p ≅ 𝔪_p` as `𝒪_{X,p}`-modules, and `F_η ≠ 0`.

Then no such `φ` is an improvement of `F` along `Z`.

Condition (2) at `q` is an epimorphism on the stalk there, which
`Stacks.ImprovementCounterexample.epi_stalkFunctor_map_of_specializes` transports to `p`; composed
with `F_p ≅ 𝔪_p` it is a surjection `𝔪_p ↠ G_p`. Condition (3) at `p` demands
`depth G_p ≥ 2 = dim 𝒪_{X,p}`, and `G_p` is a finite nonzero `𝒪_{X,p}`-module — finite because
`G` is coherent, nonzero because condition (1) at `η` makes `G_η ≅ F_η` nonzero and
`Stacks.ImprovementCounterexample.nontrivial_stalk_of_specializes` carries that to `p`. The two
are incompatible by
`Stacks.ImprovementCounterexample.not_exists_two_le_depth_quotient_maximalIdeal`.

For `X = Spec k[u, v, w]`, `Z = V(u, v)` and `F = (u, v)~ ⊕ (k[u,v,w]/(u, w))~` the hypotheses
hold with `η = (0)`, `p = (u, v)` and `q = (u, v, w)`; that instance is
`Stacks.ImprovementCounterexample.not_exists_isImprovement_cexSheaf`. -/
theorem not_isImprovement_of_linearEquiv_maximalIdeal {X : Scheme.{u}} {Z : Set X}
    {F G : X.Modules} (φ : F ⟶ G) {p q η : X}
    (hpZ : p ∈ Z) (hqZ : q ∈ Z) (hpq : p ⤳ q) (hηp : η ⤳ p) (hηZ : η ∉ Z)
    (hqr : ReachedFromOutside Z F q) (hpr : ¬ ReachedFromOutside Z F p)
    [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = (2 : WithBot ℕ∞))
    (hFη : Nontrivial (F.presheaf.stalk η))
    (e : letI := stalkModule F p
      F.presheaf.stalk p ≃ₗ[X.presheaf.stalk p] (maximalIdeal (X.presheaf.stalk p))) :
    ¬ IsImprovement Z φ := fun h =>
  let := h.1
  not_two_le_depth_stalk_of_linearEquiv_maximalIdeal φ hpq hηp (h.2.1 η hηZ)
    (h.2.2.1 q hqZ hqr).1 hdim hFη e (h.2.2.2 p hpZ hpr)

/-! ### The ideals generated by variables in a polynomial ring -/

section Variables

variable {σ K : Type*} [CommRing K]

open MvPolynomial in
/-- A variable outside `s` does not lie in the ideal generated by the variables in `s`: it is a
nonzerodivisor modulo that ideal, which is proper. -/
theorem X_notMem_span_image_X [Nontrivial K] {s : Finset σ} {i : σ} (hi : i ∉ s) :
    (X i : MvPolynomial σ K) ∉ Ideal.span (X '' (s : Set σ)) := fun h =>
  MvPolynomial.one_notMem_span_X_image
    (MvPolynomial.mem_span_X_image_of_X_mul_mem (fun hc => hi (Finset.mem_coe.mp hc))
      (by simpa using h))

open MvPolynomial in
/-- The ideal generated by the variables in `s` is strictly smaller than the one generated by the
variables in `t` as soon as `s ⊆ t` and some index of `t` is missing from `s`. -/
theorem span_image_X_lt [Nontrivial K] {s t : Finset σ} (hst : s ⊆ t) {i : σ}
    (hit : i ∈ t) (his : i ∉ s) :
    (Ideal.span (X '' (s : Set σ) : Set (MvPolynomial σ K)))
      < Ideal.span (X '' (t : Set σ)) :=
  lt_of_le_of_ne (Ideal.span_mono (Set.image_mono (Finset.coe_subset.mpr hst))) fun hEq =>
    X_notMem_span_image_X his (hEq ▸ Ideal.subset_span (Set.mem_image_of_mem _ hit))

open MvPolynomial in
/-- The height of the ideal generated by `s.card` variables is at least `s.card`: the ideals
generated by the initial segments of `s` form a strictly increasing chain of primes. -/
theorem card_le_height_span_image_X [IsDomain K] (s : Finset σ) :
    (s.card : ℕ∞)
      ≤ (Ideal.span (X '' (s : Set σ) : Set (MvPolynomial σ K))).height := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i t hi ih =>
      have := Stacks.Examples.HironakaConicIntersection.isPrime_span_image_X (k := K) t
      have := Stacks.Examples.HironakaConicIntersection.isPrime_span_image_X (k := K)
        (insert i t)
      have hlt := Ideal.height_add_one_le_of_lt_of_isPrime
        (span_image_X_lt (K := K) (σ := σ) (Finset.subset_insert i t)
          (Finset.mem_insert_self i t) hi)
      rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      exact le_trans (add_le_add ih (le_refl (1 : ℕ∞))) hlt

open MvPolynomial in
/-- The height of the ideal generated by `s.card` variables is at most `s.card`: it is a prime
generated by `s.card` elements, so Krull's height theorem applies. -/
theorem height_span_image_X_le [IsDomain K] [IsNoetherianRing (MvPolynomial σ K)]
    (s : Finset σ) :
    (Ideal.span (X '' (s : Set σ) : Set (MvPolynomial σ K))).height ≤ s.card := by
  classical
  have := Stacks.Examples.HironakaConicIntersection.isPrime_span_image_X (k := K) s
  have hmem : Ideal.span (X '' (s : Set σ) : Set (MvPolynomial σ K)) ∈
      (Ideal.span (X '' (s : Set σ) : Set (MvPolynomial σ K))).minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact rfl
  have h := Ideal.height_le_card_of_mem_minimalPrimes_span
    ((s : Set σ).toFinite.image _) hmem
  rwa [Set.ncard_image_of_injective _ MvPolynomial.X_injective,
    Set.ncard_coe_finset] at h

open MvPolynomial in
/-- **The height of the ideal generated by a finite set of variables is the size of that set.**
This is the dimension computation the counterexample needs: `(u, v)` has height two in
`k[u, v, w]`, `(u, w)` has height two and `(u, v, w)` has height three. -/
theorem height_span_image_X [IsDomain K] [IsNoetherianRing (MvPolynomial σ K)]
    (s : Finset σ) :
    (Ideal.span (X '' (s : Set σ) : Set (MvPolynomial σ K))).height = s.card :=
  le_antisymm (height_span_image_X_le s) (card_le_height_span_image_X s)

end Variables

/-! ### Immediate specializations of primes -/

/-- A specialization of primes through which a third prime strictly factors is not immediate.
This is `Stacks.Catenary.immediateSpec_iff_covby` read on the ideals; it is stated here because
the order on `PrimeSpectrum R` and the specialization order on the carrier of `Spec R`, though
definitionally the same, are two different instances. -/
theorem not_isImmediateSpecialization_of_lt_of_lt {R : Type*} [CommRing R]
    {x y : PrimeSpectrum R} (himm : TopologicalSpace.IsImmediateSpecialization x y)
    (z : PrimeSpectrum R) (h1 : x.asIdeal < z.asIdeal) (h2 : z.asIdeal < y.asIdeal) : False :=
  ((immediateSpec_iff_covby x y).mp himm).2
    ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp h1) ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp h2)

/-- An immediate specialization of primes is in particular an inclusion of the ideals. -/
theorem asIdeal_le_asIdeal_of_isImmediateSpecialization {R : Type*} [CommRing R]
    {x y : PrimeSpectrum R} (himm : TopologicalSpace.IsImmediateSpecialization x y) :
    x.asIdeal ≤ y.asIdeal :=
  (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr ((immediateSpec_iff_covby x y).mp himm).1.le

/-! ### The counterexample itself -/

section Cex

variable (k : Type u) [Field k]

/-- The point of `Spec k[u, v, w]` given by the prime generated by the variables indexed by `s`:
`∅` gives the generic point `(0)`, `{0, 1}` gives `𝔭 = (u, v)`, `{0, 2}` gives `(u, w)` and
`{0, 1, 2}` gives the closed point `(u, v, w)`. -/
noncomputable abbrev varPrime (s : Finset (Fin 3)) : PrimeSpectrum (MvPolynomial (Fin 3) k) :=
  ⟨Ideal.span (MvPolynomial.X '' (s : Set (Fin 3))),
    Stacks.Examples.HironakaConicIntersection.isPrime_span_image_X k s⟩

/-- The module `(u, v) ⊕ k[u, v, w]/(u, w)` whose associated sheaf is the counterexample. -/
noncomputable abbrev cexModule : ModuleCat.{u} (MvPolynomial (Fin 3) k) :=
  ModuleCat.of _ (↥(varPrime k {0, 1}).asIdeal ×
    (MvPolynomial (Fin 3) k ⧸ (varPrime k {0, 2}).asIdeal))

/-- The scheme `X = Spec k[u, v, w]` of the counterexample. -/
noncomputable abbrev cexScheme : Scheme.{u} := Spec (CommRingCat.of (MvPolynomial (Fin 3) k))

/-- The `𝒪_X`-module `F = (u, v)~ ⊕ (k[u, v, w]/(u, w))~` on `X = Spec k[u, v, w]`. -/
noncomputable abbrev cexSheaf : (cexScheme k).Modules :=
  (tilde.functor (CommRingCat.of (MvPolynomial (Fin 3) k))).obj (cexModule k)

/-- The closed subset `Z = V(u, v)` of `X = Spec k[u, v, w]`. -/
noncomputable abbrev cexZ : Set (cexScheme k) :=
  PrimeSpectrum.zeroLocus (MvPolynomial.X '' (({0, 1} : Finset (Fin 3)) : Set (Fin 3)))

/-- The point of `X = Spec k[u, v, w]` cut out by the variables indexed by `s`, named at the type
of the carrier of the scheme. Instance search cannot recognise a prime of `k[u, v, w]` as a point
of `Spec k[u, v, w]` without unfolding `Spec`, so every statement about a stalk is phrased with
this spelling of the point rather than with
`Stacks.ImprovementCounterexample.varPrime` itself. -/
noncomputable abbrev cexPt (s : Finset (Fin 3)) : ↥(cexScheme k) := varPrime k s

/-! #### Fact (0): `F` is coherent, as [Stacks, Tag 0DX5] requires of it -/

/-- **`F = (u, v)~ ⊕ (k[u, v, w]/(u, w))~` is coherent.** This is the hypothesis
[Stacks, Tag 0DX5] places on the module it improves, so the refutation below is a refutation of
the source's assertion under the source's own hypothesis on `F`, not of a strengthening of it.

`k[u, v, w]` is Noetherian and `(u, v) ⊕ k[u, v, w]/(u, w)` is a finite module over it — the
first summand is an ideal of a Noetherian ring, the second a quotient — so
`AlgebraicGeometry.tilde_isCoherent_of_finite` applies. -/
instance isCoherent_cexSheaf : (cexSheaf k).IsCoherent :=
  tilde_isCoherent_of_finite (R := CommRingCat.of (MvPolynomial (Fin 3) k)) (cexModule k)

/-- **`Z = V(u, v)` is closed.** The other hypothesis of [Stacks, Tag 0DX5] that is about the
data rather than about `X`; it is a zero locus. That `X` itself is Noetherian needs no lemma,
`IsNoetherian (cexScheme k)` being found by instance search from the Noetherianity of
`k[u, v, w]`. -/
theorem isClosed_cexZ : IsClosed (cexZ k) :=
  PrimeSpectrum.isClosed_zeroLocus _

/-- `k[u, v, w]` is excellent: a finite-type algebra over the field `k`, which is excellent.
This is the single input from which both hypotheses [Stacks, Tag 0DX5] places on `X` are read
off below — universal catenarity from the second component, and the `(S₁)` formal fibres from
the G-ring in the first. -/
@[ega "IV 7.8.3" "(ii), special case"]
theorem isExcellent_cexRing : IsExcellent (MvPolynomial (Fin 3) k) :=
  (isExcellent_of_standard_classes_and_finiteType.{u, u}).2.2.2.2 k (MvPolynomial (Fin 3) k)
    ((isExcellent_of_standard_classes_and_finiteType.{u, u}).1 k)

/-- **`X = Spec k[u, v, w]` is universally catenary**, the third of the five hypotheses of
[Stacks, Tag 0DX5]. A polynomial ring over a field is excellent, hence universally catenary as a
ring, and the spectrum of a Noetherian universally catenary ring is a universally catenary
scheme. -/
theorem isUniversallyCatenary_cexScheme : Scheme.IsUniversallyCatenary (cexScheme k) :=
  Scheme.isUniversallyCatenary_spec (MvPolynomial (Fin 3) k) (isExcellent_cexRing k).2

/-- **The local rings of `X = Spec k[u, v, w]` have `(S₁)` formal fibres**, the last of the five
hypotheses of [Stacks, Tag 0DX5], in the shape the development's statements of the improvement
existence theorems take it.

The stalk at a point `z` is the localization of `k[u, v, w]` at the corresponding prime, by
`AlgebraicGeometry.Spec.stalkIso`, and `k[u, v, w]` is a G-ring because it is excellent. So
`hasSerreCondition_one_formalFibres_of_isGRing_localization` applies: the formal fibres of such a
localization are geometrically regular, hence regular, hence satisfy `(S₁)`. -/
theorem hasSerreCondition_one_formalFibres_cexScheme (z : cexScheme k)
    (q : PrimeSpectrum ((cexScheme k).presheaf.stalk z)) :
    HasSerreCondition ((cexScheme k).completedLocalRing z ⊗[(cexScheme k).presheaf.stalk z]
      q.asIdeal.ResidueField) 1 :=
  have := (z : PrimeSpectrum (MvPolynomial (Fin 3) k)).isPrime
  hasSerreCondition_one_formalFibres_of_isGRing_localization (isExcellent_cexRing k).1.2.1
    (z : PrimeSpectrum (MvPolynomial (Fin 3) k)).asIdeal
    (Spec.stalkIso (CommRingCat.of (MvPolynomial (Fin 3) k))
      (z : PrimeSpectrum (MvPolynomial (Fin 3) k))).commRingCatIsoToRingEquiv.symm q

/-! #### Fact (i): the three points against `Z = V(u, v)` -/

/-- The point generated by a set of variables containing `u` and `v` lies in `Z = V(u, v)`. -/
theorem cexPt_mem_cexZ {s : Finset (Fin 3)} (hs : ({0, 1} : Finset (Fin 3)) ⊆ s) :
    cexPt k s ∈ cexZ k :=
  fun _ hy => Ideal.subset_span (Set.image_mono (Finset.coe_subset.mpr hs) hy)

/-- The point generated by a set of variables missing `v` does not lie in `Z = V(u, v)`. -/
theorem cexPt_notMem_cexZ {s : Finset (Fin 3)} (hs : (1 : Fin 3) ∉ s) :
    cexPt k s ∉ cexZ k := fun h =>
  X_notMem_span_image_X hs (h (Set.mem_image_of_mem _ (by decide)))

/-! #### Fact (ii): the associated points of `F` -/

/-- **`Ass(F) = {(0), (u, w)}`.** This instantiates
`Stacks.ImprovementCounterexample.associatedPrimes_prod_quotient_eq` at `k[u, v, w]`, the ideal
`(u, v)` and the prime `(u, w)`, and transports it to the sheaf `F` through the affine comparison
of [Stacks, Tag 02OK]. -/
theorem isAssociatedPoint_cexSheaf_iff (x : PrimeSpectrum (MvPolynomial (Fin 3) k)) :
    Stacks.Divisors.IsAssociatedPoint (cexSheaf k) (x : cexScheme k) ↔
      x.asIdeal = ⊥ ∨ x.asIdeal = (varPrime k {0, 2}).asIdeal := by
  have := (varPrime k {0, 2}).isPrime
  have hI : (varPrime k {0, 1}).asIdeal ≠ ⊥ := fun hbot => by
    have hmem : (MvPolynomial.X 0 : MvPolynomial (Fin 3) k) ∈ (varPrime k {0, 1}).asIdeal :=
      Ideal.subset_span (Set.mem_image_of_mem _ (by decide))
    rw [hbot, Ideal.mem_bot] at hmem
    exact MvPolynomial.X_ne_zero 0 hmem
  have hass : associatedPrimes (MvPolynomial (Fin 3) k)
      (↥(varPrime k {0, 1}).asIdeal × (MvPolynomial (Fin 3) k ⧸ (varPrime k {0, 2}).asIdeal))
      = {⊥, (varPrime k {0, 2}).asIdeal} :=
    associatedPrimes_prod_quotient_eq hI _
  rw [Stacks.LocalCohomology.isAssociatedPoint_tilde_iff,
    Stacks.Depth.isAssociatedPrimeStacks_iff_mem_associatedPrimes]
  show x.asIdeal ∈ associatedPrimes (MvPolynomial (Fin 3) k)
    (↥(varPrime k {0, 1}).asIdeal × (MvPolynomial (Fin 3) k ⧸ (varPrime k {0, 2}).asIdeal)) ↔ _
  rw [hass]
  exact Iff.rfl

/-! #### Fact (iii): the local ring at `𝔭 = (u, v)` -/

/-- The stalk of `Spec k[u, v, w]` at the point generated by a set of variables is a regular
local ring: it is the localization of a regular ring at a prime. -/
instance isRegularLocalRing_stalk_cexPt (s : Finset (Fin 3)) :
    IsRegularLocalRing ((cexScheme k).presheaf.stalk (cexPt k s)) :=
  IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (CommRingCat.of (MvPolynomial (Fin 3) k))
      (varPrime k s)).commRingCatIsoToRingEquiv.symm

/-- **The dimension of the local ring at the prime generated by `s` variables is `s.ncard`.**
In particular `𝒪_{X,𝔭}` is two-dimensional at `𝔭 = (u, v)`. -/
theorem ringKrullDim_stalk_cexPt (s : Finset (Fin 3)) :
    ringKrullDim ((cexScheme k).presheaf.stalk (cexPt k s))
      = ((s.card : ℕ∞) : WithBot ℕ∞) := by
  have := (varPrime k s).isPrime
  have e : (cexScheme k).presheaf.stalk (cexPt k s)
      ≃+* Localization.AtPrime (varPrime k s).asIdeal :=
    (Spec.stalkIso (CommRingCat.of (MvPolynomial (Fin 3) k))
      (varPrime k s)).commRingCatIsoToRingEquiv
  rw [ringKrullDim_eq_of_ringEquiv e,
    IsLocalization.AtPrime.ringKrullDim_eq_height (varPrime k s).asIdeal
      (Localization.AtPrime (varPrime k s).asIdeal),
    height_span_image_X (K := k) s]

/-- `{0, 1} ⊆ {0, 1, 2}`: `(u, v) ⊆ (u, v, w)`. -/
private theorem uv_subset_uvw : ({0, 1} : Finset (Fin 3)) ⊆ ({0, 1, 2} : Finset (Fin 3)) := by
  decide

/-- `{0, 2} ⊆ {0, 1, 2}`: `(u, w) ⊆ (u, v, w)`. -/
private theorem uw_subset_uvw : ({0, 2} : Finset (Fin 3)) ⊆ ({0, 1, 2} : Finset (Fin 3)) := by
  decide

/-- `{0} ⊆ {0, 1}`: `(u) ⊆ (u, v)`. -/
private theorem u_subset_uv : ({0} : Finset (Fin 3)) ⊆ ({0, 1} : Finset (Fin 3)) := by
  decide

/-- The height of the prime generated by the variables indexed by `s` is `s.ncard`. -/
theorem height_varPrime (s : Finset (Fin 3)) :
    (varPrime k s).asIdeal.height = (s.card : ℕ∞) :=
  height_span_image_X (K := k) s

/-- `(u, w)` has height two. -/
theorem height_varPrime_uw : (varPrime k {0, 2}).asIdeal.height = 2 := by
  rw [height_varPrime, show ({0, 2} : Finset (Fin 3)).card = 2 by decide]
  rfl

/-- `(u, v, w)` has height three. -/
theorem height_varPrime_uvw : (varPrime k {0, 1, 2}).asIdeal.height = 3 := by
  rw [height_varPrime, show ({0, 1, 2} : Finset (Fin 3)).card = 3 by decide]
  rfl

/-! #### Fact (ii) continued: which points of `Z` are reached from outside -/

/-- **`(u, w) ⋖ (u, v, w)`.** A prime strictly between them would have height at least three, by
the height two of `(u, w)`, and at most two, by the height three of `(u, v, w)`. -/
theorem covBy_varPrime_uw_uvw : (varPrime k {0, 2}) ⋖ (varPrime k {0, 1, 2}) := by
  have := (varPrime k {0, 2}).isPrime
  have := (varPrime k {0, 1, 2}).isPrime
  refine ⟨(PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp
    (span_image_X_lt (K := k) uw_subset_uvw
      (show (1 : Fin 3) ∈ ({0, 1, 2} : Finset (Fin 3)) by decide)
      (show (1 : Fin 3) ∉ ({0, 2} : Finset (Fin 3)) by decide)),
    fun z hz1 hz2 => ?_⟩
  have := z.isPrime
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime
    ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hz1)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime
    ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hz2)
  rw [height_varPrime_uw] at h1
  rw [height_varPrime_uvw] at h2
  have hcontra : (4 : ℕ∞) ≤ 3 :=
    le_trans (le_trans (by norm_num) (add_le_add h1 (le_refl (1 : ℕ∞)))) h2
  norm_num at hcontra

/-- **The closed point `(u, v, w)` is reached from outside `Z`.** Its associated generalization
`(u, w)` lies off `Z = V(u, v)`, being missing `v`, and specializes to it immediately. -/
theorem reachedFromOutside_cexSheaf_uvw :
    ReachedFromOutside (cexZ k) (cexSheaf k) (cexPt k {0, 1, 2}) :=
  ⟨cexPt k {0, 2}, cexPt_notMem_cexZ k (by decide),
    (isAssociatedPoint_cexSheaf_iff k _).mpr (Or.inr rfl),
    (immediateSpec_iff_covby _ _).mpr (covBy_varPrime_uw_uvw k)⟩

/-- **The generic point `𝔭 = (u, v)` of `Z` is *not* reached from outside `Z`.** Its only
associated generalization is `(0)`, and `(0) ⤳ 𝔭` factors through `(u)`, so it is not immediate;
the other associated point `(u, w)` does not specialize to `𝔭` at all, `w` not lying in `𝔭`. -/
theorem not_reachedFromOutside_cexSheaf_uv :
    ¬ ReachedFromOutside (cexZ k) (cexSheaf k) (cexPt k {0, 1}) := by
  rintro ⟨x', -, hass, himm⟩
  have := x'.isPrime
  have := (varPrime k ({0} : Finset (Fin 3))).isPrime
  rcases (isAssociatedPoint_cexSheaf_iff k x').mp hass with h | h
  · have hbot : Ideal.span (MvPolynomial.X '' ((∅ : Finset (Fin 3)) : Set (Fin 3)) :
        Set (MvPolynomial (Fin 3) k)) = ⊥ := by simp
    refine not_isImmediateSpecialization_of_lt_of_lt himm
      (varPrime k ({0} : Finset (Fin 3))) ?_ ?_
    · rw [h, ← hbot]
      exact span_image_X_lt (K := k) (i := 0) (Finset.empty_subset _) (by decide) (by decide)
    · exact span_image_X_lt (K := k) (i := 1) u_subset_uv (by decide) (by decide)
  · have hle := asIdeal_le_asIdeal_of_isImmediateSpecialization himm
    rw [h] at hle
    exact X_notMem_span_image_X (show (2 : Fin 3) ∉ ({0, 1} : Finset (Fin 3)) by decide)
      (hle (Ideal.subset_span (Set.mem_image_of_mem _ (by decide))))

/-! #### Fact (v): the stalk of `F` at the generic point is nonzero -/

/-- **`F_{(0)} ≠ 0`.** The generic point `(0)` is an associated point of `F`, and the stalk of a
module at an associated point is nonzero. -/
theorem nontrivial_stalk_cexSheaf_generic :
    Nontrivial ((cexSheaf k).presheaf.stalk (cexPt k (∅ : Finset (Fin 3)))) :=
  Stacks.Divisors.IsAssociatedPoint.nontrivial
    ((isAssociatedPoint_cexSheaf_iff k _).mpr (Or.inl (by simp)))

/-! #### Fact (iv): the stalk of `F` at `𝔭` is the maximal ideal of `𝒪_{X,𝔭}` -/

/-- If every element of the second factor of a product is annihilated by some element of `T`,
then a localization map at `T` out of the first factor, precomposed with the projection, is again
a localization map at `T`: the second factor contributes nothing after localizing.

This is how the summand `k[u, v, w]/(u, w)` of the counterexample disappears at `𝔭 = (u, v)`,
being annihilated by `w ∉ 𝔭`. -/
theorem isLocalizedModule_comp_fst {R A B N : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup N] [Module R N] (T : Submonoid R)
    (f : A →ₗ[R] N) [IsLocalizedModule T f] (hB : ∀ b : B, ∃ t : T, (t : R) • b = 0) :
    IsLocalizedModule T (f ∘ₗ LinearMap.fst R A B) where
  map_units t := IsLocalizedModule.map_units f t
  surj y := by
    obtain ⟨⟨a, t⟩, ht⟩ := IsLocalizedModule.surj T f y
    exact ⟨⟨(a, 0), t⟩, ht⟩
  exists_of_eq {x y} h := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := f) h
    obtain ⟨t₁, ht₁⟩ := hB x.2
    obtain ⟨t₂, ht₂⟩ := hB y.2
    have hc' : (c : R) • x.1 = (c : R) • y.1 := by
      simpa [Submonoid.smul_def] using hc
    have hA : ∀ z : A, ((c : R) * t₁ * t₂) • z = ((t₁ : R) * t₂) • ((c : R) • z) := fun z => by
      rw [← mul_smul, show (t₁ : R) * t₂ * c = (c : R) * t₁ * t₂ by ring]
    have hB₁ : ∀ z : B, ((c : R) * t₁ * t₂) • z = ((c : R) * t₂) • ((t₁ : R) • z) := fun z => by
      rw [← mul_smul, show (c : R) * t₂ * t₁ = (c : R) * t₁ * t₂ by ring]
    have hB₂ : ∀ z : B, ((c : R) * t₁ * t₂) • z = ((c : R) * t₁) • ((t₂ : R) • z) := fun z => by
      rw [← mul_smul]
    refine ⟨c * t₁ * t₂, Prod.ext_iff.mpr ⟨?_, ?_⟩⟩
    · show ((c * t₁ * t₂ : T) : R) • x.1 = ((c * t₁ * t₂ : T) : R) • y.1
      push_cast
      rw [hA, hA, hc']
    · show ((c * t₁ * t₂ : T) : R) • x.2 = ((c * t₁ * t₂ : T) : R) • y.2
      push_cast
      rw [hB₁ x.2, ht₁, smul_zero, hB₂ y.2, ht₂, smul_zero]

/-- **`F_𝔭 ≅ 𝔪_𝔭`.** At `𝔭 = (u, v)` the summand `(k[u, v, w]/(u, w))~` dies, because `w ∉ 𝔭`
annihilates `k[u, v, w]/(u, w)`, while `(u, v)~` localizes to `𝔭 · 𝒪_{X,𝔭}`, the maximal ideal of
`𝒪_{X,𝔭}`.

The stalk of `M~` at a prime is the localization of `M` there
(`AlgebraicGeometry.tilde.toStalk`), the stalk of the structure sheaf is the localization of the
ring (`AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`), and
`Submodule.toLocalized'` realizes the localization of the ideal `𝔭` inside it; the two
localizations of the same module are identified by `IsLocalizedModule.linearEquiv`, and the
resulting `k[u, v, w]`-linear isomorphism is automatically `𝒪_{X,𝔭}`-linear by
`LinearEquiv.extendScalarsOfIsLocalization`. -/
noncomputable def linearEquiv_stalk_cexSheaf_maximalIdeal :
    letI := stalkModule (cexSheaf k) (cexPt k {0, 1})
    (cexSheaf k).presheaf.stalk (cexPt k {0, 1})
      ≃ₗ[(cexScheme k).presheaf.stalk (cexPt k {0, 1})]
        (maximalIdeal ((cexScheme k).presheaf.stalk (cexPt k {0, 1}))) := by
  letI := stalkModule (cexSheaf k) (cexPt k {0, 1})
  have : (varPrime k {0, 1}).asIdeal.IsPrime := (varPrime k {0, 1}).isPrime
  letI : Algebra (MvPolynomial (Fin 3) k)
      ((cexScheme k).presheaf.stalk (cexPt k {0, 1})) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra _ (varPrime k {0, 1})
  have : IsLocalization.AtPrime ((cexScheme k).presheaf.stalk (cexPt k {0, 1}))
      (varPrime k {0, 1}).asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk _ (varPrime k {0, 1})
  letI : Module (MvPolynomial (Fin 3) k) ((cexSheaf k).presheaf.stalk (cexPt k {0, 1})) :=
    AlgebraicGeometry.tilde.instModuleCarrierCarrierStalkAbPresheaf
      (R := CommRingCat.of (MvPolynomial (Fin 3) k)) (cexModule k) (varPrime k {0, 1})
  letI f₀ : ↥(cexModule k) →ₗ[MvPolynomial (Fin 3) k]
      ((cexSheaf k).presheaf.stalk (cexPt k {0, 1})) :=
    AlgebraicGeometry.StructureSheaf.toStalkₗ (MvPolynomial (Fin 3) k) ↥(cexModule k)
      (varPrime k {0, 1})
  have : IsLocalizedModule (varPrime k {0, 1}).asIdeal.primeCompl f₀ :=
    tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk
      (R := CommRingCat.of (MvPolynomial (Fin 3) k)) (cexModule k) (varPrime k {0, 1})
  have : IsScalarTower (MvPolynomial (Fin 3) k)
      ((cexScheme k).presheaf.stalk (cexPt k {0, 1}))
      ((cexSheaf k).presheaf.stalk (cexPt k {0, 1})) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hkill : ∀ b : MvPolynomial (Fin 3) k ⧸ (varPrime k {0, 2}).asIdeal,
      ∃ t : (varPrime k {0, 1}).asIdeal.primeCompl, (t : MvPolynomial (Fin 3) k) • b = 0 := by
    intro b
    refine ⟨⟨MvPolynomial.X 2, X_notMem_span_image_X (by decide)⟩, ?_⟩
    have h0 : (Ideal.Quotient.mk (varPrime k {0, 2}).asIdeal) (MvPolynomial.X 2) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_image_of_mem _ (by decide)))
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, h0, zero_mul]
  have hmax : Ideal.map (algebraMap (MvPolynomial (Fin 3) k)
        ((cexScheme k).presheaf.stalk (cexPt k {0, 1}))) (varPrime k {0, 1}).asIdeal
      = maximalIdeal ((cexScheme k).presheaf.stalk (cexPt k {0, 1})) := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal
        ((cexScheme k).presheaf.stalk (cexPt k {0, 1})) (varPrime k {0, 1}).asIdeal,
      IsLocalization.map_under (varPrime k {0, 1}).asIdeal.primeCompl]
  have hloc : Submodule.localized' ((cexScheme k).presheaf.stalk (cexPt k {0, 1}))
        (varPrime k {0, 1}).asIdeal.primeCompl (Algebra.linearMap (MvPolynomial (Fin 3) k)
          ((cexScheme k).presheaf.stalk (cexPt k {0, 1})))
        (varPrime k {0, 1}).asIdeal
      = maximalIdeal ((cexScheme k).presheaf.stalk (cexPt k {0, 1})) := by
    rw [← hmax, Ideal.map, Ideal.span, Submodule.localized'_eq_span, Algebra.coe_linearMap]
  letI g : ↥(cexModule k) →ₗ[MvPolynomial (Fin 3) k]
      ↥(Submodule.localized' ((cexScheme k).presheaf.stalk (cexPt k {0, 1}))
        (varPrime k {0, 1}).asIdeal.primeCompl (Algebra.linearMap (MvPolynomial (Fin 3) k)
          ((cexScheme k).presheaf.stalk (cexPt k {0, 1})))
        (varPrime k {0, 1}).asIdeal) :=
    Submodule.toLocalized' ((cexScheme k).presheaf.stalk (cexPt k {0, 1}))
        (varPrime k {0, 1}).asIdeal.primeCompl (Algebra.linearMap (MvPolynomial (Fin 3) k)
          ((cexScheme k).presheaf.stalk (cexPt k {0, 1})))
        (varPrime k {0, 1}).asIdeal ∘ₗ
      LinearMap.fst (MvPolynomial (Fin 3) k) ↥(varPrime k {0, 1}).asIdeal
        (MvPolynomial (Fin 3) k ⧸ (varPrime k {0, 2}).asIdeal)
  have : IsLocalizedModule (varPrime k {0, 1}).asIdeal.primeCompl g :=
    isLocalizedModule_comp_fst _ _ hkill
  refine LinearEquiv.trans
    (LinearEquiv.extendScalarsOfIsLocalization (varPrime k {0, 1}).asIdeal.primeCompl
      ((cexScheme k).presheaf.stalk (cexPt k {0, 1}))
      (IsLocalizedModule.linearEquiv (varPrime k {0, 1}).asIdeal.primeCompl f₀ g))
    (LinearEquiv.ofEq _ _ hloc)

/-! #### The refutation at `X = Spec k[u, v, w]` -/

/-- **The existence clause of [Stacks, Tag 0DX5] is false.** For `X = Spec k[u, v, w]`,
`Z = V(u, v)` and `F = (u, v)~ ⊕ (k[u, v, w]/(u, w))~` there is *no* map out of `F` which is an
improvement of `F` along `Z`.

All five inputs of
`Stacks.ImprovementCounterexample.not_isImprovement_of_linearEquiv_maximalIdeal` are discharged:
the three points `(0) ⤳ (u, v) ⤳ (u, v, w)` against `Z = V(u, v)`; that `(u, v, w)` is reached
from outside `Z` and `(u, v)` is not, which is the computation `Ass(F) = {(0), (u, w)}` together
with `(u, w) ⋖ (u, v, w)` and the chain `(0) ⊊ (u) ⊊ (u, v)`; that `𝒪_{X,𝔭}` is regular local of
dimension two; the identification `F_𝔭 ≅ 𝔪_𝔭`; and the nonvanishing of `F` at the generic
point.

That `F` satisfies the source's own hypothesis on the module it improves —
coherence — is `Stacks.ImprovementCounterexample.isCoherent_cexSheaf`, and that `Z` is closed is
`Stacks.ImprovementCounterexample.isClosed_cexZ`. The hypotheses the source places on `X` are
machine-checked too — Noetherianity by instance search,
`Stacks.ImprovementCounterexample.isUniversallyCatenary_cexScheme` and
`Stacks.ImprovementCounterexample.hasSerreCondition_one_formalFibres_cexScheme` — so what is
refuted is the source's assertion at the source's own five hypotheses; they are collected under
"Which of the source's hypotheses are witnessed here" in the module docstring above. -/
theorem not_exists_isImprovement_cexSheaf :
    ¬ ∃ (G : (cexScheme k).Modules) (φ : cexSheaf k ⟶ G), IsImprovement (cexZ k) φ := by
  rintro ⟨G, φ, h⟩
  have hdim : ringKrullDim ((cexScheme k).presheaf.stalk (cexPt k {0, 1}))
      = (2 : WithBot ℕ∞) := by
    rw [ringKrullDim_stalk_cexPt, show ({0, 1} : Finset (Fin 3)).card = 2 by decide]
    rfl
  have hpq : cexPt k {0, 1} ⤳ cexPt k {0, 1, 2} :=
    (PrimeSpectrum.le_iff_specializes _ _).mp
      (Ideal.span_mono (Set.image_mono (Finset.coe_subset.mpr uv_subset_uvw)))
  have hηp : cexPt k (∅ : Finset (Fin 3)) ⤳ cexPt k {0, 1} :=
    (PrimeSpectrum.le_iff_specializes _ _).mp
      (Ideal.span_mono (Set.image_mono (by simp)))
  exact not_isImprovement_of_linearEquiv_maximalIdeal φ
    (cexPt_mem_cexZ k (le_refl _)) (cexPt_mem_cexZ k uv_subset_uvw)
    hpq hηp (cexPt_notMem_cexZ k (by decide))
    (reachedFromOutside_cexSheaf_uvw k) (not_reachedFromOutside_cexSheaf_uv k)
    hdim (nontrivial_stalk_cexSheaf_generic k)
    (linearEquiv_stalk_cexSheaf_maximalIdeal k) h

end Cex

end Stacks.ImprovementCounterexample

end
