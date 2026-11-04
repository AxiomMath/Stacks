module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-!
# Finiteness of a separated module with finite reduction over a precomplete ring

Proof of Stacks 031D. Let `R` be a ring, let `I ⊆ R` be an ideal and let `M` be an `R`-module which
is `I`-adically separated, i.e. `⋂_{n ≥ 1} IⁿM = 0`. If `M/IM` is a finite `R/I`-module and `R` is
`I`-adically precomplete, then `M` is a finite `R`-module.

Since `R/I` is a finite `R`-module, the reduction `M/IM` is one too, so a finite free module `Rⁿ`
maps onto it; as `Rⁿ` is projective that map lifts to an `f : Rⁿ → M` which is surjective modulo
`I`. Now `Rⁿ` is `I`-adically precomplete because `R` is and adic completion commutes with finite
products, and `M` is `I`-adically Hausdorff because `⋂ IⁿM = 0`, so `f` is surjective on the nose
and `M` is a finite `R`-module.

## Main results

* `Stacks.AdicCompletion.SeparatedFiniteness.solution`: the statement of Stacks 031D.

## Implementation notes

The Stacks Project's route passes through the submodule `M' = ⟨x₁, …, xₙ⟩ ⊆ M`, proves `M'` complete
from [Stacks, Tag 031B] and compares completions via [Stacks, Tag 0315]. The route taken here
replaces that comparison by the single lemma `surjective_of_mkQ_comp_surjective`, which is exactly
the statement that a map from a precomplete module to a Hausdorff module surjective modulo `I` is
surjective; it needs only precompleteness of `R`, which is why the statement assumes that instead
of the source's completeness. The three hypotheses of that lemma are supplied by the three
lemmas below, one each.

None of the three is in Mathlib. `isHausdorff_iff_iInf_pow_smul_top_eq_bot` is the converse of
`IsHausdorff.iInf_pow_smul`. `isPrecomplete_pi` is deduced from `AdicCompletion.piEquivOfFintype`,
adic completion commuting with finite products, together with `AdicCompletion.of_surjective_iff`,
rather than from a componentwise description of `Iⁿ • ⊤` in a product.
`exists_surjective_mkQ_comp` is the projectivity of `Rⁿ`, and it is what replaces the explicit lift
of a generating family of `M/IM` to elements `x₁, …, xₙ ∈ M`: the composite `Rⁿ → M → M/IM` the
source writes down by hand is a lift of a surjection along `M ↠ M/IM`.

## References

* [Stacks Project, Tag 031D](https://stacks.math.columbia.edu/tag/031D)
-/

namespace Stacks.AdicCompletion.SeparatedFiniteness

open Function Submodule

/-- A module is `I`-adically Hausdorff precisely when its `I`-adic filtration has zero
intersection. The forward direction is `IsHausdorff.iInf_pow_smul`. -/
private theorem isHausdorff_iff_iInf_pow_smul_top_eq_bot {R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] :
    IsHausdorff I M ↔ ⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) = ⊥ :=
  ⟨IsHausdorff.iInf_pow_smul, fun hsep ↦ ⟨fun x hx ↦ by
    simpa [hsep] using (Submodule.mem_iInf _).2 fun n ↦ SModEq.zero.1 (hx n)⟩⟩

/-- A finite product of `I`-adically precomplete modules is `I`-adically precomplete: adic
completion commutes with finite products, so `AdicCompletion.of` is surjective on the product as
soon as it is surjective on every factor. -/
private theorem isPrecomplete_pi {R : Type*} [CommRing R] {I : Ideal R} {ι : Type*} [Finite ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, IsPrecomplete I (M i)] : IsPrecomplete I (∀ i, M i) := by
  classical
  cases nonempty_fintype ι
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  choose x hx using fun i ↦ AdicCompletion.of_surjective I (M i) (AdicCompletion.pi I M y i)
  refine ⟨x, (AdicCompletion.piEquivOfFintype I M).injective (funext fun i ↦ ?_)⟩
  simpa [AdicCompletion.pi, AdicCompletion.map_of] using hx i

/-- If the quotient `M ⧸ N` is a finite `R`-module, then some map from a finite free module to `M`
is surjective modulo `N`: a finite free module is projective, so a surjection `Rⁿ ↠ M ⧸ N` lifts
along `N.mkQ`. -/
public theorem exists_surjective_mkQ_comp {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (N : Submodule R M) [Module.Finite R (M ⧸ N)] :
    ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Surjective (N.mkQ ∘ₗ f) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R (M ⧸ N)
  obtain ⟨f, hf⟩ := Module.projective_lifting_property N.mkQ g N.mkQ_surjective
  exact ⟨n, f, hf ▸ hg⟩

/-- Over an `I`-adically precomplete ring `R`, an `R`-module `M` with `⨅ n, I ^ n • ⊤ = ⊥`
whose reduction `M ⧸ I • ⊤` is a finite `R ⧸ I`-module is a finite `R`-module. -/
public theorem solution {R : Type*} [CommRing R] (I : Ideal R) {M : Type*} [AddCommGroup M]
    [Module R M] [IsPrecomplete I R] (hsep : ⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) = ⊥)
    (hfin : Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) :
    Module.Finite R M := by
  have : IsHausdorff I M := isHausdorff_iff_iInf_pow_smul_top_eq_bot.2 hsep
  have : Module.Finite R (M ⧸ I • (⊤ : Submodule R M)) := Module.Finite.trans (R ⧸ I) _
  obtain ⟨n, f, hf⟩ := exists_surjective_mkQ_comp (I • (⊤ : Submodule R M))
  have : IsPrecomplete I (Fin n → R) := isPrecomplete_pi
  exact .of_surjective f (surjective_of_mkQ_comp_surjective hf)

end Stacks.AdicCompletion.SeparatedFiniteness

/-!
# Finiteness of a separated module with finite reduction over a precomplete ring

Let `R` be a commutative ring, let `I ⊆ R` be an ideal and let `M` be an `R`-module. Nakayama's
lemma turns finiteness of the reduction `M/IM` into finiteness of `M` as soon as `M` is already
known to be finite; over an `I`-adically precomplete ring the a priori finiteness can be dropped,
at the cost of asking that `M` be `I`-adically separated:

if `R` is `I`-adically precomplete, `⋂_{n ≥ 1} IⁿM = 0`, and `M/IM` is a finite `R/I`-module, then
`M` is a finite `R`-module.

The mechanism is that a lift of a generating set of `M/IM` gives a map `Rⁿ → M` which is surjective
modulo `I`, and precompleteness of the source together with separatedness of the target upgrade
that to surjectivity: if `x₁, …, xₙ ∈ M` lift generators of `M/IM`, then `f : Rⁿ → M`, `eᵢ ↦ xᵢ`,
has `M/IM`-reduction surjective by construction, `Rⁿ` is `I`-adically precomplete because `R` is,
and `M` is `I`-adically Hausdorff because `⋂ IⁿM = 0`, so `f` is surjective and `M` is generated by
`x₁, …, xₙ`.

## Main results

* `Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top`: over an `I`-adically
  precomplete ring `R`, an `I`-adically separated module whose reduction `M/IM` is a finite
  `R/I`-module is a finite `R`-module.

## Implementation notes

The source asks `R` to be `I`-adically *complete*; only `IsPrecomplete I R` is used, so that is
what is assumed here. The two differ by `IsHausdorff I R`, which the argument never uses:
separatedness is needed on the *target* of `Rⁿ → M`, where hypothesis (2) supplies it, and the ring
is needed only as the source, where precompleteness is enough. The weakening is strict —
`IsPrecomplete ⊤ M` holds for every module while `IsHausdorff ⊤ M` forces `M = 0`, so `ℚ` is
`⊤`-precomplete and not `⊤`-adically complete — and it is free at every use site, since
`IsAdicComplete.toIsPrecomplete` turns the source's hypothesis into this one by instance
resolution. This is also the granularity of the Mathlib lemma that does the work, whose
precompleteness hypothesis is on the source and whose Hausdorff hypothesis is on the target.

`IⁿM` is written Mathlib's way, as `I ^ n • (⊤ : Submodule R M)`, so the source's
`⋂_{n ≥ 1} IⁿM = (0)` is the submodule equality `⨅ n, I ^ n • (⊤ : Submodule R M) = ⊥`; this is
character-for-character the spelling the neighbouring [Stacks, Tag 031B] uses for the same
hypothesis. The infimum is taken over all `n : ℕ` rather than over `n ≥ 1`, which changes nothing:
`I ^ 0 • ⊤ = ⊤` is the greatest element, so it contributes nothing to the infimum and the two
submodules are equal. The condition is equivalent to Mathlib's `IsHausdorff I M`; the literal
intersection is kept because the source states it as an equality of submodules, the derivation of
`IsHausdorff I M` from it is four lines, and it costs a user nothing.

`M/IM` is `M ⧸ (I • ⊤ : Submodule R M)`, an `R ⧸ I`-module through
`Module.instQuotientIdealSubmoduleHSMulTop`, which is the spelling this project already uses for
that reduction (Stacks 00ML, 05CG, 0471) and the one Mathlib's own converse
`Submodule.instFiniteQuotientIdealHSMulTop` is stated in. Since the `R`-action on it factors
through `R ⧸ I`, the hypothesis is interchangeable with finiteness of `M/IM` as an `R`-module; the
source's ring `R/I` is kept.

`I` is explicit, since the conclusion does not mention it.

## References

* [Stacks Project, Tag 031D](https://stacks.math.columbia.edu/tag/031D)
* [Stacks Project, Tag 031B](https://stacks.math.columbia.edu/tag/031B) for completeness of a
  finite separated module
* [Stacks Project, Tag 0315](https://stacks.math.columbia.edu/tag/0315) for surjectivity of
  `(M')^∧ → M^∧`

## Tags

adic completion, precomplete ring, Nakayama, finite module
-/


@[expose] public section

/-- Let `R` be a ring, let `I ⊆ R` be an ideal and let `M` be an `R`-module. Assume that `R` is
`I`-adically precomplete, that `⋂_{n ≥ 1} IⁿM = 0`, and that `M/IM` is a finite `R/I`-module.
Then `M` is a finite `R`-module. Here `IⁿM` is `I ^ n • (⊤ : Submodule R M)`, so the second
hypothesis is `⨅ n, I ^ n • ⊤ = ⊥`, and `M/IM` is `M ⧸ I • ⊤` with its canonical `R ⧸ I`-module
structure. -/
@[stacks 031D]
public theorem Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top
    {R : Type*} [CommRing R] (I : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]
    [IsPrecomplete I R] (hsep : ⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) = ⊥)
    (hfin : Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) :
    Module.Finite R M :=
      by exact Stacks.AdicCompletion.SeparatedFiniteness.solution I hsep hfin

end
