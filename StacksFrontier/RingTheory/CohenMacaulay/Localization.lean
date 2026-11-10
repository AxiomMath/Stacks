module

import StacksFrontier.RingTheory.Depth.Dimension
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.ENatToNat

public import StacksFrontier.RingTheory.Depth.Localization
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.RegularLocalRing.MaximalCohenMacaulay
public import StacksFrontier.Order.HeightCoheight
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Cohen–Macaulayness of a module localizes

Proof of `Module.depth_eq_supportDim_of_isLocalizedModule` (Stacks 0AAG): let `(R, 𝔪)` be a
Noetherian local ring, let `M` be a finite `R`-module which is Cohen–Macaulay, i.e.
`depth_𝔪(M) = dim Supp(M)`, and let `𝔭 ⊆ R` be a prime in the support of `M`. Then `M_𝔭` is
Cohen–Macaulay over `R_𝔭`, that is `depth_{𝔭R_𝔭}(M_𝔭) = dim Supp(M_𝔭)`.

The inequality `depth(M_𝔭) ≤ dim Supp(M_𝔭)` is Stacks 00LK, applied to the nonzero finite
`R_𝔭`-module `M_𝔭` and its maximal ideal; Nakayama's lemma supplies the hypothesis
`𝔭R_𝔭 • M_𝔭 ≠ M_𝔭` (`ofList_smul_top_ne_top_of_le_maximalIdeal`).

For the reverse inequality, write `d = dim(R/𝔭)`. Stacks 0FCC gives
`depth(M) ≤ depth(M_𝔭) + d`, and Cohen–Macaulayness turns the left-hand side into
`dim Supp(M)`, so `dim Supp(M) ≤ depth(M_𝔭) + d`. On the other side
`dim Supp(M_𝔭) + d ≤ dim Supp(M)`, the two summands on the left being the height and the
coheight of the point `𝔭` of the poset `Supp(M)`, whose sum is at most `krullDim Supp(M)`. As `d`
is a natural number — the ring `R/𝔭` is nonzero and `dim(R/𝔭) ≤ dim(R) < ∞` — it cancels,
leaving `dim Supp(M_𝔭) ≤ depth(M_𝔭)`.

## Main results

* `Stacks.CohenMacaulay.ModuleLocalization.solution`: the tagged statement.

## Implementation notes

*One application of Stacks 0FCC, not an induction along a chain.* The source reduces to the case
where no prime lies strictly between `𝔭` and `𝔪`, so that `dim(R/𝔭) = 1`, and then iterates the
one-step estimate `dim Supp(M_𝔭) ≤ dim Supp(M) - 1` along a maximal chain
`𝔭 = 𝔭_c ⊂ ⋯ ⊂ 𝔭_1 ⊂ 𝔪`. The reduction is unnecessary: the estimate holds with `dim(R/𝔭)` in
place of `1` for every prime `𝔭` of `Supp(M)`, and that is exactly the term Stacks 0FCC produces,
so the two inequalities can be combined at `𝔭` itself. This is
`supportDim_add_ringKrullDim_quotient_le_supportDim` below, whose proof is the source's
"a chain in `Supp(M_𝔭)` can be prolonged inside `Supp(M)`" argument read as the poset inequality
`height 𝔭 + coheight 𝔭 ≤ krullDim Supp(M)`. It uses neither Noetherianity nor locality of `R`,
and not finiteness of `M` either.

*The two summands are a height and a coheight in `Supp(M)`.* On the height side, `Spec(R_𝔭)` is
order isomorphic to the primes contained in `𝔭` by
`IsLocalization.AtPrime.primeSpectrumOrderIso`, and `PrimeSpectrum.comap (algebraMap R R_𝔭)`
carries `Supp(M_𝔭)` into `Supp(M)`: it carries it into the support of `M_𝔭` as an `R`-module
(`Module.support_subset_preimage_comap`), and that support is contained in `Supp(M)` because an
element of `R` killing `m` kills every fraction `m/s` (`support_subset_of_isLocalizedModule`). A
chain in `Supp(M_𝔭)` is therefore a chain in `Supp(M)` below `𝔭`. On the coheight side `Supp(M)`
is stable under specialization, so `V(𝔭) ⊆ Supp(M)`, and `dim(R/𝔭)` is the dimension of
`V(𝔭) = Set.Ici 𝔭` by `ringKrullDim_quotient`, so no prime of a quotient ring appears. The
order-theoretic inequality `height x + coheight x ≤ krullDim α`, which holds in any preorder, is
not recorded in Mathlib; it is the imported `Order.height_add_coheight_le_krullDim`, one instance
of `Order.krullDim_eq_iSup_height_add_coheight_of_nonempty`.

## References

* [StacksProject 0AAG](https://stacks.math.columbia.edu/tag/0AAG)
-/

namespace Stacks.CohenMacaulay.ModuleLocalization

/-- Over a Noetherian local ring `dim(R/𝔭)` is a natural number — the ring `R/𝔭` is nonzero, so
the dimension is not `⊥`, and `dim(R/𝔭) ≤ dim(R) < ∞` — hence it cancels from both sides of an
inequality in `WithBot ℕ∞`. -/
private lemma le_of_add_ringKrullDim_quotient_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (p : Ideal R) [p.IsPrime] {a b : WithBot ℕ∞}
    (h : a + ringKrullDim (R ⧸ p) ≤ b + ringKrullDim (R ⧸ p)) : a ≤ b := by
  lift ringKrullDim (R ⧸ p) to ℕ∞ using
    (by rw [ne_eq, ringKrullDim_eq_bot_iff_subsingleton]; exact not_subsingleton _) with d hd
  lift d to ℕ using by
    simpa [← hd] using ne_top_of_le_ne_top ringKrullDim_ne_top (ringKrullDim_quotient_le p)
  exact ENat.WithBot.add_le_add_natCast_right_iff.mp h

section Localization

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {Rₚ : Type*} [CommRing Rₚ] [Algebra R Rₚ] {Mₚ : Type*} [AddCommGroup Mₚ] [Module R Mₚ]
  [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]

/-- **A localization of `M` has no larger support over `R` than `M` itself.** An `r ∈ R` killing
`m` kills every fraction `m/s`, so a prime outside `Supp(M)` is outside `Supp(S⁻¹M)`. No
finiteness is needed. -/
private lemma support_subset_of_isLocalizedModule (S : Submonoid R) (f : M →ₗ[R] Mₚ)
    [IsLocalizedModule S f] : Module.support R Mₚ ⊆ Module.support R M := fun q hq => by
  by_contra h
  rw [Module.notMem_support_iff'] at h
  refine absurd hq (Module.notMem_support_iff'.mpr fun y => ?_)
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f y
  obtain ⟨r, hr, hrm⟩ := h m
  exact ⟨r, hr, by rw [Function.uncurry_apply_pair, ← IsLocalizedModule.mk'_smul, hrm,
    IsLocalizedModule.mk'_zero]⟩

variable (p : Ideal R) [hp : p.IsPrime]
  (hsupp : (⟨p, hp⟩ : PrimeSpectrum R) ∈ Module.support R M)

/-- **The dimension of `Supp(M_𝔭)` is at most the height of `𝔭` in `Supp(M)`.** `Spec` of the
structure map is an order isomorphism of `Spec(R_𝔭)` onto the primes contained in `𝔭`
(`IsLocalization.AtPrime.primeSpectrumOrderIso`) which carries `Supp(M_𝔭)` into `Supp(M)`, so a
chain in `Supp(M_𝔭)` is a chain in `Supp(M)` below `𝔭`. -/
private lemma supportDim_le_height [IsLocalization.AtPrime Rₚ p] (f : M →ₗ[R] Mₚ)
    [IsLocalizedModule p.primeCompl f] :
    Module.supportDim Rₚ Mₚ ≤
      (Order.height (⟨⟨p, hp⟩, hsupp⟩ : Module.support R M) : WithBot ℕ∞) := by
  have hmem : ∀ q : Module.support Rₚ Mₚ,
      PrimeSpectrum.comap (algebraMap R Rₚ) q.1 ∈ Module.support R M := fun q =>
    support_subset_of_isLocalizedModule p.primeCompl f
      (Module.support_subset_preimage_comap (A := Rₚ) q.2)
  have hle : ∀ q : PrimeSpectrum Rₚ,
      PrimeSpectrum.comap (algebraMap R Rₚ) q ≤ (⟨p, hp⟩ : PrimeSpectrum R) := fun q =>
    (IsLocalization.AtPrime.primeSpectrumOrderIso Rₚ p q).2
  rw [Module.supportDim, Order.height_eq_krullDim_Iic]
  exact Order.krullDim_le_of_strictMono (fun q => ⟨⟨_, hmem q⟩, hle q.1⟩)
    fun _ _ hab => (IsLocalization.AtPrime.primeSpectrumOrderIso Rₚ p).strictMono hab

/-- **The dimension of `R/𝔭` is at most the coheight of `𝔭` in `Supp(M)`.** The support is stable
under specialization, so `V(𝔭) = Set.Ici 𝔭` is contained in `Supp(M)`, and `dim(R/𝔭)` is the
dimension of `V(𝔭)`. -/
private lemma ringKrullDim_quotient_le_coheight :
    ringKrullDim (R ⧸ p) ≤
      (Order.coheight (⟨⟨p, hp⟩, hsupp⟩ : Module.support R M) : WithBot ℕ∞) := by
  have hIci : PrimeSpectrum.zeroLocus (R := R) (p : Set R) =
    Set.Ici (⟨p, hp⟩ : PrimeSpectrum R) := rfl
  rw [ringKrullDim_quotient, hIci, Order.coheight_eq_krullDim_Ici]
  exact Order.krullDim_le_of_strictMono
    (fun q => ⟨⟨q.1, Module.mem_support_mono q.2 hsupp⟩, q.2⟩) fun _ _ hab => hab

include hsupp in
/-- **Localizing at `𝔭` costs `dim(R/𝔭)` of the dimension of the support.** For a module `M` over a
commutative ring `R` and a prime `𝔭 ∈ Supp(M)`, `dim Supp(M_𝔭) + dim(R/𝔭) ≤ dim Supp(M)`: the two
summands on the left are the height and the coheight of the point `𝔭` of the poset `Supp(M)`. -/
@[ega "0 16.5.10" "partial"]
private lemma supportDim_add_ringKrullDim_quotient_le_supportDim [IsLocalization.AtPrime Rₚ p]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule p.primeCompl f] :
    Module.supportDim Rₚ Mₚ + ringKrullDim (R ⧸ p) ≤ Module.supportDim R M :=
  (add_le_add (supportDim_le_height p hsupp f) (ringKrullDim_quotient_le_coheight p hsupp)).trans
    (Order.height_add_coheight_le_krullDim _)

end Localization

/-- **A Cohen–Macaulay finite module stays Cohen–Macaulay after localizing at a prime of its
support.** For `(R, 𝔪)` Noetherian local, `M` a finite `R`-module with
`depth_𝔪(M) = dim Supp(M)`, and `f : M →ₗ[R] Mₚ` a localization of `M` at a prime `𝔭` with
`Mₚ` nonzero, `depth_{𝔭R_𝔭}(M_𝔭) = dim Supp(M_𝔭)`. This is the proof of
`Module.depth_eq_supportDim_of_isLocalizedModule`. -/
public theorem solution {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hM : (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) = Module.supportDim R M)
    (p : Ideal R) [p.IsPrime] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] (Mₚ : Type*) [AddCommGroup Mₚ] [Nontrivial Mₚ]
    [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ)
    [IsLocalizedModule p.primeCompl f] :
    (Module.depth Rₚ (IsLocalRing.maximalIdeal Rₚ) Mₚ : WithBot ℕ∞) = Module.supportDim Rₚ Mₚ := by
  have hfin : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule p.primeCompl f
  -- `𝔭` lies in the support of `M`, because `M_𝔭` is nonzero.
  have hsupp : (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) ∈ Module.support R M :=
    Module.mem_support_iff.mpr (IsLocalizedModule.iso p.primeCompl f).toEquiv.nontrivial
  refine le_antisymm (Module.depth_le_supportDim Rₚ (IsLocalRing.maximalIdeal Rₚ) Mₚ
    (ofList_smul_top_ne_top_of_le_maximalIdeal Rₚ Mₚ _ le_rfl)) ?_
  -- Stacks 0FCC and the drop of the support dimension, after cancelling `dim (R ⧸ 𝔭)`.
  exact le_of_add_ringKrullDim_quotient_le p
    ((supportDim_add_ringKrullDim_quotient_le_supportDim p hsupp f).trans (hM.symm.trans_le
      (Module.depth_le_depth_localized_add_ringKrullDim_quotient M p Rₚ Mₚ f)))

end Stacks.CohenMacaulay.ModuleLocalization

/-!
# Cohen–Macaulayness of a module is inherited by its localizations

Let `(R, 𝔪)` be a Noetherian local ring and let `M` be a finite `R`-module which is
Cohen–Macaulay, that is `depth_𝔪(M) = dim Supp(M)` (Definition 00N3). Then for every prime
`𝔭 ⊆ R` belonging to the support of `M`, the localization `M_𝔭` is Cohen–Macaulay over the local
ring `R_𝔭`:
`depth_{𝔭R_𝔭}(M_𝔭) = dim Supp(M_𝔭)`.
The case `M = R` says that a localization of a Cohen–Macaulay local ring at a prime is again
Cohen–Macaulay (Tag 00NB), and the statement is what makes Definition 0AAH — Cohen–Macaulayness
of a finite module over a not necessarily local Noetherian ring — checkable at the maximal ideals
alone.

The reason is a one-step descent, iterated along a maximal chain
`𝔭 = 𝔭_c ⊂ 𝔭_{c-1} ⊂ … ⊂ 𝔭_1 ⊂ 𝔪`, so that one may assume no prime lies strictly between `𝔭`
and `𝔪`. Then `dim Supp(M_𝔭) ≤ dim Supp(M) - 1`, since any chain of primes in `Supp(M_𝔭)` is a
chain in `Supp(M)` that can be prolonged by `𝔪`, while `depth(M_𝔭) ≥ depth(M) - dim(R/𝔭) =
depth(M) - 1` (Tag 0FCC). Hence `depth(M_𝔭) ≥ dim Supp(M_𝔭)`, and the reverse inequality holds
because `M_𝔭` is nonzero (Tag 00LK).

## Main results

* `Module.depth_eq_supportDim_of_isLocalizedModule`: `depth_{𝔭R_𝔭}(M_𝔭) = dim Supp(M_𝔭)` for
  `𝔭` in the support of a Cohen–Macaulay finite module `M` over a Noetherian local ring.

## Implementation notes

Faithfulness to [StacksProject 0AAG]:

1. No dead hypothesis. Taking `𝔭 = 𝔪`, so that `Rₚ = R` and `Mₚ = M`, turns the conclusion into
   `hM` itself, so the Cohen–Macaulayness of `M` cannot be dropped. `Nontrivial Mₚ` cannot be
   dropped either: for `R = k[[x]]`, `M = R ⧸ (x)` and `𝔭 = (0)` the module `M` is Cohen–Macaulay
   with `depth_𝔪(M) = dim Supp(M) = 0`, while `M_𝔭 = 0` has `depth = ⊤` and `dim Supp = ⊥`; see
   the discussion of this hypothesis below. `IsNoetherianRing R`, `IsLocalRing R` and
   `Module.Finite R M` are the source's: locality is what makes `depth_𝔪` the depth of the
   source, and Noetherianity together with finiteness are what both halves of the argument
   (Tags 0FCC and 00LK) consume.
2. The scalars and base are the source's. The hypothesis is an equation over `R`, between
   `Module.depth R (IsLocalRing.maximalIdeal R) M` and `Module.supportDim R M`; the conclusion is
   the same equation over `Rₚ`, between `Module.depth Rₚ (IsLocalRing.maximalIdeal Rₚ) Mₚ` and
   `Module.supportDim Rₚ Mₚ` — the depth is along the maximal ideal of `Rₚ`, not along `𝔭` in
   `R`, and the support is a set of primes of `Rₚ`, not of `R`.
3. The canonical maps are pinned. `IsLocalization.AtPrime Rₚ p` pins `Rₚ` as `R_𝔭` together with
   its structure map `algebraMap R Rₚ`, `IsLocalizedModule p.primeCompl f` pins the `R`-linear
   `f : M →ₗ[R] Mₚ` as the localization map `M → M_𝔭`, and `IsScalarTower R Rₚ Mₚ` makes the
   `Rₚ`-module structure carrying the conclusion the one transported along `f`. So the statement
   is about the localization, not about the existence of some module with the same invariants.
4. Not degenerate. For `R = k[[x, y]]`, `M = R ⧸ (x)` and `𝔭 = (x)` the hypothesis holds with
   `depth_𝔪(M) = dim Supp(M) = 1`, the localization `Mₚ = k((y))` is nonzero, `Rₚ` is a discrete
   valuation ring, and the conclusion is the equality `0 = 0` of two genuinely computed
   invariants: `𝔭R_𝔭` annihilates `Mₚ`, and `Supp(Mₚ) = {𝔭R_𝔭}`.

Four departures from the source's form, none of them weakening it.

*Cohen–Macaulayness is spelled out.* There is no predicate for Definition 00N3 in this library
yet, so both the hypothesis and the conclusion are the equation `depth_𝔪(N) = dim Supp(N)` that
the definition unfolds to, as in Tag 0C6G. Depth takes values in `ℕ∞` and `Module.supportDim` in
`WithBot ℕ∞`, the value `⊥` being reserved for the empty support of the zero module; both
equations are therefore read in `WithBot ℕ∞`, as in Tags 00LK and 0C6G.

*The hypothesis `𝔭 ∈ Supp(M)`, spelled `Nontrivial Mₚ`.* The source states the conclusion for
every prime `𝔭`, but with its own conventions — `depth(0) = ∞` (Definition 00LI) and
`dim(∅) = -∞` — the zero module is not Cohen–Macaulay, so the conclusion is false at a prime
outside `Supp(M)`; the counterexample is in item (1). The source's own proof needs the hypothesis
at exactly one point: the inequality `dim Supp(M_𝔭) ≥ depth(M_𝔭)` is taken from Tag 00LK, whose
hypothesis is that the module be nonzero. The condition is stated as `Nontrivial Mₚ` rather than
as `⟨𝔭, _⟩ ∈ Module.support R M` because the two are equivalent (`Module.mem_support_iff`) and
the former is about the data at hand. It is free in the applications: for `M = R` (Tag 00NB) it
is `IsLocalization.AtPrime.nontrivial`.

*The localization is presented abstractly.* Rather than fixing the models
`Localization.AtPrime 𝔭` and `LocalizedModule 𝔭.primeCompl M`, the statement quantifies over any
`Rₚ` with `IsLocalization.AtPrime Rₚ p` and any `f : M →ₗ[R] Mₚ` with
`IsLocalizedModule p.primeCompl f`, in arbitrary universes. Every such pair is uniquely
isomorphic to those models, so this is the same statement for each choice and saves every user
from transporting along the isomorphism. This is the shape of the neighbouring Tags 0FCC and
00NM, so those statements compose with this one without a bridge.

*`IsLocalRing Rₚ` is listed as an instance* although it follows from `IsLocalization.AtPrime Rₚ p`
by `IsLocalization.AtPrime.isLocalRing`, which is a theorem rather than an instance; it is needed
for `IsLocalRing.maximalIdeal Rₚ` to be available to the elaborator. Likewise
`IsNoetherianRing Rₚ` and `Module.Finite Rₚ Mₚ` are consequences of the hypotheses
(`IsLocalization.isNoetherianRing`, `Module.Finite.of_isLocalizedModule`) and are not assumed.

## References

* [StacksProject 0AAG](https://stacks.math.columbia.edu/tag/0AAG)

## Tags

Cohen-Macaulay module, depth, dimension of support, localization
-/

@[expose] public section

namespace Module

/-- **Cohen–Macaulayness localizes.** Let `(R, 𝔪)` be a Noetherian local ring and `M` a finite
`R`-module which is Cohen–Macaulay, i.e. `depth_𝔪(M) = dim Supp(M)` (Definition 00N3). Let
`𝔭 ⊆ R` be a prime in the support of `M`, presented by a localization `Rₚ` of `R` at `𝔭` and a
localization `f : M →ₗ[R] Mₚ` of `M` at `𝔭`. Then `M_𝔭` is Cohen–Macaulay over `R_𝔭`, that is
`depth_{𝔭R_𝔭}(M_𝔭) = dim Supp(M_𝔭)`. Both equations are read in `WithBot ℕ∞`, where
`Module.supportDim` lives. -/
@[stacks 0AAG "Cohen–Macaulayness is spelled out as `depth_𝔪(N) = dim Supp(N)`, the equation \
  Definition 00N3 unfolds to, there being no predicate for it in this library yet; the \
  localization is presented by `IsLocalization.AtPrime` and `IsLocalizedModule`; and `𝔭` is \
  required to lie in `Supp(M)`, spelled `Nontrivial Mₚ`, without which the conclusion is false \
  for the source's own conventions. See the module docstring.",
  ega "0 16.5.10",
  ega "0 16.5.13" "forward direction"]
public theorem depth_eq_supportDim_of_isLocalizedModule {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hM : (depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) = supportDim R M)
    (p : Ideal R) [p.IsPrime] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] (Mₚ : Type*) [AddCommGroup Mₚ] [Nontrivial Mₚ]
    [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ)
    [IsLocalizedModule p.primeCompl f] :
    (depth Rₚ (IsLocalRing.maximalIdeal Rₚ) Mₚ : WithBot ℕ∞) = supportDim Rₚ Mₚ :=
    by exact Stacks.CohenMacaulay.ModuleLocalization.solution (R := R) M hM p Rₚ Mₚ f

end Module

end

/-!
# Cohen–Macaulayness of a local ring localizes at a prime

Proof of Stacks 00NB, `Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime`: for
`(R, 𝔪)` a Noetherian local Cohen–Macaulay ring and `𝔭 ⊆ R` a prime, the local ring `R_𝔭` is
Cohen–Macaulay.

The source's proof is "special case of Lemma 0AAG", and the special case is `M = R`. Lemma 0AAG
says that a finite Cohen–Macaulay module over a Noetherian local ring stays Cohen–Macaulay after
localizing at a prime of its support, Cohen–Macaulayness of a module `N` being the equation
`depth_𝔪(N) = dim Supp(N)`. Taking `M = R`, localized along its structure map
`Algebra.linearMap R Rₚ`, turns both sides of that equation into the ones Stacks 00NB asks for,
because the support of a ring as a module over itself is its whole spectrum, so that
`dim Supp(R) = dim(R)` (`Module.supportDim_self_eq_ringKrullDim`); this is the same identification
that makes Definition 00NF, `depth_𝔪(M) = dim(R)`, agree with Definition 00N3 at `M = R`.

## Main results

* `Stacks.CohenMacaulay.LocalizationAtPrime.solution`: the tagged statement.

## Implementation notes

The hypothesis `𝔭 ∈ Supp(R)` that Lemma 0AAG carries as `Nontrivial Rₚ` is free here: `R_𝔭` is
assumed to be a local ring, and a local ring is nonzero. The localization map of `R` at `𝔭`, as a
module over itself, is the structure map `algebraMap R Rₚ` read `R`-linearly, i.e.
`Algebra.linearMap R Rₚ`; that it is a module localization at `𝔭.primeCompl` is inferred from
`IsLocalization.AtPrime Rₚ p`, so no model of `R_𝔭` is chosen.

## References

* [StacksProject 00NB](https://stacks.math.columbia.edu/tag/00NB)
-/

@[expose] public section

namespace Stacks.CohenMacaulay.LocalizationAtPrime

/-- **A localization of a Noetherian local Cohen–Macaulay ring at a prime is Cohen–Macaulay.**
The case `M = R` of `Module.depth_eq_supportDim_of_isLocalizedModule`, localized along
`Algebra.linearMap R Rₚ`. This is the proof of
`Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime`. -/
public theorem solution {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hR : Module.IsMaximalCohenMacaulay R R) (p : Ideal R)
    [p.IsPrime] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    [IsLocalRing Rₚ] : Module.IsMaximalCohenMacaulay Rₚ Rₚ := by
  have hR' : (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) = ringKrullDim R := hR
  have hM : (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) = Module.supportDim R R :=
    hR'.trans (Module.supportDim_self_eq_ringKrullDim R).symm
  change (Module.depth Rₚ (IsLocalRing.maximalIdeal Rₚ) Rₚ : WithBot ℕ∞) = ringKrullDim Rₚ
  exact (Module.depth_eq_supportDim_of_isLocalizedModule R hM p Rₚ Rₚ
    (Algebra.linearMap R Rₚ)).trans (Module.supportDim_self_eq_ringKrullDim Rₚ)

end Stacks.CohenMacaulay.LocalizationAtPrime

end

/-!
# Cohen–Macaulayness localizes at a prime

Let `(R, 𝔪)` be a Noetherian local Cohen–Macaulay ring and let `𝔭 ⊆ R` be a prime. Then the
local ring `R_𝔭` is Cohen–Macaulay as well.

Cohen–Macaulayness of a Noetherian local ring `S` says that its depth along its maximal ideal is
as large as the dimension of its spectrum allows, `depth_{𝔪_S}(S) = dim S`; the content of the
lemma is that this equality is inherited by every localization at a prime, even though both
sides drop. Concretely, going from `R` to `R_𝔭` cuts the dimension by `dim(R/𝔭)`, by the
dimension formula `dim R = dim R_𝔭 + dim(R/𝔭)` available in a Cohen–Macaulay local ring
(tag 00NA), and the depth drops by at most that much, so neither quantity can overshoot the
other.

## Main results

* `Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime`: a localization of a Noetherian local
  Cohen–Macaulay ring at a prime is again Cohen–Macaulay.

## Implementation notes

Cohen–Macaulayness of a Noetherian local ring `S` is spelled `Module.IsMaximalCohenMacaulay S S`
(tag 00NF), that is `depth_{𝔪_S}(S) = dim S`. This is Definition 00N8 verbatim: `S` is
Cohen–Macaulay when it is Cohen–Macaulay as a module over itself, i.e.
`depth_{𝔪_S}(S) = dim Supp(S)` (Definition 00N3), and `Supp(S) = Spec(S)` because `1` has zero
annihilator. The same spelling is used by tag 00NA, so the two statements compose without a bridge.

The localization is left abstract: `R_𝔭` is any `R`-algebra `Rₚ` with
`IsLocalization.AtPrime Rₚ p`, rather than the concrete `Localization.AtPrime p`, which is one
model of it. The source's more general statement about Cohen–Macaulay *modules* localizing is
Lemma 0AAG, of which this is the case `M = R`; it is a separate entity and is not restated here.

Faithfulness to [StackProject 00NB]:

1. No dead hypothesis. `hR` is the Cohen–Macaulay hypothesis on `R`; `[IsLocalRing R]` is what
   makes it a statement about `depth_𝔪`; `[IsNoetherianRing R]` is Definition 00N8's and is
   load-bearing, being what ties depth to dimension (without it the depth hypothesis says
   nothing about chains of primes); `[p.IsPrime]` is the prime being localized at, and
   `[Algebra R Rₚ]` together with `[IsLocalization.AtPrime Rₚ p]` is what makes `Rₚ` be `R_𝔭`.
   The remaining `[IsLocalRing Rₚ]` occurs in the conclusion itself, which cannot be formed
   without it; it follows from `[IsLocalization.AtPrime Rₚ p]` by
   `IsLocalization.AtPrime.isLocalRing`, which Mathlib cannot make an instance because `p` is
   not inferable from `Rₚ`, so assuming it does not weaken the statement.
2. The scalars and base are the source's. The conclusion is Cohen–Macaulayness of `R_𝔭` *over
   itself*: the depth is that of `Rₚ` as an `Rₚ`-module along the maximal ideal of `Rₚ`, and the
   dimension is `ringKrullDim Rₚ`. It is not the depth of `R_𝔭` as an `R`-module, nor the depth
   of `R` along `𝔭`. Likewise the hypothesis is over `R` along the maximal ideal of `R`.
3. The canonical map is pinned. `IsLocalization.AtPrime Rₚ p` pins `Rₚ` as the localization of
   `R` at `𝔭` through the canonical `algebraMap R Rₚ`, so no localization is chosen and no mere
   existence is asserted; the maximal ideal appearing in the conclusion is the canonical one of
   the local ring `Rₚ`, which is `𝔭 R_𝔭 = p.map (algebraMap R Rₚ)` by
   `IsLocalization.AtPrime.map_eq_maximalIdeal`.
4. The instantiation is not degenerate. Take `R` a two-dimensional regular local ring, say the
   local ring of the affine plane at the origin: it is Cohen–Macaulay, and for `𝔭` the
   height-one prime of a coordinate line the conclusion is the Cohen–Macaulayness of the
   one-dimensional local ring `R_𝔭`, so both `depth` and `dim` are strictly between `0` and
   `dim R` and the hypothesis is not inherited for trivial reasons. The two extreme cases,
   `𝔭 = 𝔪` (where `R_𝔭 = R`) and `𝔭` minimal (where `dim R_𝔭 = 0`), are genuine instances too.

## References

* [StackProject 00NB](https://stacks.math.columbia.edu/tag/00NB)

## Tags

Cohen-Macaulay ring, local ring, localization, depth, Krull dimension
-/

@[expose] public section

/-- **Cohen–Macaulayness localizes at a prime.** If `R` is a Noetherian local Cohen–Macaulay
ring, that is `depth_𝔪(R) = dim R`, then for every prime `𝔭` of `R` the local ring `R_𝔭` is
Cohen–Macaulay: `depth_{𝔭R_𝔭}(R_𝔭) = dim R_𝔭`. The localization is any `R`-algebra `Rₚ` with
`IsLocalization.AtPrime Rₚ p`. -/
@[stacks 00NB "Cohen-Macaulayness of a Noetherian local ring is the predicate
`Module.IsMaximalCohenMacaulay S S`, i.e. `depth_{𝔪_S}(S) = dim S` (Definition 00N8); the
localization is an abstract `IsLocalization.AtPrime`. See the module docstring.",
  ega "0 16.5.10" "(i) for M = A",
  ega "0 16.5.13" "partial",
  ega "IV 6.11.5" "special case"]
public theorem Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hR : Module.IsMaximalCohenMacaulay R R) (p : Ideal R)
    [p.IsPrime] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    [IsLocalRing Rₚ] : Module.IsMaximalCohenMacaulay Rₚ Rₚ :=
    by exact Stacks.CohenMacaulay.LocalizationAtPrime.solution (R := R) hR p Rₚ

end
