module

public import StacksFrontier.RingTheory.KrullAkizuki
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

/-!
# Finite length of `M / xM` for a submodule of a vector space over the fraction field

Proof of Stacks 00PF: if `R` is a Noetherian domain of Krull dimension at most one with
fraction field `K`, `V` is a finite-dimensional `K`-vector space and `M ⊆ V` is an
`R`-submodule, then `M / xM` has finite length over `R` for every nonzero `x ∈ R`.

## Main results

* `Stacks.Length.QuotientByElement.solution`: the statement of Stacks 00PF.

## Implementation notes

The source localizes: `x` lies in finitely many primes, all maximal, so `R/xR` is Artinian
and splits as the product of its localizations there (Stacks 00KJ, 00JB), `M/xM` splits
accordingly, each factor has finite length by the local case (Stacks 00PE), and a finite
filtration with residue-field quotients descends the conclusion to `R`.

The proof below replaces that route by the uniform bound
`length_R(M/xM) ≤ dim_K V · length_R(R/xR)`, which is proved over `R` itself and therefore
needs neither the localization decomposition nor the filtration. Finiteness of the
right-hand side is Mathlib's `isFiniteLength_quotient_span_singleton`, which is Stacks
00KH/00KJ: `R/xR` is Noetherian of dimension `0`, hence Artinian.

The bound is proved by descending induction on a `K`-subspace `W ≤ V`, bounding
`length_R((M ∩ W)/x(M ∩ W))` by `dim_K W · length_R(R/xR)`. Cutting `W` down by the kernel
of a `K`-linear functional `f` nonvanishing somewhere on `W` gives the exact sequence
`(M ∩ W ∩ ker f) → (M ∩ W) → f(M ∩ W)`, right exactness of `· ⊗ R/xR`
(`QuotSMulTop.map_exact`) turns it into the subadditivity
`length_R(N/xN) ≤ length_R((N ∩ ker f)/x(…)) + length_R(f(N)/x f(N))`, and the outer term is
an `R`-submodule of `K`, for which the bound is `length_R(R/xR)` itself: a finitely
generated one is isomorphic to a nonzero ideal `I ⊆ R` after clearing denominators, `R/I`
has finite length, and `length_R(I/xI) = length_R(R/xR)` by the cancellation lemma
`length_quot_xtop_eq_of_quot_finite`. A general submodule of `K` is the directed union of
its finitely generated ones and every finitely generated submodule of `N/xN` is dominated by
one of the stages, which is `length_le_of_forall_fg_submodule_le`. This last point is where
the hypothesis that `M` is *not* finitely generated is paid for.

## References

* [StacksProject 00PF](https://stacks.math.columbia.edu/tag/00PF)
-/

namespace Stacks.Length.QuotientByElement

open Pointwise

variable {R : Type*} [CommRing R]

/-- `x • ⊤` is the principal ideal `(x)` when the module is the ring itself. -/
private lemma smul_top_eq_span_singleton (x : R) : (x • ⊤ : Submodule R R) = Ideal.span {x} := by
  ext y
  rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨r, -, rfl⟩
    simp [smul_eq_mul]
  · rintro ⟨r, rfl⟩
    exact ⟨r, trivial, by rw [smul_eq_mul]⟩

/-- The zero submodule has `x`-torsion quotient zero. -/
private lemma length_quotSMulTop_bot {X : Type*} [AddCommGroup X] [Module R X] (x : R) :
    Module.length R (QuotSMulTop x ↥(⊥ : Submodule R X)) = 0 := by
  refine le_antisymm ?_ zero_le
  refine le_trans (Module.length_le_of_surjective _ (Submodule.mkQ_surjective _)) ?_
  rw [Module.length_bot]

/-- Subadditivity of `N ↦ N/xN` along a linear map: right exactness of `· ⊗ R/(x)` applied to
`0 → N ∩ ker g → N → g(N) → 0`. -/
private lemma length_quotSMulTop_le_add {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (x : R) (g : X →ₗ[R] Y) (N : Submodule R X) :
    Module.length R (QuotSMulTop x ↥N)
      ≤ Module.length R (QuotSMulTop x ↥(N ⊓ LinearMap.ker g))
        + Module.length R (QuotSMulTop x ↥(Submodule.map g N)) := by
  set ι : ↥(N ⊓ LinearMap.ker g) →ₗ[R] ↥N := Submodule.inclusion inf_le_left with hι
  set π : ↥N →ₗ[R] ↥(Submodule.map g N) := g.submoduleMap N with hπd
  have hπ : Function.Surjective π := g.submoduleMap_surjective N
  have hex : Function.Exact ι π := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro n hn
      have hn' : (n : X) ∈ LinearMap.ker g := by
        have := Subtype.ext_iff.mp (LinearMap.mem_ker.mp hn)
        rw [hπd] at this
        simpa using this
      exact ⟨⟨(n : X), Submodule.mem_inf.mpr ⟨n.2, hn'⟩⟩, rfl⟩
    · rintro n ⟨m, rfl⟩
      have hm : g (m : X) = 0 := (Submodule.mem_inf.mp m.2).2
      rw [LinearMap.mem_ker, hπd, Subtype.ext_iff, LinearMap.submoduleMap_coe_apply]
      exact hm
  have h2 : Function.Surjective (QuotSMulTop.map x π) := QuotSMulTop.map_surjective x hπ
  have hker : LinearMap.ker (QuotSMulTop.map x π) = LinearMap.range (QuotSMulTop.map x ι) :=
    LinearMap.exact_iff.mp (QuotSMulTop.map_exact x hex hπ)
  have heq : Module.length R (QuotSMulTop x ↥N)
      = Module.length R ↥(LinearMap.ker (QuotSMulTop.map x π))
        + Module.length R (QuotSMulTop x ↥(Submodule.map g N)) :=
    Module.length_eq_add_of_exact _ (QuotSMulTop.map x π) (Submodule.injective_subtype _) h2
      (by rw [LinearMap.exact_iff, Submodule.range_subtype])
  rw [heq, hker]
  exact add_le_add (Module.length_le_of_surjective (QuotSMulTop.map x ι).rangeRestrict
    (LinearMap.surjective_rangeRestrict _)) le_rfl

/-- A bound on `N/xN` valid for every finitely generated submodule `N` of `X` is a bound on
`X/xX`: every finitely generated submodule of `X/xX` is dominated by the image of some
`N/xN`. -/
private lemma length_quotSMulTop_le_of_forall_fg {X : Type*} [AddCommGroup X] [Module R X]
    (x : R) {B : ℕ∞} (h : ∀ N : Submodule R X, N.FG → Module.length R (QuotSMulTop x ↥N) ≤ B) :
    Module.length R (QuotSMulTop x X) ≤ B := by
  classical
  refine length_le_of_forall_fg_submodule_le R fun P hP => ?_
  obtain ⟨s, hs⟩ := hP
  obtain ⟨lift, hlift⟩ :=
    Function.Surjective.hasRightInverse (Submodule.mkQ_surjective (x • ⊤ : Submodule R X))
  set N : Submodule R X := Submodule.span R (lift '' (s : Set (QuotSMulTop x X))) with hN
  have hNfg : N.FG := Submodule.fg_span (s.finite_toSet.image lift)
  set φ : QuotSMulTop x ↥N →ₗ[R] QuotSMulTop x X := QuotSMulTop.map x N.subtype with hφ
  have hPle : P ≤ LinearMap.range φ := by
    rw [← hs, Submodule.span_le]
    intro y hy
    refine ⟨Submodule.Quotient.mk ⟨lift y, Submodule.subset_span ⟨y, hy, rfl⟩⟩, ?_⟩
    rw [hφ, QuotSMulTop.map_apply_mk]
    simpa using hlift y
  calc Module.length R ↥P
      ≤ Module.length R ↥(LinearMap.range φ) :=
        Module.length_le_of_injective (Submodule.inclusion hPle)
          (Submodule.inclusion_injective hPle)
    _ ≤ Module.length R (QuotSMulTop x ↥N) :=
        Module.length_le_of_surjective φ.rangeRestrict (LinearMap.surjective_rangeRestrict _)
    _ ≤ B := h N hNfg

section Dimension

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

/-- For an ideal `I` of a Noetherian domain of dimension at most one,
`length_R(I/xI) ≤ length_R(R/xR)`, with equality unless `I = 0`. -/
private lemma length_quotSMulTop_ideal_le (I : Ideal R) {x : R} (hx : x ≠ 0) :
    Module.length R (QuotSMulTop x ↥I) ≤ Module.length R (R ⧸ Ideal.span {x}) := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · rw [length_quotSMulTop_bot]
    exact zero_le
  · obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hle : Ideal.span {a} ≤ I := by
      rw [Ideal.span_le]
      simpa using haI
    have hfina : Module.length R (R ⧸ Ideal.span {a}) ≠ ⊤ :=
      Module.length_ne_top_iff.mpr
        (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero ha))
    have hfin : Module.length R (R ⧸ I) ≠ ⊤ := by
      refine ne_top_of_le_ne_top hfina (Module.length_le_of_surjective
        (Submodule.mapQ (Ideal.span {a}) I LinearMap.id (by simpa using hle)) ?_)
      intro y
      obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective I y
      exact ⟨Submodule.Quotient.mk r, rfl⟩
    have hinj : Function.Injective fun m : R => x • m := smul_right_injective R hx
    rw [← length_quot_xtop_eq_of_quot_finite R x hinj I hfin, smul_top_eq_span_singleton]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- Clearing denominators identifies a finitely generated `R`-submodule of the fraction field
with an ideal of `R`, so the ideal bound applies to it. -/
private lemma length_quotSMulTop_fg_fractionRing_le (N : Submodule R K) (hN : N.FG) {x : R}
    (hx : x ≠ 0) :
    Module.length R (QuotSMulTop x ↥N) ≤ Module.length R (R ⧸ Ideal.span {x}) := by
  classical
  obtain ⟨s, hs⟩ := hN
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors R) s (fun y : K => y)
  set c : R := (b : R) with hc
  have hc0 : c ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hinjK : Function.Injective (Algebra.linearMap R K) :=
    FaithfulSMul.algebraMap_injective R K
  have hcK : algebraMap R K c ≠ 0 := fun h => hc0 (hinjK (by simpa using h))
  set ψ : K →ₗ[R] K := LinearMap.lsmul R K c with hψd
  have hψ : Function.Injective ψ := by
    intro y z hyz
    have : algebraMap R K c * y = algebraMap R K c * z := by
      simpa [hψd, Algebra.smul_def] using hyz
    exact mul_left_cancel₀ hcK this
  have hrange : Submodule.map ψ N ≤ LinearMap.range (Algebra.linearMap R K) := by
    rw [← hs, Submodule.map_span, Submodule.span_le]
    rintro y ⟨i, hi, rfl⟩
    obtain ⟨r, hr⟩ := hb i hi
    exact ⟨r, by simpa [hψd] using hr⟩
  set I : Submodule R R := Submodule.comap (Algebra.linearMap R K) (Submodule.map ψ N) with hI
  have hmapI : Submodule.map (Algebra.linearMap R K) I = Submodule.map ψ N :=
    Submodule.map_comap_eq_self hrange
  have e1 : ↥N ≃ₗ[R] ↥(Submodule.map ψ N) := Submodule.equivMapOfInjective ψ hψ N
  have e2 : ↥I ≃ₗ[R] ↥(Submodule.map ψ N) :=
    (Submodule.equivMapOfInjective (Algebra.linearMap R K) hinjK I).trans
      (LinearEquiv.ofEq _ _ hmapI)
  rw [((QuotSMulTop.congr x e1).trans (QuotSMulTop.congr x e2).symm).length_eq]
  exact length_quotSMulTop_ideal_le I hx

/-- Every `R`-submodule of the fraction field satisfies `length_R(N/xN) ≤ length_R(R/xR)`. -/
private lemma length_quotSMulTop_fractionRing_le (N : Submodule R K) {x : R} (hx : x ≠ 0) :
    Module.length R (QuotSMulTop x ↥N) ≤ Module.length R (R ⧸ Ideal.span {x}) := by
  refine length_quotSMulTop_le_of_forall_fg x fun N₀ hN₀ => ?_
  rw [(QuotSMulTop.congr x
    (Submodule.equivMapOfInjective N.subtype (Submodule.injective_subtype N) N₀)).length_eq]
  exact length_quotSMulTop_fg_fractionRing_le K _ (hN₀.map _) hx

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V]
  [IsScalarTower R K V]

/-- The uniform bound, by induction on the `K`-dimension of a subspace `W ≤ V` cutting `M`
down: `length_R((M ∩ W)/x(M ∩ W)) ≤ dim_K W · length_R(R/xR)`. -/
private lemma length_quotSMulTop_inf_le (M : Submodule R V) {x : R} (hx : x ≠ 0) (n : ℕ) :
    ∀ W : Submodule K V, Module.finrank K ↥W ≤ n →
      Module.length R (QuotSMulTop x ↥(M ⊓ Submodule.restrictScalars R W))
        ≤ (n : ℕ∞) * Module.length R (R ⧸ Ideal.span {x}) := by
  induction n with
  | zero =>
    intro W hW
    have hWbot : W = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hW)
    subst hWbot
    rw [Submodule.restrictScalars_bot, inf_bot_eq, length_quotSMulTop_bot]
    exact zero_le
  | succ n ih =>
    intro W hW
    rcases eq_or_ne W ⊥ with rfl | hWne
    · rw [Submodule.restrictScalars_bot, inf_bot_eq, length_quotSMulTop_bot]
      exact zero_le
    obtain ⟨w, hwW, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    -- a `K`-linear functional not vanishing at `w`
    set bV := Module.Free.chooseBasis K V with hbV
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp
      (show bV.repr w ≠ 0 from fun h => hw (bV.repr.map_eq_zero_iff.mp h))
    set f : V →ₗ[K] K := bV.coord i with hf
    have hfw : f w ≠ 0 := by simpa [hf, Module.Basis.coord_apply] using hi
    set W' : Submodule K V := W ⊓ LinearMap.ker f with hW'
    have hlt : W' < W := by
      refine lt_of_le_of_ne inf_le_left fun hcon => hfw ?_
      have : w ∈ W' := hcon ▸ hwW
      exact (Submodule.mem_inf.mp this).2
    have hW'rank : Module.finrank K ↥W' ≤ n := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    set g : V →ₗ[R] K := LinearMap.restrictScalars R f with hg
    have hinf : (M ⊓ Submodule.restrictScalars R W) ⊓ LinearMap.ker g
        = M ⊓ Submodule.restrictScalars R W' := by
      rw [hg, LinearMap.ker_restrictScalars, hW', Submodule.restrictScalars_inf, inf_assoc]
    refine le_trans (length_quotSMulTop_le_add x g (M ⊓ Submodule.restrictScalars R W)) ?_
    rw [hinf]
    have hsucc : ((n + 1 : ℕ) : ℕ∞) * Module.length R (R ⧸ Ideal.span {x})
        = (n : ℕ∞) * Module.length R (R ⧸ Ideal.span {x})
          + Module.length R (R ⧸ Ideal.span {x}) := by
      push_cast
      rw [add_mul, one_mul]
    rw [hsucc]
    exact add_le_add (ih W' hW'rank) (length_quotSMulTop_fractionRing_le K
      (Submodule.map g (M ⊓ Submodule.restrictScalars R W)) hx)

end Dimension

/-- **Stacks 00PF.** If `R` is a Noetherian domain of Krull dimension at most one with fraction
field `K`, `V` is a finite-dimensional `K`-vector space and `M ⊆ V` is an `R`-submodule, then
`M / xM` has finite length over `R` for every nonzero `x ∈ R`. The proof bounds the length by
`finrank K V * Module.length R (R ⧸ Ideal.span {x})`. -/
public theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module R V] [IsScalarTower R K V]
    (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    IsFiniteLength R (QuotSMulTop x M) := by
  rw [← Module.length_ne_top_iff]
  have h := length_quotSMulTop_inf_le K M hx (Module.finrank K V) ⊤ (by simp)
  rw [Submodule.restrictScalars_top, inf_top_eq] at h
  refine ne_top_of_le_ne_top ?_ h
  exact WithTop.mul_ne_top (ENat.natCast_ne_top _)
    (Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero hx)))

end Stacks.Length.QuotientByElement

/-!
# Finite length of `M / xM` for a submodule of a vector space over the fraction field

Let `R` be a Noetherian domain of Krull dimension at most one with fraction field `K`, let `V` be
a finite-dimensional `K`-vector space and let `M ⊆ V` be an `R`-submodule. Then for every nonzero
`x ∈ R` the `R`-module `M / xM` has finite length.

The mechanism is that `x` lies in only finitely many primes of `R`, all maximal, so that `R/xR`
is Artinian and decomposes as the product of its localizations at those primes; `M/xM`
decomposes accordingly, each factor `M_m / x M_m` has finite length over `R_m` by the local
case, and the resulting finite filtration of `M/xM` has residue fields as its successive
quotients.

The point of the statement is that `M` is *not* assumed to be a finitely generated `R`-module:
the finiteness comes from the finite dimension of the ambient space `V` over `K` alone. This is
what makes the statement applicable to rings `A` with `R ⊆ A ⊆ L` for a finite extension `L/K`,
which need not be finite over `R`, and it is the analytic core of Krull–Akizuki.

## Main results

* `isFiniteLength_quotSMulTop_of_finiteDimensional`: `M / xM` has finite length over `R` for
  every `R`-submodule `M` of a finite-dimensional `K`-vector space and every nonzero `x ∈ R`.

## Implementation notes

The source's ambient module `K^{⊕ r}` is replaced by an arbitrary finite-dimensional
`K`-vector space `V`. This costs nothing — a choice of `K`-basis is an `R`-linear isomorphism
`V ≃ K^{⊕ r}` with `r = finrank K V`, carrying `M` to a submodule and `M/xM` to an isomorphic
quotient — and it is the form the dependents need: they apply the lemma to a ring `A` with
`R ⊆ A ⊆ L`, sitting inside `V = L` for a finite field extension `L/K`, where identifying `L`
with `K^{⊕ [L : K]}` is exactly the step one wants to avoid repeating.

The fraction field is an abstract `K` with `[IsFractionRing R K]` rather than the construction
`FractionRing R`; `K` has to be given explicitly since it does not occur in the conclusion.
The quotient `M/xM` is Mathlib's `QuotSMulTop x ↥M`, that is `↥M ⧸ x • (⊤ : Submodule R ↥M)`;
the submodule `x • ⊤` of `↥M` is the comap along `M.subtype` of the pointwise multiple `x • M`,
so this agrees with the model `↥M ⧸ Submodule.comap M.subtype (x • M)` in which the local case
00PE is phrased.

The source's `dim(R) = 1` is weakened to `Ring.KrullDimLE 1 R`, Mathlib's spelling of
`dim R ≤ 1`: no conclusion uses dimension exactly one, and the extra case this admits, `R` a
field, is not vacuous but trivial — every nonzero `x` is then a unit, so `xM = M` and
`M/xM = 0`. Dimension two is genuinely excluded: for `R = k[u, v]`, `K = k(u, v)`, `V = K`,
`M = R` and `x = u`, the module `M/xM = k[v]` has infinite length over `R`.

Only finiteness is asserted, as in the source. The proof in fact bounds
`Module.length R (QuotSMulTop x ↥M)` by `finrank K V * Module.length R (R ⧸ Ideal.span {x})`,
which is the content of the local Lemma 00PE; no dependent of this lemma uses the bound, and
the global statement is cited for the finiteness alone.

An intrinsic equivalent avoiding `K` and `V` is: `M` a torsion-free `R`-module with
`Module.rank R M < ℵ₀`. Such an `M` embeds in `M ⊗[R] K`, a `K`-vector space of dimension
`rank R M`, and conversely a submodule of a finite-dimensional `K`-space is torsion-free of
finite rank. The submodule form is kept because it is the source's and because it is how the
dependents present their modules.

Faithfulness. (1) No hypothesis is dead: `IsNoetherianRing R` and `Ring.KrullDimLE 1 R` are
what make `R/xR` of finite length (both are needed: a rank-one valuation ring with value group
`ℝ` is a one-dimensional non-Noetherian domain for which `R/xR` has infinite length, and the
two-dimensional example above shows the dimension hypothesis is used), `FiniteDimensional K V`
bounds the length (for `V` of infinite dimension, `M = R^{⊕ ℕ}` has `M/xM` of infinite length),
`IsFractionRing R K` fixes `K` as the fraction field of `R`, `IsDomain R` is the source's
hypothesis and turns `x ≠ 0` into `x` being a nonzerodivisor, and `x ≠ 0` is used since
`M/0M = M` has infinite length as soon as `M` is not of finite length. (2) The scalars and the
base are the source's: the length is over `R` itself, not over `K` or over a localization
`R_m`, and `M` is an `R`-submodule of `V`, the `R`-action on `V` being the restriction of the
`K`-action along `R → K` (`IsScalarTower R K V`). (3) The maps the source names are pinned:
the embedding `R → K` is `algebraMap R K`, pinned as the localization map by `IsFractionRing`,
and `M → V` is `M.subtype`; the quotient `M/xM` is the concrete `QuotSMulTop x ↥M` rather than
an unspecified module with a surjection from `M`. (4) The instantiation is not degenerate:
`R = ℤ`, `K = ℚ`, `V = ℚ ⊕ ℚ`, `M = ℤ ⊕ ℤ` and `x = 6` give `M/xM ≅ (ℤ/6)^2` of length `4`,
while `M = ℤ[1/2] ⊕ ℤ` with the same `x` gives a non-finitely-generated `M` with
`M/xM ≅ ℤ/3 ⊕ ℤ/6` of length `3`.

## References

* [StacksProject 00PF](https://stacks.math.columbia.edu/tag/00PF)

## Tags

Krull-Akizuki, finite length, dimension one, Noetherian domain, fraction field
-/

/-- Let `R` be a Noetherian domain of Krull dimension at most one with fraction field `K`, let
`V` be a finite-dimensional `K`-vector space and let `M` be an `R`-submodule of `V`. Then for
every nonzero `x ∈ R` the `R`-module `M / xM` has finite length. Note that `M` is not assumed to
be a finitely generated `R`-module. -/
@[stacks 00PF "For an arbitrary finite-dimensional vector space `V` over the fraction field in
place of `K^{⊕ r}`, and with `dim R = 1` weakened to `Ring.KrullDimLE 1 R`. See the module
docstring."]
public theorem isFiniteLength_quotSMulTop_of_finiteDimensional
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module R V] [IsScalarTower R K V]
    (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    IsFiniteLength R (QuotSMulTop x M) :=
  Stacks.Length.QuotientByElement.solution (V := V) K M hx
