module

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Sheaves.Presheaf

public import StacksFrontier.RingTheory.HilbertSamuel.DimensionTheorem
public import StacksFrontier.RingTheory.Length.Additivity
public import StacksFrontier.RingTheory.KrullDimension.Module
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# The Hilbert–Samuel degree of a finite module is the dimension of its support

Proof of `Module.hilbertSamuelDegree_eq_supportDim` (Stacks 00L8): for a finite module `M` over a
Noetherian local ring `(R, m)` the Hilbert–Samuel degree `d(M)` of Definition 00KA equals
`dim Supp(M)`.

Both invariants are additive to leading order along a short exact sequence — `d(-)` by
Lemma 00KC and `dim Supp(-)` by Lemma 0B51, each turning a short exact sequence into a maximum —
and both vanish on the zero module. A finite module over a Noetherian ring is built from the
modules `R ⧸ 𝔭`, `𝔭` prime, by finitely many short exact sequences (Lemma 00L0), so the two
invariants agree as soon as they agree on `R ⧸ 𝔭`. There the statement is that `d(R ⧸ 𝔭)` equals
`dim(R ⧸ 𝔭)`, which is the equivalence of items (1) and (2) of Proposition 00KQ applied to the
Noetherian local ring `R ⧸ 𝔭`.

## Main results

* `Stacks.HilbertSamuel.SupportDimension.solution`: the statement of Stacks 00L8.

## Implementation notes

The proof in the Stacks project runs the induction by hand over the filtration of Lemma 00L0 and
closes the
support side by identifying the minimal primes of `Supp(M)` among the `𝔭ᵢ` (Lemma 00L7). Here the
filtration and the induction over it are Mathlib's
`IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`, which is exactly Lemma 00L0 packaged
as an induction principle, and the support side is Lemma 0B51 applied at each step, so that the
two invariants are compared one short exact sequence at a time. Lemma 00L7 is then not needed:
the bookkeeping `Supp(M) = ⋃ V(𝔭ᵢ)` that it rests on is what 0B51 performs step by step.

Two changes of presentation are forced by the shape of the imported statements. Definition 00KA
presents `d(M)` as the degree of *some* rational polynomial computing the Hilbert–Samuel function,
chosen by `Classical.choose`; `hilbertSamuelDegree_eq_degree` below turns that into the usable
form "the degree of *any* computing polynomial". No appeal to the independence of Proposition 00K9
is needed for that: two polynomials computing the same Hilbert–Samuel function agree at every large
`n`, hence agree at infinitely many rationals, hence are equal — this is
`eventually_eval_eq_of_computing` followed by `eq_of_eventually_eval_natCast_eq`, which is
`Polynomial.eq_of_infinite_eval_eq`. Proposition 00K8 enters separately, as `exists_computingPoly`,
which produces a computing polynomial for a module from the binomial-basis form of 00K8; it is what
makes `hilbertSamuelDegree_eq_degree` applicable to a module given only abstractly, as in
`hilbertSamuelDegree_congr`. Proposition 00KQ presents the
Hilbert–Samuel function of a Noetherian local ring in the binomial basis, as an eventual
`ℤ`-combination `∑_{i ≤ d} (n choose i) a i` with `a d ≠ 0`, rather than by a computing
polynomial; `NumericalPoly.binomSum` converts such a combination into the rational polynomial
computing it, whose degree is `d` because the `i`-th binomial polynomial has degree `i`.

Finally, `d(R ⧸ 𝔭)` is a Hilbert–Samuel degree over `R`, filtered by `m`, whereas Proposition
00KQ computes with `R ⧸ 𝔭` filtered by its own maximal ideal. The two agree because
`m ^ k • (R ⧸ 𝔭) = (m (R ⧸ 𝔭)) ^ k` is the `k`-th power of the maximal ideal of `R ⧸ 𝔭` and
because length over `R` and over `R ⧸ 𝔭` of an `R ⧸ 𝔭`-module agree, the ring map being
surjective; this is `DimensionTheorem.length_quotient_smul_top`, stated for an arbitrary ideal in
place of `m ^ k` since neither the primality of `𝔭` nor Noetherianness is used.

## References

* [StackProject 00L8](https://stacks.math.columbia.edu/tag/00L8)
-/

@[expose] public section

namespace Stacks.HilbertSamuel.SupportDimension

open Filter Finset IsLocalRing Polynomial
open _root_.Stacks.HilbertFunction.NumericalPoly

/-! ### The Hilbert–Samuel degree as the degree of any computing polynomial -/

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] in
/-- Two polynomials computing the Hilbert–Samuel function of `M` agree at all large `n`, both
values being the length of the same quotient. -/
private lemma eventually_eval_eq_of_computing {M : Type*} [AddCommGroup M] [Module R M]
    {P Q : ℚ[X]}
    (hP : ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
      Module.length R (M ⧸ (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R M))) = p ∧
        P.eval (n : ℚ) = (p : ℚ))
    (hQ : ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
      Module.length R (M ⧸ (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R M))) = p ∧
        Q.eval (n : ℚ) = (p : ℚ)) :
    ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = Q.eval (n : ℚ) := by
  filter_upwards [hP, hQ] with n hn hm
  obtain ⟨p, hp₁, hp₂⟩ := hn
  obtain ⟨q, hq₁, hq₂⟩ := hm
  have : p = q := by exact_mod_cast hp₁.symm.trans hq₁
  rw [hp₂, hq₂, this]

omit [IsNoetherianRing R] in
/-- Definition 00KA reads off `d(M)` from a polynomial chosen by `Classical.choose`; since two
polynomials computing the Hilbert–Samuel function of `M` agree at all large `n` and hence are
equal, it is the degree of *any* polynomial computing that function. -/
private lemma hilbertSamuelDegree_eq_degree (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (P : ℚ[X])
    (hP : ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
      Module.length R (M ⧸ (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R M))) = p ∧
        P.eval (n : ℚ) = (p : ℚ)) :
    Module.hilbertSamuelDegree R M = P.degree := by
  have hex : ∃ Q : ℚ[X], ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
      Module.length R (M ⧸ (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R M))) = p ∧
        Q.eval (n : ℚ) = (p : ℚ) := ⟨P, hP⟩
  rw [Module.hilbertSamuelDegree, Ideal.hilbertSamuelDegree,
    dite_eq_left_of_eq_true (eq_true hex)]
  exact congrArg Polynomial.degree
    (eq_of_eventually_eval_natCast_eq (eventually_eval_eq_of_computing hex.choose_spec hP))

/-- Proposition 00K8: the Hilbert–Samuel function of a finite module over a Noetherian local ring
is computed by a rational polynomial.

This is Stacks 00K8, `Ideal.exists_eventually_length_quotient_smul_pow_eq_sum_choose_mul`, taken
at the ideal of definition `I = m` and converted from the binomial basis to a computing
polynomial by `binomSum`. -/
@[ega "0 16.2.1" "special case"]
private lemma exists_computingPoly (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ P : ℚ[X], ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
      Module.length R (M ⧸ (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R M))) = p ∧
        P.eval (n : ℚ) = (p : ℚ) := by
  obtain ⟨r, _, b, hab⟩ := Ideal.exists_eventually_length_quotient_smul_pow_eq_sum_choose_mul
    (maximalIdeal R) (radical_maximalIdeal R) M
  refine ⟨binomSum r b, hab.mono fun n hn => ?_⟩
  obtain ⟨q, hq1, hq2⟩ := hn.2
  refine ⟨q, hq1, ?_⟩
  rw [binomSum_eval]
  exact_mod_cast hq2.symm

private lemma hilbertSamuelDegree_congr {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] (e : M ≃ₗ[R] N) :
    Module.hilbertSamuelDegree R M = Module.hilbertSamuelDegree R N := by
  have : Module.Finite R N := Module.Finite.equiv e
  obtain ⟨P, hP⟩ := exists_computingPoly (R := R) M
  have hlen : ∀ k : ℕ, Module.length R (N ⧸ (maximalIdeal R ^ k • (⊤ : Submodule R N)))
      = Module.length R (M ⧸ (maximalIdeal R ^ k • (⊤ : Submodule R M))) := fun k =>
    (LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ e
      (by simp [Submodule.map_smul'']))).symm
  refine (hilbertSamuelDegree_eq_degree M P hP).trans
    (hilbertSamuelDegree_eq_degree N P ?_).symm
  filter_upwards [hP] with n hn
  obtain ⟨q, hq1, hq2⟩ := hn
  exact ⟨q, (hlen (n + 1)).trans hq1, hq2⟩

/-! ### The case of `R ⧸ 𝔭` -/

/-- The Hilbert–Samuel degree of `R ⧸ 𝔭` is the Krull dimension of `R ⧸ 𝔭`: this is the
equivalence of items (1) and (2) of Proposition 00KQ for the Noetherian local ring `R ⧸ 𝔭`. -/
private lemma hilbertSamuelDegree_quotient_prime (p : Ideal R) [hp : p.IsPrime] :
    (Module.hilbertSamuelDegree R (R ⧸ p)).map (Nat.cast : ℕ → ℕ∞) = ringKrullDim (R ⧸ p) := by
  have : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  have : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk p) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hmax : (maximalIdeal R).map (Ideal.Quotient.mk p) = maximalIdeal (R ⧸ p) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sup_eq_left.mpr (le_maximalIdeal hp.ne_top)]
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp
    (Ideal.height_ne_top (I := maximalIdeal (R ⧸ p)) (maximalIdeal.isMaximal (R ⧸ p)).ne_top)
  have hdim : ringKrullDim (R ⧸ p) = (d : WithBot ℕ∞) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hd]
    norm_cast
  obtain ⟨a, ha0, ha⟩ :=
    ((IsLocalRing.ringKrullDim_eq_tfae (R := R ⧸ p) d).out 1 2).mp hdim
  have hP : ∀ᶠ n : ℕ in atTop, ∃ q : ℕ,
      Module.length R ((R ⧸ p) ⧸ (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R (R ⧸ p)))) = q ∧
        (binomSum d a).eval (n : ℚ) = (q : ℚ) := by
    filter_upwards [ha] with n hn
    obtain ⟨q, hq1, hq2⟩ := hn
    refine ⟨q, ?_, ?_⟩
    · rw [DimensionTheorem.length_quotient_smul_top, Ideal.map_pow, hmax]
      exact hq1
    · rw [binomSum_eval, ← hq2]
      push_cast
      ring
  rw [hilbertSamuelDegree_eq_degree (R ⧸ p) (binomSum d a) hP, binomSum_degree d a ha0, hdim,
    WithBot.map_natCast]
  norm_cast

/-! ### The induction -/

private lemma withBot_map_natCast_max (a b : WithBot ℕ) :
    WithBot.map (Nat.cast : ℕ → ℕ∞) (max a b)
      = max (WithBot.map (Nat.cast : ℕ → ℕ∞) a) (WithBot.map (Nat.cast : ℕ → ℕ∞) b) := by
  induction a using WithBot.recBotCoe with
  | bot => simp
  | coe x =>
    induction b using WithBot.recBotCoe with
    | bot => simp
    | coe y =>
      simp only [WithBot.map_coe, ← WithBot.coe_max]
      norm_cast

/-- For a finite module `M` over a Noetherian local ring `R`, the Hilbert–Samuel degree of `M`,
viewed in `WithBot ℕ∞`, is the dimension of the support of `M`. -/
public theorem solution (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (Module.hilbertSamuelDegree R M).map (Nat.cast : ℕ → ℕ∞) = Module.supportDim R M := by
  induction ‹Module.Finite R M› using
    IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime with
  | subsingleton N =>
    rw [Module.supportDim_eq_bot_of_subsingleton,
      hilbertSamuelDegree_eq_degree N 0 (by
        filter_upwards with n
        exact ⟨0, Module.length_eq_zero, by simp⟩),
      degree_zero, WithBot.map_bot]
  | quotient N p e =>
    have : Module.Finite R (R ⧸ p.asIdeal) := Module.Finite.equiv e
    rw [hilbertSamuelDegree_congr e, Module.supportDim_eq_of_equiv e,
      Module.supportDim_quotient_eq_ringKrullDim]
    exact hilbertSamuelDegree_quotient_prime p.asIdeal
  | exact N₁ N₂ N₃ f g hf hg hfg ih₁ ih₃ =>
    have hmax : max (Module.hilbertSamuelDegree R N₁) (Module.hilbertSamuelDegree R N₃)
        = Module.hilbertSamuelDegree R N₂ :=
      (Ideal.max_degree_eq_degree_of_exact (maximalIdeal R) (radical_maximalIdeal R) hfg hf hg).2
    rw [← hmax, Module.supportDim_of_exact hfg hf hg, withBot_map_natCast_max, ih₁, ih₃]

end Stacks.HilbertSamuel.SupportDimension

end

/-!
# The Hilbert–Samuel degree of a finite module is the dimension of its support

Let `(R, m)` be a Noetherian local ring and let `M` be a finite `R`-module. Two invariants of
`M` that are defined in unrelated ways agree. The first is the Hilbert–Samuel degree `d(M)` of
[StacksProject 00KA], an *arithmetic* invariant: the degree of the numerical polynomial computing
`χ_M(n) = length_R (M / m ^ (n + 1) M)`. The second is the dimension of the support, a
*geometric* invariant: the Krull dimension of `Supp(M) ⊆ Spec(R)`, the set of primes `𝔭` with
`M_𝔭 ≠ 0`. The lemma is that

`d(M) = dim Supp(M)`.

Both sides are `-∞` exactly when `M = 0`, and otherwise the common value is the length of the
longest chain of primes in `Supp(M)`, so the rate of growth of `χ_M` measures how big the support
of `M` is.

## Main results

* `Module.hilbertSamuelDegree_eq_supportDim`: `d(M) = dim Supp(M)` for a finite module `M` over a
  Noetherian local ring.

## Implementation notes

The dimension of the support is Mathlib's `Module.supportDim R M = krullDim (Module.support R M)`,
the Krull dimension of the support as a partially ordered set of primes; for the closed subset
`Supp(M)` of `Spec(R)` this is its topological Krull dimension, because the irreducible closed
subsets of `Spec(R)` contained in `Supp(M)` are exactly the `V(𝔭)` for `𝔭 ∈ Supp(M)`, and
`V(𝔭) ⊆ V(𝔮)` iff `𝔮 ≤ 𝔭`, so chains of the former correspond to chains of primes in `Supp(M)`.

The two invariants take their values in different types: `d(M) : WithBot ℕ`, because it is a
`Polynomial.degree`, while `Module.supportDim R M : WithBot ℕ∞`, because a Krull dimension may be
infinite. The equation is therefore stated in `WithBot ℕ∞`, after transporting `d(M)` along the
canonical order embedding `WithBot ℕ → WithBot ℕ∞`, which is `WithBot.map (Nat.cast : ℕ → ℕ∞)`.
That embedding is injective and reflects `⊥`, so no information is lost: the statement says both
that `dim Supp(M)` is finite and that it is the natural number `d(M)`, or that both invariants
are `-∞`. Writing the equation the other way round, in `WithBot ℕ`, would need a truncation of
`dim Supp(M)` and would no longer assert its finiteness.

Faithfulness. (1) Every hypothesis is used by the conclusion. `IsLocalRing R` provides the
maximal ideal that `d(M)` filters by. `IsNoetherianRing R` and `Module.Finite R M` are what make
`χ_M` a numerical polynomial ([StacksProject 00K8]); without either, `d(M)` takes its fallback
value `-∞` while the support is unchanged, so the equation fails. Dropping Noetherianness: for
`R = k[x₁, x₂, …]` localized at `(x₁, x₂, …)` and `M = R` every `χ_M(n)` is infinite, so
`d(M) = -∞`, while `Supp(M) = Spec(R)` has infinite dimension. Dropping finiteness: for
`R = k[[x]]` and `M = k((x))` one has `m M = M`, so `χ_M ≡ 0` and `d(M) = -∞`, while
`Supp(M) = Spec(R)` has dimension `1`. (2) The scalars and base are the source's: the lengths
inside `d(M)` are lengths of `R`-modules, not of modules over `R / m` or over the associated
graded ring, and the support is a set of primes of `R` itself, not of a localization or a
quotient. (3) The source names two invariants rather than a canonical map, and the statement pins
both: `d(M)` is `Module.hilbertSamuelDegree R M` of Definition 00KA, and `dim Supp(M)` is
`Module.supportDim R M`, and the assertion is their equality, not an inequality in one
direction: both `d(M) ≤ dim Supp(M)` and `d(M) ≥ dim Supp(M)` are part of the conclusion.
(4) The instantiation is not degenerate: for `R = k[[x, y]]` and `M = R` one has
`χ_M(n) = binom(n + 2, 2)`, so `d(M) = 2`, and `Supp(M) = Spec(R)` has dimension `2`; the two
sides are a nonzero natural number, and the degenerate case `M = 0`, where both sides are `-∞`,
is a different instance of the same statement.

## References

* [StacksProject 00L8](https://stacks.math.columbia.edu/tag/00L8)

## Tags

Hilbert–Samuel function, degree, dimension, support, Noetherian local ring
-/

namespace Module



/-- **Stacks 00L8**.
Let `R` be a Noetherian local ring and let `M` be a finite `R`-module. Then the Hilbert–Samuel
degree `d(M)` of Definition 00KA equals the dimension of the support of `M`, that is, the Krull
dimension of `Supp(M) ⊆ Spec(R)`.

The equation is stated in `WithBot ℕ∞`, where `dim Supp(M)` lives, with `d(M) : WithBot ℕ`
transported along the order embedding `WithBot.map (Nat.cast : ℕ → ℕ∞)`; it therefore also
asserts that `dim Supp(M)` is finite. Both sides are `⊥ = -∞` exactly when `M = 0`. -/
@[stacks 00L8, ega "0 16.2.3" "special case"]
public theorem hilbertSamuelDegree_eq_supportDim (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (hilbertSamuelDegree R M).map (Nat.cast : ℕ → ℕ∞) = supportDim R M :=
    by apply Stacks.HilbertSamuel.SupportDimension.solution

end Module
