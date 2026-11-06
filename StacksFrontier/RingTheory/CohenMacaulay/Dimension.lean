module

import StacksFrontier.RingTheory.Ideal.AssociatedPrime.MinimalPrimes
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.WittVector.IsPoly

public import StacksFrontier.RingTheory.CohenMacaulay.Module
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Depth.Criteria
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.CohenMacaulay.Support

@[expose] public section

end

/-!
# Cohen-Macaulayness is inherited by and from the quotient by a nonzerodivisor

Proof of `Module.depth_eq_supportDim_iff_quotSMulTop` (Stacks 0C6G). Let `R` be a Noetherian
local ring with maximal ideal `𝔪`, let `M` be a finite `R`-module and let `x ∈ 𝔪` be a
nonzerodivisor on `M`. Cohen-Macaulayness of a module `N` is the equality
`depth_𝔪(N) = dim Supp(N)` in `WithBot ℕ∞`, and both of its sides drop by exactly one on
passing from `M` to `M/xM`: the depth by Stacks 090R(1) and the dimension of the support by the
equality case of Stacks 0B52, whose hypothesis that `x` avoid the minimal primes of the support
is supplied by `IsSMulRegular.notMem_of_mem_minimalPrimes`. Rewriting both invariants of `M` by
these two equalities turns the equivalence into `d + 1 = D + 1 ↔ d = D`, and adding one is
injective on `WithBot ℕ∞`: it fixes `⊥` and `⊤` and shifts the finite values. So no finiteness
or positivity of either invariant is needed, and in particular the source's reading of the two
cited lemmas as truncated subtractions is not.

## Main results

* `Stacks.CohenMacaulay.QuotientByRegular.solution`: `M` is Cohen-Macaulay if and only if
  `M/xM` is.

## Implementation notes

The depth is `Module.depth`, valued in `ℕ∞`, while `Module.supportDim` is valued in
`WithBot ℕ∞`; the coercion between them is moved across `+ 1` by `WithBot.coe_add` and
`WithBot.coe_one` before the cancellation `ENat.WithBot.add_one_cancel` is applied.

## References

* [StacksProject 0C6G](https://stacks.math.columbia.edu/tag/0C6G)
-/

@[expose] public section

namespace Stacks.CohenMacaulay.QuotientByRegular

/-- For `x ∈ 𝔪` a nonzerodivisor on a finite module `M` over a Noetherian local ring `(R, 𝔪)`,
`M` is Cohen-Macaulay if and only if `M/xM` is. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) :
    (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) = Module.supportDim R M ↔
      (Module.depth R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) : WithBot ℕ∞) =
        Module.supportDim R (QuotSMulTop x M) := by
  have hdepth : Module.depth R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) + 1 =
      Module.depth R (IsLocalRing.maximalIdeal R) M :=
    (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
      (IsLocalRing.maximalIdeal R) M).1 x hx hreg
  have hdim : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M :=
    Module.supportDim_quotSMulTop_succ_eq_supportDim hreg hx
  rw [← hdepth, ← hdim, WithBot.coe_add, WithBot.coe_one, ENat.WithBot.add_one_cancel]

end Stacks.CohenMacaulay.QuotientByRegular

end

/-!
# Cohen-Macaulayness is inherited by and from the quotient by a nonzerodivisor

Let `R` be a Noetherian local ring with maximal ideal `𝔪` and let `M` be a finite `R`-module.
`M` is *Cohen-Macaulay* when `depth_𝔪(M) = dim Supp(M)`: its depth along the maximal ideal
equals the dimension of its support inside `Spec(R)`. This is Definition 00N3, which this
library has as the predicate `Module.IsCohenMacaulayAtMaximalIdeal`.

Let `x ∈ 𝔪` be a nonzerodivisor on `M`. Both invariants drop by exactly one on passing to
`M/xM`: the depth by Stacks 090R(1), `depth_𝔪(M/xM) + 1 = depth_𝔪(M)`, and the dimension of
the support by Stacks 0B52, `dim Supp(M/xM) + 1 = dim Supp(M)`, the latter because a
nonzerodivisor lies in no minimal prime of `Supp(M)`. Hence the two equalities hold together:
`M` is Cohen-Macaulay if and only if `M/xM` is.

## Main results

* `Module.depth_eq_supportDim_iff_quotSMulTop`: for `x ∈ 𝔪` a nonzerodivisor on a finite module
  `M` over a Noetherian local ring, `depth_𝔪(M) = dim Supp(M)` if and only if
  `depth_𝔪(M/xM) = dim Supp(M/xM)`; that is, `M` is Cohen-Macaulay if and only if `M/xM` is.

## Implementation notes

Cohen-Macaulayness is written out on both sides of the equivalence as the equation
`(Module.depth R 𝔪 N : WithBot ℕ∞) = Module.supportDim R N` which `Module.depth` (Stacks 00LI)
and `Module.supportDim` make of Definition 00N3. The coercion is there because depth takes
values in `ℕ∞` while the Krull dimension of a support takes values in `WithBot ℕ∞`, the value
`⊥` being the dimension of the empty support; that is also how the inequality
`depth_𝔪(N) ≤ dim Supp(N)` of Stacks 00LK is read.

The equation is not a paraphrase standing in for a missing definition: it is the definiens of
`Module.IsCohenMacaulayAtMaximalIdeal R N` (Definition 00N3), so each side of the equivalence
is that predicate unfolded, and a reader holding either form has the other with no lemma in
between. Writing it out is what makes the equivalence compose directly with the neighbouring
results, since it is verbatim the Cohen-Macaulayness hypothesis of Stacks 0BUS and the equality
appearing in Stacks 00NF with `dim(R)` in place of `dim Supp(M)`.

Cohen-Macaulayness is in particular *not* spelled as the existence of an `M`-regular sequence
in `𝔪` of length `dim Supp(M)`. That condition is equivalent to the equation only through
Stacks 090R(2), which extends a given `M`-regular sequence to one of length `depth_𝔪(M)`, and
090R(2) is a lemma rather than a definition: an equivalence resting on it would oblige every
user to cite it, where the equation obliges none.

`M/xM` is `QuotSMulTop x M`, the quotient of `M` by `x • ⊤`, and "nonzerodivisor on `M`" is
`IsSMulRegular M x`, injectivity of `x • ·` on `M` itself; neither is replaced by a module
admitting some surjection from `M`. The clause "in `𝔪`" that the source attaches to the regular
sequences computing the depth is carried by `Module.depth R 𝔪 M` itself.

The source's standing hypothesis that `M` be nonzero is not needed. On the zero module
`𝔪 • ⊤ = ⊤`, so `depth_𝔪(0) = ⊤` by the second case of Stacks 00LI, while `dim Supp(0) = ⊥`;
the two are distinct in `WithBot ℕ∞`, so neither side of the equivalence holds and the
equivalence is true. This matches the source's conventions `depth(0) = ∞` and `dim(∅) = -∞`,
under which the zero module is not Cohen-Macaulay.

Neither cited lemma is read as a truncated subtraction, although the source's proof writes both
as one: Stacks 090R(1) says `depth_𝔪(M/xM) + 1 = depth_𝔪(M)` and the equality case of Stacks
0B52 says `dim Supp(M/xM) + 1 = dim Supp(M)`. Adding one is injective on `WithBot ℕ∞` — it
fixes `⊥` and `⊤` and shifts the finite values — so the equivalence follows from the two
equalities by cancellation, with no finiteness or positivity needed of either invariant.

Faithfulness. (1) No hypothesis is dead. Were `x` a unit, `M/xM` would be zero and hence not
Cohen-Macaulay while `M` may well be, so `x ∈ 𝔪` is needed; it is also what the support side,
`Module.supportDim_quotSMulTop_succ_eq_supportDim`, asks of `x`. Regularity of `x` is needed
because for `R = k[[u, v]]`, `M = R/(u) ⊕ R/(u, v)` and the zerodivisor `x = v`, the module
`M/xM ≅ k ⊕ k` has depth and support dimension `0` and so is Cohen-Macaulay, while `M` is not,
having `dim Supp(M) = 1` but depth `0` since `𝔪 ∈ Ass(M)`. Noetherianness of `R` and finiteness
of `M` are used by the depth side, Stacks 090R(1), which is stated for a finite module over a
Noetherian ring. Neither hypothesis on `x` is weakened to the other's consequence: Stacks 0B52
needs only that `x` lie in no minimal prime of `Supp(M)`, but Stacks 090R(1) needs `x` a
nonzerodivisor on `M`, so both are assumed.
(2) The scalars and the base are the source's throughout: the depth is taken along the maximal
ideal of `R`, the support inside `Spec(R)`, and `M/xM` is the `R`-module `QuotSMulTop x M`; no
localization or base change intervenes. (3) The instantiation is not degenerate: for `R` a
discrete valuation ring — `k⟦X⟧`, or `ℤ` localized at a prime — with `x` a uniformizer and
`M = R`, the left side reads `1 = 1 = dim Supp(R)` and the right side `0 = 0 = dim Supp(R/xR)`,
both computed from `IsDiscreteValuationRing.ringKrullDim_eq_one`.

## References

* [StacksProject 0C6G](https://stacks.math.columbia.edu/tag/0C6G)

## Tags

Cohen-Macaulay module, depth, regular sequence, support, Noetherian local ring
-/

@[expose] public section

namespace Module

/-- **Stacks 0C6G.** Let `R` be a Noetherian local ring with maximal ideal `𝔪`, let `M` be a
finite `R`-module and let `x ∈ 𝔪` be a nonzerodivisor on `M`. Then `M` is Cohen-Macaulay if and
only if `M/xM` is, Cohen-Macaulayness of a module `N` being the equality
`depth_𝔪(N) = dim Supp(N)` — the definiens of `Module.IsCohenMacaulayAtMaximalIdeal R N`
(Definition 00N3), written out so that each side is what Stacks 0BUS assumes. -/
@[stacks 0C6G "Cohen-Macaulayness is written out as the equation `depth_𝔪(N) = dim Supp(N)` \
  that Definition 00N3 is, rather than as the predicate, so that each side is verbatim the \
  hypothesis of Stacks 0BUS; the two differ by unfolding a definition. It is not spelled as \
  the existence of an `M`-regular sequence of length `dim Supp(M)`, which needs Stacks \
  090R(2) to be the same condition."]
public theorem depth_eq_supportDim_iff_quotSMulTop {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) :
    (depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) = supportDim R M ↔
      (depth R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) : WithBot ℕ∞) =
        supportDim R (QuotSMulTop x M) :=
          by exact Stacks.CohenMacaulay.QuotientByRegular.solution hx hreg

end Module

end

/-!
# Associated primes of a Cohen-Macaulay module are minimal in its support

Proof of `Module.ringKrullDim_quotient_eq_supportDim_and_minimal_support_of_mem_associatedPrimes`
(Stacks 0BUS): for `(R, 𝔪)` a Noetherian local ring and `M` a finite `R`-module with
`depth_𝔪(M) = dim Supp(M)`, every associated prime `𝔭` of `M` satisfies
`dim(R/𝔭) = dim Supp(M)` and is a minimal point of `Supp(M)`.

The argument is a squeeze. On one side `depth_𝔪(M) ≤ dim(R/𝔭)` (Stacks 0BK4). On the other
`dim(R/𝔭) ≤ dim Supp(M)`, because `𝔭 ∈ Supp(M)` (Stacks 0586) and `Supp(M)` is stable under
specialization, so every chain of primes above `𝔭` is a chain inside `Supp(M)`. Cohen-Macaulayness
identifies the two outer terms, so both inequalities are equalities.

Minimality is a consequence of that equality alone, and of nothing else about associated primes,
depth or supports: `dim(R/𝔭)` is the *coheight* of `𝔭` in `Spec(R)`, the coheight is strictly
antitone where it is finite, and the equality says that `𝔭` maximizes it over `Supp(M)`. A point
of a set at which a finite coheight is maximal is a minimal point of that set.

## Main results

* `Stacks.CohenMacaulay.MinimalAssociated.solution`: every associated prime `𝔭` of `M` satisfies
  `dim(R/𝔭) = dim Supp(M)` and is a minimal point of `Supp(M)`.

## Implementation notes

Both dimensions in play are coheights in `Spec(R)`: `dim(R/𝔭) = coheight 𝔭`
(`coheight_eq_ringKrullDim_quotient` of `StacksFrontier.RingTheory.Equidimensional.FlatLocal`, from
`ringKrullDim_quotient` together with the identification
of `V(𝔭)` with `Set.Ici 𝔭`, which holds by definition), and the bound
`coheight 𝔭 ≤ dim Supp(M)` for `𝔭 ∈ Supp(M)` (`coheight_le_supportDim`) is the inclusion
`Set.Ici 𝔭 ⊆ Supp(M)` fed to `Order.krullDim_le_of_strictMono`. Writing the squeeze in coheights
is what reduces minimality to the order-theoretic `minimal_of_forall_coheight_le`, in place of a
hand-made "extend a chain by one step" argument; the finiteness that lemma asks for is
`Order.coheight_lt_top`, available because a Noetherian local ring has `FiniteRingKrullDim`.

Three facts are proved here rather than cited.
`Ass(M) ⊆ Supp(M)` is Stacks 0586. The transcription `dim(R/𝔭) = coheight 𝔭` and the order fact
`minimal_of_forall_coheight_le` — an element of `s` at which `Order.coheight` is finite and maximal
is minimal in `s` — are general statements about `Spec` of a commutative ring and about an
arbitrary preorder that Mathlib does not record.

## References

* [StacksProject 0BUS](https://stacks.math.columbia.edu/tag/0BUS)
* [EGA, Chapter 0, Proposition 16.5.4]

-/

@[expose] public section

namespace Stacks.CohenMacaulay.MinimalAssociated

section Preorder

variable {α : Type*} [Preorder α] {s : Set α} {a : α}

/-- An element of `s` at which the coheight is maximal over `s`, and finite, is a minimal element
of `s`: an element of `s` strictly below it would have strictly larger coheight. -/
private theorem minimal_of_forall_coheight_le (ha : a ∈ s) (hfin : Order.coheight a < ⊤)
    (hmax : ∀ b ∈ s, Order.coheight b ≤ Order.coheight a) : Minimal (· ∈ s) a := by
  refine ⟨ha, fun b hb hba ↦ ?_⟩
  by_contra hab
  exact absurd (hmax b hb) (Order.coheight_strictAnti (lt_of_le_not_ge hba hab) hfin).not_ge

end Preorder

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Stacks 0586**: an associated prime of `M` lies in the support of `M`. No hypothesis on `R`
or on `M` is needed, since an associated prime is the radical of the annihilator of an element. -/
private theorem mem_support_of_mem_associatedPrimes {p : PrimeSpectrum R}
    (hp : p.asIdeal ∈ associatedPrimes R M) : p ∈ Module.support R M := by
  obtain ⟨-, x, hx⟩ := hp
  refine Module.mem_support_iff_exists_annihilator.mpr ⟨x, ?_⟩
  rw [hx, ← Submodule.bot_colon']
  exact Ideal.le_radical

/-- A point of `Supp(M)` has coheight at most `dim Supp(M)`: the primes above it all lie in the
support, since the support is stable under specialization. -/
private theorem coheight_le_supportDim {p : PrimeSpectrum R} (hp : p ∈ Module.support R M) :
    (Order.coheight p : WithBot ℕ∞) ≤ Module.supportDim R M := by
  rw [Module.supportDim, Order.coheight_eq_krullDim_Ici]
  exact Order.krullDim_le_of_strictMono
    (fun q ↦ (⟨q.1, Module.mem_support_mono q.2 hp⟩ : Module.support R M)) fun _ _ h ↦ h

end CommRing

/-- If `M` is a Cohen-Macaulay finite module over a Noetherian local ring `R` and `𝔭 ∈ Ass(M)`,
then `dim(R/𝔭) = dim Supp(M)` and `𝔭` is a minimal prime of `Supp(M)`. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hCM : (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) = Module.supportDim R M)
    {p : PrimeSpectrum R} (hp : p.asIdeal ∈ associatedPrimes R M) :
    ringKrullDim (R ⧸ p.asIdeal) = Module.supportDim R M ∧
      Minimal (· ∈ Module.support R M) p := by
  have hpS : p ∈ Module.support R M := mem_support_of_mem_associatedPrimes hp
  have hcoh : (Order.coheight p : WithBot ℕ∞) = Module.supportDim R M :=
    le_antisymm (coheight_le_supportDim hpS) <| by
      rw [← hCM, coheight_eq_ringKrullDim_quotient]
      exact Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes hp
  refine ⟨(coheight_eq_ringKrullDim_quotient p).symm.trans hcoh,
    minimal_of_forall_coheight_le hpS (Order.coheight_lt_top p) fun q hq ↦ ?_⟩
  exact WithBot.coe_le_coe.mp ((coheight_le_supportDim hq).trans_eq hcoh.symm)

end Stacks.CohenMacaulay.MinimalAssociated

end

/-!
# Associated primes of a Cohen-Macaulay module are minimal in its support

Let `(R, 𝔪)` be a Noetherian local ring and let `M` be a finite `R`-module which is
Cohen-Macaulay, that is, whose depth along `𝔪` equals the dimension of its support,
`depth(M) = dim Supp(M)`. Then every associated prime `𝔭` of `M` is as large as the support
allows in both available senses: `dim(R/𝔭) = dim Supp(M)`, and `𝔭` is a minimal point of
`Supp(M)`.

The reason is a squeeze between two inequalities that hold for every finite module over a
Noetherian local ring. On one side `depth(M) ≤ dim(R/𝔭)` for `𝔭 ∈ Ass(M)` (Stacks 0BK4); on the
other `dim(R/𝔭) ≤ dim Supp(M)`, because `𝔭 ∈ Supp(M)` (Stacks 0586) and `Supp(M)` is stable
under specialization, so a chain of primes above `𝔭` is a chain inside `Supp(M)`.
Cohen-Macaulayness identifies the two outer terms, forcing equality throughout. Minimality
follows: a prime `𝔮 ∈ Supp(M)` strictly below `𝔭` would prolong every chain above `𝔭` by one
step, giving `dim Supp(M) ≥ dim(R/𝔮) > dim(R/𝔭) = dim Supp(M)`.

## Main results

* `Module.ringKrullDim_quotient_eq_supportDim_and_minimal_support_of_mem_associatedPrimes`:
  for `M` a finite Cohen-Macaulay module over a Noetherian local ring and `𝔭 ∈ Ass(M)`, both
  `dim(R/𝔭) = dim Supp(M)` and `Minimal (· ∈ Supp(M)) 𝔭`.

## Implementation notes

Cohen-Macaulayness is spelled out inline as the equation `depth_𝔪(M) = dim Supp(M)` rather than
carried by a predicate: the definition of a Cohen-Macaulay module (Stacks 00N8) has no Lean form
in this library yet, and this is the equation that definition would unfold to. The depth is
`Module.depth R (IsLocalRing.maximalIdeal R) M` (Stacks 00LI), with values in `ℕ∞`, coerced into
`WithBot ℕ∞` where `Module.supportDim` lives, exactly as in the sibling
`Module.depth_le_supportDim` (Stacks 00LK); that lemma supplies `≤` unconditionally, so the
hypothesis is equivalent to the inequality `dim Supp(M) ≤ depth_𝔪(M)`, and the equation is used
here in the direction the source uses it.

`dim(R/𝔭)` is `ringKrullDim (R ⧸ 𝔭)`, which lands in `WithBot ℕ∞` on the nose, so the first
conclusion is an equation between two Krull dimensions with no coercion between them. The prime is
taken as `𝔭 : PrimeSpectrum R` with `𝔭.asIdeal ∈ associatedPrimes R M`, rather than as an
`Ideal R`, so that the second conclusion can name `Module.support R M : Set (PrimeSpectrum R)`
directly; this is the shape in which Stacks 02CE
(`Module.setOf_minimal_support_eq_setOf_minimal_associatedPrimes`) states its two sets, so the two
statements compose without a transport. Minimality is `Minimal (· ∈ Module.support R M) 𝔭`,
following `minimalPrimes_eq_minimals`.

The source's closing sentence, that `M` has no embedded associated primes, is not a third
conjunct because it is weaker than the second: an embedded associated prime is an associated
prime that is not minimal among the associated primes (Stacks 02M5), and since
`Ass(M) ⊆ Supp(M)` — five lines from `Module.mem_support_iff'`, for any module over any
commutative ring — a prime minimal in `Supp(M)` is a fortiori minimal in `Ass(M)`. So the
statement contains that sentence rather than omitting it.

Faithfulness. (1) Every hypothesis is used by the conclusion. Dropping `hCM` breaks both
conjuncts at once: over `R = k[[x, y]]` and `M = R ⧸ (x², xy)` one has `depth(M) = 0 < 1 =
dim Supp(M)`, `Ass(M) = {(x), (x, y)}`, and for `𝔭 = (x, y)` both `dim(R/𝔭) = 0 ≠ 1` and `𝔭` is
not minimal in `Supp(M) = V(x)`. Dropping `hp` breaks them for any `𝔭 ∈ Supp(M)` above a minimal
one. `IsNoetherianRing R` is what makes `depth(M) ≤ dim(R/𝔭)` true, `IsLocalRing R` is what makes
`depth` refer to `𝔪`, and `Module.Finite R M` is used by both inequalities of the squeeze.
(2) The scalars and base are the source's: `M` is an `R`-module, the depth is taken along the
maximal ideal of `R` itself, `Supp(M) ⊆ Spec(R)`, and `𝔭` is a prime of `R`; nothing is
localized or based-changed in the statement. (3) The source names no map here, and both
quantities are pinned rather than bounded: `dim(R/𝔭)` is asserted equal to `dim Supp(M)`, both
inequalities included, and minimality is the full `Minimal` predicate, not mere membership in the
support. (4) The instantiation is not degenerate: for `R` a discrete valuation ring and `M = R`
one has `depth(R) = 1 = dim Supp(R)`, `Ass(R) = {(0)}`, and the conclusions read
`dim(R/(0)) = 1 = dim Spec(R)` with `(0)` minimal in `Spec(R)` — a nonzero dimension, a prime
different from the maximal ideal, and a nonempty support.

## References

* [StacksProject 0BUS](https://stacks.math.columbia.edu/tag/0BUS)
* [EGA, Chapter 0, Proposition 16.5.4]

## Tags

Cohen-Macaulay module, associated prime, support, minimal prime, depth

-/

namespace Module

/-- **Stacks 0BUS**.
Let `R` be a Noetherian local ring and let `M` be a finite Cohen-Macaulay `R`-module, that is,
one whose depth along the maximal ideal equals the dimension of its support. If `𝔭` is an
associated prime of `M`, then `dim(R/𝔭) = dim Supp(M)` and `𝔭` is a minimal point of `Supp(M)`.

In particular `M` has no embedded associated primes: since `Ass(M) ⊆ Supp(M)`, a prime minimal in
`Supp(M)` is minimal in `Ass(M)`. -/
@[stacks 0BUS "Cohen-Macaulayness is spelled out as `depth_𝔪(M) = dim Supp(M)`, the definition \
  Stacks 00N8 unfolds to, there being no predicate for it in this library yet.",
  ega "0 16.5.4",
  ega "IV 15.4.1" "local form",
  ega "IV 7.2.1.1" "more general"]
public theorem ringKrullDim_quotient_eq_supportDim_and_minimal_support_of_mem_associatedPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M]
    (hCM : (depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) = supportDim R M)
    {p : PrimeSpectrum R} (hp : p.asIdeal ∈ associatedPrimes R M) :
    ringKrullDim (R ⧸ p.asIdeal) = supportDim R M ∧ Minimal (· ∈ support R M) p :=
    by exact Stacks.CohenMacaulay.MinimalAssociated.solution hCM hp

end Module


/-!
# Maximal chains of primes in a local ring carrying a Cohen–Macaulay module of full support

Proof of `Module.IsMaximalCohenMacaulay.length_eq_ringKrullDim_of_support_eq_univ`
(Stacks 0AAE): over a Noetherian local ring `R` admitting a finite Cohen–Macaulay module `M`
with `Supp(M) = Spec(R)`, every maximal chain of primes `𝔭₀ ⋖ 𝔭₁ ⋖ ⋯ ⋖ 𝔭ₙ` has length
`n = dim(R)`.

The argument is the source's, run over a *fixed* ring. Let `N` be any finite `R`-module which is
Cohen–Macaulay, `depth_𝔪(N) = dim Supp(N)`, and let `𝔭₀ ⋖ ⋯ ⋖ 𝔭ₙ` be a chain of primes whose
head is a minimal point of `Supp(N)` and whose last is a maximal point of `Spec(R)`. If `n = 0`
then `𝔭₀` is at once minimal in `Supp(N)` and, `R` being local, above every prime, so `Supp(N)`
is the single point `𝔭₀` and `dim Supp(N) = 0`. If `n > 0`, every associated prime of `N` is a
minimal point of `Supp(N)` (Stacks 0BUS), hence contains none of `𝔭₁ ⊋ 𝔭₀`; as `Ass(N)` is
finite, prime avoidance produces `x ∈ 𝔭₁` lying in no associated prime of `N`, so `x` is a
nonzerodivisor on `N` and `x ∉ 𝔭₀`. Then `𝔭₁` is a minimal prime over `𝔭₀ + (x)`, because a
prime between them is `𝔭₀` — excluded, since it contains `x` — or `𝔭₁`, by the covering
relation. Since `𝔭₀ ∈ Ass(N)` (Stacks 02CE), some power `xᵏ`, `k ≥ 1`, makes `𝔭₁` an associated
prime of `N/xᵏN` (Stacks 0CN5); that module is again Cohen–Macaulay (Stacks 0C6G), so `𝔭₁` is a
minimal point of `Supp(N/xᵏN) = Supp(N) ∩ V(x) = Supp(N/xN)` by Stacks 0BUS again. Thus
`𝔭₁ ⋖ ⋯ ⋖ 𝔭ₙ` is a chain of the same kind for `N/xN`, which is Cohen–Macaulay by Stacks 0C6G,
and induction gives `n - 1 = dim Supp(N/xN) = dim Supp(N) - 1`.

## Main results

* `Stacks.CohenMacaulay.ChainsFullSupport.solution`: if `R` has a finite maximal Cohen–Macaulay
  module `M` with `Supp(M) = Spec(R)`, every maximal chain of primes of `R` has length `dim(R)`.

## Implementation notes

*Where the mathematics of the induction lives.* One step of the induction is the whole content:
over a Noetherian local ring, a covering pair `𝔭 ⋖ 𝔮` whose foot is a minimal point of the
support of a finite Cohen–Macaulay module `N` admits an `x ∈ 𝔪`, a nonzerodivisor on `N`, for
which `𝔮` is a minimal point of `Supp(N/xN)`. That is the statement carrying the four cited
results, and it is what makes `𝔭₁ ⋖ ⋯ ⋖ 𝔭ₙ` a chain of the same kind for `N/xN`; the induction
itself then only has to match up the two dimensions, and the base case only has to observe that a
chain of length `0` has its head for its last.

*The ring never changes.* The source passes from `R` to `R/xR` and from `M` to `M/xM`, and
measures the drop with `dim(R/xR) = dim(R) - 1` (Stacks 00KW) and the Cohen–Macaulayness of
`M/xM` over `R/xR` (Stacks 00N6 and 0AAD). Stated with `Module.supportDim` instead of
`ringKrullDim`, the same induction runs over `R` itself: `Supp(N/xN) ⊆ Spec(R)` replaces
`Spec(R/xR)`, the dimension drop is Mathlib's
`Module.supportDim_quotSMulTop_succ_eq_supportDim` (a nonzerodivisor in `𝔪` cuts the dimension
of the support by one) and the descent of Cohen–Macaulayness is Stacks 0C6G, whose two sides are
both taken over `R`. This removes the base change of depth and of support along `R → R/xR`, which
is all that 0AAD and Stacks 00L3 were doing, and it is why the induction below is on the length
of the chain rather than on `dim(R)`: the two decrease together, and the length is the one that
is visibly a natural number.

*Cohen–Macaulay, not maximal Cohen–Macaulay, is the inductive invariant.* `N/xN` never has full
support, so `Module.IsMaximalCohenMacaulay` cannot be carried through the induction; the
invariant is the equation `depth_𝔪(N) = dim Supp(N)` of Definition 00N3, which is what Stacks
0BUS and 0C6G are stated with. The hypotheses of Stacks 0AAE give it for `M`: full support turns
`dim Supp(M)` into `dim(R)`, so `Module.IsMaximalCohenMacaulay R M` *is* that equation, exactly
as the discussion preceding the source's lemma remarks.

*Prime avoidance is taken over `Ass(N)`, not over the minimal primes.* The source avoids the
minimal primes of `R`; here the finitely many associated primes of `N` are avoided instead. This
is the stronger requirement, and it is the useful one: it gives at once that `x` is a
nonzerodivisor on `N` and that `x ∉ 𝔭₀`, the two conditions being one and the same by
`Stacks.CohenMacaulay.ChainsFullSupport.isSMulRegular_iff_forall_notMem_associatedPrimes`, the
elementwise form of
`biUnion_associatedPrimes_eq_compl_regular`. Over a Cohen–Macaulay `N` the two sets of primes
coincide by Stacks 0BUS and 02CE, so nothing is lost.

## References

* [StacksProject 0AAE](https://stacks.math.columbia.edu/tag/0AAE)
-/
namespace Stacks.CohenMacaulay.ChainsFullSupport

open Ideal IsLocalRing Module PrimeSpectrum

/-- **Prime avoidance.** An ideal that is contained in none of finitely many prime ideals
contains an element lying in none of them. -/
private theorem exists_mem_notMem_of_finite_of_forall_not_le {R : Type*} [CommRing R]
    {I : Ideal R} {S : Set (Ideal R)} (hfin : S.Finite) (hprime : ∀ q ∈ S, q.IsPrime)
    (hle : ∀ q ∈ S, ¬ I ≤ q) : ∃ x ∈ I, ∀ q ∈ S, x ∉ q := by
  by_contra hcon
  push Not at hcon
  have hsub : (I : Set R) ⊆ ⋃ q ∈ (hfin.toFinset : Set (Ideal R)), (q : Set R) := by
    intro y hy
    obtain ⟨q, hq, hyq⟩ := hcon y hy
    exact Set.mem_biUnion (by simpa using hq) hyq
  obtain ⟨q, hq, hqle⟩ := (Ideal.subset_union_prime ⊤ ⊤
    (fun i hi _ _ => hprime i (by simpa using hi))).mp hsub
  exact hle q (by simpa using hq) hqle

/-- Over a Noetherian ring, an element is a nonzerodivisor on a module exactly when it lies in no
associated prime of that module: the elementwise form of
`biUnion_associatedPrimes_eq_compl_regular`. -/
@[sga "2 III 2.1" "(ii) ⇔ (iv)"]
private theorem isSMulRegular_iff_forall_notMem_associatedPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] {N : Type*} [AddCommGroup N] [Module R N] {x : R} :
    IsSMulRegular N x ↔ ∀ p ∈ associatedPrimes R N, x ∉ p := by
  have h : (∃ p ∈ associatedPrimes R N, x ∈ p) ↔ ¬ IsSMulRegular N x := by
    simpa using Set.ext_iff.mp (biUnion_associatedPrimes_eq_compl_regular R N) x
  rw [← not_iff_not, ← h]
  simp

/-- A minimal point of the support of a finite module over a Noetherian ring is an associated
prime, by Stacks 02CE. -/
private theorem mem_associatedPrimes_of_minimal_support {R : Type*} [CommRing R]
    [IsNoetherianRing R] {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {p : PrimeSpectrum R} (hp : Minimal (· ∈ Module.support R N) p) :
    p.asIdeal ∈ associatedPrimes R N := by
  have hp' : p ∈ {q : PrimeSpectrum R | Minimal (· ∈ Module.support R N) q} := hp
  rw [Module.setOf_minimal_support_eq_setOf_minimal_associatedPrimes] at hp'
  exact hp'.1

/-- If `𝔭 ⋖ 𝔮` and `x` lies in `𝔮` but not in `𝔭`, then `𝔮` is a minimal prime over `𝔭 + (x)`:
a prime `𝔯` with `𝔭 + (x) ≤ 𝔯 ≤ 𝔮` is not `𝔭`, since it contains `x`, hence is `𝔮` by the
covering relation. -/
private theorem mem_minimalPrimes_sup_span_singleton_of_covBy {R : Type*} [CommRing R]
    {p q : PrimeSpectrum R} (hpq : p ⋖ q) {x : R} (hxq : x ∈ q.asIdeal) (hxp : x ∉ p.asIdeal) :
    q.asIdeal ∈ (p.asIdeal + Ideal.span {x}).minimalPrimes := by
  refine ⟨⟨q.isPrime, sup_le ((asIdeal_le_asIdeal _ _).mpr hpq.le)
    (Ideal.span_le.mpr (by simpa using hxq))⟩, fun r hr hrq => ?_⟩
  have hxr : x ∈ r := hr.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  have hlt : p < (⟨r, hr.1⟩ : PrimeSpectrum R) :=
    lt_of_le_of_ne ((asIdeal_le_asIdeal _ _).mp (le_sup_left.trans hr.2))
      fun h => hxp (h ▸ hxr)
  exact le_of_eq (congrArg PrimeSpectrum.asIdeal
    (eq_of_le_of_not_lt ((asIdeal_le_asIdeal _ _).mp hrq) (hpq.2 hlt)).symm)

/-- The support of `N/xᵏN` does not depend on the exponent `k ≥ 1`, both `V(xᵏ)` and `V(x)`
being the vanishing locus of the same radical. -/
private theorem support_quotSMulTop_pow {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N]
    [Module R N] [Module.Finite R N] (x : R) {k : ℕ} (hk : 0 < k) :
    Module.support R (QuotSMulTop (x ^ k) N) = Module.support R (QuotSMulTop x N) := by
  rw [Module.support_quotSMulTop, Module.support_quotSMulTop, zeroLocus_singleton_pow x k hk]

/-- A module over a local ring whose support has a minimal point that is also a maximal point of
`Spec(R)` has that point for its whole support, so `dim Supp(N) = 0`. This is the base case of
Stacks 0AAE: a chain of length `0` has its head equal to its last. -/
private theorem supportDim_eq_zero_of_minimal_of_isMax {R : Type*} [CommRing R] [IsLocalRing R]
    {N : Type*} [AddCommGroup N] [Module R N] {p : PrimeSpectrum R}
    (hmin : Minimal (· ∈ Module.support R N) p) (hmax : IsMax p) :
    Module.supportDim R N = 0 := by
  have key : ∀ c : Module.support R N, c = ⟨p, hmin.1⟩ := fun c =>
    Subtype.ext (le_antisymm (hmax.isTop c.1) (hmin.2 c.2 (hmax.isTop c.1)))
  have : Nonempty (Module.support R N) := ⟨⟨p, hmin.1⟩⟩
  have : Subsingleton (Module.support R N) := ⟨fun a b => by rw [key a, key b]⟩
  exact Order.krullDim_eq_zero (α := Module.support R N)

/-- **The induction step of Stacks 0AAE.** Let `N` be a finite Cohen–Macaulay module over a
Noetherian local ring `(R, 𝔪)`, that is `depth_𝔪(N) = dim Supp(N)`, and let `𝔭 ⋖ 𝔮` be a
covering pair of primes whose foot `𝔭` is a minimal point of `Supp(N)`. Then there is a
nonzerodivisor `x ∈ 𝔪` on `N` for which `𝔮` is a minimal point of `Supp(N/xN)`.

So `N/xN` is a finite Cohen–Macaulay module (Stacks 0C6G) for which `𝔮` plays the role `𝔭` played
for `N`, while `dim Supp(N/xN) + 1 = dim Supp(N)`: this is what lets the chain
`𝔭₀ ⋖ 𝔭₁ ⋖ ⋯ ⋖ 𝔭ₙ` be shortened at the head. -/
private theorem exists_isSMulRegular_minimal_support_quotSMulTop {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Finite R N]
    (hCM : (Module.depth R (maximalIdeal R) N : WithBot ℕ∞) = Module.supportDim R N)
    {p q : PrimeSpectrum R} (hpq : p ⋖ q) (hp : Minimal (· ∈ Module.support R N) p) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular N x ∧
      Minimal (· ∈ Module.support R (QuotSMulTop x N)) q := by
  -- Every associated prime of `N` is a minimal point of `Supp(N)` (Stacks 0BUS), so none of them
  -- contains `𝔮`, which lies strictly above the minimal point `𝔭`.
  have hnotle : ∀ r ∈ associatedPrimes R N, ¬ q.asIdeal ≤ r := by
    intro r hr hle
    have hrmin : Minimal (· ∈ Module.support R N) (⟨r, hr.isPrime⟩ : PrimeSpectrum R) :=
      (Module.ringKrullDim_quotient_eq_supportDim_and_minimal_support_of_mem_associatedPrimes
        hCM hr).2
    have hlt : p < (⟨r, hr.isPrime⟩ : PrimeSpectrum R) :=
      hpq.lt.trans_le ((asIdeal_le_asIdeal _ _).mp hle)
    exact absurd (hrmin.2 hp.1 hlt.le) (not_le_of_gt hlt)
  -- Prime avoidance over the finitely many associated primes produces the nonzerodivisor.
  obtain ⟨x, hxq, hxass⟩ := exists_mem_notMem_of_finite_of_forall_not_le
    (associatedPrimes.finite R N) (fun r hr => hr.isPrime) hnotle
  have hxm : x ∈ maximalIdeal R := le_maximalIdeal q.isPrime.ne_top hxq
  have hreg : IsSMulRegular N x := isSMulRegular_iff_forall_notMem_associatedPrimes.mpr hxass
  refine ⟨x, hxm, hreg, ?_⟩
  -- `𝔭 ∈ Ass(N)` by Stacks 02CE, so `𝔮` is a minimal prime over `𝔭 + (x)` and hence, for some
  -- `k ≥ 1`, an associated prime of the Cohen–Macaulay module `N/xᵏN`; apply Stacks 0BUS to it.
  have hpass : p.asIdeal ∈ associatedPrimes R N := mem_associatedPrimes_of_minimal_support hp
  obtain ⟨k, hk, hqass⟩ := exists_mem_associatedPrimes_quotSMulTop_pow_of_mem_minimalPrimes x
    hpass (mem_minimalPrimes_sup_span_singleton_of_covBy hpq hxq (hxass _ hpass))
  rw [← support_quotSMulTop_pow (N := N) x hk]
  exact (Module.ringKrullDim_quotient_eq_supportDim_and_minimal_support_of_mem_associatedPrimes
    ((Module.depth_eq_supportDim_iff_quotSMulTop (Ideal.pow_mem_of_mem _ hxm k hk)
      (hreg.pow k)).mp hCM) hqass).2

/-- **The induction of Stacks 0AAE, over a fixed ring.** Let `R` be a Noetherian local ring and
`N` a finite Cohen–Macaulay `R`-module, i.e. `depth_𝔪(N) = dim Supp(N)`. Any chain of primes
whose steps are covering pairs, whose head is a minimal point of `Supp(N)` and whose last is a
maximal point of `Spec(R)`, has length `dim Supp(N)`.

Stacks 0AAE is the case `Supp(N) = Spec(R)`. Passing to `N/xN` for a suitable `x` keeps the ring
fixed, which is why the induction is on the length of the chain rather than on `dim(R)`. -/
private theorem length_eq_supportDim {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (n : ℕ) :
    ∀ (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N],
      (Module.depth R (maximalIdeal R) N : WithBot ℕ∞) = Module.supportDim R N →
      ∀ s : RelSeries {(p, q) : PrimeSpectrum R × PrimeSpectrum R | p ⋖ q},
        s.length = n → Minimal (· ∈ Module.support R N) s.head → IsMax s.last →
        (n : WithBot ℕ∞) = Module.supportDim R N := by
  induction n with
  | zero =>
    intro N _ _ _ _ s hlen hmin hmax
    have hhl : s.head = s.last := by
      have : (0 : Fin (s.length + 1)) = Fin.last s.length := by ext; simp [hlen]
      simpa [RelSeries.head, RelSeries.last] using congrArg s this
    simpa using (supportDim_eq_zero_of_minimal_of_isMax hmin (hhl ▸ hmax)).symm
  | succ m ih =>
    intro N _ _ _ hCM s hlen hmin hmax
    have hlen0 : s.length ≠ 0 := by omega
    have hcov : s.head ⋖ (s.tail hlen0).head := s.step ⟨0, Nat.zero_lt_of_ne_zero hlen0⟩
    obtain ⟨x, hxm, hreg, hminq⟩ :=
      exists_isSMulRegular_minimal_support_quotSMulTop hCM hcov hmin
    have hd : Module.supportDim R (QuotSMulTop x N) + 1 = Module.supportDim R N :=
      Module.supportDim_quotSMulTop_succ_eq_supportDim hreg hxm
    rw [← ih (QuotSMulTop x N) ((Module.depth_eq_supportDim_iff_quotSMulTop hxm hreg).mp hCM)
      (s.tail hlen0) (by rw [RelSeries.tail_length]; omega) hminq
      (by rw [RelSeries.last_tail]; exact hmax)] at hd
    push_cast
    exact hd

/-- If a Noetherian local ring `R` has a finite Cohen-Macaulay module `M` with `Supp(M) = Spec(R)`,
then every maximal chain of primes of `R` has length `dim(R)`. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M] (hM : Module.IsMaximalCohenMacaulay R M)
    (hsupp : Module.support R M = Set.univ)
    (s : RelSeries {(p, q) : PrimeSpectrum R × PrimeSpectrum R | p ⋖ q})
    (hmin : IsMin s.head) (hmax : IsMax s.last) :
    (s.length : WithBot ℕ∞) = ringKrullDim R := by
  have hdim : Module.supportDim R M = ringKrullDim R :=
    Module.supportDim_eq_ringKrullDim_of_support_eq_univ hsupp
  refine (length_eq_supportDim s.length M (hM.trans hdim.symm) s rfl ?_ hmax).trans hdim
  exact ⟨hsupp ▸ Set.mem_univ _, fun {b} _ hb => hmin hb⟩

end Stacks.CohenMacaulay.ChainsFullSupport

/-!
# Maximal chains of primes in a local ring carrying a Cohen–Macaulay module of full support

Let `(R, 𝔪)` be a Noetherian local ring and suppose there is a finite Cohen–Macaulay `R`-module
`M` whose support is all of `Spec(R)`. Then `Spec(R)` is equidimensional and catenary in the
strongest sense available: every maximal chain of primes
`𝔭_0 ⊊ 𝔭_1 ⊊ ⋯ ⊊ 𝔭_n` of `R` has length `n = dim(R)`, whatever minimal prime it starts from.

The reason is an induction on `dim(R)`, the case `dim(R) = 0` being empty. If `dim(R) > 0` then
`n > 0`, and one picks `x ∈ 𝔭_1` outside every minimal prime of `R` (prime avoidance, tag 00DS),
so that `dim(R/xR) = dim(R) - 1` (tag 00KW). The module `M/xM` is again Cohen–Macaulay, now over
`R/xR` (tags 00N6 and 0AAD), and its support is all of `Spec(R/xR)` (tag 00L3). Replacing `x` by
a power one may assume `𝔭_1` is an associated prime of `M/xM` (tag 0CN5), whence `𝔭_1/(x)` is a
*minimal* prime of `R/xR` (tag 0BUS). So `𝔭_1/(x) ⊊ ⋯ ⊊ 𝔭_n/(x)` is a maximal chain of primes of
`R/xR`, of length `dim(R/xR) = dim(R) - 1` by induction.

Two special cases are separate tags: the ring itself is Cohen–Macaulay (`M = R`, tag 00N9), and
the resulting dimension formula `dim(R) = dim(R_𝔭) + dim(R/𝔭)` (tags 0AAF and 00NA).

## Main results

* `Module.IsMaximalCohenMacaulay.length_eq_ringKrullDim_of_support_eq_univ`: over a Noetherian
  local ring `R` admitting a finite module `M` with `depth_𝔪(M) = dim(R)` and `Supp(M) = Spec(R)`,
  every maximal chain of primes of `R` has length `dim(R)`.

## Implementation notes

*Cohen–Macaulay with full support, spelled `Module.IsMaximalCohenMacaulay` together with
`Supp(M) = Spec(R)`.* The source's hypothesis is that `M` is a Cohen–Macaulay module
(`depth_𝔪(M) = dim Supp(M)`, Definition 00N3) with `Supp(M) = Spec(R)`. Under the second
condition `dim Supp(M) = dim(R)`, because `Module.supportDim R M` is the Krull dimension of the
poset `Supp(M)` and `Set.univ` is order-isomorphic to `PrimeSpectrum R`; so the first condition
is `depth_𝔪(M) = dim(R)`, which is the predicate `Module.IsMaximalCohenMacaulay R M` of tag
00NF, and the conjunction of the two hypotheses below is the source's verbatim. The source itself
makes this identification in the discussion preceding the lemma ("if `M` is a Cohen-Macaulay
`R`-module with `Spec(R) = Supp(M)`, then `M` is maximal Cohen-Macaulay"). Writing it with the
named predicate is what makes this statement compose with the neighbouring 00NA, 00NB and 00NM,
which are stated in the same spelling. The support condition may not be dropped in favour of
maximal Cohen–Macaulayness alone; see item (1).

*The existential is a parameter.* The source assumes that a Cohen–Macaulay module of full support
*exists*; `M` is taken here as an argument carrying the two hypotheses, which is the same theorem
with the existential unpacked and is what a caller has in hand.

*Maximal chains are `RelSeries` for the covering relation, with extremal ends.* A maximal chain
of primes of `R` is an `s : RelSeries {(p, q) : PrimeSpectrum R × PrimeSpectrum R | p ⋖ q}` with
`IsMin s.head` and `IsMax s.last`: non-refinability in the middle is the covering relation `⋖`,
which says that no prime lies strictly between consecutive members, and non-extendability at the
two ends is minimality and maximality in `PrimeSpectrum R`. This is the spelling of the sibling
tags 00OR, 00OS and of `Ring.IsCatenary` (tag 00NI). `RelSeries.length` counts steps, so the
chain `𝔭_0 ⋖ ⋯ ⋖ 𝔭_n` has length `n`, matching the source's count. As `R` is local,
`IsMax s.last` says `s.last.asIdeal = 𝔪` (`PrimeSpectrum.isMax_iff` and uniqueness of the
maximal ideal), and `IsMin s.head` says `s.head.asIdeal ∈ minimalPrimes R`.

*The dimension is `ringKrullDim`, valued in `WithBot ℕ∞`.* Equating it to the natural number
`s.length` asserts along the way that `dim(R)` is finite, which is part of the content; that is
automatic here (`ringKrullDim_lt_top` for a Noetherian local ring), and it is the reason the
coercion goes on the left-hand side rather than the dimension being cut down to `ℕ`.

Faithfulness to [StacksProject 0AAE].

1. Every hypothesis is used by the conclusion. Both `hM` and `hsupp` fail to be droppable over the
   same ring `R = k[[x, y, z]]/(xy, xz)`, the union of a plane and a transversal line, which has
   `dim(R) = 2` and the maximal chain `(y, z) ⋖ 𝔪` of length `1`: dropping `hM` leaves `M = R`,
   with `Supp(R) = Spec(R)` and `depth_𝔪(R) = 1 ≠ 2`, and dropping `hsupp` leaves
   `M = R/(x) = k[[y, z]]`, which has `depth_𝔪(M) = 2 = dim(R)` but support the plane `V(x)`
   only. `Module.Finite R M` is also live, and not merely inherited: over that same `R` the
   module `M = k[[y, z]] ⊕ R_{(y, z)}` has support `V(x) ∪ {(y, z)} = Spec(R)` and
   `depth_𝔪(M) = 2`, since `x + y` acts on the first summand as the nonzerodivisor `y` and
   invertibly on the second, leaving `M/(x + y)M ≅ k[[z]]` of depth `1`; it is not finite, and
   the conclusion fails for it. `[IsLocalRing R]` is what lets the hypothesis speak of `𝔪` at
   all, and the conclusion genuinely needs it: `R = k × B` with `B` a discrete valuation ring is
   Cohen–Macaulay of dimension `1` with `Supp(R) = Spec(R)`, while the chain consisting of the
   single point `Spec(k)` is maximal of length `0`. `[IsNoetherianRing R]` is the source's, and it
   is what ties depth to chains of primes: the route uses prime avoidance over the finitely many
   minimal primes, Krull's `dim(R/xR) = dim(R) - 1` and the existence of associated primes, none
   of which survives without it.
2. The scalars and base are the source's. `M` is an `R`-module, its depth is taken along the
   maximal ideal of `R` itself, its support is a subset of `Spec(R)`, and the chain and the
   dimension are those of `R`: nothing is localized or based-changed in the statement.
3. The quantities are pinned, not merely compared. The length of each given maximal chain is
   asserted equal to `dim(R)`, rather than bounded by it or realized by some chain, and
   maximality of the chain is pinned as the covering relation on every step together with
   minimality and maximality of the two ends, rather than left as an unspecified maximality among
   chains.
4. The instantiation is not degenerate. For `R = k[[x, y]]` and `M = R` one has
   `depth_𝔪(R) = 2 = dim(R)` and `Supp(R) = Spec(R)`, and the chain `(0) ⋖ (x) ⋖ (x, y)` is
   maximal of length `2`, so the conclusion constrains chains of nonzero length; a witness with
   `M ≠ R` is `M = R ⊕ R` over the same `R`. The case of a field is the degenerate instance,
   where the only chain has length `0 = dim(R)`.

## References

* [StacksProject 0AAE](https://stacks.math.columbia.edu/tag/0AAE)

## Tags

Cohen-Macaulay module, maximal Cohen-Macaulay module, maximal chain of primes, Krull dimension,
support, catenary, equidimensional
-/


/-- **Maximal chains of primes in a local ring with a Cohen–Macaulay module of full support.**
Let `R` be a Noetherian local ring and let `M` be a finite `R`-module which is Cohen–Macaulay
with `Supp(M) = Spec(R)`, that is `depth_𝔪(M) = dim(R)` and `Supp(M) = Spec(R)`. Then every
maximal chain of primes of `R` — one whose steps are covering pairs `𝔭_i ⋖ 𝔭_{i + 1}`, starting
at a minimal prime and ending at a maximal ideal — has length `dim(R)`. -/
@[stacks 0AAE "The source's `M` Cohen-Macaulay with `Spec(R) = Supp(M)` is the conjunction of
`Module.IsMaximalCohenMacaulay R M` (Definition 00NF, i.e. `depth_𝔪(M) = dim R`) and
`Module.support R M = Set.univ`, the two being equivalent to it as the source itself remarks; a
maximal chain of primes is a `RelSeries` for the covering relation `⋖` on `PrimeSpectrum R` whose
head is minimal and whose last is maximal. See the module docstring.",
  ega "IV 15.4.1" "special case"]
public theorem Module.IsMaximalCohenMacaulay.length_eq_ringKrullDim_of_support_eq_univ
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] (hM : Module.IsMaximalCohenMacaulay R M)
    (hsupp : Module.support R M = Set.univ)
    (s : RelSeries {(p, q) : PrimeSpectrum R × PrimeSpectrum R | p ⋖ q})
    (hmin : IsMin s.head) (hmax : IsMax s.last) :
    (s.length : WithBot ℕ∞) = ringKrullDim R :=
      by exact Stacks.CohenMacaulay.ChainsFullSupport.solution (M := M) hM hsupp s hmin hmax


/-!
# Maximal chains of primes in a Cohen–Macaulay local ring

Proof of Stacks 00N9, `Module.IsMaximalCohenMacaulay.length_eq_ringKrullDim`: over a
Noetherian local Cohen–Macaulay ring `R`, every maximal chain of primes `𝔭_0 ⋖ ⋯ ⋖ 𝔭_n` of `R`,
starting at a minimal prime and ending at the maximal ideal, has length `n = dim(R)`.

The source's proof is "special case of Lemma 0AAE", and the special case is `M = R`. Lemma 0AAE
says the same for a Noetherian local ring `R` admitting a finite `R`-module `M` which is maximal
Cohen–Macaulay, `depth_𝔪(M) = dim(R)`, and has full support, `Supp(M) = Spec(R)`. Taking `M = R`
both extra hypotheses are free: `R` is finite over itself, and `Supp(R) = Spec(R)` because `R`
acts faithfully on itself, so its annihilator is `(0)`, whose zero locus is all of `Spec(R)`.

## Main results

* `Stacks.CohenMacaulay.MaximalChains.solution`: over a Noetherian local Cohen–Macaulay ring `R`,
  every maximal chain of primes of `R` has length `dim(R)`.

## Implementation notes

*The support of a ring as a module over itself.* `Module.support R R = Set.univ` is a lemma of the
general theory of supports rather than anything about Cohen–Macaulayness, and it holds over every
commutative ring; Mathlib has it only for a nonzero torsion-free module over a domain
(`Module.support_of_noZeroSMulDivisors`), so it is proved here as `Module.support_self`, from the
three facts that are there: the support of a finite module is the zero locus of its annihilator,
an annihilator is `⊥` exactly when the action is faithful, and `V(⊥) = Spec(R)`. The zero ring is
not an exception — there both sides are empty, `Spec` of the zero ring being empty.

## References

* [StacksProject 00N9](https://stacks.math.columbia.edu/tag/00N9)
* [StacksProject 0AAE](https://stacks.math.columbia.edu/tag/0AAE)
-/

namespace Stacks.CohenMacaulay.MaximalChains

/-- In a Cohen-Macaulay Noetherian local ring `R`, every maximal chain of primes has length
`dim(R)`. -/
public theorem solution
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : Module.IsMaximalCohenMacaulay R R)
    (s : RelSeries {(p, q) : PrimeSpectrum R × PrimeSpectrum R | p ⋖ q})
    (hmin : IsMin s.head) (hmax : IsMax s.last) :
    (s.length : WithBot ℕ∞) = ringKrullDim R :=
  hR.length_eq_ringKrullDim_of_support_eq_univ (Module.support_self R) s hmin hmax

end Stacks.CohenMacaulay.MaximalChains

/-!
# Maximal chains of primes in a Cohen–Macaulay local ring

Let `(R, 𝔪)` be a Noetherian local Cohen–Macaulay ring of dimension `d`. Then `Spec(R)` is
equidimensional and catenary in the strongest sense available: every maximal chain of primes
`𝔭_0 ⊊ 𝔭_1 ⊊ ⋯ ⊊ 𝔭_n` of `R` has length `n = d`, whatever minimal prime it starts from. In
particular no component of `Spec(R)` is too short and no chain can be refined beyond `d` steps.

This is the case `M = R` of tag 0AAE, which says the same for a Noetherian local ring admitting
*some* finite Cohen–Macaulay module of full support: the ring `R` is Cohen–Macaulay exactly when
`R` itself is such a module, its support being all of `Spec(R)` because `1` has zero annihilator.
The dimension formula `dim(R) = dim(R_𝔭) + dim(R/𝔭)` (tag 00NA) is the standard consequence,
obtained by splicing a maximal chain through a given prime `𝔭`.

## Main results

* `Module.IsMaximalCohenMacaulay.length_eq_ringKrullDim`: over a Noetherian local Cohen–Macaulay
  ring `R`, every maximal chain of primes of `R` has length `dim(R)`.

## Implementation notes

*Cohen–Macaulayness of the ring is `Module.IsMaximalCohenMacaulay R R`.* This is Definition 00N8
verbatim: a Noetherian local ring is Cohen–Macaulay when it is Cohen–Macaulay as a module over
itself, that is `depth_𝔪(R) = dim Supp(R)` (Definition 00N3), and `Supp(R) = Spec(R)` because the
annihilator of `1` is zero, so `dim Supp(R) = dim(R)` and the condition is `depth_𝔪(R) = dim(R)`,
the predicate of tag 00NF. This is the spelling of the neighbouring tags 00NA, 00NB and 00NM,
so the four compose without a bridge.

*Maximal chains are `RelSeries` for the covering relation, with extremal ends.* A maximal chain
of primes of `R` is an `s : RelSeries {(p, q) : PrimeSpectrum R × PrimeSpectrum R | p ⋖ q}` with
`IsMin s.head` and `IsMax s.last`: non-refinability in the middle is the covering relation `⋖`,
which says that no prime lies strictly between consecutive members, and non-extendability at the
two ends is minimality and maximality in `PrimeSpectrum R`. This is the spelling of tag 0AAE, of
the sibling tags 00OR and 00OS, and of `Ring.IsCatenary` (tag 00NI). `RelSeries.length` counts
steps, so `𝔭_0 ⋖ ⋯ ⋖ 𝔭_n` has length `n`, matching the source's count. As `R` is local,
`IsMax s.last` says `s.last.asIdeal = 𝔪` (`PrimeSpectrum.isMax_iff` and uniqueness of the
maximal ideal), and `IsMin s.head` says `s.head.asIdeal ∈ minimalPrimes R`.

*The dimension is `ringKrullDim`, valued in `WithBot ℕ∞`.* The source's name `d` for `dim(R)` is
not a parameter: it restricts nothing, and `n = d` is the equation `s.length = dim(R)`. Equating
`dim(R)` to the natural number `s.length` asserts along the way that `dim(R)` is finite, which is
part of the content; that is automatic here (`ringKrullDim_lt_top` for a Noetherian local ring),
and it is the reason the coercion goes on the left-hand side rather than the dimension being cut
down to `ℕ`.

*The source writes "chain of ideals".* The `𝔭_i` are primes, as the slogan of tag 0AAE and the
proof there both make explicit; a chain of arbitrary ideals of a nonzero ring is never of bounded
length, so the literal reading has no content.

Faithfulness to [StacksProject 00N9]:

1. Every hypothesis is used by the conclusion. `hR` is load-bearing: over
   `R = k[[x, y, z]]/(xy, xz)`, the union of a plane and a transversal line, one has `dim(R) = 2`
   and `depth_𝔪(R) = 1`, and `(y, z) ⋖ 𝔪` is a maximal chain of length `1 ≠ 2`. `[IsLocalRing R]`
   is what lets the hypothesis speak of `𝔪` at all, and the conclusion needs it too: `R = k × B`
   with `B` a discrete valuation ring is Cohen–Macaulay of dimension `1`, while the chain
   consisting of the single point `Spec(k)` is maximal of length `0`. `[IsNoetherianRing R]` is
   the source's and is what ties depth to chains of primes; the route (tag 0AAE) uses prime
   avoidance over the finitely many minimal primes, Krull's `dim(R/xR) = dim(R) - 1` and the
   existence of associated primes, none of which survives without it. The source's `d` is dropped
   as a parameter for the reason given above.
2. The scalars and base are the source's. The depth in the hypothesis is that of `R` as a module
   over `R` along the maximal ideal of `R` itself, and the chain and the dimension are those of
   `R`: nothing is localized or based-changed in the statement.
3. The quantities are pinned, not merely compared. The length of each given maximal chain is
   asserted equal to `dim(R)`, rather than bounded by it or realized by some chain, and
   maximality of the chain is pinned as the covering relation on every step together with
   minimality and maximality of the two ends, rather than left as an unspecified maximality among
   chains.
4. The instantiation is not degenerate. For `R = k[[x, y]]` one has `depth_𝔪(R) = 2 = dim(R)`,
   and the chain `(0) ⋖ (x) ⋖ (x, y)` is maximal of length `2`, so the conclusion constrains
   chains of nonzero length; the case of a field is the degenerate instance, where the only chain
   has length `0 = dim(R)`.

## References

* [StacksProject 00N9](https://stacks.math.columbia.edu/tag/00N9)

## Tags

Cohen-Macaulay ring, maximal chain of primes, Krull dimension, catenary, equidimensional
-/


/-- **Maximal chains of primes in a Cohen–Macaulay local ring.** Let `R` be a Noetherian local
Cohen–Macaulay ring, that is `depth_𝔪(R) = dim(R)`. Then every maximal chain of primes of `R` —
one whose steps are covering pairs `𝔭_i ⋖ 𝔭_{i + 1}`, starting at a minimal prime and ending at
the maximal ideal — has length `dim(R)`. -/
@[stacks 00N9 "Cohen-Macaulayness of the Noetherian local ring `R` is the predicate
`Module.IsMaximalCohenMacaulay R R` (Definition 00N8, i.e. `depth_𝔪(R) = dim R`); a maximal chain
of primes is a `RelSeries` for the covering relation `⋖` on `PrimeSpectrum R` whose head is
minimal and whose last is maximal; the source's name `d` for `dim R` is dropped. See the module
docstring.", ega "IV 15.4.1" "special case"]
public theorem Module.IsMaximalCohenMacaulay.length_eq_ringKrullDim
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : Module.IsMaximalCohenMacaulay R R)
    (s : RelSeries {(p, q) : PrimeSpectrum R × PrimeSpectrum R | p ⋖ q})
    (hmin : IsMin s.head) (hmax : IsMax s.last) :
    (s.length : WithBot ℕ∞) = ringKrullDim R :=
      by exact Stacks.CohenMacaulay.MaximalChains.solution hR s hmin hmax


/-!
# The dimension formula in a local ring with a Cohen–Macaulay module of full support

Proof of Stacks 0AAF, stated as
`Module.IsMaximalCohenMacaulay.ringKrullDim_eq_height_add_ringKrullDim_quotient_of_support_eq_univ`
below: for `(R, 𝔪)` a Noetherian local ring admitting a finite Cohen–Macaulay module `M` with
`Supp(M) = Spec(R)`, every prime `𝔭` satisfies `dim(R) = dim(R_𝔭) + dim(R / 𝔭)`.

The source's proof is one line, "follows immediately from Lemma 0AAE", and what it compresses is
the construction of a *maximal* chain of primes through `𝔭`. Both summands are chain lengths at
the point `𝔭` of `Spec(R)`: `dim(R_𝔭)` is its height and `dim(R / 𝔭)` is its coheight. A chain of
primes ending at `𝔭` of length `height 𝔭` cannot be refined or extended downwards, since either
operation would produce a longer chain ending at `𝔭`; so a covering refinement of it starts at a
minimal prime and still has length `height 𝔭`. Dually there is a chain of covering pairs from `𝔭`
to a maximal ideal of length `coheight 𝔭`. Splicing the two at `𝔭` exhibits a maximal chain of
primes of length `height 𝔭 + coheight 𝔭`, and Stacks 0AAE says every maximal chain has length
`dim(R)`.

## Main results

* `Stacks.CohenMacaulay.SupportDimFormula.solution`: if `R` has a finite maximal Cohen–Macaulay
  module `M` with `Supp(M) = Spec(R)`, every prime `𝔭` of `R` satisfies
  `dim(R) = height(𝔭) + dim(R/𝔭)`.

## Implementation notes

The order-theoretic content is isolated from the ring theory: for `x` an element of finite height
and coheight in a partial order whose chains are bounded in both directions there is a chain of
covering pairs through `x` from a minimal to a maximal element, of length `height x + coheight x`
(`exists_relSeries_covBy_and_isMin_head_and_isMax_last`). Its two halves are the same lemma read
in `α` and in `αᵒᵈ`, since `Order.coheight` is by definition `Order.height` in the order dual; the
transport of a series of covering pairs of `αᵒᵈ` to one of `α` is `RelSeries.reverse` followed by
`RelSeries.map` along `OrderDual.ofDual`.

Neither `Order.height` nor `Order.coheight` appears in the statement, so both have to
be identified with a ring-theoretic quantity: `Ideal.height` is `Order.height` in `PrimeSpectrum R`
by `PrimeSpectrum.height_eq_orderHeight`, and `ringKrullDim (R ⧸ 𝔭)` is the coheight of `𝔭`
(`coheight_eq_ringKrullDim_quotient` of `StacksFrontier.RingTheory.Equidimensional.FlatLocal`, which
Mathlib does not record; it is `ringKrullDim_quotient`
together with `Order.coheight_eq_krullDim_Ici`, the two sets `V(𝔭)` and `Set.Ici 𝔭` being equal by
definition).

`WellFoundedLT` and `WellFoundedGT` for an order with chains of bounded length are not instances in
Mathlib, only the `SetRel` statements `SetRel.IsWellFounded.of_finiteDimensional` and its `inv`
form, so they are re-derived here as `wellFoundedLT_of_finiteDimensionalOrder` and
`wellFoundedGT_of_finiteDimensionalOrder`, as in the proof of Stacks 00OS.

## References

* [StacksProject 0AAF](https://stacks.math.columbia.edu/tag/0AAF)
-/


namespace Stacks.CohenMacaulay.SupportDimFormula

open Order

section WellFounded

/-- An order with chains of bounded length has no infinite descending chain. -/
private lemma wellFoundedLT_of_finiteDimensionalOrder (α : Type*) [Preorder α]
    [FiniteDimensionalOrder α] : WellFoundedLT α :=
  SetRel.IsWellFounded.of_finiteDimensional {(a, b) : α × α | a < b}

/-- An order with chains of bounded length has no infinite ascending chain. -/
private lemma wellFoundedGT_of_finiteDimensionalOrder (α : Type*) [Preorder α]
    [FiniteDimensionalOrder α] : WellFoundedGT α :=
  SetRel.IsWellFounded.inv_of_finiteDimensional {(a, b) : α × α | a < b}

end WellFounded

section MaximalChains

variable {α : Type*} [PartialOrder α] [WellFoundedLT α] [WellFoundedGT α]

/-- An element of finite height `n` is the top of a chain of `n` covering pairs starting at a
minimal element: a chain of length `n` ending at `x` can be refined to one of covering pairs
with the same ends, and neither the refinement nor an extension below its head can be longer
than `height x`. -/
private lemma exists_relSeries_covBy_and_isMin_head (x : α) {n : ℕ} (hn : height x = n) :
    ∃ s : RelSeries {(a, b) : α × α | a ⋖ b}, s.last = x ∧ IsMin s.head ∧ s.length = n := by
  obtain ⟨l, hlast, hlen⟩ := exists_series_of_height_eq_coe x hn
  obtain ⟨t, i, hti, -, hi₁⟩ := l.exists_relSeries_covBy
  have hlt : {(a, b) : α × α | a ⋖ b} ≤ {(a, b) : α × α | a < b} := by
    rintro ⟨a, b⟩ hab; exact hab.lt
  have hlastt : t.last = x := by
    have h := congr_fun hti (Fin.last _)
    rw [Function.comp_apply, hi₁] at h
    exact h.trans hlast
  have hlen₁ : n ≤ t.length := by simpa [hlen] using Fintype.card_le_of_embedding i
  -- any chain of the strict order ending at `x` has length at most `height x = n`
  have hle : ∀ u : RelSeries {(a, b) : α × α | a < b}, u.last = x → u.length ≤ n := fun u hu ↦ by
    exact_mod_cast hn ▸ hu ▸ length_le_height_last (p := u)
  refine ⟨t, hlastt, ?_, le_antisymm (hle (t.ofLE hlt) hlastt) hlen₁⟩
  by_contra hmin
  obtain ⟨y, hy⟩ := not_isMin_iff.mp hmin
  have hy' : (y, (t.ofLE hlt).head) ∈ {(a, b) : α × α | a < b} := hy
  have := hle ((t.ofLE hlt).cons y hy') ((RelSeries.last_cons ..).trans hlastt)
  rw [RelSeries.cons_length] at this
  exact Nat.not_succ_le_self _ (this.trans hlen₁)

/-- An element of finite coheight `n` is the bottom of a chain of `n` covering pairs ending at a
maximal element. This is `exists_relSeries_covBy_and_isMin_head` in the order dual. -/
private lemma exists_relSeries_covBy_and_isMax_last (x : α) {n : ℕ} (hn : coheight x = n) :
    ∃ s : RelSeries {(a, b) : α × α | a ⋖ b}, s.head = x ∧ IsMax s.last ∧ s.length = n := by
  obtain ⟨t, hlast, hmin, hlen⟩ :=
    exists_relSeries_covBy_and_isMin_head (α := αᵒᵈ) (OrderDual.toDual x) hn
  refine ⟨t.reverse.map ⟨OrderDual.ofDual, fun h ↦ ofDual_covBy_ofDual_iff.mpr h⟩, ?_, ?_, ?_⟩
  · simp only [RelSeries.head_map, RelSeries.head_reverse]
    exact hlast
  · simp only [RelSeries.last_map, RelSeries.last_reverse]
    exact hmin
  · simpa using hlen

/-- An element of finite height and coheight lies on a maximal chain — a chain of covering pairs
from a minimal to a maximal element — of length `height x + coheight x`. -/
private lemma exists_relSeries_covBy_and_isMin_head_and_isMax_last (x : α) {m n : ℕ}
    (hm : height x = m) (hn : coheight x = n) :
    ∃ s : RelSeries {(a, b) : α × α | a ⋖ b}, IsMin s.head ∧ IsMax s.last ∧ s.length = m + n := by
  obtain ⟨t, htlast, htmin, htlen⟩ := exists_relSeries_covBy_and_isMin_head x hm
  obtain ⟨u, uhead, umax, ulen⟩ := exists_relSeries_covBy_and_isMax_last x hn
  refine ⟨t.smash u (htlast.trans uhead.symm), ?_, ?_, ?_⟩
  · rwa [RelSeries.head_smash]
  · rwa [RelSeries.last_smash]
  · rw [RelSeries.smash_length, htlen, ulen]

end MaximalChains

section Ring

variable {R : Type*} [CommRing R]

end Ring

/-- If a Noetherian local ring `R` has a finite Cohen-Macaulay module `M` with `Supp(M) = Spec(R)`,
then every prime `𝔭` of `R` satisfies `dim(R) = height(𝔭) + dim(R/𝔭)`. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M] (hM : Module.IsMaximalCohenMacaulay R M)
    (hsupp : Module.support R M = Set.univ) (p : Ideal R) [p.IsPrime] :
    ringKrullDim R = p.height + ringKrullDim (R ⧸ p) := by
  have := wellFoundedLT_of_finiteDimensionalOrder (PrimeSpectrum R)
  have := wellFoundedGT_of_finiteDimensionalOrder (PrimeSpectrum R)
  set x : PrimeSpectrum R := ⟨p, ‹p.IsPrime›⟩
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top_of_isPrime (I := p))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (coheight_lt_top x).ne
  have hheight : height x = (m : ℕ∞) := by
    rw [← PrimeSpectrum.height_eq_orderHeight x, ← hm]
  obtain ⟨s, hmin, hmax, hlen⟩ :=
    exists_relSeries_covBy_and_isMin_head_and_isMax_last x hheight hn.symm
  have h := Module.IsMaximalCohenMacaulay.length_eq_ringKrullDim_of_support_eq_univ hM hsupp s
    hmin hmax
  rw [hlen] at h
  rw [← h, ← hm, ← coheight_eq_ringKrullDim_quotient x, ← hn]
  push_cast
  ring

end Stacks.CohenMacaulay.SupportDimFormula


/-!
# The dimension formula in a local ring carrying a Cohen–Macaulay module of full support

Let `(R, 𝔪)` be a Noetherian local ring and suppose there is a finite Cohen–Macaulay `R`-module
`M` whose support is all of `Spec(R)`. Then for every prime `𝔭 ⊆ R`
$$
  \dim(R) = \dim(R_\mathfrak{p}) + \dim(R/\mathfrak{p}).
$$
Geometrically: the existence of such an `M` forces `Spec(R)` to be equidimensional with no
component that is too short, so `𝔭` sits at the top of a chain descending to a minimal prime of
length exactly `dim(R_𝔭)` and at the bottom of a chain ascending to `𝔪` of length exactly
`dim(R/𝔭)`; splicing the two exhibits a maximal chain of primes through `𝔭`, and every maximal
chain of primes of such an `R` has length `dim(R)` (tag 0AAE). In particular `R` is catenary and
equidimensional. The case `M = R`, that is `R` Cohen–Macaulay, is tag 00NA.

The dimension of the localisation is written `𝔭.height`: for a prime `𝔭` the height is the
dimension of `R_𝔭` on the nose, `IsLocalization.AtPrime.ringKrullDim_eq_height` transporting
that equality to any ring satisfying `IsLocalization.AtPrime _ 𝔭`, so no localisation has to be
chosen in order to state the result. Heights take values in `ℕ∞` and `ringKrullDim` in
`WithBot ℕ∞`, the value `⊥` being reserved for the zero ring; the equation is read in
`WithBot ℕ∞`.

## Main results

* `ringKrullDim_eq_height_add_ringKrullDim_quotient_of_support_eq_univ`, in the namespace
  `Module.IsMaximalCohenMacaulay`: `dim R = dim R_𝔭 + dim R/𝔭` for a prime `𝔭` of a Noetherian
  local ring `R` admitting a finite module `M` with `depth_𝔪(M) = dim(R)` and `Supp(M) = Spec(R)`.

## Implementation notes

*Cohen–Macaulay with full support, spelled `Module.IsMaximalCohenMacaulay` together with
`Supp(M) = Spec(R)`.* The source's hypothesis is that `M` is a Cohen–Macaulay module
(`depth_𝔪(M) = dim Supp(M)`, Definition 00N3) with `Supp(M) = Spec(R)`. Under the second
condition `dim Supp(M) = dim(R)`, because `Module.supportDim R M` is the Krull dimension of the
poset `Supp(M)` and `Set.univ` is order-isomorphic to `PrimeSpectrum R`; so the first condition
is `depth_𝔪(M) = dim(R)`, which is the predicate `Module.IsMaximalCohenMacaulay R M` of tag
00NF, and the conjunction of the two hypotheses below is the source's verbatim. The source itself
makes this identification in the discussion preceding tag 0AAE ("if `M` is a Cohen-Macaulay
`R`-module with `Spec(R) = Supp(M)`, then `M` is maximal Cohen-Macaulay"). This is the spelling of
the immediate neighbours 0AAE, 00NA, 00NB and 00NM, so those statements compose with this one
without a bridge. The support condition may not be dropped in favour of maximal
Cohen–Macaulayness alone; see item (1).

*The existential is a parameter.* The source assumes that a Cohen–Macaulay module of full support
*exists*; `M` is taken here as an argument carrying the two hypotheses, which is the same theorem
with the existential unpacked and is what a caller has in hand.

Faithfulness to [StacksProject 0AAF]:

1. Every hypothesis is used by the conclusion. `hM` and `hsupp` both fail to be droppable over
   `R = k[[x, y, z]]/(xy, xz)`, the union of a plane and a transversal line, which has
   `dim(R) = 2` while the minimal prime `𝔭 = (y, z)` has `𝔭.height = 0` and
   `dim(R/𝔭) = dim k[[x]] = 1`, so the conclusion reads `2 = 0 + 1` and fails: dropping `hM`
   leaves `M = R`, with `Supp(R) = Spec(R)` and `depth_𝔪(R) = 1 ≠ 2`, and dropping `hsupp`
   leaves `M = R/(x) = k[[y, z]]`, which has `depth_𝔪(M) = 2 = dim(R)` but support the plane
   `V(x)` only. `Module.Finite R M` is live too, and not merely inherited: over that same `R` the
   module `M = k[[y, z]] ⊕ R_{(y, z)}` has support `V(x) ∪ {(y, z)} = Spec(R)` and
   `depth_𝔪(M) = 2`, since `x + y` acts on the first summand as the nonzerodivisor `y` and
   invertibly on the second, leaving `M/(x + y)M ≅ k[[z]]` of depth `1`; it is not finite, and
   the conclusion fails for it at the same `𝔭`. `[IsLocalRing R]` is what lets the hypothesis
   speak of `𝔪` at all, and the conclusion needs it: for `R = k × B` with `B` a discrete
   valuation ring — Cohen–Macaulay of dimension `1` with `Supp(R) = Spec(R)` — the prime
   `𝔭 = 0 × B` has `𝔭.height = 0` and `R/𝔭 ≅ k` of dimension `0`, against `dim(R) = 1`.
   `[IsNoetherianRing R]` is the source's, and it is what ties depth to chains of primes: the
   route through 0AAE uses prime avoidance over the finitely many minimal primes, Krull's
   `dim(R/xR) = dim(R) - 1` and the existence of associated primes, none of which survives
   without it. `[p.IsPrime]` is what the conclusion quantifies over, and it is what makes
   `𝔭.height` the dimension of `R_𝔭`.
2. The scalars and base are the source's. `M` is an `R`-module, its depth is taken along the
   maximal ideal of `R` itself and its support is a subset of `Spec(R)`; the three dimensions are
   those of rings built from `R` itself — `R`, its localisation at `𝔭` (as `𝔭.height`) and the
   quotient `R ⧸ 𝔭`. Nothing is localized or based-changed in the hypotheses.
3. The quantities are pinned, not merely compared. `dim(R_𝔭)` is `𝔭.height`, which equals
   `ringKrullDim` of every localisation of `R` at `𝔭` by
   `IsLocalization.AtPrime.ringKrullDim_eq_height`, and `dim(R/𝔭)` is `ringKrullDim (R ⧸ 𝔭)` for
   the canonical quotient; the statement is the equality of those values, not one of the two
   inequalities, and not the existence of some chain through `𝔭` realizing them.
4. The instantiation is not degenerate. For `R = k[[x, y]]` and `M = R ⊕ R` one has
   `depth_𝔪(M) = 2 = dim(R)` and `Supp(M) = Spec(R)`, and at the prime `𝔭 = (x)` the formula
   reads `2 = 1 + 1`, so both summands are genuinely nonzero for some instance and the witness
   has `M ≠ R`. The primes `𝔭 = 0` and `𝔭 = 𝔪` are the two extreme instances, where the formula
   reads `dim(R) = 0 + dim(R)` and `dim(R) = dim(R) + 0`; a field is the degenerate instance,
   where every term is `0`.

## References

* [StacksProject 0AAF](https://stacks.math.columbia.edu/tag/0AAF)

## Tags

Cohen-Macaulay module, maximal Cohen-Macaulay module, Krull dimension, height, catenary,
equidimensional, dimension formula
-/


namespace Module.IsMaximalCohenMacaulay

/-- **The dimension formula in a local ring with a Cohen–Macaulay module of full support.** Let
`R` be a Noetherian local ring and let `M` be a finite `R`-module which is Cohen–Macaulay with
`Supp(M) = Spec(R)`, that is `depth_𝔪(M) = dim(R)` and `Supp(M) = Spec(R)`. Then every prime `𝔭`
of `R` satisfies `dim(R) = dim(R_𝔭) + dim(R/𝔭)`, the dimension of the localisation `R_𝔭` being
written as the height of `𝔭`. -/
@[stacks 0AAF "The source's `M` Cohen-Macaulay with `Spec(R) = Supp(M)` is the conjunction of
`Module.IsMaximalCohenMacaulay R M` (Definition 00NF, i.e. `depth_𝔪(M) = dim R`) and
`Module.support R M = Set.univ`, the two being equivalent to it as the source itself remarks;
`dim(R_𝔭)` is written `𝔭.height`. See the module docstring.",
  ega "0 16.5.11",
  ega "0 16.5.10" "(ii), Supp M = Spec A", ega "IV 15.4.1" "special case"]
public theorem ringKrullDim_eq_height_add_ringKrullDim_quotient_of_support_eq_univ
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] (hM : Module.IsMaximalCohenMacaulay R M)
    (hsupp : Module.support R M = Set.univ) (p : Ideal R) [p.IsPrime] :
    ringKrullDim R = p.height + ringKrullDim (R ⧸ p) :=
    by exact Stacks.CohenMacaulay.SupportDimFormula.solution (M := M) hM hsupp p

end Module.IsMaximalCohenMacaulay


@[expose] public section



/-!
# The dimension formula in a Cohen–Macaulay local ring

Proof of Stacks 00NA,
`Module.IsMaximalCohenMacaulay.ringKrullDim_eq_height_add_ringKrullDim_quotient`: for `(R, 𝔪)` a
Noetherian local Cohen–Macaulay ring, every prime `𝔭` satisfies
`dim(R) = dim(R_𝔭) + dim(R / 𝔭)`, the dimension of the localisation being written `𝔭.height`.

The source records that the statement is the special case `M = R` of Lemma 0AAF, and that special
case is what is taken here. Lemma 0AAF is 00NA for a Noetherian local ring `R` admitting a finite
`R`-module `M` which is maximal Cohen–Macaulay, `depth_𝔪(M) = dim(R)`, and of full support,
`Supp(M) = Spec(R)`. At `M = R` the Cohen–Macaulay hypothesis is that of 00NA, and the two extra
hypotheses are free: `R` is finite over itself, and it acts faithfully on itself, so
`Supp(R) = V(Ann(R)) = V(0) = Spec(R)`.

## Main results

* `Stacks.CohenMacaulay.DimensionFormula.solution`: over a Noetherian local Cohen–Macaulay ring
  `R`, every prime `𝔭` satisfies `dim(R) = height(𝔭) + dim(R/𝔭)`.

## Implementation notes

*Lemma 0AAF rather than Lemma 00N9.* The source's own proof is "follows immediately from Lemma
00N9": both summands are chain lengths at the point `𝔭` of `Spec(R)`, and splicing a covering
chain from a minimal prime up to `𝔭` with one from `𝔭` up to `𝔪` exhibits a maximal chain through
`𝔭` of length `𝔭.height + dim(R/𝔭)`, which 00N9 says has length `dim(R)`. That splicing is the
whole content of the proof of 0AAF, and 0AAF is deduced from 0AAE, of which 00N9 is itself the
case `M = R`; so specialising 0AAF is the same mathematics with the splicing done once instead of
twice.

*The support of `R` as a module over itself.* `Module.support R R = Set.univ` is proved here as
`Module.support_self`, from three facts of the general theory: the support of a finite module is
the zero locus of its annihilator, an annihilator is `⊥` exactly when the action is faithful, and
`V(⊥) = Spec(R)`. Mathlib has the conclusion only for a nonzero torsion-free module over a domain
(`Module.support_of_noZeroSMulDivisors`), and the form used here needs neither hypothesis; the
zero ring is not an exception, both sides being empty over it.

## References

* [StacksProject 00NA](https://stacks.math.columbia.edu/tag/00NA)
* [StacksProject 0AAF](https://stacks.math.columbia.edu/tag/0AAF)
-/

namespace Stacks.CohenMacaulay.DimensionFormula

/-- In a Cohen-Macaulay Noetherian local ring `R`, every prime `𝔭` satisfies
`dim(R) = height(𝔭) + dim(R/𝔭)`. -/
public theorem solution
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : Module.IsMaximalCohenMacaulay R R) (p : Ideal R) [p.IsPrime] :
    ringKrullDim R = p.height + ringKrullDim (R ⧸ p) :=
  hR.ringKrullDim_eq_height_add_ringKrullDim_quotient_of_support_eq_univ
    (Module.support_self R) p

end Stacks.CohenMacaulay.DimensionFormula

/-!
# The dimension formula in a Cohen–Macaulay local ring

Let `(R, 𝔪)` be a Noetherian local Cohen–Macaulay ring. Then for every prime `𝔭 ⊆ R`
$$
  \dim(R) = \dim(R_\mathfrak{p}) + \dim(R/\mathfrak{p}).
$$
Geometrically: `Spec R` has no components that are too short, so every prime sits at the top of
a chain descending to a minimal prime of length exactly `dim(R_𝔭)` and at the bottom of a chain
ascending to `𝔪` of length exactly `dim(R/𝔭)`; splicing the two exhibits a maximal chain of
primes through `𝔭`, and in a Cohen–Macaulay local ring every maximal chain of primes has length
`dim R` (tag 00N9). In particular such a ring is catenary and equidimensional.

The dimension of the localisation is written `𝔭.height`: for a prime `𝔭` the height is the
dimension of `R_𝔭` on the nose, `IsLocalization.AtPrime.ringKrullDim_eq_height` transporting
that equality to any ring satisfying `IsLocalization.AtPrime _ 𝔭`, so no localisation has to be
chosen in order to state the result. Heights take values in `ℕ∞` and `ringKrullDim` in
`WithBot ℕ∞`, the value `⊥` being reserved for the zero ring; the equation is read in
`WithBot ℕ∞`.

## Main results

* `Module.IsMaximalCohenMacaulay.ringKrullDim_eq_height_add_ringKrullDim_quotient`:
  `dim R = dim R_𝔭 + dim R/𝔭` for a prime `𝔭` of a Noetherian local Cohen–Macaulay ring `R`.

## Implementation notes

Cohen–Macaulayness of the ring is the hypothesis `Module.IsMaximalCohenMacaulay R R` (tag 00NF),
that is `depth_𝔪(R) = dim R`. This is Definition 00N8 verbatim: `R` is Cohen–Macaulay when it is
Cohen–Macaulay as a module over itself, i.e. `depth_𝔪(R) = dim Supp(R)` (Definition 00N3), and
`Supp(R) = Spec(R)` because `1` has zero annihilator, so `dim Supp(R) = dim R`. The equality
`depth_𝔪(R) = dim R` in `WithBot ℕ∞` is also what tag 00NQ concludes about a regular local ring,
so the two statements compose without a bridge.

Faithfulness to [StackProject 00NA]:

1. No dead hypothesis. `hR` is the Cohen–Macaulay hypothesis; `[IsLocalRing R]` is needed to
   state it and is what makes `dim R` the length of a maximal chain up to `𝔪`; `[p.IsPrime]`
   makes `𝔭.height` the dimension of `R_𝔭` and is what the conclusion quantifies over;
   `[IsNoetherianRing R]` is the source's and is load-bearing, being what ties depth to
   dimension (the route is 00N9, itself Noetherian dimension theory) — without it the depth
   hypothesis carries no information about chains of primes. The source's `d = dim(R)` is
   dropped: it names `ringKrullDim R` rather than restricting `R`, and the displayed equation
   does not mention it.
2. The scalars and base are the source's. All three dimensions are those of rings built from `R`
   itself — `R`, its localisation at `𝔭` (as `𝔭.height`) and the quotient `R ⧸ 𝔭` — and the
   depth in the hypothesis is that of `R` as a module over `R`, along the maximal ideal of `R`.
3. The quantities are pinned, not merely compared. `dim(R_𝔭)` is `𝔭.height`, which equals
   `ringKrullDim` of every localisation of `R` at `𝔭` by
   `IsLocalization.AtPrime.ringKrullDim_eq_height`, and `dim(R/𝔭)` is `ringKrullDim (R ⧸ 𝔭)`
   for the canonical quotient; the statement is the equality of those values, not an inequality
   or an existence claim.
4. The instantiation is not degenerate. A discrete valuation ring `R` is Noetherian local with
   `depth_𝔪(R) = 1 = dim R`, and the formula reads `1 = 0 + 1` at `𝔭 = 0` and `1 = 1 + 0` at
   `𝔭 = 𝔪`; for a two-dimensional regular local ring, such as the local ring of the affine plane
   at the origin, and `𝔭` the prime of a coordinate line through it, the formula reads
   `2 = 1 + 1`, so both summands are genuinely nonzero for some instance.

## References

* [StackProject 00NA](https://stacks.math.columbia.edu/tag/00NA)

## Tags

Cohen-Macaulay ring, Krull dimension, height, catenary
-/


/-- **The dimension formula in a Cohen–Macaulay local ring.** If `R` is a Noetherian local
Cohen–Macaulay ring, that is `depth_𝔪(R) = dim R`, then every prime `𝔭` of `R` satisfies
`dim R = dim R_𝔭 + dim R/𝔭`, the dimension of the localisation `R_𝔭` being written as the
height of `𝔭`. -/
@[stacks 00NA "Cohen-Macaulayness of `R` is the hypothesis `Module.IsMaximalCohenMacaulay R R`,
i.e. `depth_𝔪(R) = dim R` (Definition 00N8); `dim(R_𝔭)` is written `𝔭.height`; the source's name
`d` for `dim R` is dropped.",
  ega "0 16.5.11" "case M = R",
  ega "0 16.5.10" "(ii) for M = A",
  ega "IV 15.4.1" "special case"]
public theorem Module.IsMaximalCohenMacaulay.ringKrullDim_eq_height_add_ringKrullDim_quotient
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : Module.IsMaximalCohenMacaulay R R) (p : Ideal R) [p.IsPrime] :
    ringKrullDim R = p.height + ringKrullDim (R ⧸ p) :=
      by exact Stacks.CohenMacaulay.DimensionFormula.solution hR p

end
