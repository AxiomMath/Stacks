module

public import Mathlib.RingTheory.Ideal.Height
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
public import Mathlib.RingTheory.Radical.NatInt
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
# A quasi-finite map does not raise the dimension of the local ring

Let `R → S` be a ring map, let `𝔮` be a prime of `S` and let `𝔭` be the prime of `R` it lies
over. This file proves Stacks 00QF: if `R → S` is quasi-finite at `𝔮`, then

`dim(S_𝔮) ≤ dim(R_𝔭)`,

in the form `𝔮.height ≤ 𝔭.height`.

The proof compares chains of primes directly. Quasi-finiteness at `𝔮` passes to every prime
below `𝔮` (`Algebra.QuasiFiniteAt.of_le`), and a quasi-finite prime is determined by any prime
above it with the same contraction to `R`, the fibres of a quasi-finite map being discrete
(`Algebra.QuasiFiniteAt.eq_of_le_of_under_eq`). So contraction of ideals, which is always
monotone, is *strictly* monotone on the primes at most `𝔮`; a map that is strictly monotone below
a point does not decrease the height of that point, so `𝔮.height ≤ (𝔮.under R).height`, and the
right-hand side is `𝔭.height`.

## Main results

* `Stacks.QuasiFinite.HeightBound.solution`: the statement of Stacks 00QF.

## Implementation notes

The inequality is proved in the form `Q.height ≤ (Q.under R).height`, naming no prime of `R`:
that statement carries the whole content, and `solution` is it after substituting
`Ideal.LiesOver.over`, which says the given `𝔭` is `𝔮.under R`.

Three steps of it are absent from Mathlib and are proved here as private lemmas.
`Stacks.QuasiFinite.HeightBound.height_coe_Iic` is the general order-theoretic fact that
`Order.height` of a point of `Set.Iic a` agrees with its height in the ambient preorder, the lower
set of elements at most `a` containing every chain below such a point.
`Stacks.QuasiFinite.HeightBound.height_le_height_apply_of_strictMonoOn_Iic` is the consequence it
is needed for, namely `Order.height_le_height_apply_of_strictMono` with global strict monotonicity
weakened to strict monotonicity below the point in question — quasi-finiteness at `𝔮` says nothing
about primes that are not below `𝔮`, so the global form does not apply.
`Stacks.QuasiFinite.HeightBound.under_lt_under_of_lt` is strict monotonicity of `Ideal.under` at a
quasi-finite prime.

The source argues locally: for `R_𝔭` Noetherian the inequality is immediate from
`dim(S_𝔮) ≤ dim(R_𝔭) + dim(S_𝔮 / 𝔭 S_𝔮)` (Stacks 00OM), the fibre being finite over `κ(𝔭)` and
so of dimension `0`, and the general finite type case is reduced to it by passing to the integral
closure `S'` of `R_𝔭` in `S_𝔭`, where Zariski's Main Theorem (Stacks 00Q9) gives
`S_𝔮 = S'_{𝔮'}` and an integral extension does not raise dimension (Stacks 00OJ). That route
needs the source's finite type hypothesis, which the statement proved here does not carry, so it
cannot be run as transcribed; the chain argument above replaces it and uses no finiteness
hypothesis on `R → S` at all. Neither Zariski's Main Theorem nor Stacks 00OJ is used.

`Ideal.height` is used for `dim` of a local ring throughout: for any model `A` of `S_𝔮`, that is
any `A` with `[IsLocalization.AtPrime A 𝔮]`, one has `ringKrullDim A = 𝔮.height` by
`IsLocalization.AtPrime.ringKrullDim_eq_height`, so no localization has to be chosen.

## References

* [StacksProject 00QF](https://stacks.math.columbia.edu/tag/00QF)
-/

namespace Stacks.QuasiFinite.HeightBound

/-- The height of a point of `Set.Iic a` is its height in the ambient preorder: the lower set of
elements at most `a` contains every chain below such a point, so restricting to it loses no
chains. -/
private lemma height_coe_Iic {α : Type*} [Preorder α] {a : α} (x : Set.Iic a) :
    Order.height (x : α) = Order.height x :=
  (Order.height_eq_of_strictMono _ (Subtype.strictMono_coe _)
    (fun a' b hb => ⟨⟨b, hb.le.trans a'.2⟩, hb, rfl⟩) x).symm

/-- A map that is strictly monotone on `Set.Iic a` does not decrease the height of `a`: only
chains below `a` bound `Order.height a`, so `Order.height_le_height_apply_of_strictMono` needs
strict monotonicity nowhere else. -/
private lemma height_le_height_apply_of_strictMonoOn_Iic {α β : Type*} [Preorder α] [Preorder β]
    (f : α → β) {a : α} (hf : StrictMonoOn f (Set.Iic a)) :
    Order.height a ≤ Order.height (f a) :=
  (height_coe_Iic (⟨a, Set.self_mem_Iic⟩ : Set.Iic a)).trans_le
    (Order.height_le_height_apply_of_strictMono (fun x : Set.Iic a => f x)
      (fun x y h => hf x.2 y.2 h) _)

/-- Contraction of primes is strictly monotone below a prime `Q` at which `R → S` is quasi-finite:
it is monotone, and `P` is determined by `Q` once the two contractions agree, because the fibres
of a quasi-finite map are discrete. -/
private lemma under_lt_under_of_lt {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {P Q : Ideal S} [P.IsPrime] [Q.IsPrime] [Algebra.QuasiFiniteAt R Q] (h : P < Q) :
    Ideal.under R P < Ideal.under R Q :=
  lt_of_le_of_ne (Ideal.comap_mono h.le) fun he =>
    h.ne (Algebra.QuasiFiniteAt.eq_of_le_of_under_eq h.le he)

/-- The content of Stacks 00QF: a prime at which `R → S` is quasi-finite has height at most that
of its contraction to `R`. Contraction is strictly monotone on the primes at most `Q`, hence does
not decrease the height of `Q`. -/
private lemma height_le_height_under_of_quasiFiniteAt {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (Q : Ideal S) [Q.IsPrime] [Algebra.QuasiFiniteAt R Q] :
    Q.height ≤ (Q.under R).height := by
  have hmono : StrictMonoOn (PrimeSpectrum.comap (algebraMap R S))
      (Set.Iic (⟨Q, ‹Q.IsPrime›⟩ : PrimeSpectrum S)) := fun _ _ y hy h =>
    have : Algebra.QuasiFiniteAt R y.asIdeal := Algebra.QuasiFiniteAt.of_le (Q := Q) hy
    under_lt_under_of_lt h
  simpa [← PrimeSpectrum.height_eq_orderHeight] using
    height_le_height_apply_of_strictMonoOn_Iic _ hmono

/-- **Stacks 00QF.** Let `R → S` be a ring map, let `𝔮` be a prime of `S` lying over the prime
`𝔭` of `R`, and assume `R → S` is quasi-finite at `𝔮`. Then `dim(S_𝔮) = 𝔮.height` is at most
`dim(R_𝔭) = 𝔭.height`. The source's finite type hypothesis is not needed. -/
public theorem solution {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (𝔭 : Ideal R) (𝔮 : Ideal S) [𝔭.IsPrime] [𝔮.IsPrime]
    [𝔮.LiesOver 𝔭] [Algebra.QuasiFiniteAt R 𝔮] : 𝔮.height ≤ 𝔭.height := by
  obtain rfl : 𝔭 = 𝔮.under R := Ideal.LiesOver.over
  exact height_le_height_under_of_quasiFiniteAt 𝔮

end Stacks.QuasiFinite.HeightBound

/-!
# A quasi-finite map does not raise the dimension of the local ring

Let `R → S` be a ring map, let `𝔮` be a prime of `S` and let `𝔭 = R ∩ 𝔮` be the prime of `R` it
lies over. If `R → S` is quasi-finite at `𝔮`, then

`dim(S_𝔮) ≤ dim(R_𝔭)`.

For a finite type ring map and `R_𝔭` Noetherian this is immediate from
`dim(S_𝔮) ≤ dim(R_𝔭) + dim(S_𝔮/𝔭S_𝔮)` (00OM), the fibre `S_𝔮/𝔭S_𝔮` being finite over `κ(𝔭)` and
so of dimension `0`. The source treats the general finite type case by passing to the integral
closure `S'` of `R_𝔭` in `S_𝔭`: Zariski's Main Theorem (00Q9) gives `S_𝔮 = S'_{𝔮'}` for a prime
`𝔮'` of `S'` over `𝔮`, and an integral extension does not raise dimension (00OJ), so
`dim(S_𝔮) ≤ dim(S') ≤ dim(R_𝔭)`. Both of those routes use the finite type hypothesis, but the
inequality itself does not: quasi-finiteness at `𝔮` is inherited by every prime below `𝔮`
(`Algebra.QuasiFiniteAt.of_le`), and a quasi-finite prime is the only prime below itself with its
contraction (`Algebra.QuasiFiniteAt.eq_of_le_of_under_eq`), so contraction along `R → S` is
strictly monotone on the primes below `𝔮` and carries a chain below `𝔮` to a chain of the same
length below `𝔭`.

## Main results

* `Ideal.height_le_height_of_liesOver_of_quasiFiniteAt`: Stacks 00QF.

## Implementation notes

*`dim(S_𝔮)` is `𝔮.height`.* The Krull dimension of any model of the local ring of `S` at `𝔮` is
`𝔮.height`, by `IsLocalization.AtPrime.ringKrullDim_eq_height`, so the model-independent
`Ideal.height` says the source's `dim(S_𝔮)` with no localization data in the statement. For
abstract localizations `Rp` and `Sq` with `IsLocalization.AtPrime Rp 𝔭` and
`IsLocalization.AtPrime Sq 𝔮` the source's literal
`ringKrullDim Sq ≤ ringKrullDim Rp` in `WithBot ℕ∞` is that lemma twice together with
`WithBot.coe_le_coe`; no information is lost in either direction, the coercion `ℕ∞ → WithBot ℕ∞`
being an order embedding.

*Quasi-finiteness.* "`R → S` is quasi-finite at `𝔮`" (Definition 00PL: the equivalent conditions
of 00PK, in particular that `𝔮` is isolated in its fibre) is `Algebra.QuasiFiniteAt R 𝔮`. The a
priori weaker `Algebra.WeaklyQuasiFiniteAt`, equivalent to it here by
`Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt`, is not used: Mathlib documents it as an
implementation device for the proof of Zariski's Main Theorem.

*Finite type is not assumed.* The source's finite type hypothesis is what identifies
`Algebra.QuasiFiniteAt R 𝔮` with Definition 00PL: the bridge is
`Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`, which carries `[Algebra.FiniteType R S]`. The
inequality itself does not use it: all the proof needs is that contraction is injective on the
primes below `𝔮`, which is `Algebra.QuasiFiniteAt.eq_of_le_of_under_eq` together with
`Algebra.QuasiFiniteAt.of_le`, both stated with no finiteness hypothesis. So the tag is the case
`[Algebra.FiniteType R S]` of what is stated, and the extra reach is real: a fraction field of a
domain, and any localization, is quasi-finite without being of finite type.

*The prime `𝔭` is an argument.* It is given explicitly with `[𝔮.LiesOver 𝔭]`, the spelling of
"`𝔮` lies over `𝔭`" used by `Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField`, rather than
as `𝔮.under R`; the latter case is recovered by instance resolution.

Faithfulness to [StacksProject 00QF]:

1. No hypothesis is idle: `Algebra.QuasiFiniteAt R 𝔮` is the source's hypothesis on the map, and
   it cannot be dropped — for `k → k[x]` at `𝔮 = (x)` over `𝔭 = 0` the heights are `1` and `0`,
   and quasi-finiteness fails by `Polynomial.not_quasiFiniteAt`; `[𝔮.LiesOver 𝔭]` is what makes
   `𝔭` the source's `R ∩ 𝔮`, without which both sides are unrelated. The source's other
   hypothesis, finite type, is not stated because the conclusion does not use it; under it
   `Algebra.QuasiFiniteAt R 𝔮` is the source's Definition 00PL, by
   `Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`.
2. The scalars and base are the source's: the heights are those of `𝔮` in `S` and of `𝔭` in `R`
   for the given `R`-algebra structure, equal to the dimensions of the local rings `S_𝔮` and
   `R_𝔭`, and quasi-finiteness is over `R` itself, not over a localization or a quotient of it.
3. Nothing is left to exist: the two quantities compared are named functions of `𝔮` and `𝔭`, and
   the ring map is the `Algebra R S` structure, over which `𝔭` and `𝔮` are related by
   `Ideal.LiesOver`; no localization has to be chosen.
4. The instantiation is not degenerate: for `R = S = k[t]` and `𝔮 = 𝔭 = (t)` both sides are `1`,
   so the inequality is not the trivial `_ ≤ ⊤`; for `R = k[t] → S = k`, `t ↦ 0`, at `𝔮 = 0` over
   `𝔭 = (t)` it is strict, `0 ≤ 1`; and it has quasi-finite content, `ℤ → ℤ[x]/(x² - 2)` at a
   prime over `(2)` giving `1 ≤ 1`.

## References

* [StacksProject 00QF](https://stacks.math.columbia.edu/tag/00QF)
* [StacksProject 00PL](https://stacks.math.columbia.edu/tag/00PL)

## Tags

quasi-finite ring map, height, Krull dimension, local ring
-/

@[expose] public section

/-- **Stacks 00QF.** Let `R → S` be a ring map, let `𝔮` be a prime of `S` lying over the prime
`𝔭` of `R`, and assume `R → S` is quasi-finite at `𝔮`. Then `dim(S_𝔮) = 𝔮.height` is at most
`dim(R_𝔭) = 𝔭.height`. The source's finite type hypothesis is not needed. -/
@[stacks 00QF "`dim(S_𝔮)` and `dim(R_𝔭)` are `𝔮.height` and `𝔭.height`, model-independently by
`IsLocalization.AtPrime.ringKrullDim_eq_height`; quasi-finiteness at `𝔮` (Definition 00PL) is
`Algebra.QuasiFiniteAt R 𝔮`, which the source's finite type hypothesis identifies with the
source's notion by `Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`, and which the conclusion
needs without it. See the module docstring."]
public theorem Ideal.height_le_height_of_liesOver_of_quasiFiniteAt {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (𝔭 : Ideal R) (𝔮 : Ideal S) [𝔭.IsPrime] [𝔮.IsPrime]
    [𝔮.LiesOver 𝔭] [Algebra.QuasiFiniteAt R 𝔮] : 𝔮.height ≤ 𝔭.height :=
  Stacks.QuasiFinite.HeightBound.solution 𝔭 𝔮

end
