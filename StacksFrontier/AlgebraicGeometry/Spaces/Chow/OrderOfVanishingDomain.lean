module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishing
public import StacksFrontier.RingTheory.Lattice.Defs

/-!
# The two order-of-vanishing functions agree on a domain

This repository carries two integer-valued orders of vanishing of Stacks 02MD, and they are
used by two different chapters:

* `ordInt`, defined on the *fraction field* of a Noetherian domain of Krull dimension at most
  one. This is the one the ring-theoretic development and the scheme-side Chow chapter use; in
  particular Stacks 02MJ, `ord_norm_eq_sum_inertiaDeg_mul_ord` of
  `StacksFrontier.RingTheory.OrderOfVanishing.Norm`, and Stacks 02RT,
  `Stacks.Chow.properPushforward_principalDivisorCycle`, are stated with it.
* `Ring.ordTotalFracInt`, defined on the *total ring of fractions* of a Noetherian ring of Krull
  dimension at most one, with no domain hypothesis. This is the one the algebraic-spaces Chow
  chapter uses, through `AlgebraicGeometry.Space.PrimeDivisor.ord`, because the henselian local
  ring `𝒪^h_{X,ξ}` at the generic point of a prime divisor is reduced but need not be a domain.

The content of this file is that the two are **the same function** wherever both are defined:
both are the extension of `Ring.ordMonoidWithZeroHom` along the localization map at the
nonzerodivisors, and `Ring.ordTotalFrac` and `Ring.ordFrac` are literally the same lift, so on a
domain with its field of fractions the two integer values coincide.

## Main results

* `Ring.ordTotalFracInt_eq_ordInt`: on a Noetherian domain of Krull dimension at most one, with
  its field of fractions, `Ring.ordTotalFracInt` and `ordInt` agree.
* `Ring.ordTotalFracInt_eq_sum_of_ordInt_eq_sum`: a sum identity in the `ordInt` vocabulary
  transports termwise into the `Ring.ordTotalFracInt` vocabulary. This is the shape of Stacks
  02MJ, so that lemma is available in the total-ring-of-fractions vocabulary as soon as the
  rings in it are known to be domains.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_ordInt`: the order of vanishing along a prime
  divisor of an algebraic space is `ordInt` at the henselian local ring at its generic point,
  when that ring is a domain.

## Implementation notes

### What this unblocks, and what it does not

Stacks 0EQ4, `p_* div(f) = div(Nm_{R(X)/R(Y)}(f))`, and with it Stacks 0EQS, rest in this
repository on two independent missing inputs. This file removes one half of the first of them
and leaves the other untouched; the statements below are therefore a reduction, not a proof of
either tag, and no tag is attached to them.

**First input, now reduced to a domain hypothesis.** Stacks 02MJ, the multiplicativity
`ord_A(Nm_{L/K}(y)) = ∑_𝔮 [κ(𝔮) : κ(𝔪_A)] · ord_{B_𝔮}(y)`, is proved — with `[IsDomain A]`,
`[IsDomain B]`, a field of fractions, and `ordInt`. A priori it is not clear that it says anything
about `AlgebraicGeometry.Space.PrimeDivisor.ord`, which is `Ring.ordTotalFracInt` on a total ring of
fractions; the two might be different functions on different inputs.
`Ring.ordTotalFracInt_eq_ordInt` settles that: they are one function, so the whole of Stacks
02MJ transports, termwise by `Ring.ordTotalFracInt_eq_sum_of_ordInt_eq_sum`, and what remains of
this input is exactly the hypothesis that the rings involved are domains — on the geometric side,
that `𝒪^h_{Y,ξ'}` and the henselian local rings above it are domains. That hypothesis is a real
restriction and not derivable here: the henselization of a local domain need not be a domain,
which is why no module of this chapter assumes one.

**Second input, untouched.** There is no geometric presentation to apply Stacks 02MJ to. The
morphism `c_ξ : Spec(𝒪^h_{X,ξ}) ⟶ X` is not constructed in this repository, but the induced
homomorphism `𝒪^h_{Y,ξ'} ⟶ 𝒪^h_{X,ξ}` does not depend on it and is available: it is
`AlgebraicGeometry.Space.exists_henselianLocalRingHom`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/HenselianLocalRingMap.lean:234`), obtained from a
commuting square of charts and flat when the morphism is flat, with
`AlgebraicGeometry.Space.PrimeDivisor.exists_genericHenselianLocalRingHom` (line 252 of that
file) the version at the generic points of prime divisors.
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOrderOfVanishing` carries that
homomorphism as an explicit parameter so as not to presuppose where it comes from, not for want
of one.

What is absent is the *finite-algebra* presentation: Stacks 02MJ is applied to a finite algebra
over `𝒪^h_{Y,ξ'}` whose maximal ideals correspond to the prime divisors of `X` over a prime
divisor of `Y`, with the residue degrees of that correspondence as the coefficients of the sum.
The chart-level ingredients of the correspondence are available, in
`StacksFrontier/AlgebraicGeometry/Spaces/ElementaryChartFibre.lean`:
`AlgebraicGeometry.Space.bijOn_chartSchemeToPoints_fibre` (line 364) is a bijection from the
fibre of the chart morphism `r : U ⟶ V` over a point `e` of `V` onto the fibre of `|g|` over the
point of `|Y|` beneath it, and
`AlgebraicGeometry.Space.primeResidueDegree_chartPrime_eq_finrank` (line 391) identifies, for
affine charts, the residue degree of the prime of `Γ(U)` at such a point over the prime of
`Γ(V)` at `e` with the degree `[κ(z) : κ(g z)]` of the residue fields of the spaces. What they
do not supply is finiteness of `Γ(U)` over `Γ(V)`, nor the passage from points of a chart over a
point to the maximal ideals of a finite algebra over the henselian local ring. Nothing below
supplies that, and nothing below should be read as supplying it.

The source's own proof of Stacks 0EQ4 does not go through Stacks 02MJ directly in any case: it
localizes `Y`, passes to an affine étale neighbourhood of the generic point of the prime divisor,
invokes the *scheme* case Stacks 02RT on the components upstairs, and finishes with a
compatibility of norms along `M ⊗_K L = ∏ M_i` whose proof the source omits. So the route this
file shortens is the direct one, not the source's.

### Why the comparison is definitional

`Ring.ordTotalFrac` of `StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishing` and `Ring.ordFrac`
of Mathlib are the same term: both are
`(IsLocalization.toLocalizationMap (nonZeroDivisors R) K).lift₀ (Ring.ordMonoidWithZeroHom R)`
at the same unitality proof. `Ring.ordTotalFracInt` and `ordInt` then apply the same
`Multiplicative.toAdd ∘ WithZero.unzero` to it, differing only in the proof that the value is
nonzero — `IsUnit x` on one side, `x ≠ 0` on the other — and those are propositions. So the
comparison holds by `rfl`, and no lemma about lengths is needed.

## References

* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 02MJ](https://stacks.math.columbia.edu/tag/02MJ)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Ring

/-- **The two orders of vanishing of Stacks 02MD agree on a domain.** On a Noetherian domain `R`
of Krull dimension at most one, with its field of fractions `K`, the order of vanishing
`Ring.ordTotalFracInt` taken on the total ring of fractions is the order of vanishing `ordInt`
taken on the fraction field.

Both are `Multiplicative.toAdd ∘ WithZero.unzero` applied to the same extension of
`Ring.ordMonoidWithZeroHom` along the localization map at the nonzerodivisors, so this is
`rfl`. -/
theorem ordTotalFracInt_eq_ordInt (R : Type*) [CommRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [IsDomain R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] (x : K) (hx : IsUnit x) (hx0 : x ≠ 0) :
    ordTotalFracInt R x hx = ordInt R x hx0 :=
  rfl

/-- **A sum identity transports from the `ordInt` vocabulary to the
`Ring.ordTotalFracInt` vocabulary.** If the order of vanishing of `x` along a Noetherian domain
`A` of Krull dimension at most one is a `deg`-weighted sum of the orders of vanishing of `y`
along a finite family of such domains, then the same holds for the orders of vanishing taken on
the total rings of fractions.

This is the shape of Stacks 02MJ, with `A` the base, the family indexed by the maximal ideals of
the finite extension and `deg` the inertia degrees. So Stacks 02MJ,
`ord_norm_eq_sum_inertiaDeg_mul_ord` of `StacksFrontier.RingTheory.OrderOfVanishing.Norm`, is
available in the vocabulary of `AlgebraicGeometry.Space.PrimeDivisor.ord` as soon as the rings
occurring in it are known to be domains. -/
theorem ordTotalFracInt_eq_sum_of_ordInt_eq_sum {ι : Type*} [Fintype ι]
    (A : Type*) [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (C : ι → Type*) [∀ i, CommRing (C i)] [∀ i, IsNoetherianRing (C i)]
    [∀ i, Ring.KrullDimLE 1 (C i)] [∀ i, IsDomain (C i)]
    {L : Type*} [Field L] [∀ i, Algebra (C i) L] [∀ i, IsFractionRing (C i) L]
    (deg : ι → ℤ) (x : K) (hx : IsUnit x) (hx0 : x ≠ 0)
    (y : L) (hy : IsUnit y) (hy0 : y ≠ 0)
    (h : ordInt A x hx0 = ∑ i : ι, deg i * ordInt (C i) y hy0) :
    ordTotalFracInt A x hx = ∑ i : ι, deg i * ordTotalFracInt (C i) y hy := by
  rw [ordTotalFracInt_eq_ordInt A x hx hx0, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ordTotalFracInt_eq_ordInt (C i) y hy hy0]

end Ring

namespace AlgebraicGeometry.Space

/-- **The order of vanishing along a prime divisor is `ordInt` when the henselian local ring is a
domain.** For a prime divisor `Z` of an algebraic space `X` whose henselian local ring
`𝒪^h_{X,ξ}` at the generic point is a Noetherian domain of Krull dimension at most one, the order
of vanishing `AlgebraicGeometry.Space.PrimeDivisor.ord` of Stacks 0ENL is `ordInt` at that ring.

This is the geometric reading of `Ring.ordTotalFracInt_eq_ordInt`, and it is what makes the
ring-theoretic results stated with `ordInt` — Stacks 02MJ among them — say something
about this chapter's order of vanishing. The hypothesis `IsDomain` is the whole of the remaining
gap on that side: no module of this chapter assumes it, the henselization of a local domain not
being a domain in general. -/
theorem PrimeDivisor.ord_eq_ordInt (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    [IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [IsDomain ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    (f : Z.genericTotalFractionRing B S hS hX hdec) (hf : IsUnit f) (hf0 : f ≠ 0) :
    Z.ord B S hS hX hdec f hf =
      ordInt ↥(Z.genericHenselianLocalRing B S hS hX hdec) f hf0 :=
  Ring.ordTotalFracInt_eq_ordInt _ f hf hf0

end AlgebraicGeometry.Space

end
