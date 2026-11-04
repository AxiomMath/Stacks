module

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
public import Mathlib.RingTheory.Smooth.Quotient
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
public import StacksFrontier.RingTheory.Flat.QuotientMap

@[expose] public section

universe u v

/-!
# Formal smoothness lifts along a nilpotent thickening of a flat algebra

Proof of `Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_isNilpotent_of_flat`: if `R → S` is
flat, `R → R'` and `S → S'` are compatible surjections with `ker (S → S') = (ker (R → R')) S`, the
ideal `I = ker (R → R')` is nilpotent and `R' → S'` is formally smooth, then `R → S` is formally
smooth.

The square-zero case `I ^ 2 = ⊥` is the source's own argument and is Mathlib's
`RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero`. What is proved here is the reduction
of a nilpotent `I` to that case, by induction on an exponent: for `I ^ (n + 3) = ⊥` the map
`R → R'` is factored through `R ⧸ J` with `J = I ^ (n + 2)`, an ideal that is square zero because
`2 (n + 2) ≥ n + 3`, while the residual kernel `ker (R ⧸ J → R')` is the image of `I`, whose
`(n + 2)`-nd power vanishes, so the inductive hypothesis applies to it. Both standing hypotheses
survive the reduction: `S ⧸ J S` is the base change `(R ⧸ J) ⊗[R] S` and is therefore flat over
`R ⧸ J`, and the two kernel ideals are the images of the old ones.

## Main results

* `Stacks.FormallySmooth.NilpotentThickening.solution`: the tagged statement.

## Implementation notes

The induction runs on ring homomorphisms rather than on algebra structures: the four algebra
instances and two scalar towers of the statement become one commuting square `qS ∘ f = g ∘ qR`,
which is the form Mathlib's `RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero` takes.
The intermediate ring `R ⧸ J` then needs no algebra structure over `R'` or `S'` — the two maps out
of it are `Ideal.Quotient.lift`s of the given surjections, and the map to `S ⧸ J S` is
`Ideal.quotientMap` — and the tagged statement is recovered from
`RingHom.formallySmooth_algebraMap` and `RingHom.flat_algebraMap_iff`.

The inductive statement is universally quantified over `R` and `S`, since the step replaces them by
quotients; those stay in their universes, so the two universe variables are fixed.

The exponent `n` of the statement is raised to `n + 2` before the induction starts, so the base
case is exactly Mathlib's square-zero lemma and the exponents `0` and `1` need no separate
treatment.

## References

* [StacksProject 031L](https://stacks.math.columbia.edu/tag/031L), Lemma 10.138.13
-/

@[expose] public section

namespace Stacks.FormallySmooth.NilpotentThickening



/-- A vanishing power of an ideal forces every larger power to vanish. -/
private theorem pow_eq_bot_of_le {R : Type*} [CommRing R] {I : Ideal R} {m n : ℕ} (hmn : m ≤ n)
    (hm : I ^ m = ⊥) : I ^ n = ⊥ :=
  le_bot_iff.mp ((Ideal.pow_le_pow_right hmn).trans hm.le)

/-- Formal smoothness descends along a square-zero quotient thickening: if `f : R →+* S` is flat,
`J : Ideal R` satisfies `J ^ 2 = ⊥` and `R ⧸ J → S ⧸ J S` is formally smooth, then so is `f`.
This is `RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero` for the two quotient maps,
whose kernels are `J` and `J S`. -/
private theorem formallySmooth_of_quotientMap_of_sq_eq_bot {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.Flat) (J : Ideal R) (sq0 : J ^ 2 = ⊥)
    (h : (Ideal.quotientMap (J.map f) f Ideal.le_comap_map).FormallySmooth) : f.FormallySmooth :=
  .of_flat_of_ker_eq_map_of_square_zero f hf _ _ _ Ideal.Quotient.mk_surjective
    Ideal.Quotient.mk_surjective (Ideal.quotientMap_comp_mk _).symm (by rwa [Ideal.mk_ker])
    (by rw [Ideal.mk_ker, Ideal.mk_ker]) h

/-- Formal smoothness lifts along a thickening of a flat ring map whose kernel `I` satisfies
`I ^ (n + 2) = ⊥`, by induction on `n`. The base case is the square-zero case; the step factors
`qR` through `R ⧸ I ^ (n + 2)`. -/
private theorem formallySmooth_of_ker_pow_eq_bot {R' S' : Type*} [CommRing R'] [CommRing S']
    {g : R' →+* S'} (hg : g.FormallySmooth) (n : ℕ) :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S} {qR : R →+* R'}
      {qS : S →+* S'}, f.Flat → Function.Surjective qR → Function.Surjective qS →
      qS.comp f = g.comp qR → RingHom.ker qS = (RingHom.ker qR).map f →
      RingHom.ker qR ^ (n + 2) = ⊥ → f.FormallySmooth := by
  induction n with
  | zero =>
    intro R S _ _ f qR qS hf hqR hqS comm eqmap sq0
    exact .of_flat_of_ker_eq_map_of_square_zero f hf qR qS g hqR hqS comm sq0 eqmap hg
  | succ n ih =>
    intro R S _ _ f qR qS hf hqR hqS comm eqmap hnil
    set J : Ideal R := RingHom.ker qR ^ (n + 2) with hJ
    have hJR : J ≤ RingHom.ker qR := Ideal.pow_le_self (by omega)
    have hJS : J.map f ≤ RingHom.ker qS := eqmap ▸ Ideal.map_mono hJR
    refine formallySmooth_of_quotientMap_of_sq_eq_bot hf J
      (by rw [hJ, ← pow_mul]; exact pow_eq_bot_of_le (by omega) hnil) ?_
    refine ih (RingHom.flat_quotientMap f hf J)
      (Ideal.Quotient.lift_surjective_of_surjective J hJR hqR)
      (Ideal.Quotient.lift_surjective_of_surjective _ hJS hqS) ?_ ?_ ?_
    · exact Ideal.Quotient.ringHom_ext (by ext x; exact RingHom.congr_fun comm x)
    · rw [Ideal.ker_quotient_lift, Ideal.ker_quotient_lift, Ideal.map_map,
        Ideal.quotientMap_comp_mk, ← Ideal.map_map, ← eqmap]
    · rw [Ideal.ker_quotient_lift, ← Ideal.map_pow, ← hJ, Ideal.map_quotient_self]

end Stacks.FormallySmooth.NilpotentThickening

end

/-!
# Formal smoothness lifts along a nilpotent thickening of a flat algebra

Let `R → S` be a flat ring map, let `R → R'` and `S → S'` be surjections of rings compatible with
it, and assume `ker (S → S') = (ker (R → R')) S` and that `I = ker (R → R')` is nilpotent. If
`R' → S'` is formally smooth, then so is `R → S`.

Two special cases are worth naming. Taking `R' = R/I` and `S' = S/IS` with `I² = 0` gives the
statement of the source, Stacks 031L; taking arbitrary surjections but keeping `I² = 0` gives
Mathlib's `Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat`.

The square-zero case is the source's argument. Choose a polynomial presentation
`0 → J → P → S → 0` with `P = R[{x_t}]`. Flatness of `S` makes this a short exact sequence of
flat `R`-modules, so tensoring with `I` stays exact: `I ⊗_R S = IS`, `I ⊗_R P = IP`,
`I ⊗_R J = IJ`, and hence `J ∩ IP = IJ`. Since `Ω_{S'/R'} = Ω_{S/R}/IΩ_{S/R}` (Stacks 00RV),
formal smoothness of `R' → S'` says exactly that the naive cotangent sequence
`0 → J/(IJ + J²) → Ω_{P/R} ⊗_P S' → Ω_{S/R} ⊗_S S' → 0` is split (Stacks 031I). Lifting a
splitting `σ` of it to an `S`-module map `σ̃ : Ω_{P/R} ⊗_P S → J/J²`, the discrepancy
`Δ = id - σ̃ ∘ d` on `J/J²` has image inside `(IJ + J²)/J²` and kills that submodule *because*
`I² = 0`; so `Δ` factors through the split sequence again and can be absorbed, producing a
splitting over `R` itself.

A nilpotent `I` reduces to that case by induction on the nilpotency degree `n`: factor `R → R'`
through `R/I^{n-1}`. The first step has square-zero kernel `I^{n-1}` (as `2n - 2 ≥ n` for
`n ≥ 2`), the second has kernel of nilpotency degree `n - 1`, and both hypotheses survive the
reduction, since `S/I^{n-1}S = S ⊗_R R/I^{n-1}` is flat over `R/I^{n-1}` and the two kernel
ideals are the images of the old ones.

## Main results

* `Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_isNilpotent_of_flat`: formal smoothness
  descends from `R' → S'` to a flat `R → S` along a nilpotent thickening.

## Implementation notes

Mathlib already carries the tag `031L`, on the square-zero case
`Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat`, so the tag here is carried jointly:
what is added is the weakening of `ker (algebraMap R R') ^ 2 = ⊥` to
`IsNilpotent (ker (algebraMap R R'))`, which is what a nilpotent thickening of a flat algebra
needs at one application rather than `n` of them.

The surjections are left arbitrary rather than specialized to `R/I` and `S/IS`, following the
Mathlib sibling. Nothing is lost: the source's form is recovered from
`Ideal.Quotient.mk_surjective` and `Ideal.mk_ker`, with the four algebra structures and two
scalar towers relating `R`, `S`, `R/I`, `S/IS` all synthesized
(`Ideal.Quotient.algebraQuotientMapQuotient` and `Ideal.Quotient.tower_quotient_map_quotient`).
Conversely the quotient form is strictly weaker at the call sites: Stacks 0329 applies this lemma
with `R = ℤ/pⁿ⁺¹ℤ`, `R' = ℤ/pⁿℤ` and `S' = Λ/pⁿΛ`, where `R'` is not a quotient type and the
induction hypothesis is used verbatim only in the surjection form.

Both remaining hypotheses are used. Without nilpotence, `R' = S' = 0` satisfies everything else
and would make every flat algebra formally smooth, false for `𝐅_p(t) → 𝐅_p(t^{1/p})`. Without
flatness, `R = k[x]/(x²)`, `S = R/(x) = k`, `R' = S' = k` satisfies every other hypothesis, and
`R → k` is not formally smooth: an `R`-algebra section `σ` of it would give
`x = x • σ 1 = σ (x • 1) = 0` in `R`.

## References

* [StacksProject 031L](https://stacks.math.columbia.edu/tag/031L), Lemma 10.138.13
* [StacksProject 031I](https://stacks.math.columbia.edu/tag/031I)
* [StacksProject 00RV](https://stacks.math.columbia.edu/tag/00RV)
* [StacksProject 0329](https://stacks.math.columbia.edu/tag/0329)
-/

@[expose] public section

/-- Let `R → S` be a flat ring map, let `R → R'` and `S → S'` be surjections with
`ker (S → S') = (ker (R → R')) S`, and assume `I = ker (R → R')` is nilpotent. If `R' → S'` is
formally smooth, then `R → S` is formally smooth (Stacks 031L, for `I² = 0` and the quotients
`R' = R/I`, `S' = S/IS`). -/
public theorem Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_isNilpotent_of_flat
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S]
    [Algebra R R'] [Algebra R' S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsScalarTower R R' S'] [Module.Flat R S] (surj : Function.Surjective (algebraMap R R'))
    (surjS : Function.Surjective (algebraMap S S'))
    (eqmap : RingHom.ker (algebraMap S S') = (RingHom.ker (algebraMap R R')).map (algebraMap R S))
    (nil : IsNilpotent (RingHom.ker (algebraMap R R')))
    (smoothq : Algebra.FormallySmooth R' S') : Algebra.FormallySmooth R S := by
  obtain ⟨n, hn⟩ := nil
  rw [← RingHom.formallySmooth_algebraMap]
  exact Stacks.FormallySmooth.NilpotentThickening.formallySmooth_of_ker_pow_eq_bot
    (RingHom.formallySmooth_algebraMap.mpr smoothq) n
    (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat R S›) surj surjS
    ((IsScalarTower.algebraMap_eq R S S').symm.trans (IsScalarTower.algebraMap_eq R R' S'))
    eqmap (Stacks.FormallySmooth.NilpotentThickening.pow_eq_bot_of_le (by omega) hn)

namespace Stacks.FormallySmooth.NilpotentThickening

/-- Formal smoothness lifts along a nilpotent thickening of a flat algebra: if `R → S` is flat,
`R → R'` and `S → S'` are compatible surjections with `ker (S → S') = (ker (R → R')) S`, the
kernel `ker (R → R')` is nilpotent and `R' → S'` is formally smooth, then `R → S` is formally
smooth. -/
public alias solution := Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_isNilpotent_of_flat

end Stacks.FormallySmooth.NilpotentThickening

end
