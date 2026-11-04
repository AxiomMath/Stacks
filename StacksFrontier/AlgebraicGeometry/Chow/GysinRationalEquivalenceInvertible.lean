module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.InvertibleChernSpecialization

/-!
# The Gysin homomorphism of an invertible module on Chow groups

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `L` be an invertible `𝒪_X`-module and let `s ∈ Γ(X, L)` be a global section with zero
scheme `i : D = Z(s) ⟶ X`. Stacks 02T8 gives the Gysin map on cycles

  `i^* : Z_{k+1}(X) ⟶ A_k(D)`,

available as `Stacks.Chow.gysinHomomorphismOfInvertible`, and Stacks 02TO asserts that it kills
cycles rationally equivalent to zero, so that it descends to

  `i^* : A_{k+1}(X) ⟶ A_k(D)`.

`StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalence` carries out that descent for the
Gysin map of an arbitrary `Stacks.Chow.FirstChernComponentClassRule`, which is the form the Gysin
construction was written in while Stacks 02SO was unavailable. This file restates it for the first
Chern class component rule of `L` itself, so that every statement of Stacks 02TO is a statement
about `L` and `s` alone, with no component rule in sight.

That matters for the consumers. A statement threading an arbitrary `chern` is a statement about an
arbitrary rule on integral components, and (see the implementation notes) the vanishing
of Stacks 02TO is *false* for such a rule. Threading the rule therefore changes what a dependent
result says; threading only the vanishing hypothesis does not.

## Main definitions

* `Stacks.Chow.GysinOfInvertibleFactorsThroughRationalEquivalence` — **the statement of Stacks
  02TO**: the Gysin map of the zero scheme of `s` kills every `(k+1)`-cycle rationally equivalent
  to zero.
* `Stacks.Chow.gysinHomomorphismOnChowOfInvertible` — the Gysin homomorphism of `L` and `s`
  descended to Chow groups.
* `Stacks.Chow.effectiveCartierIntersectionOnChowOfInvertible` — intersection with an effective
  Cartier zero scheme, as an operation `A_{k+1}(X) ⟶ A_k(X)` on Chow groups.

## Main results

* `Stacks.Chow.gysinHomomorphismOnChowOfInvertible_mk` — the descended map agrees with the Gysin
  homomorphism on cycle representatives.
* `Stacks.Chow.eq_gysinHomomorphismOnChowOfInvertible` — it is the unique such homomorphism.
* `Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence_iff_exists` — the vanishing is
  *equivalent* to the existence of a descended homomorphism, so carrying it as a hypothesis loses
  nothing.
* `Stacks.Chow.gysinHomomorphismOnChowOfInvertible_mk_cycleAssociatedToClosedSubscheme` and
  `Stacks.Chow.gysinHomomorphismOnChowOfInvertible_mk_of_le` — the two integral-component rules of
  Stacks 02T8, read on Chow classes.
* `Stacks.Chow.gysinHomomorphismOnChowOfInvertible_finsum` — the locally finite component formula,
  read on Chow classes.

## Implementation notes

### What is new here and what is not

Every statement below is the corresponding declaration of
`StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalence` or of
`StacksFrontier.AlgebraicGeometry.Chow.InvertibleChernSpecialization` applied to
`Stacks.Chow.firstChernComponentClass C p k L`, the first Chern class component rule of `L`
supplied by `StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule`. No new mathematics is
proved. What is new is that the `chern` parameter is gone, so these are the statements of Stacks
02TO rather than statements about an arbitrary rule.

### Why the vanishing is still a hypothesis

The vanishing itself is **not** proved, and this is a genuine gap rather than a matter of effort.
The proof of Stacks 02TO pushes forward along `⨿ W_j ⟶ X` to reduce to a single integral `X` with
`α = div(f)`, and then evaluates. It consumes

* Stacks 02TA, that the Gysin map commutes with proper pushforward. Available here only as
  `Stacks.Chow.gysinHomomorphism_properPushforward`, which carries
  `Stacks.Chow.GysinCompatibleWithPushforward` as a hypothesis — the integral-component case, which
  the source gets from Stacks 02ST. Stacks 02ST is not in this repository, but its two inputs now
  are: Stacks 02RT is `Stacks.Chow.properPushforward_principalDivisorCycle` and Stacks 02SO is the
  cap product used here, so this is the one input of Stacks 02TO that is no longer blocked
  upstream;
* Stacks 02S2, for which only the closed-immersion case
  `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion` is proved;
* Stacks 02TM, that `i^* div_N(t) = c₁(N|_D) ∩ [D]_{n-1}`, which rests on the key formula of
  Stacks 0AYC. That formula is recorded as `Stacks.Chow.KeyFormulaData.KeyFormula` and is likewise
  unproved; granting it, the identity is available only after pushforward along `i`, as
  `Stacks.Chow.effectiveCartierIntersection_eq_firstChernClassCap_of_keyFormula`, which is too
  weak here because `i_*` is not injective on Chow groups;
* Stacks 02TI, the same vanishing for the cap product of Stacks 02SO, available only as the
  hypothesis `Stacks.Chow.FirstChernClassCapFactorsThroughRationalEquivalence`.

So the hypothesis is carried, as `Stacks.Chow.GysinOfInvertibleFactorsThroughRationalEquivalence`,
and `Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence_iff_exists` shows that carrying
it loses nothing: it is equivalent to the existence of the descended homomorphism, which is the
content of Stacks 02TO, and `Stacks.Chow.eq_gysinHomomorphismOnChowOfInvertible` shows that
homomorphism is unique.

### The hypothesis is weaker than its chern-parametric ancestor, not a relabelling

`Stacks.Chow.GysinFactorsThroughRationalEquivalence` is stated for an arbitrary component rule, and
for an arbitrary rule it is **false**: taking `s = 0` makes `D = X`, so every integral component is
contained in the zero scheme and the Gysin map is whatever the rule says on components, with no
reason to kill `div(f)`. Instantiating at `Stacks.Chow.firstChernComponentClass C p k L` removes
that counterexample — the resulting statement is the genuine assertion of Stacks 02TO — which is
why the restatement below is worth having and not a rename.

### Stacks 02S2 is discharged, not assumed

`Stacks.Chow.properChowPushforward` carries the vanishing of Stacks 02S2 as an explicit hypothesis.
Every morphism pushed along below is a closed immersion — the inclusion of an integral closed
subscheme into the zero scheme, and the closed immersion of the zero scheme into `X` — for which
Stacks 02S2 is proved outright as
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion`. So the
hypothesis is supplied inside each statement and no binder is added.

### No Stacks attribute

No declaration here carries a Stacks attribute. The covering set of Stacks 02TO is the vanishing
statement together with the descended map and its formula on representatives, and the vanishing is
a hypothesis here rather than a theorem, so the tag is not covered.

## References

* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-! ### The statement of Stacks 02TO -/

/-- **Stacks 02TO.** The Gysin homomorphism of the zero scheme of a global section `s` of an
invertible module `L` kills every `(k+1)`-cycle rationally equivalent to zero, hence factors
through rational equivalence.

Carried as a hypothesis; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalenceInvertible`. -/
abbrev GysinOfInvertibleFactorsThroughRationalEquivalence : Prop :=
  ∀ α ∈ rationalEquivalences C p (k + 1), gysinHomomorphismOfInvertible C p k L s α = 0

/-- The statement of Stacks 02TO is the chern-parametric
`Stacks.Chow.GysinFactorsThroughRationalEquivalence` at the first Chern class component rule of
`L`. -/
theorem gysinOfInvertibleFactorsThroughRationalEquivalence_iff :
    GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s ↔
      GysinFactorsThroughRationalEquivalence C p k L s (firstChernComponentClass C p k L) :=
  Iff.rfl

/-! ### The descended Gysin homomorphism -/

/-- **Stacks 02TO.** The Gysin homomorphism of an invertible module descended to Chow groups,
`i^* : A_{k+1}(X) ⟶ A_k(D)`, granted that it factors through rational equivalence. -/
def gysinHomomorphismOnChowOfInvertible
    (h : GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s) :
    chowGroup C p (k + 1) →+
      chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k :=
  gysinHomomorphismOnChow C p k L s (firstChernComponentClass C p k L) h

/-- **Stacks 02TO.** The descended Gysin map agrees with the Gysin homomorphism on cycle
representatives. -/
@[simp]
theorem gysinHomomorphismOnChowOfInvertible_mk
    (h : GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s)
    (α : CycleGroup C p (k + 1)) :
    gysinHomomorphismOnChowOfInvertible C p k L s h
        (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) α) =
      gysinHomomorphismOfInvertible C p k L s α :=
  rfl

/-- The descended Gysin map, composed with the projection to the Chow group of `X`, is the Gysin
homomorphism on cycles. -/
theorem gysinHomomorphismOnChowOfInvertible_comp_mk'
    (h : GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s) :
    (gysinHomomorphismOnChowOfInvertible C p k L s h).comp
        (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))) =
      gysinHomomorphismOfInvertible C p k L s :=
  rfl

/-- **Stacks 02TO.** The descended Gysin map is the only homomorphism of Chow groups agreeing with
the Gysin homomorphism on cycle representatives. -/
theorem eq_gysinHomomorphismOnChowOfInvertible
    (h : GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s)
    (F : chowGroup C p (k + 1) →+
      chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k)
    (hF : F.comp (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))) =
      gysinHomomorphismOfInvertible C p k L s) :
    F = gysinHomomorphismOnChowOfInvertible C p k L s h :=
  eq_gysinHomomorphismOnChow C p k L s (firstChernComponentClass C p k L) h F hF

/-- **The hypothesis is exactly the descent.** The Gysin homomorphism of an invertible module
factors through rational equivalence precisely when it descends to a homomorphism of Chow groups.
So carrying the vanishing of Stacks 02TO as a hypothesis loses nothing: the hypothesis *is* the
existence of the descended map, and `Stacks.Chow.eq_gysinHomomorphismOnChowOfInvertible` says that
map is unique. -/
theorem gysinOfInvertibleFactorsThroughRationalEquivalence_iff_exists :
    GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s ↔
      ∃ F : chowGroup C p (k + 1) →+
          chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k,
        F.comp (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))) =
          gysinHomomorphismOfInvertible C p k L s :=
  IntegralComponentRule.factorsThroughRationalEquivalence_iff
    (gysinRule C p k L s (firstChernComponentClass C p k L))

/-! ### The two integral-component rules on Chow classes -/

/-- **Stacks 02T8, 02TO.** The descended Gysin map sends the class of an integral closed subscheme
`W ⊆ X` of delta-dimension `k + 1` *not* contained in the zero scheme to the class of the
fundamental cycle of the scheme-theoretic intersection `W ∩ D`. -/
theorem gysinHomomorphismOnChowOfInvertible_mk_cycleAssociatedToClosedSubscheme
    (h : GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s) (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hle : ¬ Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinHomomorphismOnChowOfInvertible C p k L s h
        (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))
          (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1))) =
      QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
          ((W.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι) k) :=
  gysinHomomorphismOnChow_mk_cycleAssociatedToClosedSubscheme C p k L s
    (firstChernComponentClass C p k L) h W hW hDim hle

/-- **Stacks 02T8, 02TO.** The descended Gysin map sends the class of an integral closed subscheme
`W ⊆ X` of delta-dimension `k + 1` contained in the zero scheme to the proper Chow pushforward into
that zero scheme of the first Chern class of `L|_W`.

The instance of Stacks 02S2 that `Stacks.Chow.properChowPushforward` requires is discharged, the
inclusion of `W` into the zero scheme being a closed immersion. -/
theorem gysinHomomorphismOnChowOfInvertible_mk_of_le
    (h : GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s) (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hle : Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinHomomorphismOnChowOfInvertible C p k L s h
        (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))
          (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1))) =
      properChowPushforward C (W.subschemeι ≫ p)
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        (Scheme.IdealSheafData.inclusion hle) (by simp) k
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Scheme.IdealSheafData.inclusion hle) C (W.subschemeι ≫ p)
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (by simp) k)
        (firstChernComponentClass C p k L W hW hDim) :=
  gysinHomomorphismOfInvertible_of_le C p k L s W hW hDim hle

/-- **Stacks 02T8, 02TO.** The locally finite component formula for the descended Gysin map: on the
class of a cycle presented as `α = ∑ n_j [W_j]` by a locally finite family of integral closed
subschemes of delta-dimension `k + 1`, its value is the class of the cycle whose coefficients are
`∑ n_j` times the Gysin component cycles of the `W_j`. -/
theorem gysinHomomorphismOnChowOfInvertible_finsum
    (h : GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s) {J : Type u}
    (W : J → X.IdealSheafData) (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X)) (n : J → ℤ)
    (α : CycleGroup C p (k + 1))
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) :
    ∃ β : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k,
      gysinHomomorphismOnChowOfInvertible C p k L s h
          (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) α) =
        QuotientAddGroup.mk β ∧
      ∀ x : (Stacks.Divisors.zeroScheme X L s).subscheme,
        β.1 x = ∑ᶠ j : J, n j *
          (gysinComponentCycle C p k L s (firstChernComponentClass C p k L)
            (W j) (hW j) (hDim j)).1 x :=
  gysinHomomorphismOnChow_finsum C p k L s (firstChernComponentClass C p k L) h W hW hDim hLocal n
    α hα

/-! ### Intersection with an effective Cartier zero scheme, on Chow groups -/

/-- Intersection with the zero scheme of `s`, when that zero scheme is an effective Cartier
divisor, as an operation `A_{k+1}(X) ⟶ A_k(X)` on Chow groups: the descended Gysin map followed by
proper Chow pushforward along the closed immersion of the zero scheme into `X`.

The instance of Stacks 02S2 that `Stacks.Chow.properChowPushforward` requires is discharged, the
zero scheme being a closed subscheme of `X`. The hypothesis `hD` plays no role in the construction
and is carried to match `Stacks.Chow.effectiveCartierIntersectionOfInvertible`, of which this is
the descent. -/
def effectiveCartierIntersectionOnChowOfInvertible
    (h : GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s)
    (_hD : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme X L s)) :
    chowGroup C p (k + 1) →+ chowGroup C p k :=
  (properChowPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
    (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
    (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
      (Stacks.Divisors.zeroScheme X L s).subschemeι C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p rfl k)).comp
    (gysinHomomorphismOnChowOfInvertible C p k L s h)

/-- On the class of a cycle, intersection with an effective Cartier zero scheme on Chow groups is
`Stacks.Chow.effectiveCartierIntersectionOfInvertible` of that cycle. -/
@[simp]
theorem effectiveCartierIntersectionOnChowOfInvertible_mk
    (h : GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme X L s))
    (α : CycleGroup C p (k + 1)) :
    effectiveCartierIntersectionOnChowOfInvertible C p k L s h hD
        (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) α) =
      effectiveCartierIntersectionOfInvertible C p k L s hD α :=
  rfl

end Stacks.Chow

end
