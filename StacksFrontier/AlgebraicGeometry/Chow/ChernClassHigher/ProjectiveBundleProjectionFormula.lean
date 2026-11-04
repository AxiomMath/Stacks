module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension

/-!
# Pushing the hyperplane powers of a projective bundle forward to the base

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `ℰ` be a finite locally free `O_X`-module of rank `r` and let
`(π : P ⟶ X, O_P(1))` be the projective bundle of `ℰ`. Stacks 02TW says that for a class
`α ∈ CH_k(X)` the pushforward

  `π_*(c₁(O_P(1))^s ∩ π^*α) ∈ CH_{k+r-1-s}(X)`

is `0` for `s < r - 1` and is `α` itself for `s = r - 1`.

This file proves the vanishing half, for an arbitrary first Chern class cap operator on the
bundle and hence in particular for `c₁(O_P(1))`. The proof is the dimension count the source
makes: a representative of `c₁^s ∩ π^*α` may be taken supported over the support of a
representative of `α`, so it has delta-dimension `k + r - 1 - s` while its image in `X` has
delta-dimension at most `k`; the two differ when `s < r - 1`, and proper pushforward of cycles
weights a point of the source by zero unless its delta-dimension agrees with that of its image.

## Main definitions

* `Stacks.Chow.invertibleChernCapOperator` — the first Chern class cap operator of an invertible
  module, with the factoring of Stacks 02TI as a parameter; its component rule of Stacks 02SO is
  *constructed*.
* `Stacks.Chow.invertibleChernCap` — the same operator with no hypothesis at all, the factoring
  supplied by Stacks 02TI
  (`Stacks.Chow.firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule`).
* `Stacks.Chow.projectiveBundleProjection` — the operation
  `π_*(c₁(O_P(1))^s ∩ π^*(-)) : CH_k(X) ⟶ CH_{k+r-1-s}(X)`, built from the flat pullback of
  Stacks 0FVK along `π`, the iterated first Chern class cap of Stacks 02TI and the proper
  pushforward of Stacks 0GU8.

## Main results

* `Stacks.Chow.exists_cycle_iteratedChernCapOnChow_of_fibreDimension` — an iterated first Chern
  class cap has a cycle representative supported over the support of any chosen representative
  of its argument. This is the engine, and it is stated for an arbitrary list of first Chern
  class cap operators.
* `Stacks.Chow.properChowPushforward_iteratedChernCapOnChow_flatPullbackChow_eq_zero` — the
  dimension count itself, with the two degrees as parameters.
* `Stacks.Chow.projectiveBundleProjection_eq_zero_of_lt` — the vanishing for an arbitrary first
  Chern class cap operator on the bundle.
* `Stacks.Chow.projectiveBundleFlatPullbackFactors` — Stacks 02S1 for `π`, read off the general
  case `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`.
* `Stacks.Chow.projectiveBundleProjection_twist_eq_zero_of_lt` — **Stacks 02TW, vanishing
  below the fibre dimension**: `π_*(c₁(L)^s ∩ π^*α) = 0` for `s < r - 1`, for `L` the twist
  `O_P(1)`, with no hypothesis.
* `Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_section` and its Chow-group
  form `Stacks.Chow.properChowPushforward_cycleAssociatedToClosedSubscheme_of_section` — the last
  step of the source's proof of the other half: `π_*[σ(X)] = [X]` for a section `σ` of `π`.

## Implementation notes

### What of Stacks 02TW is proved here, and what is not

Only the vanishing `s < r - 1`, and that unconditionally. The remaining assertion `s = r - 1`,
that the pushforward of the top fibre power recovers `α`, is the one the source proves by
choosing `r - 1` rational sections of `O_P(1)` over the generic point of an integral `Z ⊆ X`,
iterating Stacks 02TM to identify `c₁(O_P(1))^{r-1} ∩ π^*[Z]` with the cycle of the image of a
section `Z ⟶ π^{-1}(Z)`, and pushing that image forward. That half is absent — not because it is
assumed anywhere, but because it is not stated here — and the `@[stacks 02TW]` attribute below is
clause-qualified for that reason alone. Both halves together, for the projective bundle of a
module of rank `n + 1`, are `Stacks.Chow.projectiveBundle_projection`.

The last step of the source's argument for the top fibre power is here:
`Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_section` is `π_*[σ(X)] = [X]`
for a section `σ` of a proper `π`, with no hypothesis. The identification of
`c₁(O_P(1))^{r-1} ∩ π^*[Z]` with the cycle of such an image uses three inputs.

1. Stacks 02TM with no hypothesis,
   `Stacks.Chow.gysinHomomorphismOfInvertible_eq_firstChernClassCapOfInvertible`; the key formula
   of Stacks 0AYC behind it is `Stacks.Chow.KeyFormulaSituation.keyFormula_toKeyFormulaData`.
2. The `r - 1` rational sections of `O_P(1)` themselves, from elements `e_1, …, e_{r-1}` of the
   stalk `ℰ_ξ`. `Stacks.ProjectiveBundleTwist.toPushforwardTwist` is Stacks 01OB's section map in
   degree one `ℰ ⟶ π_* O_P(1)` over an arbitrary base,
   `Stacks.ProjectiveBundleTwist.twistSection` is the section of `O_P(1)` over `π^{-1}(U)`
   attached to a section of `ℰ` over `U`, and `Stacks.ProjectiveBundleTwist.twistSectionGerm` is
   its germ at a point of `π^{-1}(U)` — the rational section attached to an element of the fibre,
   which by `Stacks.ProjectiveBundleTwist.twistSectionGerm_eq_of_germ_eq` depends only on that
   element and not on the representative. Nothing is assumed beyond quasi-coherence of `ℰ`.
3. The section `Z ⟶ π^{-1}(Z)` those elements cut out. Producing a morphism *into* a projective
   bundle is the mapping-in half of the universal property, Stacks 01O4; the converse direction,
   a section *given* and shown to be a closed immersion, is Stacks 0B3V
   (`Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase`).

### `O_P(1)` exists, and nothing about it is carried

`O_P(1)` itself is available:
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` builds the twists of a
relative projective spectrum from a quasi-coherent graded algebra with no further hypothesis —
that is Stacks 01NR — so the degree-one piece of its graded algebra is the twist of the
projective bundle, and the twist enters below as an invertible module `L` on `P` with nothing
assumed about it.

The passage from that module to an *operation on Chow groups* is a theorem, in both of its
halves. Stacks 02SO is `Stacks.Chow.firstChernComponentCycleRule`, the component rule of an
invertible module, unconditionally, its own restriction hypothesis discharged by Stacks 0B8L.
Stacks 02TI, the factoring of the resulting cap product through rational equivalence, is
`Stacks.Chow.firstChernCapFactorsEverywhere`, also unconditionally; read for this component rule
it is
`Stacks.Chow.firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule`,
and `Stacks.Chow.invertibleChernCap` is the resulting operator with no argument.
`Stacks.Chow.invertibleChernCapOperator` is the form taking an arbitrary factoring.

The vanishing is also proved for an *arbitrary* `Stacks.Chow.ChernCapOperator` on the bundle,
which is stronger than fixing the operator of `O_P(1)` and is the parameter the Stacks 02U6,
02U7, 02U9 and 02U2 material carries.

### Why Stacks 0FDX does not give the vanishing

`Stacks.Chow.iteratedChernCapOnChow_eq_zero_of_topologicalKrullDim_le` kills a long enough cap
product outright, but it needs the base to be Jacobson with dimension function vanishing at
closed points and the whole of `P` to have bounded topological dimension, and it kills the cap
product *on* `P` rather than its pushforward. Here `s` may be `0`, the cap product on `P` is in
general nonzero, and no dimension bound on `P` is assumed; what vanishes is only the image under
`π_*`, and the reason is the fibre dimension of `π`, not the dimension of `P`.

### The hypotheses on `π`, and which are not hypotheses

`π` is taken flat, locally of finite type, proper, and of relative dimension `r - 1` over `X`.
For the projective bundle of a finite locally free `ℰ` the first of these is Stacks 02TX and the
others are `Stacks.RelativeProj.locallyOfFiniteType_projectiveBundleToBase`,
`Stacks.RelativeProj.isProper_projectiveBundleToBase` and
`Stacks.SymGraded.relativeDimension_freeProjectiveBundleToBase`. Stacks 02S2, that proper
pushforward preserves rational equivalence, is **not** a hypothesis: it is a theorem for every
proper morphism over the base,
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`, and is supplied
from there. Neither is Stacks 02S1 for the flat pullback a hypothesis: it too is a theorem for
every morphism flat and locally of finite type of a given relative dimension,
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`, and reading it for `π` is
`Stacks.Chow.projectiveBundleFlatPullbackFactors`. So the hypothesis-taking
`Stacks.Chow.projectiveBundleProjection` is instantiated below at that theorem rather than at an
argument.

### Truncated subtraction, and `r ≤ 1`

The degree is written with `r - 1` computed in `ℕ`, as in `Stacks.Chow.projectiveBundlePullback`,
so that it also is the relative dimension of `π` without a side condition. The hypothesis
`s < r - 1` is then unsatisfiable for `r ≤ 1`, which is correct: for `r = 1` the bundle is `X`
itself and the vanishing range of the source is empty.

## References

* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TM](https://stacks.math.columbia.edu/tag/02TM)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Transports along equalities of degrees -/

/-- Evaluating a homomorphism transported along an equality of source degrees is evaluating it
on the transported argument. -/
theorem chowGroupDegreeCast_apply (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {k l m : ℤ} (h : k = l)
    (F : chowGroup C p l →+ chowGroup C p m) (x : chowGroup C p k) :
    chowGroupDegreeCast C p h F x = F (chowGroupCast C p h x) := by
  subst h; rfl

/-- Transporting the class of a cycle along an equality of degrees is the class of the
transported cycle. -/
theorem chowGroupCast_mk (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {k l : ℤ} (h : k = l) (c : CycleGroup C p k) :
    chowGroupCast C p h (QuotientAddGroup.mk' (rationalEquivalences C p k) c) =
      QuotientAddGroup.mk' (rationalEquivalences C p l) (h ▸ c) := by
  subst h; rfl

/-! ### Where the extension of a rule on integral components is supported -/

/-- A nonzero coefficient of the extension of a rule on integral components comes from a
component of the argument that the point lies over. This is the support bound the whole
dimension count below rests on, and it is the content of
`Stacks.Chow.ComponentRule.mem_closure_of_apply_ne_zero`. -/
theorem exists_specializes_of_extendCycleGroup_apply_ne_zero (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (q : Y ⟶ C.S)
    [LocallyOfFiniteType q] (g : Y ⟶ X) (k : ℤ) (R : IntegralComponentRule C p q g k)
    (c : CycleGroup C p (k + 1)) (y : Y) (hy : (R.extendCycleGroup c).1 y ≠ 0) :
    ∃ x : X, c.1 x ≠ 0 ∧ x ⤳ g.base y := by
  rw [IntegralComponentRule.extendCycleGroup_apply, ComponentRule.extend_apply] at hy
  by_cases h : ∀ x : X, c.1 x * R.toComponentRule.cycle x y = 0
  · exact absurd (finsum_eq_zero_of_forall_eq_zero h) hy
  · obtain ⟨x, hx⟩ := not_forall.1 h
    refine ⟨x, left_ne_zero_of_mul hx, specializes_iff_mem_closure.2 ?_⟩
    exact R.toComponentRule.mem_closure_of_apply_ne_zero x y (right_ne_zero_of_mul hx)

/-! ### Cycle representatives of the iterated cap products -/

/-- **The engine.** An iterated first Chern class cap product has a cycle representative whose
support lies over the part of `X` where a chosen representative of its argument is supported:
each cap replaces a component by a cycle on that component, and that only specializes the points
involved.

Stated for an arbitrary list of first Chern class cap operators and an arbitrary morphism
`π : P ⟶ X` and bound, which is what makes the induction on the list go through. -/
theorem exists_cycle_iteratedChernCapOnChow_of_fibreDimension (C : ChowSituation.{u})
    {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (π : P ⟶ X) (bound : ℤ) :
    ∀ (Os : List (ChernCapOperator C sP)) (m : ℤ) (c : CycleGroup C sP (m + (Os.length : ℤ))),
      (∀ y : P, c.1 y ≠ 0 → relativeDimension C.dimensionFunction sX (π.base y) ≤ bound) →
      ∃ d : CycleGroup C sP m,
        iteratedChernCapOnChow C sP Os m
            (QuotientAddGroup.mk' (rationalEquivalences C sP (m + (Os.length : ℤ))) c) =
          QuotientAddGroup.mk' (rationalEquivalences C sP m) d ∧
        ∀ y : P, d.1 y ≠ 0 → relativeDimension C.dimensionFunction sX (π.base y) ≤ bound := by
  intro Os
  induction Os with
  | nil =>
    intro m c hc
    refine ⟨(by simp : m + ((([] : List (ChernCapOperator C sP)).length : ℤ)) = m) ▸ c, ?_, ?_⟩
    · rw [iteratedChernCapOnChow, chowGroupDegreeCast_apply, chowGroupCast_mk]
      rfl
    · intro y hy
      exact hc y (by rwa [val_cycleGroup_cast] at hy)
  | cons O Os ih =>
    intro m c hc
    have hdeg : m + (((O :: Os).length : ℕ) : ℤ) = m + 1 + ((Os.length : ℕ) : ℤ) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    obtain ⟨d', hd', hsupp'⟩ := ih (m + 1) (hdeg ▸ c)
      (fun y hy ↦ hc y (by rwa [val_cycleGroup_cast] at hy))
    refine ⟨(firstChernCapRule C sP m (O.chern m)).extendCycleGroup d', ?_, ?_⟩
    · rw [iteratedChernCapOnChow, chowGroupDegreeCast_apply, chowGroupCast_mk]
      rw [AddMonoidHom.comp_apply, hd']
      rfl
    · intro y hy
      obtain ⟨x, hx, hspec⟩ := exists_specializes_of_extendCycleGroup_apply_ne_zero C sP sP
        (𝟙 P) m _ d' y hy
      exact le_trans (relativeDimension_le_of_specializes C sX (hspec.map π.continuous))
        (hsupp' x hx)

/-! ### The pushforward of an iterated cap of a flat pullback -/

/-- **The dimension count of Stacks 02TW.** Let `π : P ⟶ X` be flat and proper of relative
dimension `e` over the base. For a class of degree `k` on `X`, an iterated first Chern class cap
of its flat pullback, read in a degree `m` strictly larger than `k`, pushes forward to zero.

This is the whole of the vanishing half of Stacks 02TW, with the degrees as parameters: the cap
product has a representative supported over the support of a representative of the class, so its
points have image of delta-dimension at most `k`, while the representative itself is an `m`-cycle
with `k < m`; proper pushforward weights such a point by zero. -/
theorem properChowPushforward_iteratedChernCapOnChow_flatPullbackChow_eq_zero
    (C : ChowSituation.{u}) {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [Flat π] [IsProper π]
    (hsP : π ≫ sX = sP) (e : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π e) (k m : ℤ)
    (hkm : k < m) (hfac : FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP e hπ k)
    (Os : List (ChernCapOperator C sP)) (hcast : k + (e : ℤ) = m + ((Os.length : ℕ) : ℤ))
    (α : chowGroup C sX k) :
    properChowPushforward C sP sX π hsP m
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sX π hsP m)
        (iteratedChernCapOnChow C sP Os m
          (chowGroupCast C sP hcast
            (flatPullbackChow C sP sX π hsP e hπ k hfac α))) = 0 := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sX k) α
  obtain ⟨d, hd, hsupp⟩ := exists_cycle_iteratedChernCapOnChow_of_fibreDimension C sX sP π k
    Os m (hcast ▸ flatPullback C sP sX π hsP e hπ k a) (by
      intro y hy
      rw [val_cycleGroup_cast, flatPullback_apply] at hy
      exact le_of_eq ((mem_cyclesOfDimension_iff_forall_point C sX k a.1).1 a.2 _
        (left_ne_zero_of_mul hy)))
  have hzero : properPushforward C sP sX π hsP m d = 0 := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    rw [properPushforward_apply]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun y _ ↦ ?_
    by_cases hy : d.1 y = 0
    · rw [hy, zero_mul]
    · have hdim : relativeDimension C.dimensionFunction sP y = m :=
        (mem_cyclesOfDimension_iff_forall_point C sP m d.1).1 d.2 y hy
      have hne : ¬ relativeDimension C.dimensionFunction sP y =
          relativeDimension C.dimensionFunction sX (π.base y) := by
        rw [hdim]
        exact fun h ↦ absurd (h ▸ hsupp y hy) (by omega)
      rw [ite_eq_right hne, mul_zero]
  rw [flatPullbackChow_mk, chowGroupCast_mk, hd, properChowPushforward_mk, hzero]
  simp

/-! ### Pushing the image of a section back down -/

/-- **The last step of the source's proof of the top fibre power.** Let `π : P ⟶ X` be proper
over the base and let `σ : X ⟶ P` be a section of it which is a closed immersion. Then the cycle
of the image of `σ` pushes forward along `π` to the cycle of `X` in itself:

  `π_*[σ(X)]_k = [X]_k`.

This is the step the source writes as "pushing forward the image of a section over `Z` returns
`[Z]`". It is
`Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp`,
a special case of Stacks 02R6, read at `i = σ` and `f = π`: the composite `σ ≫ π` is the
identity, hence a closed immersion, so the hypothesis of that lemma holds and its right hand side
is the cycle of `X` as a closed subscheme of itself.

For the projective bundle of a quasi-coherent module the closed-immersion hypothesis on `σ` is
automatic, by Stacks 0B3V
(`Stacks.RelativeProj.isClosedImmersion_of_section_projectiveBundleToBase`), since `π` is
separated. -/
theorem properPushforward_cycleAssociatedToClosedSubscheme_of_section (C : ChowSituation.{u})
    {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (π : P ⟶ X) [IsProper π] (hsP : π ≫ sX = sP) (σ : X ⟶ P)
    [IsClosedImmersion σ] (hσ : σ ≫ π = 𝟙 X) (k : ℤ) :
    properPushforward C sP sX π hsP k (cycleAssociatedToClosedSubscheme C sP σ k) =
      cycleAssociatedToClosedSubscheme C sX (𝟙 X) k := by
  have hci : IsClosedImmersion (σ ≫ π) := hσ ▸ (inferInstance : IsClosedImmersion (𝟙 X))
  refine (properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
    C sP sX π hsP σ k).trans ?_
  revert hci
  rw [hσ]
  intro _
  rfl

/-- The same identity read in the Chow groups: the class of the image of a section pushes
forward to the class of `X`. Stacks 02S2 for `π` is supplied by
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`, so there is no
hypothesis here either. -/
theorem properChowPushforward_cycleAssociatedToClosedSubscheme_of_section (C : ChowSituation.{u})
    {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (π : P ⟶ X) [IsProper π] (hsP : π ≫ sX = sP) (σ : X ⟶ P)
    [IsClosedImmersion σ] (hσ : σ ≫ π = 𝟙 X) (k : ℤ) :
    properChowPushforward C sP sX π hsP k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sX π hsP k)
        (QuotientAddGroup.mk' (rationalEquivalences C sP k)
          (cycleAssociatedToClosedSubscheme C sP σ k)) =
      QuotientAddGroup.mk' (rationalEquivalences C sX k)
        (cycleAssociatedToClosedSubscheme C sX (𝟙 X) k) := by
  rw [properChowPushforward_mk,
    properPushforward_cycleAssociatedToClosedSubscheme_of_section C sX sP π hsP σ hσ k]

/-! ### The cap operator of an invertible module -/

/-- **The first Chern class cap operator of an invertible module**, with only Stacks 02TI carried.

Of the two fields of `Stacks.Chow.ChernCapOperator` the component rule of Stacks 02SO is
*constructed*, with no hypothesis: it is `Stacks.Chow.firstChernComponentCycleRule`, the divisor
cycle of a nonzero meromorphic section of `L` restricted to each integral component, whose own
restriction hypothesis is discharged by Stacks 0B8L
(`Stacks.Chow.isInvertible_presheaf_modulePullback`). Only the factoring through rational
equivalence, Stacks 02TI, is an argument, and it is stated for exactly that constructed rule. -/
def invertibleChernCapOperator (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hfactors : ∀ k : ℤ, FirstChernClassCapFactorsThroughRationalEquivalence C p k
      (firstChernComponentCycleRule C p k L)) :
    ChernCapOperator C p where
  chern k := firstChernComponentCycleRule C p k L
  factors := hfactors

/-- The component rule of `invertibleChernCapOperator C p L hfactors` in degree `k` is
`firstChernComponentCycleRule C p k L`. -/
@[simp]
theorem invertibleChernCapOperator_chern (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hfactors : ∀ k : ℤ, FirstChernClassCapFactorsThroughRationalEquivalence C p k
      (firstChernComponentCycleRule C p k L)) (k : ℤ) :
    (invertibleChernCapOperator C p L hfactors).chern k =
      firstChernComponentCycleRule C p k L :=
  rfl

/-- **The first Chern class cap operator of an invertible module, with no hypothesis.**

Both fields are theorems of this development: the component rule of Stacks 02SO is
`Stacks.Chow.firstChernComponentCycleRule`, and its factoring through rational equivalence,
Stacks 02TI, is
`Stacks.Chow.firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule`,
which is `Stacks.Chow.firstChernCapFactorsEverywhere` read for this scheme and this module. -/
def invertibleChernCap (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    ChernCapOperator C p :=
  invertibleChernCapOperator C p L fun k ↦
    firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C k p L

/-- The component rule of `invertibleChernCap C p L` in degree `k` is
`firstChernComponentCycleRule C p k L`. -/
@[simp]
theorem invertibleChernCap_chern (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (k : ℤ) :
    (invertibleChernCap C p L).chern k = firstChernComponentCycleRule C p k L :=
  rfl

/-! ### The operation of Stacks 02TW -/

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [Flat π]
  [IsProper π] (hsP : π ≫ sX = sP) (r : ℕ)
  (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
  (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)
  (twist : ChernCapOperator C sP)

/-- **The left-hand side of Stacks 02TW**: pull a class of degree `k` back to the projective
bundle, cap it `s` times with the first Chern class of the twist, and push the result forward to
the base. The result has degree `k + (r - 1) - s`.

The flat pullback is `Stacks.Chow.projectiveBundlePullback`, Stacks 0FVK along `π`; the cap is
`Stacks.Chow.iteratedChernCapOnChow` at the constant list, Stacks 02TI; the pushforward is
`Stacks.Chow.properChowPushforward`, Stacks 0GU8, whose hypothesis Stacks 02S2 is discharged by
properness of `π`. -/
def projectiveBundleProjection (s : ℕ) (k : ℤ) :
    chowGroup C sX k →+ chowGroup C sX (k + ((r - 1 : ℕ) : ℤ) - (s : ℤ)) :=
  (properChowPushforward C sP sX π hsP (k + ((r - 1 : ℕ) : ℤ) - (s : ℤ))
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sX π hsP
        (k + ((r - 1 : ℕ) : ℤ) - (s : ℤ)))).comp
    ((iteratedChernCapOnChow C sP (List.replicate s twist)
        (k + ((r - 1 : ℕ) : ℤ) - (s : ℤ))).comp
      (((chowGroupCast C sP (show k + ((r - 1 : ℕ) : ℤ) =
            k + ((r - 1 : ℕ) : ℤ) - (s : ℤ) +
              (((List.replicate s twist).length : ℕ) : ℤ) from by
          simp only [List.length_replicate]; ring)).toAddMonoidHom).comp
        (projectiveBundlePullback C sX sP π hsP r hπ hfac k)))

/-- **The vanishing half of Stacks 02TW, for an arbitrary cap operator.** For `s < r - 1` the
pushforward `π_*(c₁^s ∩ π^*α)` vanishes in `CH_{k+r-1-s}(X)`, for any first Chern class cap
operator on the bundle in place of the one of `O_P(1)`.

The source argues "for dimension reasons", and this is those reasons. Choose a cycle `a`
representing `α`; it is a `k`-cycle, so its support meets only points of delta-dimension `k`, and
the flat pullback of `a` is supported over that support. By
`Stacks.Chow.exists_cycle_iteratedChernCapOnChow_of_fibreDimension` the `s`-fold cap product has
a representative `d` still supported over it, so every point in the support of `d` has image of
delta-dimension at most `k`, while `d` itself is a cycle of degree `k + (r - 1) - s`, which
exceeds `k` exactly because `s < r - 1`. A point of the source whose delta-dimension differs
from that of its image contributes weight zero to a proper pushforward, so every coefficient of
`π_*d` vanishes. -/
theorem projectiveBundleProjection_eq_zero_of_lt (s : ℕ) (hs : s < r - 1) (k : ℤ)
    (α : chowGroup C sX k) :
    projectiveBundleProjection C sX sP π hsP r hπ hfac twist s k α = 0 :=
  properChowPushforward_iteratedChernCapOnChow_flatPullbackChow_eq_zero C sX sP π hsP (r - 1) hπ
    k (k + ((r - 1 : ℕ) : ℤ) - (s : ℤ))
    (by omega) (hfac k) (List.replicate s twist)
    (by simp only [List.length_replicate]; ring) α

/-! ### Stacks 02TW, vanishing below the fibre dimension, with no hypothesis -/

/-- **Stacks 02S1 for the projection of the bundle.** Flat pullback along `π` carries cycles
rationally equivalent to zero to cycles rationally equivalent to zero. This is
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`, which holds for every
morphism flat and locally of finite type of a given relative dimension, read for `π`; local
finite type comes from properness. -/
theorem projectiveBundleFlatPullbackFactors (k : ℤ) :
    FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k :=
  flatPullbackFactorsThroughRationalEquivalence_general C sP sX π hsP (r - 1) hπ k

/-- **Stacks 02TW, vanishing below the fibre dimension, with no hypothesis.** For `s < r - 1`,

  `π_*(c₁(L)^s ∩ π^*α) = 0`  in  `A_{k+(r-1)-s}(X)`,

for `L` the twist `O_P(1)` of the projective bundle. Nothing is assumed beyond the geometry of
the bundle: `π` is flat, proper and of relative dimension `r - 1` over the base, which for the
projective bundle of a finite locally free module of rank `r` is Stacks 02TX
(`Stacks.RelativeProj.isProper_projectiveBundleToBase`,
`Stacks.RelativeProj.locallyOfFiniteType_projectiveBundleToBase` and
`Stacks.SymGraded.relativeDimension_freeProjectiveBundleToBase`), and `L` is an invertible
module on `P`, which the twist is.

The three inputs the operation is built from are all theorems here: Stacks 02S1 for the flat
pullback is `Stacks.Chow.projectiveBundleFlatPullbackFactors`, Stacks 02SO and 02TI for the cap
with `c₁(L)` are `Stacks.Chow.invertibleChernCap`, and Stacks 02S2 for the pushforward is
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`. The vanishing
itself is the dimension count of
`Stacks.Chow.properChowPushforward_iteratedChernCapOnChow_flatPullbackChow_eq_zero`. -/
@[stacks 02TW "vanishing below the fibre dimension: the assertion for s < r - 1, with no \
hypothesis. The projective bundle enters as a flat, proper morphism of relative dimension r - 1 \
over the base (Stacks 02TX) and its twist as an invertible module; Stacks 02S1 for the flat \
pullback, Stacks 02SO and 02TI for the cap product and Stacks 02S2 for the pushforward are all \
supplied from this development. The top fibre power, that the pushforward at s = r - 1 is α \
itself, is NOT proved here. What it still needs is the mapping-in half of the universal property \
of relative Proj, Stacks 01O4, to produce the section Z -> pi^-1(Z) whose image the r - 1 \
sections cut out; the other two ingredients the source's proof uses are now available, Stacks \
02TM unconditionally and the rational sections of O_P(1) as \
Stacks.ProjectiveBundleTwist.twistSectionGerm"]
theorem projectiveBundleProjection_twist_eq_zero_of_lt (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (s : ℕ) (hs : s < r - 1) (k : ℤ) (α : chowGroup C sX k) :
    projectiveBundleProjection C sX sP π hsP r hπ
      (projectiveBundleFlatPullbackFactors C sX sP π hsP r hπ)
      (invertibleChernCap C sP L) s k α = 0 :=
  projectiveBundleProjection_eq_zero_of_lt C sX sP π hsP r hπ
    (projectiveBundleFlatPullbackFactors C sX sP π hsP r hπ)
    (invertibleChernCap C sP L) s hs k α

/-- **Stacks 02TW, vanishing below the fibre dimension, for the twist itself.** The same
statement with the cap operator replaced by the one `O_P(1)` provides: its component rule of
Stacks 02SO is built here from the module, and only the factoring of Stacks 02TI is an argument.

This is the form in which the source states the vanishing half: `L` is the twist `O_P(1)` of the
projective bundle, which exists — the degree-one piece of the graded algebra of
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, Stacks 01NR, which takes
no hypothesis beyond the quasi-coherent graded algebra.

No `@[stacks 02TW]` attribute is attached: Stacks 02TW with nothing carried is
`Stacks.Chow.projectiveBundle_projection`. -/
theorem projectiveBundleProjection_invertible_eq_zero_of_lt (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (hfactors : ∀ k : ℤ, FirstChernClassCapFactorsThroughRationalEquivalence C sP k
      (firstChernComponentCycleRule C sP k L))
    (s : ℕ) (hs : s < r - 1) (k : ℤ) (α : chowGroup C sX k) :
    projectiveBundleProjection C sX sP π hsP r hπ hfac
      (invertibleChernCapOperator C sP L hfactors) s k α = 0 :=
  projectiveBundleProjection_eq_zero_of_lt C sX sP π hsP r hπ hfac
    (invertibleChernCapOperator C sP L hfactors) s hs k α

end Stacks.Chow

end
