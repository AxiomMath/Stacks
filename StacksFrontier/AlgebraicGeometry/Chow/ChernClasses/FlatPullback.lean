module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.ChernCapDescent

/-!
# Flat pullback and the first Chern class cap product

Let `X` and `X'` be schemes locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project, let `f : X' ⟶ X` be flat of relative dimension `r` and let `L` be an invertible
module on `X`. Stacks 02SS is the identity

  `f^*(c₁(L) ∩ α) = c₁(f^*L) ∩ f^*α`  in  `A_{k+r}(X')`,  for `α ∈ Z_{k+1}(X)`.

The source proves it one integral component at a time: for an integral closed subscheme
`W ⊆ X` of delta-dimension `k + 1` it decomposes `f^{-1}(W)` into its components of
delta-dimension `k + r + 1`, restricts a meromorphic section of `L|_W` to each, and produces a
rational equivalence on `f^{-1}(W)`. This file performs the complementary step: **the identity on
integral components implies the identity on all cycles.** The component case is the hypothesis
`Stacks.Chow.FirstChernCapCompatibleWithFlatPullback`.

That step is where the work is, and it is not formal. Both sides are locally finite sums over the
points of their own scheme — the left over the points of `X'`, the right over those of `X` — so
the proof reindexes the left-hand sum over the fibres of `f` with
`Stacks.Chow.finsum_finsum_mem_fiber`, after which the hypothesis applies fibre by fibre. The
finiteness that reindexing needs comes from the local finiteness of the support of the pulled-back
cycle, through `Stacks.Chow.finite_support_inter_generalizations`.

## Main definitions

* `Stacks.Chow.FirstChernCapCompatibleWithFlatPullback` — the identity of Stacks 02SS on integral
  components, which is the case the source proves, read as a hypothesis.

## Main results

* `Stacks.Chow.flatPullback_firstChernCapRule_extendCycleGroup` — Stacks 02SS at the level of
  **cycles**: granted the identity on integral components, the cap product cycle of a flat
  pullback is the flat pullback of the cap product cycle.
* `Stacks.Chow.flatPullbackChow_firstChernClassCap` — **Stacks 02SS**, the same identity read
  through flat pullback on Chow groups.
* `Stacks.Chow.flatPullbackChow_firstChernClassCapOnChow` — **Stacks 02SS** with both cap
  products descended to Chow groups by Stacks 02TI, which is the form the bivariant class of
  Stacks 0B77 needs for its flat-pullback axiom.
* `Stacks.Chow.firstChernCapCompatibleWithFlatPullback_of_components` — the hypothesis, restated
  on integral closed subschemes rather than on points.

## Implementation notes

### The parameters threaded, and why

Three inputs of the source are absent from this repository and are carried as explicit
parameters, in the way established by `StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass`,
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward` and
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCap`:

* the component rules `chern` on `X` and `chern'` on `X'`, standing in for the component input of
  Stacks 02SO, whose intended values are the divisor cycles of Stacks 02SJ for `L` and for
  `f^*L`. They are `FirstChernComponentCycleRule`s, hence **data**, so they are parameters rather
  than quantified over — the rule recorded in the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic`: for data, `∀ G, P G` is strictly stronger
  than `P G₀`, and over-strengthening is as unfaithful as weakening. In the source `chern'` comes
  from `f^*L`; here the two rules are independent and are linked only by the compatibility
  hypothesis below. In particular Stacks 0B8L, which the source needs in order to know that
  `f^*L` is invertible, is not needed;
* the vanishing of Stacks 02S1 carried by `Stacks.Chow.flatPullbackChow`, needed to have the map
  `f^* : A_k(X) ⟶ A_{k+r}(X')` of Stacks 0FVK at all. It is a `Prop`, so it is an ordinary
  hypothesis and proof irrelevance makes the conclusion independent of which proof is supplied;
* the vanishing of Stacks 02TI for each of the two cap products, in
  `Stacks.Chow.flatPullbackChow_firstChernClassCapOnChow`. Also a `Prop`.

The relative dimension `Stacks.Chow.relativeDimension` enters only through the delta-dimension of
an integral component, so the dimension function of Stacks 02JW is not a parameter and is not
needed.

### The compatibility hypothesis is the component case of the source, and is indispensable

`Stacks.Chow.FirstChernCapCompatibleWithFlatPullback` says that the identity holds, at the level
of cycle coefficients, over each integral component of `X` of delta-dimension `k + 1` — the sum
over the fibre of `f` above its generic point of the component cycles on `X'`, weighted by the
flat pullback multiplicity, is the flat pullback of the component cycle on `X`. That is exactly
the case the source proves, and which it proves by exhibiting a rational equivalence on
`f^{-1}(W)`.

It cannot be dropped. The cap product on `X` is built from an arbitrary
`Stacks.Chow.FirstChernComponentCycleRule` and the one on `X'` from another; two unrelated rules
have no reason to be compatible along `f`, so without the hypothesis the conclusion is false —
take `chern' = 0` and `chern` with some nonzero value on a component dominated by `X'`.

The hypothesis is also strictly weaker than the conclusion: it constrains the rules only over
single integral components, and the theorem extends it to every cycle. A cycle is a *locally*
finite sum of components, so that extension needs the fibrewise reindexing described above; it
is the same step that `Stacks.Chow.flatPullback_gysinRule_extendCycleGroup` performs for the
Gysin map of Stacks 0B71.

### The degree cast

The flat pullback of a `(k+1)`-cycle has degree `(k + 1) + r`, while the cap product in degree
`k + r` consumes a cycle of degree `(k + r) + 1`. These are the same integer and not the same
term, so the statements carry the transport `hcast : k + 1 + r = k + r + 1` as a hypothesis,
exactly as Stacks 0B71 does in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback`. `Stacks.Chow.val_cycleGroup_cast`
says the transport does not change the coefficient function, which is what makes the proof
go through.

## References

* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X' X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (r : ℕ)
  (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
  (chern : FirstChernComponentCycleRule C p k)
  (chern' : FirstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ)))

/-! ### Stacks 02SS on integral components -/

/-- **Stacks 02SS on integral components.** The assertion that for every integral component of
`X` of delta-dimension `k + 1` — equivalently, for every point `x` of relative dimension `k + 1` —
the sum over the fibre `f^{-1}(x)` of the first Chern class component cycles on `X'`, weighted by
the flat pullback multiplicity, is the flat pullback of the component cycle of `x`.

This is the case the source proves, by producing a rational equivalence on `f^{-1}(W)` for the
integral closed subscheme `W = closure {x}`. It is carried as a hypothesis here; see the
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.ChernClasses.FlatPullback`. The
assertion is an equality of cycle *coefficients*, as the component formula of Stacks 02SO is. -/
def FirstChernCapCompatibleWithFlatPullback : Prop :=
  ∀ x : X, relativeDimension C.dimensionFunction p x = k + 1 → ∀ y' : X',
    ∑ᶠ x' ∈ f.base ⁻¹' {x},
        flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
          (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) chern' x').1 y' =
      (flatPullback C (f ≫ p) p f rfl r hf k
        (firstChernComponentCycleAt C p k chern x)).1 y'

/-- The compatibility of the component rules along `f`, restated on integral closed subschemes of
`X` instead of on points: the two are the same datum, by
`Stacks.Chow.integralComponentAt_genericPointOf`. -/
theorem firstChernCapCompatibleWithFlatPullback_of_components
    (h : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) (y' : X'),
      ∑ᶠ x' ∈ f.base ⁻¹' {genericPointOf W hW},
          flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
            (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) chern' x').1 y' =
        (flatPullback C (f ≫ p) p f rfl r hf k
          (firstChernComponentCycle C p k chern W hW hDim)).1 y') :
    FirstChernCapCompatibleWithFlatPullback C p f r hf k chern chern' := by
  intro x hdim y'
  have hW : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hDim : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_integralComponentAt C p x, hdim]
  have hx : genericPointOf (integralComponentAt x) hW = x := genericPointOf_integralComponentAt x
  have h' := h (integralComponentAt x) hW hDim y'
  rw [← firstChernComponentCycleAt_genericPointOf C p k chern _ hW hDim, hx] at h'
  exact h'

/-! ### Stacks 02SS -/

/-- **Stacks 02SS, at the level of cycles.** Granted the identity on integral components,
intersection with the first Chern class commutes with flat pullback already on cycles.

The left side is a locally finite sum over the points of `X'` and the right side one over the
points of `X`. The proof reindexes the first over the fibres of `f`, using
`Stacks.Chow.finsum_finsum_mem_fiber`; the finiteness it needs comes from the local finiteness of
the support of the pulled-back cycle. After that the hypothesis applies term by term, and only
the points carrying a nonzero coefficient of `α` are compared — those have relative dimension
`k + 1` because `α` is a `(k+1)`-cycle. -/
theorem flatPullback_firstChernCapRule_extendCycleGroup
    (hcomp : FirstChernCapCompatibleWithFlatPullback C p f r hf k chern chern')
    (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) (α : CycleGroup C p (k + 1)) :
    (firstChernCapRule C (f ≫ p) (k + (r : ℤ)) chern').extendCycleGroup
        (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1) α) =
      flatPullback C (f ≫ p) p f rfl r hf k
        ((firstChernCapRule C p k chern).extendCycleGroup α) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y'
  set β := flatPullback C (f ≫ p) p f rfl r hf (k + 1) α with hβ
  set R' := firstChernCapRule C (f ≫ p) (k + (r : ℤ)) chern' with hR'
  set G : X' → ℤ := fun x' ↦ β.1 x' *
    (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) chern' x').1 y' with hG
  -- only the components of the pulled-back cycle passing through `y'` contribute
  have hGfin : (Function.support G).Finite := by
    refine (finite_support_inter_generalizations β.1.locallyFiniteSupport
      (isCompact_singleton (x := (𝟙 X' : X' ⟶ X').base y'))).subset ?_
    intro x' hx'
    replace hx' : β.1 x' * R'.toComponentRule.cycle x' y' ≠ 0 := hx'
    exact ⟨⟨_, rfl, R'.toComponentRule.mem_closure_of_apply_ne_zero x' y'
      (right_ne_zero_of_mul hx')⟩, left_ne_zero_of_mul hx'⟩
  -- the left hand side, reindexed over the fibres of `f`
  have hLHS : (R'.extendCycleGroup (hcast ▸ β)).1 y' =
      ∑ᶠ x : X, ∑ᶠ x' ∈ f.base ⁻¹' {x}, G x' := by
    rw [finsum_finsum_mem_fiber f.base G hGfin,
      show (R'.extendCycleGroup (hcast ▸ β)).1 y' =
        R'.toComponentRule.extendCoeff (hcast ▸ β : CycleGroup C (f ≫ p) _).1 y' from rfl,
      val_cycleGroup_cast C (f ≫ p) hcast β]
    rfl
  -- the right hand side, as a locally finite sum over the points of `X`
  have hRHS : (flatPullback C (f ≫ p) p f rfl r hf k
      ((firstChernCapRule C p k chern).extendCycleGroup α)).1 y' =
      ∑ᶠ x : X, α.1 x *
        (flatPullback C (f ≫ p) p f rfl r hf k
          (firstChernComponentCycleAt C p k chern x)).1 y' := by
    rw [flatPullback_apply,
      show ((firstChernCapRule C p k chern).extendCycleGroup α).1 (f.base y') =
        ∑ᶠ x : X, α.1 x * (firstChernComponentCycleAt C p k chern x).1 (f.base y') from rfl,
      finsum_mul]
    exact finsum_congr fun x ↦ by rw [flatPullback_apply]; ring
  rw [hLHS, hRHS]
  refine finsum_congr fun x ↦ ?_
  -- the coefficient at a point of the fibre over `x`
  have hGval : ∀ x' : X', f.base x' = x → G x' = α.1 x *
      (flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
        (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) chern' x').1 y') := by
    intro x' hx'
    have h1 : β.1 x' = α.1 x * flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' := by
      rw [hβ, flatPullback_apply, hx']
    simp only [hG]
    rw [h1, mul_assoc]
  by_cases hx : α.1 x = 0
  · rw [hx, zero_mul]
    exact finsum_mem_eq_zero_of_forall_eq_zero fun x' hx' ↦ by
      rw [hGval x' hx', hx, zero_mul]
  · rw [← hcomp x ((mem_cyclesOfDimension_iff_forall_point C p (k + 1) α.1).1 α.2 x hx) y',
      mul_finsum_mem]
    exact finsum_mem_congr rfl fun x' hx' ↦ hGval x' hx'

/-- **Stacks 02SS.** Intersection with the first Chern class commutes with flat pullback:
`c₁(f^*L) ∩ f^*α = f^*(c₁(L) ∩ α)` in `A_{k+r}(X')` for every `α ∈ Z_{k+1}(X)`.

The component rules of the cap products on `X` and on `X'`, their compatibility along `f` and the
vanishing of Stacks 02S1 needed for `Stacks.Chow.flatPullbackChow` are explicit parameters; see
the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClasses.FlatPullback`. The identity holds already at the
level of cycles, which is `Stacks.Chow.flatPullback_firstChernCapRule_extendCycleGroup`. -/
theorem flatPullbackChow_firstChernClassCap
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (f ≫ p) p f rfl r hf k)
    (hcomp : FirstChernCapCompatibleWithFlatPullback C p f r hf k chern chern')
    (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) (α : CycleGroup C p (k + 1)) :
    firstChernClassCap C (f ≫ p) (k + (r : ℤ)) chern'
        (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1) α) =
      flatPullbackChow C (f ≫ p) p f rfl r hf k hfac
        (firstChernClassCap C p k chern α) := by
  change QuotientAddGroup.mk ((firstChernCapRule C (f ≫ p) (k + (r : ℤ)) chern').extendCycleGroup
    (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1) α)) = _
  rw [flatPullback_firstChernCapRule_extendCycleGroup C p f r hf k chern chern' hcomp hcast α]
  rfl

/-- Transporting a Chow class along an equality of degrees commutes with taking the class of a
cycle. The two sides of Stacks 02SS sit in degrees `k + 1 + r` and `k + r + 1`, and the descended
form below has to move the transport past the quotient map. -/
private theorem chowGroup_cast_mk {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q]
    {j j' : ℤ} (h : j = j') (β : CycleGroup C q j) :
    (h ▸ QuotientAddGroup.mk' (rationalEquivalences C q j) β : chowGroup C q j') =
      QuotientAddGroup.mk' (rationalEquivalences C q j') (h ▸ β) := by
  subst h
  rfl

/-- **Stacks 02SS, with both cap products descended to Chow groups.** Intersection with the first
Chern class, as the operation `A_{k+1}(X) ⟶ A_k(X)` of Stacks 02TI, commutes with flat pullback
on Chow groups.

This is the form the flat-pullback axiom of the bivariant class of Stacks 0B77 is stated in: both
arguments and both values are Chow classes. It follows from the cycle-level identity
`Stacks.Chow.flatPullbackChow_firstChernClassCap` by inspecting the class of a cycle, the two
descents being determined by their values there. -/
theorem flatPullbackChow_firstChernClassCapOnChow
    (h : FirstChernClassCapFactorsThroughRationalEquivalence C p k chern)
    (h' : FirstChernClassCapFactorsThroughRationalEquivalence C (f ≫ p) (k + (r : ℤ)) chern')
    (hfacTop : FlatPullbackFactorsThroughRationalEquivalence C (f ≫ p) p f rfl r hf (k + 1))
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (f ≫ p) p f rfl r hf k)
    (hcomp : FirstChernCapCompatibleWithFlatPullback C p f r hf k chern chern')
    (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) (α : chowGroup C p (k + 1)) :
    firstChernClassCapOnChow C (f ≫ p) (k + (r : ℤ)) chern' h'
        (hcast ▸ flatPullbackChow C (f ≫ p) p f rfl r hf (k + 1) hfacTop α) =
      flatPullbackChow C (f ≫ p) p f rfl r hf k hfac
        (firstChernClassCapOnChow C p k chern h α) := by
  induction α using QuotientAddGroup.induction_on with
  | H α₀ =>
    rw [show QuotientAddGroup.mk α₀ =
      QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) α₀ from rfl,
      flatPullbackChow_mk, chowGroup_cast_mk C (f ≫ p) hcast,
      firstChernClassCapOnChow_mk, firstChernClassCapOnChow_mk,
      flatPullbackChow_firstChernClassCap C p f r hf k chern chern' hfac hcomp hcast α₀]

end Stacks.Chow

end
