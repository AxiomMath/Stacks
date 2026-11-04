module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClasses.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality

/-!
# Flat pullback and the first Chern class cap product of an invertible module

Let `X` and `X'` be schemes locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project, let `f : X' ⟶ X` be flat of relative dimension `r` and let `L` be an invertible
module on `X`. Stacks 02SS is the identity

  `f^*(c₁(L) ∩ α) = c₁(f^*L) ∩ f^*α`  in  `A_{k+r}(X')`,  for `α ∈ Z_{k+1}(X)`.

`StacksFrontier.AlgebraicGeometry.Chow.ChernClasses.FlatPullback` proves it for a pair of abstract
first Chern class component rules on `X` and on `X'`. This file does two further things, and the
second is why the first is needed.

* It states the component case of the source **up to rational equivalence** rather than as an
  equality of cycles, and proves that the weaker hypothesis still gives Stacks 02SS. That is what
  the source actually produces: its proof of the component case ends by *"producing a rational
  equivalence on the closed subscheme `f^{-1}(W_i)`"*, and the sum over the components of a cycle
  of those rational equivalences is Stacks 02RZ, which this repository proves as
  `Stacks.Chow.rationallyEquivalentToZero_finsum_of_closedSupports`.
* It specialises the result to the component rules of an invertible module `L` on `X` and of
  `f^*L` on `X'`, so that no component rule is a parameter any more. Those rules are
  `Stacks.Chow.firstChernComponentCycleRule`, and the cap products they give are
  `Stacks.Chow.firstChernClassCapOfInvertible`, the cap product of Stacks 02SO for an invertible
  module.

## Why the equality of cycles is the wrong hypothesis for an invertible module

`Stacks.Chow.FirstChernCapCompatibleWithFlatPullback` asks for an equality of cycle
*coefficients* on `X'`. Instantiated at the two component rules of `L` and `f^*L` that assertion
is not available, and not merely unproved: each rule obtains its cycle as the divisor of a nonzero
meromorphic section of the restriction of its module to the component, chosen independently on
each component by `Stacks.Divisors.exists_ne_zero_genericStalk`. Two independent choices on a
component `W'` of `f^{-1}(W)` differ by a nonzero element of the function field of `W'`, so the
two divisor cycles differ by its principal divisor; the source's own cycle identity holds for the
*restriction* `s|_{W'}` of the section chosen on `W`, which the rule on `X'` has no reason to pick.
What survives the change of section is the class in `A_{k+r}(W')`, by Stacks 02SJ (2)
(`Stacks.Chow.mk_chernComponentCycleRule_eq`). So the component hypothesis has to be stated
modulo rational equivalence, which is what
`Stacks.Chow.FirstChernCapRationallyCompatibleWithFlatPullback` does.

It is genuinely weaker: the cycle-level form implies it by the zero rational equivalence, which is
`Stacks.Chow.firstChernCapRationallyCompatibleWithFlatPullback_of_compatible`.

## What is still a hypothesis, and what it is

Two `Prop`s, and neither of them data:

* `Stacks.Chow.FirstChernCapRationallyCompatibleWithFlatPullback` is
  [Stacks, Tag 0EPJ](https://stacks.math.columbia.edu/tag/0EPJ) in the shape Stacks 02SS consumes
  it — the flat pullback of the divisor of a nonzero meromorphic section is the weighted sum of
  the divisors of its restrictions to the components of the preimage — read modulo a rational
  equivalence carried on `f^{-1}(W)`. It is a hypothesis *here* only because this file is stated
  for a pair of abstract component rules, for which it can fail. At the component rules of an
  invertible module it is a theorem:
  `Stacks.Chow.firstChernCapRationallyCompatibleWithFlatPullback_invertible`, in
  `StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapCompatible`, proves it from
  tag 0EPJ itself, which this repository has as
  `Stacks.Chow.flatPullback_meromorphicDivisor_eq_sum_components`. So the conclusions below carry
  no unproved component hypothesis once they are read at an invertible module;
  `StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapPullback` does exactly that
  and is where Stacks 02SS is registered.
* `Stacks.Chow.FlatPullbackFactorsThroughRationalEquivalence` is
  [Stacks, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1), needed to have the map
  `f^* : A_k(X) ⟶ A_{k+r}(X')` of Stacks 0FVK at all. It is threaded in exactly this way
  throughout `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback` and
  `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic`.

Both are `Prop`s, so proof irrelevance makes the conclusions independent of which proof is
supplied; neither is a datum, and nothing below quantifies over a datum. The relative dimension
`Stacks.Chow.relativeDimension` enters only through the delta-dimension of an integral component,
so the dimension function of Stacks 02JW is not needed.

## Main definitions

* `Stacks.Chow.FirstChernCapRationallyCompatibleWithFlatPullback` — the component case of
  Stacks 02SS up to rational equivalence, with the equivalence carried on the preimage
  `f^{-1}(W)` of the component, which is the closed subscheme the source works on.

## Main results

* `Stacks.Chow.flatPullback_firstChernCapRule_rationallyEquivalent` — **Stacks 02SS at the level
  of cycles, up to rational equivalence**: the two cycles of Stacks 02SS are rationally
  equivalent as soon as they are rationally equivalent over each integral component.
* `Stacks.Chow.flatPullbackChow_firstChernClassCap_of_rationallyCompatible` — **Stacks 02SS**
  from the weaker component hypothesis.
* `Stacks.Chow.flatPullbackChow_firstChernClassCapOfInvertible` — **Stacks 02SS for an invertible
  module**: the cap products on both sides are those of Stacks 02SO for `L` and for `f^*L`, so no
  component rule is a parameter.
* `Stacks.Chow.flatPullbackChow_firstChernClassCapOfInvertible_of_base` — the same with the
  structure morphism of `X'` an independent morphism `sX` and `f ≫ sY = sX` a hypothesis, which
  is how the source states it.

## Implementation notes

### The sum over the components of a cycle

The proof of `Stacks.Chow.flatPullback_firstChernCapRule_rationallyEquivalent` writes the
difference of the two cycles of Stacks 02SS as a locally finite sum, indexed by the support of
`α`, of pushforwards along the closed immersions `f^{-1}(closure {x}) ⟶ X'`, and applies
Stacks 02RZ. The two ingredients are:

* the coefficientwise identities of
  `StacksFrontier.AlgebraicGeometry.Chow.ChernClasses.FlatPullback` — the left side reindexed over
  the fibres of `f` by `Stacks.Chow.finsum_finsum_mem_fiber`, the right side as a sum over the
  points of `X`. For a fixed point of `X'` both sums have **finite** support, by
  `Stacks.Chow.finite_support_inter_generalizations`, which is what lets them be subtracted
  termwise;
* local finiteness of the family `f^{-1}(closure {x})` for `x` in the support of `α`. The family
  `closure {x}` is locally finite by `Stacks.Chow.locallyFinite_closure_support`, and `f` is
  continuous, so `LocallyFinite.preimage_continuous` transports it.

The index type of Stacks 02RZ is forced to be `Type u`; the support of `α` is a subtype of the
carrier of `X`, so it is.

## References

* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 0EPJ](https://stacks.math.columbia.edu/tag/0EPJ)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
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

/-- Proper pushforward of cycles commutes with multiplication by an integer, read on
coefficients. It is additive as `Stacks.Chow.properPushforwardHom`. -/
private theorem coe_properPushforward_zsmul {Y Z : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (g : Y ⟶ Z) [IsProper g]
    (hg : g ≫ sZ = sY) (j : ℤ) (n : ℤ) (c : CycleGroup C sY j) (z : Z) :
    (properPushforward C sY sZ g hg j (n • c)).1 z
      = n * (properPushforward C sY sZ g hg j c).1 z := by
  rw [← properPushforwardHom_apply, map_zsmul, properPushforwardHom_apply]
  rfl

/-- Weighting the first Chern class component cycles at the points of a locally finite family by
integers, the coefficient at a fixed point is nonzero for only finitely many points. -/
private theorem finite_support_mul_firstChernComponentCycleAt {Y : Scheme.{u}} (q : Y ⟶ C.S)
    [LocallyOfFiniteType q] (j : ℤ) (R : FirstChernComponentCycleRule C q j) (c : Y → ℤ)
    (hc : LocallyFiniteSupport c) (y : Y) :
    (Function.support fun x : Y ↦ c x * (firstChernComponentCycleAt C q j R x).1 y).Finite := by
  refine (finite_support_inter_generalizations hc
    (isCompact_singleton (x := (𝟙 Y : Y ⟶ Y).base y))).subset fun x hx ↦ ?_
  replace hx : c x * (firstChernCapRule C q j R).toComponentRule.cycle x y ≠ 0 := hx
  exact ⟨⟨_, rfl, (firstChernCapRule C q j R).toComponentRule.mem_closure_of_apply_ne_zero x y
    (right_ne_zero_of_mul hx)⟩, left_ne_zero_of_mul hx⟩

omit [LocallyOfFiniteType f] [Flat f] in
/-- The support of the preimage `f^{-1}(W)` of the integral closed subscheme `W = closure {x}` is
the preimage of the closure of `x`. This is what makes the family of those preimages locally
finite when the family of the `closure {x}` is. -/
theorem coe_support_integralComponentPreimage (x : X) :
    (((integralComponentAt x).comap f).support : Set X') = f.base ⁻¹' closure {x} := by
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    coe_support_integralComponentAt]

/-- **The component case of Stacks 02SS, up to rational equivalence.** For every integral
component of `X` of delta-dimension `k + 1` — equivalently, for every point `x` of relative
dimension `k + 1` — the sum over the fibre `f^{-1}(x)` of the first Chern class component cycles
on `X'`, weighted by the flat pullback multiplicity, differs from the flat pullback of the
component cycle of `x` by a cycle rationally equivalent to zero **on the closed subscheme
`f^{-1}(closure {x})`**.

This is exactly what the source produces: its proof of the component case of Stacks 02SS ends by
exhibiting a rational equivalence on `f^{-1}(W)`, obtained from
[Stacks, Tag 0EPJ](https://stacks.math.columbia.edu/tag/0EPJ). The equivalence is required to
live on `f^{-1}(W)` and not merely on `X'`, because the equivalences over the various components
of a cycle are summed by Stacks 02RZ, which needs their carriers to form a locally finite family.

It is strictly weaker than `Stacks.Chow.FirstChernCapCompatibleWithFlatPullback`, and that is
the point: see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClasses.FlatPullbackInvertible` for why the equality of
cycles is unavailable at the component rules of an invertible module. -/
def FirstChernCapRationallyCompatibleWithFlatPullback : Prop :=
  ∀ x : X, relativeDimension C.dimensionFunction p x = k + 1 →
    ∃ a : CycleGroup C (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)),
      IsRationallyEquivalentToZero C
          (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)) a ∧
        ∀ y' : X',
          (∑ᶠ x' ∈ f.base ⁻¹' {x},
              flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
                (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) chern' x').1 y') -
            (flatPullback C (f ≫ p) p f rfl r hf k
              (firstChernComponentCycleAt C p k chern x)).1 y' =
          (properPushforward C (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (f ≫ p)
            ((integralComponentAt x).comap f).subschemeι rfl (k + (r : ℤ)) a).1 y'

/-- The equality of cycles over each integral component implies the rational equivalence over it,
by the zero rational equivalence. So the hypothesis of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClasses.FlatPullback` is the stronger of the two and
everything proved from it there is subsumed here. -/
theorem firstChernCapRationallyCompatibleWithFlatPullback_of_compatible
    (h : FirstChernCapCompatibleWithFlatPullback C p f r hf k chern chern') :
    FirstChernCapRationallyCompatibleWithFlatPullback C p f r hf k chern chern' := by
  intro x hx
  refine ⟨0, rationallyEquivalentToZero_zero _ _ _, fun y' ↦ ?_⟩
  rw [h x hx y', sub_self]
  simp

/-- **Stacks 02SS at the level of cycles, up to rational equivalence.** Granted the rational
equivalence over each integral component, the cap product cycle of a flat pullback and the flat
pullback of the cap product cycle are rationally equivalent.

The proof writes their difference as a locally finite sum, indexed by the support of `α`, of
pushforwards along the closed immersions `f^{-1}(closure {x}) ⟶ X'` of the rational equivalences
the hypothesis supplies, and applies Stacks 02RZ. At a fixed point of `X'` both coefficient sums
over the points of `X` have finite support, so they may be subtracted term by term. -/
theorem flatPullback_firstChernCapRule_rationallyEquivalent
    (hcomp : FirstChernCapRationallyCompatibleWithFlatPullback C p f r hf k chern chern')
    (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) (α : CycleGroup C p (k + 1)) :
    RationallyEquivalent C (f ≫ p) (k + (r : ℤ))
      ((firstChernCapRule C (f ≫ p) (k + (r : ℤ)) chern').extendCycleGroup
        (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1) α))
      (flatPullback C (f ≫ p) p f rfl r hf k
        ((firstChernCapRule C p k chern).extendCycleGroup α)) := by
  have hdim : ∀ i : ↥(Function.support (α.1 : X → ℤ)),
      relativeDimension C.dimensionFunction p (i : X) = k + 1 := fun i ↦
    (mem_cyclesOfDimension_iff_forall_point C p (k + 1) α.1).1 α.2 i i.2
  choose a ha hval using fun i : ↥(Function.support (α.1 : X → ℤ)) ↦ hcomp (i : X) (hdim i)
  refine rationallyEquivalentToZero_finsum_of_closedSupports C (f ≫ p) (k + (r : ℤ))
    (fun i : ↥(Function.support (α.1 : X → ℤ)) ↦ (integralComponentAt (i : X)).comap f) ?_
    (fun i ↦ (α.1 (i : X)) • a i)
    (fun i ↦ (rationalEquivalences C _ (k + (r : ℤ))).zsmul_mem (ha i) _) ?_
  · refine ((locallyFinite_closure_support α.1.locallyFiniteSupport).preimage_continuous
      f.continuous).subset fun i ↦ ?_
    rw [coe_support_integralComponentPreimage]
  · intro y'
    set β := flatPullback C (f ≫ p) p f rfl r hf (k + 1) α with hβ
    set R' := firstChernCapRule C (f ≫ p) (k + (r : ℤ)) chern' with hR'
    set R := firstChernCapRule C p k chern with hR
    set G : X' → ℤ := fun x' ↦ β.1 x' *
      (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) chern' x').1 y' with hG
    -- only the components of the pulled-back cycle passing through `y'` contribute
    have hGfin : (Function.support G).Finite :=
      finite_support_mul_firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) chern' β.1
        β.1.locallyFiniteSupport y'
    -- the left hand side, reindexed over the fibres of `f`
    have hLHS : (R'.extendCycleGroup (hcast ▸ β)).1 y' =
        ∑ᶠ x : X, ∑ᶠ x' ∈ f.base ⁻¹' {x}, G x' := by
      rw [finsum_finsum_mem_fiber f.base G hGfin,
        show (R'.extendCycleGroup (hcast ▸ β)).1 y' =
          R'.toComponentRule.extendCoeff (hcast ▸ β : CycleGroup C (f ≫ p) _).1 y' from rfl,
        val_cycleGroup_cast C (f ≫ p) hcast β]
      rfl
    -- the right hand side, as a locally finite sum over the points of `X`
    have hRHS : (flatPullback C (f ≫ p) p f rfl r hf k (R.extendCycleGroup α)).1 y' =
        ∑ᶠ x : X, α.1 x *
          (flatPullback C (f ≫ p) p f rfl r hf k
            (firstChernComponentCycleAt C p k chern x)).1 y' := by
      rw [flatPullback_apply,
        show (R.extendCycleGroup α).1 (f.base y') =
          ∑ᶠ x : X, α.1 x * (firstChernComponentCycleAt C p k chern x).1 (f.base y') from rfl,
        finsum_mul]
      exact finsum_congr fun x ↦ by rw [flatPullback_apply]; ring
    -- the coefficient at a point of the fibre over `x`
    have hGval : ∀ (x : X) (x' : X'), f.base x' = x → G x' = α.1 x *
        (flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
          (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) chern' x').1 y') := by
      intro x x' hx'
      have h1 : β.1 x' = α.1 x * flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' := by
        rw [hβ, flatPullback_apply, hx']
      simp only [hG]
      rw [h1, mul_assoc]
    -- both coefficient functions on `X` have finite support at `y'`, so they may be subtracted
    have hufin : Function.HasFiniteSupport
        (fun x : X ↦ ∑ᶠ x' ∈ f.base ⁻¹' {x}, G x') := by
      refine (hGfin.image f.base).subset fun x hx ↦ ?_
      by_contra hcon
      exact hx (finsum_mem_eq_zero_of_forall_eq_zero fun x' hx' ↦ by
        by_contra hG0
        exact hcon ⟨x', hG0, hx'⟩)
    have hvfin : Function.HasFiniteSupport
        (fun x : X ↦ α.1 x *
          (flatPullback C (f ≫ p) p f rfl r hf k
            (firstChernComponentCycleAt C p k chern x)).1 y') := by
      refine (finite_support_mul_firstChernComponentCycleAt C p k chern α.1
        α.1.locallyFiniteSupport (f.base y')).subset fun x hx ↦ ?_
      have hx0 : α.1 x * (flatPullback C (f ≫ p) p f rfl r hf k
          (firstChernComponentCycleAt C p k chern x)).1 y' ≠ 0 := hx
      rw [flatPullback_apply, ← mul_assoc] at hx0
      exact left_ne_zero_of_mul hx0
    have hdiff : (R'.extendCycleGroup (hcast ▸ β) -
          flatPullback C (f ≫ p) p f rfl r hf k (R.extendCycleGroup α)).1 y' =
        (∑ᶠ x : X, ∑ᶠ x' ∈ f.base ⁻¹' {x}, G x') -
          ∑ᶠ x : X, α.1 x *
            (flatPullback C (f ≫ p) p f rfl r hf k
              (firstChernComponentCycleAt C p k chern x)).1 y' := by
      rw [← hLHS, ← hRHS]; rfl
    rw [hdiff, ← finsum_sub_distrib hufin hvfin, ← finsum_mem_univ,
      finsum_mem_inter_support_eq' _ Set.univ (Function.support (α.1 : X → ℤ)) ?_,
      ← finsum_set_coe_eq_finsum_mem (Function.support (α.1 : X → ℤ))]
    · refine finsum_congr fun i ↦ ?_
      have h1 : ∑ᶠ x' ∈ f.base ⁻¹' {(i : X)}, G x' =
          α.1 (i : X) * ∑ᶠ x' ∈ f.base ⁻¹' {(i : X)},
            flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
              (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ)) chern' x').1 y' := by
        rw [mul_finsum_mem]
        exact finsum_mem_congr rfl fun x' hx' ↦ hGval (i : X) x' hx'
      rw [h1, ← mul_sub, hval i y', coe_properPushforward_zsmul]
    · intro x hx
      refine ⟨fun _ ↦ ?_, fun _ ↦ Set.mem_univ x⟩
      by_contra hcon
      replace hcon : α.1 x = 0 := by
        simpa only [Function.mem_support, not_not] using hcon
      refine hx ?_
      change (∑ᶠ x' ∈ f.base ⁻¹' {x}, G x') -
        α.1 x * (flatPullback C (f ≫ p) p f rfl r hf k
          (firstChernComponentCycleAt C p k chern x)).1 y' = 0
      rw [hcon, zero_mul, sub_zero]
      exact finsum_mem_eq_zero_of_forall_eq_zero fun x' hx' ↦ by
        rw [hGval x x' hx', hcon, zero_mul]

/-- **Stacks 02SS.** Intersection with the first Chern class commutes with flat pullback:
`c₁(f^*L) ∩ f^*α = f^*(c₁(L) ∩ α)` in `A_{k+r}(X')` for every `α ∈ Z_{k+1}(X)`, granted the
component case of the source up to rational equivalence.

This is `Stacks.Chow.flatPullbackChow_firstChernClassCap` with its component hypothesis weakened
to `Stacks.Chow.FirstChernCapRationallyCompatibleWithFlatPullback`, which is the form an
invertible module supplies. The conclusion is an equality of Chow classes, so the rational
equivalence of the two cycles is all that is needed. -/
theorem flatPullbackChow_firstChernClassCap_of_rationallyCompatible
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (f ≫ p) p f rfl r hf k)
    (hcomp : FirstChernCapRationallyCompatibleWithFlatPullback C p f r hf k chern chern')
    (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) (α : CycleGroup C p (k + 1)) :
    firstChernClassCap C (f ≫ p) (k + (r : ℤ)) chern'
        (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1) α) =
      flatPullbackChow C (f ≫ p) p f rfl r hf k hfac
        (firstChernClassCap C p k chern α) := by
  have h0 := flatPullback_firstChernCapRule_rationallyEquivalent C p f r hf k chern chern'
    hcomp hcast α
  change (QuotientAddGroup.mk ((firstChernCapRule C (f ≫ p) (k + (r : ℤ)) chern').extendCycleGroup
      (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1) α)) :
      chowGroup C (f ≫ p) (k + (r : ℤ))) =
    QuotientAddGroup.mk (flatPullback C (f ≫ p) p f rfl r hf k
      ((firstChernCapRule C p k chern).extendCycleGroup α))
  exact QuotientAddGroup.eq_iff_sub_mem.2 h0

/-- **Stacks 02SS for an invertible module.** Flat pullback commutes with the cap product by the
first Chern class of an invertible module:

  `f^*(c₁(L) ∩ α) = c₁(f^*L) ∩ f^*α`  in  `A_{k+r}(X')`,  for `α ∈ Z_{k+1}(X)`.

Both cap products are the one of Stacks 02SO at the component rule of the module,
`Stacks.Chow.firstChernClassCapOfInvertible`, so **no component rule is a parameter**: the
invertibility of `f^*L` that the right hand side needs is Stacks 0B8L, available here as an
instance. The degree transport `k + 1 + r = k + r + 1` is discharged rather than carried.

The two hypotheses are the component case of the source — Stacks 0EPJ, as
`Stacks.Chow.FirstChernCapRationallyCompatibleWithFlatPullback` at the two component rules — and
the vanishing of Stacks 02S1 that `Stacks.Chow.flatPullbackChow` needs. Both are `Prop`s. Only
the second is unproved: the first is
`Stacks.Chow.firstChernCapRationallyCompatibleWithFlatPullback_invertible`, which is what
`Stacks.Chow.flatPullbackChow_firstChernClassCapOfInvertible_of_invertible` supplies here. -/
theorem flatPullbackChow_firstChernClassCapOfInvertible (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (f ≫ p) p f rfl r hf k)
    (hcomp : FirstChernCapRationallyCompatibleWithFlatPullback C p f r hf k
      (firstChernComponentCycleRule C p k L)
      (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L)))
    (α : CycleGroup C p (k + 1)) :
    flatPullbackChow C (f ≫ p) p f rfl r hf k hfac
        (firstChernClassCapOfInvertible C p k L α) =
      firstChernClassCapOfInvertible C (f ≫ p) (k + (r : ℤ))
        ((Scheme.Modules.pullback f).obj L)
        ((show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 by omega) ▸
          flatPullback C (f ≫ p) p f rfl r hf (k + 1) α) :=
  (flatPullbackChow_firstChernClassCap_of_rationallyCompatible C p f r hf k _ _ hfac hcomp
    (by omega) α).symm

/-- **Stacks 02SS for an invertible module**, with the structure morphism of the source an
independent morphism `sX` and the factorisation `g ≫ sY = sX` a hypothesis, which is how the
source states it. Both base morphisms being locally of finite type is a `Prop`, so substituting
the factorisation costs nothing. -/
theorem flatPullbackChow_firstChernClassCapOfInvertible_of_base
    {Y : Scheme.{u}} (sX : X' ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (g : X' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (hbase : g ≫ sY = sX) (s : ℕ) (hg : AlgebraicGeometry.RelativeDimension g s) (j : ℤ)
    (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX sY g hbase s hg j)
    (hcomp : FirstChernCapRationallyCompatibleWithFlatPullback C sY g s hg j
      (firstChernComponentCycleRule C sY j L)
      (firstChernComponentCycleRule C (g ≫ sY) (j + (s : ℤ))
        ((Scheme.Modules.pullback g).obj L)))
    (α : CycleGroup C sY (j + 1)) :
    flatPullbackChow C sX sY g hbase s hg j hfac
        (firstChernClassCapOfInvertible C sY j L α) =
      firstChernClassCapOfInvertible C sX (j + (s : ℤ)) ((Scheme.Modules.pullback g).obj L)
        ((show j + 1 + (s : ℤ) = j + (s : ℤ) + 1 by omega) ▸
          flatPullback C sX sY g hbase s hg (j + 1) α) := by
  subst hbase
  exact flatPullbackChow_firstChernClassCapOfInvertible C sY g s hg j L hfac hcomp α

end Stacks.Chow

end
