module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The self-intersection formula

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `L` be an invertible `𝒪_X`-module and let `s ∈ Γ(X, L)` be a global section with
zero scheme `i : D = Z(s) ⟶ X`. The self-intersection formula computes the composite of the
Gysin map of `D` with the pushforward along `i`:

  `i^* i_* α = c₁(L|_D) ∩ α`  in  `A_k(D)`,  for `α ∈ Z_{k+1}(D)`.

Nothing is carried as a hypothesis: the Gysin map is the one of
[Stacks, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8) at the first Chern class component
rule of `L`, the right hand side is the cap product of
[Stacks, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO) at the component rule of `L|_D`,
and both rules are functions of the module alone.

## The proof

The source's proof reads the identity off the definition of `i_*` on cycles and the definition of
`i^*`: every integral component of a cycle on `D` is contained in the zero scheme, so the Gysin
map evaluates on `i_* α` by the contained-component rule — the first Chern class of the
restriction of `L` — and that is the component rule of the cap product on `D`.

Here the two rules are not literally the same function, because each chooses its own meromorphic
section on its own presentation of the component, so the proof is in two steps.

* At the level of **cycles** the Gysin extension of `i_* α` is the cap product extension of `α`
  for the rule on `D` *transported* from `X` —
  `Stacks.Chow.pullbackComponentRule` applied to the rule `W ↦ Quotient.out (c₁(L|_W) ∩ [W])`,
  which is the very representative the contained-component rule of Tag 02T8 pushes forward. This
  is `Stacks.Chow.gysinRule_extendCycleGroup_properPushforward_eq`, and it is an equality of
  cycle coefficients: the two sides are the same locally finite sum, reindexed over the fibres of
  `i` by `Stacks.Chow.ComponentRule.extendCoeff_map_apply`, with pushforward weight one because
  `i` is a closed immersion.
* The transported rule and the component rule of `L|_D` agree in the Chow group of each integral
  component of `D`, which is
  `Stacks.Chow.rationallyEquivalent_firstChernComponentCycleRule_pullbackComponentRule`
  composed with `Quotient.mk ∘ Quotient.out = id`, and
  `Stacks.Chow.firstChernClassCap_congr` turns that into equality of the two cap products.

## Degrees

The source writes the composite as `CH_k(D) ⟶ CH_{k-1}(D)`. Here the input degree is `k + 1` and
the output degree is `k`, so that the degree-lowering operations compose without casts, as in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCap`.

## Main definitions

* `Stacks.Chow.gysinOutComponentCycleRule` — the cycle-valued rule `W ↦ Quotient.out (c₁(L|_W) ∩
  [W])` whose pushforward is the contained-component rule of Tag 02T8.

## Main results

* `Stacks.Chow.gysinRule_extendCycleGroup_properPushforward_eq` — the identity at the level of
  cycles, for the transported rule.
* `Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι` — the
  self-intersection formula.

## Implementation notes

### The pushforward is taken on cycles

The source states the composite on `CH_k(D)`, which presupposes that `i^*` descends to Chow
groups; that descent is
[Stacks, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO) and is not available here. The
identity below is the one the source's proof establishes: `i_*` is proper pushforward of
*cycles*, and the conclusion is an equality of classes in `A_k(D)`. The attribute therefore
carries a part descriptor naming that reading; no hypothesis is carried.

### Why the two component rules are compared and not identified

For an integral closed subscheme `V ⊆ D` of delta-dimension `k + 1`, the Gysin rule on `X` works
with the scheme-theoretic image `V.map i ⊆ X` and the restriction of `L` along
`(V.map i) ⟶ X`, while the cap product rule on `D` works with `V` and the restriction of `L|_D`
along `V ⟶ D`. The two schemes are isomorphic and the two modules correspond, but each rule
chooses a nonzero meromorphic section independently, so the divisor *cycles* differ. They have
the same class, by
[Stacks, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ) (2), and that is what
`Stacks.Chow.rationallyEquivalent_firstChernComponentCycleRule_pullbackComponentRule` records.
A second rational equivalence is needed for the same reason on the Gysin side:
`Stacks.Chow.gysinComponentCycle` pushes forward `Quotient.out` of a class, an arbitrary
representative, and `Quotient.out` is constrained only by `Quotient.mk ∘ Quotient.out = id`.
Carrying both comparisons through the locally infinite sum a cycle may be is what
`Stacks.Chow.firstChernClassCap_congr` does, by Tag 02RZ.

### Stacks 02S2 is discharged, not assumed

The only morphisms pushed along are closed immersions and an isomorphism of components, and for
an arbitrary proper morphism over the base Tag 02S2 is proved outright as
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence`, so no vanishing hypothesis is
carried.

## References

* [Stacks Project, Tag 0F95](https://stacks.math.columbia.edu/tag/0F95)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
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

/-! ### The representative the contained-component rule of Tag 02T8 pushes forward -/

/-- The cycle-valued component rule whose value on an integral closed subscheme `W ⊆ X` of
delta-dimension `k + 1` is the representative `Quotient.out` of the first Chern class
`c₁(L|_W) ∩ [W]` in `A_k(W)`.

This is exactly the cycle that the contained-component rule of
[Stacks, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8) pushes forward into the zero
scheme; see `Stacks.Chow.gysinComponentCycle_of_le`. It is rationally equivalent to the divisor
cycle the component rule of Tag 02SO chose, but not equal to it. -/
def gysinOutComponentCycleRule : FirstChernComponentCycleRule C p k := fun W hW hDim =>
  Quotient.out (firstChernComponentClass C p k L W hW hDim)

/-- The representative is rationally equivalent to the divisor cycle the component rule of
Tag 02SO chose: it represents the same class, by `Quotient.mk ∘ Quotient.out = id`. -/
theorem rationallyEquivalent_gysinOutComponentCycleRule (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    RationallyEquivalent C (W.subschemeι ≫ p) k
      (gysinOutComponentCycleRule C p k L W hW hDim)
      (firstChernComponentCycleRule C p k L W hW hDim) :=
  QuotientAddGroup.eq_iff_sub_mem.mp
    ((Quotient.out_eq _).trans (firstChernComponentClass_eq_mk C p k L W hW hDim))

/-! ### Every integral component of the zero scheme is contained in it -/

/-- The integral closed subscheme of `X` through the image of a point of the zero scheme is
contained in the zero scheme: its support is the closure of a point of the closed set underlying
`D`, hence lies in that set. Ideal sheaves are ordered oppositely to their closed subschemes, so
the containment is the inequality `D ≤ closure {i x}`. -/
theorem zeroScheme_le_integralComponentAt_subschemeι_base
    (x : (Stacks.Divisors.zeroScheme X L s).subscheme) :
    Stacks.Divisors.zeroScheme X L s ≤
      integralComponentAt ((Stacks.Divisors.zeroScheme X L s).subschemeι.base x) := by
  have hmem : (Stacks.Divisors.zeroScheme X L s).subschemeι.base x ∈
      ((Stacks.Divisors.zeroScheme X L s).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨x, rfl⟩
  have hsub : ((Closeds.closure
        ({(Stacks.Divisors.zeroScheme X L s).subschemeι.base x} : Set X) : Closeds X) : Set X) ⊆
      ((Stacks.Divisors.zeroScheme X L s).support : Set X) := by
    rw [Closeds.coe_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hmem)
      (Stacks.Divisors.zeroScheme X L s).support.isClosed
  exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
    (SetLike.coe_subset_coe.mp hsub)

/-! ### The component comparison -/

/-- **The component identity.** At a point `x` of the zero scheme of relative dimension `k + 1`,
the Gysin component cycle of Tag 02T8 attached to the image of `x` in `X` is the cap product
component cycle on `D` attached to `x` by the transported rule.

Both are the pushforward into `D` of one and the same cycle on the scheme-theoretic image
`(closure {x}).map i`: the Gysin side pushes along the inclusion of that closed subscheme of `D`,
the cap product side along the inverse of the component isomorphism followed by
`closure {x} ⟶ D`, and the two morphisms agree because `i` is a monomorphism. -/
theorem gysinComponentCycleAt_base_eq_firstChernComponentCycleAt
    (x : (Stacks.Divisors.zeroScheme X L s).subscheme)
    (hx : relativeDimension C.dimensionFunction
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) x = k + 1) :
    gysinComponentCycleAt C p k L s (firstChernComponentClass C p k L)
        ((Stacks.Divisors.zeroScheme X L s).subschemeι.base x) =
      firstChernComponentCycleAt C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
        (pullbackComponentRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
          (gysinOutComponentCycleRule C p k L)) x := by
  have hV : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hDimV : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)) = ((k + 1 : ℤ) : EInt) :=
    schemeDeltaDimension_integralComponentAt_of_eq C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) hx
  have hW : IsIntegral
      ((integralComponentAt x).map (Stacks.Divisors.zeroScheme X L s).subschemeι).subscheme :=
    isIntegral_subscheme_map (Stacks.Divisors.zeroScheme X L s).subschemeι _ hV
  have hDimW : schemeDeltaDimension C
      (((integralComponentAt x).map
        (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt) :=
    schemeDeltaDimension_subscheme_map C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
      (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k _ hV hDimV
  have hle : Stacks.Divisors.zeroScheme X L s ≤
      (integralComponentAt x).map (Stacks.Divisors.zeroScheme X L s).subschemeι := by
    rw [← ChernCap42.integralComponentAt_comp (Stacks.Divisors.zeroScheme X L s).subschemeι x]
    exact zeroScheme_le_integralComponentAt_subschemeι_base L s x
  -- the Gysin side, as the pushforward of the representative along the inclusion
  have hAt : gysinComponentCycleAt C p k L s (firstChernComponentClass C p k L)
      ((Stacks.Divisors.zeroScheme X L s).subschemeι.base x) =
      gysinComponentCycle C p k L s (firstChernComponentClass C p k L)
        ((integralComponentAt x).map (Stacks.Divisors.zeroScheme X L s).subschemeι)
        hW hDimW := by
    apply Subtype.ext
    change (gysinRule C p k L s (firstChernComponentClass C p k L)).totalize
      (integralComponentAt ((Stacks.Divisors.zeroScheme X L s).subschemeι.base x)) = _
    rw [ChernCap42.integralComponentAt_comp (Stacks.Divisors.zeroScheme X L s).subschemeι x]
    exact (gysinRule C p k L s (firstChernComponentClass C p k L)).totalize_eq _ _ _
  -- the two morphisms into `D` agree, `i` being a monomorphism
  have hmor : Scheme.IdealSheafData.inclusion hle =
      (imageIsoOfIsClosedImmersion (Stacks.Divisors.zeroScheme X L s).subschemeι
        (integralComponentAt x)).inv ≫ (integralComponentAt x).subschemeι := by
    rw [← cancel_mono (Stacks.Divisors.zeroScheme X L s).subschemeι,
      Scheme.IdealSheafData.inclusion_subschemeι, Category.assoc,
      ← imageIsoOfIsClosedImmersion_hom_subschemeι
        (Stacks.Divisors.zeroScheme X L s).subschemeι (integralComponentAt x),
      Iso.inv_hom_id_assoc]
  rw [hAt, gysinComponentCycle_of_le C p k L s (firstChernComponentClass C p k L) _ hW hDimW hle,
    firstChernComponentCycleAt_eq C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k _ hx,
    firstChernComponentCycle_pullbackComponentRule C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
      (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
      (gysinOutComponentCycleRule C p k L) _ hV hDimV]
  exact properPushforward_hom_congr C
    (((integralComponentAt x).map
      (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι ≫ p)
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) hmor _ _ k _

/-! ### The identity at the level of cycles -/

/-- **The self-intersection formula at the level of cycles, for the transported rule.** The Gysin
extension of the pushforward along `i` of a `(k+1)`-cycle `α` on `D` is the cap product extension
of `α` for the rule on `D` transported from `X`.

Both sides are locally finite sums over the integral components of `α`:
`Stacks.Chow.ComponentRule.extendCoeff_map_apply` turns the left side into a sum over the fibres
of `i`, which is where properness of `i` is used, the pushforward weight of a closed immersion is
one, and `Stacks.Chow.gysinComponentCycleAt_base_eq_firstChernComponentCycleAt` matches the
terms. Only the points carrying a nonzero coefficient of `α` are compared, and those have
relative dimension `k + 1` because `α` is a `(k+1)`-cycle. -/
theorem gysinRule_extendCycleGroup_properPushforward_eq
    (α : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (k + 1)) :
    (gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup
        (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1) α) =
      (firstChernCapRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
        (pullbackComponentRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
          (gysinOutComponentCycleRule C p k L))).extendCycleGroup α := by
  refine Subtype.ext <| Function.locallyFinsuppWithin.ext fun y ↦ ?_
  set i := (Stacks.Divisors.zeroScheme X L s).subschemeι
  have hcpt : IsCompact (i.base ⁻¹' {i.base y}) :=
    i.isProperMap.isCompact_preimage isCompact_singleton
  have hLHS : ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup
      (properPushforward C (i ≫ p) p i rfl (k + 1) α)).1 y =
      ∑ᶠ x : (Stacks.Divisors.zeroScheme X L s).subscheme, α.1 x *
        pushforwardWeight C (i ≫ p) p i x *
        (gysinComponentCycleAt C p k L s (firstChernComponentClass C p k L) (i.base x)).1 y := by
    rw [show ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup
        (properPushforward C (i ≫ p) p i rfl (k + 1) α)).1 y =
      (gysinRule C p k L s (firstChernComponentClass C p k L)).toComponentRule.extendCoeff
        (Function.locallyFinsupp.map i.base (pushforwardWeight C (i ≫ p) p i)
          i.isSpectralMap α.1) y from rfl,
      ComponentRule.extendCoeff_map_apply _ i.isSpectralMap i.isProperMap.isClosedMap _ _ y hcpt]
    exact finsum_congr fun _ ↦ rfl
  have hRHS : ((firstChernCapRule C (i ≫ p) k
      (pullbackComponentRule C (i ≫ p) p i rfl k
        (gysinOutComponentCycleRule C p k L))).extendCycleGroup α).1 y =
      ∑ᶠ x : (Stacks.Divisors.zeroScheme X L s).subscheme, α.1 x *
        (firstChernComponentCycleAt C (i ≫ p) k
          (pullbackComponentRule C (i ≫ p) p i rfl k
            (gysinOutComponentCycleRule C p k L)) x).1 y := rfl
  rw [hLHS, hRHS]
  refine finsum_congr fun x ↦ ?_
  by_cases hx : α.1 x = 0
  · simp [hx]
  · rw [pushforwardWeight_eq_one_of_isClosedImmersion C (i ≫ p) p i rfl x, mul_one,
      gysinComponentCycleAt_base_eq_firstChernComponentCycleAt C p k L s x
        ((mem_cyclesOfDimension_iff_forall_point C (i ≫ p) (k + 1) α.1).1 α.2 x hx)]

/-! ### The comparison of the transported rule with the component rule of `L|_D` -/

/-- **The two component rules on `D` agree in the Chow group of every integral component.** On an
integral closed subscheme `V ⊆ D` of delta-dimension `k + 1`, the rule transported from `X` and
the component rule of the restriction `L|_D` have the same class in `A_k(V)`.

Two rational equivalences are composed. On the scheme-theoretic image `V.map i ⊆ X` the
representative `Quotient.out` is rationally equivalent to the divisor cycle the rule of `L` chose
(`Stacks.Chow.rationallyEquivalent_gysinOutComponentCycleRule`), and pushing that forward along
the component isomorphism preserves rational equivalence by Tag 02S2. The transported rule of `L`
is then compared with the rule of `L|_D` by
`Stacks.Chow.rationallyEquivalent_firstChernComponentCycleRule_pullbackComponentRule`, which is
Tag 02SJ (2). -/
theorem rationallyEquivalent_pullbackComponentRule_gysinOut
    (V : (Stacks.Divisors.zeroScheme X L s).subscheme.IdealSheafData)
    (hV : IsIntegral V.subscheme)
    (hDim : schemeDeltaDimension C
      (V.subschemeι ≫ ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)) =
        ((k + 1 : ℤ) : EInt)) :
    RationallyEquivalent C
      (V.subschemeι ≫ ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)) k
      (pullbackComponentRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
        (gysinOutComponentCycleRule C p k L) V hV hDim)
      (firstChernComponentCycleRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
        ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L)
        V hV hDim) := by
  have h₁ : RationallyEquivalent C
      (V.subschemeι ≫ ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)) k
      (pullbackComponentRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
        (gysinOutComponentCycleRule C p k L) V hV hDim)
      (pullbackComponentRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
        (firstChernComponentCycleRule C p k L) V hV hDim) :=
    properPushforward_rationallyEquivalent C
      ((V.map (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι ≫ p)
      (V.subschemeι ≫ ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p))
      (imageIsoOfIsClosedImmersion (Stacks.Divisors.zeroScheme X L s).subschemeι V).inv
      (imageIsoOfIsClosedImmersion_inv_comp_base C
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl V) k
      (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion _ C _ _ _ k)
      (rationallyEquivalent_gysinOutComponentCycleRule C p k L _ _ _)
  have h₃ := (rationalEquivalences C
    (V.subschemeι ≫ ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)) k).sub_mem h₁
    (rationallyEquivalent_firstChernComponentCycleRule_pullbackComponentRule C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
      (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k L V hV hDim)
  rwa [sub_sub_sub_cancel_right] at h₃

/-! ### The self-intersection formula -/

/-- **The self-intersection formula.** For the Gysin map of the zero scheme `i : D = Z(s) ⟶ X` of
a global section of an invertible module `L`, the composite with the pushforward along `i` is
intersection with the first Chern class of the restriction `L|_D`:

  `i^* i_* α = c₁(L|_D) ∩ α`  in  `A_k(D)`,  for `α ∈ Z_{k+1}(D)`.

Both operations are functions of `L` and `s` alone: the Gysin map is
`Stacks.Chow.gysinHomomorphismOfInvertible` (Tag 02T8) and the right hand side is the cap product
`Stacks.Chow.firstChernClassCapOfInvertible` (Tag 02SO) of the restricted module, which is
invertible by Tag 0B8L. No hypothesis is carried; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.SelfIntersectionFormula`. -/
@[stacks 0F95 "the identity i^* i_* α = c₁(L|_D) ∩ α in A_k(D), with i_* taken on cycles as in \
the source's proof", sga "5 VII 9.2" "Codimension d = 1"]
theorem gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι
    (α : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (k + 1)) :
    gysinHomomorphismOfInvertible C p k L s
        (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1) α) =
      firstChernClassCapOfInvertible C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
        ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L) α := by
  have hL : gysinHomomorphismOfInvertible C p k L s
      (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1) α) =
      firstChernClassCap C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
        (pullbackComponentRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
          (gysinOutComponentCycleRule C p k L)) α :=
    congrArg QuotientAddGroup.mk
      (gysinRule_extendCycleGroup_properPushforward_eq C p k L s α)
  exact hL.trans (firstChernClassCap_congr C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
    (pullbackComponentRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
      (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k (gysinOutComponentCycleRule C p k L))
    (firstChernComponentCycleRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L))
    (rationallyEquivalent_pullbackComponentRule_gysinOut C p k L s) α)

end Stacks.Chow

end
