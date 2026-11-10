module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentRule
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow

/-!
# Proper pushforward and the first Chern class cap product

Let `X` and `Y` be schemes locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project, let `p : X ⟶ Y` be proper over `S` and let `L` be an invertible module on `Y`.
Stacks 02SU is the projection formula

  `p_*(c₁(p^*L) ∩ α) = c₁(L) ∩ p_*α`  in  `A_k(Y)`,  for `α ∈ Z_{k+1}(X)`.

This file shows that the projection formula on integral components implies the projection
formula on all cycles, at the level of cycles rather than of classes. The cap products on `X`
and on `Y` are built from component rules `chernX` and `chernY` (the component input of
Stacks 02SO), and the formula on integral components is the hypothesis
`Stacks.Chow.FirstChernCapCompatibleWithPushforward`.

## Main definitions

* `Stacks.Chow.pushforwardWeight` — the weight with which a point of `X` enters the proper
  pushforward of a cycle: the degree of the residue field extension when the delta-dimension is
  preserved, and zero otherwise.
* `Stacks.Chow.firstChernComponentCycleAt` — the component cycle of Stacks 02SO attached to a
  *point* of `X` rather than to an integral closed subscheme, the two being the same datum.
* `Stacks.Chow.FirstChernCapCompatibleWithPushforward` — the projection formula of Stacks 02SU on
  integral components, at the level of cycle coefficients.

## Main results

* `Stacks.Chow.properPushforward_firstChernCapRule_extendCycleGroup` — the projection formula at
  the level of **cycles**: granted the formula on integral components, the pushforward of the
  cap product cycle is the cap product cycle of the pushforward.
* `Stacks.Chow.properChowPushforward_firstChernClassCap` — the same formula read through proper
  pushforward on Chow groups.
* `Stacks.Chow.firstChernCapCompatibleWithPushforward_of_components` — the hypothesis, restated
  on integral closed subschemes rather than on points.
* `Stacks.Chow.pushforwardWeight_eq_one_of_isClosedImmersion`,
  `Stacks.Chow.properChowPushforward_firstChernClassCap_of_isClosedImmersion` — the case of a
  closed immersion, where the pushforward weight is identically one so that the hypothesis takes
  the unweighted form `p_*(c(x)) = c'(p x)`.

## Implementation notes

The component rules `chernX` and `chernY` of the cap product on `X` and on `Y` are explicit,
independent parameters, linked only by the compatibility hypothesis
`Stacks.Chow.FirstChernCapCompatibleWithPushforward`. They are *cycle*-valued rather than
class-valued, since the component formula of Stacks 02SO is an equality of cycle coefficients.
The vanishing of Stacks 02S2, needed to define the map `p_* : A_k(X) ⟶ A_k(Y)` of Stacks 0GU8, is
the explicit hypothesis of `Stacks.Chow.properChowPushforward`.

## References

* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The weight of a point under proper pushforward -/

/-- The weight with which a point `x` of `X` contributes to the proper pushforward of a cycle
along `p : X ⟶ Y`: the degree of the residue field extension `κ(x)/κ(p x)` when `p` preserves the
delta-dimension at `x`, and zero when it drops it, as in the coefficient formula of
Stacks 02R4. -/
def pushforwardWeight (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) (x : X) : ℤ :=
  (AlgebraicCycle.mapCoeff p (relativeDimension C.dimensionFunction sX)
    (relativeDimension C.dimensionFunction sY) x : ℤ)

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y)

/-- A point at which the proper morphism drops the delta-dimension contributes nothing to the
pushforward. -/
theorem pushforwardWeight_eq_zero {x : X} (hx : relativeDimension C.dimensionFunction sX x ≠
    relativeDimension C.dimensionFunction sY (p.base x)) :
    pushforwardWeight C sX sY p x = 0 := by
  simp [pushforwardWeight, AlgebraicCycle.mapCoeff, hx]

/-- A point at which the proper morphism preserves the delta-dimension and induces an isomorphism
of residue fields contributes with weight one. -/
theorem pushforwardWeight_eq_one {x : X} (hdim : relativeDimension C.dimensionFunction sX x =
    relativeDimension C.dimensionFunction sY (p.base x)) (hdeg : p.residueDegree x = 1) :
    pushforwardWeight C sX sY p x = 1 := by
  simp [pushforwardWeight, AlgebraicCycle.mapCoeff, hdim, hdeg]

/-- The coefficient formula for proper pushforward, in the shape
`Function.locallyFinsupp.map` of `Stacks.Chow.pushforwardWeight`. -/
theorem properPushforward_apply_eq_map [IsProper p] (hp : p ≫ sY = sX) (k : ℤ)
    (c : CycleGroup C sX k) (y : Y) :
    (properPushforward C sX sY p hp k c).1 y =
      Function.locallyFinsupp.map p.base (pushforwardWeight C sX sY p) p.isSpectralMap c.1 y :=
  rfl

/-! ### The component cycle at a point -/

section ComponentCycleAt

/-- The delta-dimension of the integral closed subscheme attached to a point is the relative
dimension of that point. -/
theorem schemeDeltaDimension_integralComponentAt (q : X ⟶ C.S) [LocallyOfFiniteType q] (x : X) :
    schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ q) =
      ((relativeDimension C.dimensionFunction q x : ℤ) : EInt) := by
  have _ : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  rw [schemeDeltaDimension_eq_genericPoint C ((integralComponentAt x).subschemeι ≫ q),
    relativeDimension_comp_closedImmersion]
  exact congrArg (fun z : ℤ ↦ (z : EInt))
    (congrArg (relativeDimension C.dimensionFunction q) (genericPointOf_integralComponentAt x))

variable (q : X ⟶ C.S) [LocallyOfFiniteType q] (k : ℤ) (chern : FirstChernComponentCycleRule C q k)

/-- The component cycle of Stacks 02SO attached to a *point* of `X`: the cycle the rule attaches
to the integral closed subscheme `closure {x}`, extended by zero when that subscheme does not have
delta-dimension `k + 1`. -/
def firstChernComponentCycleAt (x : X) : CycleGroup C q k :=
  ⟨(firstChernCapRule C q k chern).totalize (integralComponentAt x),
    (firstChernCapRule C q k chern).totalize_mem_cyclesOfDimension _⟩

/-- At the generic point of an integral closed subscheme of delta-dimension `k + 1`, the
point-indexed component cycle is the component cycle of that subscheme. -/
theorem firstChernComponentCycleAt_genericPointOf (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ q) = ((k + 1 : ℤ) : EInt)) :
    firstChernComponentCycleAt C q k chern (genericPointOf W hW) =
      firstChernComponentCycle C q k chern W hW hDim := by
  apply Subtype.ext
  change (firstChernCapRule C q k chern).totalize (integralComponentAt (genericPointOf W hW)) = _
  rw [integralComponentAt_genericPointOf W hW]
  exact (firstChernCapRule C q k chern).totalize_eq W hW hDim

end ComponentCycleAt

/-! ### The projection formula on integral components -/

section Proper

variable [IsProper p] (hp : p ≫ sY = sX) (k : ℤ) (chernX : FirstChernComponentCycleRule C sX k)
  (chernY : FirstChernComponentCycleRule C sY k)

/-- **The projection formula of Stacks 02SU on integral components.** The assertion that for
every integral component of `X` of delta-dimension `k + 1` — equivalently, for every point `x` of
relative dimension `k + 1` — the proper pushforward of the component cycle attached to it by
`chernX` is the component cycle attached by `chernY` to its image, weighted by
`Stacks.Chow.pushforwardWeight`, as an equality of cycle coefficients. -/
def FirstChernCapCompatibleWithPushforward : Prop :=
  ∀ x : X, relativeDimension C.dimensionFunction sX x = k + 1 → ∀ y : Y,
    (properPushforward C sX sY p hp k (firstChernComponentCycleAt C sX k chernX x)).1 y =
      pushforwardWeight C sX sY p x *
        (firstChernComponentCycleAt C sY k chernY (p.base x)).1 y

/-- The compatibility of the component rules along `p`, restated on integral closed subschemes of
`X` instead of on points. -/
theorem firstChernCapCompatibleWithPushforward_of_components
    (h : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt)) (y : Y),
      (properPushforward C sX sY p hp k (firstChernComponentCycle C sX k chernX W hW hDim)).1 y =
        pushforwardWeight C sX sY p (genericPointOf W hW) *
          (firstChernComponentCycleAt C sY k chernY
            (p.base (genericPointOf W hW))).1 y) :
    FirstChernCapCompatibleWithPushforward C sX sY p hp k chernX chernY := by
  intro x hdim y
  have hW : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hDim : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ sX) =
      ((k + 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_integralComponentAt C sX x, hdim]
  have hx : genericPointOf (integralComponentAt x) hW = x := genericPointOf_integralComponentAt x
  have h' := h (integralComponentAt x) hW hDim y
  rwa [← firstChernComponentCycleAt_genericPointOf C sX k chernX _ hW hDim, hx] at h'

/-! ### The projection formula -/

/-- **The projection formula, at the level of cycles.** Granted the projection formula on
integral components, the proper pushforward of the cycle representing `c₁(p^*L) ∩ α` is the cycle
representing `c₁(L) ∩ p_*α`. -/
theorem properPushforward_firstChernCapRule_extendCycleGroup
    (hcomp : FirstChernCapCompatibleWithPushforward C sX sY p hp k chernX chernY)
    (α : CycleGroup C sX (k + 1)) :
    properPushforward C sX sY p hp k ((firstChernCapRule C sX k chernX).extendCycleGroup α) =
      (firstChernCapRule C sY k chernY).extendCycleGroup
        (properPushforward C sX sY p hp (k + 1) α) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  have hcpt : IsCompact (p.base ⁻¹' {y}) :=
    p.isProperMap.isCompact_preimage isCompact_singleton
  have hLHS : (properPushforward C sX sY p hp k
      ((firstChernCapRule C sX k chernX).extendCycleGroup α)).1 y =
      ∑ᶠ x : X, α.1 x *
        (properPushforward C sX sY p hp k (firstChernComponentCycleAt C sX k chernX x)).1 y := by
    rw [properPushforward_apply_eq_map,
      show ((firstChernCapRule C sX k chernX).extendCycleGroup α).1 =
        (firstChernCapRule C sX k chernX).toComponentRule.extendCycle
          (𝟙 X : X ⟶ X).continuous α.1 from rfl,
      ComponentRule.map_extendCycle_apply _ _ _ _ _ hcpt]
    exact finsum_congr fun _ ↦ rfl
  have hRHS : ((firstChernCapRule C sY k chernY).extendCycleGroup
      (properPushforward C sX sY p hp (k + 1) α)).1 y =
      ∑ᶠ x : X, α.1 x * pushforwardWeight C sX sY p x *
        (firstChernComponentCycleAt C sY k chernY (p.base x)).1 y := by
    have hcpt' : IsCompact (p.base ⁻¹' {(𝟙 Y : Y ⟶ Y).base y}) := by simpa using hcpt
    rw [show ((firstChernCapRule C sY k chernY).extendCycleGroup
        (properPushforward C sX sY p hp (k + 1) α)).1 y =
      (firstChernCapRule C sY k chernY).toComponentRule.extendCoeff
        (Function.locallyFinsupp.map p.base (pushforwardWeight C sX sY p) p.isSpectralMap α.1)
        y from rfl,
      ComponentRule.extendCoeff_map_apply _ _ p.isProperMap.isClosedMap _ _ _ hcpt']
    exact finsum_congr fun _ ↦ rfl
  rw [hLHS, hRHS]
  refine finsum_congr fun x ↦ ?_
  by_cases hx : α.1 x = 0
  · rw [hx, zero_mul, zero_mul, zero_mul]
  · rw [hcomp x ((mem_cyclesOfDimension_iff_forall_point C sX (k + 1) α.1).1 α.2 x hx) y]
    ring

/-- **The projection formula.** Granted the projection formula on integral components, proper
pushforward on Chow groups commutes with intersecting with a first Chern class:
`p_*(c₁(p^*L) ∩ α) = c₁(L) ∩ p_*α` in `A_k(Y)` for every `α ∈ Z_{k+1}(X)`. -/
theorem properChowPushforward_firstChernClassCap
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k)
    (hcomp : FirstChernCapCompatibleWithPushforward C sX sY p hp k chernX chernY)
    (α : CycleGroup C sX (k + 1)) :
    properChowPushforward C sX sY p hp k hfac (firstChernClassCap C sX k chernX α) =
      firstChernClassCap C sY k chernY (properPushforward C sX sY p hp (k + 1) α) := by
  change properChowPushforward C sX sY p hp k hfac
    (QuotientAddGroup.mk' (rationalEquivalences C sX k)
      ((firstChernCapRule C sX k chernX).extendCycleGroup α)) = _
  rw [properChowPushforward_mk,
    properPushforward_firstChernCapRule_extendCycleGroup C sX sY p hp k chernX chernY hcomp α]
  rfl

end Proper

/-! ### The case of a closed immersion -/

section ClosedImmersion

variable [IsClosedImmersion p] (hp : p ≫ sY = sX) (k : ℤ)
  (chernX : FirstChernComponentCycleRule C sX k) (chernY : FirstChernComponentCycleRule C sY k)

include hp

/-- A closed immersion over the base has pushforward weight one at every point: it preserves the
relative dimension, and its residue degree is one. -/
theorem pushforwardWeight_eq_one_of_isClosedImmersion (x : X) :
    pushforwardWeight C sX sY p x = 1 := by
  refine pushforwardWeight_eq_one C sX sY p ?_ (residueDegree_eq_one_of_isClosedImmersion p x)
  rw [← hp]
  exact relativeDimension_comp_closedImmersion C.dimensionFunction p sY x

/-- Along a closed immersion the compatibility hypothesis
`Stacks.Chow.FirstChernCapCompatibleWithPushforward` is unweighted: it holds as soon as the
component cycle of `chernX` at each point `x` of relative dimension `k + 1` pushes forward to the
component cycle of `chernY` at the image of `x`. -/
theorem firstChernCapCompatibleWithPushforward_of_isClosedImmersion
    (h : ∀ x : X, relativeDimension C.dimensionFunction sX x = k + 1 →
      properPushforward C sX sY p hp k (firstChernComponentCycleAt C sX k chernX x) =
        firstChernComponentCycleAt C sY k chernY (p.base x)) :
    FirstChernCapCompatibleWithPushforward C sX sY p hp k chernX chernY := by
  intro x hdim y
  rw [h x hdim, pushforwardWeight_eq_one_of_isClosedImmersion C sX sY p hp x, one_mul]

/-- **The projection formula for a closed immersion.** If the component rule of the cap product
on `X` pushes forward to the component rule on `Y` on every integral component, then the cap
product commutes with pushforward along the closed immersion, on Chow groups. -/
theorem properChowPushforward_firstChernClassCap_of_isClosedImmersion
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k)
    (h : ∀ x : X, relativeDimension C.dimensionFunction sX x = k + 1 →
      properPushforward C sX sY p hp k (firstChernComponentCycleAt C sX k chernX x) =
        firstChernComponentCycleAt C sY k chernY (p.base x))
    (α : CycleGroup C sX (k + 1)) :
    properChowPushforward C sX sY p hp k hfac (firstChernClassCap C sX k chernX α) =
      firstChernClassCap C sY k chernY (properPushforward C sX sY p hp (k + 1) α) :=
  properChowPushforward_firstChernClassCap C sX sY p hp k chernX chernY hfac
    (firstChernCapCompatibleWithPushforward_of_isClosedImmersion C sX sY p hp k chernX chernY h) α

/-- If the cap product on `X` kills a `(k+1)`-cycle, then the cap product on `Y` kills its
pushforward along a closed immersion on which the two component rules agree. -/
theorem firstChernClassCap_properPushforward_eq_zero_of_isClosedImmersion
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k)
    (h : ∀ x : X, relativeDimension C.dimensionFunction sX x = k + 1 →
      properPushforward C sX sY p hp k (firstChernComponentCycleAt C sX k chernX x) =
        firstChernComponentCycleAt C sY k chernY (p.base x))
    (α : CycleGroup C sX (k + 1)) (hα : firstChernClassCap C sX k chernX α = 0) :
    firstChernClassCap C sY k chernY (properPushforward C sX sY p hp (k + 1) α) = 0 := by
  rw [← properChowPushforward_firstChernClassCap_of_isClosedImmersion C sX sY p hp k chernX
    chernY hfac h α, hα, map_zero]

end ClosedImmersion

end Stacks.Chow

end
