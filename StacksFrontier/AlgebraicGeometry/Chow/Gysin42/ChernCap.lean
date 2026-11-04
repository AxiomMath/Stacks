module

public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.ChernCapDescent

/-!
# Gysin pullback and the first Chern class cap product

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `L` be an invertible module on `X` and let `s ∈ Γ(X, L)` be a global section with
zero scheme `i : D = Z(s) ⟶ X`. Let `N` be a second invertible module on `X`. Stacks 0B72 is the
compatibility

  `i^*(c₁(N) ∩ α) = c₁(i^*N) ∩ i^*α`  in  `A_k(D)`,  for `α ∈ A_{k+2}(X)`.

Both sides are composites of two operations defined by a rule on integral components, so the
identity is, at bottom, a statement about those rules. This file proves the passage from the rules
to all cycles once: `Stacks.Chow.ComponentRule.extendCoeff_extendCycle_apply` says that the
composite of two coefficientwise extensions is again a coefficientwise sum over the components of
the cycle, after which the identity is a pointwise statement about the component rules.

## Main definitions

* `Stacks.Chow.GysinCommutesWithChernCapOnComponents` — the identity of Stacks 0B72 on the
  fundamental cycle of a single integral component, which is the case the source proves.

## Main results

* `Stacks.Chow.ComponentRule.extendCoeff_extendCycle_apply` — the composite of two
  coefficientwise extensions of component rules, as a single locally finite sum over the
  components of the cycle.
* `Stacks.Chow.gysinRule_extendCycleGroup_firstChernCapRule_extendCycleGroup` — Stacks 0B72 at
  the level of **cycles**.
* `Stacks.Chow.gysinHomomorphismOnChow_firstChernClassCapOnChow` — **Stacks 0B72**: the same
  identity on Chow groups.
* `Stacks.Chow.gysinCommutesWithChernCapOnComponents_of_components` — the hypothesis restated on
  integral closed subschemes rather than on points.

## Implementation notes

### Degrees

The source writes the input degree as `k` and the output degree as `k - 2`. Here the output degree
is `k` and the input degree is `k + 1 + 1`, so that the two successive degree-lowering operations
compose without casts, exactly as in the statement of Stacks 0B72. The Gysin map therefore
appears at two degrees, `k` and `k + 1`, and so carries two component rules; likewise the cap
product appears on `X` in degree `k + 1` and on `D` in degree `k`.

### The invertible module `N` does not appear

In this repository the cap product of Stacks 02SO is built from an explicit component rule rather
than from an invertible module — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass`. So the module `N` of the source enters only
through its component rule `chernN` on `X` and the component rule `chernD` of its restriction
`i^*N` on `D`, which are independent parameters here. In particular Stacks 0B8L, which the
statement of Stacks 0B72 uses to know that `i^*N` is invertible, is not needed.

### The compatibility hypothesis is the integral case of the source, and is indispensable

`Stacks.Chow.GysinCommutesWithChernCapOnComponents` says that the identity holds, at the level of
cycles, on the fundamental cycle of each integral component of `X` of delta-dimension `k + 2`.
That is precisely the case the source proves: "Let `W ⊆ X` be an integral closed subscheme of
dimension `k`. Let us prove the equality in case `α = [W]`", after which the general case follows
by the component formula. The source's proof of that case uses Stacks 02SU, 02TJ and 02TM, none of
which is available here in the form it needs — Stacks 02SU is carried as a hypothesis in
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward`, and Stacks 02TM and 02TJ rest on the key
formula of Stacks 0AYC and on Stacks 02SJ. Granting the key formula, Stacks 02TM is available
after pushforward along the divisor, as
`Stacks.Chow.effectiveCartierIntersection_eq_firstChernClassCap_of_keyFormula`, which is too weak
for the component comparison here.

It cannot be dropped. All four operations here are built from arbitrary component rules, and four
unrelated rules have no reason to satisfy any identity: taking `chernD = 0` and `chernN` with some
nonzero value already makes the conclusion fail.

The hypothesis is strictly weaker than the conclusion: it constrains the rules only on single
integral components, and the theorem extends it to every cycle. That extension is the work, and it
is not formal — a cycle is a *locally* finite sum of components, so both composites are double
locally finite sums and the proof has to exchange them. That is
`Stacks.Chow.ComponentRule.extendCoeff_extendCycle_apply`.

### No `@[stacks 0B72]`

The tag's single statement is the unconditional identity. Every declaration below carries four
component rules, three descent hypotheses of Stacks 02TI and 02TO, and the integral-component
compatibility, so none of them is literally the tagged statement. Accordingly no `@[stacks]`
attribute is placed in this file.

## References

* [Stacks Project, Tag 0B72](https://stacks.math.columbia.edu/tag/0B72)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Set

universe u

namespace Stacks.Chow

/-! ### Composing two coefficientwise extensions -/

namespace ComponentRule

/-- **Composing two coefficientwise extensions.** Extending a component rule `G₂` on `Z` over
`Y` across the extension of a component rule `G₁` on `Y` over `X` is the coefficientwise sum, over
the points of `X`, of the `G₂`-extensions of the component cycles of `G₁`.

Neither sum is finite, so this is not a formal manipulation: the exchange of summation needs the
joint support of the double family to be finite. It is, and no compactness is required. A term
`α x · G₁.cycle x y · G₂.cycle y z` is nonzero only if `i₂ z` is a generalization of `y` and
`i₁ y` is a generalization of `x`, hence `i₁ (i₂ z)` is a generalization of `x`; there are
finitely many such `x` in the support of `α`, and for each of them finitely many such `y` in the
support of `G₁.cycle x`, both by
`Stacks.Chow.finite_support_inter_generalizations` applied to the compact set `{i₁ (i₂ z)}`,
respectively `{i₂ z}`. -/
theorem extendCoeff_extendCycle_apply {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {i₁ : Y → X} (G₁ : ComponentRule i₁) (hi₁ : Continuous i₁)
    {i₂ : Z → Y} (G₂ : ComponentRule i₂) (α : Function.locallyFinsupp X ℤ) (z : Z) :
    G₂.extendCoeff (G₁.extendCycle hi₁ α) z =
      ∑ᶠ x : X, α x * G₂.extendCoeff (G₁.cycle x) z := by
  set A : Set X := {x : X | (∃ a ∈ ({i₁ (i₂ z)} : Set X), a ∈ closure ({x} : Set X)) ∧ α x ≠ 0}
  have hAfin : A.Finite :=
    finite_support_inter_generalizations α.locallyFiniteSupport isCompact_singleton
  set B : Set Y := ⋃ x ∈ A, {y : Y | (∃ a ∈ ({i₂ z} : Set Y), a ∈ closure ({y} : Set Y)) ∧
    G₁.cycle x y ≠ 0}
  have hBfin : B.Finite := hAfin.biUnion fun x _ ↦
    finite_support_inter_generalizations (G₁.cycle x).locallyFiniteSupport isCompact_singleton
  -- a nonzero term forces `x ∈ A` and `y ∈ B`
  have hvan : ∀ (x : X) (y : Y), y ∈ (Set.univ : Set Y) →
      α x * (G₁.cycle x y * G₂.cycle y z) ≠ 0 → x ∈ A ∧ y ∈ B := by
    intro x y _ hne
    have h₁ : G₁.cycle x y ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hne)
    have hzy : i₂ z ∈ closure ({y} : Set Y) :=
      G₂.mem_closure_of_apply_ne_zero y z (right_ne_zero_of_mul (right_ne_zero_of_mul hne))
    have hxA : x ∈ A := ⟨⟨i₁ (i₂ z), rfl, specializes_iff_mem_closure.1
      ((specializes_iff_mem_closure.2 (G₁.mem_closure_of_apply_ne_zero x y h₁)).trans
        ((specializes_iff_mem_closure.2 hzy).map hi₁))⟩, left_ne_zero_of_mul hne⟩
    exact ⟨hxA, Set.mem_biUnion hxA ⟨⟨i₂ z, rfl, hzy⟩, h₁⟩⟩
  have key := finsum_finsum_mem_comm (fun (x : X) (y : Y) ↦ α x * (G₁.cycle x y * G₂.cycle y z))
    Set.univ hAfin hBfin (Set.subset_univ B) hvan
  have hL : ∀ y : Y, G₁.extendCycle hi₁ α y * G₂.cycle y z =
      ∑ᶠ x : X, α x * (G₁.cycle x y * G₂.cycle y z) := by
    intro y
    show (∑ᶠ x : X, α x * G₁.cycle x y) * G₂.cycle y z = _
    rw [finsum_mul]
    exact finsum_congr fun x ↦ mul_assoc _ _ _
  show (∑ᶠ y : Y, G₁.extendCycle hi₁ α y * G₂.cycle y z) = _
  rw [← finsum_mem_univ fun y : Y ↦ G₁.extendCycle hi₁ α y * G₂.cycle y z,
    finsum_mem_congr rfl fun y _ ↦ hL y, key]
  refine finsum_congr fun x ↦ ?_
  rw [finsum_mem_univ fun y : Y ↦ α x * (G₁.cycle x y * G₂.cycle y z)]
  exact (mul_finsum (fun y : Y ↦ G₁.cycle x y * G₂.cycle y z) (α x)).symm

end ComponentRule

/-! ### Stacks 0B72 on integral components -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  (chern : FirstChernComponentClassRule C p k)
  (chernUp : FirstChernComponentClassRule C p (k + 1))
  (chernN : FirstChernComponentCycleRule C p (k + 1))
  (chernD : FirstChernComponentCycleRule C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k)

/-- **Stacks 0B72 on integral components.** The assertion that for every integral component of
`X` of delta-dimension `k + 1 + 1` — equivalently, for every point of relative dimension
`k + 1 + 1` — the identity `i^*(c₁(N) ∩ [W]) = c₁(i^*N) ∩ i^*[W]` holds at the level of cycles.

This is the case the source proves, from which the general case follows by the component formula;
it is carried as a hypothesis here because the source's proof uses Stacks 02SU, 02TJ and 02TM. See
the implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCap`. -/
def GysinCommutesWithChernCapOnComponents : Prop :=
  ∀ x : X, relativeDimension C.dimensionFunction p x = k + 1 + 1 →
    (gysinRule C p k L s chern).extendCycleGroup
        (firstChernComponentCycleAt C p (k + 1) chernN x) =
      IntegralComponentRule.extendCycleGroup
        (firstChernCapRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD)
        (gysinComponentCycleAt C p (k + 1) L s chernUp x)

/-- The compatibility of Stacks 0B72 on integral components, restated on integral closed
subschemes of `X` instead of on points: the two are the same datum, by
`Stacks.Chow.integralComponentAt_genericPointOf`. -/
theorem gysinCommutesWithChernCapOnComponents_of_components
    (h : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt)),
      (gysinRule C p k L s chern).extendCycleGroup
          (firstChernComponentCycle C p (k + 1) chernN W hW hDim) =
        IntegralComponentRule.extendCycleGroup
          (firstChernCapRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD)
          (gysinComponentCycle C p (k + 1) L s chernUp W hW hDim)) :
    GysinCommutesWithChernCapOnComponents C p k L s chern chernUp chernN chernD := by
  intro x hdim
  have hW : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hDim : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_integralComponentAt C p x, hdim]
  have h' := h (integralComponentAt x) hW hDim
  rwa [← firstChernComponentCycleAt_genericPointOf C p (k + 1) chernN _ hW hDim,
    ← gysinComponentCycleAt_genericPointOf C p (k + 1) L s chernUp _ hW hDim,
    genericPointOf_integralComponentAt x] at h'

/-! ### Stacks 0B72 -/

/-- **Stacks 0B72, at the level of cycles.** Granted the identity on integral components, Gysin
pullback through the zero scheme of `s` commutes with intersecting with a first Chern class,
already on cycles.

Both sides are composites of two coefficientwise extensions, so
`Stacks.Chow.ComponentRule.extendCoeff_extendCycle_apply` puts both into the shape
`∑_x α(x) · (something attached to x)`, after which the hypothesis applies term by term. Only the
points carrying a nonzero coefficient of `α` are compared, and those have relative dimension
`k + 1 + 1` because `α` is a `(k+1+1)`-cycle. -/
theorem gysinRule_extendCycleGroup_firstChernCapRule_extendCycleGroup
    (hcomp : GysinCommutesWithChernCapOnComponents C p k L s chern chernUp chernN chernD)
    (α : CycleGroup C p (k + 1 + 1)) :
    (gysinRule C p k L s chern).extendCycleGroup
        ((firstChernCapRule C p (k + 1) chernN).extendCycleGroup α) =
      IntegralComponentRule.extendCycleGroup
        (firstChernCapRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD)
        ((gysinRule C p (k + 1) L s chernUp).extendCycleGroup α) := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  have hLHS := ComponentRule.extendCoeff_extendCycle_apply
    (firstChernCapRule C p (k + 1) chernN).toComponentRule (𝟙 X : X ⟶ X).continuous
    (gysinRule C p k L s chern).toComponentRule α.1 y
  have hRHS := ComponentRule.extendCoeff_extendCycle_apply
    (gysinRule C p (k + 1) L s chernUp).toComponentRule
    (Stacks.Divisors.zeroScheme X L s).subschemeι.continuous
    (IntegralComponentRule.toComponentRule
      (firstChernCapRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD)) α.1 y
  refine (hLHS.trans (Eq.trans ?_ hRHS.symm))
  refine finsum_congr fun x ↦ ?_
  by_cases hx : α.1 x = 0
  · simp [hx]
  · exact congrArg (α.1 x * ·) (congrArg (fun β ↦ β.1 y)
      (hcomp x ((mem_cyclesOfDimension_iff_forall_point C p (k + 1 + 1) α.1).1 α.2 x hx)))

/-- **Stacks 0B72.** Gysin pullback through the zero scheme of a section commutes with capping
with a first Chern class: `i^*(c₁(N) ∩ α) = c₁(i^*N) ∩ i^*α` in `A_k(D)` for every
`α ∈ A_{k+1+1}(X)`.

The four component rules, the three descent hypotheses of Stacks 02TO and 02TI and the
integral-component compatibility are explicit parameters; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCap`. The identity holds already at the level of
cycles, which is
`Stacks.Chow.gysinRule_extendCycleGroup_firstChernCapRule_extendCycleGroup`. -/
theorem gysinHomomorphismOnChow_firstChernClassCapOnChow
    (hgysin : GysinFactorsThroughRationalEquivalence C p k L s chern)
    (hgysinUp : GysinFactorsThroughRationalEquivalence C p (k + 1) L s chernUp)
    (hchernN : FirstChernClassCapFactorsThroughRationalEquivalence C p (k + 1) chernN)
    (hchernD : FirstChernClassCapFactorsThroughRationalEquivalence C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD)
    (hcomp : GysinCommutesWithChernCapOnComponents C p k L s chern chernUp chernN chernD)
    (α : chowGroup C p (k + 1 + 1)) :
    gysinHomomorphismOnChow C p k L s chern hgysin
        (firstChernClassCapOnChow C p (k + 1) chernN hchernN α) =
      firstChernClassCapOnChow C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k chernD
        hchernD (gysinHomomorphismOnChow C p (k + 1) L s chernUp hgysinUp α) := by
  induction α using QuotientAddGroup.induction_on with
  | H β =>
    show QuotientAddGroup.mk ((gysinRule C p k L s chern).extendCycleGroup
      ((firstChernCapRule C p (k + 1) chernN).extendCycleGroup β)) = _
    rw [gysinRule_extendCycleGroup_firstChernCapRule_extendCycleGroup C p k L s chern chernUp
      chernN chernD hcomp β]
    rfl

end Stacks.Chow

end
