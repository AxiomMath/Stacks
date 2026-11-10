module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapRuleIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projection formula of Stacks 02SU from componentwise rational equivalence

Let `X` and `Y` be locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `p : X ⟶ Y` be proper over `S`, and let a first Chern class component rule of
Stacks 02SO be given on each of `X` and `Y`. The projection formula

  `p_*(c₁(p^*L) ∩ α) = c₁(L) ∩ p_*α`  in  `A_k(Y)`

of [Stacks, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU) is proved in
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward` from the hypothesis
`Stacks.Chow.FirstChernCapCompatibleWithPushforward`, which asks the two rules to agree along
`p`, on each integral component of `X`, **as cycles**. That hypothesis is too strong for the
rules of an invertible module: the rule of `p^*L` on an integral component `W ⊆ X` and the rule
of `L` on the image component `W' ⊆ Y` each choose a meromorphic section independently, so the
pushforward of the one and the other differ by the principal divisor of their ratio.

This file redoes the reduction with the componentwise hypothesis weakened to **rational
equivalence in the Chow group of the image component**, which is what Stacks 02SJ (2) and
Stacks 02ST deliver. The price is that the two cycles on `Y` are no longer equal: they are
rationally equivalent, by Stacks 02RZ, which sums the componentwise equivalences over the locally
finite family of image components.

## What has to be rebuilt, and what is reused

The two coefficient identities putting both sides into the shape `∑_x α(x) · (… at x)` are those
of `StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentRule`, extracted here as
`Stacks.Chow.properPushforward_firstChernCapRule_extendCycleGroup_apply` and
`Stacks.Chow.firstChernCapRule_extendCycleGroup_properPushforward_apply`; and the factorization
of the pushforward of a component cycle through the component restriction `W ⟶ W'` is
`Stacks.Chow.properPushforward_firstChernComponentCycleAt`.

What is new is the assembly. Stacks 02RZ, in the form
`Stacks.Chow.rationallyEquivalent_finsum_of_closedSupports`, wants both cycles on `Y` presented
coefficientwise as locally finite sums of pushforwards from a locally finite family of closed
subschemes **of `Y`**. The family is the image components `W'_i = closure {p x_i}` of the
components of the cycle `α` being capped, and its local finiteness is where the properness of `p`
is used a second time: `Stacks.Chow.locallyFinite_closure_singleton_map` deduces it from the local
finiteness of the support of `α` and the fact that a spectral map pulls a quasi-compact open back
to a quasi-compact one. (Properness is used a first time in the two coefficient identities, for
the compactness of the fibres.)

## Main definitions

* `Stacks.Chow.imageComponentCycle` — the cycle on the image component `W'` of a point `x` of `X`
  that the right-hand side of the projection formula contributes at `x`: the value of the rule on
  `Y` at `W'`, weighted by `Stacks.Chow.pushforwardWeight`, and zero when `p` drops the
  delta-dimension at `x` — which is the same thing, the weight being zero then.

## Main results

* `Stacks.Chow.locallyFinite_closure_singleton_map` — the images under a spectral map of the
  components of a locally finitely supported function form a locally finite family.
* `Stacks.Chow.properPushforward_firstChernCapRule_extendCycleGroup_apply`,
  `Stacks.Chow.firstChernCapRule_extendCycleGroup_properPushforward_apply` — the two sides of the
  projection formula, coefficientwise, as locally finite sums over the points of `X`.
* `Stacks.Chow.properPushforward_firstChernCapRule_extendCycleGroup_rationallyEquivalent` — the
  two sides are rationally equivalent, granted the componentwise hypothesis.
* `Stacks.Chow.properChowPushforward_firstChernClassCap_of_imageComponentCycle` — **the
  projection formula of Stacks 02SU** from the componentwise hypothesis.

## Implementation notes

Nothing here is a tagged statement: every result carries the two component rules and the
componentwise hypothesis, so none of them is literally Stacks 02SU. The tag is placed where the
hypothesis is discharged for an invertible module, in
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapProperPushforward.Invertible`.

## References

* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The image of a locally finite family under a spectral map -/

/-- **The images under a spectral map of the components of a locally finitely supported function
form a locally finite family.** A quasi-compact open `U` of the target pulls back to a
quasi-compact open of the source, which meets the support in a finite set; and `U`, being open, is
stable under generalization, so it meets `closure {f x}` exactly when it contains `f x`.

For a cycle on `X` and a proper morphism `p : X ⟶ Y` this says that the images of the integral
closed subschemes the cycle is supported on form a locally finite family of closed subsets of
`Y` — the remark the source of Stacks 02SU makes about its disjoint-union diagram. -/
@[ega "IV 21.10.14" "Local finiteness step", ega "IV 21.6.1" "partial"]
theorem locallyFinite_closure_singleton_map {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [PrespectralSpace Y] {f : X → Y} (hf : IsSpectralMap f) {R : Type*}
    [Zero R] {c : X → R} (hc : LocallyFiniteSupport c) :
    LocallyFinite fun i : Function.support c ↦ closure {f (i : X)} := by
  rw [locallyFinite_closure_singleton_iff]
  intro y
  obtain ⟨U, hU⟩ := (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
    (by simp : y ∈ ⊤) (by simp)
  refine ⟨U, hU.1.1.mem_nhds hU.2.1, ?_⟩
  have hfin : (f ⁻¹' U ∩ Function.support c).Finite :=
    hc.finite_inter_support_of_isCompact (hf.2 hU.1.1 hU.1.2)
  have h : {i : Function.support c | f (i : X) ∈ U} =
      Subtype.val ⁻¹' (f ⁻¹' U ∩ Function.support c) := by
    ext i
    exact ⟨fun hi ↦ ⟨hi, i.2⟩, fun hi ↦ hi.1⟩
  rw [h]
  exact Set.Finite.preimage Subtype.val_injective.injOn hfin

/-- A locally finite sum over all of `X` is the sum over the support of a weight function, when
every term with vanishing weight vanishes.

This is `Stacks.Chow.firstChernCapRule_extendCycleGroup_apply_support`'s restriction step, needed
here for both sides of the projection formula. -/
theorem finsum_subtype_support_eq' {ι : Type*} {M : Type*} [AddCommMonoid M]
    {β : Type*} [Zero β] (c : ι → β) (f : ι → M) (hf : ∀ a, c a = 0 → f a = 0) :
    ∑ᶠ i : Function.support c, f (i : ι) = ∑ᶠ a : ι, f a := by
  classical
  rw [finsum_set_coe_eq_finsum_mem,
    finsum_mem_inter_support_eq' f (Function.support c) Set.univ fun x hx ↦ ?_,
    finsum_mem_univ]
  exact ⟨fun _ ↦ trivial, fun _ ↦ fun hc ↦ hx (hf x hc)⟩

/-! ### The two sides of the projection formula, coefficientwise -/

/-- Proper pushforward commutes with an integer multiple. -/
private theorem properPushforward_zsmul_eq (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (k n : ℤ) (c : CycleGroup C sX k) :
    properPushforward C sX sY f hf k (n • c) = n • properPushforward C sX sY f hf k c :=
  map_zsmul (properPushforwardHom C sX sY f hf k) n c

section Proper

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ)
  (chernX : FirstChernComponentCycleRule C sX k) (chernY : FirstChernComponentCycleRule C sY k)

include hp

/-- **The left-hand side of the projection formula, coefficientwise.** The coefficient of the
proper pushforward of the cap product cycle is the locally finite sum over the points of `X` of
the pushforwards of the component cycles, weighted by the coefficients of `α`.

This is `Stacks.Chow.ComponentRule.map_extendCycle_apply` at the component rule of Stacks 02SO,
the compactness of the fibre coming from the properness of `p`. -/
theorem properPushforward_firstChernCapRule_extendCycleGroup_apply
    (α : CycleGroup C sX (k + 1)) (y : Y) :
    (properPushforward C sX sY p hp k
        ((firstChernCapRule C sX k chernX).extendCycleGroup α)).1 y =
      ∑ᶠ x : X, α.1 x *
        (properPushforward C sX sY p hp k (firstChernComponentCycleAt C sX k chernX x)).1 y := by
  have hcpt : IsCompact (p.base ⁻¹' {y}) :=
    p.isProperMap.isCompact_preimage isCompact_singleton
  rw [properPushforward_apply_eq_map,
    show ((firstChernCapRule C sX k chernX).extendCycleGroup α).1 =
      (firstChernCapRule C sX k chernX).toComponentRule.extendCycle
        (𝟙 X : X ⟶ X).continuous α.1 from rfl,
    ComponentRule.map_extendCycle_apply _ _ _ _ _ hcpt]
  exact finsum_congr fun _ ↦ rfl

/-- **The right-hand side of the projection formula, coefficientwise.** The coefficient of the
cap product cycle of the pushforward of `α` is the locally finite sum over the points of `X` of
the component cycles at their images, weighted by the coefficients of `α` and by the pushforward
weights.

This is `Stacks.Chow.ComponentRule.extendCoeff_map_apply` at the component rule of Stacks 02SO;
the reindexing of a sum over `Y` as a sum over `X` uses that a proper morphism is closed and has
compact fibres. -/
theorem firstChernCapRule_extendCycleGroup_properPushforward_apply
    (α : CycleGroup C sX (k + 1)) (y : Y) :
    ((firstChernCapRule C sY k chernY).extendCycleGroup
        (properPushforward C sX sY p hp (k + 1) α)).1 y =
      ∑ᶠ x : X, α.1 x * pushforwardWeight C sX sY p x *
        (firstChernComponentCycleAt C sY k chernY (p.base x)).1 y := by
  have hcpt : IsCompact (p.base ⁻¹' {y}) :=
    p.isProperMap.isCompact_preimage isCompact_singleton
  have hcpt' : IsCompact (p.base ⁻¹' {(𝟙 Y : Y ⟶ Y).base y}) := by simpa using hcpt
  rw [show ((firstChernCapRule C sY k chernY).extendCycleGroup
      (properPushforward C sX sY p hp (k + 1) α)).1 y =
    (firstChernCapRule C sY k chernY).toComponentRule.extendCoeff
      (Function.locallyFinsupp.map p.base (pushforwardWeight C sX sY p) p.isSpectralMap α.1)
      y from rfl,
    ComponentRule.extendCoeff_map_apply _ _ p.isProperMap.isClosedMap _ _ _ hcpt']
  exact finsum_congr fun _ ↦ rfl

omit hp

/-! ### The cycle contributed on the image component -/

/-- **The cycle on the image component that the right-hand side of the projection formula
contributes at a point `x` of `X`:** the value of the rule on `Y` at the integral component
`W' = closure {p x}`, weighted by `Stacks.Chow.pushforwardWeight`, when `p` preserves the
delta-dimension at `x`, and the zero cycle when it drops it.

The two branches agree in substance: the weight is zero where the delta-dimension drops
(`Stacks.Chow.pushforwardWeight_eq_zero`). The case distinction is there only because the rule on
`Y` is defined on components of delta-dimension `k + 1` and `W'` is one only in the first
branch. -/
def imageComponentCycle (x : X) :
    CycleGroup C ((integralComponentAt (p.base x)).subschemeι ≫ sY) k :=
  if hy : relativeDimension C.dimensionFunction sY (p.base x) = k + 1 then
    pushforwardWeight C sX sY p x •
      chernY (integralComponentAt (p.base x)) (isIntegral_integralComponentAt (p.base x))
        (schemeDeltaDimension_integralComponentAt_of_eq C sY hy)
  else 0

omit [IsProper p] in
/-- **The coefficient the image component cycle contributes.** Pushed from the image component to
`Y` and scaled by `n`, it is `n` times the pushforward weight times the component cycle of the
rule on `Y` at the image point — in both branches of its definition, the dropping one because the
weight vanishes there and the component cycle at a point of the wrong relative dimension is
zero. -/
theorem properPushforward_imageComponentCycle_apply {x : X}
    (hx : relativeDimension C.dimensionFunction sX x = k + 1) (n : ℤ) (y : Y) :
    (properPushforward C ((integralComponentAt (p.base x)).subschemeι ≫ sY) sY
        (integralComponentAt (p.base x)).subschemeι rfl k
        (n • imageComponentCycle C sX sY p k chernY x)).1 y =
      n * pushforwardWeight C sX sY p x *
        (firstChernComponentCycleAt C sY k chernY (p.base x)).1 y := by
  by_cases hy : relativeDimension C.dimensionFunction sY (p.base x) = k + 1
  · rw [imageComponentCycle, dite_eq_left hy, smul_smul,
      properPushforward_zsmul_eq,
      firstChernComponentCycleAt_eq C sY k chernY hy]
    rfl
  · rw [imageComponentCycle, dite_eq_right hy, smul_zero, properPushforward_zero,
      pushforwardWeight_eq_zero C sX sY p fun heq ↦ hy (heq.symm.trans hx)]
    simp

/-! ### The projection formula -/

include hp

/-- **The two sides of the projection formula of Stacks 02SU are rationally equivalent**, granted
that on each integral component of `X` the pushforward to the image component of the value of the
rule on `X` is rationally equivalent to the weighted value of the rule on `Y`.

Both sides are, coefficientwise, locally finite sums over the components of `α` of pushforwards
from the image components; the hypothesis makes the members rationally equivalent term by term,
and Stacks 02RZ sums the equivalences. The family of image components is locally finite by
`Stacks.Chow.locallyFinite_closure_singleton_map`, which is where the properness of `p` enters a
second time. -/
theorem properPushforward_firstChernCapRule_extendCycleGroup_rationallyEquivalent
    (hcomp : ∀ (x : X) (hx : relativeDimension C.dimensionFunction sX x = k + 1),
      RationallyEquivalent C ((integralComponentAt (p.base x)).subschemeι ≫ sY) k
        (properPushforward C ((integralComponentAt x).subschemeι ≫ sX)
          ((integralComponentAt (p.base x)).subschemeι ≫ sY) (integralComponentMap p x)
          (integralComponentMap_comp_base C sX sY p hp x) k
          (chernX (integralComponentAt x) (isIntegral_integralComponentAt x)
            (schemeDeltaDimension_integralComponentAt_of_eq C sX hx)))
        (imageComponentCycle C sX sY p k chernY x))
    (α : CycleGroup C sX (k + 1)) :
    RationallyEquivalent C sY k
      (properPushforward C sX sY p hp k ((firstChernCapRule C sX k chernX).extendCycleGroup α))
      ((firstChernCapRule C sY k chernY).extendCycleGroup
        (properPushforward C sX sY p hp (k + 1) α)) := by
  classical
  have hdim : ∀ i : Function.support (α.1 : X → ℤ),
      relativeDimension C.dimensionFunction sX (i : X) = k + 1 := fun i ↦
    (mem_cyclesOfDimension_iff_forall_point C sX (k + 1) α.1).1 α.2 i i.2
  refine rationallyEquivalent_finsum_of_closedSupports C sY k
    (fun i : Function.support (α.1 : X → ℤ) ↦ integralComponentAt (p.base (i : X))) ?_
    (fun i ↦ α.1 (i : X) •
      properPushforward C ((integralComponentAt (i : X)).subschemeι ≫ sX)
        ((integralComponentAt (p.base (i : X))).subschemeι ≫ sY)
        (integralComponentMap p (i : X)) (integralComponentMap_comp_base C sX sY p hp (i : X)) k
        (chernX (integralComponentAt (i : X)) (isIntegral_integralComponentAt (i : X))
          (schemeDeltaDimension_integralComponentAt_of_eq C sX (hdim i))))
    (fun i ↦ α.1 (i : X) • imageComponentCycle C sX sY p k chernY (i : X))
    (fun i ↦ ?_) (fun y ↦ ?_) (fun y ↦ ?_)
  · refine (locallyFinite_closure_singleton_map p.isSpectralMap
      α.1.locallyFiniteSupport).subset fun i ↦ ?_
    rw [coe_support_integralComponentAt]
  · have hmem := (rationalEquivalences C
      ((integralComponentAt (p.base (i : X))).subschemeι ≫ sY) k).zsmul_mem
      (hcomp (i : X) (hdim i)) (α.1 (i : X))
    rwa [smul_sub] at hmem
  · rw [properPushforward_firstChernCapRule_extendCycleGroup_apply C sX sY p hp k chernX α y,
      ← finsum_subtype_support_eq' (α.1 : X → ℤ)
        (fun x : X ↦ α.1 x *
          (properPushforward C sX sY p hp k (firstChernComponentCycleAt C sX k chernX x)).1 y)
        fun x hx ↦ by rw [hx, zero_mul]]
    refine finsum_congr fun i ↦ ?_
    rw [properPushforward_firstChernComponentCycleAt C sX sY p hp k chernX (hdim i),
      properPushforward_zsmul_eq]
    rfl
  · rw [firstChernCapRule_extendCycleGroup_properPushforward_apply C sX sY p hp k chernY α y,
      ← finsum_subtype_support_eq' (α.1 : X → ℤ)
        (fun x : X ↦ α.1 x * pushforwardWeight C sX sY p x *
          (firstChernComponentCycleAt C sY k chernY (p.base x)).1 y)
        fun x hx ↦ by rw [hx, zero_mul, zero_mul]]
    exact finsum_congr fun i ↦
      (properPushforward_imageComponentCycle_apply C sX sY p k chernY (hdim i) _ y).symm

/-- **The projection formula of Stacks 02SU**, granted the componentwise rational equivalence of
`Stacks.Chow.properPushforward_firstChernCapRule_extendCycleGroup_rationallyEquivalent`: proper
Chow pushforward commutes with capping with a first Chern class.

The component rules on `X` and on `Y` and the vanishing of Stacks 02S2 needed for
`Stacks.Chow.properChowPushforward` are explicit parameters, exactly as in
`Stacks.Chow.properChowPushforward_firstChernClassCap`; what is weaker here is the
compatibility hypothesis, which is asked only in the Chow group of each image component. -/
theorem properChowPushforward_firstChernClassCap_of_imageComponentCycle
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k)
    (hcomp : ∀ (x : X) (hx : relativeDimension C.dimensionFunction sX x = k + 1),
      RationallyEquivalent C ((integralComponentAt (p.base x)).subschemeι ≫ sY) k
        (properPushforward C ((integralComponentAt x).subschemeι ≫ sX)
          ((integralComponentAt (p.base x)).subschemeι ≫ sY) (integralComponentMap p x)
          (integralComponentMap_comp_base C sX sY p hp x) k
          (chernX (integralComponentAt x) (isIntegral_integralComponentAt x)
            (schemeDeltaDimension_integralComponentAt_of_eq C sX hx)))
        (imageComponentCycle C sX sY p k chernY x))
    (α : CycleGroup C sX (k + 1)) :
    properChowPushforward C sX sY p hp k hfac (firstChernClassCap C sX k chernX α) =
      firstChernClassCap C sY k chernY (properPushforward C sX sY p hp (k + 1) α) := by
  change properChowPushforward C sX sY p hp k hfac
    (QuotientAddGroup.mk' (rationalEquivalences C sX k)
      ((firstChernCapRule C sX k chernX).extendCycleGroup α)) = _
  rw [properChowPushforward_mk]
  exact QuotientAddGroup.eq_iff_sub_mem.2
    (properPushforward_firstChernCapRule_extendCycleGroup_rationallyEquivalent C sX sY p hp k
      chernX chernY hcomp α)

end Proper

end Stacks.Chow

end
