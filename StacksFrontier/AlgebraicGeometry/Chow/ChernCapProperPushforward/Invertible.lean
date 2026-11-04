module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapProperPushforward.ComponentClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDominantPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardDimensionDrop

/-!
# Stacks 02SU: proper pushforward and the first Chern class cap product

Let `p : X ⟶ Y` be a **proper** morphism of schemes locally of finite type over the base scheme
`S` of chapter 42 of the Stacks Project and let `ℒ` be an invertible `𝒪_Y`-module. This file
proves the projection formula

  `p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α`  in  `A_k(Y)`,  for `α ∈ Z_{k+1}(X)`,

which is [Stacks, Tag 02SU]. The case of a closed immersion is
`Stacks.Chow.properChowPushforward_firstChernClassCapOfInvertible`.

The general cycle is reduced by
`Stacks.Chow.properChowPushforward_firstChernClassCap_of_imageComponentCycle` to its integral
components. For a point `x` of `X` of relative dimension `k + 1`, with `W = closure {x} ⊆ X`,
`W' = closure {p x} ⊆ Y` and `r : W ⟶ W'` the restriction of `p`
(`Stacks.Chow.integralComponentMap`), the pushforward along `r` of the value at `W` of the
component rule of `p^*ℒ` is rationally equivalent on `W'` to `Stacks.Chow.imageComponentCycle`:
`[R(W) : R(W')]` times the value at `W'` of the component rule of `ℒ` if `p` preserves the
delta-dimension at `x` (Stacks 02ST), and `0` if it drops it.

## Main definitions

* `Stacks.Chow.integralComponentModuleIso` — the restriction to `W` of `p^*ℒ` is the pullback
  along `r` of the restriction of `ℒ` to `W'`.

## Main results

* `Stacks.Chow.properPushforward_chernComponentCycle_of_val` — the grading transport between the
  divisor cycle of Stacks 02SJ (1) and the component cycle of Stacks 02SO under proper
  pushforward.
* `Stacks.Chow.rationallyEquivalent_properPushforward_firstChernComponentCycleRule` — the
  componentwise input: the pushforward to the image component of the value of the rule of `p^*ℒ`
  is rationally equivalent to `Stacks.Chow.imageComponentCycle`.
* `Stacks.Chow.properChowPushforward_firstChernClassCapOfInvertible_of_isProper'` —
  **Stacks 02SU.**

## Implementation notes

The two gradings of one cycle — `Stacks.Chow.meromorphicDivisorCycle`, graded `n - 1` on a scheme
of delta-dimension `n`, and `Stacks.Chow.chernComponentCycle`, graded `k` on a scheme of
delta-dimension `k + 1` — are crossed by `Stacks.Chow.properPushforward_chernComponentCycle_of_val`
rather than by a cast: the two have the same underlying algebraic cycle and proper pushforward
reads only that.

## References

* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### Crossing the two gradings under proper pushforward -/

/-- **A pushforward identity transported between two gradings of one cycle.** Proper pushforward
reads only the underlying algebraic cycle, so an identity `g_*c = d` between cycles in one grading
gives the identity `g_*c' = d'` for any cycles `c'`, `d'` with the same underlying cycles. -/
theorem properPushforward_chernComponentCycle_of_val (C : ChowSituation.{u}) {V T : Scheme.{u}}
    (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (g : V ⟶ T)
    [IsProper g] (hg : g ≫ sT = sV) {m m' : ℤ} (c : CycleGroup C sV m) (c' : CycleGroup C sV m')
    (hc : (c : AlgebraicCycle V ℤ) = (c' : AlgebraicCycle V ℤ)) (d : CycleGroup C sT m)
    (d' : CycleGroup C sT m') (hd : (d : AlgebraicCycle T ℤ) = (d' : AlgebraicCycle T ℤ))
    (hpush : properPushforward C sV sT g hg m c = d) :
    properPushforward C sV sT g hg m' c' = d' := by
  refine Subtype.ext ?_
  rw [← val_properPushforward_eq_of_val_eq C sV sT g hg c c' hc, ← hd]
  exact congrArg Subtype.val hpush

/-- An integer multiple of a cycle, read as an algebraic cycle. The cycle group is a subgroup of
the group of algebraic cycles, so this is the coercion being additive. -/
theorem val_zsmul_cycleGroup (C : ChowSituation.{u}) {V : Scheme.{u}} (sV : V ⟶ C.S)
    [LocallyOfFiniteType sV] {m : ℤ} (n : ℤ) (c : CycleGroup C sV m) :
    ((n • c : CycleGroup C sV m) : AlgebraicCycle V ℤ) = n • (c : AlgebraicCycle V ℤ) :=
  rfl

/-! ### The restriction of `p^*ℒ` to an integral component -/

/-- **The restriction of `ℒ` to the image component, pulled back along the component restriction,
is the restriction of `p^*ℒ`.** Both are the pullback of `ℒ` along the one morphism
`closure {x} ⟶ Y`, written through its two factorizations
`closure {x} ⟶ closure {p x} ⟶ Y` and `closure {x} ⟶ X ⟶ Y`, which agree by
`Stacks.Chow.integralComponentMap_subschemeι`. -/
def integralComponentModuleIso {X Y : Scheme.{u}} (p : X ⟶ Y) (L : Y.Modules) (x : X) :
    (Scheme.Modules.pullback (integralComponentMap p x)).obj
        ((Scheme.Modules.pullback (integralComponentAt (p.base x)).subschemeι).obj L) ≅
      (Scheme.Modules.pullback (integralComponentAt x).subschemeι).obj
        ((Scheme.Modules.pullback p).obj L) :=
  (Scheme.Modules.pullbackComp (integralComponentMap p x)
      (integralComponentAt (p.base x)).subschemeι).app L ≪≫
    (Scheme.Modules.pullbackCongr (integralComponentMap_subschemeι p x)).app L ≪≫
    ((Scheme.Modules.pullbackComp (integralComponentAt x).subschemeι p).app L).symm

/-! ### The componentwise input to the projection formula -/

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX)
  (k : ℤ) (L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]

include hp

/-- For a point `x` of `X` of relative dimension `k + 1`, the pushforward along the component
restriction `r : closure {x} ⟶ closure {p x}` of the value at `closure {x}` of the component rule
of `p^*ℒ` is rationally equivalent to `Stacks.Chow.imageComponentCycle`, the weighted value at
`closure {p x}` of the component rule of `ℒ`. -/
theorem rationallyEquivalent_properPushforward_firstChernComponentCycleRule (x : X)
    (hx : relativeDimension C.dimensionFunction sX x = k + 1) :
    RationallyEquivalent C ((integralComponentAt (p.base x)).subschemeι ≫ sY) k
      (properPushforward C ((integralComponentAt x).subschemeι ≫ sX)
        ((integralComponentAt (p.base x)).subschemeι ≫ sY) (integralComponentMap p x)
        (integralComponentMap_comp_base C sX sY p hp x) k
        (firstChernComponentCycleRule C sX k ((Scheme.Modules.pullback p).obj L)
          (integralComponentAt x) (isIntegral_integralComponentAt x)
          (schemeDeltaDimension_integralComponentAt_of_eq C sX hx)))
      (imageComponentCycle C sX sY p k (firstChernComponentCycleRule C sY k L) x) := by
  classical
  set W := integralComponentAt x with hWdef
  set W' := integralComponentAt (p.base x) with hW'def
  have hW : IsIntegral W.subscheme := isIntegral_integralComponentAt x
  have hW' : IsIntegral W'.subscheme := isIntegral_integralComponentAt (p.base x)
  have hDim : schemeDeltaDimension C (W.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt) :=
    schemeDeltaDimension_integralComponentAt_of_eq C sX hx
  have _ : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ sX)
  have _ : IsLocallyNoetherian W'.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W'.subschemeι ≫ sY)
  set r := integralComponentMap p x with hrdef
  have hr : r ≫ (W'.subschemeι ≫ sY) = W.subschemeι ≫ sX :=
    integralComponentMap_comp_base C sX sY p hp x
  set N : W'.subscheme.Modules := (Scheme.Modules.pullback W'.subschemeι).obj L with hNdef
  have hNinv : AlgebraicGeometry.SheafOfModules.IsInvertible W'.subscheme.presheaf
      W'.subscheme.ringCatSheaf.2 N := isInvertible_presheaf_modulePullback L _
  have hNinv' : AlgebraicGeometry.SheafOfModules.IsInvertible W'.subscheme.sheaf.obj
      W'.subscheme.ringCatSheaf.property N := hNinv
  set σ := (exists_ne_zero_genericStalk
    (isTrivializedNear_of_isInvertible N (genericPoint W'.subscheme))).choose with hσdef
  have hσ : σ ≠ 0 := (exists_ne_zero_genericStalk
    (isTrivializedNear_of_isInvertible N (genericPoint W'.subscheme))).choose_spec
  set τ := genericStalkPullback r N σ with hτdef
  have hRinv : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.presheaf
      W.subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback r).obj N) :=
    isInvertible_presheaf_modulePullback N r
  have hMinv : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.presheaf
      W.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback W.subschemeι).obj ((Scheme.Modules.pullback p).obj L)) :=
    isInvertible_presheaf_modulePullback ((Scheme.Modules.pullback p).obj L) _
  have hτ : τ ≠ 0 :=
    genericStalkPullback_ne_zero r (isTrivializedNear_of_isInvertible N) hσ
  set e := integralComponentModuleIso p L x with hedef
  set t := stalkLinearMap ((Scheme.Modules.pullback r).obj N)
    ((Scheme.Modules.pullback W.subschemeι).obj ((Scheme.Modules.pullback p).obj L)) e.hom
    (genericPoint W.subscheme) τ with htdef
  have ht : t ≠ 0 := fun h =>
    hτ ((bijective_stalkLinearMap _ _ e.hom (genericPoint W.subscheme)).1
      (h.trans (map_zero _).symm))
  have hstep1 : (QuotientAddGroup.mk
        (firstChernComponentCycleRule C sX k ((Scheme.Modules.pullback p).obj L) W hW hDim) :
      chowGroup C (W.subschemeι ≫ sX) k) =
      QuotientAddGroup.mk (chernComponentCycle C (W.subschemeι ≫ sX) hDim
        (fun z => isTrivializedNear_of_isInvertible _ z) τ) := by
    refine ((firstChernComponentClass_eq_mk C sX k ((Scheme.Modules.pullback p).obj L) W hW
      hDim).symm.trans (firstChernComponentClass_eq_mk_of_ne_zero C sX k
      ((Scheme.Modules.pullback p).obj L) W hDim ht)).trans ?_
    exact congrArg QuotientAddGroup.mk
      (chernComponentCycle_mapStalkLinearMap C (W.subschemeι ≫ sX) hDim _ _ e.hom
        (fun z => isTrivializedNear_of_isInvertible _ z)
        (fun z => isTrivializedNear_of_isInvertible _ z) τ)
  have hstep2 : (QuotientAddGroup.mk
        (properPushforward C (W.subschemeι ≫ sX) (W'.subschemeι ≫ sY) r hr k
          (firstChernComponentCycleRule C sX k ((Scheme.Modules.pullback p).obj L) W hW hDim)) :
      chowGroup C (W'.subschemeι ≫ sY) k) =
      QuotientAddGroup.mk (properPushforward C (W.subschemeι ≫ sX) (W'.subschemeι ≫ sY) r hr k
        (chernComponentCycle C (W.subschemeι ≫ sX) hDim
          (fun z => isTrivializedNear_of_isInvertible _ z) τ)) :=
    congrArg (properChowPushforward C (W.subschemeι ≫ sX) (W'.subschemeι ≫ sY) r hr k
      (properPushforwardFactorsThroughRationalEquivalence C (W.subschemeι ≫ sX)
        (W'.subschemeι ≫ sY) r hr k)) hstep1
  have cross : ∀ (d : CycleGroup C (W'.subschemeι ≫ sY) (k + 1 - 1))
      (d' : CycleGroup C (W'.subschemeι ≫ sY) k),
      (d : AlgebraicCycle W'.subscheme ℤ) = d' →
      properPushforward C (W.subschemeι ≫ sX) (W'.subschemeι ≫ sY) r hr (k + 1 - 1)
        (meromorphicDivisorCycle C (W.subschemeι ≫ sX) hDim
          (fun z => isTrivializedNear_of_isInvertible _ z) τ).val = d →
      properPushforward C (W.subschemeι ≫ sX) (W'.subschemeι ≫ sY) r hr k
        (chernComponentCycle C (W.subschemeι ≫ sX) hDim
          (fun z => isTrivializedNear_of_isInvertible _ z) τ) = d' :=
    fun d d' hd h => properPushforward_chernComponentCycle_of_val C (W.subschemeι ≫ sX)
      (W'.subschemeι ≫ sY) r hr _ _
      (val_meromorphicDivisorCycle_eq_chernComponentCycle C (W.subschemeι ≫ sX) hDim _ τ) d d' hd h
  refine QuotientAddGroup.eq_iff_sub_mem.1 (hstep2.trans ?_)
  by_cases hy : relativeDimension C.dimensionFunction sY (p.base x) = k + 1
  · have hDim' : schemeDeltaDimension C (W'.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt) :=
      schemeDeltaDimension_integralComponentAt_of_eq C sY hy
    let _ : Algebra W'.subscheme.functionField W.subscheme.functionField :=
      (dominantFunctionFieldMap r).toAlgebra
    have hweight : pushforwardWeight C sX sY p x =
        (Module.finrank W'.subscheme.functionField W.subscheme.functionField : ℤ) :=
      pushforwardWeight_eq_finrank_functionField C sX sY p x (hx.trans hy.symm)
    have h02ST := properPushforward_meromorphicDivisorCycleOfInvertible C (W.subschemeι ≫ sX)
      (W'.subschemeι ≫ sY) hDim hDim' r hr N σ hσ
    have hpush : properPushforward C (W.subschemeι ≫ sX) (W'.subschemeι ≫ sY) r hr k
        (chernComponentCycle C (W.subschemeι ≫ sX) hDim
          (fun z => isTrivializedNear_of_isInvertible _ z) τ) =
        pushforwardWeight C sX sY p x •
          chernComponentCycle C (W'.subschemeι ≫ sY) hDim'
            (fun z => isTrivializedNear_of_isInvertible _ z) σ := by
      refine cross _ _ ?_ h02ST
      rw [val_zsmul_cycleGroup, val_zsmul_cycleGroup, hweight,
        val_meromorphicDivisorCycle_eq_chernComponentCycle C (W'.subschemeι ≫ sY) hDim' _ σ]
    have hstep4 : (QuotientAddGroup.mk
          (chernComponentCycle C (W'.subschemeι ≫ sY) hDim'
            (fun z => isTrivializedNear_of_isInvertible _ z) σ) :
        chowGroup C (W'.subschemeι ≫ sY) k) =
        QuotientAddGroup.mk (firstChernComponentCycleRule C sY k L W' hW' hDim') :=
      ((firstChernComponentClass_eq_mk C sY k L W' hW' hDim').symm.trans
        (firstChernComponentClass_eq_mk_of_ne_zero C sY k L W' hDim' hσ)).symm
    rw [hpush, imageComponentCycle, dite_eq_left hy]
    exact ((map_zsmul (QuotientAddGroup.mk' (rationalEquivalences C (W'.subschemeι ≫ sY) k))
          (pushforwardWeight C sX sY p x) _).trans
        (congrArg (fun z : chowGroup C (W'.subschemeι ≫ sY) k ↦
          pushforwardWeight C sX sY p x • z) hstep4)).trans
      (map_zsmul (QuotientAddGroup.mk' (rationalEquivalences C (W'.subschemeι ≫ sY) k))
        (pushforwardWeight C sX sY p x) _).symm
  · have hDimNe : schemeDeltaDimension C (W'.subschemeι ≫ sY) ≠ ((k + 1 : ℤ) : EInt) := by
      rw [schemeDeltaDimension_integralComponentAt C sY (p.base x)]
      exact fun h => hy (WithBotTop.coe_injective h)
    have hrft : LocallyOfFiniteType (r ≫ (W'.subschemeι ≫ sY)) := by rw [hr]; infer_instance
    have _ : LocallyOfFiniteType r := locallyOfFiniteType_of_comp r (W'.subschemeι ≫ sY)
    have hlt : schemeDeltaDimension C (W'.subschemeι ≫ sY) < ((k + 1 : ℤ) : EInt) :=
      lt_of_le_of_ne (hDim ▸ schemeDeltaDimension_le_of_isDominant C (W.subschemeι ≫ sX)
        (W'.subschemeι ≫ sY) r hr) hDimNe
    have h0 := properPushforward_meromorphicDivisorCycleOfInvertible_eq_zero C
      (W.subschemeι ≫ sX) (W'.subschemeι ≫ sY) hDim hlt r hr N σ hσ
    have hpush : properPushforward C (W.subschemeι ≫ sX) (W'.subschemeι ≫ sY) r hr k
        (chernComponentCycle C (W.subschemeι ≫ sX) hDim
          (fun z => isTrivializedNear_of_isInvertible _ z) τ) = 0 :=
      cross 0 0 rfl h0
    rw [hpush, imageComponentCycle, dite_eq_right hy]

/-! ### Stacks 02SU -/

/-- **Stacks 02SU.** Let `p : X ⟶ Y` be a proper morphism of schemes locally of finite type over
the base scheme of chapter 42 and let `ℒ` be an invertible `𝒪_Y`-module. Then for every
`(k+1)`-cycle `α` on `X`

  `p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α`  in  `A_k(Y)`. -/
@[stacks 02SU]
theorem properChowPushforward_firstChernClassCapOfInvertible_of_isProper'
    (α : CycleGroup C sX (k + 1)) :
    letI := isInvertible_presheaf_modulePullback L p
    properChowPushforward C sX sY p hp k
        (properPushforwardFactorsThroughRationalEquivalence C sX sY p hp k)
        (firstChernClassCapOfInvertible C sX k ((Scheme.Modules.pullback p).obj L) α) =
      firstChernClassCapOfInvertible C sY k L
        (properPushforward C sX sY p hp (k + 1) α) :=
  properChowPushforward_firstChernClassCap_of_imageComponentCycle C sX sY p hp k
    (firstChernComponentCycleRule C sX k ((Scheme.Modules.pullback p).obj L))
    (firstChernComponentCycleRule C sY k L) _
    (fun x hx => rationallyEquivalent_properPushforward_firstChernComponentCycleRule C sX sY p hp
      k L x hx) α

end Stacks.Chow

end
