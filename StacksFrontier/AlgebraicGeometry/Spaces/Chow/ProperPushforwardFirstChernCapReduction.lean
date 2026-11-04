module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCap

/-!
# Stacks 0EQT reduced to the source's final step

In Situation 0EDT let `X/B` and `Y/B` be good, let `p : X ⟶ Y` be a **proper** morphism over
`B`, let `ℒ` be an invertible `𝒪_Y`-module and let `α ∈ Z_{k+1}(X)`. Stacks 0EQT is the
projection formula

`p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α`.

`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCap` proves it at the
level of cycles from `AlgebraicGeometry.Space.ProperPushforwardChernComparison`, a bundle of two
inputs. This module does three things to that proof, and all three are consequences of material
already in the repository rather than new mathematics about algebraic spaces.

* **The first of the two inputs is a theorem, not an assumption.** It is discharged by
  `AlgebraicGeometry.Space.properPushforwardChernComparison_of_componentCycle_comm`, so only the
  second input — Stacks 0EQS along the component morphism `p|_W : W ⟶ W'` of Stacks 0EEG — is
  ever needed.
* **The reduction to a single integral closed subspace is an equivalence**, not just an
  implication: `AlgebraicGeometry.Space.properPushforward_firstChernCapCycleMap_iff_component`,
  proved in both directions with nothing assumed.
* **The two component rules can be tied to `ℒ`**, so that `c₁(p^*ℒ)` is the first Chern class of
  the genuine inverse image `p^*ℒ` of Stacks 03LU rather than a free parameter:
  `AlgebraicGeometry.Space.properPushforward_canonicalFirstChernCapCycleMap_iff_component`.

## Main definitions

* `AlgebraicGeometry.Space.canonicalPullbackFirstChernRule`: the component rule of Stacks 0EQJ
  at the genuine inverse image `p^*ℒ` of Stacks 03LU.

## Main results

* `AlgebraicGeometry.Space.properPushforwardChernComparison_of_componentCycle_comm`: the bundle
  of inputs of the source's reduction, built from its second field alone.
* `AlgebraicGeometry.Space.properPushforward_firstChernComponentCycle_of_componentCycle_comm`:
  the source's final step, from Stacks 0EQS along the component morphism and nothing else.
* `AlgebraicGeometry.Space.properPushforward_firstChernComponentCycle_of_firstChernCapCycleMap`:
  the converse of the source's steps (2)–(4) — the projection formula for every cycle gives it
  on the fundamental cycle of a single integral closed subspace.
* `AlgebraicGeometry.Space.properPushforward_firstChernCapCycleMap_iff_component`:
  **Stacks 0EQT reduced, in both directions and with nothing assumed.**
* `AlgebraicGeometry.Space.properPushforward_canonicalFirstChernCapCycleMap_iff_component`: the
  same reduction with both component rules tied to `ℒ`.

## Implementation notes

### The first input of the reduction is proved

`AlgebraicGeometry.Space.ProperPushforwardChernComparison.properPushforward_pushforward` is the
square formed by `i_W : W → X`, `i_{W'} : W' → Y`, `p` and the component morphism `g = p|_W`:
pushing a `k`-cycle on `W` forward along `W → X → Y` is pushing it forward along
`W → W' → Y`. It is
`AlgebraicGeometry.Space.properCyclePushforward_integralClosedSubspacePushforward` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare`, proved at
the source's own hypotheses with no extra assumption — it does not even need `g` to be dominant
or `W'` to be the integral closed image of `|W|`.

The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCap` said that Stacks 0EP2
could not reach this square, on two grounds: that the two constructions of the pushforward of
Stacks 0EP1 which this chapter carries were nowhere compared, and that
`AlgebraicGeometry.Space.integralClosedSubspacePushforward` of the localization sequence was
compared with neither. **Both grounds were already false when written.** The module named above
supplies the two comparisons, as
`AlgebraicGeometry.Space.properPushforwardInDimension_eq_properCyclePushforward` and
`AlgebraicGeometry.Space.properCyclePushforward_ι_eq_integralClosedSubspacePushforward`, the
second from the degree of a closed immersion being `1` at every point (Stacks 0EMX) and from the
δ-dimension of a subspace being unchanged by enlarging the ambient space. That module's own
implementation notes record the same correction.

### The reduction is an equivalence

The source's steps (2)–(4) pass from a single integral closed subspace to an arbitrary cycle,
and are proved in the module above as
`AlgebraicGeometry.Space.properPushforward_firstChernCapCycleMap_of_component`. The converse is
proved here: for `W` of δ-dimension `k + 1` it is the projection formula at `α = [W]`, read
coefficientwise, the cap product taking `[W]` to the component cycle of `W` on the left and the
pushforward of `[W]` being supported at the closure of the image of `|W|` with coefficient the
degree of Stacks 0EP1, part (1), on the right; for `W` of any other δ-dimension both sides
vanish outright. Nothing is assumed in either direction, which is why the equivalence is what
this module registers for Stacks 0EQT.

### `c₁(p^*ℒ)` is tied to `ℒ`

The inverse image of a sheaf of modules along a morphism of algebraic spaces **does** exist in
this repository: `AlgebraicGeometry.Space.modulePullback` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback`, which is Stacks 03D6, part (2)
for the small étale ringed topoi and the inverse-image half of Stacks 03LU, with its adjunction;
and the inverse image of an invertible module is invertible by Stacks 0B8P,
`AlgebraicGeometry.Space.modulePullbackInvertible`. Notes in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCap` and in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisor` said otherwise, and the
consequence was that `c₁(p^*ℒ)` entered Stacks 0EQT only as a free component rule `chernX`, tied
to nothing at all.

So `p^*ℒ` is written down here, and with it the component rule of Stacks 0EQJ at `p^*ℒ`:
`AlgebraicGeometry.Space.canonicalPullbackFirstChernRule` is
`AlgebraicGeometry.Space.canonicalFirstChernRule` — the rule `W ↦ div_{𝒩|_W}(t_W)` of
Stacks 0EQJ at the canonical ratios of Stacks 0EPR, for a regular meromorphic section produced
by Stacks 0EPQ — at the module `(modulePullback p).obj ℒ`. The tied form of the equivalence then
has no parameter on either side: `c₁(p^*ℒ)` is the first Chern class of the genuine `p^*ℒ` and
`c₁(ℒ)` that of `ℒ`.

The general statements keep the two rules as parameters, because the equivalence is true of any
pair of rules and is not weakened by their being free; the tied form is the instance at the
canonical rules, and is the one to quote.

### What remains open

Stacks 0EQS along `p|_W`. It has a statement in this repository,
`AlgebraicGeometry.Space.properPushforward_divisorCycleOfSection` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisor`, which rests on the
coefficient identity of **Stacks 0EQ4**; and Stacks 0EQ4 is itself only *reduced* here, in
`AlgebraicGeometry.Space.properPushforward_principalDivisorCycle_eq_iff`. So the chain
0EQT ← 0EQS ← 0EQ4 is open at its far end and nowhere in between. Two further mismatches would
have to be crossed even with Stacks 0EQ4 in hand: the conclusion of the library's Stacks 0EQS is
about `AlgebraicGeometry.Space.divisorCycleOfSection`, which has to be matched with the
component rule of Stacks 0EQJ — for `AlgebraicGeometry.Space.canonicalFirstChernRule` the two
are the same object by construction, which is a second reason to work at the tied form; and its
degree is `AlgebraicGeometry.Space.functionFieldDegreeAtGenericPoint` of `p|_W`, a degree of
residue fields of `W` and `W'`, while the degree here is that of the ambient `X` and `Y`.

## References

* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
* [Stacks Project, Tag 0EMX](https://stacks.math.columbia.edu/tag/0EMX)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP2](https://stacks.math.columbia.edu/tag/0EP2)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] Classical.propDecidable

/-- The coefficient of a cycle scaled by an integer is the scaled coefficient. -/
private theorem zsmul_cycle_coe_apply (D : BaseSpaceDimensionSituation.{u})
    {Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (s : Z ⟶ D.space) (k : ℤ)
    (c : CycleGroup D s k) (d : ℤ)
    (T : IntegralClosedSubspace D.site D.base D.base_mem Z) : (d • c).1 T = d * c.1 T := by
  change d • c.1 T = d * c.1 T
  rw [zsmul_eq_mul, Int.cast_id]

section Reduction

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)
    {p : X ⟶ Y} (hpB : p ≫ sY = sX) (hp : IsProper D.site D.base D.base_mem p) (k : ℤ)
    (chernX : FirstChernComponentCycleRule D sX k)
    (chernY : FirstChernComponentCycleRule D sY k)

include hX hY hpB hp

/-- **The square of the source's reduction of Stacks 0EQT is a theorem.** The bundle
`AlgebraicGeometry.Space.ProperPushforwardChernComparison` is built from its second field alone:
the first, the identity `p_* i_* = i'_* g_*` over the square of `i_W`, `i_{W'}`, `p` and the
component morphism `g = p|_W`, is
`AlgebraicGeometry.Space.properCyclePushforward_integralClosedSubspacePushforward`, proved at the
source's own hypotheses.

So the only input Stacks 0EQT needs beyond what is proved is Stacks 0EQS along `p|_W`. -/
theorem properPushforwardChernComparison_of_componentCycle_comm
    (hcomm : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D sX W = k + 1)
      (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (g : W.subspace.toFunctor ⟶ W'.subspace.toFunctor)
      (hg : g ≫ W'.subspace.ι = W.subspace.ι ≫ p)
      (_hdom : IsDominant D.site D.base D.base_mem g),
      properCyclePushforward D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W) (W'.subspace.ι ≫ sY)
            (isGood_integralClosedSubspace D sY hY W')
            (IntegralClosedSubspace.comp_structure_of_comp_ι_eq D hpB hg)
            (IntegralClosedSubspace.isQuasiCompact_of_comp_ι_eq D hX hY hp hg) k (chernX W hW) =
        properCycleDegree D sX hX sY hY p W • chernComponentCycleOrZero D sY k chernY W') :
    ProperPushforwardChernComparison D hX hY hpB hp k chernX chernY where
  properPushforward_pushforward W W' g hg _hdom c :=
    properCyclePushforward_integralClosedSubspacePushforward D sX sY hX hY hpB hp W W' g hg k c
  componentCycle_comm := hcomm

/-- **The source's final step, from Stacks 0EQS along the component morphism and nothing else.**
For a single integral closed subspace `W ⊆ X`,

`p_*(c₁(p^*ℒ) ∩ [W]) = c₁(ℒ) ∩ p_*[W]`,

the right side being the degree of Stacks 0EP1, part (1), times the component cycle of the
closure `W'` of the image of `|W|`. The square of the reduction is discharged by
`AlgebraicGeometry.Space.properPushforwardChernComparison_of_componentCycle_comm`. -/
theorem properPushforward_firstChernComponentCycle_of_componentCycle_comm
    (hcomm : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D sX W = k + 1)
      (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (g : W.subspace.toFunctor ⟶ W'.subspace.toFunctor)
      (hg : g ≫ W'.subspace.ι = W.subspace.ι ≫ p)
      (_hdom : IsDominant D.site D.base D.base_mem g),
      properCyclePushforward D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W) (W'.subspace.ι ≫ sY)
            (isGood_integralClosedSubspace D sY hY W')
            (IntegralClosedSubspace.comp_structure_of_comp_ι_eq D hpB hg)
            (IntegralClosedSubspace.isQuasiCompact_of_comp_ι_eq D hX hY hp hg) k (chernX W hW) =
        properCycleDegree D sX hX sY hY p W • chernComponentCycleOrZero D sY k chernY W')
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (firstChernComponentCycle D sX hX k chernX W) =
      properCycleDegree D sX hX sY hY p W •
        firstChernComponentCycle D sY hY k chernY
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) p W) :=
  properPushforward_firstChernComponentCycle D hX hY hpB hp k chernX chernY
    (properPushforwardChernComparison_of_componentCycle_comm D hX hY hpB hp k chernX chernY
      hcomm) W

/-- **The converse of the source's steps (2)–(4).** If the projection formula holds for every
cycle `α ∈ Z_{k+1}(X)` then it holds on the fundamental cycle `[W]` of every integral closed
subspace `W ⊆ X`, which is the source's final step.

For `W` of δ-dimension `k + 1` this is the identity at `α = [W]` read coefficientwise: on the
left the cap product of Stacks 0EQJ takes `[W]` to the component cycle of `W`, and on the right
the pushforward of `[W]` is supported at the closure of the image of `|W|` with coefficient the
degree of Stacks 0EP1, part (1). For `W` of any other δ-dimension both sides vanish outright,
the component cycle of `W` being zero and a nonzero degree forcing `dim_δ(W') = dim_δ(W)`. -/
theorem properPushforward_firstChernComponentCycle_of_firstChernCapCycleMap
    (hgen : ∀ α : CycleGroup D sX (k + 1),
      properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (firstChernCapCycleMap D sX hX k chernX α) =
        firstChernCapCycleMap D sY hY k chernY
          (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 (k + 1) α))
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (firstChernComponentCycle D sX hX k chernX W) =
      properCycleDegree D sX hX sY hY p W •
        firstChernComponentCycle D sY hY k chernY
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) p W) := by
  by_cases hW : deltaDimension D sX W = k + 1
  · refine Subtype.ext (funext fun T => ?_)
    have hc := congrArg (fun c : CycleGroup D sY k => c.1 T)
      (hgen (integralCycle D sX (k + 1) W hW))
    rw [properPushforward_firstChernCapCoeff D hX hY hpB hp k chernX _ T,
      firstChernCapCoeff_properPushforward D hX hY hpB hp k chernY _ T,
      finsum_eq_single _ W (fun W₀ hW₀ => by
        rw [integralCycle_coe, integralCycleCoeff_eq_zero D W hW₀, zero_mul]),
      finsum_eq_single _ W (fun W₀ hW₀ => by
        rw [integralCycle_coe, integralCycleCoeff_eq_zero D W hW₀, zero_mul]),
      integralCycle_coe, integralCycleCoeff_self, one_mul, one_mul] at hc
    rw [hc, zsmul_cycle_coe_apply]
  · rw [firstChernComponentCycle_of_deltaDimension_ne D sX hX k chernX hW, map_zero]
    by_cases hdeg : properCycleDegree D sX hX sY hY p W = 0
    · rw [hdeg, zero_smul]
    · have hdim := deltaDimension_closureImage_of_properCycleDegree_ne_zero D sX hX sY hY p hdeg
      rw [firstChernComponentCycle_of_deltaDimension_ne D sY hY k chernY
          (by rw [hdim]; exact hW), smul_zero]

/-- **Stacks 0EQT, reduced to the source's final step, in both directions.** In Situation 0EDT
let `X/B` and `Y/B` be good, let `p : X ⟶ Y` be a proper morphism over `B`, let `ℒ` be an
invertible `𝒪_Y`-module and let `α` range over `Z_{k+1}(X)`. Then the projection formula

`p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α` in `Z_k(Y)`

holds for every `α` **exactly when** it holds on the fundamental cycle `[W]` of every integral
closed subspace `W ⊆ X`, that is when

`p_*(c₁(p^*ℒ) ∩ [W]) = deg(W/W') · (c₁(ℒ) ∩ [W'])`

for `W'` the closure of the image of `|W|` and `deg(W/W')` the degree of Stacks 0EP1, part (1).

Both directions are proved and nothing is assumed: the forward direction is
`AlgebraicGeometry.Space.properPushforward_firstChernComponentCycle_of_firstChernCapCycleMap`,
the reverse the source's steps (2)–(4),
`AlgebraicGeometry.Space.properPushforward_firstChernCapCycleMap_of_component`.

The cap products are the cycle-level cap product of Stacks 0EQJ and the pushforwards those of
Stacks 0EP1, taken along the quasi-compactness that properness of `p` supplies. The component
rules of `p^*ℒ` and of `ℒ` are the parameters `chernX` and `chernY`; the instance at the
canonical rules, where `c₁(p^*ℒ)` is the first Chern class of the genuine inverse image `p^*ℒ`
of Stacks 03LU, is
`AlgebraicGeometry.Space.properPushforward_canonicalFirstChernCapCycleMap_iff_component`.

The right-hand clause is Stacks 0EQS along the component morphism `p|_W : W ⟶ W'` of Stacks
0EEG, and it is open here; see the implementation notes. -/
@[stacks 0EQT "REDUCED, not proved: p_*(c_1(p^*L) ∩ α) = c_1(L) ∩ p_*α in Z_k(Y) for every α in
Z_{k+1}(X) IF AND ONLY IF it holds on the fundamental cycle [W] of every integral closed
subspace W of X. BOTH directions are proved and nothing is assumed, with the cap product of
Stacks 0EQJ and the pushforward of Stacks 0EP1. The remaining clause, at a single W, is Stacks
0EQS along the component morphism p|_W of Stacks 0EEG, which rests on Stacks 0EQ4 and is open in
this repository"]
theorem properPushforward_firstChernCapCycleMap_iff_component :
    (∀ α : CycleGroup D sX (k + 1),
        properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
            (firstChernCapCycleMap D sX hX k chernX α) =
          firstChernCapCycleMap D sY hY k chernY
            (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 (k + 1) α)) ↔
      ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
            (firstChernComponentCycle D sX hX k chernX W) =
          properCycleDegree D sX hX sY hY p W •
            firstChernComponentCycle D sY hY k chernY
              (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
                (D.isDecentSpace_of_isGood sY hY) p W) :=
  ⟨properPushforward_firstChernComponentCycle_of_firstChernCapCycleMap D hX hY hpB hp k chernX
    chernY, properPushforward_firstChernCapCycleMap_of_component D hX hY hpB hp k chernX chernY⟩

end Reduction

/-! ### Stacks 0EQT at the genuine inverse image `p^*ℒ` -/

section Canonical

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)
    (q : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **The component rule of `p^*ℒ`.** The component rule of Stacks 0EQJ at the genuine inverse
image `p^*ℒ` of Stacks 03LU: `AlgebraicGeometry.Space.canonicalFirstChernRule` at the module
`(AlgebraicGeometry.Space.modulePullback p).obj ℒ`, which is invertible by Stacks 0B8P,
`AlgebraicGeometry.Space.modulePullbackInvertible`.

This is what ties the left-hand side of Stacks 0EQT to `ℒ`: the rule is not a parameter, and no
choice is made on `X` beyond the one already made on `Y`. -/
abbrev canonicalPullbackFirstChernRule (k : ℤ) : FirstChernComponentCycleRule D sX k :=
  canonicalFirstChernRule D sX hX ((modulePullback D.site D.base D.base_mem q).obj L)
    (modulePullbackInvertible q L hL) k

/-- **Stacks 0EQT, reduced to the source's final step, with both component rules tied to `ℒ`.**
In Situation 0EDT let `X/B` and `Y/B` be good, let `p : X ⟶ Y` be a proper morphism over `B`,
let `ℒ` be an invertible `𝒪_Y`-module and let `α` range over `Z_{k+1}(X)`. Then

`p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α` in `Z_k(Y)`

holds for every `α` **exactly when** it holds on the fundamental cycle `[W]` of every integral
closed subspace `W ⊆ X`. Both directions are proved and nothing is assumed; this is
`AlgebraicGeometry.Space.properPushforward_firstChernCapCycleMap_iff_component` at the canonical
component rules of Stacks 0EQJ.

Here `c₁(p^*ℒ)` is the first Chern class of the *genuine* inverse image `p^*ℒ` of Stacks 03LU,
through `AlgebraicGeometry.Space.canonicalPullbackFirstChernRule`, and `c₁(ℒ)` that of `ℒ`,
through `AlgebraicGeometry.Space.canonicalFirstChernRule`; neither is a parameter, and both are
the rule `W ↦ div(t_W)` of Stacks 0EQJ at the canonical ratios of Stacks 0EPR.

The remaining clause, at a single `W`, is Stacks 0EQS along the component morphism
`p|_W : W ⟶ W'` of Stacks 0EEG, and is open here: Stacks 0EQS rests on the coefficient identity
of Stacks 0EQ4, which this repository does not prove. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisor`. -/
@[stacks 0EQT "REDUCED, not proved, with BOTH component rules tied to L rather than parametric:
p_*(c_1(p^*L) ∩ α) = c_1(L) ∩ p_*α in Z_k(Y) for every α in Z_{k+1}(X) IF AND ONLY IF it holds
on the fundamental cycle [W] of every integral closed subspace W of X. BOTH directions are
proved and nothing is assumed. c_1(p^*L) is the canonical rule of Stacks 0EQJ at the genuine
inverse image p^*L of Stacks 03LU, invertible by Stacks 0B8P, and c_1(L) the canonical rule at
L. The remaining clause, at a single W, is Stacks 0EQS along the component morphism p|_W of
Stacks 0EEG, which rests on Stacks 0EQ4 and is open in this repository"]
theorem properPushforward_canonicalFirstChernCapCycleMap_iff_component (hqB : q.hom ≫ sY = sX)
    (hq : IsProper D.site D.base D.base_mem q.hom) (k : ℤ) :
    (∀ α : CycleGroup D sX (k + 1),
        properCyclePushforward D sX hX sY hY hqB hq.2.1.2 k
            (firstChernCapCycleMap D sX hX k
              (canonicalPullbackFirstChernRule D hX hY q L hL k) α) =
          firstChernCapCycleMap D sY hY k (canonicalFirstChernRule D sY hY L hL k)
            (properCyclePushforward D sX hX sY hY hqB hq.2.1.2 (k + 1) α)) ↔
      ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        properCyclePushforward D sX hX sY hY hqB hq.2.1.2 k
            (firstChernComponentCycle D sX hX k
              (canonicalPullbackFirstChernRule D hX hY q L hL k) W) =
          properCycleDegree D sX hX sY hY q.hom W •
            firstChernComponentCycle D sY hY k (canonicalFirstChernRule D sY hY L hL k)
              (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
                (D.isDecentSpace_of_isGood sY hY) q.hom W) :=
  properPushforward_firstChernCapCycleMap_iff_component D hX hY hqB hq k _ _

end Canonical

end AlgebraicGeometry.Space

end
