module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles

/-!
# Proper pushforward and intersecting with an invertible sheaf

In Situation 0EDT let `X/B` and `Y/B` be good, let `p : X ⟶ Y` be a **proper** morphism over
`B`, let `ℒ` be an invertible `𝒪_Y`-module and let `α ∈ Z_{k+1}(X)`. Stacks 0EQT is the
projection formula

`p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α` in `CH_k(Y)`.

This file proves it — at the level of cycles, which is finer than the source's statement in the
Chow group, and then in `CH_k(Y)` itself. The cap product is the canonical one of Stacks 0EQJ,
`AlgebraicGeometry.Space.firstChernCapCycleMap` and
`AlgebraicGeometry.Space.firstChernClassCap`, and the pushforward is the canonical one of
Stacks 0EP1, `AlgebraicGeometry.Space.properCyclePushforward`; no stand-in is introduced for
either.

## Main definitions

* `AlgebraicGeometry.Space.chernComponentCycleOrZero`: the component cycle
  `c₁(ℒ|_W) ∩ [W]` of Stacks 0EQJ on the subspace `W` itself, extended by zero to the integral
  closed subspaces of δ-dimension other than `k + 1`.
* `AlgebraicGeometry.Space.ProperPushforwardChernComparison`: the two carried inputs of the
  source's reduction — Stacks 0EP2 for the closed-immersion square of that reduction, and
  Stacks 0EQS along the component morphism of Stacks 0EEG.

## Main results

* `AlgebraicGeometry.Space.properPushforward_firstChernComponentCycle`: the source's final step,
  the identity for the cycle `[W]` of a single integral closed subspace, derived from the two
  carried inputs.
* `AlgebraicGeometry.Space.properPushforward_firstChernCapCycleMap_of_component`: **Stacks
  0EQT at the level of cycles**, from the identity for a single integral closed subspace taken
  as the hypothesis `hcomp`. This is the source's steps (2)–(4), and it is proved.
* `AlgebraicGeometry.Space.properPushforward_firstChernCapCycleMap`: **Stacks 0EQT** at the
  level of cycles, on the two carried inputs.
* `AlgebraicGeometry.Space.properPushforward_firstChernClassCap`: **Stacks 0EQT**, the identity
  in `CH_k(Y)` which the source states.

## Implementation notes

### Where properness is used

Properness of `p` enters in two places, and in both of them it is what makes the objects in the
statement exist, as the source says.

First, the pushforward of cycles `p_*` of Stacks 0EP1 is constructed in this repository for a
quasi-compact morphism — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles` — so the two pushforwards in
the statement are `AlgebraicGeometry.Space.properCyclePushforward` applied to the
quasi-compactness `hp.2.1.2` extracted from properness. The hypothesis is therefore consumed
inside the statement itself: it is an argument of both maps being compared. The local finiteness
of the family of image closures, Stacks 0ENZ, which the source invokes in step (3) of its proof
to know that `{W'_i}` is locally finite on `Y`, is used through the same quasi-compactness, in
`AlgebraicGeometry.Space.finite_properPushforwardFirstChernCapSupport` and
`AlgebraicGeometry.Space.finite_firstChernCapProperPushforwardSupport`.

Second, properness is what gives the component morphism `p|_W : W ⟶ W'` of Stacks 0EEG, along
which the source's final step takes place: `W ⟶ W'` is proper, hence quasi-compact, by
`AlgebraicGeometry.Space.IntegralClosedSubspace.isProper_of_comp_ι_eq`, and that is what lets
`(p|_W)_*` be formed at all. Both fields of
`AlgebraicGeometry.Space.ProperPushforwardChernComparison` are statements about that
pushforward, so properness of `p` occurs in their types too — through
`AlgebraicGeometry.Space.IntegralClosedSubspace.isQuasiCompact_of_comp_ι_eq`, which is Stacks
0EEG read along `hp`. Neither field can even be written down for a morphism which is not
proper.

### The grading

Both sides are elements of `Z_k(Y)`, and they are so for the reason the source gives. On the
left, `α` is a `(k+1)`-cycle on `X`, the cap product of Stacks 0EQJ carries `Z_{k+1}(X)` to
`Z_k(X)` — its component rule is indexed by the integral closed subspaces of δ-dimension
exactly `k + 1` — and `p_*` preserves the grading. On the right, `p_*α` is a `(k+1)`-cycle on
`Y` and the cap product on `Y` carries it to `Z_k(Y)`. No cycle group is transported along an
equality of degrees anywhere below, and the two component rules are rules for the same `k`.

### What is carried, and what is proved

The source proves Stacks 0EQT by writing `α = ∑ n_i [W_i]`, replacing `p` by
`∐ W_i ⟶ ∐ W'_i` and reducing to the case of `X` and `Y` integral, `p` dominant and
`α = [X]`, which is Stacks 0EQS. Two things are carried here, and they are exactly the two
steps of that reduction which this repository cannot take; everything else is proved.

* `AlgebraicGeometry.Space.ProperPushforwardChernComparison.properPushforward_pushforward`
  is **Stacks 0EP2** for the square formed by `i_W : W → X`, `i_{W'} : W' → Y`, `p` and the
  component morphism `g = p|_W`: pushing a `k`-cycle on `W` forward along `W → X → Y` is the
  same as pushing it forward along `W → W' → Y`.

  Stacks 0EP2 itself *is* proved in this library, as
  `AlgebraicGeometry.Space.properPushforwardInDimension_comp`, and it does not reach this
  square, for two reasons. It is stated for
  `AlgebraicGeometry.Space.properPushforwardInDimension`, a second construction of the
  pushforward of Stacks 0EP1 which this repository carries beside
  `AlgebraicGeometry.Space.properCyclePushforward` — the one the rest of this chapter uses,
  Stacks 0EQS and Stacks 0ER5 among them — and the two constructions are nowhere compared,
  although they are built from the same degree, `AlgebraicGeometry.Space.residueDegree` at the
  ambient generic point. And, more seriously, it is a statement about a composite of morphisms
  of ambient spaces, whereas the component cycle of Stacks 0EQJ is pushed forward along the
  closed immersion `i_W` by `AlgebraicGeometry.Space.integralClosedSubspacePushforward`, the
  pushforward of the localization sequence, which is compared with neither proper pushforward
  anywhere here: that comparison would need the subspace bookkeeping of
  `AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward` against the integral closed
  image along `i_W`, the invariance of the δ-dimension of a subspace under enlarging the
  ambient space, and the degree over the image along `i_W` to be `1`, none of which is
  available. So the square of the source's reduction, which has one closed immersion on each
  side, is out of reach even with Stacks 0EP2 in hand.
* `AlgebraicGeometry.Space.ProperPushforwardChernComparison.componentCycle_comm` is **Stacks
  0EQS** along the component morphism: for `W` of δ-dimension `k + 1`,
  `(p|_W)_*(c₁(p^*ℒ|_W) ∩ [W]) = deg(W/W') · (c₁(ℒ|_{W'}) ∩ [W'])`, the degree being the one of
  Stacks 0EP1, part (1), which is `0` exactly when the δ-dimension drops. Stacks 0EQS is proved
  in this library, as
  `AlgebraicGeometry.Space.properPushforward_divisorCycleOfSection` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisor`, but it does not reach
  this statement, for three reasons. Its conclusion is about
  `AlgebraicGeometry.Space.divisorCycleOfSection`, the divisor cycle of a chosen nonzero
  meromorphic section, whereas the component cycle of Stacks 0EQJ is the free parameter
  `AlgebraicGeometry.Space.FirstChernComponentCycleRule` — the same mismatch which
  `AlgebraicGeometry.Space.GysinProperPushforwardComparison` records for Stacks 0ER5. Its
  degree is `AlgebraicGeometry.Space.functionFieldDegreeAtGenericPoint` of `p|_W`, a degree of
  residue fields of `W` and `W'`, while the degree here is that of the ambient `X` and `Y`, and
  the comparison is the one described in the previous item. And it is itself conditional on the
  carried `AlgebraicGeometry.Space.ProperPushforwardNormRule`, which is Stacks 0EQ4, whose
  coefficient identity is not proved in this repository —
  `AlgebraicGeometry.Space.properPushforward_principalDivisorCycle_eq_iff` reduces Stacks 0EQ4
  to its coefficients at the prime divisors of `Y` and leaves the identity itself open. The
  δ-dimension-dropping case is contained in the same field,
  the degree being `0` there; the source passes over that case, and on the scheme side
  `StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward` carries it in the same way, for the
  same reason: nothing about an arbitrary component rule makes that pushforward vanish.

What is proved is the passage from a single integral closed subspace to an arbitrary cycle,
which is the source's steps (2)–(4) and is not formal: a cycle is an infinite formal sum, so
both sides are locally finite double sums, and the proof exchanges them. The exchange rests on
the local finiteness of `α`, of the component cycles, and of the family of image closures —
Stacks 0ENZ — exactly as the source's passage to `∐ W_i ⟶ ∐ W'_i` does, and it avoids forming
any disjoint union.

### `p^*ℒ`, and the reading of the two sides

The pullback of a sheaf of modules along a morphism of algebraic spaces does not exist in this
repository; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisor`. As there, and as in the
carried Stacks 0EQK, `p^*ℒ` is therefore not written down: the invertible sheaf on `X` enters
the cap product of Stacks 0EQJ only through its component rule, and `chernX` is the component
rule of `p^*ℒ` while `chernY` is that of `ℒ`. The sheaf `ℒ` itself does appear in the identity
in `CH_k(Y)`, as the argument of
`AlgebraicGeometry.Space.firstChernClassCap`, together with its invertibility.

Proper pushforward on Chow groups is not available here, only on cycles, so `p_*(c₁(p^*ℒ) ∩ α)`
is read as the class on `Y` of the pushforward of the cycle representing `c₁(p^*ℒ) ∩ α`. This
is the same reading that Stacks 0EQS and Stacks 0EQJ, case (1), already
use, and it is why the identity at the level of cycles — which is proved below and is strictly
finer — is the honest form of the lemma.

## References

* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
* [Stacks Project, Tag 0ENX](https://stacks.math.columbia.edu/tag/0ENX)
* [Stacks Project, Tag 0ENZ](https://stacks.math.columbia.edu/tag/0ENZ)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP2](https://stacks.math.columbia.edu/tag/0EP2)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQK](https://stacks.math.columbia.edu/tag/0EQK)
* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u w v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] Classical.propDecidable

/-! ### Exchanging the order of a double sum of integers -/

/-- A double `finsum` of integers may be summed in either order as soon as only finitely many
pairs contribute a nonzero term: both iterated sums equal the sum over all pairs. -/
theorem finsum_comm_of_finite {A B : Type*} (u : A → B → ℤ)
    (h : {ab : A × B | u ab.1 ab.2 ≠ 0}.Finite) :
    (∑ᶠ b : B, ∑ᶠ a : A, u a b) = ∑ᶠ a : A, ∑ᶠ b : B, u a b :=
  (finsum_curry (fun ba : B × A => u ba.2 ba.1)
    (h.preimage (Equiv.prodComm B A).injective.injOn)).symm.trans <|
      (finsum_comp_equiv (Equiv.prodComm B A)).trans
        (finsum_curry (fun ab : A × B => u ab.1 ab.2) h)

/-! ### The component cycle on the subspace itself -/

section ComponentCycle

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (chern : FirstChernComponentCycleRule D sX k)

/-- The component cycle `c₁(ℒ|_W) ∩ [W]` of Stacks 0EQJ on the integral closed subspace `W`
itself, extended by zero to the subspaces of δ-dimension other than `k + 1`, where the rule has
no value and where `W` does not occur in a `(k+1)`-cycle. -/
def chernComponentCycleOrZero (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    CycleGroup D (W.subspace.ι ≫ sX) k :=
  if hW : deltaDimension D sX W = k + 1 then chern W hW else 0

/-- On a subspace of δ-dimension `k + 1` the extended component cycle is the value of the
rule. -/
theorem chernComponentCycleOrZero_of_deltaDimension_eq
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D sX W = k + 1) :
    chernComponentCycleOrZero D sX k chern W = chern W hW :=
  dite_eq_left hW

/-- On a subspace of δ-dimension other than `k + 1` the extended component cycle is zero. -/
theorem chernComponentCycleOrZero_of_deltaDimension_ne
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D sX W ≠ k + 1) :
    chernComponentCycleOrZero D sX k chern W = 0 :=
  dite_eq_right hW

/-- The ambient component cycle of Stacks 0EQJ is the pushforward along `i : W → X` of the
extended component cycle on `W`: in the branch of δ-dimension `k + 1` by definition, and in the
other branch because the pushforward of the zero cycle is zero. -/
theorem firstChernComponentCycle_eq_pushforward
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    firstChernComponentCycle D sX hX k chern W =
      integralClosedSubspacePushforward D sX hX W k
        (chernComponentCycleOrZero D sX k chern W) := by
  by_cases hW : deltaDimension D sX W = k + 1
  · rw [firstChernComponentCycle_of_deltaDimension_eq D sX hX k chern hW,
      chernComponentCycleOrZero_of_deltaDimension_eq D sX k chern hW]
  · rw [firstChernComponentCycle_of_deltaDimension_ne D sX hX k chern hW,
      chernComponentCycleOrZero_of_deltaDimension_ne D sX k chern hW, map_zero]

end ComponentCycle

/-- The coefficient of a cycle scaled by an integer is the scaled coefficient. -/
private theorem zsmul_cycle_apply (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (s : X ⟶ D.space) (k : ℤ)
    (c : CycleGroup D s k) (d : ℤ)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) : (d • c).1 T = d * c.1 T := by
  change d • c.1 T = d * c.1 T
  rw [zsmul_eq_mul, Int.cast_id]

/-! ### The component morphism of Stacks 0EEG -/

section ComponentHom

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} {sY : Y ⟶ D.space}

/-- A morphism of integral closed subspaces over a morphism `p : X ⟶ Y` over `B` is itself a
morphism over `B`. This is what the pushforward of cycles along it asks for. -/
theorem IntegralClosedSubspace.comp_structure_of_comp_ι_eq {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    {W' : IntegralClosedSubspace D.site D.base D.base_mem Y}
    {g : W.subspace.toFunctor ⟶ W'.subspace.toFunctor}
    (hg : g ≫ W'.subspace.ι = W.subspace.ι ≫ p) :
    g ≫ (W'.subspace.ι ≫ sY) = W.subspace.ι ≫ sX := by
  rw [← Category.assoc, hg, Category.assoc, hpB]

/-- **Stacks 0EEG for a proper morphism.** A morphism of integral closed subspaces over a
proper `p : X ⟶ Y` is quasi-compact, being proper. This is what makes the pushforward of cycles
along the component morphism `p|_W : W ⟶ W'` exist. -/
theorem IntegralClosedSubspace.isQuasiCompact_of_comp_ι_eq (hX : D.IsGood sX) (hY : D.IsGood sY)
    {p : X ⟶ Y} (hp : IsProper D.site D.base D.base_mem p)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    {W' : IntegralClosedSubspace D.site D.base D.base_mem Y}
    {g : W.subspace.toFunctor ⟶ W'.subspace.toFunctor}
    (hg : g ≫ W'.subspace.ι = W.subspace.ι ≫ p) :
    IsQuasiCompact D.site D.base D.base_mem g :=
  (IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 p hp W W' g
    hg).2.1.2

end ComponentHom

/-! ### The two carried inputs of the source's reduction -/

/-- The two inputs of the source's reduction of Stacks 0EQT to Stacks 0EQS which this
repository cannot supply. Both are statements about the pushforward of cycles along the
component morphism `g = p|_W : W ⟶ W'` of Stacks 0EEG, which exists because `p` is proper, so
neither can be stated for a morphism which is not proper.

The first field is **Stacks 0EP2** for the closed-immersion square of the reduction, and the
second is **Stacks 0EQS** along `g`. Both tags have statements in this library —
`AlgebraicGeometry.Space.properPushforwardInDimension_comp` and
`AlgebraicGeometry.Space.properPushforward_divisorCycleOfSection` — and neither reaches the
assertion below; the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCap` record in detail
why. Everything else in the source's proof is proved. -/
structure ProperPushforwardChernComparison (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)
    {p : X ⟶ Y} (hpB : p ≫ sY = sX) (hp : IsProper D.site D.base D.base_mem p) (k : ℤ)
    (chernX : FirstChernComponentCycleRule D sX k)
    (chernY : FirstChernComponentCycleRule D sY k) : Prop where
  /-- **Stacks 0EP2 for the square of the source's reduction.** For an integral closed subspace
  `W ⊆ X`, an integral closed subspace `W' ⊆ Y` and a dominant morphism `g : W ⟶ W'` over `p` —
  the data of Stacks 0EEG — pushing a `k`-cycle on `W` forward along `W → X → Y` is pushing it
  forward along `W → W' → Y`. -/
  properPushforward_pushforward :
    ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (g : W.subspace.toFunctor ⟶ W'.subspace.toFunctor)
      (hg : g ≫ W'.subspace.ι = W.subspace.ι ≫ p)
      (_hdom : IsDominant D.site D.base D.base_mem g)
      (c : CycleGroup D (W.subspace.ι ≫ sX) k),
      properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (integralClosedSubspacePushforward D sX hX W k c) =
        integralClosedSubspacePushforward D sY hY W' k
          (properCyclePushforward D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
            (W'.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY W')
            (IntegralClosedSubspace.comp_structure_of_comp_ι_eq D hpB hg)
            (IntegralClosedSubspace.isQuasiCompact_of_comp_ι_eq D hX hY hp hg) k c)
  /-- **Stacks 0EQS along the component morphism.** For an integral closed subspace `W ⊆ X` of
  δ-dimension `k + 1` and the dominant `g : W ⟶ W'` over `p` of Stacks 0EEG,

  `(p|_W)_*(c₁(p^*ℒ|_W) ∩ [W]) = deg(W/W') · (c₁(ℒ|_{W'}) ∩ [W'])`,

  the degree being that of Stacks 0EP1, part (1), which is `0` exactly where the δ-dimension
  drops; in that case the assertion is that the pushforward vanishes, which is the case the
  source passes over. -/
  componentCycle_comm :
    ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
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
        properCycleDegree D sX hX sY hY p W • chernComponentCycleOrZero D sY k chernY W'

/-! ### Stacks 0EQT -/

section Projection

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)
    {p : X ⟶ Y} (hpB : p ≫ sY = sX) (hp : IsProper D.site D.base D.base_mem p) (k : ℤ)
    (chernX : FirstChernComponentCycleRule D sX k)
    (chernY : FirstChernComponentCycleRule D sY k)

include hX hY hpB hp

/-- **The source's final step.** For a single integral closed subspace `W ⊆ X` the pushforward
of the component cycle of `W` is the degree of Stacks 0EP1, part (1), times the component cycle
of the closure `W'` of the image of `|W|`, that is

`p_*(c₁(p^*ℒ) ∩ [W]) = c₁(ℒ) ∩ p_*[W]`.

The component morphism `g : W ⟶ W'` of Stacks 0EEG is proper, hence quasi-compact, because `p`
is proper, so the two carried inputs apply to it: the first turns the left side into the
pushforward along `W → W' → Y`, and the second — Stacks 0EQS — evaluates the pushforward along
`g`. When `dim_δ(W) ≠ k + 1` both sides vanish, the component cycle of `W` being zero and a
nonzero degree forcing `dim_δ(W') = dim_δ(W)`. -/
theorem properPushforward_firstChernComponentCycle
    (cmp : ProperPushforwardChernComparison D hX hY hpB hp k chernX chernY)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (firstChernComponentCycle D sX hX k chernX W) =
      properCycleDegree D sX hX sY hY p W •
        firstChernComponentCycle D sY hY k chernY
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) p W) := by
  obtain ⟨g, hg⟩ := IntegralClosedSubspace.exists_hom_closureImage D.site D.base D.base_mem
    hY.1 (D.isDecentSpace_of_isGood sY hY) p W
  have hdom := IntegralClosedSubspace.isDominant_of_comp_ι_eq_closureImage D.site D.base
    D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) p W g hg
  rw [firstChernComponentCycle_eq_pushforward D sX hX k chernX W,
    cmp.properPushforward_pushforward W _ g hg hdom (chernComponentCycleOrZero D sX k chernX W)]
  by_cases hW : deltaDimension D sX W = k + 1
  · rw [chernComponentCycleOrZero_of_deltaDimension_eq D sX k chernX hW,
      cmp.componentCycle_comm W hW _ g hg hdom, map_zsmul,
      firstChernComponentCycle_eq_pushforward D sY hY k chernY]
  · rw [chernComponentCycleOrZero_of_deltaDimension_ne D sX k chernX hW, map_zero, map_zero]
    by_cases hdeg : properCycleDegree D sX hX sY hY p W = 0
    · rw [hdeg, zero_smul]
    · have hdim := deltaDimension_closureImage_of_properCycleDegree_ne_zero D sX hX sY hY p hdeg
      rw [firstChernComponentCycle_of_deltaDimension_ne D sY hY k chernY
          (by rw [hdim]; exact hW), smul_zero]

/-- Only finitely many integral closed subspaces `W` carrying a nonzero coefficient of `α` have
the generic point of `T` in the closure of the image of `|W|`, by Stacks 0ENZ. -/
private theorem exists_finite_of_ambientGenericPoint_mem_closure_image
    (α : CycleGroup D sX (k + 1)) (T : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    ∃ F : Set (IntegralClosedSubspace D.site D.base D.base_mem X), F.Finite ∧
      ∀ W, α.1 W ≠ 0 → T.ambientGenericPoint D.site D.base D.base_mem ∈
        closure (pointsMap D.site D.base D.base_mem X p ''
          subspacePointSet D.site D.base D.base_mem X W.subspace) → W ∈ F := by
  obtain ⟨hlf, -⟩ := locallyFinite_closure_image_pointsMap D sX hX sY hY hpB hp.2.1.2
    (cycleSupportFamily D α.1) (isClosed_cycleSupportFamily D sX hX α.1) α.2.1
  obtain ⟨V, hV, hVfin⟩ := hlf (T.ambientGenericPoint D.site D.base D.base_mem)
  refine ⟨_, hVfin, fun W hα hmem => ⟨_, ?_, mem_of_mem_nhds hV⟩⟩
  simpa only [cycleSupportFamily_of_ne_zero D α.1 hα] using hmem

/-- At a fixed integral closed subspace `T ⊆ Y` only finitely many pairs `(W, Z)` of integral
closed subspaces of `X` contribute to the coefficient of `p_*(c₁(p^*ℒ) ∩ α)`.

A contributing pair has `|Z| ⊆ |W|`, because the component cycle of `W` is carried by `W`, and
`T` for the closure of the image of `|Z|`; so the generic point of `T` lies in the closure of
the image of `|W|`, and only finitely many `W` occurring in `α` have that property, by Stacks
0ENZ. For each of them the contributing `Z` are finitely many, again by Stacks 0ENZ applied to
the component cycle of `W`. -/
theorem finite_properPushforwardFirstChernCapSupport (α : CycleGroup D sX (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    {a : IntegralClosedSubspace D.site D.base D.base_mem X ×
        IntegralClosedSubspace D.site D.base D.base_mem X |
      α.1 a.1 * (firstChernComponentCycle D sX hX k chernX a.1).1 a.2 *
        properCycleMult D sX hX sY hY p a.2 T ≠ 0}.Finite := by
  obtain ⟨hlf, -⟩ := locallyFinite_closure_image_pointsMap D sX hX sY hY hpB hp.2.1.2
    (cycleSupportFamily D α.1) (isClosed_cycleSupportFamily D sX hX α.1) α.2.1
  obtain ⟨V, hV, hVfin⟩ := hlf (T.ambientGenericPoint D.site D.base D.base_mem)
  obtain ⟨F, hF, hFmem⟩ := exists_finite_of_ambientGenericPoint_mem_closure_image D hX hY hpB hp
    k α T
  refine (Set.Finite.prod hF (Set.Finite.biUnion hF
    (t := fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
      {Z : IntegralClosedSubspace D.site D.base D.base_mem X |
        (firstChernComponentCycle D sX hX k chernX W).1 Z ≠ 0 ∧
          IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) p Z = T})
    fun W _ => finite_properCycleFibre D sX hX sY hY hpB hp.2.1.2
      (firstChernComponentCycle D sX hX k chernX W).1
      (firstChernComponentCycle D sX hX k chernX W).2.1 T)).subset ?_
  rintro ⟨W, Z⟩ hne
  have hprod : α.1 W * (firstChernComponentCycle D sX hX k chernX W).1 Z *
      properCycleMult D sX hX sY hY p Z T ≠ 0 := hne
  have hα : α.1 W ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hprod)
  have hc : (firstChernComponentCycle D sX hX k chernX W).1 Z ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hprod)
  have hm : properCycleMult D sX hX sY hY p Z T ≠ 0 := right_ne_zero_of_mul hprod
  have hZim : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) p Z = T :=
    ((properCycleMult_ne_zero_iff D sX hX sY hY p Z T).1 hm).1
  have hZW : subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X W.subspace :=
    subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX k chernX W Z hc
  have hmemZ : T.ambientGenericPoint D.site D.base D.base_mem ∈
      closure (pointsMap D.site D.base D.base_mem X p ''
        subspacePointSet D.site D.base D.base_mem X Z.subspace) := by
    rw [← IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) p Z, hZim]
    exact ⟨_, rfl⟩
  have hWmem : W ∈ F := hFmem W hα (closure_mono (Set.image_mono hZW) hmemZ)
  exact Set.mk_mem_prod hWmem (Set.mem_biUnion hWmem ⟨hc, hZim⟩)

/-- At a fixed integral closed subspace `T ⊆ Y` only finitely many pairs `(W, W')` of an
integral closed subspace of `X` and one of `Y` contribute to the coefficient of
`c₁(ℒ) ∩ p_*α`.

A contributing pair has `W'` for the closure of the image of `|W|`, so `W'` is determined by
`W`; and the generic point of `T` lies in `|W'|`, because the component cycle of `W'` is
carried by `W'`. Only finitely many `W` occurring in `α` have that property, by Stacks 0ENZ. -/
theorem finite_firstChernCapProperPushforwardSupport (α : CycleGroup D sX (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    {a : IntegralClosedSubspace D.site D.base D.base_mem X ×
        IntegralClosedSubspace D.site D.base D.base_mem Y |
      α.1 a.1 * properCycleMult D sX hX sY hY p a.1 a.2 *
        (firstChernComponentCycle D sY hY k chernY a.2).1 T ≠ 0}.Finite := by
  obtain ⟨F, hF, hFmem⟩ := exists_finite_of_ambientGenericPoint_mem_closure_image D hX hY hpB hp
    k α T
  refine (hF.image fun W => (W, IntegralClosedSubspace.closureImage D.site D.base D.base_mem
    hY.1 (D.isDecentSpace_of_isGood sY hY) p W)).subset ?_
  rintro ⟨W, W'⟩ hne
  have hprod : α.1 W * properCycleMult D sX hX sY hY p W W' *
      (firstChernComponentCycle D sY hY k chernY W').1 T ≠ 0 := hne
  have hα : α.1 W ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hprod)
  have hm : properCycleMult D sX hX sY hY p W W' ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hprod)
  have hc : (firstChernComponentCycle D sY hY k chernY W').1 T ≠ 0 := right_ne_zero_of_mul hprod
  have hWeq : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) p W = W' :=
    ((properCycleMult_ne_zero_iff D sX hX sY hY p W W').1 hm).1
  refine ⟨W, hFmem W hα ?_, congrArg (Prod.mk W) hWeq⟩
  rw [← IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) p W, hWeq]
  exact subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sY hY k chernY W' T hc
    ⟨_, rfl⟩

/-- **The pushforward of a cap product, expanded.** The coefficient of `p_*(c₁(p^*ℒ) ∩ α)` at an
integral closed subspace `T ⊆ Y` is the `α`-weighted sum over the integral closed subspaces
`W ⊆ X` of the coefficient of `p_*(c₁(p^*ℒ) ∩ [W])` there.

Both the cap product and the pushforward are coefficientwise sums, so the composite is a double
sum, which is exchanged by
`AlgebraicGeometry.Space.finite_properPushforwardFirstChernCapSupport`. -/
theorem properPushforward_firstChernCapCoeff (α : CycleGroup D sX (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
        (firstChernCapCycleMap D sX hX k chernX α)).1 T =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X, α.1 W *
        (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (firstChernComponentCycle D sX hX k chernX W)).1 T := by
  have step : (∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        (firstChernCapCycleMap D sX hX k chernX α).1 Z *
          properCycleMult D sX hX sY hY p Z T) =
      ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
          α.1 W * (firstChernComponentCycle D sX hX k chernX W).1 Z *
            properCycleMult D sX hX sY hY p Z T :=
    finsum_congr fun Z => by
      rw [firstChernCapCycleMap_apply]
      exact finsum_mul' _ _ (hasFiniteSupport_firstChernCapCoeff D sX hX k chernX α Z)
  rw [properPushforward_apply, step, finsum_comm_of_finite _
    (finite_properPushforwardFirstChernCapSupport D hX hY hpB hp k chernX α T)]
  refine finsum_congr fun W => ?_
  rw [properPushforward_apply, mul_finsum' _ _ (hasFiniteSupport_properCycleMult D sX hX sY hY
    hpB hp.2.1.2 (firstChernComponentCycle D sX hX k chernX W).1
    (firstChernComponentCycle D sX hX k chernX W).2.1 T)]
  exact finsum_congr fun Z => mul_assoc _ _ _

/-- **The cap product of a pushforward, expanded.** The coefficient of `c₁(ℒ) ∩ p_*α` at an
integral closed subspace `T ⊆ Y` is the `α`-weighted sum over the integral closed subspaces
`W ⊆ X` of the degree of Stacks 0EP1, part (1), times the coefficient at `T` of the component
cycle of the closure of the image of `|W|`.

The inner sum over the integral closed subspaces of `Y` has a single term, the multiplicity of
Stacks 0EP1 vanishing away from that closure. -/
theorem firstChernCapCoeff_properPushforward (α : CycleGroup D sX (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    (firstChernCapCycleMap D sY hY k chernY
        (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 (k + 1) α)).1 T =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X, α.1 W *
        (properCycleDegree D sX hX sY hY p W *
          (firstChernComponentCycle D sY hY k chernY
            (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
              (D.isDecentSpace_of_isGood sY hY) p W)).1 T) := by
  have step : (∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem Y,
        (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 (k + 1) α).1 W' *
          (firstChernComponentCycle D sY hY k chernY W').1 T) =
      ∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem Y,
        ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
          α.1 W * properCycleMult D sX hX sY hY p W W' *
            (firstChernComponentCycle D sY hY k chernY W').1 T :=
    finsum_congr fun W' => by
      rw [properPushforward_apply]
      exact finsum_mul' _ _ (hasFiniteSupport_properCycleMult D sX hX sY hY hpB hp.2.1.2 α.1
        α.2.1 W')
  rw [firstChernCapCycleMap_apply, step, finsum_comm_of_finite _
    (finite_firstChernCapProperPushforwardSupport D hX hY hpB hp k chernY α T)]
  refine finsum_congr fun W => ?_
  have hmult : properCycleMult D sX hX sY hY p W (IntegralClosedSubspace.closureImage D.site
        D.base D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) p W) =
      properCycleDegree D sX hX sY hY p W := by
    unfold properCycleMult
    split_ifs with h
    · rfl
    · exact absurd rfl h
  rw [finsum_eq_single _ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) p W) fun W' hW' => by
      rw [properCycleMult_eq_zero_of_ne D sX hX sY hY p W hW'.symm, mul_zero, zero_mul],
    hmult, mul_assoc]

/-- **Stacks 0EQT at the level of cycles, from the case of a single integral closed subspace.**
In Situation 0EDT let `X/B` and `Y/B` be good, let `p : X ⟶ Y` be proper over `B`, let `ℒ` be
an invertible `𝒪_Y`-module and let `α ∈ Z_{k+1}(X)`. If

`p_*(c₁(p^*ℒ) ∩ [W]) = c₁(ℒ) ∩ p_*[W]`

for every integral closed subspace `W ⊆ X` — the hypothesis `hcomp`, which is the source's final
step — then

`p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α` in `Z_k(Y)`.

This is the content of the source's steps (2)–(4), where the reduction to a single integral
closed subspace is performed by passing to `∐ W_i ⟶ ∐ W'_i`. Here the two sides are expanded
into locally finite double sums and the sums are exchanged, which needs no disjoint union; only
the subspaces carrying a nonzero coefficient of `α` are compared. -/
theorem properPushforward_firstChernCapCycleMap_of_component
    (hcomp : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
          (firstChernComponentCycle D sX hX k chernX W) =
        properCycleDegree D sX hX sY hY p W •
          firstChernComponentCycle D sY hY k chernY
            (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
              (D.isDecentSpace_of_isGood sY hY) p W))
    (α : CycleGroup D sX (k + 1)) :
    properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
        (firstChernCapCycleMap D sX hX k chernX α) =
      firstChernCapCycleMap D sY hY k chernY
        (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 (k + 1) α) := by
  refine Subtype.ext (funext fun T => ?_)
  rw [properPushforward_firstChernCapCoeff D hX hY hpB hp k chernX α T,
    firstChernCapCoeff_properPushforward D hX hY hpB hp k chernY α T]
  refine finsum_congr fun W => ?_
  have h : (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
        (firstChernComponentCycle D sX hX k chernX W)).1 T =
      properCycleDegree D sX hX sY hY p W *
        (firstChernComponentCycle D sY hY k chernY
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) p W)).1 T := by
    rw [hcomp W]
    exact zsmul_cycle_apply D sY k _ _ T
  rw [h]

/-- **Stacks 0EQT, at the level of cycles.** In Situation 0EDT let `X/B` and `Y/B` be good, let
`p : X ⟶ Y` be a proper morphism over `B`, let `ℒ` be an invertible `𝒪_Y`-module and let
`α ∈ Z_{k+1}(X)`. Then

`p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α` in `Z_k(Y)`,

an identity of `k`-cycles, hence also of classes in `CH_k(Y)`.

The cap products are the cycle-level cap product of Stacks 0EQJ, with the component rule of
`p^*ℒ` on `X` and of `ℒ` on `Y`, and the pushforwards are those of Stacks 0EP1, taken along the
quasi-compactness that properness of `p` supplies. The two carried inputs are the fields of
`AlgebraicGeometry.Space.ProperPushforwardChernComparison`, both of them statements about the
pushforward along the component morphism `p|_W : W ⟶ W'` of Stacks 0EEG, which is proper
because `p` is: Stacks 0EP2 for the square of the source's reduction, and Stacks 0EQS along
`p|_W`, which is the source's final step. The passage from a single integral closed subspace to
an arbitrary cycle is proved. -/
@[stacks 0EQT "at the level of cycles: p_*(c_1(p^*L) ∩ α) = c_1(L) ∩ p_*α in Z_k(Y) for α in
Z_{k+1}(X), with the cap product of Stacks 0EQJ and the pushforward of Stacks 0EP1; on the two
carried inputs of ProperPushforwardChernComparison — Stacks 0EP2 for the closed-immersion
square of the source's reduction, and Stacks 0EQS along the component morphism p|_W of Stacks
0EEG, which is proper
because p is; the component rule of p^*L is the parameter chernX, the repository having no
pullback of sheaves of modules; the reduction to a single subspace is PROVED"]
theorem properPushforward_firstChernCapCycleMap
    (cmp : ProperPushforwardChernComparison D hX hY hpB hp k chernX chernY)
    (α : CycleGroup D sX (k + 1)) :
    properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
        (firstChernCapCycleMap D sX hX k chernX α) =
      firstChernCapCycleMap D sY hY k chernY
        (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 (k + 1) α) :=
  properPushforward_firstChernCapCycleMap_of_component D hX hY hpB hp k chernX chernY
    (properPushforward_firstChernComponentCycle D hX hY hpB hp k chernX chernY cmp) α

/-- **Stacks 0EQT.** In Situation 0EDT let `X/B` and `Y/B` be good, let `p : X ⟶ Y` be a proper
morphism over `B`, let `α ∈ Z_{k+1}(X)` and let `ℒ` be an invertible sheaf on `Y`. Then

`p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α` in `CH_k(Y)`.

The right side is the cap product of Stacks 0EQJ on `Y`,
`AlgebraicGeometry.Space.firstChernClassCap` at `ℒ`, applied to the pushforward of cycles
`p_*α`. Proper pushforward on Chow groups is not available in this repository, only on cycles,
so the left side is the class on `Y` of the pushforward of the cycle representing
`c₁(p^*ℒ) ∩ α`, which is the reading Stacks 0EQS and Stacks 0EQJ, case (1), already
use. The identity holds already at the level of cycles, which is
`AlgebraicGeometry.Space.properPushforward_firstChernCapCycleMap`. -/
@[stacks 0EQT "p_*(c_1(p^*L) ∩ α) = c_1(L) ∩ p_*α in CH_k(Y) for α in Z_{k+1}(X), the right side
being the cap product firstChernClassCap of Stacks 0EQJ at the invertible L, the left the class
on Y of the pushforward CYCLE, proper pushforward of Chow classes being unavailable here; on the
two carried inputs of ProperPushforwardChernComparison — Stacks 0EP2 for the closed-immersion
square of the source's reduction and Stacks 0EQS along the component morphism of Stacks 0EEG,
proper because p is; the component rule of p^*L is the parameter chernX"]
theorem properPushforward_firstChernClassCap
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1) (hL : IsInvertibleSheaf D sY hY L)
    {CH : Type w} [AddCommGroup CH] (chow : ChowTarget.{u, w, v} D sY hY k CH)
    (cmp : ProperPushforwardChernComparison D hX hY hpB hp k chernX chernY)
    (α : CycleGroup D sX (k + 1)) :
    chow.cls (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k
        (firstChernCapCycleMap D sX hX k chernX α)) =
      firstChernClassCap D sY hY L k hL chernY chow
        (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 (k + 1) α) := by
  rw [properPushforward_firstChernCapCycleMap D hX hY hpB hp k chernX chernY cmp α]
  rfl

end Projection

end AlgebraicGeometry.Space

end
