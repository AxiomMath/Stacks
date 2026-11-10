module

public import StacksFrontier.Deformation.Examples.Linear.CoprimeCoverStagedTowerIndependence

/-!
# Carrying a divisible correction up the whole tower: the condition that closes the weak link

`StacksFrontier/Deformation/Examples/Linear/CoprimeCoverStagedTower.lean` packages the deformation
theory the gluing principle of Stacks 0DZ7 runs on as
`Deformation.Examples.CoprimeCover.CoverLiftTower` and proves the staged induction from it together
with one further assertion,
`Deformation.Examples.CoprimeCover.CoverLiftTower.WeakLink`: that an `f ^ n`-divisible translate of
a class which rises two or more stages again rises that many stages.
`StacksFrontier/Deformation/Examples/Linear/CoprimeCoverStagedTowerIndependence.lean` builds a tower
in which every field of the bundle holds, the weak link fails, and the top stage is empty, so the
induction past a kernel with `I³ = 0` needs something the bundle does not record.

This file names that something. The condition is that an `f ^ n`-divisible translation at one stage
is covered by a **coherent system of self-maps of all the stages above it**: a transport along the
tower whose bottom component is the translation and each of whose components reduces to the
previous one. That is `Deformation.Examples.CoprimeCover.CoverLiftTower.DivisibleTransport`. It
implies the weak link — indeed the stability of rising *any* number of stages, with no restriction
to two or more
(`Deformation.Examples.CoprimeCover.CoverLiftTower.liftsTo_tr_pow_smul_of_divisibleTransport`) —
hence carries the tower to its top stage at a general nilpotent kernel, and it fails in the
counterexample tower, so the two results do not collide.

## Main definitions

* `Deformation.Examples.CoprimeCover.CoverLiftTower.DivisibleTransport` — the condition: every
  `f ^ n`-divisible translation is the bottom of a reduction-compatible system of self-maps of the
  higher stages.
* `Deformation.Examples.CoprimeCover.CoverLiftTower.OneStageTranslationLift` — the one-stage form
  of the same idea, recorded only to be dismissed: it is a theorem of the bundle, not a hypothesis.

## Main results

* `Deformation.Examples.CoprimeCover.CoverLiftTower.oneStageTranslationLift` — the one-stage form
  holds in every tower.
* `Deformation.Examples.CoprimeCover.CoverLiftTower.liftsTo_tr_pow_smul_of_divisibleTransport` —
  granted a divisible transport, an `f ^ n`-divisible translation preserves rising `j` stages, for
  every `j` and at every stage.
* `Deformation.Examples.CoprimeCover.CoverLiftTower.weakLink_of_divisibleTransport` — hence the
  weak link.
* `Deformation.Examples.CoprimeCover.CoverLiftTower.exists_gl_of_divisibleTransport` — hence the
  tower reaches its top stage, for every `N`, which is the gluing principle at a general nilpotent
  kernel rather than only at `I³ = 0`.
* `Deformation.Examples.CoprimeCover.CoverLiftTower.divisibleTransport_of_pow_smul_eq_zero` — the
  condition is consistent with every field of the bundle: where `f ^ n` annihilates the translation
  module it holds in every tower, by the identity transport.
* `Deformation.Examples.CoprimeCover.StagedIndependence.not_divisibleTransport` — it fails in the
  counterexample tower of
  `Deformation.Examples.CoprimeCover.StagedIndependence.exists_tower_not_weakLink`.
* `Deformation.Examples.CoprimeCover.StagedIndependence.exists_tower_not_divisibleTransport` — the
  facts about that tower together: the one-stage form holds in it, the divisible transport fails,
  and so do the weak link and the conclusion of the induction.

## Implementation notes

**Why the one-stage form is not a condition at all.** The first thing one writes down is: a
stage-`(k + 1)` class with a lift one stage up has an `f ^ n`-divisible translate with a lift one
stage up. That is `CoverLiftTower.OneStageTranslationLift`, and it is a *theorem* — it is
`CoverLiftTower.liftsTo_one_tr_pow_smul` with the two `liftsTo 1`s unfolded, so it follows from the
variation formula `ob_tr` and the annihilation of the obstruction module. Being a theorem of the
bundle it cannot imply the weak link, which is not one; `badTower` satisfies it and refutes the
weak link (`StagedIndependence.exists_tower_not_divisibleTransport`).

**Why no condition phrased through `tr` alone can work.** The next thing one hopes is that the
translation itself lifts: that a stage-`(k + 2)` lift `z` of `y` has an `f ^ n`-divisible translate
lying over `tr (f ^ n • b) y`. No tower has that property, for a formal reason. `redGg_tr` says a
translation does not move the reduction, so every translate of `z` lies over `y` again, and
`tr (f ^ n • b) y = y` forces `f ^ n • b = 0` by freeness of the action (`tr_eq_self`). The fibre
of `redGg` over `y` and the fibre over its translate are disjoint, and no translation at any stage
maps one into the other. A map covering a translation is therefore not a translation, and a
condition that is to deliver one has to quantify over it.

**Why one such map is not enough, and hence the shape of the condition.** Suppose the condition
hands us, for each stage-`(k + 2)` lift `z` of `y`, a stage-`(k + 2)` lift `w` of
`tr (f ^ n • b) y`. The staged induction needs more: it has to know that `w` rises as far as `z`
did, and the number of remaining stages is arbitrary. Re-applying the condition one stage up is
impossible, because the move `z ↦ w` is not a translation and the condition speaks only of
translations. What does propagate is a whole system: a self-map of each stage above `k + 1`, each
covering the one below it, the bottom one being the translation. Then the induction on the length
of a lifting chain transports it term by term, and it needs no restriction on the number of
remaining stages at all — the weak link's `2 ≤ N - (k + 1)` is simply not used.

**Why the condition holds in the deformation situation.** The correction the staged argument has to
apply is the `D(g)`-share of the Čech splitting of the comparison class on the overlap, and
`Deformation.Examples.CoprimeCover.exists_eq_add_pow_smul` makes that share divisible by *any*
prescribed power of `f`. By
`Deformation.Examples.CoprimeCover.exists_towerProj_eq_pow_smul` a class so divisible rises as far
up the tower of coefficient modules as one likes: the correction comes from a class with
coefficients in the honest ideal `I^(k+1) ⊆ A'`, not merely in the one graded piece
`I^(k+1)/I^(k+2)` of it that acts at stage `k + 1`. A single class with coefficients in `I^(k+1)`
acts on the lifts over `A'/I^(m+1)` for *every* `m` at once — the gauge action of the class on the
deformation groupoid, whose first-order shadow is the `Ext¹`-torsor translation `tr` and whose
second-order term is the cup-square of the field `ob_tr` — and those actions commute with reduction
because they are induced by one class over `A'`. A coherent system of self-maps covering the
translation is exactly what that provides, which is why the condition has this shape: what the
local-global analysis of the cover supplies is one class acting at all stages at once, not a
translation at a single stage.

**Why it is an assertion and not a consequence.** The bundle records only the first two orders of
that action, and the elementary description of it — twisting by a class whose coefficient ideal is
square-zero — reaches only the stages `m ≤ 2k + 1` (see the implementation notes of
`StacksFrontier/Deformation/Examples/Linear/CoprimeCoverStagedTower.lean`, where the same bound is
what stops the natural repair of the weak link). Past that range the condition asserts the
existence of the gauge action itself. It is an assertion about the deformation theory of the cover,
exactly as the weak link is, and it is carried as a hypothesis for the same reason.

**What is not claimed.** The condition is sufficient for the staged induction, not necessary: a
different route to the gluing principle need not pass through it, and even within this argument it
is consumed only at the classes the Čech splitting produces. It is also not vacuous in either
direction: `CoverLiftTower.divisibleTransport_of_pow_smul_eq_zero` shows it is consistent with
every field of the bundle, and `StagedIndependence.not_divisibleTransport` shows it is not a
consequence of them. No Stacks attribute is claimed, here or in the modules this one builds on; the
condition is open, as is the weak link it replaces.

## References

* [Stacks Project, Tag 0DZ7](https://stacks.math.columbia.edu/tag/0DZ7)
* [Stacks Project, Tag 07M8](https://stacks.math.columbia.edu/tag/07M8)
* [Stacks Project, Tag 08S7](https://stacks.math.columbia.edu/tag/08S7)
-/

@[expose] public noncomputable section

universe u

namespace Deformation.Examples.CoprimeCover

namespace CoverLiftTower

variable {B : Type u} [CommRing B] {f : B} {n N : ℕ} {T₁ T₂ : Type u}
  [AddCommGroup T₁] [Module B T₁] [AddCommGroup T₂] [Module B T₂]
  (D : CoverLiftTower B f n N T₁ T₂)

/-! ### The one-stage form of the condition is a theorem of the bundle -/

/-- **The one-stage form of "the translation lifts":** if a stage-`(k + 1)` class `y` has a lift at
stage `k + 2`, then so does each of its `f ^ n`-divisible translates.

This is stated only to be dismissed. It is not an extra condition but a theorem of the bundle
(`CoverLiftTower.oneStageTranslationLift`), being the variation formula `ob_tr` read through
`CoverLiftTower.liftsTo_one_iff`, and so it cannot imply `CoverLiftTower.WeakLink`. What the staged
induction needs is the same statement with "a lift at stage `k + 2`" replaced by "a lift that
itself rises as far as the one it replaces", and that is `CoverLiftTower.DivisibleTransport`. -/
def OneStageTranslationLift : Prop :=
  ∀ (k : ℕ) (b : T₁) (y : D.Gg (k + 1)) (z : D.Gg (k + 2)), D.redGg z = y →
    ∃ w : D.Gg (k + 2), D.redGg w = D.tr (f ^ n • b) y

/-- **Every tower lifts a divisible translation by one stage.** An `f ^ n`-divisible translation
changes neither the obstruction (`CoverLiftTower.ob_tr_pow_smul`) nor therefore liftability by one
stage (`CoverLiftTower.liftsTo_one_tr_pow_smul`), and a lift of `y` at stage `k + 2` is exactly a
witness that `y` is liftable by one stage.

So `CoverLiftTower.OneStageTranslationLift` is no addition to the bundle, and in particular is not
the missing step: `badTower` satisfies it and refutes the weak link. -/
theorem oneStageTranslationLift : D.OneStageTranslationLift := by
  intro k b y z hz
  obtain ⟨w, hw, -⟩ := D.liftsTo_one_tr_pow_smul k b y ⟨z, hz, trivial⟩
  exact ⟨w, hw⟩

/-! ### The condition: a divisible translation is covered by a transport of the tower -/

/-- **A divisible translation is covered by a transport of the whole tower above it.** For every
stage `k` and every class `b` there is a self-map `Φ j` of each stage `k + 1 + j` such that `Φ 0`
is the translation by `f ^ n • b` and each `Φ (j + 1)` covers `Φ j`, in the sense that
`redGg (Φ (j + 1) z) = Φ j (redGg z)`.

**Why this is true in the deformation situation.** The correction to be applied is the `D(g)`-share
of a Čech splitting, which `Deformation.Examples.CoprimeCover.exists_eq_add_pow_smul` may take
divisible by any prescribed power of `f`; by
`Deformation.Examples.CoprimeCover.exists_towerProj_eq_pow_smul` such a share comes from a class
with coefficients in the ideal `I^(k+1)` of `A'` itself, not merely in the graded piece
`I^(k+1)/I^(k+2)` that acts at stage `k + 1`. A single class over `A'` acts on the lifts over
`A'/I^(m+1)` for every `m` at once — the gauge action on the deformation groupoid, whose
first-order shadow is the `Ext¹`-torsor translation `tr` and whose second-order term is the
cup-square of the field `ob_tr` — and those actions commute with reduction because they come from
one class. That system of compatible self-maps is what this asks for, with the translation as its
bottom component.

**Why it is an assertion and not a consequence.** The bundle records only the first two orders of
the gauge action, and the elementary description of the action — twisting by a class with
square-zero coefficient ideal — reaches only the stages `m ≤ 2k + 1`. So past that range the
condition asserts the existence of the action itself, and it is indeed independent of the fields:
`Deformation.Examples.CoprimeCover.StagedIndependence.not_divisibleTransport`. It is carried as a
hypothesis for the same reason `CoverLiftTower.WeakLink` is, and it implies that hypothesis
(`CoverLiftTower.weakLink_of_divisibleTransport`) at every nilpotence index, not only where two
stages remain. -/
def DivisibleTransport : Prop :=
  ∀ (k : ℕ) (b : T₁), ∃ Φ : ∀ j : ℕ, D.Gg (k + 1 + j) → D.Gg (k + 1 + j),
    (∀ y : D.Gg (k + 1), Φ 0 y = D.tr (f ^ n • b) y) ∧
      ∀ (j : ℕ) (z : D.Gg (k + 1 + j + 1)), D.redGg (Φ (j + 1) z) = Φ j (D.redGg z)

/-- **Granted a divisible transport, an `f ^ n`-divisible translation preserves rising any number
of stages.** The transport carries a lifting chain above `y` term by term to a lifting chain above
the translate: the induction is on the length of the chain, and at each step the component of the
transport one stage higher produces the next term, its covering property identifying the reduction.

This is stronger than `CoverLiftTower.WeakLink` in two ways: there is no restriction to two or more
remaining stages, and the number of stages risen is arbitrary rather than tied to `N`. -/
theorem liftsTo_tr_pow_smul_of_divisibleTransport (hT : D.DivisibleTransport)
    (j k : ℕ) (b : T₁) (y : D.Gg (k + 1)) (hy : D.liftsTo j (k + 1) y) :
    D.liftsTo j (k + 1) (D.tr (f ^ n • b) y) := by
  obtain ⟨Φ, hΦ0, hΦ⟩ := hT k b
  have key : ∀ (m i : ℕ) (z : D.Gg (k + 1 + i)),
      D.liftsTo m (k + 1 + i) z → D.liftsTo m (k + 1 + i) (Φ i z) := by
    intro m
    induction m with
    | zero => intro i z _; exact D.liftsTo_zero _ _
    | succ m ih =>
      intro i z hz
      rw [D.liftsTo_succ] at hz
      obtain ⟨u, hu1, hu2⟩ := hz
      rw [D.liftsTo_succ]
      exact ⟨Φ (i + 1) u, by rw [hΦ i u, hu1], ih (i + 1) u hu2⟩
  have h := key j 0 y hy
  rwa [hΦ0 y] at h

/-- **A divisible transport implies the weak link.** The weak link is the special case where the
number of stages risen is the number remaining and at least two of them remain; neither restriction
is used. -/
theorem weakLink_of_divisibleTransport (hT : D.DivisibleTransport) : D.WeakLink :=
  fun k _ b y hy => D.liftsTo_tr_pow_smul_of_divisibleTransport hT _ k b y hy

/-- **The tower reaches its top stage under a divisible transport**, for every number of stages.

With `CoverLiftTower.exists_gl_of_weakLink` this is the gluing principle of Stacks 0DZ7 at a
general nilpotent kernel: the staged induction of that theorem, whose only hypothesis beyond the
lifting data was the weak link, now runs on a condition about the cover's local-global analysis.
`CoverLiftTower.exists_gl_of_le_two` remains the statement for `I³ = 0`, where no condition beyond
the bundle is needed at all. -/
theorem exists_gl_of_divisibleTransport (hT : D.DivisibleTransport) (x₀ : D.Gl 0)
    (h₀ : D.liftsTo N 0 (D.res x₀)) : Nonempty (D.Gl N) :=
  D.exists_gl_of_weakLink (D.weakLink_of_divisibleTransport hT) x₀ h₀

/-- **The condition is consistent with every field of the bundle.** Where `f ^ n` annihilates the
translation module as well as the obstruction module, every divisible translation is the identity
and the identity transport covers it, so every such tower has a divisible transport.

This is the check that the condition is not vacuously false — that the fields of `CoverLiftTower`
do not refute it — the complement of
`Deformation.Examples.CoprimeCover.StagedIndependence.not_divisibleTransport`, which shows they do
not prove it either. -/
theorem divisibleTransport_of_pow_smul_eq_zero (h : ∀ b : T₁, f ^ n • b = 0) :
    D.DivisibleTransport := by
  intro k b
  refine ⟨fun _ y => y, fun y => ?_, fun j z => rfl⟩
  rw [h b, D.tr_zero]

end CoverLiftTower

/-! ### The counterexample tower has no divisible transport -/

namespace StagedIndependence

/-- **The counterexample tower fails the condition.** In `badTower` the obstruction at stage two is
decided by coordinate `0`, which the stage-**one** translation moves, and no carrier at stage three
has that coordinate non-zero. A transport covering the translation by `2` at stage one would have
to raise coordinate `0` by `2` at every higher stage, while reduction preserves that coordinate and
every stage-three carrier has it zero: the stage-three component of the transport forces coordinate
`0` of the stage-two component to be `0`, and the stage-two component forces it to be `2`.

So `Deformation.Examples.CoprimeCover.CoverLiftTower.DivisibleTransport` is not a consequence of
the fields of `CoverLiftTower`, and the independence result and
`Deformation.Examples.CoprimeCover.CoverLiftTower.exists_gl_of_divisibleTransport` are consistent:
the tower whose top stage is empty is a tower without a divisible transport. -/
theorem not_divisibleTransport : ¬ badTower.DivisibleTransport := by
  intro hT
  obtain ⟨Φ, hΦ0, hΦ⟩ := hT 0 1
  have hA : ∀ v : Stage 1, Φ 0 v = trans ((2 : ℤ) ^ 1 • (1 : ℤ)) v := hΦ0
  have hB : ∀ v : Stage 2, red (Φ 1 v) = Φ 0 (red v) := hΦ 0
  have hC : ∀ v : Stage 3, red (Φ 2 v) = Φ 1 (red v) := hΦ 1
  have eRed3 : ∀ v : Stage 3, (red v).1 0 = v.1 0 := fun v => by
    rw [red_val, ite_eq_right (show ¬((0 : ℕ) = 2) by omega)]
  have eRed2 : ∀ v : Stage 2, (red v).1 0 = v.1 0 := fun v => by
    rw [red_val, ite_eq_right (show ¬((0 : ℕ) = 1) by omega)]
  have hz1 : red (red (zeroStage 3)) = zeroStage 1 := by
    rw [red_zeroStage, red_zeroStage]
  have h1 : (Φ 1 (red (zeroStage 3))).1 0 = 0 :=
    ((congrFun (congrArg Subtype.val (hC (zeroStage 3))) 0).symm.trans
        (eRed3 (Φ 2 (zeroStage 3)))).trans
      ((show Stage 3 from Φ 2 (zeroStage 3)).2.2 (by omega))
  have hL : (red (Φ 1 (red (zeroStage 3)))).1 0 = 0 :=
    (eRed2 (Φ 1 (red (zeroStage 3)))).trans h1
  have hR : (Φ 0 (red (red (zeroStage 3)))).1 0 = 0 :=
    (congrFun (congrArg Subtype.val (hB (red (zeroStage 3)))) 0).symm.trans hL
  have hRval : (Φ 0 (red (red (zeroStage 3)))).1 0 = (2 : ℤ) ^ 1 • (1 : ℤ) := by
    rw [hA, hz1, trans_val, ite_eq_left rfl, zeroStage_val, zero_add]
  have hc : ((2 : ℤ) ^ 1 • (1 : ℤ)) = 0 := hRval.symm.trans hR
  rw [two_pow_one_smul] at hc
  omega

/-- **The counterexample tower, read against both candidate conditions.** The one-stage form of
"the translation lifts" holds in it — as it does in every tower — while the divisible transport
fails, and so do the weak link and the conclusion of the staged induction.

The first conjunct is why the one-stage form is not the missing step: it is a theorem of the bundle
and holds here, yet the weak link fails. The others are why the divisible transport is consistent
with the independence result: it is refuted by exactly the tower that refutes the conclusion. -/
theorem exists_tower_not_divisibleTransport :
    ∃ (D : CoverLiftTower ℤ (2 : ℤ) 1 3 ℤ (ZMod 2)) (x : D.Gl 0),
      D.liftsTo 3 0 (D.res x) ∧ D.OneStageTranslationLift ∧ ¬ D.DivisibleTransport ∧
        ¬ D.WeakLink ∧ IsEmpty (D.Gl 3) :=
  ⟨badTower, glBase, liftsTo_res_glBase, badTower.oneStageTranslationLift,
    not_divisibleTransport, not_weakLink, isEmpty_gl_top⟩

end StagedIndependence

end Deformation.Examples.CoprimeCover

end
