module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.ZMod.Basic
public import StacksFrontier.Deformation.Examples.Linear.CoprimeCoverStagedTower

/-!
# The weak link of the staged gluing induction is not a consequence of the lifting data

`StacksFrontier/Deformation/Examples/Linear/CoprimeCoverStagedTower.lean` packages the deformation
theory that the gluing principle of Stacks 0DZ7 runs on — the tower of stages, the torsor
translation, the obstruction and its Bockstein-plus-cup-square variation, the annihilation of the
obstruction module by a power of the syntomic equation, and the Čech–descent gluing step — as the
structure `Deformation.Examples.CoprimeCover.CoverLiftTower`, and proves the staged induction from
it together with one further assertion,
`Deformation.Examples.CoprimeCover.CoverLiftTower.WeakLink`: that an `f ^ n`-divisible translate of
a class which rises two or more stages again rises that many stages.

This file shows that the further assertion is **genuinely further**. It builds a tower with four
stages — the nilpotence index at which the question first arises — satisfying every field of
`CoverLiftTower`, in which

* a class at stage one rises to the top stage,
* its translate by `f ^ n · 1` rises exactly one stage and no further, and
* the top stage of the global tower is **empty**.

So the weak link fails for this tower
(`Deformation.Examples.CoprimeCover.StagedIndependence.not_weakLink`) and so does the conclusion it
is used for (`Deformation.Examples.CoprimeCover.StagedIndependence.isEmpty_gl_top`). No derivation
of the weak link from the fields of `CoverLiftTower` exists, and the staged induction past two
stages is therefore not bookkeeping: it is an assertion about the deformation theory of the cover
that has to be proved from something the structure does not record.

## The tower

Take `B = ℤ`, `f = 2`, `n = 1`, `N = 3`, translation module `T₁ = ℤ` and obstruction module
`T₂ = ZMod 2`, which `2` annihilates. A stage-`k` carrier is a function `ℕ → ℤ` supported below
`k`, subject to the one further condition that its coordinate `0` vanish once `k` exceeds two;
reduction zeroes the top coordinate and the translation by `c` adds `c` to it, so the fibres of a
reduction are `ℤ`-torsors, freely and transitively.

The obstruction is non-zero exactly at stage two with non-zero coordinate `0`: a stage-two carrier
rises to stage three precisely when its coordinate `0` vanishes, which is what the extra condition
says. The stage-two translation moves coordinate `1` and the obstruction reads coordinate `0`, so
the variation of the obstruction along the torsor is identically zero — in particular it is a
Bockstein plus a cup-square with both terms zero, which is exactly the shape the variation formula
prescribes. That is why the formula is no help here: the obstruction at stage two is invisible to
the stage-two torsor and is decided by a coordinate the stage-**one** torsor moves.

The global tower is cut out inside the carriers: a global stage-`k` carrier has coordinate `0`
equal to `1` or to `2`, and there are none past stage two. Comaximality is what makes the gluing
field hold at stage zero — the carriers with coordinate `0` equal to `1` or to `2` meet every class
modulo `2`, so a stage-one carrier can always be translated by an even integer into the global
tower. And `1` and `2` are both non-zero, so no global carrier at stage two restricts to one that
rises to stage three: the gluing field holds vacuously there, and the top stage can be empty.

## Main definitions

* `Deformation.Examples.CoprimeCover.StagedIndependence.Stage` — the stage-`k` carriers.
* `Deformation.Examples.CoprimeCover.StagedIndependence.Glob` — the global stage-`k` carriers.
* `Deformation.Examples.CoprimeCover.StagedIndependence.badTower` — the tower itself.

## Main results

* `Deformation.Examples.CoprimeCover.StagedIndependence.not_weakLink` — the weak link fails.
* `Deformation.Examples.CoprimeCover.StagedIndependence.isEmpty_gl_top` — the top stage of the
  global tower is empty, so the conclusion of the staged induction fails too.
* `Deformation.Examples.CoprimeCover.StagedIndependence.exists_tower_not_weakLink` — the two
  together: a tower with the induction's base datum, no weak link, and an empty top stage.

## Implementation notes

**Why four stages and not three.** With `N ≤ 2` the staged induction needs no weak link at all
(`Deformation.Examples.CoprimeCover.CoverLiftTower.exists_gl_of_le_two`), because every stage at
which it has to restore the invariant has at most one stage left to rise, and one stage is what the
variation formula gives. The first tower that can separate the two is therefore one with `N = 3`,
and that is the one built here. Read back in the deformation theory: a kernel with `I³ = 0` is
handled by the lifting data alone, and the weak link is an assertion about `I⁴ = 0` and beyond.

**What this does not show.** It does not refute the weak link in the deformation theory of a
comaximal pair, and so does not refute the gluing principle or Stacks 0DZ7. A tower of sets knows
nothing of the extra structure the real tower carries — that the carriers are isomorphism classes
of flat algebra lifts, that the modules are `Ext` groups of a naive cotangent complex, and that
everything is natural in the ring. The claim is the exact one stated: the fields of
`CoverLiftTower` do not entail the weak link, so a proof of the gluing principle has to reach past
them.

## References

* [Stacks Project, Tag 0DZ7](https://stacks.math.columbia.edu/tag/0DZ7)
-/

@[expose] public noncomputable section

namespace Deformation.Examples.CoprimeCover.StagedIndependence

/-! ### The carriers -/

/-- **The stage-`k` carriers of the counterexample tower**: functions `ℕ → ℤ` supported below `k`,
whose coordinate `0` moreover vanishes once `k` exceeds two. The second condition is the only
source of obstruction in the tower: it makes a stage-two carrier rise to stage three exactly when
its coordinate `0` vanishes. -/
abbrev Stage (k : ℕ) : Type :=
  {v : ℕ → ℤ // (∀ i, k ≤ i → v i = 0) ∧ (2 < k → v 0 = 0)}

/-- Reduction to the previous stage: zero the top coordinate. -/
def red {k : ℕ} (v : Stage (k + 1)) : Stage k :=
  ⟨fun i => if i = k then 0 else v.1 i, by
    refine ⟨fun i hi => ?_, fun hk => ?_⟩
    · change (if i = k then (0 : ℤ) else v.1 i) = 0
      by_cases h : i = k
      · rw [ite_eq_left h]
      · rw [ite_eq_right h]
        exact v.2.1 i (by omega)
    · change (if (0 : ℕ) = k then (0 : ℤ) else v.1 0) = 0
      rw [ite_eq_right (show ¬((0 : ℕ) = k) by omega)]
      exact v.2.2 (by omega)⟩

/-- The translation action on a fibre of `red`: add `c` to the top coordinate. -/
def trans {k : ℕ} (c : ℤ) (v : Stage (k + 1)) : Stage (k + 1) :=
  ⟨fun i => if i = k then v.1 i + c else v.1 i, by
    refine ⟨fun i hi => ?_, fun hk => ?_⟩
    · change (if i = k then v.1 i + c else v.1 i) = 0
      rw [ite_eq_right (show ¬(i = k) by omega)]
      exact v.2.1 i hi
    · change (if (0 : ℕ) = k then v.1 0 + c else v.1 0) = 0
      rw [ite_eq_right (show ¬((0 : ℕ) = k) by omega)]
      exact v.2.2 hk⟩

/-- The obstruction: non-zero exactly at stage two with non-zero coordinate `0`. -/
def obs {k : ℕ} (v : Stage k) : ZMod 2 :=
  if k = 2 ∧ v.1 0 ≠ 0 then 1 else 0

/-- The all-zero carrier. -/
def zeroStage (k : ℕ) : Stage k := ⟨fun _ => 0, ⟨fun _ _ => rfl, fun _ => rfl⟩⟩

/-! ### Computation rules -/

/-- The coordinates of a reduction. -/
theorem red_val {k : ℕ} (v : Stage (k + 1)) (i : ℕ) :
    (red v).1 i = if i = k then 0 else v.1 i := rfl

/-- The coordinates of a translate. -/
theorem trans_val {k : ℕ} (c : ℤ) (v : Stage (k + 1)) (i : ℕ) :
    (trans c v).1 i = if i = k then v.1 i + c else v.1 i := rfl

/-- The coordinates of the zero carrier. -/
theorem zeroStage_val (k i : ℕ) : (zeroStage k).1 i = 0 := rfl

/-- The obstruction, unfolded. -/
theorem obs_eq {k : ℕ} (v : Stage k) : obs v = if k = 2 ∧ v.1 0 ≠ 0 then 1 else 0 := rfl

/-- Two carriers with the same coordinates are equal. -/
theorem stage_ext {k : ℕ} {v w : Stage k} (h : ∀ i, v.1 i = w.1 i) : v = w :=
  Subtype.ext (funext h)

/-- A stage-zero carrier is the zero one. -/
theorem stage_zero_eq (v : Stage 0) : v = zeroStage 0 :=
  stage_ext fun i => v.2.1 i (Nat.zero_le i)

/-- Reduction kills the zero carrier. -/
theorem red_zeroStage (k : ℕ) : red (zeroStage (k + 1)) = zeroStage k :=
  stage_ext fun i => by
    simp only [red_val, zeroStage_val, ite_self]

/-- The reduction of a stage-three carrier has coordinate `0` zero. -/
theorem red_three_val_zero (w : Stage 3) : (red w).1 0 = 0 := by
  rw [red_val, ite_eq_right (show ¬((0 : ℕ) = 2) by omega)]
  exact w.2.2 (by omega)

/-- Multiplication by two is the scalar action of `f ^ n` for `f = 2` and `n = 1`. -/
theorem two_pow_one_smul (b : ℤ) : (2 : ℤ) ^ 1 • b = 2 * b := by
  simp only [pow_one, smul_eq_mul]

/-! ### The torsor -/

/-- A translation does not move the reduction. -/
theorem red_trans {k : ℕ} (c : ℤ) (v : Stage (k + 1)) : red (trans c v) = red v :=
  stage_ext fun i => by
    by_cases h : i = k
    · simp only [red_val, ite_eq_left h]
    · simp only [red_val, trans_val, ite_eq_right h]

/-- Translating by zero does nothing. -/
theorem trans_zero {k : ℕ} (v : Stage (k + 1)) : trans (0 : ℤ) v = v :=
  stage_ext fun i => by
    by_cases h : i = k
    · simp only [trans_val, ite_eq_left h, add_zero]
    · simp only [trans_val, ite_eq_right h]

/-- Translation is an action of `ℤ`. -/
theorem trans_add {k : ℕ} (c d : ℤ) (v : Stage (k + 1)) :
    trans (c + d) v = trans c (trans d v) :=
  stage_ext fun i => by
    by_cases h : i = k
    · simp only [trans_val, ite_eq_left h]
      omega
    · simp only [trans_val, ite_eq_right h]

/-- The action is free. -/
theorem trans_eq_self {k : ℕ} (c : ℤ) (v : Stage (k + 1)) (h : trans c v = v) : c = 0 := by
  have h0 : (trans c v).1 k = v.1 k := by rw [h]
  rw [trans_val, ite_eq_left rfl] at h0
  omega

/-- The action is transitive on each fibre of `red`. -/
theorem exists_trans {k : ℕ} (v w : Stage (k + 1)) (h : red v = red w) :
    ∃ c : ℤ, trans c v = w := by
  refine ⟨w.1 k - v.1 k, stage_ext fun i => ?_⟩
  by_cases hi : i = k
  · subst hi
    rw [trans_val, ite_eq_left rfl]
    omega
  · have h' : (red v).1 i = (red w).1 i := congrFun (congrArg Subtype.val h) i
    rw [red_val, red_val, ite_eq_right hi, ite_eq_right hi] at h'
    rw [trans_val, ite_eq_right hi]
    exact h'

/-! ### The obstruction detects liftability by one stage -/

/-- A carrier whose coordinate `0` vanishes as far as the next stage demands is a reduction. -/
theorem exists_red_eq (k : ℕ) (v : Stage k) (h3 : 2 < k + 1 → v.1 0 = 0) :
    ∃ z : Stage (k + 1), red z = v := by
  refine ⟨⟨v.1, fun i hi => v.2.1 i (by omega), h3⟩, stage_ext fun i => ?_⟩
  by_cases hi : i = k
  · have hv : v.1 k = 0 := v.2.1 k le_rfl
    rw [red_val, ite_eq_left hi, hi, hv]
  · simp only [red_val, ite_eq_right hi]

/-- **The obstruction vanishes exactly when the carrier rises one stage.** -/
theorem obs_eq_zero_iff {k : ℕ} (v : Stage k) :
    obs v = 0 ↔ ∃ z : Stage (k + 1), red z = v := by
  refine ⟨fun h => exists_red_eq k v fun hk₃ => ?_, ?_⟩
  · by_cases hk : k = 2
    · by_contra h0
      rw [obs_eq, ite_eq_left ⟨hk, h0⟩] at h
      exact absurd h (by decide)
    · exact v.2.2 (by omega)
  · rintro ⟨z, hz⟩
    rw [obs_eq, ite_eq_right]
    rintro ⟨rfl, h0⟩
    exact h0 (hz ▸ red_three_val_zero z)

/-- A translation does not change the obstruction: at stage two the obstruction reads coordinate
`0` while the stage-two translation moves coordinate `1`, and at every other stage the obstruction
is zero. -/
theorem obs_trans {k : ℕ} (c : ℤ) (v : Stage (k + 1)) : obs (trans c v) = obs v := by
  by_cases hk : k + 1 = 2
  · have hk0 : ¬((0 : ℕ) = k) := by omega
    rw [obs_eq, obs_eq, trans_val, ite_eq_right hk0]
  · have h1 : ¬(k + 1 = 2 ∧ (trans c v).1 0 ≠ 0) := fun hc => hk hc.1
    have h2 : ¬(k + 1 = 2 ∧ v.1 0 ≠ 0) := fun hc => hk hc.1
    rw [obs_eq, obs_eq, ite_eq_right h1, ite_eq_right h2]

/-- `2` annihilates the obstruction module. -/
theorem two_pow_one_smul_eq_zero (t : ZMod 2) : (2 : ℤ) ^ 1 • t = 0 := by
  rw [pow_one, two_zsmul]
  revert t
  decide

/-! ### The global tower -/

/-- The condition cutting the global tower out of the carriers: coordinate `0` equal to `1` or to
`2`, and nothing past stage two. -/
def Adm (k : ℕ) (v : Stage k) : Prop :=
  k ≤ 2 ∧ (0 < k → v.1 0 = 1 ∨ v.1 0 = 2)

/-- **The global stage-`k` carriers.** -/
abbrev Glob (k : ℕ) : Type := {v : Stage k // Adm k v}

/-- Reduction of a global carrier. -/
def redGlob {k : ℕ} (x : Glob (k + 1)) : Glob k :=
  ⟨red x.1, by
    refine ⟨by have := x.2.1; omega, fun hk => ?_⟩
    have hx := x.2.2 (by omega)
    rw [red_val, ite_eq_right (show ¬((0 : ℕ) = k) by omega)]
    exact hx⟩

/-- A global stage-zero carrier is unique. -/
theorem glob_zero_eq (x y : Glob 0) : x = y :=
  Subtype.ext ((stage_zero_eq x.1).trans (stage_zero_eq y.1).symm)

/-- **The gluing step at stage zero is comaximality**: an even translation carries any stage-one
carrier onto one whose coordinate `0` is `1` or `2`, because those two meet both classes modulo
`2`. -/
theorem glue_zero (x : Glob 0) (z : Stage 1) (_h : red z = x.1) :
    ∃ (b : ℤ) (y : Glob 1), redGlob y = x ∧ y.1 = trans (2 * b) z := by
  obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Int.even_or_odd (z.1 0)
  · refine ⟨1 - m, ⟨trans (2 * (1 - m)) z, ⟨by omega, fun _ => Or.inr ?_⟩⟩,
      glob_zero_eq _ _, rfl⟩
    rw [trans_val, ite_eq_left rfl, hm]
    omega
  · refine ⟨-m, ⟨trans (2 * -m) z, ⟨by omega, fun _ => Or.inl ?_⟩⟩, glob_zero_eq _ _, rfl⟩
    rw [trans_val, ite_eq_left rfl, hm]
    omega

/-- **The gluing step at stage one is the identity**: a stage-two carrier above a global one is
already global, its coordinate `0` being untouched by the reduction. -/
theorem glue_one (x : Glob 1) (z : Stage 2) (h : red z = x.1) :
    ∃ (b : ℤ) (y : Glob 2), redGlob y = x ∧ y.1 = trans (2 * b) z := by
  have hz0 : z.1 0 = 1 ∨ z.1 0 = 2 := by
    have hx := x.2.2 (by omega)
    rw [← h] at hx
    simpa only [red_val, ite_eq_right (show ¬((0 : ℕ) = 1) by omega)] using hx
  refine ⟨0, ⟨z, ⟨by omega, fun _ => hz0⟩⟩, Subtype.ext h, ?_⟩
  rw [mul_zero, trans_zero]

/-- **The gluing step at stage two is vacuous**: a global carrier has coordinate `0` equal to `1`
or to `2`, and a stage-three carrier has it zero, so nothing lies above a global stage-two carrier.
This is what lets the top stage of the global tower be empty. -/
theorem glue_two (x : Glob 2) (z : Stage 3) (h : red z = x.1) : False := by
  have hx := x.2.2 (by omega)
  rw [← h, red_three_val_zero] at hx
  omega

/-- **The gluing step of the tower.** -/
theorem glue_stage : ∀ (k : ℕ) (x : Glob k) (z : Stage (k + 1)), red z = x.1 →
    ∃ (b : ℤ) (y : Glob (k + 1)), redGlob y = x ∧ y.1 = trans (2 * b) z
  | 0, x, z, h => glue_zero x z h
  | 1, x, z, h => glue_one x z h
  | 2, x, z, h => (glue_two x z h).elim
  | (_ + 3), x, _, _ => absurd x.2.1 (by omega)

/-! ### The tower, and the failure of the weak link -/

/-- **The counterexample tower**: four stages over `B = ℤ` with `f = 2`, `n = 1`, translation
module `ℤ` and obstruction module `ZMod 2`. Every field of `CoverLiftTower` holds. -/
def badTower : CoverLiftTower ℤ (2 : ℤ) 1 3 ℤ (ZMod 2) where
  Gl := Glob
  Gg := Stage
  res x := x.1
  redGl := redGlob
  redGg := red
  res_redGl _ := rfl
  tr := trans
  redGg_tr := red_trans
  tr_zero := trans_zero
  tr_add := trans_add
  tr_eq_self := trans_eq_self
  exists_tr := exists_trans
  ob := obs
  ob_eq_zero_iff := obs_eq_zero_iff
  bockstein _ := 0
  cupSquare _ _ := 0
  cupSquare_smul _ r _ := (smul_zero (r ^ 2)).symm
  ob_tr _ c y := by
    simpa only [LinearMap.zero_apply, add_zero] using obs_trans c y
  pow_smul_eq_zero := two_pow_one_smul_eq_zero
  glue k x z h := by
    obtain ⟨b, y, h1, h2⟩ := glue_stage k x z h
    refine ⟨b, y, h1, ?_⟩
    rw [h2, two_pow_one_smul]

/-- The reduction of the tower is `red`. -/
theorem badTower_redGg {k : ℕ} (v : Stage (k + 1)) : badTower.redGg v = red v := rfl

/-- The translation of the tower is `trans`. -/
theorem badTower_tr {k : ℕ} (c : ℤ) (v : Stage (k + 1)) : badTower.tr c v = trans c v := rfl

/-- The base datum of the staged induction: the unique global stage-zero carrier. -/
def glBase : badTower.Gl 0 := ⟨zeroStage 0, ⟨by omega, fun h => absurd h (by omega)⟩⟩

/-- Its restriction rises all three stages, which is what a flat lift of `B_g` over the thickening
provides. -/
theorem liftsTo_res_glBase : badTower.liftsTo 3 0 (badTower.res glBase) :=
  ⟨zeroStage 1, red_zeroStage 0, zeroStage 2, red_zeroStage 1, zeroStage 3,
    red_zeroStage 2, trivial⟩

/-- The zero carrier at stage one rises two stages, to the top of the tower. -/
theorem liftsTo_two_zeroStage : badTower.liftsTo 2 1 (zeroStage 1) :=
  ⟨zeroStage 2, red_zeroStage 1, zeroStage 3, red_zeroStage 2, trivial⟩

/-- **A stage-one carrier with coordinate `0` equal to `2` does not rise two stages.** A carrier
above it at stage two has the same coordinate `0`, and a stage-three carrier has coordinate `0`
zero. -/
theorem not_exists_red_chain (y : Stage 1) (hy : y.1 0 = 2) :
    ¬ ∃ z : Stage 2, red z = y ∧ ∃ w : Stage 3, red w = z ∧ True := by
  rintro ⟨z, hz, w, hw, -⟩
  have hz0 : z.1 0 = 0 := by
    rw [← hw]
    exact red_three_val_zero w
  have h' : (red z).1 0 = y.1 0 := congrFun (congrArg Subtype.val hz) 0
  rw [red_val, ite_eq_right (show ¬((0 : ℕ) = 1) by omega), hy] at h'
  omega

/-- **The `2`-divisible translate of the zero carrier does not rise two stages**, although it
rises one: its coordinate `0` is `2`. -/
theorem not_liftsTo_two_trans_zeroStage :
    ¬ badTower.liftsTo 2 1 (badTower.tr ((2 : ℤ) ^ 1 • (1 : ℤ)) (zeroStage 1)) :=
  not_exists_red_chain (trans ((2 : ℤ) ^ 1 • (1 : ℤ)) (zeroStage 1)) (by
    rw [trans_val, ite_eq_left rfl, zeroStage_val, two_pow_one_smul]
    omega)

/-- **The weak link fails in this tower.** Every field of `CoverLiftTower` holds for `badTower`, so
`Deformation.Examples.CoprimeCover.CoverLiftTower.WeakLink` is not a consequence of them: the
staged induction past two stages assumes something the lifting data does not provide. -/
theorem not_weakLink : ¬ badTower.WeakLink := fun h =>
  not_liftsTo_two_trans_zeroStage (h 0 (by omega) 1 (zeroStage 1) liftsTo_two_zeroStage)

/-- **The top stage of the global tower is empty.** So the conclusion of
`Deformation.Examples.CoprimeCover.CoverLiftTower.exists_gl_of_weakLink` fails for `badTower`, and
the weak link is not merely unproved from the lifting data but indispensable to that conclusion. -/
theorem isEmpty_gl_top : IsEmpty (badTower.Gl 3) :=
  ⟨fun x => absurd x.2.1 (by omega)⟩

/-- **The staged lifting data of a two-element cover does not entail the weak link, and does not
reach the top stage without it.** A tower with four stages, the base datum of the induction, no
weak link and an empty top stage.

Read back in the deformation theory of Stacks 0DZ7: the Čech splitting, the obstruction and its
quadratic variation, and the annihilation of the obstruction module by a power of the syntomic
equation together close the gluing principle for a kernel with `I³ = 0`
(`Deformation.Examples.CoprimeCover.CoverLiftTower.exists_gl_of_le_two`) and leave a genuine gap
beyond it. -/
theorem exists_tower_not_weakLink :
    ∃ (D : CoverLiftTower ℤ (2 : ℤ) 1 3 ℤ (ZMod 2)) (x : D.Gl 0),
      D.liftsTo 3 0 (D.res x) ∧ ¬ D.WeakLink ∧ IsEmpty (D.Gl 3) :=
  ⟨badTower, glBase, liftsTo_res_glBase, not_weakLink, isEmpty_gl_top⟩

end Deformation.Examples.CoprimeCover.StagedIndependence

end
