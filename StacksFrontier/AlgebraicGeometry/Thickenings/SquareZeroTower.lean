module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension

/-!
# Iterating the realization of a square-zero extension

`Stacks.Thickenings.squareZeroExtension_realization` ([Stacks, Tag 05YV]) turns a surjection
`𝒪' ⟶ 𝒪_Y` of sheaves of rings on a scheme `Y`, with **square-zero** quasi-coherent kernel, into
a scheme on the space of `Y` with structure sheaf `𝒪'`.  An argument that has to realize a sheaf
of rings whose kernel is merely *nilpotent* cannot call it once: it must filter the kernel so
that the successive quotients are square-zero, and apply the tag once per step.  This file
provides that iteration.

A single step is `Stacks.Thickenings.SquareZeroStep`: a first-order thickening `Y ⟶ Y'`
compatible with the structure morphisms to a fixed base `S`.  Such a step is exactly what Tag
05YV produces (`Stacks.Thickenings.SquareZeroStep.ofRealization`) and, by the converse half of
the same tag, exactly what produces one
(`Stacks.Thickenings.SquareZeroStep.exists_squareZeroExtension`), so nothing is lost by phrasing
the iteration in terms of steps rather than of extensions.

## The invariant

What a consumer needs from the iteration is not the bare sequence of schemes but the
identification of the structure sheaf of each stage with a prescribed sheaf.  That identification
is carried as a *parameter*: the theorems below take an invariant

`P : ℕ → (Y : Scheme) → (Y ⟶ S) → Prop`

which the consumer instantiates with the property that identifies the stage, supplies at stage
`0`, and propagates across a step by exhibiting a square-zero extension and its realization.
The theorems then return the invariant at every stage, so the identification at the top — the
thing the argument was after — comes back with it.  Nothing about sheaves of rings appears in the
statements, which is what lets one file carry the iteration for every use of it.

## Main definitions

* `Stacks.Thickenings.SquareZeroStep`: one square-zero step over a base.

## Main results

* `Stacks.Thickenings.SquareZeroStep.ofRealization` and
  `Stacks.Thickenings.SquareZeroStep.exists_squareZeroExtension`: steps and square-zero
  extensions determine one another, by the two halves of [Stacks, Tag 05YV].
* `Stacks.Thickenings.exists_squareZeroTower`: **the tower exists.** As soon as the invariant
  propagates across a step there is an `ℕ`-indexed sequence of schemes over `S`, consecutive
  stages joined by a step, satisfying the invariant at every stage.
* `Stacks.Thickenings.exists_thickening_of_iterate`: **the top of a finite tower**, which is what
  an argument with a nilpotent kernel consumes: `N` applications of Tag 05YV produce a single
  scheme over `S` satisfying the invariant at level `N`, together with a thickening of the bottom
  stage into it.

## Implementation notes

The tower is returned as its components — the stages, their structure morphisms and the steps —
rather than as a new structure, because a structure for it already exists:
`Stacks.PuncturedSpectrumPicard.ThickeningTower` of
`StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.FormalTower` is an `ℕ`-indexed sequence of
schemes with first-order thickenings between consecutive stages, which is this tower minus the
base.  Given the components returned here, `⟨obj, fun n => (step n).immersion,
fun n => (step n).isFirstOrder⟩` is such a tower on the nose, so a consumer wanting that
packaging has it without a second copy of the type being introduced; a consumer wanting the base
needs the `toBase` and the `over_base` field of the steps, which `ThickeningTower` does not carry.
Lifting the base into `ThickeningTower` itself would make the Picard-descent file that declares
it the home of this notion, which is why it is not done here.

`Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood` is a third `ℕ`-indexed sequence of
schemes, and the one this is least like: its stages live inside a fixed ambient scheme and are
cut out by the powers of one ideal sheaf, whereas the stages here are *produced* one at a time by
Tag 05YV and are not subschemes of anything given in advance.

## References

* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Thickenings

/-! ### One square-zero step -/

/-- **One square-zero step over a base.** The scheme carrying `g' : Y' ⟶ S` is a first-order
thickening of the one carrying `g : Y ⟶ S`, compatibly with the two structure morphisms.

This is the shape of what [Stacks, Tag 05YV] produces out of a square-zero extension of `𝒪_Y`
with quasi-coherent kernel, and — by the converse half of the tag — of nothing else; see
`Stacks.Thickenings.SquareZeroStep.ofRealization` and
`Stacks.Thickenings.SquareZeroStep.exists_squareZeroExtension`. -/
structure SquareZeroStep {S : Scheme.{u}} {Y Y' : Scheme.{u}} (g : Y ⟶ S) (g' : Y' ⟶ S) where
  /-- The first-order thickening of the lower stage by the upper one. -/
  immersion : Y ⟶ Y'
  isFirstOrder : IsFirstOrderThickening immersion
  over_base : immersion ≫ g' = g

namespace SquareZeroStep

variable {S Y Y' : Scheme.{u}} {g : Y ⟶ S} {g' : Y' ⟶ S}

/-- A step is in particular a thickening: the two stages have the same underlying space. -/
theorem isThickening (s : SquareZeroStep g g') : IsThickening s.immersion :=
  s.isFirstOrder.isThickening

/-- **Tag 05YV produces a step.** The scheme realizing a square-zero extension of `𝒪_Y` with
quasi-coherent kernel sits one square-zero step above `Y`, over the same base. -/
def ofRealization {E : SquareZeroExtension g} (r : Realization E) :
    SquareZeroStep g r.toBase :=
  ⟨r.immersion, r.immersion_isFirstOrder, r.over_base⟩

/-- The thickening of the step `ofRealization r` is the immersion of the realization `r`. -/
@[simp]
theorem ofRealization_immersion {E : SquareZeroExtension g} (r : Realization E) :
    (ofRealization r).immersion = r.immersion :=
  rfl

/-- **Conversely, a step comes from a square-zero extension.** This is the converse half of
[Stacks, Tag 05YV], `Stacks.Thickenings.firstOrderThickening_squareZeroExtension`, read on a
step: the step's own thickening is realized by an extension of the structure sheaf of the lower
stage whose realization is the upper stage.

Together with `Stacks.Thickenings.SquareZeroStep.ofRealization` this says that phrasing the
iteration in terms of steps loses nothing against phrasing it in terms of extensions. -/
theorem exists_squareZeroExtension (s : SquareZeroStep g g') :
    ∃ E : SquareZeroExtension (s.immersion ≫ g'),
      ∃ r : Realization E, r.ambient = Y' ∧ HEq r.immersion s.immersion ∧ HEq r.toBase g' :=
  firstOrderThickening_squareZeroExtension s.immersion g' s.isFirstOrder

/-- **The extension a step comes from, with its kernel identified.** The direct image of the
kernel of the extension along the step's own thickening is the kernel of the structure-sheaf
comparison of that thickening, i.e. the ideal sheaf cutting the lower stage out of the upper one.

This is the form an iteration consumes: the two hypotheses of
`Stacks.Thickenings.SquareZeroExtension.pushforward` are statements about the kernel of the
extension, so an argument that supplies them has to recognize that kernel, and
`Stacks.Thickenings.SquareZeroStep.exists_squareZeroExtension` leaves it anonymous. -/
theorem exists_squareZeroExtension_kernel (s : SquareZeroStep g g') :
    ∃ E : SquareZeroExtension (s.immersion ≫ g'),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pushforward s.immersion).obj E.I ≅
        CategoryTheory.Limits.kernel
          (SheafOfModules.unitToPushforwardObjUnit s.immersion.toRingCatSheafHom)) ∧
      ∃ r : Realization E, r.ambient = Y' ∧ HEq r.immersion s.immersion ∧ HEq r.toBase g' :=
  firstOrderThickening_squareZeroExtension_kernel s.immersion g' s.isFirstOrder

end SquareZeroStep

/-! ### Building a tower by iterating Tag 05YV -/

section Construction

variable {S : Scheme.{u}}

/-- A stage of a tower under construction: a scheme over `S` satisfying the invariant `P` at
level `n`.  Auxiliary to `Stacks.Thickenings.exists_squareZeroTower`, where it carries the
simultaneous recursion on the scheme, its structure morphism and the invariant. -/
private structure Stage (P : ℕ → (Y : Scheme.{u}) → (Y ⟶ S) → Prop) (n : ℕ) where
  obj : Scheme.{u}
  toBase : obj ⟶ S
  property : P n obj toBase

variable (P : ℕ → (Y : Scheme.{u}) → (Y ⟶ S) → Prop)
  (hstep : ∀ (n : ℕ) (Y : Scheme.{u}) (g : Y ⟶ S), P n Y g →
    ∃ E : SquareZeroExtension g, ∃ r : Realization E, P (n + 1) r.ambient r.toBase)

include hstep

/-- The realization chosen by `hstep` above a stage. -/
private def chosenRealization (n : ℕ) (T : Stage P n) :
    Realization (hstep n T.obj T.toBase T.property).choose :=
  (hstep n T.obj T.toBase T.property).choose_spec.choose

/-- The stage above a given one, namely the scheme realizing the chosen extension. -/
private def nextStage (n : ℕ) (T : Stage P n) : Stage P (n + 1) :=
  ⟨(chosenRealization P hstep n T).ambient, (chosenRealization P hstep n T).toBase,
    (hstep n T.obj T.toBase T.property).choose_spec.choose_spec⟩

/-- The step joining a stage to the one above it. -/
private def nextStep (n : ℕ) (T : Stage P n) :
    SquareZeroStep T.toBase (nextStage P hstep n T).toBase :=
  SquareZeroStep.ofRealization (chosenRealization P hstep n T)

/-- The sequence of stages above a given bottom stage. -/
private def stageSeq (T₀ : Stage P 0) : (n : ℕ) → Stage P n
  | 0 => T₀
  | n + 1 => nextStage P hstep n (stageSeq T₀ n)

/-- **The tower exists.** Let `P` be an invariant of schemes over `S` graded by `ℕ`, holding at
level `0` of a given `Y₀ ⟶ S`, and propagating across one application of [Stacks, Tag 05YV]: for
every stage satisfying `P` at level `n` there is a square-zero extension of its structure sheaf,
with quasi-coherent kernel, whose realization satisfies `P` at level `n + 1`.  Then there is an
`ℕ`-indexed sequence of schemes over `S`, consecutive stages joined by a
`Stacks.Thickenings.SquareZeroStep`, which starts at `Y₀` and satisfies `P` at every stage.

The invariant is what an argument iterating the tag carries up the tower; for [Stacks, Tag 0E3X]
it is the identification of the structure sheaf of the stage `n` with `f_*(𝒪_U/𝔪ⁿ⁺¹𝒪_U)`.

Forgetting the base, `⟨obj, fun n => (step n).immersion, fun n => (step n).isFirstOrder⟩` is a
`Stacks.PuncturedSpectrumPicard.ThickeningTower`; see the implementation notes. -/
theorem exists_squareZeroTower {Y₀ : Scheme.{u}} {g₀ : Y₀ ⟶ S} (h₀ : P 0 Y₀ g₀) :
    ∃ (obj : ℕ → Scheme.{u}) (toBase : ∀ n, obj n ⟶ S)
      (_step : ∀ n, SquareZeroStep (toBase n) (toBase (n + 1))),
      obj 0 = Y₀ ∧ HEq (toBase 0) g₀ ∧ ∀ n, P n (obj n) (toBase n) :=
  let T := stageSeq P hstep ⟨Y₀, g₀, h₀⟩
  ⟨fun n => (T n).obj, fun n => (T n).toBase, fun n => nextStep P hstep n (T n),
    rfl, HEq.rfl, fun n => (T n).property⟩

end Construction

/-- **The top of a finite tower of square-zero extensions.** This is the form an argument whose
kernel is nilpotent of order `N` consumes: given an invariant `P` holding at level `0` of
`g₀ : Y₀ ⟶ S` and propagating across one application of [Stacks, Tag 05YV] at each of the levels
below `N`, there is a single scheme `V` over `S` satisfying `P` at level `N`, together with a
thickening `Y₀ ⟶ V` over `S`.

`N` applications of the tag are made, one per step of the filtration whose successive quotients
are square-zero; the hypothesis is required only below `N` because the filtration has reached
zero there, which is what makes the iteration finite.  The conclusion is a thickening rather than
a first-order thickening: a composite of `N` first-order thickenings is not first-order, but it
is still a closed immersion surjective on points, and that is what identifies the underlying
topological space of `V` with that of `Y₀` — the identification [Stacks, Tag 0E3X] makes when it
says that the thickening `X → U` "can be used to identify the underlying topological spaces". -/
theorem exists_thickening_of_iterate {S : Scheme.{u}} (N : ℕ)
    (P : ℕ → (Y : Scheme.{u}) → (Y ⟶ S) → Prop) {Y₀ : Scheme.{u}} {g₀ : Y₀ ⟶ S}
    (h₀ : P 0 Y₀ g₀)
    (hstep : ∀ (n : ℕ) (Y : Scheme.{u}) (g : Y ⟶ S), n < N → P n Y g →
      ∃ E : SquareZeroExtension g, ∃ r : Realization E, P (n + 1) r.ambient r.toBase) :
    ∃ (V : Scheme.{u}) (g : V ⟶ S) (i : Y₀ ⟶ V),
      P N V g ∧ IsThickening i ∧ i ≫ g = g₀ := by
  suffices h : ∀ k ≤ N, ∃ (V : Scheme.{u}) (g : V ⟶ S) (i : Y₀ ⟶ V),
      P k V g ∧ IsThickening i ∧ i ≫ g = g₀ from h N le_rfl
  intro k
  induction k with
  | zero =>
    exact fun _ => ⟨Y₀, g₀, 𝟙 _, h₀, isThickening_of_isIso (𝟙 Y₀), Category.id_comp _⟩
  | succ k ih =>
    intro hk
    obtain ⟨V, g, i, hP, hi, hig⟩ := ih (by omega)
    obtain ⟨E, r, hP'⟩ := hstep k V g (by omega) hP
    exact ⟨r.ambient, r.toBase, i ≫ r.immersion, hP',
      isThickening_comp hi r.immersion_isFirstOrder.isThickening,
      by rw [Category.assoc, r.over_base, hig]⟩

end Stacks.Thickenings

end
