module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push

/-!
# The level induction of Epp's theorem in mixed characteristic

`StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel` proves the two mixed-characteristic
layers of Epp's theorem (Stacks Tag 09F9):

* `exists_totallyRamified_galoisExtension_isWeakSolution_or_finiteLevel` — from a
  degree-`p` Galois extension to one of *finite level*, and
* `exists_totallyRamified_isWeakSolution_or_extensionLevel_le` — from level `l > 0` to
  level at most `max 0 (max (l - 1) (2 * l - p))`.

Neither is an endgame: each returns a finite totally ramified base extension which is *either* a
weak solution *or* a situation of smaller level. Getting a weak solution out of them means
iterating the second until the level reaches `0`. This file proves that this iteration terminates
and runs the resulting induction over an abstract state type.

It deliberately imports no discrete-valuation-ring machinery: the descent measure is a statement
about the rational recursion alone, and keeping it separate is what makes it reusable by any layer
whose measure obeys that recursion.

## The recursion terminates

`Stacks.DiscreteValuationRing.EppLevelInduction.levelStep p l = max 0 (max (l - 1) (2 * l - p))` is
the bound Tag 09F5 achieves. It is monotone, fixes `0`, and is strictly decreasing on `(0, p)`
(`levelStep_lt_self`) — but `ℚ` is not well-founded under `<`, so strict decrease alone terminates
nothing. What does is
`exists_iterate_levelStep_eq_zero`: iterated from any `l ∈ [0, p)`, `levelStep p` reaches `0` after
finitely many steps. The argument has two phases, and both are needed, because the reading "the
level drops by one each time" is false near the top of the range:

* on `(p - 1, p)` the active branch is `2 * l - p`, and `p - levelStep p l = 2 * (p - l)`: the
  distance to `p` *doubles*. So the level does decrease, but it can decrease by arbitrarily little,
  and what terminates this phase is that after finitely many doublings the distance exceeds `1` and
  the level has left the region (`exists_iterate_le_sub_one`);
* on `[0, p - 1]` the active branch is `l - 1`, and any number of steps at least `l` reaches `0`
  (`iterate_levelStep_eq_zero_of_le`).

The bound `l < p` is not decoration.
`Stacks.DegreePExtensionLevel.exists_extensionLevel_isLeast_and_mem_Ico` proves the level always
lies in `[0, p)`, and at `l = p` the recursion has a fixed point, so the theorem is false without
it.

`levelStep_zero` — reaching `0` is absorbing — is what lets the two phases be composed, and what
lets a *bound* on the successor's level be used where the induction wants its value
(`iterate_levelStep_eq_zero_of_le_levelStep`). That last point is why Tag 09F5's conclusion, an
inequality, is usable at all.

## The induction step

`Stacks.DiscreteValuationRing.EppLevelInduction.isSolved_of_levelStep` runs the induction over an
abstract state type. Its one non-formal hypothesis, `hstep`, is:

> from a state of positive level, either that state is already solved, or there is a successor
> state whose level is at most `levelStep p (level s)` **and whose being solved solves the
> predecessor**.

Tag 09F5 supplies the successor and its level bound. Its conclusion hands over
`B₁ = integralClosure B (L ⊗[K] K₁)`, the base-changed fields `L₁`, `M₁`, the cyclotomic data
`f₁`, `P₁`, and the level bound; it does not hand over the new base ring
`A₁ = integralClosure A K₁` with `IsDiscreteValuationRing.IsWeaklyUnramified A₁ B₁` (hypothesis (2)
of Tag 09F5), the new top ring `C₁`, the residue condition at `(A₁, B₁)` (hypothesis (5)), or the
implication that a weak solution upstairs gives one downstairs.

Tag 09F5's own proof calls Tag 09ER
(`IsDiscreteValuationRing.isField_tensorProduct_and_isDVR_baseChange_of_totallyRamified`) at three
places, and that theorem's conclusion carries `A₁` a discrete valuation ring, `B₁` a discrete
valuation ring, `Ideal.map _ (𝔪 A₁) = 𝔪 B₁` — which *is* weak unramifiedness — `C₁` with
`IsFractionRing C₁ L₁`, and `B₁ ≃ₐ[B] C₁`.

Nor does the ascent failure recorded for the equal-characteristic branch apply to the residue
condition here: the extension Tag 09F5 returns is *totally ramified* with respect to `A`, and
`IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo` includes triviality of the residue field
extension, so residue fields do not grow. `exists_residueField_algEquiv_of_totallyRamified` gives
`κ_{A₁} ≅ κ_A`. Transporting the residue condition also needs the upstairs half `κ_{B₁} ≅ κ_B`
together with compatibility of the two isomorphisms with `κ_A → κ_B` — it is the equality
`κ_A = ⋂ₙ κ_B^{pⁿ}`, a statement about that map's range, that has to transport — and the
implication back down is the composition half of Tag 09ES
(`IsDiscreteValuationRing.weakSolutions_and_solutions_go_down_and_compose`).

## One shared extension for the whole conjugate family

`Stacks.DiscreteValuationRing.EppLevelInduction.forall_isSolved_of_shared_levelStep` is the same
induction run over a finite family of states at once, with a **single** step lowering every
member's level simultaneously. Its measure is the maximum of the members' levels, and
`levelStep_monotone` is what makes that maximum obey the same recursion: each member's new level
is at most `levelStep p` of its own old level, hence at most `levelStep p` of the maximum.

This is the shape the all-factor route to Tag 09F9 requires. The conjugate factors of
`(L ⊗[K] K₁) ⧸ nilradical` are pairwise distinct
(`Stacks.WeakSolution.Obstruction.conjugateFactor_injective`), and the one-factor inference of
the published proof of Tag 09ET is refuted, so
there is no canonical transport of a weak solution from one factor to the others compatible with
the base: the factors are permuted by the Galois action, but no identification available here
carries the weak-solution property along. One extension fixed before any factor is examined,
serving all of them, is therefore the only shape left. Compare
`Stacks.EppTheorem.FactorSolutions` in
`StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync`, whose per-factor obligation
this is the termination argument for.

The family version is *not* a strengthening of the single-state version — it is deduced from it, by
taking the state to be the whole family and the level to be the maximum. Its value is that the
shared step is visible in the statement, so a caller cannot discharge it by choosing an extension
per factor.

## Main definitions

* `Stacks.DiscreteValuationRing.EppLevelInduction.levelStep`: the level bound of Tag 09F5, as a
  function `ℚ → ℚ`.

## Main results

* `Stacks.DiscreteValuationRing.EppLevelInduction.levelStep_lt_self`: the level strictly drops on
  `(0, p)`.
* `Stacks.DiscreteValuationRing.EppLevelInduction.exists_iterate_levelStep_eq_zero`: iterating
  `levelStep p` from any `l ∈ [0, p)` reaches `0`.
* `Stacks.DiscreteValuationRing.EppLevelInduction.isSolved_of_levelStep`: the level induction, over
  an abstract state type.
* `Stacks.DiscreteValuationRing.EppLevelInduction.forall_isSolved_of_shared_levelStep`: the same
  induction with one step shared by a finite family of states.

## References

* [The Stacks Project, Tag 09F4](https://stacks.math.columbia.edu/tag/09F4)
* [The Stacks Project, Tag 09F5](https://stacks.math.columbia.edu/tag/09F5)
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

namespace Stacks.DiscreteValuationRing.EppLevelInduction

/-! ### The level recursion -/

/-- **The level bound of Tag 09F5.**

`exists_totallyRamified_isWeakSolution_or_extensionLevel_le` lowers a positive level `l`
to at most `max 0 (max (l - 1) (2 * l - p))`, and this is that bound as a function of `l`.
Iterating it from any level in `[0, p)` reaches `0` (`exists_iterate_levelStep_eq_zero`), which is
what terminates the mixed-characteristic branch of Epp's theorem. -/
def levelStep (p : ℕ) (l : ℚ) : ℚ := max 0 (max (l - 1) (2 * l - p))

/-- The defining formula of `levelStep`. -/
theorem levelStep_def (p : ℕ) (l : ℚ) : levelStep p l = max 0 (max (l - 1) (2 * l - p)) := rfl

/-- `levelStep p l` is nonnegative. -/
theorem levelStep_nonneg (p : ℕ) (l : ℚ) : 0 ≤ levelStep p l := by
  rw [levelStep_def]; exact le_max_left _ _

/-- `levelStep p l` is at least `l - 1`. -/
theorem sub_one_le_levelStep (p : ℕ) (l : ℚ) : l - 1 ≤ levelStep p l := by
  rw [levelStep_def]; exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- `levelStep p l` is at least `2 * l - p`. -/
theorem two_mul_sub_le_levelStep (p : ℕ) (l : ℚ) : 2 * l - p ≤ levelStep p l := by
  rw [levelStep_def]; exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- `levelStep` is monotone, being a maximum of monotone functions. This is what lets a *bound* on
the level of a successor state stand in for its value, and what makes the maximum over a finite
family obey the same recursion. -/
theorem levelStep_monotone (p : ℕ) : Monotone (levelStep p) := by
  intro a b hab
  rw [levelStep_def, levelStep_def]
  exact max_le_max le_rfl (max_le_max (by linarith) (by linarith))

/-- Level `0` is absorbing. With monotonicity this is what makes "the iteration has reached `0`" a
stable condition, so the two phases of `exists_iterate_levelStep_eq_zero` compose, and what makes
an inequality `level t ≤ levelStep p (level s)` as good as an equality. -/
theorem levelStep_zero (p : ℕ) : levelStep p 0 = 0 := by
  have hp : (0 : ℚ) ≤ (p : ℚ) := by exact_mod_cast Nat.zero_le p
  refine le_antisymm ?_ (levelStep_nonneg p 0)
  rw [levelStep_def]
  exact max_le le_rfl (max_le (by norm_num) (by linarith))

/-- **The level strictly drops.** Each branch of `levelStep p l` is below `l`: `0 < l` by
hypothesis, `l - 1 < l` always, and `2 * l - p < l` exactly because `l < p`.

On its own this does not terminate an induction — `ℚ` is not well-founded under `<`, and on
`(p - 1, p)` the drop can be arbitrarily small. `exists_iterate_levelStep_eq_zero` is the
statement that does. -/
theorem levelStep_lt_self {p : ℕ} {l : ℚ} (hl : 0 < l) (hlp : l < p) : levelStep p l < l := by
  rw [levelStep_def]
  exact max_lt hl (max_lt (by linarith) (by linarith))

/-- The level stays in the range `[0, p)` that
`Stacks.DegreePExtensionLevel.exists_extensionLevel_isLeast_and_mem_Ico` puts it in, so the
iteration never leaves the region where `levelStep_lt_self` applies. -/
theorem levelStep_lt {p : ℕ} {l : ℚ} (hp : 0 < p) (hlp : l < p) : levelStep p l < p := by
  have hp' : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  rw [levelStep_def]
  exact max_lt hp' (max_lt (by linarith) (by linarith))

/-! ### Termination -/

private theorem exists_one_le_two_pow_mul {d : ℚ} (hd : 0 < d) : ∃ k : ℕ, 1 ≤ 2 ^ k * d := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / d) (one_lt_two (α := ℚ))
  exact ⟨k, by rw [div_lt_iff₀ hd] at hk; exact hk.le⟩

/-- Above `p - 1` the active branch of the recursion is `2 * l - p`. This is the only property of
that region the first phase of the termination argument uses; the upper bound `l < p` is not needed
for it, only for the doubling to make progress. -/
private theorem levelStep_eq_two_mul_sub {p : ℕ} {l : ℚ} (hp : 2 ≤ p) (hl : (p : ℚ) - 1 < l) :
    levelStep p l = 2 * l - p := by
  have hp' : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have h1 : l - 1 ≤ 2 * l - p := by linarith
  have h2 : (0 : ℚ) ≤ 2 * l - p := by linarith
  rw [levelStep_def, max_eq_right h1, max_eq_right h2]

/-- **Phase one of termination.** After finitely many steps the level is at most `p - 1`, i.e. it
has left the region where the `2 * l - p` branch is active.

The induction is on a natural number `k` with `1 ≤ 2 ^ k * (p - l)`, which
`exists_one_le_two_pow_mul` supplies because `l < p`: in the region the distance to `p` doubles at
every step, so `k` steps suffice. -/
theorem exists_iterate_le_sub_one {p : ℕ} (hp : 2 ≤ p) {l : ℚ} (hl : 0 ≤ l) (hlp : l < p) :
    ∃ j : ℕ, (levelStep p)^[j] l ≤ (p : ℚ) - 1 := by
  have hp' : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have key : ∀ (k : ℕ) (l : ℚ), 0 ≤ l → l < p → 1 ≤ 2 ^ k * ((p : ℚ) - l) →
      ∃ j : ℕ, (levelStep p)^[j] l ≤ (p : ℚ) - 1 := by
    intro k
    induction k with
    | zero =>
      intro l _ _ hk
      rw [pow_zero, one_mul] at hk
      exact ⟨0, by rw [Function.iterate_zero_apply]; linarith⟩
    | succ n ih =>
      intro l hl hlp hk
      rcases le_or_gt l ((p : ℚ) - 1) with hle | hgt
      · exact ⟨0, by rw [Function.iterate_zero_apply]; exact hle⟩
      · have hstep : levelStep p l = 2 * l - p := levelStep_eq_two_mul_sub hp hgt
        have hnn : (0 : ℚ) ≤ 2 * l - p := by linarith
        have hlt : 2 * l - p < p := by linarith
        have hnext : 1 ≤ 2 ^ n * ((p : ℚ) - (2 * l - p)) := by
          have heq : (2 : ℚ) ^ n * ((p : ℚ) - (2 * l - p)) = 2 ^ (n + 1) * ((p : ℚ) - l) := by
            rw [pow_succ]; ring
          rw [heq]; exact hk
        obtain ⟨j, hj⟩ := ih (2 * l - p) hnn hlt hnext
        refine ⟨j + 1, ?_⟩
        rw [Function.iterate_succ_apply, hstep]
        exact hj
  obtain ⟨k, hk⟩ := exists_one_le_two_pow_mul (d := (p : ℚ) - l) (by linarith)
  exact key k l hl hlp hk

/-- **Phase two of termination.** Below `p - 1` the active branch is `l - 1`, so the recursion is
`l ↦ max 0 (l - 1)` and any number of steps at least `l` reaches `0`. -/
theorem iterate_levelStep_eq_zero_of_le {p : ℕ} (hp : 2 ≤ p) :
    ∀ (n : ℕ) (l : ℚ), 0 ≤ l → l ≤ (p : ℚ) - 1 → l ≤ n → (levelStep p)^[n] l = 0 := by
  have hp' : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  intro n
  induction n with
  | zero =>
    intro l hl _ hln
    have hln' : l ≤ 0 := by exact_mod_cast hln
    rw [Function.iterate_zero_apply]
    exact le_antisymm hln' hl
  | succ m ih =>
    intro l hl hlp hln
    have hstep : levelStep p l = max 0 (l - 1) := by
      rw [levelStep_def, max_eq_left (by linarith : 2 * l - p ≤ l - 1)]
    have hnn : (0 : ℚ) ≤ max 0 (l - 1) := le_max_left _ _
    have hle : max 0 (l - 1) ≤ (p : ℚ) - 1 := max_le (by linarith) (by linarith)
    have hlem : max 0 (l - 1) ≤ (m : ℚ) := by
      have hm : (0 : ℚ) ≤ (m : ℚ) := by exact_mod_cast Nat.zero_le m
      have hln' : l ≤ (m : ℚ) + 1 := by push_cast at hln; linarith
      exact max_le hm (by linarith)
    rw [Function.iterate_succ_apply, hstep]
    exact ih _ hnn hle hlem

/-- Every iterate of `levelStep p` at a nonnegative `l` is nonnegative. -/
theorem iterate_levelStep_nonneg (p : ℕ) {l : ℚ} (hl : 0 ≤ l) (N : ℕ) :
    0 ≤ (levelStep p)^[N] l := by
  induction N with
  | zero => rw [Function.iterate_zero_apply]; exact hl
  | succ n _ =>
    rw [Function.iterate_succ_apply']
    exact levelStep_nonneg p _

/-- **The level recursion terminates.** Iterated from any `l` in the range `[0, p)` that
`Stacks.DegreePExtensionLevel.exists_extensionLevel_isLeast_and_mem_Ico` guarantees, `levelStep p`
reaches `0` after finitely many steps.

This is what stands in for "the level strictly decreases" — true, by `levelStep_lt_self`, but
useless on its own since `ℚ` is not well-founded under `<`. -/
theorem exists_iterate_levelStep_eq_zero {p : ℕ} (hp : 2 ≤ p) {l : ℚ} (hl : 0 ≤ l) (hlp : l < p) :
    ∃ N : ℕ, (levelStep p)^[N] l = 0 := by
  obtain ⟨j, hj⟩ := exists_iterate_le_sub_one hp hl hlp
  obtain ⟨n, hn⟩ := exists_nat_ge ((levelStep p)^[j] l)
  refine ⟨n + j, ?_⟩
  rw [Function.iterate_add_apply]
  exact iterate_levelStep_eq_zero_of_le hp n _ (iterate_levelStep_nonneg p hl j) hj hn

/-- Every iterate of `levelStep p` is monotone. -/
theorem monotone_iterate_levelStep (p : ℕ) (N : ℕ) : Monotone ((levelStep p)^[N]) := by
  induction N with
  | zero => rw [Function.iterate_zero]; exact monotone_id
  | succ n ih =>
    rw [Function.iterate_succ]
    exact ih.comp (levelStep_monotone p)

/-- A *bound* on the successor's level is as good as its value: if `N` steps take
`levelStep p l` to `0`, then `N` steps take anything nonnegative and below `levelStep p l` to `0`
as well.

This is the lemma that lets Tag 09F5's conclusion — an inequality
`≤ max 0 (max (l - 1) (2 * l - p))`, not an equality — drive the induction. -/
theorem iterate_levelStep_eq_zero_of_le_levelStep {p : ℕ} {l l' : ℚ} {N : ℕ} (hl' : 0 ≤ l')
    (hle : l' ≤ levelStep p l) (hN : (levelStep p)^[N] (levelStep p l) = 0) :
    (levelStep p)^[N] l' = 0 :=
  le_antisymm (le_of_le_of_eq (monotone_iterate_levelStep p N hle) hN)
    (iterate_levelStep_nonneg p hl' N)

/-! ### The induction -/

/-- **The level induction of the mixed-characteristic branch, over an abstract state type.**

`State` is the type of situations Tag 09F5 consumes — a tower `A ⊆ B ⊆ C` of discrete valuation
rings in mixed characteristic, with all of its structure — `level` the level of the top layer, and
`IsSolved` the existence of a weak solution. The conclusion is that every state is solved.

The hypotheses are exactly what the iteration needs:

* `hnonneg`, `hlt`: the level lies in `[0, p)`, which is
  `Stacks.DegreePExtensionLevel.exists_extensionLevel_isLeast_and_mem_Ico`;
* `hzero`: level `0` is solved. In the intended instance the extension is then generated by a root
  of `P(z) = ξ` with `ξ` integral, so case (A) of Tag 09F3 makes it unramified, hence weakly
  unramified;
* `hstep`: from positive level, either the state is already solved, or there is a successor of
  level at most `levelStep p (level s)` whose being solved solves `s`.

In the intended instance Tag 09F5 produces the successor `B₁ = integralClosure B (L ⊗[K] K₁)` with
the level bound. The new base ring `A₁` with `IsWeaklyUnramified A₁ B₁` and the new top ring `C₁`
come from Tag 09ER, which its proof calls; the residue condition at `(A₁, B₁)` is not obstructed by
the ascent failure of the equal-characteristic branch, because the extension is totally ramified
and so does not grow residue fields; and the implication back down is the composition half of
Tag 09ES.

Nothing here is specific to mixed characteristic beyond the shape of `levelStep`, so the same
induction serves any layer whose measure obeys that recursion. -/
theorem isSolved_of_levelStep {State : Type*} {p : ℕ} (hp : 2 ≤ p)
    (level : State → ℚ) (IsSolved : State → Prop)
    (hnonneg : ∀ s, 0 ≤ level s) (hlt : ∀ s, level s < p)
    (hzero : ∀ s, level s = 0 → IsSolved s)
    (hstep : ∀ s, 0 < level s → IsSolved s ∨
      ∃ t, level t ≤ levelStep p (level s) ∧ (IsSolved t → IsSolved s))
    (s : State) : IsSolved s := by
  have key : ∀ (N : ℕ) (s : State), (levelStep p)^[N] (level s) = 0 → IsSolved s := by
    intro N
    induction N with
    | zero =>
      intro s hs
      rw [Function.iterate_zero_apply] at hs
      exact hzero s hs
    | succ n ih =>
      intro s hs
      rcases eq_or_lt_of_le (hnonneg s) with hzeros | hpos
      · exact hzero s hzeros.symm
      · rcases hstep s hpos with hsolved | ⟨t, hlevel, himp⟩
        · exact hsolved
        · rw [Function.iterate_succ_apply] at hs
          exact himp (ih t (iterate_levelStep_eq_zero_of_le_levelStep (hnonneg t) hlevel hs))
  obtain ⟨N, hN⟩ := exists_iterate_levelStep_eq_zero hp (hnonneg s) (hlt s)
  exact key N s hN

/-- **The same induction with one step shared by a finite family of states.**

`hstep` here produces a *single* successor family from a whole family, lowering every member's
level at once — no member is singled out, and a caller cannot discharge it by choosing an extension
per member.

That is the shape the all-factor route to Tag 09F9 needs. The conjugate factors of
`(L ⊗[K] K₁) ⧸ nilradical` are pairwise distinct
(`Stacks.WeakSolution.Obstruction.conjugateFactor_injective`) and the one-factor inference of the
published proof of Tag 09ET is refuted, so there is no canonical transport of a weak solution from
one factor to the others compatible with the base; one extension fixed before any factor is
examined is the only shape left. Compare `Stacks.EppTheorem.FactorSolutions` in
`StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync`.

The measure is the maximum of the members' levels, and `levelStep_monotone` is what makes that
maximum obey the same recursion.

This is a corollary of `isSolved_of_levelStep`, not a strengthening of it — the state is the whole
family. Its content is that the shared step is visible in the statement. -/
theorem forall_isSolved_of_shared_levelStep {ι : Type*} [Finite ι]
    {State : Type*} {p : ℕ} (hp : 2 ≤ p)
    (level : ι → State → ℚ) (IsSolved : ι → State → Prop)
    (hnonneg : ∀ i s, 0 ≤ level i s) (hlt : ∀ i s, level i s < p)
    (hzero : ∀ s, (∀ i, level i s = 0) → ∀ i, IsSolved i s)
    (hstep : ∀ s, (∃ i, 0 < level i s) → (∀ i, IsSolved i s) ∨
      ∃ t, (∀ i, level i t ≤ levelStep p (level i s)) ∧
        ((∀ i, IsSolved i t) → ∀ i, IsSolved i s))
    (s : State) (i : ι) : IsSolved i s := by
  classical
  have : Nonempty ι := ⟨i⟩
  have : Fintype ι := Fintype.ofFinite ι
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  have hle_fam : ∀ (j : ι) (u : State), level j u ≤ Finset.univ.sup' hne (fun k => level k u) :=
    fun j u => Finset.le_sup' (fun k => level k u) (Finset.mem_univ j)
  have hattained : ∀ u : State, ∃ j : ι, Finset.univ.sup' hne (fun k => level k u) = level j u := by
    intro u
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' hne (fun k => level k u)
    exact ⟨j, hj⟩
  have h1 : ∀ u : State, 0 ≤ Finset.univ.sup' hne (fun k => level k u) :=
    fun u => le_trans (hnonneg (Classical.arbitrary ι) u) (hle_fam _ u)
  have h2 : ∀ u : State, Finset.univ.sup' hne (fun k => level k u) < (p : ℚ) := by
    intro u
    obtain ⟨j, hj⟩ := hattained u
    rw [hj]
    exact hlt j u
  have h3 : ∀ u : State, Finset.univ.sup' hne (fun k => level k u) = 0 → ∀ j, IsSolved j u := by
    intro u hu
    exact hzero u fun j => le_antisymm (le_trans (hle_fam j u) hu.le) (hnonneg j u)
  have h4 : ∀ u : State, 0 < Finset.univ.sup' hne (fun k => level k u) →
      (∀ j, IsSolved j u) ∨ ∃ t : State,
        Finset.univ.sup' hne (fun k => level k t) ≤
            levelStep p (Finset.univ.sup' hne (fun k => level k u)) ∧
          ((∀ j, IsSolved j t) → ∀ j, IsSolved j u) := by
    intro u hu
    obtain ⟨j, hj⟩ := hattained u
    rw [hj] at hu
    rcases hstep u ⟨j, hu⟩ with hsolved | ⟨t, hlevel, himp⟩
    · exact Or.inl hsolved
    · refine Or.inr ⟨t, Finset.sup'_le hne _ fun k _ => ?_, himp⟩
      exact le_trans (hlevel k) (levelStep_monotone p (hle_fam k u))
  exact isSolved_of_levelStep hp (fun u => Finset.univ.sup' hne (fun k => level k u))
    (fun u => ∀ j, IsSolved j u) h1 h2 h3 h4 s i

end Stacks.DiscreteValuationRing.EppLevelInduction

end
