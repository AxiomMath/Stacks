module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ChosenDifferential
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeTower
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.LowDegree

/-!
# The boundary of a degree-by-degree recursion

`DividedPowers.TateResolution.towerIndices` recurses on the *index families* of a Tate
resolution built one degree at a time. This file recurses on the prescribed *boundary* alongside
it: a rule assigning to a family of variables, a boundary for it, and a degree `k` a boundary
for each new variable of degree `k + 1` determines a boundary on the family after every number
of rungs, and hence one on the limiting family.

The rule has to see the boundary on the family it extends, not only the family: the new
variables of degree `k + 1` are to kill cycles of the algebra built so far, and which elements
are cycles depends on the differential, which depends on the boundary. The boundaries after `k`
rungs are therefore carried together with the proof that they are homogeneous — the differential
is `IndexedPresentation.chosenDifferential`, which asks for that proof — so the recursion runs
into a subtype, `BdryAt`.

Each rung pushes the boundaries built so far forward along the one-step comparison
`oneStepComparison`, and the limiting boundary pushes the boundary at rung `n + 1` forward along
`towerComparison`. The resulting family is *compatible* with every rung
(`limitBoundary_towerEmbed`), which is exactly the hypothesis
`IndexedPresentation.comparison_differential` asks for, so each rung's comparison is a map of
complexes. Compatibility is a cocycle condition on the *chosen* comparisons and so rests on
`IndexedPresentation.comparison_comp`.

## Main definitions

* `DividedPowers.TateResolution.towerIndicesStep` — the one-rung inclusion of index families, with
  retraction `towerIndicesStepRetract`.
* `DividedPowers.TateResolution.oneStepComparison` — the algebra map it induces.
* `DividedPowers.TateResolution.towerBoundary` — the boundary after `k` rungs.
* `DividedPowers.TateResolution.limitBoundary` — the boundary on the limiting family.

## Main results

* `DividedPowers.TateResolution.towerComparison_oneStepComparison` — the comparisons of the
  tower form a directed system over the one-rung comparisons.
* `DividedPowers.TateResolution.limitBoundary_towerEmbed` — the limiting boundary restricts on
  the family after `k` rungs to the boundary after `k` rungs, pushed forward.
* `DividedPowers.TateResolution.exists_cycle_towerComparison` — a cycle of degree `m` of the
  algebra on the limiting family is the image of a cycle of degree `m` of the algebra after `k`
  rungs, for every `m ≤ k`. This is what lets the rung that adjoins the variables of degree
  `m + 1` see every cycle of degree `m` of the final algebra.

## Implementation notes

An index of the family after `k + 1` rungs is an index of the family after `k` rungs, or a new
index of degree `k + 1`, and the two cases are separated by a decidable equality of degrees
rather than by a pattern match: `towerIndices` records a rung by `Function.update`, so the
agreement of consecutive families away from the rung is an equality of types and an index is
carried along it by `cast`. Casts are compared by `HEq` throughout rather than rewritten.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe t u v w

/-- Two casts of one element into one type agree, since each is heterogeneously equal to the
element. -/
private theorem cast_eq_of_heq_aux {α β : Type t} (h : α = β) {a : α} {b : β} (hab : HEq a b) :
    cast h a = b :=
  eq_of_heq ((cast_heq h a).trans hab)

variable {newIdx : (ℕ → Type t) → ℕ → Type t}

/-- The inclusion of the index family after `k` rungs into the family after `k + 1` rungs: in
degree `k` there is nothing to include, and in every other degree the two families agree. -/
public def towerIndicesStep (newIdx : (ℕ → Type t) → ℕ → Type t) (k n : ℕ) :
    towerIndices newIdx k n → towerIndices newIdx (k + 1) n :=
  fun x =>
    if h : n = k then (isEmpty_towerIndices (le_of_eq h.symm)).elim x
    else cast (towerIndices_succ_of_ne h).symm x

/-- The retraction of the index family after `k + 1` rungs onto the family after `k` rungs: the
indices adjoined at the rung, those of degree `k`, are not in the image. -/
public def towerIndicesStepRetract (newIdx : (ℕ → Type t) → ℕ → Type t) (k n : ℕ) :
    towerIndices newIdx (k + 1) n → Option (towerIndices newIdx k n) :=
  fun y => if h : n = k then none else some (cast (towerIndices_succ_of_ne h) y)

/-- Away from the rung, the one-rung inclusion is a cast, so it changes nothing. -/
public theorem towerIndicesStep_heq {k n : ℕ} (h : n ≠ k) (x : towerIndices newIdx k n) :
    HEq (towerIndicesStep newIdx k n x) x := by
  rw [towerIndicesStep, dite_eq_right h]
  exact cast_heq _ x

/-- Away from the rung, the one-rung inclusion is undone by the cast that identifies the two
families. -/
public theorem cast_towerIndicesStep {k n : ℕ} (h : n ≠ k) (x : towerIndices newIdx k n) :
    cast (towerIndices_succ_of_ne h) (towerIndicesStep newIdx k n x) = x :=
  cast_eq_of_heq_aux _ (towerIndicesStep_heq h x)

public theorem towerIndicesStepRetract_towerIndicesStep (k n : ℕ) (x : towerIndices newIdx k n) :
    towerIndicesStepRetract newIdx k n (towerIndicesStep newIdx k n x) = some x := by
  by_cases h : n = k
  · exact (isEmpty_towerIndices (le_of_eq h.symm)).elim x
  · rw [towerIndicesStepRetract, dite_eq_right h]
    exact congrArg some (cast_eq_of_heq_aux _ (towerIndicesStep_heq h x))

/-- The one-rung inclusions are compatible with the inclusions into the limiting family. -/
public theorem towerEmbed_towerIndicesStep (k n : ℕ) (x : towerIndices newIdx k n) :
    towerEmbed newIdx (k + 1) n (towerIndicesStep newIdx k n x) = towerEmbed newIdx k n x := by
  by_cases h : n < k
  · rw [towerEmbed, dite_eq_left (by omega : n < k + 1), towerEmbed, dite_eq_left h]
    exact cast_eq_of_heq_aux _ ((towerIndicesStep_heq (by omega : n ≠ k) x).trans
      (cast_heq (towerIndices_eq_towerLimit h) x).symm)
  · exact (isEmpty_towerIndices (Nat.not_lt.mp h)).elim x

/-- Below rung `k` the inclusion into the limiting family is surjective: it is a cast. -/
public theorem towerEmbed_surjective {k n : ℕ} (hn : n < k) (y : towerLimit newIdx n) :
    ∃ x : towerIndices newIdx k n, towerEmbed newIdx k n x = y := by
  refine ⟨cast (towerIndices_eq_towerLimit hn).symm y, ?_⟩
  rw [towerEmbed, dite_eq_left hn]
  exact cast_eq_of_heq_aux _ (cast_heq (towerIndices_eq_towerLimit hn).symm y)

section Comparison

variable (R : Type u) (P : Type v) [CommRing R] [CommRing P] [Algebra R P]

/-- The comparison from the algebra after `k` rungs to the algebra after `k + 1` rungs, induced
by the one-rung inclusion of index families. -/
public noncomputable def oneStepComparison
    (newIdx : (ℕ → Type (max u v w)) → ℕ → Type (max u v w)) (k : ℕ) :
    (chosenPresentation.{u, v, w} R P (towerIndices newIdx k)).A →ₐ[R]
      (chosenPresentation.{u, v, w} R P (towerIndices newIdx (k + 1))).A :=
  (chosenPresentation.{u, v, w} R P (towerIndices newIdx k)).comparison
    (chosenPresentation.{u, v, w} R P (towerIndices newIdx (k + 1))) (towerIndicesStep newIdx k)

/-- **The comparisons of the tower form a directed system.** Comparing the algebra after `k`
rungs with the algebra on the limiting family directly is the same as comparing it with the
algebra after `k + 1` rungs first. This is a cocycle condition on *chosen* comparisons, so it
rests on `IndexedPresentation.comparison_comp`. -/
public theorem towerComparison_oneStepComparison
    (newIdx : (ℕ → Type (max u v w)) → ℕ → Type (max u v w)) (k : ℕ) :
    (towerComparison.{u, v, w} R P newIdx (k + 1)).comp
        (oneStepComparison.{u, v, w} R P newIdx k) =
      towerComparison.{u, v, w} R P newIdx k := by
  have he : (fun (n : ℕ) (x : towerIndices newIdx k n) =>
      towerEmbed newIdx (k + 1) n (towerIndicesStep newIdx k n x)) = towerEmbed newIdx k := by
    funext n x
    exact towerEmbed_towerIndicesStep k n x
  rw [oneStepComparison, towerComparison, towerComparison,
    IndexedPresentation.comparison_comp, he]

end Comparison

section Boundary

/-- A homogeneous element of one degree is homogeneous of any degree equal to it. -/
private theorem mem_grade_of_degree_eq {R : Type u} {P : Type v} [CommRing R] [CommRing P]
    [Algebra R P] {idx : ℕ → Type (max u v w)} (T : IndexedPresentation.{u, v, w} R P idx)
    {m n : ℕ} (h : n = m) {x : T.A} (hx : x ∈ T.grade m) : x ∈ T.grade n := by
  rw [h]
  exact hx

variable (R : Type u) (P : Type v) [CommRing R] [CommRing P] [Algebra R P]

/-- A boundary for the index family after `k` rungs: an element of the algebra it presents for
each variable, homogeneous of the degree one below the variable's.

The proof of homogeneity travels with the function because
`IndexedPresentation.chosenDifferential` asks for it, and the rule choosing the variables of the
next rung asks for the differential. -/
public def BdryAt (newIdx : (ℕ → Type (max u v w)) → ℕ → Type (max u v w)) (k : ℕ) :
    Type (max u v w) :=
  {b : (Σ n : ℕ, towerIndices newIdx k n) →
      (chosenPresentation.{u, v, w} R P (towerIndices newIdx k)).A //
    ∀ j, b j ∈ (chosenPresentation.{u, v, w} R P (towerIndices newIdx k)).grade j.1}

variable (newIdx : (ℕ → Type (max u v w)) → ℕ → Type (max u v w))
  (newBdry : (f : ℕ → Type (max u v w)) →
    (b : (Σ n : ℕ, f n) → (chosenPresentation.{u, v, w} R P f).A) →
    (∀ j, b j ∈ (chosenPresentation.{u, v, w} R P f).grade j.1) →
    (k : ℕ) → newIdx f k → (chosenPresentation.{u, v, w} R P f).A)
  (hnew : ∀ (f : ℕ → Type (max u v w))
    (b : (Σ n : ℕ, f n) → (chosenPresentation.{u, v, w} R P f).A)
    (hb : ∀ j, b j ∈ (chosenPresentation.{u, v, w} R P f).grade j.1) (k : ℕ) (x : newIdx f k),
    newBdry f b hb k x ∈ (chosenPresentation.{u, v, w} R P f).grade k)

/-- One rung of the boundary recursion: the boundaries of the variables already present are
pushed forward along the one-rung comparison, and a new variable of degree `k + 1` is given the
boundary the rule prescribes for it, pushed forward too. -/
public noncomputable def bdryStep (k : ℕ) (prev : BdryAt.{u, v, w} R P newIdx k) :
    BdryAt.{u, v, w} R P newIdx (k + 1) :=
  ⟨fun j =>
      if h : j.1 = k then
        oneStepComparison.{u, v, w} R P newIdx k
          (newBdry (towerIndices newIdx k) prev.1 prev.2 k
            (cast ((congrArg (towerIndices newIdx (k + 1)) h).trans
              (towerIndices_succ_self k)) j.2))
      else
        oneStepComparison.{u, v, w} R P newIdx k
          (prev.1 ⟨j.1, cast (towerIndices_succ_of_ne h) j.2⟩),
    by
      intro j
      dsimp only
      by_cases h : j.1 = k
      · rw [dite_eq_left h]
        exact mem_grade_of_degree_eq _ h
          (IndexedPresentation.comparison_mem_grade _ _ _ _ _ (hnew _ _ _ _ _))
      · rw [dite_eq_right h]
        exact IndexedPresentation.comparison_mem_grade _ _ _ _ _
          (prev.2 ⟨j.1, cast (towerIndices_succ_of_ne h) j.2⟩)⟩

/-- The boundary after `k` rungs of the recursion, with its homogeneity. -/
public noncomputable def towerBdryFull (k : ℕ) : BdryAt.{u, v, w} R P newIdx k :=
  Nat.rec (motive := fun k => BdryAt.{u, v, w} R P newIdx k)
    ⟨fun j => (isEmpty_towerIndices (Nat.zero_le j.1)).elim j.2,
      fun j => (isEmpty_towerIndices (Nat.zero_le j.1)).elim j.2⟩
    (fun k prev => bdryStep.{u, v, w} R P newIdx newBdry hnew k prev) k

public theorem towerBdryFull_succ (k : ℕ) :
    towerBdryFull.{u, v, w} R P newIdx newBdry hnew (k + 1) =
      bdryStep.{u, v, w} R P newIdx newBdry hnew k
        (towerBdryFull.{u, v, w} R P newIdx newBdry hnew k) := rfl

/-- **The boundary after `k` rungs of the recursion.** -/
public noncomputable def towerBoundary (k : ℕ) :
    (Σ n : ℕ, towerIndices newIdx k n) →
      (chosenPresentation.{u, v, w} R P (towerIndices newIdx k)).A :=
  (towerBdryFull.{u, v, w} R P newIdx newBdry hnew k).1

public theorem towerBoundary_mem (k : ℕ) (j : Σ n : ℕ, towerIndices newIdx k n) :
    towerBoundary.{u, v, w} R P newIdx newBdry hnew k j ∈
      (chosenPresentation.{u, v, w} R P (towerIndices newIdx k)).grade j.1 :=
  (towerBdryFull.{u, v, w} R P newIdx newBdry hnew k).2 j

/-- A variable already present at rung `k` keeps the boundary it had, pushed forward along the
one-rung comparison. -/
public theorem towerBoundary_succ_of_ne (k : ℕ) (j : Σ n : ℕ, towerIndices newIdx (k + 1) n)
    (h : j.1 ≠ k) :
    towerBoundary.{u, v, w} R P newIdx newBdry hnew (k + 1) j =
      oneStepComparison.{u, v, w} R P newIdx k
        (towerBoundary.{u, v, w} R P newIdx newBdry hnew k
          ⟨j.1, cast (towerIndices_succ_of_ne h) j.2⟩) := by
  rw [towerBoundary, towerBdryFull_succ, bdryStep]
  exact dite_eq_right h

/-- A variable adjoined at rung `k` is given the boundary the rule prescribes, pushed forward
along the one-rung comparison. -/
public theorem towerBoundary_succ_self (k : ℕ) (x : newIdx (towerIndices newIdx k) k) :
    towerBoundary.{u, v, w} R P newIdx newBdry hnew (k + 1)
        ⟨k, cast (towerIndices_succ_self k).symm x⟩ =
      oneStepComparison.{u, v, w} R P newIdx k
        (newBdry (towerIndices newIdx k) (towerBoundary.{u, v, w} R P newIdx newBdry hnew k)
          (towerBoundary_mem.{u, v, w} R P newIdx newBdry hnew k) k x) := by
  have key : cast ((congrArg (towerIndices newIdx (k + 1)) (rfl : k = k)).trans
      (towerIndices_succ_self k))
      (cast (towerIndices_succ_self (newIdx := newIdx) k).symm x) = x :=
    cast_eq_of_heq_aux _ (cast_heq _ x)
  rw [towerBoundary, towerBdryFull_succ, bdryStep]
  dsimp only
  rw [dite_eq_left (rfl : k = k)]
  exact congrArg (oneStepComparison.{u, v, w} R P newIdx k)
    (congrArg (fun y => newBdry (towerIndices newIdx k)
      (towerBdryFull.{u, v, w} R P newIdx newBdry hnew k).1
      (towerBdryFull.{u, v, w} R P newIdx newBdry hnew k).2 k y) key)

/-- **The boundary after rung `k` is the boundary after rung `n + 1`**, once both are pushed
forward to the algebra on the limiting family, for every variable of degree `n + 1` with
`n < k`: each rung pushes the boundaries forward along its own comparison, and the comparisons
of the tower form a directed system. -/
public theorem towerComparison_towerBoundary (n : ℕ) :
    ∀ (k : ℕ) (hn : n < k) (x : towerLimit newIdx n),
      towerComparison.{u, v, w} R P newIdx k
          (towerBoundary.{u, v, w} R P newIdx newBdry hnew k
            ⟨n, cast (towerIndices_eq_towerLimit hn).symm x⟩) =
        towerComparison.{u, v, w} R P newIdx (n + 1)
          (towerBoundary.{u, v, w} R P newIdx newBdry hnew (n + 1) ⟨n, x⟩) := by
  intro k
  induction k with
  | zero => intro hn; omega
  | succ k ih =>
    intro hn x
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
    · have hne : n ≠ k := by omega
      have hstep : cast (towerIndices_eq_towerLimit hn).symm x =
          towerIndicesStep newIdx k n (cast (towerIndices_eq_towerLimit hlt).symm x) :=
        cast_eq_of_heq_aux _ ((towerIndicesStep_heq hne _).trans
          (cast_heq (towerIndices_eq_towerLimit hlt).symm x)).symm
      rw [hstep, towerBoundary_succ_of_ne R P newIdx newBdry hnew k
        ⟨n, towerIndicesStep newIdx k n (cast (towerIndices_eq_towerLimit hlt).symm x)⟩ hne,
        cast_towerIndicesStep hne, ← AlgHom.comp_apply, towerComparison_oneStepComparison]
      exact ih hlt x
    · subst heq
      rw [cast_eq_of_heq_aux (towerIndices_eq_towerLimit hn).symm (HEq.refl x)]

/-- **The boundary on the limiting family**: a variable of degree `n + 1` keeps the boundary it
was given at the rung that adjoined it, pushed forward to the algebra on the limiting family. -/
public noncomputable def limitBoundary (j : Σ n : ℕ, towerLimit newIdx n) :
    (chosenPresentation.{u, v, w} R P (towerLimit newIdx)).A :=
  towerComparison.{u, v, w} R P newIdx (j.1 + 1)
    (towerBoundary.{u, v, w} R P newIdx newBdry hnew (j.1 + 1) ⟨j.1, j.2⟩)

public theorem limitBoundary_mem (j : Σ n : ℕ, towerLimit newIdx n) :
    limitBoundary.{u, v, w} R P newIdx newBdry hnew j ∈
      (chosenPresentation.{u, v, w} R P (towerLimit newIdx)).grade j.1 :=
  IndexedPresentation.comparison_mem_grade _ _ (towerEmbed newIdx (j.1 + 1)) j.1 _
    (towerBoundary_mem.{u, v, w} R P newIdx newBdry hnew (j.1 + 1) ⟨j.1, j.2⟩)

/-- **The limiting boundary is compatible with every rung.** On the variables already present
after `k` rungs it is the boundary after `k` rungs, pushed forward along the comparison. This is
exactly the hypothesis `IndexedPresentation.comparison_differential` asks for, so the comparison
out of each rung is a map of complexes for the prescribed differentials. -/
public theorem limitBoundary_towerEmbed (k : ℕ) (j : Σ n : ℕ, towerIndices newIdx k n) :
    limitBoundary.{u, v, w} R P newIdx newBdry hnew ⟨j.1, towerEmbed newIdx k j.1 j.2⟩ =
      towerComparison.{u, v, w} R P newIdx k
        (towerBoundary.{u, v, w} R P newIdx newBdry hnew k j) := by
  have hlt : j.1 < k := by
    by_contra h
    exact (isEmpty_towerIndices (Nat.not_lt.mp h)).elim j.2
  have hx : cast (towerIndices_eq_towerLimit hlt).symm (towerEmbed newIdx k j.1 j.2) = j.2 := by
    refine cast_eq_of_heq_aux _ ?_
    rw [towerEmbed, dite_eq_left hlt]
    exact cast_heq _ j.2
  rw [limitBoundary, ← towerComparison_towerBoundary R P newIdx newBdry hnew j.1 k hlt
    (towerEmbed newIdx k j.1 j.2), hx]

/-- **A cycle of degree `m` of the algebra on the limiting family is the image of a cycle of
degree `m` of the algebra after `k` rungs, for every `m ≤ k`.**

This is what makes the degree-by-degree construction compute: the rung that is to kill the
cycles of degree `m` sees all of them. Surjectivity in low degrees is
`IndexedPresentation.exists_mem_grade_comparison_eq`, and that the preimage is again a cycle is
`IndexedPresentation.comparison_differential_eq_zero_iff`, whose compatibility hypothesis is
`limitBoundary_towerEmbed`. -/
public theorem exists_cycle_towerComparison (k m : ℕ) (hm : m ≤ k)
    (x : (chosenPresentation.{u, v, w} R P (towerLimit newIdx)).A)
    (hx : x ∈ (chosenPresentation.{u, v, w} R P (towerLimit newIdx)).grade m)
    (hD : (chosenPresentation.{u, v, w} R P (towerLimit newIdx)).chosenDifferential
      (limitBoundary.{u, v, w} R P newIdx newBdry hnew)
      (limitBoundary_mem.{u, v, w} R P newIdx newBdry hnew) x = 0) :
    ∃ y : (chosenPresentation.{u, v, w} R P (towerIndices newIdx k)).A,
      y ∈ (chosenPresentation.{u, v, w} R P (towerIndices newIdx k)).grade m ∧
        (chosenPresentation.{u, v, w} R P (towerIndices newIdx k)).chosenDifferential
          (towerBoundary.{u, v, w} R P newIdx newBdry hnew k)
          (towerBoundary_mem.{u, v, w} R P newIdx newBdry hnew k) y = 0 ∧
        towerComparison.{u, v, w} R P newIdx k y = x := by
  obtain ⟨y, hy, hyx⟩ := IndexedPresentation.exists_mem_grade_comparison_eq
    (chosenPresentation.{u, v, w} R P (towerIndices newIdx k))
    (chosenPresentation.{u, v, w} R P (towerLimit newIdx)) (towerEmbed newIdx k)
    (towerRetract newIdx k) (towerRetract_towerEmbed k)
    (fun n hn z => towerEmbed_surjective (lt_of_lt_of_le hn hm) z) x hx
  refine ⟨y, hy, ?_, hyx⟩
  refine (IndexedPresentation.comparison_differential_eq_zero_iff _ _ (towerEmbed newIdx k)
    (towerBoundary.{u, v, w} R P newIdx newBdry hnew k)
    (towerBoundary_mem.{u, v, w} R P newIdx newBdry hnew k)
    (limitBoundary.{u, v, w} R P newIdx newBdry hnew)
    (limitBoundary_mem.{u, v, w} R P newIdx newBdry hnew) (towerRetract newIdx k)
    (towerRetract_towerEmbed k)
    (limitBoundary_towerEmbed.{u, v, w} R P newIdx newBdry hnew k) y).mp ?_
  rw [hyx]
  exact hD

end Boundary

end DividedPowers.TateResolution

end
