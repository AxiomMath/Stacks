module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TowerBoundary

/-!
# The rule of a degree-by-degree recursion sees the boundary

`DividedPowers.TateResolution.towerIndices` recurses on index families along a rule
`newIdx : (ℕ → Type t) → ℕ → Type t`, and
`DividedPowers.TateResolution.towerBoundary` recurses on the boundary alongside it along a rule
`newBdry` which does see the boundary of the family it extends. **The family rule does not.**
That is not expressive enough for a Tate resolution: the variables adjoined in degree `k + 1`
are to kill the cycles of degree `k`, and the module of cycles is a module of the differential,
hence of the boundary already chosen. Its finite generating families therefore vary with the
boundary, and no finite type depending on the family alone indexes one: a submodule of a fixed
finitely generated module over a Noetherian ring needs an unbounded number of generators, so
there is no bound to take.

This file repairs that by recursing on the *pair*. A `RungState k` is a family of variable
indices, empty in degrees at or above `k`, together with a homogeneous boundary for it; one rung
adjoins the variables of degree `k + 1` the rule prescribes for the state and pushes the
boundary forward. Since `RungState k` is a plain type the recursion is again an ordinary
`Nat.rec`.

The state recursion is then transported back onto the existing tower, so that every result of
`TowerBoundary` applies to it: `ruleIdx` reads off the state how many variables the rung
adjoins, `ruleBdry` prescribes their boundaries from the family and boundary it is handed, and
`rungState_eq` says the state after `k` rungs is exactly the family and boundary the tower
recursion builds from those two rules.

## Main definitions

* `DividedPowers.TateResolution.HomogeneousBoundary` — a boundary for a family of variable
  indices, homogeneous of the degree one below each variable's.
* `DividedPowers.TateResolution.RungState` — the state of the recursion after `k` rungs.
* `DividedPowers.TateResolution.BoundaryRule` — a rule for the recursion: how many variables to
  adjoin in each degree, and what their boundaries are.
* `DividedPowers.TateResolution.rungState` — the state after `k` rungs.
* `DividedPowers.TateResolution.ruleIdx` and `DividedPowers.TateResolution.ruleBdry` — the two
  rules of the existing tower that the state recursion induces.

## Main results

* `DividedPowers.TateResolution.rungState_eq` — the state after `k` rungs is the family and the
  boundary that the tower recursion builds from `ruleIdx` and `ruleBdry`. This is what lets a
  rule that sees the boundary be run by a tower whose family rule does not.
* `DividedPowers.TateResolution.size_towerBoundary` — the one consequence of that transport the
  construction uses: the rung-`k` rule adjoins as many variables for the family and boundary the
  tower has after `k` rungs as it does for the state.

## Implementation notes

The variables a rung adjoins are indexed by `ULift (Fin m)`, so a rule says *how many* there
are rather than naming a type, and prescribes their boundaries by a natural number index. That
is what makes the transport cheap: `ruleIdx f k` ignores the family it is handed and reads `m`
off the state, `ruleBdry` needs nothing from the state at all, and the two recursions therefore
differ in a single natural number, so `rungState_eq` is a congruence in it. A rule naming a type
would instead force the boundaries to be transported along an equality of index types.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

section State

variable (R : Type u) (P : Type v) [CommRing R] [CommRing P] [Algebra R P]

/-- A boundary for a prescribed family of variable indices: an element of the algebra the family
presents for each variable, homogeneous of the degree one below the variable's. -/
public def HomogeneousBoundary (f : ℕ → Type (max u v w)) : Type (max u v w) :=
  {b : (Σ n : ℕ, f n) → (chosenPresentation.{u, v, w} R P f).A //
    ∀ j, b j ∈ (chosenPresentation.{u, v, w} R P f).grade j.1}

/-- The boundaries carried by the existing tower after `k` rungs are the boundaries of the family
after `k` rungs. -/
public theorem bdryAt_eq_homogeneousBoundary
    (newIdx : (ℕ → Type (max u v w)) → ℕ → Type (max u v w)) (k : ℕ) :
    BdryAt.{u, v, w} R P newIdx k =
      HomogeneousBoundary.{u, v, w} R P (towerIndices newIdx k) := rfl

/-- The state of a degree-by-degree recursion after `k` rungs: a family of variable indices with
nothing adjoined in degree `n + 1` for `n ≥ k`, together with a homogeneous boundary for it.

The boundary travels with the family because the rule choosing the variables of the next rung
needs it: those variables are to kill cycles, and which elements are cycles depends on the
boundary already chosen. -/
public def RungState (k : ℕ) : Type (max u v w + 1) :=
  Σ f : {g : ℕ → Type (max u v w) // ∀ n : ℕ, k ≤ n → IsEmpty (g n)},
    HomogeneousBoundary.{u, v, w} R P f.1

end State

section Step

universe t

/-- The inclusion of a family of variable indices into the family with the variables of one
degree adjoined: in the degree of the rung there is nothing to include, and in every other
degree the two families agree. -/
public def updateEmbed (f : ℕ → Type t) (k : ℕ) (hf : IsEmpty (f k)) (τ : Type t) (n : ℕ) :
    f n → Function.update f k τ n :=
  fun x => if h : n = k then (hf.false (cast (congrArg f h) x)).elim
    else cast (Function.update_of_ne h τ f).symm x

/-- Away from the rung, the one-rung inclusion of the existing tower is the one-rung inclusion of
families: both are the cast that identifies the two families, and in the degree of the rung both
are an elimination of the empty type. -/
public theorem towerIndicesStep_eq_updateEmbed {newIdx : (ℕ → Type t) → ℕ → Type t} (k : ℕ)
    (hf : IsEmpty (towerIndices newIdx k k)) :
    towerIndicesStep newIdx k =
      updateEmbed (towerIndices newIdx k) k hf (newIdx (towerIndices newIdx k) k) := rfl

end Step

section Update

variable {R : Type u} {P : Type v} [CommRing R] [CommRing P] [Algebra R P]

/-- A homogeneous element of one degree is homogeneous of any degree equal to it. -/
private theorem mem_grade_of_eq {f : ℕ → Type (max u v w)} {m n : ℕ} (h : n = m)
    {x : (chosenPresentation.{u, v, w} R P f).A}
    (hx : x ∈ (chosenPresentation.{u, v, w} R P f).grade m) :
    x ∈ (chosenPresentation.{u, v, w} R P f).grade n := by
  rw [h]
  exact hx

variable (R P)

/-- The boundary after one rung: the boundaries of the variables already present are pushed
forward along the one-rung comparison, and a variable adjoined at the rung is given the
boundary prescribed for it, pushed forward too. -/
public noncomputable def updateBdry (f : ℕ → Type (max u v w)) (k : ℕ) (hf : IsEmpty (f k))
    (β : HomogeneousBoundary.{u, v, w} R P f) (τ : Type (max u v w))
    (nb : τ → (chosenPresentation.{u, v, w} R P f).A)
    (hnb : ∀ x : τ, nb x ∈ (chosenPresentation.{u, v, w} R P f).grade k) :
    HomogeneousBoundary.{u, v, w} R P (Function.update f k τ) :=
  ⟨fun j =>
      if h : j.1 = k then
        (chosenPresentation.{u, v, w} R P f).comparison _ (updateEmbed f k hf τ)
          (nb (cast ((congrArg (Function.update f k τ) h).trans
            (Function.update_self k τ f)) j.2))
      else
        (chosenPresentation.{u, v, w} R P f).comparison _ (updateEmbed f k hf τ)
          (β.1 ⟨j.1, cast (Function.update_of_ne h τ f) j.2⟩),
    by
      intro j
      dsimp only
      by_cases h : j.1 = k
      · rw [dite_eq_left h]
        exact mem_grade_of_eq h
          (IndexedPresentation.comparison_mem_grade _ _ _ _ _ (hnb _))
      · rw [dite_eq_right h]
        exact IndexedPresentation.comparison_mem_grade _ _ _ _ _
          (β.2 ⟨j.1, cast (Function.update_of_ne h τ f) j.2⟩)⟩

end Update
section Recursion

variable (R : Type u) (P : Type v) [CommRing R] [CommRing P] [Algebra R P]

/-- **A rule for a degree-by-degree construction**: how many variables to adjoin in degree
`k + 1` to a family of variable indices carrying a boundary, and what boundary each of them is
to be given.

The rule says how *many* variables to adjoin rather than naming a type for them, and prescribes
their boundaries by a natural-number index. That is what makes `rungState_eq` cheap: the two
recursions then differ in a single natural number. -/
public structure BoundaryRule : Type (max u v w + 1) where
  /-- The number of variables to adjoin in degree `k + 1`. -/
  size : (f : ℕ → Type (max u v w)) →
    (b : (Σ n : ℕ, f n) → (chosenPresentation.{u, v, w} R P f).A) →
    (∀ j, b j ∈ (chosenPresentation.{u, v, w} R P f).grade j.1) → ℕ → ℕ
  /-- The boundary prescribed for the variable adjoined at a given index. -/
  bdry : (f : ℕ → Type (max u v w)) →
    (b : (Σ n : ℕ, f n) → (chosenPresentation.{u, v, w} R P f).A) →
    (∀ j, b j ∈ (chosenPresentation.{u, v, w} R P f).grade j.1) → ℕ → ℕ →
      (chosenPresentation.{u, v, w} R P f).A
  /-- Each prescribed boundary is homogeneous of the degree one below its variable's. -/
  bdry_mem : ∀ (f : ℕ → Type (max u v w))
    (b : (Σ n : ℕ, f n) → (chosenPresentation.{u, v, w} R P f).A)
    (hb : ∀ j, b j ∈ (chosenPresentation.{u, v, w} R P f).grade j.1) (k i : ℕ),
    bdry f b hb k i ∈ (chosenPresentation.{u, v, w} R P f).grade k

/-- One rung of the recursion on states, with the number of variables adjoined and their
boundaries given separately. The variables are indexed by `ULift (Fin m)`, a type depending on
the state only through a natural number, which is what lets the recursion be transported onto
the existing tower by a congruence in that number alone. -/
public noncomputable def mkRungState (k : ℕ) (f : ℕ → Type (max u v w))
    (hf : ∀ n : ℕ, k ≤ n → IsEmpty (f n)) (β : HomogeneousBoundary.{u, v, w} R P f)
    (nb : ℕ → (chosenPresentation.{u, v, w} R P f).A)
    (hnb : ∀ i : ℕ, nb i ∈ (chosenPresentation.{u, v, w} R P f).grade k) (m : ℕ) :
    RungState.{u, v, w} R P (k + 1) :=
  ⟨⟨Function.update f k (ULift.{max u v w} (Fin m)), by
      intro n hn
      rw [Function.update_of_ne (by omega : n ≠ k)]
      exact hf n (by omega)⟩,
    updateBdry R P f k (hf k le_rfl) β (ULift.{max u v w} (Fin m))
      (fun x => nb x.down.1) (fun x => hnb x.down.1)⟩

variable (ρ : BoundaryRule.{u, v, w} R P)

/-- **The state after `k` rungs of the recursion.** -/
public noncomputable def rungState : (k : ℕ) → RungState.{u, v, w} R P k :=
  Nat.rec (motive := fun k => RungState.{u, v, w} R P k)
    ⟨⟨fun _ => (PEmpty : Type (max u v w)),
        fun _ _ => (inferInstance : IsEmpty (PEmpty : Type (max u v w)))⟩,
      ⟨fun j => (inferInstance : IsEmpty (PEmpty : Type (max u v w))).elim j.2,
        fun j => (inferInstance : IsEmpty (PEmpty : Type (max u v w))).elim j.2⟩⟩
    (fun k s => mkRungState.{u, v, w} R P k s.1.1 s.1.2 s.2
      (ρ.bdry s.1.1 s.2.1 s.2.2 k) (ρ.bdry_mem s.1.1 s.2.1 s.2.2 k)
      (ρ.size s.1.1 s.2.1 s.2.2 k))

/-- One more rung of the recursion: the state after `k + 1` rungs is the state after `k`
extended by the variables the rule adjoins in degree `k + 1`. -/
public theorem rungState_succ (k : ℕ) :
    rungState R P ρ (k + 1) =
      mkRungState.{u, v, w} R P k (rungState R P ρ k).1.1 (rungState R P ρ k).1.2
        (rungState R P ρ k).2
        (ρ.bdry _ (rungState R P ρ k).2.1 (rungState R P ρ k).2.2 k)
        (ρ.bdry_mem _ (rungState R P ρ k).2.1 (rungState R P ρ k).2.2 k)
        (ρ.size _ (rungState R P ρ k).2.1 (rungState R P ρ k).2.2 k) := rfl

/-- The family rule the state recursion induces, for the existing tower to run. It ignores the
family it is handed: the number of variables to adjoin is read off the state, and they are
indexed by a type depending on nothing else. -/
public noncomputable def ruleIdx (_f : ℕ → Type (max u v w)) (k : ℕ) : Type (max u v w) :=
  ULift.{max u v w} (Fin (ρ.size _ (rungState R P ρ k).2.1 (rungState R P ρ k).2.2 k))

/-- The boundary rule the state recursion induces, for the existing tower to run. It needs nothing
from the state: the index is a natural number, and the rule's boundary is applied to the family
and the boundary it is handed. -/
public noncomputable def ruleBdry (f : ℕ → Type (max u v w))
    (b : (Σ n : ℕ, f n) → (chosenPresentation.{u, v, w} R P f).A)
    (hb : ∀ j, b j ∈ (chosenPresentation.{u, v, w} R P f).grade j.1) (k : ℕ)
    (x : ruleIdx R P ρ f k) : (chosenPresentation.{u, v, w} R P f).A :=
  ρ.bdry f b hb k x.down.1

/-- The boundary `ruleBdry` assigns to each new variable has degree `k`. -/
public theorem ruleBdry_mem (f : ℕ → Type (max u v w))
    (b : (Σ n : ℕ, f n) → (chosenPresentation.{u, v, w} R P f).A)
    (hb : ∀ j, b j ∈ (chosenPresentation.{u, v, w} R P f).grade j.1) (k : ℕ)
    (x : ruleIdx R P ρ f k) :
    ruleBdry R P ρ f b hb k x ∈ (chosenPresentation.{u, v, w} R P f).grade k :=
  ρ.bdry_mem f b hb k x.down.1

/-- Every rung adjoins finitely many variables, whatever the rule says. -/
public instance finite_ruleIdx (f : ℕ → Type (max u v w)) (k : ℕ) :
    Finite (ruleIdx R P ρ f k) :=
  inferInstanceAs (Finite (ULift _))

/-- **The state after `k` rungs is the family and the boundary the tower recursion builds from
the two rules the state recursion induces.**

This is what lets a rule that sees the boundary be run by a tower whose family rule does not,
and it is a congruence in a single natural number: the two recursions differ only in the number
of variables the rung adjoins, which the two sides compute from the same state. -/
public theorem rungState_eq : ∀ k : ℕ,
    rungState R P ρ k =
      ⟨⟨towerIndices (ruleIdx R P ρ) k, fun _ hn => isEmpty_towerIndices hn⟩,
        towerBdryFull.{u, v, w} R P (ruleIdx R P ρ) (ruleBdry R P ρ) (ruleBdry_mem R P ρ) k⟩
  | 0 => rfl
  | k + 1 => by
      have ih := rungState_eq k
      rw [rungState_succ, ih]
      exact congrArg
        (mkRungState.{u, v, w} R P k (towerIndices (ruleIdx R P ρ) k)
          (fun _ hn => isEmpty_towerIndices hn)
          (towerBdryFull R P _ _ (ruleBdry_mem R P ρ) k)
          (ρ.bdry _ (towerBdryFull R P _ _ (ruleBdry_mem R P ρ) k).1
            (towerBdryFull R P _ _ (ruleBdry_mem R P ρ) k).2 k)
          (ρ.bdry_mem _ (towerBdryFull R P _ _ (ruleBdry_mem R P ρ) k).1
            (towerBdryFull R P _ _ (ruleBdry_mem R P ρ) k).2 k))
        (congrArg (fun s : RungState.{u, v, w} R P k => ρ.size s.1.1 s.2.1 s.2.2 k) ih).symm

/-- The number of variables the rung-`k` rule adjoins, computed from the family and boundary the
existing tower has after `k` rungs, is the number computed from the state. This is the only thing
the transport is needed for. -/
public theorem size_towerBoundary (k : ℕ) :
    ρ.size (towerIndices (ruleIdx R P ρ) k)
        (towerBoundary R P (ruleIdx R P ρ) (ruleBdry R P ρ) (ruleBdry_mem R P ρ) k)
        (towerBoundary_mem R P (ruleIdx R P ρ) (ruleBdry R P ρ) (ruleBdry_mem R P ρ) k) k =
      ρ.size _ (rungState R P ρ k).2.1 (rungState R P ρ k).2.2 k :=
  (congrArg (fun s : RungState.{u, v, w} R P k => ρ.size s.1.1 s.2.1 s.2.2 k)
    (rungState_eq R P ρ k)).symm

end Recursion

end DividedPowers.TateResolution

end
