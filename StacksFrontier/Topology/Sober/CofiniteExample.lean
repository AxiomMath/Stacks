module

public import StacksFrontier.Topology.Sober.Defs

/-!
# An infinite set with the cofinite topology is Kolmogorov but not quasi-sober (Stacks 0B33)

Let `Y` be an infinite set carrying the topology whose closed sets are `Y` and the finite
subsets of `Y`. This is Mathlib's `CofiniteTopology Y`, so it is not redefined here; the
hypothesis that `Y` is infinite is `Infinite Y` and is essential, since on a finite set the
cofinite topology is discrete and hence sober.

* Kolmogorov: singletons are finite, hence closed, so the space is `T1Space` — this is a
  Mathlib instance — and therefore `T0Space`.
* Not quasi-sober: any two nonempty opens meet, because their complements are finite and an
  infinite set is not a union of two finite sets, so the whole space is irreducible (again a
  Mathlib instance) as well as closed. A generic point `x` for it would give
  `Set.univ = closure {x} = {x}`, making an infinite space a singleton.
* The singletons cover `Y`, and each of them, as a subspace, is a one-point space: discrete,
  and sober in the sense of Stacks 004X (`StacksSober`).

Stacks 0B33 calls the singletons the irreducible components of `Y`. That parenthetical is
inaccurate: the space is irreducible, so `Set.univ` is its unique irreducible component
(`irreducibleComponents_cofiniteTopology`), the singletons being irreducible but not maximal.
The covering statement itself does not depend on it and is recorded below.

## Main results

* `t0Space_cofiniteTopology`: `T0Space (CofiniteTopology Y)`.
* `not_quasiSober_cofiniteTopology`: `¬ QuasiSober (CofiniteTopology Y)` for `Y` infinite.
* `singleton_cover_cofiniteTopology`: the singletons cover the space and each is discrete and
  sober.
* `irreducibleComponents_cofiniteTopology`: the unique irreducible component is `Set.univ`.
-/

@[expose] public section

variable (Y : Type*)

/-- **Stacks 0B33** (Kolmogorov).
An infinite set with the cofinite topology is Kolmogorov: its singletons are finite, hence
closed, so the space is `T1Space` and a fortiori `T0Space`. Infiniteness is not needed here. -/
@[stacks 0B33 "Kolmogorov"]
theorem t0Space_cofiniteTopology : T0Space (CofiniteTopology Y) := inferInstance

/-- **Stacks 0B33** (not quasi-sober).
An infinite set with the cofinite topology is not quasi-sober: the whole space is irreducible
and closed, but the closure of a singleton is that singleton, so no point is generic for it. -/
@[stacks 0B33 "not quasi-sober"]
theorem not_quasiSober_cofiniteTopology [Infinite Y] : ¬ QuasiSober (CofiniteTopology Y) := by
  intro _
  have : Infinite (CofiniteTopology Y) :=
    Infinite.of_injective CofiniteTopology.of CofiniteTopology.of.injective
  obtain ⟨x, hx⟩ := QuasiSober.sober
    (IrreducibleSpace.isIrreducible_univ (CofiniteTopology Y)) isClosed_univ
  have hclos : closure ({x} : Set (CofiniteTopology Y)) = Set.univ := hx
  rw [isClosed_singleton.closure_eq] at hclos
  exact Set.infinite_univ (hclos ▸ Set.finite_singleton x)

/-- **Stacks 0B33** (covering by sober subspaces).
The singletons of an infinite set with the cofinite topology cover it, and each singleton
subspace is discrete and hence sober: it has exactly one point. So a space covered by sober
subspaces need not be quasi-sober. -/
@[stacks 0B33 "covering by discrete, hence sober, subspaces"]
theorem singleton_cover_cofiniteTopology :
    (⋃ y : CofiniteTopology Y, ({y} : Set (CofiniteTopology Y))) = Set.univ ∧
      ∀ y : CofiniteTopology Y, DiscreteTopology ({y} : Set (CofiniteTopology Y)) ∧
        StacksSober ({y} : Set (CofiniteTopology Y)) :=
  ⟨Set.iUnion_of_singleton _, fun _ =>
    ⟨inferInstance, stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩⟩⟩

