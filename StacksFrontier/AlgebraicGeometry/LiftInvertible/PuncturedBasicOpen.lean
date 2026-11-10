module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# Punctured basic opens around a closed point of a one-dimensional spectrum

Let `R` be a commutative ring and `𝔪` a closed point of `Spec R`. If `f ∈ 𝔪` cuts out a
*finite* set of *closed* points — which, on a Noetherian spectrum of Krull dimension at most
one, happens as soon as the zero locus of `f` contains no irreducible component — then there is
`u ∈ R` with

* `𝔪 ∈ D(u)`,
* `D(u) \ {𝔪} = D(u * f)`, and
* `D(u)` disjoint from any prescribed finite set of closed points not containing `𝔪`.

So `𝔪` has a basic open neighbourhood, avoiding finitely many other closed points, whose
puncture at `𝔪` is again a *basic* open, hence again affine. This is the step that turns a
lifting problem on a punctured neighbourhood of a closed point of a curve into a lifting
problem over a ring: on an affine scheme the restriction map of the structure sheaf to a closed
subscheme is surjective, so a section of the closed subscheme extends, and a unit extends to a
unit as soon as the ideal cutting out the subscheme is nilpotent
(`IsNilpotent.isUnit_quotient_mk_iff`).

The complement of a closed point in a one-dimensional affine scheme is affine for a softer
reason as well — Serre's criterion plus the vanishing of `H²` of a zero-dimensional local
cohomology — but the statement proved here is elementary: `u` is produced by prime avoidance
and the identity `D(u) \ {𝔪} = D(uf)` is a membership computation.

The finite avoidance set is what lets the punctured neighbourhood be used as a *chart* in a
star-shaped cover: the finitely many closed points left over by a one-dimensional cover have to
be separated from one another, not merely isolated one at a time.

## Main results

* `Stacks.LiftInvertible.exists_notMem_asIdeal_forall_mem_asIdeal`: prime avoidance against a
  finite set of closed points of `Spec R` not containing `𝔪` — an element outside `𝔪` and
  inside every one of them.
* `Stacks.LiftInvertible.exists_basicOpen_disjoint_sdiff_singleton_eq_basicOpen`: the statement
  above, with the finiteness and closedness of the zero locus of `f` as hypotheses.
* `Stacks.LiftInvertible.exists_basicOpen_sdiff_singleton_eq_basicOpen`: its case of an empty
  avoidance set.
* `Stacks.LiftInvertible.exists_mem_asIdeal_forall_not_irreducibleComponent_subset_zeroLocus`:
  on a Noetherian spectrum, an element of a closed point `𝔪` which is not in the generic point
  of any irreducible component, provided some other point specializes to `𝔪`.
* `exists_basicOpen_sdiff_singleton_eq_basicOpen_of_topologicalKrullDim_le_one` and
  `exists_basicOpen_isolating_of_topologicalKrullDim_le_one`
  (in the same namespace): the two statements above with the finiteness and closedness
  hypotheses supplied by the dimension bound through
  `Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset` and
  `Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset`, the second
  additionally choosing `f` by prime avoidance so that nothing but the bound is assumed.

## Implementation notes

`u` is chosen in the intersection of the primes of `V(f) \ {𝔪}` and of the avoidance set, and
outside `𝔪`. That such a `u` exists is prime avoidance in the form `Ideal.IsPrime.inf_le'`:
were the finite intersection contained in `𝔪`, one of the primes would be, and a maximal ideal
contained in a proper ideal equals it. The closedness hypothesis is what makes those primes
maximal; it is stated topologically, as `IsClosed {p}`, because that is the form in which the
dimension results of `StacksFrontier/Topology/Dimension/DimensionLEOne.lean` deliver it.

No Noetherian hypothesis is used in the statements that take the finiteness of `V(f)` outright.

The hypothesis under which `f` can be chosen is that `𝔪` is **not** the generic point of an
irreducible component. It is stated as the existence of a point specializing to `𝔪` and
distinct from it, rather than as `{𝔪} ∉ irreducibleComponents`, because that form transports
along an open immersion by `Topology.IsInducing.specializes_iff` whereas the set of irreducible
components does not.

## References

* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
-/

@[expose] public section

open Set PrimeSpectrum TopologicalSpace Topology

universe u

namespace Stacks.LiftInvertible

variable {R : Type u} [CommRing R]

/-- **Prime avoidance against a finite set of closed points.** Given a finite set `S` of closed
points of `Spec R` and a point `𝔪 ∉ S`, some `u ∈ R` lies outside `𝔪` and inside every member
of `S`.

Were the finite intersection of the members of `S` contained in `𝔪`, one of them would be, and
a maximal ideal contained in the proper ideal `𝔪` equals it — so `𝔪` would be a member. -/
theorem exists_notMem_asIdeal_forall_mem_asIdeal {𝔪 : PrimeSpectrum R}
    {S : Set (PrimeSpectrum R)} (hfin : S.Finite)
    (hcl : ∀ p ∈ S, IsClosed ({p} : Set (PrimeSpectrum R))) (hm : 𝔪 ∉ S) :
    ∃ u : R, u ∉ 𝔪.asIdeal ∧ ∀ p ∈ S, u ∈ p.asIdeal := by
  classical
  have hnot : ¬ (hfin.toFinset.inf (fun p : PrimeSpectrum R => p.asIdeal) ≤ 𝔪.asIdeal) := by
    rw [Ideal.IsPrime.inf_le' 𝔪.isPrime]
    rintro ⟨p, hp, hple⟩
    rw [Set.Finite.mem_toFinset] at hp
    have hpmax : p.asIdeal.IsMaximal := (isClosed_singleton_iff_isMaximal p).mp (hcl p hp)
    exact hm (PrimeSpectrum.ext (hpmax.eq_of_le 𝔪.isPrime.ne_top hple) ▸ hp)
  obtain ⟨u, humem, hunot⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  refine ⟨u, hunot, fun p hp => ?_⟩
  have hle := Finset.inf_le (f := fun q : PrimeSpectrum R => q.asIdeal)
    ((Set.Finite.mem_toFinset hfin).mpr hp)
  exact IsConcreteLE.le_iff.mp hle humem

/-- **A closed point whose zero locus is finite and closed has a basic open neighbourhood with
basic punctured complement, avoiding any prescribed finite set of other closed points.** Let
`f ∈ 𝔪` be such that the zero locus of `f` is finite and consists of closed points, and let `T`
be a finite set of closed points with `𝔪 ∉ T`. Then some `u ∈ R` satisfies `𝔪 ∈ D(u)`,
`D(u) \ {𝔪} = D(u * f)` and `D(u) ∩ T = ∅`.

The element `u` is chosen inside every prime of `V(f) \ {𝔪}` and of `T`, and outside `𝔪`, by
`Stacks.LiftInvertible.exists_notMem_asIdeal_forall_mem_asIdeal`. -/
theorem exists_basicOpen_disjoint_sdiff_singleton_eq_basicOpen {𝔪 : PrimeSpectrum R} {f : R}
    (hf : f ∈ 𝔪.asIdeal)
    (hfin : (zeroLocus {f} : Set (PrimeSpectrum R)).Finite)
    (hcl : ∀ p ∈ (zeroLocus {f} : Set (PrimeSpectrum R)),
      IsClosed ({p} : Set (PrimeSpectrum R)))
    {T : Set (PrimeSpectrum R)} (hTfin : T.Finite)
    (hTcl : ∀ p ∈ T, IsClosed ({p} : Set (PrimeSpectrum R))) (hTm : 𝔪 ∉ T) :
    ∃ u : R, 𝔪 ∈ basicOpen u ∧
      (basicOpen u : Set (PrimeSpectrum R)) \ {𝔪} =
        (basicOpen (u * f) : Set (PrimeSpectrum R)) ∧
      (basicOpen u : Set (PrimeSpectrum R)) ∩ T = ∅ := by
  classical
  obtain ⟨u, hunot, hu⟩ :=
    exists_notMem_asIdeal_forall_mem_asIdeal
      (S := ((zeroLocus {f} : Set (PrimeSpectrum R)) \ {𝔪}) ∪ T)
      ((hfin.subset sdiff_subset).union hTfin)
      (fun p hp => hp.elim (fun h => hcl p h.1) (fun h => hTcl p h))
      (fun h => h.elim (fun h' => h'.2 rfl) (fun h' => hTm h'))
  refine ⟨u, (mem_basicOpen u 𝔪).mpr hunot, ?_, ?_⟩
  · have hmul : (basicOpen (u * f) : Set (PrimeSpectrum R)) =
        (basicOpen u : Set (PrimeSpectrum R)) ∩ (basicOpen f : Set (PrimeSpectrum R)) := by
      rw [basicOpen_mul]; rfl
    rw [hmul]
    ext p
    refine ⟨fun hp => ⟨hp.1, ?_⟩, fun hp => ⟨hp.1, ?_⟩⟩
    · refine (mem_basicOpen f p).mpr fun hfp => ?_
      have hpT : p ∈ (zeroLocus {f} : Set (PrimeSpectrum R)) :=
        (mem_zeroLocus _ _).mpr (Set.singleton_subset_iff.mpr hfp)
      exact (mem_basicOpen u p).mp hp.1 (hu p (Or.inl ⟨hpT, hp.2⟩))
    · intro hpm
      exact (mem_basicOpen f p).mp hp.2 (by rw [show p = 𝔪 from hpm]; exact hf)
  · refine Set.eq_empty_iff_forall_notMem.2 fun p hp => ?_
    exact (mem_basicOpen u p).mp hp.1 (hu p (Or.inr hp.2))

/-- **A closed point whose zero locus is finite and closed has a basic open neighbourhood with
basic punctured complement.** Let `f ∈ 𝔪` be such that the zero locus of `f` is finite and
consists of closed points. Then some `u ∈ R` satisfies `𝔪 ∈ D(u)` and `D(u) \ {𝔪} = D(u * f)`.

The case of an empty avoidance set of
`Stacks.LiftInvertible.exists_basicOpen_disjoint_sdiff_singleton_eq_basicOpen`. -/
theorem exists_basicOpen_sdiff_singleton_eq_basicOpen {𝔪 : PrimeSpectrum R} {f : R}
    (hf : f ∈ 𝔪.asIdeal)
    (hfin : (zeroLocus {f} : Set (PrimeSpectrum R)).Finite)
    (hcl : ∀ p ∈ (zeroLocus {f} : Set (PrimeSpectrum R)),
      IsClosed ({p} : Set (PrimeSpectrum R))) :
    ∃ u : R, 𝔪 ∈ basicOpen u ∧
      (basicOpen u : Set (PrimeSpectrum R)) \ {𝔪} =
        (basicOpen (u * f) : Set (PrimeSpectrum R)) :=
  let ⟨u, hmem, heq, _⟩ :=
    exists_basicOpen_disjoint_sdiff_singleton_eq_basicOpen hf hfin hcl (T := ∅)
      Set.finite_empty (fun _ h => h.elim) (fun h => h)
  ⟨u, hmem, heq⟩

/-- **The dimension-one form.** On a Noetherian spectrum of Krull dimension at most one, a
closed point `𝔪` and an `f ∈ 𝔪` whose zero locus contains no irreducible component yield
`u ∈ R` with `𝔪 ∈ D(u)` and `D(u) \ {𝔪} = D(u * f)`.

The two hypotheses of `exists_basicOpen_sdiff_singleton_eq_basicOpen` are exactly what the
dimension bound supplies: a closed set containing no irreducible component of a Noetherian
sober space of dimension at most one is finite and consists of closed points. -/
theorem exists_basicOpen_sdiff_singleton_eq_basicOpen_of_topologicalKrullDim_le_one
    [NoetherianSpace (PrimeSpectrum R)] (hdim : topologicalKrullDim (PrimeSpectrum R) ≤ 1)
    {𝔪 : PrimeSpectrum R} {f : R} (hf : f ∈ 𝔪.asIdeal)
    (hfc : ∀ C ∈ irreducibleComponents (PrimeSpectrum R),
      ¬ C ⊆ (zeroLocus {f} : Set (PrimeSpectrum R))) :
    ∃ u : R, 𝔪 ∈ basicOpen u ∧
      (basicOpen u : Set (PrimeSpectrum R)) \ {𝔪} =
        (basicOpen (u * f) : Set (PrimeSpectrum R)) :=
  exists_basicOpen_sdiff_singleton_eq_basicOpen hf
    (Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hdim
      (isClosed_zeroLocus _) hfc)
    (fun _ hp => Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
      hdim (isClosed_zeroLocus _) hfc hp)

/-- **A closed point which is not a generic point carries a function missing every irreducible
component.** On a Noetherian spectrum, let `𝔪` be a closed point to which some other point
specializes. Then some `f ∈ 𝔪` lies in no generic point of an irreducible component, so no
irreducible component is contained in the zero locus of `f`.

This is prime avoidance against the finitely many generic points. That `𝔪` contains none of
them is where the hypothesis is used: a generic point above `𝔪` would equal `𝔪` because `𝔪` is
closed, making `{𝔪}` an irreducible component, which the point specializing to `𝔪` contradicts
by maximality. -/
theorem exists_mem_asIdeal_forall_not_irreducibleComponent_subset_zeroLocus
    [NoetherianSpace (PrimeSpectrum R)] {𝔪 : PrimeSpectrum R}
    (hmcl : IsClosed ({𝔪} : Set (PrimeSpectrum R)))
    (hspec : ∃ y : PrimeSpectrum R, y ≠ 𝔪 ∧ 𝔪 ∈ closure ({y} : Set (PrimeSpectrum R))) :
    ∃ f ∈ 𝔪.asIdeal, ∀ C ∈ irreducibleComponents (PrimeSpectrum R),
      ¬ C ⊆ (zeroLocus {f} : Set (PrimeSpectrum R)) := by
  classical
  have : Finite (irreducibleComponents (PrimeSpectrum R)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  choose η hη using fun C : irreducibleComponents (PrimeSpectrum R) =>
    QuasiSober.sober C.2.1 (isClosed_of_mem_irreducibleComponents _ C.2)
  have hηmem : ∀ C : irreducibleComponents (PrimeSpectrum R),
      η C ∈ (C : Set (PrimeSpectrum R)) := by
    intro C
    rw [← isGenericPoint_def.1 (hη C)]
    exact subset_closure rfl
  have hnot : ¬ ((𝔪.asIdeal : Set R) ⊆ ⋃ p ∈ Set.range η, (p.asIdeal : Set R)) := by
    intro hsub
    obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime_finite (Set.finite_range η) 𝔪 𝔪
      (f := PrimeSpectrum.asIdeal) (fun i _ _ _ => i.isPrime)).mp hsub
    obtain ⟨C, rfl⟩ := hp
    have hpm : η C = 𝔪 := by
      have hmem : η C ∈ closure ({𝔪} : Set (PrimeSpectrum R)) := by
        rw [PrimeSpectrum.closure_singleton]
        exact hle
      simpa [hmcl.closure_eq] using hmem
    have hC : (C : Set (PrimeSpectrum R)) = {𝔪} := by
      rw [← isGenericPoint_def.1 (hη C), hpm, hmcl.closure_eq]
    obtain ⟨y, hyne, hy⟩ := hspec
    have hsub' : (C : Set (PrimeSpectrum R)) ⊆ closure ({y} : Set (PrimeSpectrum R)) := by
      rw [hC]; exact Set.singleton_subset_iff.2 hy
    have hback := C.2.2 isIrreducible_singleton.closure hsub'
    rw [hC] at hback
    exact hyne (hback (subset_closure rfl))
  obtain ⟨f, hfm, hf⟩ := Set.not_subset.mp hnot
  refine ⟨f, hfm, fun C hC hCsub => ?_⟩
  have hz : η ⟨C, hC⟩ ∈ (zeroLocus {f} : Set (PrimeSpectrum R)) := hCsub (hηmem ⟨C, hC⟩)
  rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hz
  exact hf (Set.mem_biUnion (Set.mem_range_self _) hz)

/-- **An isolating basic open with basic puncture, from the dimension bound alone.** On a
Noetherian spectrum of Krull dimension at most one, let `𝔪` be a closed point to which some
other point specializes, and let `T` be a finite set of closed points with `𝔪 ∉ T`. Then there
are `u, v ∈ R` with `𝔪 ∈ D(u)`, `D(u) ∩ T = ∅` and `D(u) \ {𝔪} = D(v)`.

Nothing beyond the bound is assumed: the function cutting out `𝔪` is produced by
`Stacks.LiftInvertible.exists_mem_asIdeal_forall_not_irreducibleComponent_subset_zeroLocus` and
its zero locus is then finite and discrete by the dimension results of
`StacksFrontier/Topology/Dimension/DimensionLEOne.lean`. -/
theorem exists_basicOpen_isolating_of_topologicalKrullDim_le_one
    [NoetherianSpace (PrimeSpectrum R)] (hdim : topologicalKrullDim (PrimeSpectrum R) ≤ 1)
    {𝔪 : PrimeSpectrum R} (hmcl : IsClosed ({𝔪} : Set (PrimeSpectrum R)))
    (hspec : ∃ y : PrimeSpectrum R, y ≠ 𝔪 ∧ 𝔪 ∈ closure ({y} : Set (PrimeSpectrum R)))
    {T : Set (PrimeSpectrum R)} (hTfin : T.Finite)
    (hTcl : ∀ p ∈ T, IsClosed ({p} : Set (PrimeSpectrum R))) (hTm : 𝔪 ∉ T) :
    ∃ u v : R, 𝔪 ∈ basicOpen u ∧
      (basicOpen u : Set (PrimeSpectrum R)) ∩ T = ∅ ∧
      (basicOpen u : Set (PrimeSpectrum R)) \ {𝔪} =
        (basicOpen v : Set (PrimeSpectrum R)) := by
  obtain ⟨f, hf, hfc⟩ :=
    exists_mem_asIdeal_forall_not_irreducibleComponent_subset_zeroLocus hmcl hspec
  obtain ⟨u, humem, hueq, hudisj⟩ :=
    exists_basicOpen_disjoint_sdiff_singleton_eq_basicOpen hf
      (Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hdim
        (isClosed_zeroLocus _) hfc)
      (fun _ hp => Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
        hdim (isClosed_zeroLocus _) hfc hp)
      hTfin hTcl hTm
  exact ⟨u, u * f, humem, hudisj, hueq⟩

end Stacks.LiftInvertible

end
