module

public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ClopenRefinement
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationTransition

/-!
# Lifting clopen sets from the closed points of a w-local space

In a w-local space `X` the closed points form a closed subspace which is homeomorphic, via
`x ↦ ConnectedComponents.mk x`, to the space of connected components of `X`. Pulling a clopen
subset of the closed points back along that homeomorphism and then along the quotient map
`X → π₀(X)` produces a clopen subset of `X` meeting the closed points in exactly the given set.
This is the geometric input for the universal property of the w-localization of a ring: for a
ring map `f : A → B` with `Spec B` w-local, each finite vanishing stratification of `Spec A`
induces a partition of the closed points of `Spec B` into clopen pieces, which lifts to a
partition of `Spec B` into clopen pieces and hence to a complete set of orthogonal idempotents
of `B`.

## Main definitions

* `AlgebraicGeometry.ProEtale.closedPointsComponentsHomeomorph`: the homeomorphism from the
  closed points of a w-local space to its space of connected components.
* `AlgebraicGeometry.ProEtale.closedPointsClopenLift`: the clopen subset of `X` attached to a
  clopen subset of the closed points of `X`.
* `AlgebraicGeometry.ProEtale.stratumClopen`: the clopen subset of `Spec B` cut out by a
  vanishing pattern of a finite subset of `A`.
* `AlgebraicGeometry.ProEtale.stratumIdempotent`: the idempotent of `B` cutting out
  `stratumClopen`.
* `AlgebraicGeometry.ProEtale.quotientProductEquiv`: the resulting decomposition of `B` as the
  product of its quotients by the stratum idempotents.

## Main results

* `AlgebraicGeometry.ProEtale.isClopen_of_isConstructible`: in a compact Hausdorff space every
  constructible set is clopen.
* `AlgebraicGeometry.ProEtale.closedPoints_preimage_isClopen_of_isConstructible`: a
  constructible subset of a w-local space meets its closed points in a clopen set.
* `AlgebraicGeometry.ProEtale.mem_closedPointsClopenLift_iff_specialization`: a point lies in
  the lift of a clopen set of closed points exactly when its closed specialization does.
* `AlgebraicGeometry.ProEtale.stratumIdempotents_complete`: the stratum idempotents attached to
  a finite subset `E ⊆ A` form a complete set of orthogonal idempotents of `B`.

## Implementation notes

The pin from which this file is ported used an unavailable implication "constructible and stable
under generalization implies open". It is replaced here by
`AlgebraicGeometry.ProEtale.isClopen_of_isConstructible`, which needs only compactness and the
Hausdorff property: a retrocompact open subset of a compact space is compact, hence closed, and
the clopen sets form a Boolean subalgebra. The Hausdorff property of the closed points is read
off the homeomorphism with the space of connected components, so that homeomorphism is
constructed before the clopen criterion rather than after it.

## References

* [Stacks Project, Tag 0977](https://stacks.math.columbia.edu/tag/0977)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.ProEtale

/-! ### Clopen sets of the closed points of a w-local space -/

section ClopenLift

variable {X : Type*} [TopologicalSpace X]

/-- In a compact Hausdorff space every constructible set is clopen: a retrocompact open set is
compact, hence closed, and the clopen sets are closed under union and complement. -/
theorem isClopen_of_isConstructible [CompactSpace X] [T2Space X] {s : Set X}
    (hs : Topology.IsConstructible s) : IsClopen s := by
  induction hs using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUcomp => exact ⟨hUcomp.isCompact.isClosed, hUopen⟩
  | union s _ t _ hs' ht' => exact hs'.union ht'
  | compl s _ hs' => exact hs'.compl

/-- The closed points of a topological space form a `T₁` subspace. -/
theorem t1Space_closedPoints : T1Space (closedPoints X) :=
  ⟨fun x => by
    refine isClosed_induced_iff.2 ⟨{(x : X)}, mem_closedPoints_iff.mp x.2, ?_⟩
    ext y
    simp [Subtype.ext_iff]⟩

/-- The closed points of a w-local space form a spectral space: they are a closed subset, hence
closed in the constructible topology. -/
theorem spectralSpace_closedPoints [WLocalSpace X] : SpectralSpace (closedPoints X) :=
  spectralSpace_of_isClosed_constructibleTopology _
    WLocalSpace.isClosed_closedPoints.isClosed_constructibleTopology

/-- Every point of a w-local space is in the same connected component as any of its
specializations. -/
theorem connectedComponents_eq_of_specializes {x y : X} (hxy : x ⤳ y) :
    ConnectedComponents.mk x = ConnectedComponents.mk y :=
  (ConnectedComponents.coe_eq_coe'.2 <|
    isPreconnected_singleton.closure.subset_connectedComponent
      (subset_closure (Set.mem_singleton x)) (specializes_iff_mem_closure.mp hxy)).symm

variable [WLocalSpace X]

/-- Sending a closed point of a w-local space to its connected component is a homeomorphism
from the closed points of `X` onto the space of connected components of `X`. -/
def closedPointsComponentsHomeomorph : closedPoints X ≃ₜ ConnectedComponents X := by
  letI : SpectralSpace (closedPoints X) := spectralSpace_closedPoints
  have huniq : ∀ x : X, ∃! x₀ : closedPoints X, x ⤳ x₀.1 := by
    intro x
    obtain ⟨c, ⟨hc, hxc⟩, hunique⟩ := WLocalSpace.existsUnique_closedPoint_specializes x
    exact ⟨⟨c, hc⟩, hxc, fun c' hc' => Subtype.ext (hunique c'.1 ⟨c'.2, hc'⟩)⟩
  have hbij := closedPoints_to_connectedComponents_bijective_of_unique_specialization
    WLocalSpace.isClosed_closedPoints huniq
  letI : T2Space (ConnectedComponents X) := (connectedComponents_isProfinite X).1
  exact (isHomeomorph_iff_continuous_bijective.mpr
    ⟨ConnectedComponents.continuous_coe.comp continuous_subtype_val, hbij⟩).homeomorph

/-- The homeomorphism onto the space of connected components sends a closed point to its own
connected component. -/
@[simp]
theorem closedPointsComponentsHomeomorph_apply (c : closedPoints X) :
    closedPointsComponentsHomeomorph c = ConnectedComponents.mk c.1 := rfl

/-- The closed points of a w-local space form a Hausdorff space, being homeomorphic to the
(profinite) space of connected components. -/
theorem t2Space_closedPoints : T2Space (closedPoints X) := by
  have : T2Space (ConnectedComponents X) := (connectedComponents_isProfinite X).1
  exact (closedPointsComponentsHomeomorph (X := X)).symm.t2Space

/-- A constructible subset of a w-local space meets the closed points in a clopen set. -/
theorem closedPoints_preimage_isClopen_of_isConstructible {s : Set X}
    (hs : Topology.IsConstructible s) :
    IsClopen ((Subtype.val : closedPoints X → X) ⁻¹' s) := by
  have : SpectralSpace (closedPoints X) := spectralSpace_closedPoints
  have : T2Space (closedPoints X) := t2Space_closedPoints
  have hretro : IsRetrocompact (closedPoints X : Set X) := by
    intro U hUcompact hUopen
    simpa [Set.inter_comm] using
      hUcompact.inter_right WLocalSpace.isClosed_closedPoints
  refine isClopen_of_isConstructible (hs.preimage continuous_subtype_val ?_)
  intro U hUopen hUcompact
  exact ((IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hretro).isCompact_preimage_of_isOpen
    hUopen hUcompact.isCompact).isRetrocompact (hUopen.preimage continuous_subtype_val)

/-- The clopen subset of a w-local space `X` attached to a clopen subset of its closed points:
the saturation of the given set under generalization, described as the preimage of its image in
`π₀(X)`. -/
def closedPointsClopenLift (S : Clopens (closedPoints X)) : Clopens X where
  carrier := ConnectedComponents.mk ⁻¹'
    (closedPointsComponentsHomeomorph (X := X) '' (S : Set (closedPoints X)))
  isClopen' := by
    have hS : IsClopen (closedPointsComponentsHomeomorph (X := X) ''
        (S : Set (closedPoints X))) :=
      ⟨(closedPointsComponentsHomeomorph (X := X)).isClosedMap _ S.2.isClosed,
        (closedPointsComponentsHomeomorph (X := X)).isOpenMap _ S.2.isOpen⟩
    exact hS.preimage ConnectedComponents.continuous_coe

/-- A closed point lies in the lift of a clopen set of closed points exactly when it lies in
that set. -/
theorem mem_closedPointsClopenLift (S : Clopens (closedPoints X)) (c : closedPoints X) :
    (c : X) ∈ closedPointsClopenLift S ↔ c ∈ S := by
  change ConnectedComponents.mk (c : X) ∈
    closedPointsComponentsHomeomorph (X := X) '' (S : Set (closedPoints X)) ↔ c ∈ S
  rw [Set.mem_image]
  refine ⟨?_, fun hc => ⟨c, hc, rfl⟩⟩
  rintro ⟨d, hd, hdc⟩
  obtain rfl : d = c := closedPointsComponentsHomeomorph.injective (by simpa using hdc)
  exact hd

/-- A point of a w-local space lies in the lift of a clopen set of closed points exactly when
one of its closed specializations lies in that set. -/
theorem mem_closedPointsClopenLift_iff_specialization (S : Clopens (closedPoints X)) (x : X) :
    x ∈ closedPointsClopenLift S ↔ ∃ c : closedPoints X, x ⤳ c.1 ∧ c ∈ S := by
  obtain ⟨c, ⟨hc, hxc⟩, huniq⟩ := WLocalSpace.existsUnique_closedPoint_specializes x
  change ConnectedComponents.mk x ∈
    closedPointsComponentsHomeomorph (X := X) '' (S : Set (closedPoints X)) ↔ _
  rw [connectedComponents_eq_of_specializes hxc]
  constructor
  · intro hx
    obtain ⟨d, hd, hdx⟩ := Set.mem_image _ _ _ |>.mp hx
    have hdc : d = ⟨c, hc⟩ := closedPointsComponentsHomeomorph.injective (by simpa using hdx)
    exact ⟨⟨c, hc⟩, hxc, by simpa [hdc] using hd⟩
  · rintro ⟨d, hxd, hd⟩
    have hdc : d = ⟨c, hc⟩ := Subtype.ext (huniq d.1 ⟨d.2, hxd⟩)
    exact Set.mem_image _ _ _ |>.mpr ⟨⟨c, hc⟩, hdc ▸ hd, rfl⟩

end ClopenLift

/-! ### Vanishing patterns of a finite subset of a ring -/

section Pattern

variable {A : Type*} [CommRing A]

/-- The subsets of a finite subset of a ring form a finite type. -/
instance finite_subtype_subset_finset (E : Finset A) : Finite {E' : Finset A // E' ⊆ E} :=
  Finite.of_injective
    (fun i => (⟨i.val, Finset.mem_powerset.mpr i.property⟩ : {s // s ∈ E.powerset}))
    (fun _ _ h => Subtype.ext (congrArg (fun k : {s // s ∈ E.powerset} => k.val) h))

/-- The vanishing patterns of a finite subset of a ring form a finite type, chosen
noncomputably. -/
@[instance_reducible]
def patternIndexFintype (E : Finset A) : Fintype {E' : Finset A // E' ⊆ E} :=
  Fintype.ofFinite _

/-- A prime lies in the stratum of the vanishing pattern `i ⊆ E` exactly when the elements of
`i` avoid it and the remaining elements of `E` lie in it. -/
theorem mem_stratum_iff_vanishingPattern (E : Finset A)
    (i : {E' : Finset A // E' ⊆ E}) (q : PrimeSpectrum A) :
    q ∈ locallyClosedPoints (stratumIdeal E i) (stratumOpenElement i.val) ↔
      (∀ a ∈ i.val, a ∉ q.asIdeal) ∧ ∀ a ∈ ((E : Set A) \ (i.val : Set A)), a ∈ q.asIdeal := by
  classical
  change Ideal.span (↑(E \ i.val) : Set A) ≤ q.asIdeal ∧ i.val.prod id ∉ q.asIdeal ↔ _
  constructor
  · rintro ⟨hspan, hprod⟩
    rw [Ideal.IsPrime.prod_mem_iff] at hprod
    rw [Ideal.span_le] at hspan
    exact ⟨by simpa using hprod, fun a ha => hspan (by simpa [Finset.coe_sdiff] using ha)⟩
  · rintro ⟨hnonzero, hzero⟩
    refine ⟨Ideal.span_le.2 fun a ha => hzero a (by simpa [Finset.coe_sdiff] using ha), ?_⟩
    rw [Ideal.IsPrime.prod_mem_iff]
    simpa using hnonzero

/-- An element required not to vanish on a stratum becomes a unit in the stratum's coordinate
ring, hence in its localization. -/
theorem stratumLocalization_algebraMap_isUnit (E : Finset A)
    (i : {E' : Finset A // E' ⊆ E}) (a : A) (ha : a ∈ i.val) :
    IsUnit (algebraMap A (localizationRing (stratumIdeal E i) (stratumOpenElement i.val)) a) := by
  have hdiv : Ideal.Quotient.mk (stratumIdeal E i) a ∣
      Ideal.Quotient.mk (stratumIdeal E i) (stratumOpenElement i.val) := by
    simpa [stratumOpenElement] using
      Finset.dvd_prod_of_mem (fun x : A => Ideal.Quotient.mk (stratumIdeal E i) x) ha
  have hcoord : IsUnit (locallyClosedCoordinateMap (stratumIdeal E i)
      (stratumOpenElement i.val) a) :=
    IsLocalization.Away.isUnit_of_dvd
      (x := Ideal.Quotient.mk (stratumIdeal E i) (stratumOpenElement i.val)) hdiv
  exact IsLocalization.map_units _
    (⟨a, hcoord⟩ : localizationSubmonoid (stratumIdeal E i) (stratumOpenElement i.val))

/-- An element invertible on a stratum avoids every prime of that stratum. -/
theorem localizationSubmonoid_avoids_stratum (I : Ideal A) (f s : A)
    (hs : s ∈ localizationSubmonoid I f) (q : PrimeSpectrum A)
    (hq : q ∈ locallyClosedPoints I f) : s ∉ q.asIdeal := by
  have : q.asIdeal.IsPrime := q.2
  set k := q.asIdeal.ResidueField
  let qbar : A ⧸ I →+* k := Ideal.Quotient.lift I (algebraMap A k)
    (fun x hx => Ideal.algebraMap_residueField_eq_zero.2 (hq.1 hx))
  have hqbar (x : A) : qbar (Ideal.Quotient.mk I x) = algebraMap A k x := by simp [qbar]
  have hf : IsUnit (qbar (Ideal.Quotient.mk I f)) := by
    rw [hqbar]
    exact isUnit_iff_ne_zero.mpr fun hz =>
      hq.2 (Ideal.algebraMap_residueField_eq_zero.mp hz)
  let ψ : locallyClosedCoordinateRing I f →+* k :=
    IsLocalization.Away.lift (x := Ideal.Quotient.mk I f) (g := qbar) hf
  have hcomp : ψ.comp (locallyClosedCoordinateMap I f) = qbar.comp (Ideal.Quotient.mk I) := by
    ext a
    simp [ψ, qbar, locallyClosedCoordinateMap]
  have hu : IsUnit (qbar (Ideal.Quotient.mk I s)) := by
    have h := hs.map ψ
    change IsUnit ((ψ.comp (locallyClosedCoordinateMap I f)) s) at h
    rwa [hcomp] at h
  exact fun hmem => hu.ne_zero ((hqbar s).trans (Ideal.algebraMap_residueField_eq_zero.2 hmem))

/-- Every prime of `A` lies in the stratum of exactly one vanishing pattern of `E`. -/
theorem existsUnique_stratum_for_prime (E : Finset A) (q : PrimeSpectrum A) :
    ∃! i : {E' : Finset A // E' ⊆ E},
      q ∈ locallyClosedPoints (stratumIdeal E i) (stratumOpenElement i.val) := by
  classical
  let i₀ : {E' : Finset A // E' ⊆ E} :=
    ⟨E.filter fun a => a ∉ q.asIdeal, Finset.filter_subset _ _⟩
  have hP : q ∈ locallyClosedPoints (stratumIdeal E i₀) (stratumOpenElement i₀.val) := by
    rw [mem_stratum_iff_vanishingPattern]
    refine ⟨fun a ha => (Finset.mem_filter.mp ha).2, fun a ha => ?_⟩
    by_contra hq'
    exact ha.2 (Finset.mem_filter.mpr ⟨ha.1, hq'⟩)
  refine ⟨i₀, hP, fun j hj => ?_⟩
  have hi := (mem_stratum_iff_vanishingPattern E i₀ q).mp hP
  have hj' := (mem_stratum_iff_vanishingPattern E j q).mp hj
  refine Subtype.ext (Finset.ext fun a => ?_)
  by_cases haE : a ∈ E
  · constructor
    · intro haj
      by_contra hai
      exact hj'.1 a haj (hi.2 a ((Set.mem_sdiff a).mpr ⟨by simpa using haE, by simpa using hai⟩))
    · intro hai
      by_contra haj
      exact hi.1 a hai (hj'.2 a ((Set.mem_sdiff a).mpr ⟨by simpa using haE, by simpa using haj⟩))
  · exact ⟨fun haj => (haE (j.property haj)).elim, fun hai => (haE (i₀.property hai)).elim⟩

/-- The locus of primes of `B` whose contraction to `A` lies in a given stratum is a
constructible subset of `Spec B`. -/
theorem isConstructible_stratum_preimage {B : Type*} [CommRing B] (f : A →+* B)
    (E : Finset A) (i : {E' : Finset A // E' ⊆ E}) :
    Topology.IsConstructible
      {q : PrimeSpectrum B | PrimeSpectrum.comap f q ∈
        locallyClosedPoints (stratumIdeal E i) (stratumOpenElement i.val)} := by
  classical
  set V : A → Set (PrimeSpectrum B) := fun a => PrimeSpectrum.basicOpen (f a) with hV
  have hVc (a : A) : Topology.IsConstructible (V a) :=
    PrimeSpectrum.isRetrocompact_basicOpen.isConstructible PrimeSpectrum.isOpen_basicOpen
  have heq : {q : PrimeSpectrum B | PrimeSpectrum.comap f q ∈
      locallyClosedPoints (stratumIdeal E i) (stratumOpenElement i.val)} =
      (⋂ a ∈ i.val, V a) ∩ ⋂ a ∈ (E \ i.val), (V a)ᶜ := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, hV]
    rw [mem_stratum_iff_vanishingPattern]
    simp [PrimeSpectrum.comap]
  rw [heq]
  exact (Topology.IsConstructible.biInter i.val.finite_toSet fun a _ => hVc a).inter
    (Topology.IsConstructible.biInter (E \ i.val).finite_toSet fun a _ => (hVc a).compl)

end Pattern

/-! ### Stratum clopens and stratum idempotents of a w-local spectrum -/

section StratumClopen

variable {A B : Type*} [CommRing A] [CommRing B] [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)

/-- The closed points of `Spec B` lying over a given stratum of `E` form a clopen set. -/
theorem stratumClosedPoints_isClopen (E : Finset A) (i : {E' : Finset A // E' ⊆ E}) :
    IsClopen {c : closedPoints (PrimeSpectrum B) |
      PrimeSpectrum.comap f c.1 ∈
        locallyClosedPoints (stratumIdeal E i) (stratumOpenElement i.val)} :=
  closedPoints_preimage_isClopen_of_isConstructible (isConstructible_stratum_preimage f E i)

/-- The clopen set of closed points of `Spec B` lying over a given stratum of `E`. -/
def stratumClosedPointsClopen (E : Finset A) (i : {E' : Finset A // E' ⊆ E}) :
    Clopens (closedPoints (PrimeSpectrum B)) :=
  ⟨{c | PrimeSpectrum.comap f c.1 ∈
      locallyClosedPoints (stratumIdeal E i) (stratumOpenElement i.val)},
    stratumClosedPoints_isClopen f E i⟩

/-- Every closed point of `Spec B` lies over exactly one stratum of `E`. -/
theorem existsUnique_stratum_closedPoint (E : Finset A) (c : closedPoints (PrimeSpectrum B)) :
    ∃! i : {E' : Finset A // E' ⊆ E}, c ∈ stratumClosedPointsClopen f E i := by
  simpa [stratumClosedPointsClopen] using existsUnique_stratum_for_prime (A := A) E
    (PrimeSpectrum.comap f c.1)

/-- The strata cover the closed points of `Spec B`. -/
theorem stratumClosedPoints_cover (E : Finset A) (c : closedPoints (PrimeSpectrum B)) :
    ∃ i : {E' : Finset A // E' ⊆ E}, c ∈ stratumClosedPointsClopen f E i :=
  (existsUnique_stratum_closedPoint f E c).exists

/-- The clopen subset of `Spec B` cut out by a vanishing pattern `i ⊆ E`: the set of points
whose closed specialization lies over the stratum of `i`. -/
def stratumClopen (E : Finset A) (i : {E' : Finset A // E' ⊆ E}) : Clopens (PrimeSpectrum B) :=
  closedPointsClopenLift (stratumClosedPointsClopen f E i)

/-- A point of `Spec B` lies in a stratum clopen exactly when one of its closed specializations
lies over the corresponding stratum. -/
theorem mem_stratumClopen_iff_closedSpecialization (E : Finset A)
    (i : {E' : Finset A // E' ⊆ E}) (x : PrimeSpectrum B) :
    x ∈ stratumClopen f E i ↔
      ∃ c : closedPoints (PrimeSpectrum B), x ⤳ c.1 ∧ c ∈ stratumClosedPointsClopen f E i :=
  mem_closedPointsClopenLift_iff_specialization _ x

/-- The idempotent of `B` cutting out the stratum clopen of a vanishing pattern `i ⊆ E`. -/
def stratumIdempotent (E : Finset A) (i : {E' : Finset A // E' ⊆ E}) : B :=
  Classical.choose
    (PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (stratumClopen f E i).2)

/-- The stratum idempotent is idempotent. -/
theorem stratumIdempotent_isIdempotent (E : Finset A) (i : {E' : Finset A // E' ⊆ E}) :
    IsIdempotentElem (stratumIdempotent f E i) :=
  (Classical.choose_spec
    (PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (stratumClopen f E i).2)).1

/-- The stratum idempotent cuts out the stratum clopen. -/
theorem basicOpen_stratumIdempotent (E : Finset A) (i : {E' : Finset A // E' ⊆ E}) :
    (stratumClopen f E i : Set (PrimeSpectrum B)) =
      (PrimeSpectrum.basicOpen (stratumIdempotent f E i)).carrier :=
  (Classical.choose_spec
    (PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (stratumClopen f E i).2)).2

/-- A prime lies in a stratum clopen exactly when the stratum idempotent is not in it. -/
private theorem mem_stratumClopen_iff_idempotent_notMem (E : Finset A)
    (i : {E' : Finset A // E' ⊆ E}) (p : PrimeSpectrum B) :
    p ∈ stratumClopen f E i ↔ stratumIdempotent f E i ∉ p.asIdeal :=
  (Set.ext_iff.1 (basicOpen_stratumIdempotent f E i) p).trans (PrimeSpectrum.mem_basicOpen _ _)

/-- Refining a vanishing pattern to a smaller finite set enlarges its stratum clopen. -/
theorem stratumClopen_subset_restrictStratum (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂)
    (i : {E' : Finset A // E' ⊆ E₂}) :
    (stratumClopen f E₂ i : Set (PrimeSpectrum B)) ⊆
      stratumClopen f E₁ (restrictStratum E₁ E₂ h i) := by
  intro x hx
  obtain ⟨c, hxc, hc⟩ := (mem_closedPointsClopenLift_iff_specialization _ x).mp hx
  refine (mem_closedPointsClopenLift_iff_specialization _ x).2 ⟨c, hxc, ?_⟩
  simpa [stratumClosedPointsClopen] using
    locallyClosedPoints_restrictStratum E₁ E₂ h i (PrimeSpectrum.comap f c.1)
      (by simpa [stratumClosedPointsClopen] using hc)

/-- An inclusion of stratum clopens multiplies the corresponding idempotents to the smaller
one. -/
theorem stratumIdempotent_mul_eq_of_clopen_subset (E₁ E₂ : Finset A)
    (i₁ : {E' : Finset A // E' ⊆ E₁}) (i₂ : {E' : Finset A // E' ⊆ E₂})
    (h : (stratumClopen f E₂ i₂ : Set (PrimeSpectrum B)) ⊆ stratumClopen f E₁ i₁) :
    stratumIdempotent f E₂ i₂ * stratumIdempotent f E₁ i₁ = stratumIdempotent f E₂ i₂ := by
  set e₁ := stratumIdempotent f E₁ i₁
  set e₂ := stratumIdempotent f E₂ i₂
  have hbasic : PrimeSpectrum.basicOpen (e₂ * e₁) = PrimeSpectrum.basicOpen e₂ := by
    refine SetLike.coe_injective ?_
    ext p
    change (e₂ * e₁ ∉ p.asIdeal) ↔ e₂ ∉ p.asIdeal
    rw [p.2.mul_mem_iff_mem_or_mem]
    simp only [not_or]
    exact ⟨fun hp => hp.1, fun hp => ⟨hp, (mem_stratumClopen_iff_idempotent_notMem f E₁ i₁ p).1
      (h ((mem_stratumClopen_iff_idempotent_notMem f E₂ i₂ p).2 hp))⟩⟩
  exact PrimeSpectrum.basicOpen_injOn_isIdempotentElem
    ((stratumIdempotent_isIdempotent f E₂ i₂).mul (stratumIdempotent_isIdempotent f E₁ i₁))
    (stratumIdempotent_isIdempotent f E₂ i₂) hbasic

/-- The stratum clopens of a finite subset `E ⊆ A` partition `Spec B`. -/
theorem stratumClopen_partition (E : Finset A) :
    (∀ x : PrimeSpectrum B, ∃ i : {E' : Finset A // E' ⊆ E}, x ∈ stratumClopen f E i) ∧
      Pairwise fun i j : {E' : Finset A // E' ⊆ E} =>
        Disjoint (stratumClopen f E i : Set (PrimeSpectrum B))
          (stratumClopen f E j : Set (PrimeSpectrum B)) := by
  refine ⟨fun x => ?_, fun i j hij => ?_⟩
  · obtain ⟨c, ⟨hc, hxc⟩, _⟩ :=
      WLocalSpace.existsUnique_closedPoint_specializes x
    obtain ⟨i, hi⟩ := stratumClosedPoints_cover f E ⟨c, hc⟩
    exact ⟨i, (mem_stratumClopen_iff_closedSpecialization f E i x).2 ⟨⟨c, hc⟩, hxc, hi⟩⟩
  · refine Set.disjoint_left.2 fun x hxi hxj => ?_
    obtain ⟨ci, hxc_i, hci⟩ := (mem_stratumClopen_iff_closedSpecialization f E i x).mp hxi
    obtain ⟨cj, hxc_j, hcj⟩ := (mem_stratumClopen_iff_closedSpecialization f E j x).mp hxj
    obtain rfl : ci = cj :=
      Subtype.ext (WLocalSpace.eq_of_specializes
        (mem_closedPoints_iff.mp ci.property) (mem_closedPoints_iff.mp cj.property)
        hxc_i hxc_j)
    obtain ⟨k, _, hku⟩ := existsUnique_stratum_closedPoint f E ci
    exact hij ((hku i hci).trans (hku j hcj).symm)

/-- The stratum idempotents of a finite subset `E ⊆ A` are orthogonal idempotents of `B`. -/
private theorem stratumIdempotents_orthogonal (E : Finset A) :
    OrthogonalIdempotents (stratumIdempotent f E) := by
  refine ⟨stratumIdempotent_isIdempotent f E, fun i j hij => ?_⟩
  have hdisSet : Disjoint (PrimeSpectrum.basicOpen (stratumIdempotent f E i)).carrier
      (PrimeSpectrum.basicOpen (stratumIdempotent f E j)).carrier := by
    rw [← basicOpen_stratumIdempotent f E i, ← basicOpen_stratumIdempotent f E j]
    exact (stratumClopen_partition f E).2 hij
  refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem
    ((stratumIdempotent_isIdempotent f E i).mul (stratumIdempotent_isIdempotent f E j))
    IsIdempotentElem.zero ?_
  rw [PrimeSpectrum.basicOpen_mul, disjoint_iff.mp (Opens.coe_disjoint.mp hdisSet),
    PrimeSpectrum.basicOpen_zero]

/-- The stratum idempotents of a finite subset `E ⊆ A` form a complete set of orthogonal
idempotents of `B`. -/
theorem stratumIdempotents_complete (E : Finset A) [Fintype {E' : Finset A // E' ⊆ E}] :
    CompleteOrthogonalIdempotents (stratumIdempotent f E) := by
  classical
  have hortho := stratumIdempotents_orthogonal f E
  refine ⟨hortho, ?_⟩
  have hsumIdem : IsIdempotentElem (∑ i, stratumIdempotent f E i) := by
    simpa using hortho.isIdempotentElem_sum (s := Finset.univ)
  refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem hsumIdem IsIdempotentElem.one ?_
  refine SetLike.ext fun p => ⟨fun _ => by simp, fun _ => ?_⟩
  obtain ⟨i, hi⟩ := (stratumClopen_partition f E).1 p
  intro hsum_mem
  refine (mem_stratumClopen_iff_idempotent_notMem f E i p).1 hi ?_
  rw [← hortho.mul_sum_of_mem (Finset.mem_univ i)]
  exact p.asIdeal.mul_mem_left _ hsum_mem

/-- The decomposition of `B` as the product of its quotients by the stratum idempotents of a
finite subset `E ⊆ A`. -/
def quotientProductEquiv (E : Finset A) :
    B ≃+* ∀ i : {E' : Finset A // E' ⊆ E}, B ⧸ Ideal.span {1 - stratumIdempotent f E i} := by
  letI := patternIndexFintype E
  exact RingEquiv.ofBijective
    (RingHom.pi fun i => Ideal.Quotient.mk (Ideal.span {1 - stratumIdempotent f E i}))
    (stratumIdempotents_complete f E).bijective_pi

/-- The coordinates of a preimage under `quotientProductEquiv` are the given ones. -/
theorem quotientProductEquiv_apply_symm (E : Finset A)
    (y : ∀ i : {E' : Finset A // E' ⊆ E}, B ⧸ Ideal.span {1 - stratumIdempotent f E i})
    (i : {E' : Finset A // E' ⊆ E}) :
    Ideal.Quotient.mk (Ideal.span {1 - stratumIdempotent f E i})
        ((quotientProductEquiv f E).symm y) = y i := by
  let := patternIndexFintype E
  have heq := (quotientProductEquiv f E).apply_symm_apply y
  change (RingHom.pi (fun i =>
    Ideal.Quotient.mk (Ideal.span {1 - stratumIdempotent f E i}))
      ((quotientProductEquiv f E).symm y)) = y at heq
  exact congrFun heq i

/-- The stratum idempotent is the preimage under `quotientProductEquiv` of the `i`-th
standard basis vector. -/
theorem quotientProductEquiv_symm_single_one (E : Finset A) (i : {E' : Finset A // E' ⊆ E})
    [DecidableEq {E' : Finset A // E' ⊆ E}] :
    (quotientProductEquiv f E).symm
        (Pi.single i (1 : B ⧸ Ideal.span {1 - stratumIdempotent f E i})) =
      stratumIdempotent f E i := by
  classical
  let := patternIndexFintype E
  set e := quotientProductEquiv f E
  have hone (j : {E' : Finset A // E' ⊆ E}) :
      Ideal.Quotient.mk (Ideal.span {1 - stratumIdempotent f E j})
        (stratumIdempotent f E j) = 1 := by
    have hz : Ideal.Quotient.mk (Ideal.span {1 - stratumIdempotent f E j})
        (1 - stratumIdempotent f E j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))
    rw [map_sub, map_one, sub_eq_zero] at hz
    exact hz.symm
  have hcoord (j : {E' : Finset A // E' ⊆ E}) :
      Ideal.Quotient.mk (Ideal.span {1 - stratumIdempotent f E j})
        (stratumIdempotent f E i) = if j = i then 1 else 0 := by
    by_cases hji : j = i
    · subst j
      simpa using hone i
    · have hzero : Ideal.Quotient.mk (Ideal.span {1 - stratumIdempotent f E j})
          (stratumIdempotent f E i) = 0 :=
        calc Ideal.Quotient.mk _ (stratumIdempotent f E i)
            = Ideal.Quotient.mk _ (stratumIdempotent f E i) *
                Ideal.Quotient.mk _ (stratumIdempotent f E j) := by rw [hone j, mul_one]
          _ = Ideal.Quotient.mk _ (stratumIdempotent f E i * stratumIdempotent f E j) :=
              (map_mul _ _ _).symm
          _ = 0 := by
              rw [(stratumIdempotents_complete f E).ortho fun h => hji h.symm, map_zero]
      simp [hzero, hji]
  refine e.injective ?_
  rw [e.apply_symm_apply]
  refine funext fun j => ?_
  change _ = Ideal.Quotient.mk _ (stratumIdempotent f E i)
  rw [hcoord j]
  by_cases hji : j = i
  · subst j; simp
  · simp [hji]

end StratumClopen

end AlgebraicGeometry.ProEtale

end
