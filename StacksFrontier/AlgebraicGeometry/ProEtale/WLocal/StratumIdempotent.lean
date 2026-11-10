module

public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ClosedPointsClopen
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationTransition
public import Mathlib.Data.Finset.SDiff
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Idempotents cutting out the vanishing strata of a w-local spectrum

Let `A → B` be a ring map and let `Spec B` be w-local. A finite subset `E ⊆ A` partitions
`Spec A` into the locally closed strata on which a prescribed subset of `E` vanishes, and
pulling these strata back along `Spec B → Spec A` partitions `Spec B` into constructible
subsets. Because `Spec B` is w-local, each such piece is clopen, hence cut out by an idempotent
of `B`, and these idempotents form a complete orthogonal family. Consequently `B` decomposes as
the product of the quotients `B / (1 - e)`, one for each vanishing pattern.

## Main definitions

* `AlgebraicGeometry.ProEtale.stratumQuotientPiEquiv`: the resulting product decomposition of
  `B`.

The clopen subset `AlgebraicGeometry.ProEtale.stratumClopen` of `Spec B` lying over a vanishing
stratum of `Spec A`, the idempotent `AlgebraicGeometry.ProEtale.stratumIdempotent` of `B`
cutting it out, and the fact `AlgebraicGeometry.ProEtale.stratumClopen_partition` that the
pieces partition `Spec B` are in
`StacksFrontier.AlgebraicGeometry.ProEtale.Limits.ClopenLift`, re-exported here.

## Main results

* `AlgebraicGeometry.ProEtale.existsUnique_mem_stratum`: every point of `Spec B` lies over
  exactly one vanishing stratum of `Spec A`.
* `AlgebraicGeometry.ProEtale.completeOrthogonalIdempotents_stratumIdempotent`: the idempotents
  cutting them out are a complete orthogonal family.

## Implementation notes

A vanishing stratum is indexed by a subset `E' ⊆ E`, the elements of `E` that do *not* vanish on
it, and is the locally closed subset `D(∏ E') ∩ V(E \ E')`. Its preimage in `Spec B` is a finite
intersection of basic opens and their complements, hence constructible, and a constructible
subset of a w-local space is clopen on the closed points. The clopen subset of `Spec B` itself is
recovered from its trace on the closed points, using that every point has a unique closed
specialization.

The idempotent is extracted from the clopen subset by `Classical.choose`, and all of its
properties are read off from the characterizing equation between its basic open and the clopen
subset, using that `PrimeSpectrum.basicOpen` is injective on idempotents.

## References

* [Stacks Project, Tag 096V](https://stacks.math.columbia.edu/tag/096V)
* [Stacks Project, Tag 096Z](https://stacks.math.columbia.edu/tag/096Z)
* [Stacks Project, Tag 0977](https://stacks.math.columbia.edu/tag/0977)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

open TopologicalSpace

/-- A prime lies on the stratum of `E` indexed by `i` exactly when the elements of `i` avoid it
and the remaining elements of `E` belong to it. -/
theorem mem_locallyClosedPoints_stratum_iff
    {A : Type*} [CommRing A] (E : Finset A)
    (i : {E' : Finset A // E' ⊆ E}) (q : PrimeSpectrum A) :
    q ∈ locallyClosedPoints (stratumIdeal E i)
        (stratumOpenElement i.val) ↔
      (∀ a ∈ i.val, a ∉ q.asIdeal) ∧
        ∀ a ∈ ((E : Set A) \ (i.val : Set A)), a ∈ q.asIdeal := by
  classical
  change Ideal.span (↑(E \ i.val) : Set A) ≤ q.asIdeal ∧
      i.val.prod id ∉ q.asIdeal ↔ _
  constructor
  · rintro ⟨hspan, hprod⟩
    refine ⟨?_, ?_⟩
    · rw [Ideal.IsPrime.prod_mem_iff] at hprod
      simpa using hprod
    · rw [Ideal.span_le] at hspan
      intro a ha
      have ha' : a ∈ (↑(E \ i.val) : Set A) := by
        simpa [Finset.coe_sdiff] using ha
      exact hspan ha'
  · rintro ⟨hnonzero, hzero⟩
    refine ⟨?_, ?_⟩
    · rw [Ideal.span_le]
      intro a ha
      have ha' : a ∈ ((E : Set A) \ (i.val : Set A)) := by
        simpa [Finset.coe_sdiff] using ha
      exact hzero a ha'
    · rw [Ideal.IsPrime.prod_mem_iff]
      simpa using hnonzero

/-- An element of `E` not required to vanish on the stratum indexed by `i` becomes a unit in the
localization attached to that stratum. -/
theorem isUnit_algebraMap_stratumLocalization
    {A : Type*} [CommRing A] (E : Finset A)
    (i : {E' : Finset A // E' ⊆ E}) (a : A) (ha : a ∈ i.val) :
    IsUnit (algebraMap A
      (localizationRing (stratumIdeal E i)
        (stratumOpenElement i.val)) a) := by
  let I := stratumIdeal E i
  let f := stratumOpenElement i.val
  let L := locallyClosedCoordinateRing I f
  have : IsLocalization.Away (Ideal.Quotient.mk I f) L := inferInstance
  have hdiv : Ideal.Quotient.mk I a ∣ Ideal.Quotient.mk I f := by
    simpa [f, stratumOpenElement] using
      (Finset.dvd_prod_of_mem (fun x : A => Ideal.Quotient.mk I x) ha)
  have hcoord : IsUnit (locallyClosedCoordinateMap I f a) := by
    change IsUnit (algebraMap (A ⧸ I) L (Ideal.Quotient.mk I a))
    exact IsLocalization.Away.isUnit_of_dvd
      (R := A ⧸ I) (S := L) (x := Ideal.Quotient.mk I f) hdiv
  have hmem : a ∈ localizationSubmonoid I f :=
    (IsUnit.mem_submonoid_iff _).mpr hcoord
  exact IsLocalization.map_units _ ⟨a, hmem⟩

/-- The preimage in `Spec B` of a vanishing stratum of `Spec A` is constructible. -/
theorem isConstructible_comap_preimage_stratum
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (E : Finset A) (i : {E' : Finset A // E' ⊆ E}) :
    Topology.IsConstructible
      {q : PrimeSpectrum B | PrimeSpectrum.comap f q ∈
        locallyClosedPoints (stratumIdeal E i)
          (stratumOpenElement i.val)} := by
  classical
  let V (a : A) : Set (PrimeSpectrum B) := PrimeSpectrum.basicOpen (f a)
  have hV (a : A) : Topology.IsConstructible (V a) :=
    (PrimeSpectrum.isRetrocompact_basicOpen).isConstructible PrimeSpectrum.isOpen_basicOpen
  have hnon : Topology.IsConstructible (⋂ a ∈ i.val, V a) :=
    Topology.IsConstructible.biInter i.val.finite_toSet (fun a ha => hV a)
  have hzero : Topology.IsConstructible (⋂ a ∈ (E \ i.val), (V a)ᶜ) :=
    Topology.IsConstructible.biInter (E \ i.val).finite_toSet
      (fun a ha => (hV a).compl)
  have heq : {q : PrimeSpectrum B | PrimeSpectrum.comap f q ∈
      locallyClosedPoints (stratumIdeal E i)
        (stratumOpenElement i.val)} =
      (⋂ a ∈ i.val, V a) ∩ ⋂ a ∈ (E \ i.val), (V a)ᶜ := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_compl_iff, V]
    rw [mem_locallyClosedPoints_stratum_iff]
    simp [PrimeSpectrum.comap]
  rw [heq]
  exact hnon.inter hzero

/-- A prime of `B` contracts to a point lying on exactly one of the vanishing strata of `E`. -/
theorem existsUnique_mem_stratum
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (E : Finset A) (q : PrimeSpectrum B) :
    ∃! i : {E' : Finset A // E' ⊆ E},
      PrimeSpectrum.comap f q ∈
        locallyClosedPoints (stratumIdeal E i)
          (stratumOpenElement i.val) := by
  classical
  let qA := PrimeSpectrum.comap f q
  let P := E.filter fun a => a ∉ qA.asIdeal
  let i₀ : {E' : Finset A // E' ⊆ E} := ⟨P, Finset.filter_subset _ _⟩
  have hP : qA ∈ locallyClosedPoints
      (stratumIdeal E i₀)
      (stratumOpenElement P) := by
    rw [mem_locallyClosedPoints_stratum_iff]
    constructor
    · intro a ha
      exact (Finset.mem_filter.mp ha).2
    · intro a ha
      rcases (Set.mem_sdiff a).mp ha with ⟨haE, haP⟩
      have haE' : a ∈ E := by simpa using haE
      have haP' : a ∉ P := by simpa using haP
      by_contra hq
      exact haP' (Finset.mem_filter.mpr ⟨haE', hq⟩)
  refine ⟨i₀, hP, ?_⟩
  intro j hj
  apply Subtype.ext
  apply Finset.ext
  intro a
  have hi := (mem_locallyClosedPoints_stratum_iff E i₀ qA).mp hP
  have hj' := (mem_locallyClosedPoints_stratum_iff E j qA).mp hj
  by_cases haE : a ∈ E
  · constructor
    · intro hai
      by_contra haj
      have hdiff : a ∈ ((E : Set A) \ (i₀.val : Set A)) := by
        simp [haE, haj]
      exact hj'.1 a hai (hi.2 a hdiff)
    · intro haj
      by_contra hai
      have hdiff : a ∈ ((E : Set A) \ (j.val : Set A)) := by
        simp [haE, hai]
      exact hi.1 a haj (hj'.2 a hdiff)
  · constructor
    · intro hai
      exact (haE (j.property hai)).elim
    · intro haj
      exact (haE (i₀.property haj)).elim

/-- An element inverted on `D(f) ∩ V(I)` avoids every prime of that locally closed subset. -/
lemma localizationSubmonoid_notMem_of_mem_locallyClosedPoints
    {A : Type*} [CommRing A] (I : Ideal A) (f s : A)
    (hs : s ∈ localizationSubmonoid I f)
    (q : PrimeSpectrum A)
    (hq : q ∈ locallyClosedPoints I f) : s ∉ q.asIdeal := by
  classical
  have : q.asIdeal.IsPrime := q.2
  let k := q.asIdeal.ResidueField
  let qbar : A ⧸ I →+* k := Ideal.Quotient.lift I (algebraMap A k) (by
    intro x hx
    apply (Ideal.algebraMap_residueField_eq_zero).2
    exact hq.1 hx)
  have hf : IsUnit (qbar (Ideal.Quotient.mk I f)) := by
    rw [show qbar (Ideal.Quotient.mk I f) = algebraMap A k f by
      simp [qbar]]
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact hq.2 (Ideal.algebraMap_residueField_eq_zero.mp hz)
  let ψ : locallyClosedCoordinateRing I f →+* k :=
    IsLocalization.Away.lift (x := Ideal.Quotient.mk I f) (g := qbar) hf
  have hcomp : ψ.comp (locallyClosedCoordinateMap I f) =
      qbar.comp (Ideal.Quotient.mk I) := by
    ext a
    simp [ψ, qbar, locallyClosedCoordinateMap]
  have hu : IsUnit (qbar (Ideal.Quotient.mk I s)) := by
    have h := hs.map ψ
    change IsUnit ((ψ.comp (locallyClosedCoordinateMap I f)) s) at h
    rw [hcomp] at h
    exact h
  intro hmem
  apply hu.ne_zero
  rw [show qbar (Ideal.Quotient.mk I s) = algebraMap A k s by
    simp [qbar]]
  exact (Ideal.algebraMap_residueField_eq_zero).2 hmem

/-- For a ring map `f : A →+* B` with `Spec B` w-local, the set of closed points of `Spec B`
lying over the stratum of `Spec A` indexed by `i` is clopen in the space of closed points. -/
lemma isClopen_stratumClosedPoints
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) (i : {E' : Finset A // E' ⊆ E})
    :
    IsClopen {c : closedPoints (PrimeSpectrum B) |
      PrimeSpectrum.comap f c.1 ∈
        locallyClosedPoints (stratumIdeal E i)
          (stratumOpenElement i.val)} := by
  exact isClopen_preimage_closedPoints_of_isConstructible
    (X := PrimeSpectrum B)
    (s := {q : PrimeSpectrum B | PrimeSpectrum.comap f q ∈
      locallyClosedPoints (stratumIdeal E i)
        (stratumOpenElement i.val)})
    (isConstructible_comap_preimage_stratum f E i)

/-- A point of `Spec B` lies in the clopen piece indexed by `i` exactly when its closed
specialization lies over the stratum indexed by `i`. -/
theorem mem_stratumClopen_iff
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) (i : {E' : Finset A // E' ⊆ E})
    (x : PrimeSpectrum B) :
    x ∈ stratumClopen f E i ↔
      ∃ c : closedPoints (PrimeSpectrum B),
        Specializes x c.1 ∧ c ∈ stratumClosedPointsClopen f E i :=
  mem_stratumClopen_iff_closedSpecialization f E i x

/-- The element cutting out a clopen piece of `Spec B` is idempotent. -/
theorem stratumIdempotent_isIdempotentElem
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) (i : {E' : Finset A // E' ⊆ E}) :
    IsIdempotentElem (stratumIdempotent f E i) :=
  stratumIdempotent_isIdempotent f E i

/-- The clopen piece indexed by `i` is the basic open of its idempotent. -/
theorem coe_stratumClopen_eq_basicOpen
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) (i : {E' : Finset A // E' ⊆ E}) :
    (stratumClopen f E i : Set (PrimeSpectrum B)) =
      (PrimeSpectrum.basicOpen (stratumIdempotent f E i)).carrier :=
  basicOpen_stratumIdempotent f E i

/-- The idempotents cutting out the clopen pieces of `Spec B` form a complete orthogonal family. -/
theorem completeOrthogonalIdempotents_stratumIdempotent
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) [Fintype {E' : Finset A // E' ⊆ E}] :
    CompleteOrthogonalIdempotents (stratumIdempotent f E) := by
  classical
  have hparts := stratumClopen_partition f E
  have hortho : OrthogonalIdempotents (stratumIdempotent f E) := by
    refine ⟨stratumIdempotent_isIdempotentElem f E, ?_⟩
    intro i j hij
    have hdis := hparts.2 hij
    have hdisSet : Disjoint
        (PrimeSpectrum.basicOpen (stratumIdempotent f E i)).carrier
        (PrimeSpectrum.basicOpen (stratumIdempotent f E j)).carrier := by
      rw [← coe_stratumClopen_eq_basicOpen f E i,
        ← coe_stratumClopen_eq_basicOpen f E j]
      exact hdis
    have hdisOpen : Disjoint
        (PrimeSpectrum.basicOpen (stratumIdempotent f E i))
        (PrimeSpectrum.basicOpen (stratumIdempotent f E j)) :=
      Opens.coe_disjoint.mp hdisSet
    have hbot : PrimeSpectrum.basicOpen (stratumIdempotent f E i) ⊓
        PrimeSpectrum.basicOpen (stratumIdempotent f E j) = ⊥ := by
      exact le_antisymm (disjoint_iff_inf_le.mp hdisOpen) bot_le
    have heq : PrimeSpectrum.basicOpen
        (stratumIdempotent f E i * stratumIdempotent f E j) =
        PrimeSpectrum.basicOpen (0 : B) := by
      rw [PrimeSpectrum.basicOpen_mul, hbot, PrimeSpectrum.basicOpen_zero]
    have hid : IsIdempotentElem
        (stratumIdempotent f E i * stratumIdempotent f E j) := by
      change (stratumIdempotent f E i * stratumIdempotent f E j) *
        (stratumIdempotent f E i * stratumIdempotent f E j) = _
      calc
        _ = stratumIdempotent f E i * stratumIdempotent f E i *
            (stratumIdempotent f E j * stratumIdempotent f E j) := by ring
        _ = stratumIdempotent f E i * stratumIdempotent f E j := by
          rw [(stratumIdempotent_isIdempotentElem f E i).eq,
            (stratumIdempotent_isIdempotentElem f E j).eq]
    exact PrimeSpectrum.basicOpen_injOn_isIdempotentElem hid
      IsIdempotentElem.zero heq
  have hsum : (∑ i, stratumIdempotent f E i) = 1 := by
    have hsumIdem : IsIdempotentElem (∑ i, stratumIdempotent f E i) := by
      simpa using hortho.isIdempotentElem_sum (s := Finset.univ)
    have hbasic : PrimeSpectrum.basicOpen (∑ i, stratumIdempotent f E i) =
        PrimeSpectrum.basicOpen (1 : B) := by
      apply SetLike.ext
      intro p
      constructor
      · intro _
        simp
      · intro _
        obtain ⟨i, hi⟩ := hparts.1 p
        have hnei : stratumIdempotent f E i ∉ p.asIdeal := by
          have hi' : p ∈ (PrimeSpectrum.basicOpen (stratumIdempotent f E i)).carrier := by
            rw [← coe_stratumClopen_eq_basicOpen f E i]
            exact hi
          exact (PrimeSpectrum.mem_basicOpen _ _).mp hi'
        intro hsum_mem
        have hmul : stratumIdempotent f E i *
            (∑ j, stratumIdempotent f E j) ∈ p.asIdeal :=
          p.asIdeal.mul_mem_left _ hsum_mem
        rw [hortho.mul_sum_of_mem (Finset.mem_univ i)] at hmul
        exact hnei hmul
    exact PrimeSpectrum.basicOpen_injOn_isIdempotentElem hsumIdem
      IsIdempotentElem.one hbasic
  exact ⟨hortho, hsum⟩

/-- The vanishing patterns of a finite subset of `A`, as a `Fintype`. -/
@[instance_reducible]
noncomputable def stratumIndexFintype
    {A : Type*} [CommRing A] (E : Finset A) :
    Fintype {E' : Finset A // E' ⊆ E} :=
  have : Finite {s : Set A // s ⊆ (E : Set A)} := E.finite_toSet.finite_subsets.to_subtype
  have : Finite {E' : Finset A // E' ⊆ E} :=
    Finite.of_injective
      (fun i => (⟨(i.1 : Set A), Finset.coe_subset.mpr i.2⟩ : {s : Set A // s ⊆ (E : Set A)}))
      (fun _ _ h => Subtype.ext (Finset.coe_injective (congrArg Subtype.val h)))
  Fintype.ofFinite _

/-- The decomposition of `B` as the product of the quotients attached to the vanishing strata
of `E`. -/
noncomputable def stratumQuotientPiEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B) (E : Finset A) :
    B ≃+* ∀ i : {E' : Finset A // E' ⊆ E},
      B ⧸ Ideal.span {1 - stratumIdempotent f E i} := by
  letI := stratumIndexFintype E
  exact RingEquiv.ofBijective
    (RingHom.pi fun i => Ideal.Quotient.mk (Ideal.span {1 - stratumIdempotent f E i}))
    (completeOrthogonalIdempotents_stratumIdempotent f E).bijective_pi

/-- Reading off a coordinate of the product decomposition of `B`. -/
theorem mk_stratumQuotientPiEquiv_symm
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) (y : ∀ i : {E' : Finset A // E' ⊆ E},
      B ⧸ Ideal.span {1 - stratumIdempotent f E i})
    (i : {E' : Finset A // E' ⊆ E}) :
    Ideal.Quotient.mk (Ideal.span {1 - stratumIdempotent f E i})
        ((stratumQuotientPiEquiv f E).symm y) = y i := by
  classical
  let _ := stratumIndexFintype E
  have heq := (stratumQuotientPiEquiv f E).apply_symm_apply y
  change (RingHom.pi (fun i =>
    Ideal.Quotient.mk (Ideal.span {1 - stratumIdempotent f E i}))
      ((stratumQuotientPiEquiv f E).symm y)) = y at heq
  exact congrFun heq i

/-- An element becomes `1` in the quotient by the ideal generated by `1 - e`. -/
private theorem mk_span_one_sub_eq_self {B : Type*} [CommRing B] (e : B) :
    Ideal.Quotient.mk (Ideal.span {1 - e}) e = 1 := by
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - e})), Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact neg_sub 1 e ▸ (Ideal.span {1 - e}).neg_mem (Ideal.mem_span_singleton_self _)

/-- The element of `B` with coordinate `1` at the stratum `i` and `0` elsewhere is the idempotent
cutting out the clopen piece indexed by `i`. -/
theorem stratumQuotientPiEquiv_symm_single_one
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) (i : {E' : Finset A // E' ⊆ E})
    [DecidableEq {E' : Finset A // E' ⊆ E}] :
    (stratumQuotientPiEquiv f E).symm (Pi.single i (1 : B ⧸
      Ideal.span {1 - stratumIdempotent f E i})) = stratumIdempotent f E i := by
  classical
  let _ := stratumIndexFintype E
  let e := stratumQuotientPiEquiv f E
  have hcomplete := completeOrthogonalIdempotents_stratumIdempotent f E
  have hcoord (j : {E' : Finset A // E' ⊆ E}) :
      Ideal.Quotient.mk (Ideal.span {1 - stratumIdempotent f E j})
        (stratumIdempotent f E i) = if j = i then 1 else 0 := by
    by_cases hji : j = i
    · subst j
      simp [mk_span_one_sub_eq_self]
    · have hji' : i ≠ j := fun h => hji h.symm
      have horth := hcomplete.ortho hji'
      simp only [hji, ↓reduceIte]
      calc
        Ideal.Quotient.mk _ (stratumIdempotent f E i) =
            Ideal.Quotient.mk _ (stratumIdempotent f E i) *
              Ideal.Quotient.mk _ (stratumIdempotent f E j) := by
          rw [mk_span_one_sub_eq_self, mul_one]
        _ = Ideal.Quotient.mk _
              (stratumIdempotent f E i * stratumIdempotent f E j) := (map_mul _ _ _).symm
        _ = 0 := by rw [horth]; simp
  have heval : e (stratumIdempotent f E i) = Pi.single i 1 := by
    ext j
    change Ideal.Quotient.mk _ (stratumIdempotent f E i) =
      ((Pi.single i (1 : B ⧸ Ideal.span {1 - stratumIdempotent f E i}) :
        ∀ j : {E' : Finset A // E' ⊆ E},
          B ⧸ Ideal.span {1 - stratumIdempotent f E j}) j)
    by_cases hji : j = i
    · subst j
      simp [hcoord]
    · simp [hcoord, hji]
  apply e.injective
  calc
    e (e.symm (Pi.single i (1 : B ⧸
        Ideal.span {1 - stratumIdempotent f E i}))) =
        Pi.single i 1 := e.apply_symm_apply _
    _ = e (stratumIdempotent f E i) := heval.symm

end AlgebraicGeometry.ProEtale

end
