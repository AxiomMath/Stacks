module

public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratumIdempotent
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimit
public import Mathlib.RingTheory.Ideal.Nonunits

/-!
# Maps out of the stratification rings of a ring with w-local spectrum

Let `A → B` be a ring map with `Spec B` w-local. For each finite subset `E ⊆ A` the ring `A_E`
is the product of the localizations attached to the vanishing strata of `E`, and `B` is the
product of the quotients cut out by the idempotents of those strata. Matching the factors
produces a ring map `A_E → B` over `A`, compatible with the transition maps `A_{E₁} → A_{E₂}`,
hence a ring map `A_w → B` out of the colimit. This map is the unique one over `A` carrying each
stratum idempotent of `A_E` to the corresponding idempotent of `B`.

## Main definitions

* `AlgebraicGeometry.ProEtale.stratificationStageMap`: the map `A_E → B` at a finite stage.
* `AlgebraicGeometry.ProEtale.stratificationColimitLift`: the induced map `A_w → B`.
* `RingHom.piSelectedFactor`: the factor through which a ring map out of a finite product
  factors when it kills all but one of the coordinate units.

## Main results

* `AlgebraicGeometry.ProEtale.stratificationStageMap_transition`: the stage maps are compatible
  with the transition maps.
* `AlgebraicGeometry.ProEtale.stratificationColimitLift_comp_algebraMap`: the induced map is a
  map over `A`.
* `AlgebraicGeometry.ProEtale.stratificationStageMap_eq_of_idempotents`: a map `A_E → B` over
  `A` sending each coordinate unit to the matching stratum idempotent is the stage map.

## Implementation notes

The factor of the stage map at a vanishing stratum is obtained by the universal property of
localization: the elements of `A` inverted on the stratum become units in the quotient of `B`
cut out by the matching idempotent, because a prime of that quotient contracts to a point of
`Spec B` whose closed specialization lies over the stratum.

A ring map out of a finite product of rings that sends one coordinate unit to `1` and the others
to `0` is determined by its restriction to that coordinate, which is recorded separately as
`RingHom.piSelectedFactor`; this is what reduces the uniqueness statements to the uniqueness in
the universal property of a localization.

## References

* [Stacks Project, Tag 0972](https://stacks.math.columbia.edu/tag/0972)
* [Stacks Project, Tag 0973](https://stacks.math.columbia.edu/tag/0973)
* [Stacks Project, Tag 0977](https://stacks.math.columbia.edu/tag/0977)
-/

@[expose] public noncomputable section

namespace RingHom

/-- The `j`-th factor through which a ring map out of a finite product of rings factors, given
that it sends the `j`-th coordinate unit to `1` and every other coordinate unit to `0`. -/
noncomputable def piSelectedFactor
    {ι : Type*} [DecidableEq ι]
    {C : ι → Type*} [∀ i, Semiring (C i)] {D : Type*} [Semiring D]
    (φ : (∀ i, C i) →+* D) (j : ι)
    (hone : φ (Pi.single j 1) = 1) : C j →+* D where
  toFun x := φ (Pi.single j x)
  map_one' := hone
  map_mul' x y := by rw [← map_mul φ, ← Pi.single_mul]
  map_zero' := by simp
  map_add' x y := by rw [← map_add φ, ← Pi.single_add]

/-- A ring map out of a finite product of rings that sends the `j`-th coordinate unit to `1` and
every other coordinate unit to `0` is evaluation at `j` followed by its `j`-th factor. -/
theorem apply_eq_piSelectedFactor
    {ι : Type*} [_root_.Finite ι] [DecidableEq ι]
    {C : ι → Type*} [∀ i, Semiring (C i)] {D : Type*} [Semiring D]
    (φ : (∀ i, C i) →+* D) (j : ι)
    (hone : φ (Pi.single j 1) = 1)
    (hzero : ∀ i, i ≠ j → φ (Pi.single i 1) = 0)
    (x : ∀ i, C i) :
    φ x = piSelectedFactor φ j hone (x j) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite _
  have hdecomp : x = ∑ i, Pi.single i (x i) := by
    ext i
    simp
  have hzero' : ∀ i, i ≠ j → φ (Pi.single i (x i)) = 0 := by
    intro i hij
    have hmul : Pi.single i (x i) = Pi.single i 1 * Pi.single i (x i) := by
      rw [← Pi.single_mul, one_mul]
    rw [hmul, map_mul, hzero i hij, zero_mul]
  calc
    φ x = φ (∑ i, Pi.single i (x i)) := congrArg φ hdecomp
    _ = ∑ i, φ (Pi.single i (x i)) := map_sum φ _ _
    _ = φ (Pi.single j (x j)) :=
      Finset.sum_eq_single j (fun i _ hij => hzero' i hij) (by simp)
    _ = piSelectedFactor φ j hone (x j) := rfl

end RingHom

namespace AlgebraicGeometry.ProEtale

/-- An element of `A` inverted on the vanishing stratum `i` becomes a unit in the quotient of
`B` cut out by the idempotent of the matching clopen piece of `Spec B`. -/
lemma isUnit_mk_map_of_mem_localizationSubmonoid
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) (i : {E' : Finset A // E' ⊆ E}) (s : A)
    (hs : s ∈ localizationSubmonoid
      (stratumIdeal E i) (stratumOpenElement i.val)) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {1 - stratumIdempotent f E i}) (f s)) := by
  classical
  let J : Ideal B := Ideal.span {1 - stratumIdempotent f E i}
  let π : B →+* B ⧸ J := Ideal.Quotient.mk J
  have hAvoid : ∀ q : PrimeSpectrum (B ⧸ J),
      π (f s) ∉ q.asIdeal := by
    intro q hmem
    let p : PrimeSpectrum B := PrimeSpectrum.comap π q
    have hOneSub : (1 - stratumIdempotent f E i) ∈ p.asIdeal := by
      show π (1 - stratumIdempotent f E i) ∈ q.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))]
      exact q.asIdeal.zero_mem
    have hnot : stratumIdempotent f E i ∉ p.asIdeal := fun he =>
      p.2.ne_top ((Ideal.eq_top_iff_one p.asIdeal).2
        (by simpa using p.asIdeal.add_mem he hOneSub))
    have hp : p ∈ stratumClopen f E i := by
      show p ∈ (stratumClopen f E i : Set (PrimeSpectrum B))
      rw [coe_stratumClopen_eq_basicOpen f E i]
      exact (PrimeSpectrum.mem_basicOpen _ _).2 hnot
    obtain ⟨c, hpc, hc⟩ :=
      (mem_stratumClopen_iff f E i p).mp hp
    let qA : PrimeSpectrum A := PrimeSpectrum.comap f c.1
    have hqA : qA ∈ locallyClosedPoints
        (stratumIdeal E i) (stratumOpenElement i.val) := by
      simpa [qA, stratumClosedPointsClopen] using hc
    have hsNot : s ∉ (PrimeSpectrum.comap f p).asIdeal := fun hsp =>
      localizationSubmonoid_notMem_of_mem_locallyClosedPoints
        (stratumIdeal E i) (stratumOpenElement i.val) s hs qA hqA
        ((PrimeSpectrum.le_iff_specializes _ _).mpr
          (hpc.map (PrimeSpectrum.continuous_comap f)) hsp)
    exact hsNot hmem
  by_contra hunit
  obtain ⟨M, hM, hmem⟩ := exists_max_ideal_of_mem_nonunits (a := π (f s)) (by
    simpa [mem_nonunits_iff] using hunit)
  let q : PrimeSpectrum (B ⧸ J) := ⟨M, hM.isPrime⟩
  exact hAvoid q hmem

/-- The factor `A_{E,i} → B / (1 - e_i)` of the stage map at the vanishing stratum `i`, where
`e_i` is the idempotent cutting out the matching clopen piece of `Spec B`. -/
noncomputable def stratumLocalizationMap
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) (i : {E' : Finset A // E' ⊆ E}) :
    localizationRing (stratumIdeal E i)
      (stratumOpenElement i.val) →+*
      B ⧸ Ideal.span {1 - stratumIdempotent f E i} := by
  let M := localizationSubmonoid
    (stratumIdeal E i) (stratumOpenElement i.val)
  let π : B →+* B ⧸ Ideal.span {1 - stratumIdempotent f E i} :=
    Ideal.Quotient.mk _
  exact IsLocalization.lift (M := M) (g := π.comp f) (fun s =>
    isUnit_mk_map_of_mem_localizationSubmonoid f E i s s.2)

/-- The map `A_E → B` matching the factors of the product decompositions of `A_E` and of `B`
along the vanishing strata of `E`. -/
noncomputable def stratificationStageMap
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) : stratificationRing E →+* B := by
  classical
  letI := stratumIndexFintype E
  let e := stratumQuotientPiEquiv f E
  let h : stratificationRing E →+*
      ∀ i : {E' : Finset A // E' ⊆ E},
        B ⧸ Ideal.span {1 - stratumIdempotent f E i} :=
    RingHom.pi (fun i =>
      (stratumLocalizationMap f E i).comp (Pi.evalRingHom _ i))
  exact e.symm.toRingHom.comp h

/-- The stage map is a map of `A`-algebras. -/
theorem stratificationStageMap_comp_algebraMap
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) :
    (stratificationStageMap f E).comp (stratificationAlgebraMap E) = f := by
  classical
  let _ := stratumIndexFintype E
  apply RingHom.ext
  intro a
  apply (stratumQuotientPiEquiv f E).injective
  ext i
  simp [stratificationStageMap, stratumQuotientPiEquiv, stratumLocalizationMap,
    stratificationAlgebraMap, IsLocalization.lift_eq]

private noncomputable def stratumQuotientTransition
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E₁ E₂ : Finset A) (i₁ : {E' : Finset A // E' ⊆ E₁})
    (i₂ : {E' : Finset A // E' ⊆ E₂})
    (h : stratumIdempotent f E₂ i₂ * stratumIdempotent f E₁ i₁ =
      stratumIdempotent f E₂ i₂) :
    B ⧸ Ideal.span {1 - stratumIdempotent f E₁ i₁} →+*
      B ⧸ Ideal.span {1 - stratumIdempotent f E₂ i₂} := by
  refine Ideal.Quotient.lift _ (Ideal.Quotient.mk _) fun x hx => ?_
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.1 hx
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2
    ⟨(1 - stratumIdempotent f E₁ i₁) * a, by linear_combination -a * h⟩)

private theorem stratumLocalizationMap_transition
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E₁ E₂ : Finset A) (hE : E₁ ⊆ E₂)
    (i₂ : {E' : Finset A // E' ⊆ E₂})
    (hcl : (stratumClopen f E₂ i₂ : Set (PrimeSpectrum B)) ⊆
      stratumClopen f E₁ (restrictStratum E₁ E₂ hE i₂ :
        {E' : Finset A // E' ⊆ E₁})) :
    (stratumLocalizationMap f E₂ i₂).comp
        (localizationMap (RingHom.id A)
          (stratumIdeal E₁
            (restrictStratum E₁ E₂ hE i₂))
          (stratumOpenElement
            (restrictStratum E₁ E₂ hE i₂).val)
          (stratumIdeal E₂ i₂) (stratumOpenElement i₂.val)
          (by
            intro q hq
            simpa only [PrimeSpectrum.comap_id] using
              locallyClosedPoints_restrictStratum E₁ E₂ hE i₂ q hq)) =
      (stratumQuotientTransition f E₁ E₂
        (restrictStratum E₁ E₂ hE i₂) i₂
        (stratumIdempotent_mul_eq_of_clopen_subset f E₁ E₂ _ _ hcl)).comp
        (stratumLocalizationMap f E₁
          (restrictStratum E₁ E₂ hE i₂)) := by
  apply IsLocalization.ringHom_ext
    (localizationSubmonoid
      (stratumIdeal E₁
        (restrictStratum E₁ E₂ hE i₂))
      (stratumOpenElement
        (restrictStratum E₁ E₂ hE i₂).val))
  apply RingHom.ext
  intro a
  simp [stratumLocalizationMap, stratumQuotientTransition,
    localizationMap]

/-- The stage maps are compatible with the transition maps between stratification rings. -/
theorem stratificationStageMap_transition
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E₁ E₂ : Finset A) (hE : E₁ ⊆ E₂) :
    (stratificationStageMap f E₂).comp
        (stratificationRingMap E₁ E₂ hE) =
      stratificationStageMap f E₁ := by
  classical
  let _ := stratumIndexFintype E₁
  let _ := stratumIndexFintype E₂
  apply RingHom.ext
  intro x
  apply (stratumQuotientPiEquiv f E₂).injective
  ext i₂
  let i₁ := restrictStratum E₁ E₂ hE i₂
  let e₁ := stratumIdempotent f E₁ i₁
  let e₂ := stratumIdempotent f E₂ i₂
  let θ : B ⧸ Ideal.span {1 - e₁} →+* B ⧸ Ideal.span {1 - e₂} :=
    stratumQuotientTransition f E₁ E₂ i₁ i₂
      (stratumIdempotent_mul_eq_of_clopen_subset f E₁ E₂ i₁ i₂
        (stratumClopen_subset_restrictStratum f E₁ E₂ hE i₂))
  have hθ (b : B) : θ (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ b := by
    show Ideal.Quotient.lift _ (Ideal.Quotient.mk _) _
        (Ideal.Quotient.mk _ b) = _
    rw [Ideal.Quotient.lift_mk]
  rw [stratificationStageMap, RingHom.comp_apply]
  show (Ideal.Quotient.mk (Ideal.span {1 - e₂}))
      ((stratumQuotientPiEquiv f E₂).symm
        ((RingHom.pi fun i =>
          (stratumLocalizationMap f E₂ i).comp (Pi.evalRingHom _ i))
          ((stratificationRingMap E₁ E₂ hE) x))) = _
  rw [mk_stratumQuotientPiEquiv_symm]
  rw [stratificationStageMap]
  show (stratumLocalizationMap f E₂ i₂)
      ((stratificationRingMap E₁ E₂ hE x) i₂) =
    Ideal.Quotient.mk (Ideal.span {1 - e₂})
      ((stratumQuotientPiEquiv f E₁).symm
        ((RingHom.pi fun i =>
          (stratumLocalizationMap f E₁ i).comp (Pi.evalRingHom _ i)) x))
  rw [← hθ, mk_stratumQuotientPiEquiv_symm]
  simp only [stratificationRingMap, RingHom.pi_apply,
    RingHom.comp_apply, Pi.evalRingHom_apply]
  exact congrArg (fun φ : localizationRing
      (stratumIdeal E₁ i₁) (stratumOpenElement i₁.val) →+*
      B ⧸ Ideal.span {1 - e₂} => φ (x i₁))
    (stratumLocalizationMap_transition f E₁ E₂ hE i₂
      (stratumClopen_subset_restrictStratum f E₁ E₂ hE i₂))

/-- The map `A_w → B` induced by the stage maps on the colimit of the stratification rings. -/
noncomputable def stratificationColimitLift
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B) :
    stratificationColimitRing (A := A) →+* B :=
  Ring.DirectLimit.lift
    (fun E : Finset A => stratificationRing E)
    (fun E₁ E₂ h => stratificationRingMap E₁ E₂ h) B
    (stratificationStageMap f)
    (fun E₁ E₂ h x =>
      DFunLike.congr_fun (stratificationStageMap_transition f E₁ E₂ h) x)

/-- The induced map on the colimit restricts to the stage map at each finite stage. -/
theorem stratificationColimitLift_of
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) (x : stratificationRing E) :
    stratificationColimitLift f (stratificationColimitMap E x) =
      stratificationStageMap f E x :=
  Ring.DirectLimit.lift_of ..

/-- The induced map `A_w → B` is a map of `A`-algebras. -/
theorem stratificationColimitLift_comp_algebraMap
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B) :
    (stratificationColimitLift f).comp
        (stratificationColimitAlgebraMap (A := A)) = f := by
  refine RingHom.ext fun a => ?_
  show stratificationColimitLift f
      (stratificationColimitMap ∅
        (stratificationAlgebraMap ∅ a)) = f a
  rw [stratificationColimitLift_of]
  exact DFunLike.congr_fun (stratificationStageMap_comp_algebraMap f ∅) a

private theorem single_one_mul_stratificationAlgebraMap
    {A : Type*} [CommRing A] (E : Finset A)
    (i : {E' : Finset A // E' ⊆ E})
    [DecidableEq {E' : Finset A // E' ⊆ E}] (a : A) :
    (Pi.single i (1 : localizationRing
      (stratumIdeal E i) (stratumOpenElement i.val))) *
        stratificationAlgebraMap E a =
      Pi.single i (algebraMap A
        (localizationRing (stratumIdeal E i)
          (stratumOpenElement i.val)) a) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [stratificationAlgebraMap, RingHom.pi_apply]
  · simp [stratificationAlgebraMap, RingHom.pi_apply, hji]

/-- Two maps `A_E → K` over `A` that send the coordinate unit at `i` to `1` and every other
coordinate unit to `0` are equal. -/
theorem ringHom_stratificationRing_eq_of_single
    {A K : Type*} [CommRing A] [CommRing K] (E : Finset A)
    (f : A →+* K) (i : {E' : Finset A // E' ⊆ E})
    [DecidableEq {E' : Finset A // E' ⊆ E}]
    (φ ψ : stratificationRing E →+* K)
    (hφ : φ.comp (stratificationAlgebraMap E) = f)
    (hψ : ψ.comp (stratificationAlgebraMap E) = f)
    (hφone : φ (Pi.single i 1) = 1)
    (hψone : ψ (Pi.single i 1) = 1)
    (hφzero : ∀ j, j ≠ i → φ (Pi.single j 1) = 0)
    (hψzero : ∀ j, j ≠ i → ψ (Pi.single j 1) = 0) :
    φ = ψ := by
  classical
  let _ := stratumIndexFintype E
  let L := localizationRing (stratumIdeal E i)
    (stratumOpenElement i.val)
  have hbase (θ : stratificationRing E →+* K) (hθ : θ.comp (stratificationAlgebraMap E) = f)
      (h₁ : θ (Pi.single i 1) = 1) :
      (RingHom.piSelectedFactor θ i h₁ : L →+* K).comp (algebraMap A L) = f := by
    ext a
    show θ (Pi.single i (algebraMap A L a)) = f a
    rw [← single_one_mul_stratificationAlgebraMap E i a, map_mul, h₁, one_mul]
    exact DFunLike.congr_fun hθ a
  have hα : (RingHom.piSelectedFactor φ i hφone : L →+* K) =
      RingHom.piSelectedFactor ψ i hψone :=
    IsLocalization.ringHom_ext
      (localizationSubmonoid (stratumIdeal E i) (stratumOpenElement i.val))
      ((hbase φ hφ hφone).trans (hbase ψ hψ hψone).symm)
  refine RingHom.ext fun x => ?_
  calc
    φ x = RingHom.piSelectedFactor φ i hφone (x i) :=
      RingHom.apply_eq_piSelectedFactor φ i hφone hφzero x
    _ = RingHom.piSelectedFactor ψ i hψone (x i) :=
      congrArg (fun k : L →+* K => k (x i)) hα
    _ = ψ x := (RingHom.apply_eq_piSelectedFactor ψ i hψone hψzero x).symm

/-- The stage map sends the coordinate unit at the vanishing stratum `i` to the idempotent of `B`
cutting out the matching clopen piece. -/
theorem stratificationStageMap_single_one
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) (j : {E' : Finset A // E' ⊆ E})
    [DecidableEq {E' : Finset A // E' ⊆ E}] :
    stratificationStageMap f E (Pi.single j
      (1 : localizationRing (stratumIdeal E j)
        (stratumOpenElement j.val))) = stratumIdempotent f E j := by
  classical
  let _ := stratumIndexFintype E
  rw [stratificationStageMap]
  show (stratumQuotientPiEquiv f E).symm
    ((RingHom.pi fun k =>
      (stratumLocalizationMap f E k).comp (Pi.evalRingHom _ k))
      (Pi.single j 1)) = stratumIdempotent f E j
  have heval : (RingHom.pi fun k =>
      (stratumLocalizationMap f E k).comp (Pi.evalRingHom _ k))
      (Pi.single j (1 : localizationRing
        (stratumIdeal E j) (stratumOpenElement j.val))) =
      Pi.single j 1 := by
    ext k
    by_cases hkj : k = j
    · subst k
      rw [Pi.single_eq_same]
      simp
    · simp [hkj]
  rw [heval]
  exact stratumQuotientPiEquiv_symm_single_one f E j

/-- A map `A_E → B` over `A` sending each coordinate unit to the matching stratum idempotent is
the stage map. -/
theorem stratificationStageMap_eq_of_idempotents
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) (φ : stratificationRing E →+* B)
    [DecidableEq {E' : Finset A // E' ⊆ E}]
    (hφ : φ.comp (stratificationAlgebraMap E) = f)
    (hid : ∀ i : {E' : Finset A // E' ⊆ E},
      φ (Pi.single i (1 : localizationRing
        (stratumIdeal E i) (stratumOpenElement i.val))) =
        stratumIdempotent f E i) :
    φ = stratificationStageMap f E := by
  classical
  let _ := stratumIndexFintype E
  refine RingHom.ext fun x => ?_
  apply (stratumQuotientPiEquiv f E).injective
  ext i
  let J : Ideal B := Ideal.span {1 - stratumIdempotent f E i}
  let π : B →+* B ⧸ J := Ideal.Quotient.mk J
  let fi : A →+* B ⧸ J := π.comp f
  have hπi : π (stratumIdempotent f E i) = 1 := by
    have hz : π (1 - stratumIdempotent f E i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))
    rw [map_sub, map_one, sub_eq_zero] at hz
    exact hz.symm
  have hπjzero (j : {E' : Finset A // E' ⊆ E}) (hji : j ≠ i) :
      π (stratumIdempotent f E j) = 0 := by
    have horth := (completeOrthogonalIdempotents_stratumIdempotent f E).ortho hji
    change stratumIdempotent f E j * stratumIdempotent f E i = 0 at horth
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2
      ⟨stratumIdempotent f E j, by linear_combination horth⟩)
  have key (θ : stratificationRing E →+* B) (hθ : θ.comp (stratificationAlgebraMap E) = f)
      (hθid : ∀ j : {E' : Finset A // E' ⊆ E}, θ (Pi.single j
        (1 : localizationRing (stratumIdeal E j) (stratumOpenElement j.val))) =
        stratumIdempotent f E j) :
      (π.comp θ).comp (stratificationAlgebraMap E) = fi ∧
        π.comp θ (Pi.single i
          (1 : localizationRing (stratumIdeal E i) (stratumOpenElement i.val))) = 1 ∧
        ∀ j, j ≠ i → π.comp θ (Pi.single j
          (1 : localizationRing (stratumIdeal E j) (stratumOpenElement j.val))) = 0 :=
    ⟨RingHom.ext fun a => congrArg π (DFunLike.congr_fun hθ a),
      (congrArg π (hθid i)).trans hπi,
      fun j hji => (congrArg π (hθid j)).trans (hπjzero j hji)⟩
  obtain ⟨hφbase, hφone, hφzero⟩ := key φ hφ hid
  obtain ⟨hψbase, hψone, hψzero⟩ := key (stratificationStageMap f E)
    (stratificationStageMap_comp_algebraMap f E) (stratificationStageMap_single_one f E ·)
  exact DFunLike.congr_fun (ringHom_stratificationRing_eq_of_single E fi i (π.comp φ)
    (π.comp (stratificationStageMap f E))
    hφbase hψbase hφone hψone hφzero hψzero) x

end AlgebraicGeometry.ProEtale

end
