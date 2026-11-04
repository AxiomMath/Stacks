module

public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationStageMap
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationLimitBijection
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationLimitClosedPoints
public import StacksCore.Tactic.StacksAttribute

/-!
# Universal property of the w-localization of a ring

For a commutative ring `A`, the colimit `A_w` of the finite vanishing stratification rings of
`Spec A` is universal among maps from `A` into rings with w-local spectrum: a ring map `A → B`
with `Spec B` w-local factors through `A → A_w` by exactly one ring map `A_w → B` whose induced
map of spectra is w-local.

## Main results

* `AlgebraicGeometry.ProEtale.existsUnique_wLocal_lift`: the unique factorization through `A_w`.

## Implementation notes

Existence is the map assembled from the stage maps, and the content of the existence half is
that its map of spectra carries closed points to closed points. A closed point of `Spec B` is a
maximal ideal, and the composite of the induced map with the residue field of that maximal ideal
is the map attached to the vanishing pattern that the residue field sees; the kernel of that map
is maximal, which is exactly the required statement.

Uniqueness is proved stage by stage. A competing factorization `g` with w-local spectrum map
agrees with the assembled map on the coordinate units of each stage, because both send a
coordinate unit to an idempotent of `B` with the same basic open: a closed point of `Spec B`
has the same image under both maps, since the two images are closed points of `Spec A_w` with
the same contraction to `Spec A`, and the closed points of `Spec A_w` inject into `Spec A` by
the identification of the limiting closed subscheme.

W-locality of the spectrum map is part of the uniqueness predicate rather than a property
asserted of one chosen factorization, since without it the factorization is not unique.

## References

* [Stacks Project, Tag 0977](https://stacks.math.columbia.edu/tag/0977)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProEtale

open CategoryTheory TopologicalSpace

universe u v

private noncomputable def fieldPatternIndex
    {A K : Type*} [CommRing A] [Field K]
    (f : A →+* K) (E : Finset A) :
    {E' : Finset A // E' ⊆ E} := by
  classical
  exact ⟨E.filter (fun a => f a ≠ 0), Finset.filter_subset _ _⟩

private theorem fieldPatternIndex_locallyClosed
    {A K : Type*} [CommRing A] [Field K]
    (f : A →+* K) (E : Finset A) :
    PrimeSpectrum.comap f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) ∈
      locallyClosedPoints
        (stratumIdeal E (fieldPatternIndex f E))
        (stratumOpenElement (fieldPatternIndex f E).val) := by
  classical
  have : CommRing K := Field.toCommRing
  let q : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  rw [mem_locallyClosedPoints_stratum_iff]
  constructor
  · intro a ha
    have haf : f a ≠ 0 := (Finset.mem_filter.mp ha).2
    show f a ∉ (⊥ : Ideal K)
    rw [Ideal.mem_bot]
    exact haf
  · intro a ha
    have hae : a ∈ E := by
      exact (Set.mem_sdiff a).mp ha |>.1
    have han : a ∉ (fieldPatternIndex f E).val := by
      exact (Set.mem_sdiff a).mp ha |>.2
    have haf : f a = 0 := by
      by_contra hne
      exact han (Finset.mem_filter.mpr ⟨hae, hne⟩)
    show f a ∈ (⊥ : Ideal K)
    rw [Ideal.mem_bot]
    exact haf

private theorem fieldPatternLocalizationMap_units
    {A K : Type*} [CommRing A] [Field K]
    (f : A →+* K) (E : Finset A) :
    ∀ t : localizationSubmonoid
      (stratumIdeal E (fieldPatternIndex f E))
      (stratumOpenElement (fieldPatternIndex f E).val), IsUnit (f t) := by
  let i := fieldPatternIndex f E
  let I := stratumIdeal E i
  let s := stratumOpenElement i.val
  have : CommRing K := Field.toCommRing
  let q : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  intro t
  have hnot := localizationSubmonoid_notMem_of_mem_locallyClosedPoints I s t.1 t.2
    (PrimeSpectrum.comap f q) (fieldPatternIndex_locallyClosed f E)
  have hne : f t.1 ≠ 0 := by
    intro hz
    apply hnot
    show f t.1 ∈ (⊥ : Ideal K)
    rw [Ideal.mem_bot]
    exact hz
  exact isUnit_iff_ne_zero.mpr hne

private noncomputable def fieldPatternLocalizationMap
    {A K : Type*} [CommRing A] [Field K]
    (f : A →+* K) (E : Finset A) :
    localizationRing
        (stratumIdeal E (fieldPatternIndex f E))
        (stratumOpenElement (fieldPatternIndex f E).val) →+* K :=
  IsLocalization.lift (M := localizationSubmonoid
    (stratumIdeal E (fieldPatternIndex f E))
    (stratumOpenElement (fieldPatternIndex f E).val))
    (g := f) (fieldPatternLocalizationMap_units f E)

/-- The localization map restricts to `f` along `algebraMap`. -/
private theorem fieldPatternLocalizationMap_algebraMap
    {A K : Type*} [CommRing A] [Field K] (f : A →+* K) (E : Finset A) (a : A) :
    fieldPatternLocalizationMap f E (algebraMap A
      (localizationRing
        (stratumIdeal E (fieldPatternIndex f E))
        (stratumOpenElement (fieldPatternIndex f E).val)) a) = f a :=
  IsLocalization.lift_eq (fieldPatternLocalizationMap_units f E) a

private theorem fieldPatternLocalizationMap_comp_algebraMap
    {A K : Type*} [CommRing A] [Field K] (f : A →+* K) (E : Finset A) :
    (fieldPatternLocalizationMap f E).comp (algebraMap A
      (localizationRing
        (stratumIdeal E (fieldPatternIndex f E))
        (stratumOpenElement (fieldPatternIndex f E).val))) = f :=
  RingHom.ext (fieldPatternLocalizationMap_algebraMap f E)

private noncomputable def fieldPatternStageMap
    {A K : Type*} [CommRing A] [Field K]
    (f : A →+* K) (E : Finset A) :
    stratificationRing E →+* K :=
  (fieldPatternLocalizationMap f E).comp
    (Pi.evalRingHom _ (fieldPatternIndex f E))

private theorem fieldPatternIndex_restrict
    {A K : Type*} [CommRing A] [Field K] (f : A →+* K)
    (E₁ E₂ : Finset A) (hE : E₁ ⊆ E₂) :
    fieldPatternIndex f E₁ =
      restrictStratum E₁ E₂ hE (fieldPatternIndex f E₂) := by
  classical
  apply Subtype.ext
  ext a
  simp only [fieldPatternIndex, Finset.mem_filter, restrictStratum,
    Finset.mem_inter]
  constructor
  · rintro ⟨ha, hfa⟩
    exact ⟨ha, hE ha, hfa⟩
  · rintro ⟨ha, _, hfa⟩
    exact ⟨ha, hfa⟩

private theorem stratumLocalizationMap_index_cast
    {A : Type*} [CommRing A] (E₁ E₂ : Finset A) (_hE : E₁ ⊆ E₂)
    (i j : {E' : Finset A // E' ⊆ E₁}) (hij : i = j)
    (k : {E' : Finset A // E' ⊆ E₂})
    (hik : ∀ q : PrimeSpectrum A, q ∈
      locallyClosedPoints (stratumIdeal E₂ k)
        (stratumOpenElement k.val) →
      PrimeSpectrum.comap (RingHom.id A) q ∈
        locallyClosedPoints (stratumIdeal E₁ i)
          (stratumOpenElement i.val))
    (hjk : ∀ q : PrimeSpectrum A, q ∈
      locallyClosedPoints (stratumIdeal E₂ k)
        (stratumOpenElement k.val) →
      PrimeSpectrum.comap (RingHom.id A) q ∈
        locallyClosedPoints (stratumIdeal E₁ j)
          (stratumOpenElement j.val))
    (x : localizationRing (stratumIdeal E₁ i)
      (stratumOpenElement i.val)) :
    localizationMap (RingHom.id A) (stratumIdeal E₁ j)
        (stratumOpenElement j.val) (stratumIdeal E₂ k)
        (stratumOpenElement k.val) hjk
        (cast (congrArg (fun l => localizationRing
          (stratumIdeal E₁ l) (stratumOpenElement l.val)) hij) x) =
      localizationMap (RingHom.id A) (stratumIdeal E₁ i)
        (stratumOpenElement i.val) (stratumIdeal E₂ k)
        (stratumOpenElement k.val) hik x := by
  cases hij
  rfl

private theorem fieldPatternStageMap_transition
    {A K : Type*} [CommRing A] [Field K] (f : A →+* K)
    (E₁ E₂ : Finset A) (hE : E₁ ⊆ E₂) :
    (fieldPatternStageMap f E₂).comp
        (stratificationRingMap E₁ E₂ hE) =
      fieldPatternStageMap f E₁ := by
  classical
  let i₁ := fieldPatternIndex f E₁
  let i₂ := fieldPatternIndex f E₂
  have hi : i₁ = restrictStratum E₁ E₂ hE i₂ :=
    fieldPatternIndex_restrict f E₁ E₂ hE
  let M₁ := localizationSubmonoid
    (stratumIdeal E₁ i₁) (stratumOpenElement i₁.val)
  let hZ : ∀ q : PrimeSpectrum A,
      q ∈ locallyClosedPoints (stratumIdeal E₂ i₂)
        (stratumOpenElement i₂.val) →
      PrimeSpectrum.comap (RingHom.id A) q ∈
        locallyClosedPoints (stratumIdeal E₁ i₁)
          (stratumOpenElement i₁.val) := by
    intro q hq
    rw [hi]
    show q ∈ locallyClosedPoints
      (stratumIdeal E₁ (restrictStratum E₁ E₂ hE i₂))
      (stratumOpenElement (restrictStratum E₁ E₂ hE i₂).val)
    exact locallyClosedPoints_restrictStratum E₁ E₂ hE i₂ q hq
  have hθ :
      (fieldPatternLocalizationMap f E₂).comp
        (localizationMap (RingHom.id A)
          (stratumIdeal E₁ i₁)
          (stratumOpenElement i₁.val)
          (stratumIdeal E₂ i₂)
          (stratumOpenElement i₂.val)
hZ) =
        fieldPatternLocalizationMap f E₁ := by
    have hbase₁ :
        (fieldPatternLocalizationMap f E₁).comp (algebraMap A
          (localizationRing (stratumIdeal E₁ i₁)
            (stratumOpenElement i₁.val))) = f := by
      simpa [i₁] using fieldPatternLocalizationMap_comp_algebraMap f E₁
    have hbase₂ :
        (fieldPatternLocalizationMap f E₂).comp (algebraMap A
          (localizationRing (stratumIdeal E₂ i₂)
            (stratumOpenElement i₂.val))) = f := by
      simpa [i₂] using fieldPatternLocalizationMap_comp_algebraMap f E₂
    have hmap :
        (localizationMap (RingHom.id A)
          (stratumIdeal E₁ i₁)
          (stratumOpenElement i₁.val)
          (stratumIdeal E₂ i₂)
          (stratumOpenElement i₂.val)
hZ).comp
          (algebraMap A (localizationRing
            (stratumIdeal E₁ i₁) (stratumOpenElement i₁.val))) =
        algebraMap A (localizationRing
          (stratumIdeal E₂ i₂) (stratumOpenElement i₂.val)) := by
      ext a
      simp [localizationMap]
    apply IsLocalization.ringHom_ext M₁
    apply RingHom.ext
    intro a
    calc
      fieldPatternLocalizationMap f E₂
          ((localizationMap (RingHom.id A)
            (stratumIdeal E₁ i₁)
            (stratumOpenElement i₁.val)
            (stratumIdeal E₂ i₂)
            (stratumOpenElement i₂.val) hZ)
            (algebraMap A (localizationRing
              (stratumIdeal E₁ i₁)
              (stratumOpenElement i₁.val)) a)) =
        fieldPatternLocalizationMap f E₂
          (algebraMap A (localizationRing
            (stratumIdeal E₂ i₂)
            (stratumOpenElement i₂.val)) a) := by
              congr 1
              exact DFunLike.congr_fun hmap a
      _ = f a := DFunLike.congr_fun hbase₂ a
      _ = fieldPatternLocalizationMap f E₁
            (algebraMap A (localizationRing
              (stratumIdeal E₁ i₁)
              (stratumOpenElement i₁.val)) a) :=
          (DFunLike.congr_fun hbase₁ a).symm
  apply RingHom.ext
  intro x
  let L : {E' : Finset A // E' ⊆ E₁} → Type _ := fun i =>
    localizationRing (stratumIdeal E₁ i)
      (stratumOpenElement i.val)
  have hcast := dependentSection_cast (β := L) x hi
  have hZr : ∀ q : PrimeSpectrum A,
      q ∈ locallyClosedPoints (stratumIdeal E₂ i₂)
        (stratumOpenElement i₂.val) →
      PrimeSpectrum.comap (RingHom.id A) q ∈
        locallyClosedPoints
          (stratumIdeal E₁ (restrictStratum E₁ E₂ hE i₂))
          (stratumOpenElement
            (restrictStratum E₁ E₂ hE i₂).val) := by
    intro q hq
    simpa only [PrimeSpectrum.comap_id] using
      locallyClosedPoints_restrictStratum E₁ E₂ hE i₂ q hq
  have hmapcast := stratumLocalizationMap_index_cast E₁ E₂ hE i₁
    (restrictStratum E₁ E₂ hE i₂) hi i₂ hZ hZr (x i₁)
  simp only [fieldPatternStageMap, RingHom.comp_apply,
    stratificationRingMap, RingHom.pi_apply,
    Pi.evalRingHom_apply]
  rw [← hcast, hmapcast]
  exact congrArg (fun θ => θ (x i₁)) hθ

private noncomputable def fieldPatternLift
    {A K : Type*} [CommRing A] [Field K] (f : A →+* K) :
    stratificationColimitRing (A := A) →+* K :=
  Ring.DirectLimit.lift
    (fun E : Finset A => stratificationRing E)
    (fun E₁ E₂ h => stratificationRingMap E₁ E₂ h) K
    (fieldPatternStageMap f)
    (fun E₁ E₂ h x =>
      congrArg (fun φ => φ x) (fieldPatternStageMap_transition f E₁ E₂ h))

private theorem fieldPatternStageMap_comp_algebraMap
    {A K : Type*} [CommRing A] [Field K] (f : A →+* K) (E : Finset A) :
    (fieldPatternStageMap f E).comp (stratificationAlgebraMap E) = f := by
  classical
  apply RingHom.ext
  intro a
  exact fieldPatternLocalizationMap_algebraMap f E a

private theorem fieldPatternLift_of
    {A K : Type*} [CommRing A] [Field K] (f : A →+* K)
    (E : Finset A) (x : stratificationRing E) :
    fieldPatternLift f (stratificationColimitMap E x) =
      fieldPatternStageMap f E x := by
  show Ring.DirectLimit.lift
      (fun E : Finset A => stratificationRing E)
      (fun E₁ E₂ h => stratificationRingMap E₁ E₂ h) K
      (fieldPatternStageMap f)
      (fun E₁ E₂ h x =>
        congrArg (fun φ => φ x) (fieldPatternStageMap_transition f E₁ E₂ h))
      (Ring.DirectLimit.of
        (fun E : Finset A => stratificationRing E)
        (fun E₁ E₂ h => stratificationRingMap E₁ E₂ h) E x) = _
  rw [Ring.DirectLimit.lift_of]

private theorem fieldPatternLift_mul_eq_one_of_ne_zero
    {A K : Type*} [CommRing A] [Field K] (f : A →+* K)
    (x : stratificationColimitRing (A := A))
    (hx : fieldPatternLift f x ≠ 0) :
    ∃ y, fieldPatternLift f (x * y) = 1 := by
  classical
  obtain ⟨E, xE, rfl⟩ := Ring.DirectLimit.exists_of x
  let i := fieldPatternIndex f E
  let L := localizationRing (stratumIdeal E i)
    (stratumOpenElement i.val)
  let M := localizationSubmonoid (stratumIdeal E i)
    (stratumOpenElement i.val)
  have hliftNonzero : fieldPatternLocalizationMap f E (xE i) ≠ 0 := by
    change fieldPatternLift f (stratificationColimitMap E xE) ≠ 0 at hx
    rw [fieldPatternLift_of f E xE] at hx
    exact hx
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj M (xE i)
  have hsEq : xE i * algebraMap A L (s : A) = algebraMap A L a := by
    simpa [L] using hs
  have hsmem : IsUnit (f (s : A)) := fieldPatternLocalizationMap_units f E s
  have hmul : fieldPatternLocalizationMap f E (xE i) * f (s : A) = f a := by
    rw [← fieldPatternLocalizationMap_algebraMap f E (s : A),
      ← fieldPatternLocalizationMap_algebraMap f E a, ← map_mul, hsEq]
  have hfa : f a ≠ 0 := by
    intro hzero
    have hzero' : fieldPatternLocalizationMap f E (xE i) * f (s : A) = 0 := by
      rw [hmul, hzero]
    rcases mul_eq_zero.mp hzero' with hmapZero | hszero
    · exact hliftNonzero hmapZero
    · exact hsmem.ne_zero hszero
  let E' := insert a E
  let i' := fieldPatternIndex f E'
  let L' := localizationRing (stratumIdeal E' i')
    (stratumOpenElement i'.val)
  have hai' : a ∈ i'.val := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hfa⟩
  have hunitA : IsUnit (algebraMap A L' a) :=
    isUnit_algebraMap_stratumLocalization E' i' a hai'
  let v : L' := algebraMap A L' (s : A) * ↑(hunitA.unit⁻¹)
  let yE : stratificationRing E' := Pi.single i' v
  let y : stratificationColimitRing (A := A) :=
    stratificationColimitMap E' yE
  have hmapInv : fieldPatternLocalizationMap f E' (↑(hunitA.unit⁻¹)) = (f a)⁻¹ := by
    have hmul' := congrArg (fieldPatternLocalizationMap f E') hunitA.mul_val_inv
    rw [map_mul, map_one] at hmul'
    rw [fieldPatternLocalizationMap_algebraMap f E' a] at hmul'
    exact eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hmul')
  have hstageY : fieldPatternStageMap f E' yE = f (s : A) * (f a)⁻¹ := by
    simp only [fieldPatternStageMap, RingHom.comp_apply, Pi.evalRingHom_apply]
    dsimp [yE, i']
    rw [Pi.single_eq_same, map_mul,
      fieldPatternLocalizationMap_algebraMap f E' (s : A), hmapInv]
  have hxmap : fieldPatternLift f (stratificationColimitMap E xE) =
      fieldPatternStageMap f E xE := fieldPatternLift_of f E xE
  refine ⟨y, ?_⟩
  show fieldPatternLift f
      (stratificationColimitMap E xE *
        stratificationColimitMap E' yE) = 1
  rw [map_mul, fieldPatternLift_of f E xE,
    fieldPatternLift_of f E' yE, hstageY]
  have hmulStage : fieldPatternLocalizationMap f E
      (xE (fieldPatternIndex f E)) * f (s : A) = f a := by
    simpa [i] using hmul
  calc
    fieldPatternStageMap f E xE * (f (s : A) * (f a)⁻¹) =
        (fieldPatternStageMap f E xE * f (s : A)) * (f a)⁻¹ := by ring
    _ = f a * (f a)⁻¹ := by
      show (fieldPatternLocalizationMap f E
        (xE (fieldPatternIndex f E)) * f (s : A)) * (f a)⁻¹ = _
      rw [hmulStage]
    _ = 1 := mul_inv_cancel₀ hfa

private theorem fieldPatternLift_ker_isMaximal
    {A K : Type*} [CommRing A] [Field K] (f : A →+* K) :
    (RingHom.ker (fieldPatternLift f)).IsMaximal := by
  classical
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h
    change fieldPatternLift f 1 = 0 at h
    rw [map_one] at h
    exact one_ne_zero h
  · intro J x hkerJ hxnot hxJ
    have hx : fieldPatternLift f x ≠ 0 := by
      intro hz
      exact hxnot (RingHom.mem_ker.mpr hz)
    obtain ⟨y, hy⟩ := fieldPatternLift_mul_eq_one_of_ne_zero f x hx
    have hker : x * y - 1 ∈ RingHom.ker (fieldPatternLift f) := by
      show fieldPatternLift f (x * y - 1) = 0
      rw [map_sub, hy, map_one, sub_self]
    have hmul : x * y ∈ J := J.mul_mem_right y hxJ
    have hker' : x * y - 1 ∈ J := hkerJ hker
    have hone : (1 : stratificationColimitRing (A := A)) ∈ J := by
      have h := J.sub_mem hmul hker'
      simpa using h
    exact hone

private theorem wLocalSpace_primeSpectrum_of_field
    (K : Type*) [Field K] : WLocalSpace (PrimeSpectrum K) := by
  have : CommRing K := Field.toCommRing
  let hK : IsField K := Field.toIsField K
  have : IsDomain K := hK.isDomain
  have : SpectralSpace (PrimeSpectrum K) := inferInstance
  have : T1Space (PrimeSpectrum K) :=
    (PrimeSpectrum.t1Space_iff_isField).2 hK
  refine ⟨?_, ?_⟩
  · intro x c c' hc hc' hxc hxc'
    exact (t1Space_iff_specializes_imp_eq.mp inferInstance hxc).symm.trans
      (t1Space_iff_specializes_imp_eq.mp inferInstance hxc')
  · have hpoints : (closedPoints (PrimeSpectrum K) : Set (PrimeSpectrum K)) = Set.univ := by
      ext x
      simp only [mem_closedPoints_iff, Set.mem_univ, iff_true]
      exact T1Space.t1 x
    rw [hpoints]
    exact isClosed_univ

private theorem idempotent_mem_iff_of_specializes
    {B : Type*} [CommRing B] {p q : PrimeSpectrum B}
    (hpq : Specializes p q) {e : B} (he : e * e = e) :
    (e ∈ p.asIdeal ↔ e ∈ q.asIdeal) := by
  constructor
  · intro h
    exact (PrimeSpectrum.le_iff_specializes p q).mpr hpq h
  · intro h
    by_contra hp
    have honeSub : 1 - e ∈ p.asIdeal := by
      have hprod' : e * (1 - e) = 0 := by
        calc
          e * (1 - e) = e - e * e := by ring
          _ = 0 := by rw [he]; ring
      have hprod : e * (1 - e) ∈ p.asIdeal := by
        rw [hprod']
        exact p.asIdeal.zero_mem
      rcases p.2.mul_mem_iff_mem_or_mem.mp hprod with he' | hsub
      · exact (hp he').elim
      · exact hsub
    have hsubq : 1 - e ∈ q.asIdeal :=
      (PrimeSpectrum.le_iff_specializes p q).mpr hpq honeSub
    have hone : (1 : B) ∈ q.asIdeal := by
      have := q.asIdeal.add_mem h hsubq
      simpa using this
    exact q.2.ne_top ((Ideal.eq_top_iff_one q.asIdeal).mpr hone)

private theorem stratumIdempotent_quotient_eq_pattern
    {A B : Type*} [CommRing A] [CommRing B]
    [WLocalSpace (PrimeSpectrum B)] (f : A →+* B)
    (E : Finset A) (q : PrimeSpectrum B)
    (hq : IsClosed ({q} : Set (PrimeSpectrum B)))
    [DecidableEq {E' : Finset A // E' ⊆ E}]
    (j : {E' : Finset A // E' ⊆ E}) :
    algebraMap B q.asIdeal.ResidueField (stratumIdempotent f E j) =
      if j = fieldPatternIndex ((algebraMap B q.asIdeal.ResidueField).comp f) E then 1 else 0 := by
  classical
  let ρ : B →+* q.asIdeal.ResidueField := algebraMap B q.asIdeal.ResidueField
  have : q.asIdeal.IsPrime := q.2
  let : Field q.asIdeal.ResidueField := inferInstance
  let fbar : A →+* q.asIdeal.ResidueField := ρ.comp f
  let i₀ := fieldPatternIndex fbar E
  let qA := PrimeSpectrum.comap f q
  have hlocal : qA ∈ locallyClosedPoints
      (stratumIdeal E i₀) (stratumOpenElement i₀.val) := by
    have h := fieldPatternIndex_locallyClosed fbar E
    have e : PrimeSpectrum.comap fbar (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _) = qA :=
      PrimeSpectrum.ext (by ext x; exact Ideal.algebraMap_residueField_eq_zero)
    rwa [e] at h
  have hclopen (k : {E' : Finset A // E' ⊆ E}) :
      q ∈ stratumClopen f E k ↔ qA ∈
        locallyClosedPoints (stratumIdeal E k)
          (stratumOpenElement k.val) := by
    show q ∈ closedPointsClopenLift (stratumClosedPointsClopen f E k) ↔ _
    rw [mem_closedPointsClopenLift_iff]
    constructor
    · rintro ⟨c, hqc, hc⟩
      have hqeq : c.1 = q := hqc.mem_closed hq (by simp)
      simpa [stratumClosedPointsClopen, hqeq] using hc
    · intro hk
      refine ⟨⟨q, hq⟩, specializes_refl q, ?_⟩
      simpa [stratumClosedPointsClopen] using hk
  have hbasic (k : {E' : Finset A // E' ⊆ E}) :
      stratumIdempotent f E k ∉ q.asIdeal ↔ q ∈ stratumClopen f E k := by
    have heq := coe_stratumClopen_eq_basicOpen f E k
    constructor
    · intro h
      have hb : q ∈ (PrimeSpectrum.basicOpen
          (stratumIdempotent f E k)).carrier :=
        (PrimeSpectrum.mem_basicOpen _ _).2 h
      rw [← heq] at hb
      exact hb
    · intro h
      have hb : q ∈ (PrimeSpectrum.basicOpen
          (stratumIdempotent f E k)).carrier := by
        rw [← heq]
        exact h
      exact (PrimeSpectrum.mem_basicOpen _ _).1 hb
  by_cases hj : j = i₀
  · subst j
    have hne : stratumIdempotent f E i₀ ∉ q.asIdeal := by
      apply (hbasic i₀).2
      exact (hclopen i₀).2 hlocal
    have hquotne : ρ (stratumIdempotent f E i₀) ≠ 0 := by
      intro hz
      exact hne ((Ideal.algebraMap_residueField_eq_zero).1 hz)
    have hmul : ρ (stratumIdempotent f E i₀) *
        (ρ (stratumIdempotent f E i₀) - 1) = 0 := by
      have hid := (stratumIdempotent_isIdempotentElem f E i₀).eq
      calc
        _ = ρ (stratumIdempotent f E i₀) *
            ρ (stratumIdempotent f E i₀) - ρ (stratumIdempotent f E i₀) := by ring
        _ = ρ (stratumIdempotent f E i₀ * stratumIdempotent f E i₀) -
            ρ (stratumIdempotent f E i₀) := by rw [← map_mul]
        _ = 0 := by rw [hid]; ring
    rcases mul_eq_zero.mp hmul with hz | hone
    · exact (hquotne hz).elim
    · simpa [i₀, ρ, fbar] using (sub_eq_zero.mp hone)
  · have hnotclopen : q ∉ stratumClopen f E j := by
      intro hqj
      have hjlocal := (hclopen j).mp hqj
      obtain ⟨k, hk, huniq⟩ := existsUnique_mem_stratum f E q
      exact hj (huniq j hjlocal |>.trans (huniq i₀ hlocal).symm)
    have hmem : stratumIdempotent f E j ∈ q.asIdeal := by
      by_contra hnot
      exact hnotclopen ((hbasic j).mp hnot)
    have hz : ρ (stratumIdempotent f E j) = 0 :=
      (Ideal.algebraMap_residueField_eq_zero).2 hmem
    show ρ (stratumIdempotent f E j) = if j = i₀ then 1 else 0
    rw [hz]
    simp [hj]

private theorem closedPrime_eq_of_same_contraction
    {A : Type*} [CommRing A]
    (p q : PrimeSpectrum (stratificationColimitRing (A := A)))
    (hp : IsClosed ({p} : Set (PrimeSpectrum
      (stratificationColimitRing (A := A)))))
    (hq : IsClosed ({q} : Set (PrimeSpectrum
      (stratificationColimitRing (A := A)))))
    (hcontract : PrimeSpectrum.comap
      (stratificationColimitAlgebraMap (A := A)) p =
      PrimeSpectrum.comap
        (stratificationColimitAlgebraMap (A := A)) q) : p = q := by
  classical
  let L := stratificationLimit (A := A)
  have hlift (r : PrimeSpectrum (stratificationColimitRing (A := A)))
      (hr : IsClosed ({r} : Set (PrimeSpectrum (stratificationColimitRing (A := A))))) :
      ∃ z, L.inclusion.base z = specPointEquiv _ r ∧
        (L.inclusion ≫ Spec.map (CommRingCat.ofHom
          (stratificationColimitAlgebraMap (A := A)))).base z =
        specPointEquiv A (PrimeSpectrum.comap (stratificationColimitAlgebraMap (A := A)) r) := by
    have hrz : specPointEquiv _ r ∈ Set.range L.inclusion.base := by
      rw [range_inclusion_eq_closedPoints L]
      exact hr
    obtain ⟨z, hz⟩ := hrz
    refine ⟨z, hz, ?_⟩
    change (Spec.map (CommRingCat.ofHom
      (stratificationColimitAlgebraMap (A := A)))).base (L.inclusion.base z) = _
    rw [hz]
    exact specMap_specPointEquiv _ r
  obtain ⟨zp, hpzp, hmapP⟩ := hlift p hp
  obtain ⟨zq, hqzq, hmapQ⟩ := hlift q hq
  have hpoint : (L.inclusion ≫ Spec.map (CommRingCat.ofHom
      (stratificationColimitAlgebraMap (A := A)))).base zp =
      (L.inclusion ≫ Spec.map (CommRingCat.ofHom
      (stratificationColimitAlgebraMap (A := A)))).base zq := by
    rw [hmapP, hmapQ, hcontract]
  have hz : zp = zq := (stratificationLimit_closedScheme_bijective L).injective hpoint
  apply (specPointEquiv _).injective
  calc
    specPointEquiv _ p = L.inclusion.base zp := hpzp.symm
    _ = L.inclusion.base zq := congrArg L.inclusion.base hz
    _ = specPointEquiv _ q := hqzq

/-- **Stacks 0977.** A ring map `A → B` with `Spec B` w-local factors through `A → A_w` by
exactly one ring map `A_w → B` whose induced map of spectra is w-local. -/
@[stacks 0977]
theorem existsUnique_wLocal_lift
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    (f : A →+* B) [WLocalSpace (Spec (.of B))] :
    ∃! g : stratificationColimitRing (A := A) →+* B,
      g.comp (stratificationColimitAlgebraMap (A := A)) = f ∧
        IsWLocalMap (PrimeSpectrum.comap g) := by
  classical
  have hB : WLocalSpace (Spec (.of B)) := inferInstance
  have : WLocalSpace (PrimeSpectrum B) := hB
  let u : stratificationColimitRing (A := A) →+* B := stratificationColimitLift f
  have hucomp : u.comp (stratificationColimitAlgebraMap (A := A)) = f :=
    stratificationColimitLift_comp_algebraMap f
  have huwlocal : IsWLocalMap (PrimeSpectrum.comap u) := by
    refine ⟨PrimeSpectrum.isSpectralMap_comap u, ?_⟩
    intro q hqclosedPoints
    have hqclosed : IsClosed ({q} : Set (PrimeSpectrum B)) :=
      mem_closedPoints_iff.mp hqclosedPoints
    have : q.asIdeal.IsPrime := q.2
    let K := q.asIdeal.ResidueField
    let ρ : B →+* K := algebraMap B K
    let fK : A →+* K := ρ.comp f
    let : Field K := inferInstance
    have : WLocalSpace (PrimeSpectrum K) := wLocalSpace_primeSpectrum_of_field K
    have hstage (E : Finset A) :
        ρ.comp (stratificationStageMap f E) = fieldPatternStageMap fK E := by
      let _ := stratumIndexFintype E
      let i := fieldPatternIndex fK E
      have hvalues (j : {E' : Finset A // E' ⊆ E}) :=
        stratumIdempotent_quotient_eq_pattern f E q hqclosed j
      have hθbase : (ρ.comp (stratificationStageMap f E)).comp
          (stratificationAlgebraMap E) = fK := by
        ext a
        exact congrArg ρ
          (DFunLike.congr_fun (stratificationStageMap_comp_algebraMap f E) a)
      have hψbase : (fieldPatternStageMap fK E).comp
          (stratificationAlgebraMap E) = fK :=
        fieldPatternStageMap_comp_algebraMap fK E
      have hθone : (ρ.comp (stratificationStageMap f E))
          (Pi.single i (1 : localizationRing
            (stratumIdeal E i) (stratumOpenElement i.val))) = 1 := by
        rw [RingHom.comp_apply, stratificationStageMap_single_one f E i]
        simpa [i, fK, ρ, K] using hvalues i
      have hθzero : ∀ j, j ≠ i → (ρ.comp (stratificationStageMap f E))
          (Pi.single j (1 : localizationRing
            (stratumIdeal E j) (stratumOpenElement j.val))) = 0 := by
        intro j hji
        rw [RingHom.comp_apply, stratificationStageMap_single_one f E j]
        simpa [i, fK, ρ, K, hji] using hvalues j
      have hψone : fieldPatternStageMap fK E (Pi.single i
          (1 : localizationRing (stratumIdeal E i)
            (stratumOpenElement i.val))) = 1 := by
        rw [fieldPatternStageMap, RingHom.comp_apply]
        dsimp [i]
        simp only [Pi.evalRingHom_apply, Pi.single_eq_same]
        exact map_one _
      have hψzero : ∀ j, j ≠ i → fieldPatternStageMap fK E
          (Pi.single j (1 : localizationRing
            (stratumIdeal E j) (stratumOpenElement j.val))) = 0 := by
        intro j hji
        rw [fieldPatternStageMap, RingHom.comp_apply]
        dsimp [i] at hji ⊢
        simp [Pi.evalRingHom_apply, hji]
      exact ringHom_stratificationRing_eq_of_single E fK i
        (ρ.comp (stratificationStageMap f E)) (fieldPatternStageMap fK E)
        hθbase hψbase hθone hψone hθzero hψzero
    have hρu : ρ.comp u = fieldPatternLift fK := by
      apply Ring.DirectLimit.hom_ext
      intro E
      apply RingHom.ext
      intro x
      show ρ (stratificationColimitLift f (stratificationColimitMap E x)) =
        fieldPatternLift fK (stratificationColimitMap E x)
      rw [stratificationColimitLift_of, fieldPatternLift_of]
      exact congrArg (fun θ => θ x) (hstage E)
    have hker : RingHom.ker (ρ.comp u) =
        (PrimeSpectrum.comap u q).asIdeal := by
      ext x
      show ρ (u x) = 0 ↔ u x ∈ q.asIdeal
      exact Ideal.algebraMap_residueField_eq_zero
    have hmax : (PrimeSpectrum.comap u q).asIdeal.IsMaximal := by
      rw [← hker, hρu]
      exact fieldPatternLift_ker_isMaximal fK
    exact mem_closedPoints_iff.mpr
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hmax)
  refine ⟨u, ⟨hucomp, huwlocal⟩, ?_⟩
  intro g hg
  have hbaseg : g.comp (stratificationColimitAlgebraMap (A := A)) = f :=
    hg.1
  have hlocalg : IsWLocalMap (PrimeSpectrum.comap g) := hg.2
  have hgu : g = u := by
    apply Ring.DirectLimit.hom_ext
    intro E
    let φ : stratificationRing E →+* B :=
      g.comp (stratificationColimitMap E)
    have hφbase : φ.comp (stratificationAlgebraMap E) = f := by
      calc
        _ = g.comp ((stratificationColimitMap E).comp
            (stratificationAlgebraMap E)) := by
              simp [φ, RingHom.comp_assoc]
        _ = g.comp (stratificationColimitAlgebraMap (A := A)) := by
              rw [stratificationColimitMap_comp_algebraMap E]
        _ = f := hbaseg
    have hid : ∀ i : {E' : Finset A // E' ⊆ E},
        φ (Pi.single i (1 : localizationRing
          (stratumIdeal E i) (stratumOpenElement i.val))) =
          stratumIdempotent f E i := by
      intro i
      let z : stratificationRing E := Pi.single i 1
      let e := stratumIdempotent f E i
      have hzid : z * z = z := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [z, Pi.single_eq_same]
        · simp [z, hji]
      have hφid : φ z * φ z = φ z := by
        calc
          φ z * φ z = φ (z * z) := (map_mul φ z z).symm
          _ = φ z := congrArg φ hzid
      have heid : e * e = e := (stratumIdempotent_isIdempotentElem f E i).eq
      have hclosedMem (q : PrimeSpectrum B) (hq : IsClosed ({q} : Set _)) :
          φ z ∈ q.asIdeal ↔ e ∈ q.asIdeal := by
        have hqClosedPoints : q ∈ closedPoints (PrimeSpectrum B) :=
          mem_closedPoints_iff.mpr hq
        have hqg : PrimeSpectrum.comap g q ∈
            closedPoints (PrimeSpectrum (stratificationColimitRing (A := A))) :=
          hlocalg.closedPoints_subset_preimage_closedPoints hqClosedPoints
        have hqu : PrimeSpectrum.comap u q ∈
            closedPoints (PrimeSpectrum (stratificationColimitRing (A := A))) :=
          huwlocal.closedPoints_subset_preimage_closedPoints hqClosedPoints
        have hcontract : PrimeSpectrum.comap
            (stratificationColimitAlgebraMap (A := A))
            (PrimeSpectrum.comap g q) = PrimeSpectrum.comap
            (stratificationColimitAlgebraMap (A := A))
            (PrimeSpectrum.comap u q) := by
          apply PrimeSpectrum.ext
          ext a
          show (g.comp (stratificationColimitAlgebraMap (A := A))) a ∈ q.asIdeal ↔
            (u.comp (stratificationColimitAlgebraMap (A := A))) a ∈ q.asIdeal
          rw [DFunLike.congr_fun hbaseg a, DFunLike.congr_fun hucomp a]
        have hpoint := closedPrime_eq_of_same_contraction
          (PrimeSpectrum.comap g q) (PrimeSpectrum.comap u q)
          (mem_closedPoints_iff.mp hqg) (mem_closedPoints_iff.mp hqu) hcontract
        have heval : u (stratificationColimitMap E z) = e := by
          show stratificationColimitLift f (stratificationColimitMap E z) = e
          rw [stratificationColimitLift_of]
          exact stratificationStageMap_single_one f E i
        show g (stratificationColimitMap E z) ∈ q.asIdeal ↔
          e ∈ q.asIdeal
        rw [← heval]
        show stratificationColimitMap E z ∈
            (PrimeSpectrum.comap g q).asIdeal ↔
          stratificationColimitMap E z ∈
            (PrimeSpectrum.comap u q).asIdeal
        rw [hpoint]
      have hmem (p : PrimeSpectrum B) : φ z ∈ p.asIdeal ↔ e ∈ p.asIdeal := by
        obtain ⟨c, ⟨hc, hpc⟩, _⟩ :=
          WLocalSpace.existsUnique_closedPoint_specializes p
        exact (idempotent_mem_iff_of_specializes hpc hφid).trans
          ((hclosedMem c (mem_closedPoints_iff.mp hc)).trans
            (idempotent_mem_iff_of_specializes hpc heid).symm)
      have hbasic : PrimeSpectrum.basicOpen (φ z) =
          PrimeSpectrum.basicOpen e := by
        ext p
        exact not_congr (hmem p)
      have hEq := PrimeSpectrum.basicOpen_injOn_isIdempotentElem hφid heid hbasic
      exact hEq
    have hφstage := stratificationStageMap_eq_of_idempotents f E φ hφbase hid
    apply RingHom.ext
    intro x
    show φ x = u (stratificationColimitMap E x)
    rw [hφstage, stratificationColimitLift_of]
  exact hgu

end AlgebraicGeometry.ProEtale

end
