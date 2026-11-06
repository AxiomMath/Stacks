module

public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.UniformFilterBasis
public import Mathlib.Topology.Instances.TrivSqZeroExt
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Closed immersions: the kernel and the failure of surjectivity

For a closed ideal `J` of a weakly admissible ring `A`, the canonical map from the completion
of `A` along the weak ideals of definition of `A/J` has kernel the closure of `J`.  The second
half of the file constructs a weakly admissible ring for which that canonical map is *not*
surjective, so the closed-immersion criterion cannot be strengthened.

## References

* [Stacks Project, Tag 0ANR](https://stacks.math.columbia.edu/tag/0ANR)
-/

@[expose] public section

namespace TopologicalRing

section

open AlgebraicGeometry CategoryTheory


universe u

/-- A weakly admissible topological ring over a base scheme, together with a closed ideal. -/
public structure ClosedIdealQuotientCompletionSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The topological ring. -/
  A : Type u
  [commRingA : CommRing A]
  [topologicalSpaceA : TopologicalSpace A]
  [isTopologicalRingA : IsTopologicalRing A]
  [isLinearTopologyA : IsLinearTopology A A]
  /-- Weak admissibility of the topological ring. -/
  weaklyAdmissible : TopologicalRing.IsWeaklyAdmissible A
  /-- The structure morphisms of the formal spectrum of `A` over `S`. -/
  overS : ∀ J : TopologicalRing.WeakIdealOfDefinitionIndex A,
    Spec (.of (A ⧸ J.1)) ⟶ S
  /-- Compatibility of the structure morphisms under refinement of weak ideals. -/
  overS_compatible : ∀ (J L :
      TopologicalRing.WeakIdealOfDefinitionIndex A)
      (h : (J.1 : Ideal A) ≤ L.1),
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫ overS J = overS L
  /-- The closed ideal by which we quotient. -/
  K : Ideal A
  /-- Closedness of the ideal in the topology of `A`. -/
  closed_K : IsClosed (K : Set A)

attribute [instance]
  ClosedIdealQuotientCompletionSituation.commRingA
  ClosedIdealQuotientCompletionSituation.topologicalSpaceA
  ClosedIdealQuotientCompletionSituation.isTopologicalRingA
  ClosedIdealQuotientCompletionSituation.isLinearTopologyA

namespace ClosedIdealQuotientCompletionSituation

/-- The inverse-limit completion of the quotient by the closed ideal. -/
public abbrev B (D : ClosedIdealQuotientCompletionSituation.{u}) :=
  TopologicalRing.CompletionOver (Ideal.Quotient.mk D.K)

/-- The canonical map from the original ring to the completion of its quotient. -/
public abbrev canonicalMap (D : ClosedIdealQuotientCompletionSituation.{u}) :
    D.A →+* D.B :=
  TopologicalRing.CompletionOver.canonicalMap (Ideal.Quotient.mk D.K)

end ClosedIdealQuotientCompletionSituation

end

section

universe u

/-- The kernel of the canonical map to the completion of a quotient by a closed ideal
is that ideal. -/
@[stacks 0ANR "kernel"]
public theorem ker_canonicalMap_eq {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (K : Ideal A)
    (hK : IsClosed (K : Set A)) :
    RingHom.ker
      (TopologicalRing.CompletionOver.canonicalMap (Ideal.Quotient.mk K)) = K := by
  let f : A →+* A ⧸ K := Ideal.Quotient.mk K
  apply Ideal.ext; intro x; constructor
  · intro hx; change TopologicalRing.CompletionOver.canonicalMap f x = 0 at hx
    let hb := TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hA
    have hclosure : x ∈ closure (K : Set A) := by
      rw [← hb.iInter_add_right_eq_closure (s := (K : Set A))]
      simp only [Set.mem_iInter]; intro I hI
      have hcoord := congrArg
        (fun y : TopologicalRing.CompletionOver f => y.1 ⟨I, hI⟩) hx
      have hmem : f x ∈ Ideal.map f I := (Ideal.Quotient.eq_zero_iff_mem).mp
        (by simpa [f, TopologicalRing.CompletionOver.canonicalMap] using hcoord)
      obtain ⟨y, hy, hyx⟩ :=
        (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp hmem
      have hsub : x - y ∈ K :=
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem x y).mp hyx.symm
      rw [Set.mem_add]; exact ⟨x - y, hsub, y, hy, by ring⟩
    simpa [hK.closure_eq] using hclosure
  · intro hx; show TopologicalRing.CompletionOver.canonicalMap f x = 0
    apply Subtype.ext; funext J
    have hzero : f x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    simp [f, TopologicalRing.CompletionOver.canonicalMap, hzero]

end

section

universe u

open Filter
open scoped Topology

private abbrev K2 := ZMod 2
private abbrev Q := ℕ →₀ K2

private theorem k2_eq_zero_or_one (c : K2) : c = 0 ∨ c = 1 := by
  revert c
  decide

private def tail (n : ℕ) : AddSubgroup Q where
  carrier := {x | ∀ i, i < n → x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  neg_mem' := by
    intro x hx i hi
    simp [hx i hi]

@[instance_reducible]
private def qBasis : AddGroupFilterBasis Q where
  sets := Set.range (fun n : ℕ => (tail n : Set Q))
  nonempty := ⟨tail 0, ⟨0, rfl⟩⟩
  inter_sets := by
    rintro U V ⟨m, rfl⟩ ⟨n, rfl⟩
    refine ⟨tail (max m n), ⟨max m n, rfl⟩, ?_⟩
    exact fun x hx => ⟨fun i hi => hx i (by omega), fun i hi => hx i (by omega)⟩
  zero' := by
    rintro U ⟨n, rfl⟩
    exact (tail n).zero_mem
  add' := by
    rintro U ⟨n, rfl⟩
    refine ⟨(tail n : Set Q), ⟨n, rfl⟩, ?_⟩
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact (tail n).add_mem ha hb
  neg' := by
    rintro U ⟨n, rfl⟩
    refine ⟨(tail n : Set Q), ⟨n, rfl⟩, ?_⟩
    rintro x hx
    exact (tail n).neg_mem hx
  conj' := by
    intro x U hU
    obtain ⟨n, rfl⟩ := hU
    refine ⟨tail n, ⟨n, rfl⟩, ?_⟩
    intro y hy
    change x + y + -x ∈ (tail n : Set Q)
    rwa [show x + y + -x = y by abel]

private noncomputable instance qTopology : TopologicalSpace Q := qBasis.topology

private noncomputable instance qTopologicalAddGroup : IsTopologicalAddGroup Q :=
  qBasis.isTopologicalAddGroup

private noncomputable instance qUniformSpace : UniformSpace Q := qBasis.uniformSpace

private noncomputable instance qUniformAddGroup : IsUniformAddGroup Q :=
  qBasis.isUniformAddGroup

private theorem qBasis_intersection_eq_zero : ⋂₀ qBasis.sets = ({0} : Set Q) := by
  ext x
  simp only [Set.mem_sInter, Set.mem_singleton_iff]
  constructor
  · intro hx
    apply Finsupp.ext
    intro i
    by_contra hi
    have htail : x ∈ tail (i + 1) := hx (tail (i + 1)) ⟨i + 1, rfl⟩
    exact hi (htail i (by omega))
  · rintro rfl U hU
    obtain ⟨n, rfl⟩ := hU
    exact (tail n).zero_mem

private noncomputable instance qT2 : T2Space Q :=
  (qBasis.t2Space_iff rfl).2 qBasis_intersection_eq_zero

private theorem tail_mono {m n : ℕ} (h : n ≤ m) : tail m ≤ tail n := by
  intro x hx i hi
  exact hx i (by omega)

private def box (J : Finset ℕ) (n : ℕ → ℕ) : AddSubgroup (ℕ → Q) where
  carrier := {x | (∀ i, i ∈ J → x i = 0) ∧ ∀ i, i ∉ J → x i ∈ tail (n i)}
  zero_mem' := by
    constructor
    · simp
    · intro i hi
      exact (tail (n i)).zero_mem
  add_mem' := by
    intro x y hx hy
    constructor
    · intro i hi
      simp [hx.1 i hi, hy.1 i hi]
    · intro i hi
      exact (tail (n i)).add_mem (hx.2 i hi) (hy.2 i hi)
  neg_mem' := by
    intro x hx
    constructor
    · intro i hi
      simp [hx.1 i hi]
    · intro i hi
      exact (tail (n i)).neg_mem (hx.2 i hi)

@[instance_reducible]
private def boxBasis : AddGroupFilterBasis (ℕ → Q) where
  sets := Set.range (fun p : Finset ℕ × (ℕ → ℕ) => (box p.1 p.2 : Set (ℕ → Q)))
  nonempty := ⟨box ∅ 0, ⟨(∅, 0), rfl⟩⟩
  inter_sets := by
    rintro U V ⟨p, rfl⟩ ⟨q, rfl⟩
    refine ⟨box (p.1 ∪ q.1) (fun i => max (p.2 i) (q.2 i)),
      ⟨(p.1 ∪ q.1, fun i => max (p.2 i) (q.2 i)), rfl⟩, ?_⟩
    intro x hx
    change x ∈ (box p.1 p.2 : Set (ℕ → Q)) ∧ x ∈ (box q.1 q.2 : Set (ℕ → Q))
    constructor
    · constructor
      · intro i hi
        exact hx.1 i (Finset.mem_union_left _ hi)
      · intro i hi
        by_cases hq : i ∈ q.1
        · have hz := hx.1 i (Finset.mem_union_right _ hq)
          simp [hz]
        · have hi' : i ∉ p.1 ∪ q.1 := by simpa [Finset.mem_union] using And.intro hi hq
          exact tail_mono (le_max_left _ _) (hx.2 i hi')
    · constructor
      · intro i hi
        exact hx.1 i (Finset.mem_union_right _ hi)
      · intro i hi
        by_cases hp : i ∈ p.1
        · have hz := hx.1 i (Finset.mem_union_left _ hp)
          simp [hz]
        · have hi' : i ∉ p.1 ∪ q.1 := by simpa [Finset.mem_union] using And.intro hp hi
          exact tail_mono (le_max_right _ _) (hx.2 i hi')
  zero' := by
    rintro U ⟨p, rfl⟩
    exact (box p.1 p.2).zero_mem
  add' := by
    rintro U ⟨p, rfl⟩
    refine ⟨(box p.1 p.2 : Set (ℕ → Q)), ⟨p, rfl⟩, ?_⟩
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact (box p.1 p.2).add_mem ha hb
  neg' := by
    rintro U ⟨p, rfl⟩
    refine ⟨(box p.1 p.2 : Set (ℕ → Q)), ⟨p, rfl⟩, ?_⟩
    rintro x hx
    change -x ∈ (box p.1 p.2 : Set (ℕ → Q))
    exact (box p.1 p.2).neg_mem hx
  conj' := by
    intro x U hU
    obtain ⟨p, rfl⟩ := hU
    refine ⟨box p.1 p.2, ⟨p, rfl⟩, ?_⟩
    intro y hy
    change x + y + -x ∈ (box p.1 p.2 : Set (ℕ → Q))
    rwa [show x + y + -x = y by abel]

private noncomputable instance boxTopology : TopologicalSpace (ℕ → Q) := boxBasis.topology

private theorem boxBasis_intersection_eq_zero :
    ⋂₀ boxBasis.sets = ({0} : Set (ℕ → Q)) := by
  ext x
  simp only [Set.mem_sInter, Set.mem_singleton_iff]
  constructor
  · intro hx
    funext i
    by_contra hi
    have hp : x ∈ box ({i} : Finset ℕ) 0 :=
      hx (box ({i} : Finset ℕ) 0) ⟨({i}, 0), rfl⟩
    have hzero : x i = 0 := hp.1 i (by simp)
    exact hi hzero
  · rintro rfl U hU
    obtain ⟨p, rfl⟩ := hU
    exact (box p.1 p.2).zero_mem

private noncomputable instance boxT2 : T2Space (ℕ → Q) :=
  (boxBasis.t2Space_iff rfl).2 boxBasis_intersection_eq_zero

private noncomputable instance boxTopologicalAddGroup :
    IsTopologicalAddGroup (ℕ → Q) := boxBasis.isTopologicalAddGroup

private noncomputable instance boxUniformSpace : UniformSpace (ℕ → Q) :=
  boxBasis.uniformSpace

private noncomputable instance boxUniformAddGroup : IsUniformAddGroup (ℕ → Q) :=
  boxBasis.isUniformAddGroup

private theorem box_coord_eventually_constant {f : Filter (ℕ → Q)} (hf : Cauchy f)
    (i : ℕ) : ∃ a : Q, {x | x i = a} ∈ f := by
  have hci := (boxBasis.cauchy_iff (F := f)).mp hf
  let : f.NeBot := hci.1
  obtain ⟨M, hM, hdiff⟩ := hci.2 (box {i} 0) ⟨({i}, 0), rfl⟩
  obtain ⟨z, hz⟩ := Filter.nonempty_of_mem hM
  refine ⟨z i, Filter.mem_of_superset hM fun y hy => ?_⟩
  have hzero : z i - y i = 0 := (hdiff y hy z hz).1 i (by simp)
  exact (sub_eq_zero.mp hzero).symm

private theorem box_completeSpace : CompleteSpace (ℕ → Q) := by
  apply completeSpace_of_isComplete_univ
  intro f hf _
  let : f.NeBot := hf.1
  choose a ha using fun i => box_coord_eventually_constant hf i
  refine ⟨a, trivial, fun S hS => ?_⟩
  rcases (boxBasis.nhds_hasBasis a).mem_iff.mp hS with ⟨T, hT, hTS⟩
  obtain ⟨p, rfl⟩ := hT
  have hci := (boxBasis.cauchy_iff (F := f)).mp hf
  obtain ⟨M, hM, hdiff⟩ := hci.2 (box p.1 p.2) ⟨p, rfl⟩
  obtain ⟨z, hz⟩ := Filter.nonempty_of_mem hM
  have hzx : z - a ∈ box p.1 p.2 := by
    constructor
    · intro i hi
      obtain ⟨w, hw, hwi⟩ := Filter.nonempty_of_mem (Filter.inter_mem hM (ha i))
      exact sub_eq_zero.mpr ((sub_eq_zero.mp ((hdiff z hz w hw).1 i hi)).symm.trans hwi)
    · intro i hi
      obtain ⟨w, hw, hwi⟩ := Filter.nonempty_of_mem (Filter.inter_mem hM (ha i))
      have htail : w i - z i ∈ tail (p.2 i) := (hdiff z hz w hw).2 i hi
      rw [show w i = a i from hwi] at htail
      simpa using (tail (p.2 i)).neg_mem htail
  have hMsub : M ⊆ (fun y => a + y) '' (box p.1 p.2 : Set (ℕ → Q)) := by
    intro y hy
    have hyx : y - a ∈ box p.1 p.2 := by
      convert (box p.1 p.2).add_mem (hdiff z hz y hy) hzx using 1
      abel
    exact ⟨y - a, hyx, by simp⟩
  exact Filter.mem_of_superset hM (hMsub.trans hTS)

private def outerSubmodule : Submodule K2 (ℕ → Q) where
  carrier := {x | {i | x i ≠ 0}.Finite}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    apply hx.union hy |>.subset
    intro i hi
    by_contra h
    have hxy : x i = 0 ∧ y i = 0 := by
      simpa [Set.mem_union, Set.mem_setOf_eq] using h
    simp [hxy.1, hxy.2] at hi
  smul_mem' := by
    intro c x hx
    apply hx.subset
    intro i hi
    by_contra h
    have hxzero : x i = 0 := by simpa using h
    simp [hxzero] at hi

private abbrev V := outerSubmodule

private noncomputable instance vTopology : TopologicalSpace V :=
  TopologicalSpace.induced (fun x : V => (x : ℕ → Q)) boxTopology

private def boxSubmodule (J : Finset ℕ) (n : ℕ → ℕ) : Submodule K2 (ℕ → Q) where
  carrier := box J n
  zero_mem' := (box J n).zero_mem
  add_mem' := (box J n).add_mem
  smul_mem' := by
    intro c x hx
    rcases k2_eq_zero_or_one c with rfl | rfl
    · simp
    · simpa using hx

private noncomputable def vBoxSubmodule (J : Finset ℕ) (n : ℕ → ℕ) : Submodule K2 V :=
  (boxSubmodule J n).comap V.subtype

private theorem v_nhds_hasBasis : (𝓝 (0 : V)).HasBasis
    (fun _ : Finset ℕ × (ℕ → ℕ) => True)
    (fun p => ((vBoxSubmodule p.1 p.2).toAddSubgroup : Set V)) := by
  rw [nhds_induced]
  have h := (boxBasis.nhds_zero_hasBasis.comap (fun x : V => (x : ℕ → Q)))
  refine h.to_hasBasis ?_ ?_
  · intro U hU
    obtain ⟨p, rfl⟩ := hU
    exact ⟨p, trivial, by rfl⟩
  · intro p hp
    exact ⟨box p.1 p.2, ⟨p, rfl⟩, by rfl⟩

private noncomputable instance vLinearTopology : IsLinearTopology K2 V := by
  apply IsLinearTopology.mk_of_hasBasis' K2 (S := AddSubgroup V)
    (p := fun _ : Finset ℕ × (ℕ → ℕ) => True)
    (s := fun p => (vBoxSubmodule p.1 p.2).toAddSubgroup) v_nhds_hasBasis ?_
  intro U c x hx
  rcases k2_eq_zero_or_one c with rfl | rfl
  · simp
  · simpa using hx

private theorem q_exists_nonzero_coeff (q : Q) (hq : q ≠ 0) : ∃ i, q i ≠ 0 := by
  by_contra! h
  exact hq (Finsupp.ext h)

private noncomputable def qMarker (q : Q) (hq : q ≠ 0) : ℕ :=
  Classical.choose (q_exists_nonzero_coeff q hq)

private theorem qMarker_spec (q : Q) (hq : q ≠ 0) : q (qMarker q hq) ≠ 0 :=
  (Classical.choose_spec (q_exists_nonzero_coeff q hq))

private theorem outer_isClosed : IsClosed (outerSubmodule : Set (ℕ → Q)) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hxnot : ¬ {i | x i ≠ 0}.Finite := by simpa [outerSubmodule] using hx
  let n : ℕ → ℕ := fun i => if h : x i ≠ 0 then qMarker (x i) h + 1 else 0
  have hnotTail : ∀ i, x i ≠ 0 → x i ∉ tail (n i) := by
    intro i hi ht
    have hm := qMarker_spec (x i) hi
    have hz : x i (qMarker (x i) hi) = 0 := ht _ (by simp [n, hi])
    exact hm hz
  refine (boxBasis.nhds_hasBasis x).mem_iff.mpr ?_
  refine ⟨(box ∅ n : Set (ℕ → Q)), ⟨(∅, n), rfl⟩, ?_⟩
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  change z ∈ box ∅ n at hz
  intro hyfinite
  have hnotSub : ¬ ({i | x i ≠ 0} ⊆ {i | (x + z) i ≠ 0}) := fun hsub =>
    hxnot (hyfinite.subset hsub)
  obtain ⟨i, hxi, hyi⟩ := Set.not_subset.mp hnotSub
  have hyzero : (x + z) i = 0 := by simpa [Set.mem_setOf_eq] using hyi
  have hzmem : z i ∈ tail (n i) := hz.2 i (by simp)
  have hzne : z i = -x i := eq_neg_of_add_eq_zero_right (by simpa using hyzero)
  have hxTail : x i ∈ tail (n i) := by simpa [hzne] using (tail (n i)).neg_mem hzmem
  exact hnotTail i hxi hxTail

private noncomputable instance vCompleteSpace : CompleteSpace V := by
  let : CompleteSpace (ℕ → Q) := box_completeSpace
  exact outer_isClosed.completeSpace_coe

private noncomputable instance vUniformSpace : UniformSpace V :=
  UniformSpace.comap (fun x : V => (x : ℕ → Q)) boxUniformSpace

private def vValAddHom : V →+ (ℕ → Q) where
  toFun := fun x => x.1
  map_zero' := rfl
  map_add' _ _ := rfl

private noncomputable instance vUniformAddGroup : IsUniformAddGroup V :=
  IsUniformAddGroup.comap vValAddHom

private noncomputable instance k2Topology : TopologicalSpace K2 := ⊥
private noncomputable instance k2Discrete : DiscreteTopology K2 := discreteTopology_bot K2
private noncomputable instance k2UniformSpace : UniformSpace K2 := ⊥
private noncomputable instance k2UniformAddGroup : IsUniformAddGroup K2 := inferInstance

private noncomputable instance vContinuousConstSMul : ContinuousConstSMul K2 V where
  continuous_const_smul c := by
    rcases k2_eq_zero_or_one c with rfl | rfl
    · simpa using (continuous_const : Continuous fun _ : V => (0 : V))
    · simp only [one_smul]
      exact continuous_id

private noncomputable instance vContinuousSMul : ContinuousSMul K2 V :=
  ⟨(continuous_prod_of_discrete_left).2 fun c => continuous_const_smul c⟩

private abbrev A := TrivSqZeroExt K2 V

private noncomputable instance aTopologicalRing : IsTopologicalRing A := inferInstance

private noncomputable def vSum (x : V) : Q := ∑ i ∈ x.2.toFinset, x.1 i

private lemma v_support_mem (x : V) (i : ℕ) : i ∈ x.2.toFinset ↔ x.1 i ≠ 0 := by
  simpa using (Set.Finite.mem_toFinset x.2 (a := i))

private lemma vSum_eq_of_superset {x : V} {s : Finset ℕ}
    (hs : x.2.toFinset ⊆ s) :
    (∑ i ∈ x.2.toFinset, x.1 i) = ∑ i ∈ s, x.1 i := by
  apply Finset.sum_subset hs
  intro i hi hnot
  have hxi : x.1 i = 0 := by
    by_contra hne
    exact hnot ((v_support_mem x i).2 hne)
  simp [hxi]

private noncomputable def vSumLinear : V →ₗ[K2] Q where
  toFun := vSum
  map_add' x y := by
    let s := x.2.toFinset ∪ y.2.toFinset
    have hxs : x.2.toFinset ⊆ s := Finset.subset_union_left
    have hys : y.2.toFinset ⊆ s := Finset.subset_union_right
    have hxys : (x + y).2.toFinset ⊆ s := by
      intro i hi
      by_contra h
      have hnot : i ∉ x.2.toFinset ∧ i ∉ y.2.toFinset := by
        simpa [s, Finset.mem_union] using h
      have hx0 : x.1 i = 0 := by
        by_contra hn
        exact hnot.1 ((v_support_mem x i).2 hn)
      have hy0 : y.1 i = 0 := by
        by_contra hn
        exact hnot.2 ((v_support_mem y i).2 hn)
      have hxy : (x + y).1 i = 0 := by simp [hx0, hy0]
      have hi' : (x + y).1 i ≠ 0 := (v_support_mem (x + y) i).1 hi
      simp [hxy] at hi'
    rw [vSum, vSum, vSum,
      vSum_eq_of_superset hxs, vSum_eq_of_superset hys,
      vSum_eq_of_superset hxys]
    rw [← Finset.sum_add_distrib]
    congr 1
  map_smul' c x := by
    rcases k2_eq_zero_or_one c with rfl | rfl <;> simp [vSum]

private lemma vSum_mem_tail {x : V} {n : ℕ} (hx : ∀ i, x.1 i ∈ tail n) :
    vSum x ∈ tail n := by
  classical
  let s := x.2.toFinset
  show (∑ i ∈ s, x.1 i) ∈ tail n
  induction s using Finset.induction_on with
  | empty => simp [tail]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (tail n).add_mem (hx i) ih

private theorem vSum_continuousAt_zero :
    ContinuousAt (vSumLinear : V → Q) 0 := by
  rw [ContinuousAt, vSumLinear.map_zero]
  refine (v_nhds_hasBasis.tendsto_iff (qBasis.nhds_zero_hasBasis)).2 ?_
  intro U hU
  obtain ⟨n, rfl⟩ := hU
  refine ⟨(∅, fun _ => n), trivial, ?_⟩
  intro x hx
  have hx' : x.1 ∈ box ∅ (fun _ => n) := hx
  have htail : ∀ i, x.1 i ∈ tail n := by
    intro i
    exact hx'.2 i (by simp)
  exact vSum_mem_tail htail

private theorem vSum_continuous : Continuous (vSumLinear : V → Q) :=
  @continuous_of_continuousAt_zero V vTopology (inferInstance : AddGroup V)
    (inferInstance : IsTopologicalAddGroup V) Q (V →ₗ[K2] Q) (inferInstance : AddZeroClass Q)
    qTopology (inferInstance : ContinuousAdd Q) inferInstance inferInstance
    vSumLinear vSum_continuousAt_zero

private noncomputable def vCoord (i : ℕ) : Q →ₗ[K2] V where
  toFun q := ⟨fun j => if j = i then q else 0, by
    apply Set.Finite.subset (Set.finite_singleton i)
    intro j hj
    by_contra hji
    have hji' : j ≠ i := by simpa using hji
    change (if j = i then q else 0) ≠ 0 at hj
    simp [hji'] at hj⟩
  map_add' q r := by
    apply Subtype.ext
    funext j
    by_cases hji : j = i <;> simp [hji]
  map_smul' c q := by
    apply Subtype.ext
    funext j
    by_cases hji : j = i <;> simp [hji]

private lemma vSum_coord (i : ℕ) (q : Q) : vSum (vCoord i q) = q := by
  have hs : (vCoord i q).2.toFinset ⊆ {i} := by
    intro j hj
    by_contra hji
    have hji' : j ≠ i := by simpa using hji
    have hval : (vCoord i q).1 j = 0 := by simp [vCoord, hji']
    exact ((v_support_mem (vCoord i q) j).1 hj) hval
  unfold vSum
  rw [vSum_eq_of_superset hs]
  simp [vCoord]

private def aIdeal (p : Finset ℕ × (ℕ → ℕ)) : Ideal A where
  carrier := {x | x.fst = 0 ∧ x.snd ∈ vBoxSubmodule p.1 p.2}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    constructor
    · simp [hx.1, hy.1]
    · exact (vBoxSubmodule p.1 p.2).add_mem hx.2 hy.2
  smul_mem' := by
    intro a x hx
    change a * x ∈ {x | x.fst = 0 ∧ x.snd ∈ vBoxSubmodule p.1 p.2}
    constructor
    · simp [TrivSqZeroExt.fst_mul, hx.1]
    · rw [TrivSqZeroExt.snd_mul, hx.1]
      simpa using (vBoxSubmodule p.1 p.2).smul_mem a.fst hx.2

private theorem a_nhds_hasBasis : (𝓝 (0 : A)).HasBasis
    (fun _ : Finset ℕ × (ℕ → ℕ) => True) (fun p => (aIdeal p : Set A)) := by
  rw [TrivSqZeroExt.nhds_def]
  have hk : (𝓝 (0 : K2)).HasBasis (fun _ : Unit => True)
      (fun _ => ({0} : Set K2)) := by
    rw [nhds_discrete]
    exact hasBasis_pure _
  have h := hk.prod v_nhds_hasBasis
  refine h.to_hasBasis ?_ ?_
  · intro p hp
    refine ⟨p.2, trivial, ?_⟩
    intro x hx
    change x.fst = 0 ∧ x.snd ∈ vBoxSubmodule p.2.1 p.2.2 at hx
    show x ∈ aIdeal p.2
    exact hx
  · intro p hp
    refine ⟨((), p), ⟨trivial, hp⟩, ?_⟩
    intro x hx
    change x.fst = 0 ∧ x.snd ∈ vBoxSubmodule p.1 p.2 at hx
    show x ∈ aIdeal p
    exact hx

private noncomputable instance aLinearTopology : IsLinearTopology A A := by
  let : AddSubmonoidClass (Submodule A A) A := Submodule.addSubmonoidClass
  exact IsLinearTopology.mk_of_hasBasis' A (S := Submodule A A)
    (p := fun _ : Finset ℕ × (ℕ → ℕ) => True) (s := aIdeal) a_nhds_hasBasis
    (fun I r x hx => I.smul_mem r hx)

private noncomputable instance vT2 : T2Space V :=
  T2Space.of_injective_continuous Subtype.val_injective continuous_subtype_val

private noncomputable instance aT2 : T2Space A := inferInstance

private noncomputable instance aTopologicalAddGroup : IsTopologicalAddGroup A := by
  constructor

private noncomputable instance aUniformAddGroup : IsUniformAddGroup A := by
  change IsUniformAddGroup (K2 × V)
  infer_instance

private noncomputable def nilIdeal : Ideal A := TrivSqZeroExt.kerIdeal K2 V

private theorem nilIdeal_open : IsOpen (nilIdeal : Set A) := by
  have hset : (nilIdeal : Set A) = {x | x.fst = 0} := by
    ext x
    rfl
  rw [hset]
  exact (isOpen_discrete ({0} : Set K2)).preimage TrivSqZeroExt.continuous_fst

private theorem nilIdeal_topologicallyNilpotent (x : A) (hx : x ∈ nilIdeal) :
    IsTopologicallyNilpotent x := by
  have hx' : x = TrivSqZeroExt.inr x.snd :=
    (TrivSqZeroExt.mem_kerIdeal_iff_inr K2 V x).mp hx
  have hx2 : x ^ 2 = 0 := by
    rw [hx', pow_two, TrivSqZeroExt.inr_mul_inr]
  unfold IsTopologicallyNilpotent
  have heq : (fun n : ℕ => x ^ n) =ᶠ[atTop] fun _ => (0 : A) := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨2, fun n hn => hn⟩] with n hn
    have hpow : x ^ n = 0 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      simp [pow_add, hx2]
    exact hpow
  exact heq.tendsto

private theorem aWeaklyAdmissible : TopologicalRing.IsWeaklyAdmissible A := by
  refine ⟨⟨nilIdeal, ⟨nilIdeal_open, nilIdeal_topologicallyNilpotent⟩⟩, ?_, ?_⟩
  · let : UniformSpace A := TrivSqZeroExt.instUniformSpace
    have hright : IsTopologicalAddGroup.rightUniformSpace A =
        (inferInstance : UniformSpace A) := IsUniformAddGroup.rightUniformSpace_eq
    rw [hright]
    exact TrivSqZeroExt.instCompleteSpace (R := K2) (M := V)
  · infer_instance

private noncomputable instance qContinuousConstSMul : ContinuousConstSMul K2 Q where
  continuous_const_smul c := by
    rcases k2_eq_zero_or_one c with rfl | rfl
    · simpa using (continuous_const : Continuous fun _ : Q => (0 : Q))
    · simp only [one_smul]
      exact continuous_id

private noncomputable instance qContinuousSMul : ContinuousSMul K2 Q :=
  ⟨(continuous_prod_of_discrete_left).2 fun c => continuous_const_smul c⟩

private abbrev Aq := TrivSqZeroExt K2 Q

private noncomputable instance aqTopologicalRing : IsTopologicalRing Aq := inferInstance

private noncomputable instance aqT2 : T2Space Aq := inferInstance

private noncomputable def phi : A →+* Aq := (TrivSqZeroExt.map vSumLinear).toRingHom

private theorem phi_apply (x : A) : phi x = (x.fst, vSum x.snd) := by
  ext
  · simp [phi, TrivSqZeroExt.fst_map]
  · simp [phi, TrivSqZeroExt.snd_map, vSumLinear]

private theorem phi_surjective : Function.Surjective phi := by
  intro x
  let y : A := (x.fst, vCoord 0 x.snd)
  refine ⟨y, ?_⟩
  rw [phi_apply]
  apply Prod.ext
  · rfl
  · exact vSum_coord 0 x.snd

private theorem phi_continuous : Continuous phi := by
  let : TopologicalSpace A :=
    TopologicalSpace.induced TrivSqZeroExt.fst k2Topology ⊓
      TopologicalSpace.induced TrivSqZeroExt.snd vTopology
  let : TopologicalSpace Aq :=
    TopologicalSpace.induced TrivSqZeroExt.fst k2Topology ⊓
      TopologicalSpace.induced TrivSqZeroExt.snd qTopology
  have hfstEq : TrivSqZeroExt.fst ∘ phi = TrivSqZeroExt.fst := by
    funext x
    show TrivSqZeroExt.fst (phi x) = x.fst
    rw [phi_apply]
    rfl
  have hsndEq : TrivSqZeroExt.snd ∘ phi = vSumLinear ∘ TrivSqZeroExt.snd := by
    funext x
    show TrivSqZeroExt.snd (phi x) = vSumLinear x.snd
    rw [phi_apply]
    rfl
  have hfst : Continuous (TrivSqZeroExt.fst ∘ phi) := by
    rw [hfstEq]
    exact TrivSqZeroExt.continuous_fst
  have hsnd : Continuous (TrivSqZeroExt.snd ∘ phi) := by
    rw [hsndEq]
    exact vSum_continuous.comp TrivSqZeroExt.continuous_snd
  exact continuous_inf_rng.mpr
    ⟨continuous_induced_rng.mpr hfst, continuous_induced_rng.mpr hsnd⟩

private noncomputable def qPrefix (n : ℕ) : Q :=
  ∑ i ∈ Finset.range n, Finsupp.single i (1 : K2)

private lemma qPrefix_apply (n i : ℕ) : qPrefix n i = if i < n then 1 else 0 := by
  classical
  simp [qPrefix, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.mem_range]

private lemma qPrefix_diff_mem_tail {n m : ℕ} (hnm : n ≤ m) :
    qPrefix m - qPrefix n ∈ tail n := by
  intro i hi
  have him : i < m := lt_of_lt_of_le hi hnm
  show qPrefix m i - qPrefix n i = 0
  rw [qPrefix_apply, qPrefix_apply]
  simp [hi, him]

private lemma vCoord_mem_vBox {p : Finset ℕ × (ℕ → ℕ)} {i : ℕ} {q : Q}
    (hi : i ∉ p.1) (hq : q ∈ tail (p.2 i)) :
    vCoord i q ∈ vBoxSubmodule p.1 p.2 := by
  show (vCoord i q : V).1 ∈ box p.1 p.2
  constructor
  · intro j hj
    have hji : j ≠ i := by
      intro hji
      subst j
      exact hi hj
    simp [vCoord, hji]
  · intro j hj
    by_cases hji : j = i
    · subst j
      simpa [vCoord] using hq
    · have hz : (vCoord i q : V).1 j = 0 := by simp [vCoord, hji]
      rw [hz]
      exact (tail (p.2 j)).zero_mem

private abbrev A2 := ULift.{u} A
private abbrev K2Lift := ULift.{u} K2

private noncomputable instance a2CommRing : CommRing A2 := ULift.commRing

private noncomputable def a2Ideal (p : Finset ℕ × (ℕ → ℕ)) : Ideal A2 :=
  Ideal.comap (ULift.ringEquiv (R := A)).toRingHom (aIdeal p)

private theorem a2_nhds_hasBasis : (𝓝 (0 : A2)).HasBasis
    (fun _ : Finset ℕ × (ℕ → ℕ) => True) (fun p => (a2Ideal p : Set A2)) := by
  rw [ULift.topologicalSpace, nhds_induced]
  convert a_nhds_hasBasis.comap (ULift.down : A2 → A) using 1
  funext p
  ext x
  rfl

private noncomputable instance a2LinearTopology : IsLinearTopology A2 A2 := by
  let : AddSubmonoidClass (Submodule A2 A2) A2 := Submodule.addSubmonoidClass
  exact IsLinearTopology.mk_of_hasBasis' A2 (S := Submodule A2 A2)
    (p := fun _ : Finset ℕ × (ℕ → ℕ) => True) (s := a2Ideal) a2_nhds_hasBasis
    (fun I r x hx => I.smul_mem r hx)

private noncomputable instance a2TopologicalRing : IsTopologicalRing A2 := inferInstance

private noncomputable instance a2TopologicalAddGroup : IsTopologicalAddGroup A2 := by
  constructor

private noncomputable instance a2T2 : T2Space A2 :=
  T2Space.of_injective_continuous ULift.down_injective continuous_uliftDown

private noncomputable instance a2UniformSpace : UniformSpace A2 :=
  UniformSpace.comap ULift.down (IsTopologicalAddGroup.rightUniformSpace A)

private noncomputable instance a2UniformAddGroup : IsUniformAddGroup A2 :=
  by
    let : AddGroup A := (inferInstance : AddCommGroup A).toAddGroup
    let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    exact IsUniformAddGroup.comap (ULift.ringEquiv (R := A)).toAddMonoidHom

private noncomputable def a2NilIdeal : Ideal A2 :=
  Ideal.comap (ULift.ringEquiv (R := A)).toRingHom nilIdeal

private theorem a2NilIdeal_open : IsOpen (a2NilIdeal : Set A2) := by
  have hset : (a2NilIdeal : Set A2) = ULift.down ⁻¹' (nilIdeal : Set A) := by
    ext x
    rfl
  rw [hset]
  exact nilIdeal_open.preimage continuous_uliftDown

private theorem a2NilIdeal_topologicallyNilpotent (x : A2)
    (hx : x ∈ a2NilIdeal) : IsTopologicallyNilpotent x := by
  have hx' : x.down ∈ nilIdeal := hx
  have hA : IsTopologicallyNilpotent x.down :=
    nilIdeal_topologicallyNilpotent x.down hx'
  -- `A2` carries the `ULift` ring structure and the `ULift` topology, so powers
  -- and `0` are computed on the coordinate: transport the limit along
  -- `ULift.up`.  Going through `IsTopologicallyNilpotent.map` instead leaves
  -- `ULift`'s universe argument a metavariable while its
  -- `MonoidWithZeroHomClass` instance is searched for, and the search fails.
  exact (continuous_uliftUp.tendsto (0 : A)).comp hA

private theorem a2_complete_rightUniform :
    @CompleteSpace A2 (IsTopologicalAddGroup.rightUniformSpace A2) := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : CompleteSpace A := aWeaklyAdmissible.2.1
  have h : CompleteSpace A2 := ULift.instCompleteSpace
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact h

private theorem a2WeaklyAdmissible : TopologicalRing.IsWeaklyAdmissible A2 := by
  refine ⟨⟨a2NilIdeal, ⟨a2NilIdeal_open, a2NilIdeal_topologicallyNilpotent⟩⟩, ?_, ?_⟩
  · exact a2_complete_rightUniform
  · infer_instance

private noncomputable def weakBox2 (p : Finset ℕ × (ℕ → ℕ)) :
    TopologicalRing.WeakIdealOfDefinitionIndex A2 :=
  ⟨a2Ideal p, by
    constructor
    · have hmemI : (a2Ideal p : Set A2) ∈ 𝓝 (0 : A2) :=
        (a2_nhds_hasBasis.mem_iff).2 ⟨p, trivial, subset_rfl⟩
      let I : AddSubgroup A2 :=
        @Submodule.toAddSubgroup A2 A2 inferInstance inferInstance inferInstance (a2Ideal p)
      have hmem : (I : Set A2) ∈ 𝓝 (0 : A2) := by
        change (a2Ideal p : Set A2) ∈ 𝓝 (0 : A2)
        exact hmemI
      exact I.isOpen_of_mem_nhds hmem
    · intro x hx
      apply a2NilIdeal_topologicallyNilpotent x
      change ((ULift.ringEquiv (R := A)) x) ∈ nilIdeal
      change ((ULift.ringEquiv (R := A)) x).fst = 0
      exact hx.1⟩

private noncomputable def phi2 : A2 →+* Aq :=
  phi.comp (ULift.ringEquiv (R := A)).toRingHom

private theorem phi2_apply (x : A2) : phi2 x = (x.down.fst, vSum x.down.snd) := by
  show phi ((ULift.ringEquiv (R := A)) x) = (x.down.fst, vSum x.down.snd)
  rw [phi_apply]
  rfl

private theorem phi2_surjective : Function.Surjective phi2 := by
  intro q
  obtain ⟨x, hx⟩ := phi_surjective q
  refine ⟨ULift.up x, ?_⟩
  simpa [phi2, ULift.ringEquiv] using hx

private theorem phi2_continuous : Continuous phi2 :=
  phi_continuous.comp continuous_uliftDown

private theorem phi2_ker_closed : IsClosed (RingHom.ker phi2 : Set A2) := by
  show IsClosed (phi2 ⁻¹' ({0} : Set Aq))
  exact isClosed_singleton.preimage phi2_continuous

/-- A pure-tensor `(0, q)` with `q` in a deep enough tail comes from `a2Ideal p`. -/
private lemma exists_mem_a2Ideal_phi2_eq {p : Finset ℕ × (ℕ → ℕ)} {i : ℕ} {q : Q}
    (hi : i ∉ p.1) (hq : q ∈ tail (p.2 i)) : ∃ y ∈ a2Ideal p, phi2 y = (0, q) := by
  refine ⟨ULift.up (0, vCoord i q), ⟨rfl, vCoord_mem_vBox hi hq⟩, ?_⟩
  simp [phi2_apply, vSum_coord]
  rfl

private lemma phi2_tail_mem_map {I : Ideal A2} (hI : IsOpen (I : Set A2))
    (h0 : (0 : A2) ∈ I) :
    ∃ N, ∀ q : Q, q ∈ tail N → (0, q) ∈ I.map phi2 := by
  obtain ⟨p, hp, hsub⟩ := a2_nhds_hasBasis.mem_iff.mp (hI.mem_nhds h0)
  let i := p.1.sup id + 1
  have hi : i ∉ p.1 := by
    intro hip
    have hle := Finset.le_sup (f := id) hip
    dsimp [i] at hle
    omega
  refine ⟨p.2 i, ?_⟩
  intro q hq
  obtain ⟨y, hy, hphi⟩ := exists_mem_a2Ideal_phi2_eq hi hq
  rw [← hphi]
  exact Ideal.mem_map_of_mem phi2 (hsub hy)

private noncomputable def targetKernel : Ideal A2 := RingHom.ker phi2

private noncomputable instance a2HasQuotient : HasQuotient A2 (Ideal A2) := by
  infer_instance

private noncomputable def targetQuotientMap : A2 →+* A2 ⧸ targetKernel :=
  Ideal.Quotient.mk targetKernel

private abbrev targetQuotient := A2 ⧸ targetKernel

private noncomputable def scalarLiftHom : K2Lift →+* A2 :=
  (ULift.ringEquiv (R := A)).symm.toRingHom.comp
    ((TrivSqZeroExt.inlHom K2 V).comp (ULift.ringEquiv (R := K2)).toRingHom)

private noncomputable def witnessSituation :
    TopologicalRing.ClosedIdealQuotientCompletionSituation.{u} where
  S := AlgebraicGeometry.Spec (.of K2Lift)
  A := A2
  commRingA := inferInstance
  topologicalSpaceA := inferInstance
  isTopologicalRingA := a2TopologicalRing
  isLinearTopologyA := a2LinearTopology
  weaklyAdmissible := a2WeaklyAdmissible
  overS J := AlgebraicGeometry.Spec.map <| CommRingCat.ofHom <|
    (Ideal.Quotient.mk J.1).comp scalarLiftHom
  overS_compatible J L h := by
    rw [← AlgebraicGeometry.Spec.map_comp]
    congr 1
  K := targetKernel
  closed_K := phi2_ker_closed

private theorem quotient_mem_map_of_phi_mem {I : Ideal A2} {x : A2}
    (hx : phi2 x ∈ I.map phi2) :
    targetQuotientMap x ∈ I.map targetQuotientMap := by
  obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective phi2 phi2_surjective).mp hx
  have hker : x - y ∈ targetKernel := by
    show phi2 (x - y) = 0
    rw [map_sub, hxy]
    simp
  have hquot : targetQuotientMap x = targetQuotientMap y :=
    (Ideal.Quotient.eq).2 hker
  rw [hquot]
  exact Ideal.mem_map_of_mem targetQuotientMap hy

private theorem phi_mem_map_of_quotient_mem_map {I : Ideal A2} {x : A2}
    (hx : targetQuotientMap x ∈ I.map targetQuotientMap) :
    phi2 x ∈ I.map phi2 := by
  obtain ⟨y, hy, hxy⟩ :=
    (Ideal.mem_map_iff_of_surjective targetQuotientMap
      Ideal.Quotient.mk_surjective).mp hx
  have hker : x - y ∈ targetKernel := (Ideal.Quotient.eq).mp hxy.symm
  have hphi : phi2 (x - y) = 0 := hker
  have hxy' : phi2 x = phi2 y := sub_eq_zero.mp (by simpa only [map_sub] using hphi)
  rw [hxy']
  exact Ideal.mem_map_of_mem phi2 hy

private noncomputable def prefixLift (n : ℕ) : A2 := ULift.up (0, vCoord 0 (qPrefix n))

private lemma phi2_prefixLift (n : ℕ) : phi2 (prefixLift n) = (0, qPrefix n) := by
  simp [prefixLift, phi2_apply, vSum_coord]
  rfl

private lemma phi2_prefixLift_sub (n N : ℕ) :
    phi2 (prefixLift n - prefixLift N) = (0, qPrefix n - qPrefix N) := by
  rw [RingHom.map_sub phi2, phi2_prefixLift, phi2_prefixLift]
  rfl

/-- Equal images in the completion coordinate at `J` follow from `phi2` of the difference
lying in `J.map phi2`. -/
private theorem mk_eq_of_phi2_sub_mem_map {J : TopologicalRing.WeakIdealOfDefinitionIndex A2}
    {x y : A2} (h : phi2 (x - y) ∈ J.1.map phi2) :
    Ideal.Quotient.mk (TopologicalRing.extendedIdeal targetQuotientMap J)
        (targetQuotientMap x) =
      Ideal.Quotient.mk (TopologicalRing.extendedIdeal targetQuotientMap J)
        (targetQuotientMap y) := by
  apply (Ideal.Quotient.eq).2
  have hmem := quotient_mem_map_of_phi_mem h
  change targetQuotientMap (x - y) ∈ J.1.map targetQuotientMap at hmem
  simpa only [map_sub] using hmem

private noncomputable def completionSeq (n : ℕ) :
    TopologicalRing.CompletionOver targetQuotientMap :=
  TopologicalRing.CompletionOver.canonicalMap targetQuotientMap (prefixLift n)

private theorem completionCoord_eventually_constant
    (J : TopologicalRing.WeakIdealOfDefinitionIndex A2) :
    ∃ z, ∀ᶠ n : ℕ in atTop,
      TopologicalRing.CompletionOver.projection targetQuotientMap J
        (completionSeq n) = z := by
  obtain ⟨N, hN⟩ := phi2_tail_mem_map J.2.1 (Ideal.zero_mem J.1)
  refine ⟨TopologicalRing.CompletionOver.projection targetQuotientMap J
    (completionSeq N), ?_⟩
  filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun n hn => hn⟩] with n hn
  exact mk_eq_of_phi2_sub_mem_map (by
    rw [phi2_prefixLift_sub]
    exact hN _ (qPrefix_diff_mem_tail hn))

private noncomputable def completionCoordLimit
    (J : TopologicalRing.WeakIdealOfDefinitionIndex A2) :
    targetQuotient ⧸ TopologicalRing.extendedIdeal targetQuotientMap J :=
  Classical.choose (completionCoord_eventually_constant J)

private theorem completionCoordLimit_spec
    (J : TopologicalRing.WeakIdealOfDefinitionIndex A2) :
    ∀ᶠ n : ℕ in atTop,
      (completionSeq n).1 J = completionCoordLimit J := by
  simpa [completionCoordLimit,
    TopologicalRing.CompletionOver.projection] using
    Classical.choose_spec (completionCoord_eventually_constant J)

private noncomputable def completionLimit :
    TopologicalRing.CompletionOver targetQuotientMap := by
  refine ⟨completionCoordLimit, ?_⟩
  intro J K h
  have hJ := completionCoordLimit_spec J
  have hK := completionCoordLimit_spec K
  obtain ⟨n, hn⟩ := Filter.Eventually.exists (hJ.and hK)
  rw [← hn.1, ← hn.2]
  exact (completionSeq n).2 J K h

private theorem completionCoordLimit_eq_of_eventually
    (J : TopologicalRing.WeakIdealOfDefinitionIndex A2) {z}
    (hz : ∀ᶠ n : ℕ in atTop,
      TopologicalRing.CompletionOver.projection targetQuotientMap J
        (completionSeq n) = z) :
    completionCoordLimit J = z := by
  have hlim := completionCoordLimit_spec J
  have hlim' : ∀ᶠ n : ℕ in atTop,
      TopologicalRing.CompletionOver.projection targetQuotientMap J
        (completionSeq n) = completionCoordLimit J := by
    simpa [TopologicalRing.CompletionOver.projection] using hlim
  obtain ⟨n, hn⟩ := Filter.Eventually.exists (hz.and hlim')
  exact hn.2.symm.trans hn.1

private theorem phi2_prefixDiff_mem_map {N n : ℕ} (hn : N ≤ n) :
    phi2 (prefixLift n - prefixLift N) ∈
      (a2Ideal (∅, fun _ => N)).map phi2 := by
  obtain ⟨y, hy, hyphi⟩ := exists_mem_a2Ideal_phi2_eq (p := (∅, fun _ => N)) (i := 0)
    (q := qPrefix n - qPrefix N) (by simp) (qPrefix_diff_mem_tail hn)
  rw [phi2_prefixLift_sub, ← hyphi]
  exact Ideal.mem_map_of_mem phi2 hy

private theorem completionCoord_stable_at (N : ℕ) :
    ∀ n : ℕ, N ≤ n →
      TopologicalRing.CompletionOver.projection targetQuotientMap
        (weakBox2 (∅, fun _ => N)) (completionSeq n) =
      TopologicalRing.CompletionOver.projection targetQuotientMap
        (weakBox2 (∅, fun _ => N)) (completionSeq N) := by
  intro n hn
  exact mk_eq_of_phi2_sub_mem_map (J := weakBox2 (∅, fun _ => N))
    (phi2_prefixDiff_mem_map hn)

private theorem completionCoord_stable_at_eventually (N : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      TopologicalRing.CompletionOver.projection targetQuotientMap
        (weakBox2 (∅, fun _ => N)) (completionSeq n) =
      TopologicalRing.CompletionOver.projection targetQuotientMap
        (weakBox2 (∅, fun _ => N)) (completionSeq N) :=
  Filter.eventually_atTop.mpr ⟨N, completionCoord_stable_at N⟩

private theorem phi2_map_mem_snd_tail {N : ℕ} {z : A2}
    (hz : phi2 z ∈ (a2Ideal (∅, fun _ => N)).map phi2) :
    (phi2 z).snd ∈ tail N := by
  obtain ⟨y, hy, hzy⟩ :=
    (Ideal.mem_map_iff_of_surjective phi2 phi2_surjective).mp hz
  have hy' : (ULift.ringEquiv (R := A) y).snd ∈
      vBoxSubmodule ∅ (fun _ => N) := by
    change (ULift.ringEquiv (R := A) y).fst = 0 ∧
      (ULift.ringEquiv (R := A) y).snd ∈ vBoxSubmodule ∅ (fun _ => N) at hy
    exact hy.2
  rw [← hzy, phi2_apply]
  apply vSum_mem_tail
  have hbox : (ULift.ringEquiv (R := A) y).snd.1 ∈ box ∅ (fun _ => N) := hy'
  intro i
  exact hbox.2 i (by simp)

/-- For some weakly admissible ring and closed ideal, the map to the completed quotient
is not surjective. -/
@[stacks 0ANR "nonsurjectivity"]
theorem exists_not_surjective_canonicalMap :
    ∃ D : TopologicalRing.ClosedIdealQuotientCompletionSituation.{u},
      ¬ Function.Surjective D.canonicalMap := by
  refine ⟨witnessSituation, ?_⟩
  intro hsurj
  let x := completionLimit
  obtain ⟨a, ha⟩ := hsurj x
  change A2 at a
  change TopologicalRing.CompletionOver.canonicalMap
    targetQuotientMap a = x at ha
  let q : Q := vSum a.down.snd
  let i : ℕ := q.support.sup id + 1
  have hi : i ∉ q.support := by
    intro hmem
    have hle := Finset.le_sup (f := id) hmem
    dsimp [i] at hle
    omega
  have hqi : q i = 0 := by
    by_contra hne
    exact hi (Finsupp.mem_support_iff.mpr hne)
  let N := i + 1
  let J := weakBox2 (∅, fun _ => N)
  have hcoord :
      TopologicalRing.CompletionOver.projection targetQuotientMap J
        (TopologicalRing.CompletionOver.canonicalMap targetQuotientMap a) =
      TopologicalRing.CompletionOver.projection targetQuotientMap J
        (completionSeq N) := by
    calc
      _ = TopologicalRing.CompletionOver.projection targetQuotientMap J x :=
        congrArg (TopologicalRing.CompletionOver.projection targetQuotientMap J) ha
      _ = completionCoordLimit J := rfl
      _ = TopologicalRing.CompletionOver.projection targetQuotientMap J
          (completionSeq N) :=
            completionCoordLimit_eq_of_eventually J (completionCoord_stable_at_eventually N)
  have hclasses' :
      Ideal.Quotient.mk (TopologicalRing.extendedIdeal targetQuotientMap J)
        (targetQuotientMap a) =
      Ideal.Quotient.mk (TopologicalRing.extendedIdeal targetQuotientMap J)
        (targetQuotientMap (prefixLift N)) := by
    calc
      _ = TopologicalRing.CompletionOver.projection targetQuotientMap J
          (TopologicalRing.CompletionOver.canonicalMap targetQuotientMap a) :=
            (TopologicalRing.CompletionOver.projection_canonicalMap
              targetQuotientMap J a).symm
      _ = TopologicalRing.CompletionOver.projection targetQuotientMap J
          (completionSeq N) := hcoord
      _ = _ := by
        simpa only [completionSeq] using
          TopologicalRing.CompletionOver.projection_canonicalMap
            targetQuotientMap J (prefixLift N)
  have hqmem : targetQuotientMap a - targetQuotientMap (prefixLift N) ∈
      J.1.map targetQuotientMap := (Ideal.Quotient.eq).mp hclasses'
  have hmap : phi2 (a - prefixLift N) ∈ J.1.map phi2 :=
    phi_mem_map_of_quotient_mem_map (by simpa only [map_sub] using hqmem)
  have htail : (phi2 (a - prefixLift N)).snd ∈ tail N := phi2_map_mem_snd_tail hmap
  have hsecond : (phi2 (a - prefixLift N)).snd = q - qPrefix N := by
    rw [map_sub, phi2_apply, phi2_prefixLift]
    rfl
  rw [hsecond] at htail
  have hzero : (q - qPrefix N) i = 0 := htail i (by dsimp [N]; omega)
  have hqone : q i = 1 := by
    have hiN : i < N := by dsimp [N]; omega
    have hzero' : q i - 1 = 0 := by
      simpa [qPrefix_apply, hiN] using hzero
    exact sub_eq_zero.mp hzero'
  exact zero_ne_one (hqi.symm.trans hqone)

end

end TopologicalRing

end
