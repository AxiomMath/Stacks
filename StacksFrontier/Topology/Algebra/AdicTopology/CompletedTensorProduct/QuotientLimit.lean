module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct
public import StacksFrontier.Topology.Algebra.AdicTopology.Completion

/-!
# The completed tensor product of algebras as an inverse limit of quotients

For algebras `A` and `C` over `B` with descending systems of ideals `I` and `J` giving
neighbourhood bases of zero, the completed tensor product `A ⊗̂[B] C` is the inverse limit of
the discrete rings `A/Iᵢ ⊗[B] C/Jⱼ`.  This file produces that identification as a topological
ring equivalence and reads off the open kernels of its projections.

## References


-/

@[expose] public section

namespace TopologicalRing

section

open Filter Set
open scoped TensorProduct Topology


variable {B A C : Type*} [CommRing B] [CommRing A] [CommRing C]
  [Algebra B A] [Algebra B C]
  [TopologicalSpace A] [TopologicalSpace C]
  [ContinuousAdd A] [ContinuousAdd C]
  [IsLinearTopology A A] [IsLinearTopology C C]

/-- Compatible families of quotient tensor-product rings. -/
public def quotientLimitSubring {ι κ : Type*} (I : ι → Ideal A) (J : κ → Ideal C) :
    Subring (∀ p : ι × κ, (A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) where
  carrier := { x | ∀ p q : ι × κ, ∀ hp : I p.1 ≤ I q.1, ∀ hq : J p.2 ≤ J q.2,
    Algebra.TensorProduct.map (Ideal.Quotient.factorₐ B hp)
      (Ideal.Quotient.factorₐ B hq) (x p) = x q }
  one_mem' := by
    intro p q hp hq
    simp
  mul_mem' := by
    intro x y hx hy p q hp hq
    simp [hx p q hp hq, hy p q hp hq]
  zero_mem' := by
    intro p q hp hq
    simp
  add_mem' := by
    intro x y hx hy p q hp hq
    simp [hx p q hp hq, hy p q hp hq]
  neg_mem' := by
    intro x hx p q hp hq
    simp [hx p q hp hq]

/-- The ring inverse limit for two chosen systems of open ideals. -/
public abbrev quotientLimit {ι κ : Type*} (I : ι → Ideal A) (J : κ → Ideal C) :=
  quotientLimitSubring (B := B) I J

/-- The limit topology, with discrete topology on each quotient tensor product. -/
@[instance_reducible] public noncomputable def quotientLimitTopology {ι κ : Type*}
    (I : ι → Ideal A) (J : κ → Ideal C) :
    TopologicalSpace (quotientLimit (B := B) I J) :=
  TopologicalSpace.induced Subtype.val
    (@Pi.topologicalSpace (ι × κ)
      (fun p => (A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) (fun _ => ⊥))

/-- The tensor submodule of two basic ideals is a neighbourhood of zero. -/
private theorem tensorProductSubmodule_mem_nhds {R P Q ι' κ' : Type*} [CommRing R] [CommRing P]
    [CommRing Q] [Algebra R P] [Algebra R Q] [TopologicalSpace P] [TopologicalSpace Q]
    [ContinuousAdd P] [ContinuousAdd Q] {F : ι' → Ideal P} {G : κ' → Ideal Q}
    (bF : (nhds (0 : P)).HasBasis (fun _ : ι' => True) (fun i => (F i : Set P)))
    (bG : (nhds (0 : Q)).HasBasis (fun _ : κ' => True) (fun j => (G j : Set Q))) (i : ι') (j : κ') :
    letI := TopologicalRing.tensorProductTopology (R := R) (M := P) (N := Q)
    (TopologicalRing.tensorProductSubmodule
      ((F i).restrictScalars R) ((G j).restrictScalars R) : Set (P ⊗[R] Q)) ∈
        nhds (0 : P ⊗[R] Q) := by
  let := TopologicalRing.tensorProductTopology (R := R) (M := P) (N := Q)
  exact (TopologicalRing.hasBasis_tensorProductTopology
    (R := R) (M := P) (N := Q)).mem_iff.mpr
      ⟨(⟨(F i).restrictScalars R, (F i).toAddSubgroup.isOpen_of_mem_nhds
          (bF.mem_iff.mpr ⟨i, trivial, Subset.rfl⟩)⟩,
        ⟨(G j).restrictScalars R, (G j).toAddSubgroup.isOpen_of_mem_nhds
          (bG.mem_iff.mpr ⟨j, trivial, Subset.rfl⟩)⟩), trivial, Subset.rfl⟩

/-- The kernel of the quotient map on tensor products is the tensor submodule of the ideals. -/
private theorem map_mkₐ_eq_zero_iff {R P Q : Type*} [CommRing R] [CommRing P] [CommRing Q]
    [Algebra R P] [Algebra R Q] (I : Ideal P) (J : Ideal Q) (z : P ⊗[R] Q) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R J) z = 0 ↔
      z ∈ TopologicalRing.tensorProductSubmodule (I.restrictScalars R) (J.restrictScalars R) := by
  let K := TopologicalRing.tensorProductSubmodule (I.restrictScalars R) (J.restrictScalars R)
  have hf : (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ R J)).toLinearMap = (TensorProduct.quotientTensorQuotientEquiv
        (I.restrictScalars R) (J.restrictScalars R)).symm.toLinearMap.comp K.mkQ := by
    ext a c
    rfl
  have hz := LinearMap.congr_fun hf z
  change _ = (TensorProduct.quotientTensorQuotientEquiv _ _).symm (K.mkQ z) at hz
  rw [← AlgHom.toLinearMap_apply, hz]
  exact (LinearEquiv.map_eq_zero_iff _).trans (Submodule.Quotient.mk_eq_zero K)

/-- The transition maps are compatible with the projections from the tensor product. -/
private theorem factor_comp_map_mkₐ {R P Q : Type*} [CommRing R] [CommRing P] [CommRing Q]
    [Algebra R P] [Algebra R Q] {I I' : Ideal P} {J J' : Ideal Q} (hI : I ≤ I') (hJ : J ≤ J') :
    (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R hI)
      (Ideal.Quotient.factorₐ R hJ)).toRingHom.comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R J)).toRingHom =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I')
        (Ideal.Quotient.mkₐ R J')).toRingHom := by
  ext a <;> simp

variable {ι κ : Type*} (I : ι → Ideal A) (J : κ → Ideal C)
  (bI : (nhds (0 : A)).HasBasis (fun _ : ι => True) (fun i => (I i : Set A)))
  (bJ : (nhds (0 : C)).HasBasis (fun _ : κ => True) (fun j => (J j : Set C)))

include bI bJ

omit [IsLinearTopology A A] [IsLinearTopology C C] in
private theorem hasBasis_tensorProductTopology_system :
    letI := TopologicalRing.tensorProductTopology (R := B) (M := A) (N := C)
    (nhds (0 : A ⊗[B] C)).HasBasis
      (fun _ : ι × κ => True)
      (fun p => (TopologicalRing.tensorProductSubmodule
        ((I p.1).restrictScalars B) ((J p.2).restrictScalars B) : Set (A ⊗[B] C))) := by
  let := TopologicalRing.tensorProductTopology (R := B) (M := A) (N := C)
  refine (TopologicalRing.hasBasis_tensorProductTopology
    (R := B) (M := A) (N := C)).to_hasBasis ?_ ?_
  · intro p _
    obtain ⟨i, _, hI⟩ := bI.mem_iff.mp (p.1.2.mem_nhds p.1.1.zero_mem)
    obtain ⟨j, _, hJ⟩ := bJ.mem_iff.mp (p.2.2.mem_nhds p.2.1.zero_mem)
    exact ⟨(i, j), trivial,
      TopologicalRing.tensorProductSubmodule_mono hI hJ⟩
  · exact fun p _ => (TopologicalRing.hasBasis_tensorProductTopology
      (R := B) (M := A) (N := C)).mem_iff.mp (tensorProductSubmodule_mem_nhds bI bJ p.1 p.2)

private noncomputable def quotientTensorProductExtension (i : ι) (j : κ) :
    TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) →+*
      (A ⧸ I i) ⊗[B] (C ⧸ J j) := by
  classical
  letI := TopologicalRing.tensorProductTopology (R := B) (M := A) (N := C)
  letI := TopologicalRing.tensorProductUniformSpace (R := B) (M := A) (N := C)
  let P : Submodule B A := (I i).restrictScalars B
  let Q : Submodule B C := (J j).restrictScalars B
  let K := TopologicalRing.tensorProductSubmodule P Q
  let f : (A ⊗[B] C) →ₐ[B] ((A ⧸ I i) ⊗[B] (C ⧸ J j)) :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ B (I i)) (Ideal.Quotient.mkₐ B (J j))
  have hKo : IsOpen (K : Set (A ⊗[B] C)) :=
    K.toAddSubgroup.isOpen_of_mem_nhds (tensorProductSubmodule_mem_nhds bI bJ i j)
  have hsub : K.toAddSubgroup ≤ (RingHom.ker f.toRingHom).toAddSubgroup := fun z hz =>
    (map_mkₐ_eq_zero_iff (I i) (J j) z).2 hz
  have hopen : IsOpen ((RingHom.ker f.toRingHom).toAddSubgroup : Set (A ⊗[B] C)) :=
    AddSubgroup.isOpen_mono hsub hKo
  letI : TopologicalSpace ((A ⧸ I i) ⊗[B] (C ⧸ J j)) := ⊥
  letI : UniformSpace ((A ⧸ I i) ⊗[B] (C ⧸ J j)) := ⊥
  haveI : DiscreteTopology ((A ⧸ I i) ⊗[B] (C ⧸ J j)) := ⟨rfl⟩
  haveI : DiscreteUniformity ((A ⧸ I i) ⊗[B] (C ⧸ J j)) := inferInstance
  haveI : IsUniformAddGroup ((A ⧸ I i) ⊗[B] (C ⧸ J j)) :=
    ⟨by
      haveI : DiscreteUniformity
          (((A ⧸ I i) ⊗[B] (C ⧸ J j)) × ((A ⧸ I i) ⊗[B] (C ⧸ J j))) := inferInstance
      exact @DiscreteUniformity.uniformContinuous
        (((A ⧸ I i) ⊗[B] (C ⧸ J j)) × ((A ⧸ I i) ⊗[B] (C ⧸ J j))) _ _
        ((A ⧸ I i) ⊗[B] (C ⧸ J j)) _
        (fun p : ((A ⧸ I i) ⊗[B] (C ⧸ J j)) × ((A ⧸ I i) ⊗[B] (C ⧸ J j)) => p.1 - p.2)⟩
  have huc : UniformContinuous f.toRingHom.toAddMonoidHom :=
    (IsUniformAddGroup.uniformContinuous_iff_isOpen_ker).2 hopen
  exact UniformSpace.Completion.extensionHom f.toRingHom huc.continuous

private def sourceProjection (i : ι) (j : κ) :
    (A ⊗[B] C) →+* ((A ⧸ I i) ⊗[B] (C ⧸ J j)) :=
  (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ B (I i))
    (Ideal.Quotient.mkₐ B (J j))).toRingHom

private def sourceToQuotientLimit : (A ⊗[B] C) →+*
    quotientLimit (B := B) I J where
  toFun z := ⟨fun p => sourceProjection I J p.1 p.2 z, fun p q hp hq =>
    RingHom.congr_fun (factor_comp_map_mkₐ hp hq) z⟩
  map_one' := by ext p; simp [sourceProjection]
  map_mul' x y := by ext p; simp [sourceProjection]
  map_zero' := by ext p; simp [sourceProjection]
  map_add' x y := by ext p; simp [sourceProjection]

omit [ContinuousAdd A] [ContinuousAdd C] [IsLinearTopology A A] [IsLinearTopology C C] in
private theorem selectedCommonRefinement (s : Finset (ι × κ)) :
    ∃ k l, ∀ p ∈ s, I k ≤ I p.1 ∧ J l ≤ J p.2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      obtain ⟨k, _, _⟩ := bI.mem_iff.mp (Filter.univ_mem : (Set.univ : Set A) ∈ 𝓝 (0 : A))
      obtain ⟨l, _, _⟩ := bJ.mem_iff.mp (Filter.univ_mem : (Set.univ : Set C) ∈ 𝓝 (0 : C))
      exact ⟨k, l, by simp⟩
  | @insert p s hps ih =>
      obtain ⟨k, l, hk⟩ := ih
      obtain ⟨k', _, hk'⟩ := bI.mem_iff.mp
        (Filter.inter_mem
          (bI.mem_iff.mpr ⟨p.1, trivial, Subset.rfl⟩)
          (bI.mem_iff.mpr ⟨k, trivial, Subset.rfl⟩))
      obtain ⟨l', _, hl'⟩ := bJ.mem_iff.mp
        (Filter.inter_mem
          (bJ.mem_iff.mpr ⟨p.2, trivial, Subset.rfl⟩)
          (bJ.mem_iff.mpr ⟨l, trivial, Subset.rfl⟩))
      refine ⟨k', l', ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact ⟨SetLike.coe_subset_coe.mp (Set.Subset.trans hk' Set.inter_subset_left),
          SetLike.coe_subset_coe.mp (Set.Subset.trans hl' Set.inter_subset_left)⟩
      · obtain ⟨hI, hJ⟩ := hk q hq
        exact ⟨SetLike.coe_subset_coe.mp
            (Set.Subset.trans hk' (Set.inter_subset_right.trans
              (SetLike.coe_subset_coe.mpr hI))),
          SetLike.coe_subset_coe.mp
            (Set.Subset.trans hl' (Set.inter_subset_right.trans
              (SetLike.coe_subset_coe.mpr hJ)))⟩

omit [ContinuousAdd A] [ContinuousAdd C] [IsLinearTopology A A] [IsLinearTopology C C] in
private theorem source_finiteApprox
    (x : quotientLimit (B := B) I J) (s : Finset (ι × κ)) :
    ∃ z : A ⊗[B] C, ∀ p ∈ s, sourceProjection I J p.1 p.2 z = x.1 p := by
  obtain ⟨k, l, hk⟩ := selectedCommonRefinement I J bI bJ s
  have hs' : Function.Surjective
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ B (I k))
        (Ideal.Quotient.mkₐ B (J l))) :=
    Algebra.TensorProduct.map_surjective
      (f := Ideal.Quotient.mkₐ B (I k)) (g := Ideal.Quotient.mkₐ B (J l))
      (Ideal.Quotient.mkₐ_surjective B (I k))
      (Ideal.Quotient.mkₐ_surjective B (J l))
  have hs : Function.Surjective
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ B (I k))
        (Ideal.Quotient.mkₐ B (J l))).toLinearMap := hs'
  obtain ⟨z, hz⟩ := hs (x.1 (k, l))
  refine ⟨z, ?_⟩
  intro p hp
  obtain ⟨hI, hJ⟩ := hk p hp
  have hz' : sourceProjection I J k l z = x.1 (k, l) := by
    show (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ B (I k))
      (Ideal.Quotient.mkₐ B (J l))) z = _
    exact hz
  calc
    sourceProjection I J p.1 p.2 z =
        Algebra.TensorProduct.map (Ideal.Quotient.factorₐ B hI)
          (Ideal.Quotient.factorₐ B hJ) (sourceProjection I J k l z) :=
      (RingHom.congr_fun (factor_comp_map_mkₐ hI hJ) z).symm
    _ = x.1 p := by rw [hz']; exact x.2 (k, l) p hI hJ

omit [ContinuousAdd A] [ContinuousAdd C] [IsLinearTopology A A] [IsLinearTopology C C] in
private theorem sourceProjection_ker (i : ι) (j : κ) (z : A ⊗[B] C) :
    sourceProjection I J i j z = 0 ↔
      z ∈ TopologicalRing.tensorProductSubmodule
        ((I i).restrictScalars B) ((J j).restrictScalars B) :=
  map_mkₐ_eq_zero_iff (I i) (J j) z

omit [IsLinearTopology A A] [IsLinearTopology C C] in
private theorem continuous_sourceProjection (i : ι) (j : κ) :
    letI := TopologicalRing.tensorProductTopology (R := B) (M := A) (N := C)
    @Continuous (A ⊗[B] C) ((A ⧸ I i) ⊗[B] (C ⧸ J j))
      (TopologicalRing.tensorProductTopology (R := B) (M := A) (N := C)) ⊥
      (sourceProjection I J i j) := by
  let := TopologicalRing.tensorProductTopology (R := B) (M := A) (N := C)
  let : TopologicalSpace ((A ⧸ I i) ⊗[B] (C ⧸ J j)) := ⊥
  have : DiscreteTopology ((A ⧸ I i) ⊗[B] (C ⧸ J j)) := ⟨rfl⟩
  apply continuous_of_continuousAt_zero (sourceProjection I J i j).toAddMonoidHom
  show Tendsto (sourceProjection I J i j) (𝓝 0)
    (𝓝 (0 : (A ⧸ I i) ⊗[B] (C ⧸ J j)))
  rw [show 𝓝 (0 : (A ⧸ I i) ⊗[B] (C ⧸ J j)) = pure 0 from
    congrFun (nhds_discrete ((A ⧸ I i) ⊗[B] (C ⧸ J j))) 0]
  rw [tendsto_pure]
  exact Filter.mem_of_superset (tensorProductSubmodule_mem_nhds bI bJ i j) fun z hz =>
    (sourceProjection_ker I J bI bJ i j z).2 hz

/-- The canonical comparison with the inverse limit is a topological ring equivalence,
whose components restrict to the evident algebraic quotient maps. -/
public theorem exists_completedTensorProductRingEquivQuotientLimit :
    letI := quotientLimitTopology (B := B) I J
    ∃ e : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) ≃+*
        quotientLimit (B := B) I J,
      Continuous e ∧ Continuous e.symm ∧
      (∀ z : A ⊗[B] C, ∀ i j,
        (e (↑z : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))).1
          (i, j) = Algebra.TensorProduct.map
            (Ideal.Quotient.mkₐ B (I i)) (Ideal.Quotient.mkₐ B (J j)) z) := by
  classical
  let : ∀ p : ι × κ, TopologicalSpace ((A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) := fun _ => ⊥
  let : ∀ p : ι × κ, DiscreteTopology ((A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) := fun _ => ⟨rfl⟩
  let : ∀ p : ι × κ, UniformSpace ((A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) := fun _ => ⊥
  let : ∀ p : ι × κ, DiscreteUniformity ((A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) :=
    fun _ => inferInstance
  let : UniformSpace (∀ p : ι × κ, (A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) := inferInstance
  let : TopologicalSpace (quotientLimit (B := B) I J) :=
    quotientLimitTopology (B := B) I J
  let : UniformSpace (quotientLimit (B := B) I J) :=
    UniformSpace.comap Subtype.val inferInstance
  have hclosed : IsClosed
      (quotientLimitSubring (B := B) I J :
        Set (∀ p : ι × κ, (A ⧸ I p.1) ⊗[B] (C ⧸ J p.2))) := by
    let T := {t : (ι × κ) × (ι × κ) //
      I t.1.1 ≤ I t.2.1 ∧ J t.1.2 ≤ J t.2.2}
    let F : (∀ p : ι × κ, (A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) →
        (∀ t : T, (A ⧸ I t.1.2.1) ⊗[B] (C ⧸ J t.1.2.2)) := fun x t =>
      Algebra.TensorProduct.map (Ideal.Quotient.factorₐ B t.2.1)
        (Ideal.Quotient.factorₐ B t.2.2) (x t.1.1)
    let G : (∀ p : ι × κ, (A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) →
        (∀ t : T, (A ⧸ I t.1.2.1) ⊗[B] (C ⧸ J t.1.2.2)) := fun x t => x t.1.2
    have hset : (quotientLimitSubring (B := B) I J :
        Set (∀ p : ι × κ, (A ⧸ I p.1) ⊗[B] (C ⧸ J p.2))) = {x | F x = G x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun hx => funext fun t => hx t.1.1 t.1.2 t.2.1 t.2.2,
        fun hx p q hp hq => congrFun hx ⟨(p, q), hp, hq⟩⟩
    rw [hset]
    exact isClosed_eq
      (continuous_pi fun t => continuous_of_discreteTopology.comp (continuous_apply t.1.1))
      (continuous_pi fun t => continuous_apply t.1.2)
  have : CompleteSpace (quotientLimit (B := B) I J) := by
    have : ∀ p : ι × κ, CompleteSpace ((A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) :=
      fun _ => inferInstance
    have : CompleteSpace (∀ p : ι × κ, (A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) :=
      Pi.complete (α := fun p : ι × κ => (A ⧸ I p.1) ⊗[B] (C ⧸ J p.2))
    exact hclosed.completeSpace_coe
  have : T0Space (quotientLimit (B := B) I J) := inferInstance
  -- Named rather than searched: the subring sits inside a product of discrete rings, and
  -- rediscovering that through the uniform structure costs more than the instance budget.
  have : IsTopologicalAddGroup (quotientLimit (B := B) I J) :=
    (quotientLimitSubring (B := B) I J).toAddSubgroup.instIsTopologicalAddGroupSubtypeMem
  let : TopologicalSpace (A ⊗[B] C) :=
    TopologicalRing.tensorProductTopology (R := B) (M := A) (N := C)
  let : UniformSpace (A ⊗[B] C) :=
    TopologicalRing.tensorProductUniformSpace (R := B) (M := A) (N := C)
  have hcont : Continuous (sourceToQuotientLimit (B := B) (A := A) (C := C) I J) := by
    rw [continuous_induced_rng]
    show Continuous (fun z : A ⊗[B] C =>
      fun p : ι × κ => sourceProjection I J p.1 p.2 z)
    exact continuous_pi fun p => continuous_sourceProjection I J bI bJ p.1 p.2
  have hind : Topology.IsInducing
      (sourceToQuotientLimit (B := B) (A := A) (C := C) I J) := by
    apply IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr
    apply le_antisymm
    · apply Filter.tendsto_iff_comap.mp
      simpa using hcont.continuousAt (x := (0 : A ⊗[B] C)) |>.tendsto
    · intro U hU
      obtain ⟨p, _, hp⟩ :=
        (hasBasis_tensorProductTopology_system I J bI bJ).mem_iff.mp hU
      let V : Set (quotientLimit (B := B) I J) := {x | x.1 p = 0}
      have hopenV : IsOpen V := by
        show IsOpen ((fun x : quotientLimit (B := B) I J => x.1 p) ⁻¹'
          ({0} : Set ((A ⧸ I p.1) ⊗[B] (C ⧸ J p.2))))
        exact IsOpen.preimage ((continuous_apply p).comp continuous_subtype_val)
          (isOpen_discrete ({0} : Set ((A ⧸ I p.1) ⊗[B] (C ⧸ J p.2))))
      refine Filter.mem_of_superset
        (Filter.mem_comap.mpr ⟨V, hopenV.mem_nhds (by simp [V]), ?_⟩) hp
      exact fun z hz => (sourceProjection_ker I J bI bJ p.1 p.2 z).1 hz
  have hdense : DenseRange (sourceToQuotientLimit (B := B) (A := A) (C := C) I J) := by
    refine fun x => mem_closure_iff.mpr fun o ho hxo => ?_
    obtain ⟨u, hu, rfl⟩ := isOpen_induced_iff.mp ho
    obtain ⟨s, v, hv, hsub⟩ := isOpen_pi_iff.mp hu x.1 hxo
    obtain ⟨z, hz⟩ := source_finiteApprox I J bI bJ x s
    refine ⟨sourceToQuotientLimit (B := B) (A := A) (C := C) I J z, ?_, ⟨z, rfl⟩⟩
    apply hsub
    intro p hp
    have hp' : p ∈ s := Finset.mem_coe.mp hp
    show sourceProjection I J p.1 p.2 z ∈ v p
    rw [hz p hp']
    exact (hv p hp').2
  have : ∀ p : ι × κ, IsUniformAddGroup ((A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) :=
    fun _ => inferInstance
  have : IsUniformAddGroup (quotientLimit (B := B) I J) :=
    (quotientLimitSubring (B := B) I J).toAddSubgroup.isUniformAddGroup
  let pkg : AbstractCompletion (A ⊗[B] C) :=
    { space := quotientLimit (B := B) I J
      coe := sourceToQuotientLimit (B := B) (A := A) (C := C) I J
      uniformStruct := UniformSpace.comap Subtype.val inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := AddMonoidHom.isUniformInducing_of_isInducing hind
      dense := hdense }
  let eu : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) ≃ᵤ
      quotientLimit (B := B) I J := UniformSpace.Completion.cPkg.compareEquiv pkg
  have heU (z : A ⊗[B] C) :
      eu (z : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) =
        sourceToQuotientLimit (B := B) (A := A) (C := C) I J z :=
    UniformSpace.Completion.cPkg.compare_coe pkg z
  have hadd (x y : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) :
      eu (x + y) = eu x + eu y := by
    refine UniformSpace.Completion.induction_on₂
      (p := fun x y => eu (x + y) = eu x + eu y) x y ?_ ?_
    · exact isClosed_eq (eu.continuous.comp (continuous_fst.add continuous_snd))
        ((eu.continuous.comp continuous_fst).add (eu.continuous.comp continuous_snd))
    · intro a b
      simp only [← UniformSpace.Completion.coe_add, heU]
      exact (sourceToQuotientLimit (B := B) (A := A) (C := C) I J).map_add a b
  have hmul (x y : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) :
      eu (x * y) = eu x * eu y := by
    refine UniformSpace.Completion.induction_on₂
      (p := fun x y => eu (x * y) = eu x * eu y) x y ?_ ?_
    · exact isClosed_eq (eu.continuous.comp (continuous_fst.mul continuous_snd))
        ((eu.continuous.comp continuous_fst).mul (eu.continuous.comp continuous_snd))
    · intro a b
      simp only [← UniformSpace.Completion.coe_mul, heU]
      exact (sourceToQuotientLimit (B := B) (A := A) (C := C) I J).map_mul a b
  let e : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) ≃+*
      quotientLimit (B := B) I J := { eu.toEquiv with map_mul' := hmul, map_add' := hadd }
  exact ⟨e, eu.continuous, eu.symm.continuous, fun z i j =>
    congrArg (fun x : quotientLimit (B := B) I J => x.1 (i, j)) (heU z)⟩

/-- The canonical ring equivalence furnished by the inverse-limit identification. -/
public noncomputable def completedTensorProductRingEquivQuotientLimit :
    TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) ≃+*
      quotientLimit (B := B) I J :=
  letI := quotientLimitTopology (B := B) I J
  Classical.choose (exists_completedTensorProductRingEquivQuotientLimit I J bI bJ)

/-- The canonical projection to a quotient tensor-product ring. -/
public noncomputable def projectionRingHom (i : ι) (j : κ) :
    TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) →+*
      (A ⧸ I i) ⊗[B] (C ⧸ J j) :=
  ((Pi.evalRingHom (fun p : ι × κ => (A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) (i, j)).comp
    (Subring.subtype (quotientLimitSubring (B := B) I J))).comp
      (completedTensorProductRingEquivQuotientLimit I J bI bJ).toRingHom

private theorem continuous_completedTensorProductRingEquivQuotientLimit :
    letI := quotientLimitTopology (B := B) I J
    Continuous (completedTensorProductRingEquivQuotientLimit (B := B) I J bI bJ) ∧
      Continuous (completedTensorProductRingEquivQuotientLimit (B := B) I J bI bJ).symm :=
  letI := quotientLimitTopology (B := B) I J
  let h := Classical.choose_spec
    (exists_completedTensorProductRingEquivQuotientLimit (B := B) I J bI bJ)
  ⟨h.1, h.2.1⟩

/-- An open ideal kernel of a canonical projection. -/
public noncomputable def projectionKernel (i : ι) (j : κ) :
    Ideal (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) :=
  RingHom.ker (projectionRingHom I J bI bJ i j)

/-- Projection kernels for the chosen quotient tensor products are open. -/
public theorem isOpen_projectionKernel (i : ι) (j : κ) :
    IsOpen (SetLike.coe (projectionKernel (B := B) I J bI bJ i j) :
      Set (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))) := by
  classical
  let := quotientLimitTopology (B := B) I J
  let : ∀ p : ι × κ, TopologicalSpace ((A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) := fun _ => ⊥
  let : TopologicalSpace ((A ⧸ I i) ⊗[B] (C ⧸ J j)) := ⊥
  have : DiscreteTopology ((A ⧸ I i) ⊗[B] (C ⧸ J j)) := ⟨rfl⟩
  let e : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) ≃+*
      quotientLimit (B := B) I J :=
    completedTensorProductRingEquivQuotientLimit I J bI bJ
  have he : Continuous e :=
    (continuous_completedTensorProductRingEquivQuotientLimit (B := B) I J bI bJ).1
  have hcont : Continuous (projectionRingHom
      (B := B) (A := A) (C := C) I J bI bJ i j) := by
    show Continuous (((Pi.evalRingHom
      (fun p : ι × κ => (A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) (i, j)).comp
        (Subring.subtype (quotientLimitSubring (B := B) I J))).comp e.toRingHom)
    exact (continuous_apply (i, j)).comp continuous_subtype_val |>.comp he
  show IsOpen (↑(RingHom.ker (projectionRingHom
    (B := B) (A := A) (C := C) I J bI bJ i j)) :
      Set (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)))
  exact (isOpen_discrete ({0} : Set ((A ⧸ I i) ⊗[B] (C ⧸ J j)))).preimage hcont

/-- The projection kernels form a fundamental system of neighbourhoods of zero. -/
public theorem hasBasis_projectionKernel :
    (nhds (0 : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))).HasBasis
      (fun _ : ι × κ => True)
      (fun p => (SetLike.coe (projectionKernel (B := B) I J bI bJ p.1 p.2) :
        Set (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)))) := by
  classical
  let := quotientLimitTopology (B := B) I J
  let : ∀ p : ι × κ, TopologicalSpace ((A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) := fun _ => ⊥
  let : ∀ p : ι × κ, DiscreteTopology ((A ⧸ I p.1) ⊗[B] (C ⧸ J p.2)) :=
    fun _ => ⟨rfl⟩
  have hlim : (nhds (0 : quotientLimit (B := B) I J)).HasBasis
      (fun _ : ι × κ => True) (fun p => {x : quotientLimit (B := B) I J | x.1 p = 0}) := by
    let bPi : (nhds (0 : ∀ p : ι × κ, (A ⧸ I p.1) ⊗[B] (C ⧸ J p.2))).HasBasis
        Set.Finite (fun s => {x | ∀ p ∈ s, x p = 0}) := by
      simpa only [nhds_pi, Pi.zero_apply, nhds_discrete, pure_zero, Prod.forall] using
        (Filter.hasBasis_pi_pure
          (fun p : ι × κ => (0 : (A ⧸ I p.1) ⊗[B] (C ⧸ J p.2))))
    have hsub : (nhds (0 : quotientLimit (B := B) I J)).HasBasis
        Set.Finite (fun s => {x : quotientLimit (B := B) I J | ∀ p ∈ s, x.1 p = 0}) := by
      simpa only [nhds_induced, ZeroMemClass.coe_zero, Prod.forall,
        preimage_ofPred_eq] using bPi.comap
        (Subtype.val : quotientLimit (B := B) I J →
          ∀ p : ι × κ, (A ⧸ I p.1) ⊗[B] (C ⧸ J p.2))
    refine hsub.to_hasBasis (p' := fun _ : ι × κ => True)
      (s' := fun p : ι × κ => {x : quotientLimit (B := B) I J | x.1 p = 0}) ?_ ?_
    · intro s hs
      obtain ⟨k, l, hkl⟩ := selectedCommonRefinement I J bI bJ hs.toFinset
      refine ⟨(k, l), trivial, ?_⟩
      intro x hx q hq
      have hq' : q ∈ hs.toFinset := hs.mem_toFinset.mpr hq
      have hcompat := x.2 (k, l) q (hkl q hq').1 (hkl q hq').2
      rw [hx] at hcompat
      simpa using hcompat.symm
    · intro p _
      refine ⟨{p}, by simp, ?_⟩
      intro x hx
      exact hx p (by simp)
  let : UniformSpace (A ⊗[B] C) :=
    TopologicalRing.tensorProductUniformSpace (R := B) (M := A) (N := C)
  let : TopologicalSpace
      (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) := inferInstance
  let e : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) ≃+*
      quotientLimit (B := B) I J :=
    completedTensorProductRingEquivQuotientLimit I J bI bJ
  let h : TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) ≃ₜ
      quotientLimit (B := B) I J :=
    Homeomorph.mk e.toEquiv (continuous_completedTensorProductRingEquivQuotientLimit I J bI bJ).1
      (continuous_completedTensorProductRingEquivQuotientLimit I J bI bJ).2
  have hzero : h 0 = 0 := map_zero e
  have hBasis := hlim.comap h
  rw [h.nhds_eq_comap 0, hzero]
  refine hBasis.to_hasBasis (p' := fun _ : ι × κ => True)
    (s' := fun p : ι × κ => (SetLike.coe (projectionKernel (B := B) I J bI bJ p.1 p.2) :
      Set (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)))) ?_ ?_
  · exact fun p _ => ⟨p, trivial, fun _ hx => hx⟩
  · exact fun p _ => ⟨p, trivial, fun _ hx => hx⟩

/-- A projection kernel is the closure of the sum of the two extended ideals. -/
public theorem projectionKernel_eq_closure (i : ι) (j : κ) :
    letI := TopologicalRing.tensorProductUniformSpace (R := B) (M := A) (N := C)
    (SetLike.coe (projectionKernel (B := B) I J bI bJ i j) :
      Set (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))) =
      (Ideal.closure
        ((I i).map ((UniformSpace.Completion.coeRingHom :
            (A ⊗[B] C) →+* TopologicalRing.CompletedTensorProduct
              (R := B) (M := A) (N := C)).comp
            (Algebra.TensorProduct.includeLeft : A →ₐ[B] A ⊗[B] C).toRingHom) +
          (J j).map ((UniformSpace.Completion.coeRingHom :
            (A ⊗[B] C) →+* TopologicalRing.CompletedTensorProduct
              (R := B) (M := A) (N := C)).comp
            (Algebra.TensorProduct.includeRight : C →ₐ[B] A ⊗[B] C).toRingHom)) :
        Set (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))) := by
  classical
  let := TopologicalRing.tensorProductTopology (R := B) (M := A) (N := C)
  let := TopologicalRing.tensorProductUniformSpace (R := B) (M := A) (N := C)
  let : TopologicalSpace
      (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) := inferInstance
  let c : (A ⊗[B] C) →+*
      TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C) :=
    UniformSpace.Completion.coeRingHom
  let il : A →+* A ⊗[B] C :=
    (Algebra.TensorProduct.includeLeft : A →ₐ[B] A ⊗[B] C).toRingHom
  let ir : C →+* A ⊗[B] C :=
    (Algebra.TensorProduct.includeRight : C →ₐ[B] A ⊗[B] C).toRingHom
  let K : Ideal (A ⊗[B] C) := RingHom.ker (sourceProjection I J i j)
  let L : Ideal (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C)) :=
    RingHom.ker (projectionRingHom I J bI bJ i j)
  have hK : K = (I i).map il + (J j).map ir := by
    let P : Submodule B A := (I i).restrictScalars B
    let Q : Submodule B C := (J j).restrictScalars B
    let T := TopologicalRing.tensorProductSubmodule P Q
    have hT : T = ((I i).map il + (J j).map ir).restrictScalars B := by
      show LinearMap.range (LinearMap.rTensor C P.subtype) ⊔
          LinearMap.range (LinearMap.lTensor A Q.subtype) =
        Submodule.restrictScalars B
          (Ideal.map il (I i) + Ideal.map ir (J j))
      rw [Ideal.add_eq_sup, Submodule.restrictScalars_sup B]
      dsimp [il, ir]
      rw [(Ideal.map_includeLeft_eq (R := B) (A := A) (B := C) (I i)).symm,
        (Ideal.map_includeRight_eq (R := B) (A := A) (B := C) (J j)).symm]
      rfl
    apply Ideal.ext
    intro z
    have hs := sourceProjection_ker (B := B) (A := A) (C := C) I J bI bJ i j z
    change sourceProjection I J i j z = 0 ↔ z ∈ T at hs
    show sourceProjection I J i j z = 0 ↔ z ∈ (I i).map il + (J j).map ir
    exact hs.trans (by rw [hT]; rfl)
  have hcomp (z : A ⊗[B] C) :
      projectionRingHom I J bI bJ i j (c z) = sourceProjection I J i j z :=
    (Classical.choose_spec (exists_completedTensorProductRingEquivQuotientLimit
      (B := B) (A := A) (C := C) I J bI bJ)).2.2 z i j
  have hLopen : IsOpen (L : Set
      (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))) :=
    isOpen_projectionKernel (B := B) (A := A) (C := C) I J bI bJ i j
  have hLclosed : IsClosed (L : Set
      (TopologicalRing.CompletedTensorProduct (R := B) (M := A) (N := C))) :=
    AddSubgroup.isClosed_of_isOpen L.toAddSubgroup hLopen
  have hmap_le : Ideal.map c K ≤ L := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun z hz => (hcomp z).trans hz
  have hclosure_le : Ideal.closure (Ideal.map c K) ≤ L := fun _ hx =>
    hLclosed.closure_subset_iff.mpr (fun _ hy => hmap_le hy) hx
  have hL_le : L ≤ Ideal.closure (Ideal.map c K) := fun x hx => by
    refine mem_closure_iff.mpr fun U hU hxU => ?_
    obtain ⟨y, hyO, z, rfl⟩ := mem_closure_iff.mp (UniformSpace.Completion.denseRange_coe x)
      _ (hU.inter hLopen) ⟨hxU, hx⟩
    have hzK : z ∈ K := (hcomp z).symm.trans hyO.2
    exact ⟨c z, ⟨hyO.1, Ideal.mem_map_of_mem c hzK⟩⟩
  have hEq : L = Ideal.closure (Ideal.map c K) := le_antisymm hL_le hclosure_le
  have hfinal : Ideal.map c ((I i).map il + (J j).map ir) =
      Ideal.map (c.comp il) (I i) + Ideal.map (c.comp ir) (J j) := by
    rw [Ideal.add_eq_sup, Ideal.map_sup, Ideal.map_map, Ideal.map_map,
      ← Ideal.add_eq_sup]
  ext x
  show x ∈ L ↔ x ∈ Ideal.closure
    (Ideal.map (c.comp il) (I i) + Ideal.map (c.comp ir) (J j))
  rw [hEq, hK, hfinal]

end

end TopologicalRing

end
