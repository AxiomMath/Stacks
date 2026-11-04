module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.UniformRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# The completed tensor product of linearly topologized modules

The tensor product `M ⊗[R] N` of two linearly topologized modules carries the topology whose
neighbourhood basis at zero is given by the submodules `P ⊗ N + M ⊗ Q` for `P`, `Q` open.  Its
separated completion is the *completed tensor product*.  This file builds the topology, shows
it is a linear topology (a ring topology when `M` and `N` are algebras), and identifies the
completion with the inverse limit of the discrete quotients `M/P ⊗ N/Q`.  The last section
computes the kernel of the canonical map in terms of the closure of an extended ideal.

## References

* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
* [Stacks Project, Tag 0AMZ](https://stacks.math.columbia.edu/tag/0AMZ)
-/

@[expose] public section

namespace TopologicalRing

section

open Filter Set
open scoped TensorProduct Topology


variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The image of `P ⊗[R] N + M ⊗[R] Q` in `M ⊗[R] N`. -/
def tensorProductSubmodule (P : Submodule R M) (Q : Submodule R N) :
    Submodule R (M ⊗[R] N) :=
  LinearMap.range (TensorProduct.map P.subtype LinearMap.id) ⊔
    LinearMap.range (TensorProduct.map LinearMap.id Q.subtype)

/-- The submodules defining the tensor product topology are monotone in both
arguments. -/
lemma tensorProductSubmodule_mono {P P' : Submodule R M} {Q Q' : Submodule R N}
    (hP : P ≤ P') (hQ : Q ≤ Q') :
    tensorProductSubmodule P Q ≤ tensorProductSubmodule P' Q' := by
  unfold tensorProductSubmodule
  apply sup_le
  · apply le_trans (TensorProduct.range_map_mono (by simpa) le_rfl) le_sup_left
  · apply le_trans (TensorProduct.range_map_mono le_rfl (by simpa)) le_sup_right

/-- An open submodule, used to index the canonical fundamental system of a
linearly topologized module. -/
abbrev OpenSubmodule (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] := { P : Submodule R M // IsOpen (P : Set M) }

variable [TopologicalSpace M] [TopologicalSpace N]

/-- Pairs of open submodules indexing the fundamental system for the tensor
product topology. -/
abbrev TensorProductSubmoduleIndex := OpenSubmodule R M × OpenSubmodule R N

/-- The fundamental submodule associated to a pair of open submodules. -/
def tensorProductSubmoduleBasis
    (i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N)) :
    Submodule R (M ⊗[R] N) :=
  tensorProductSubmodule i.1.1 i.2.1

/-- A quotient occurring in the first inverse limit in Tag 0AMU. -/
abbrev TensorProductQuotient
    (i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N)) :=
  (M ⊗[R] N) ⧸ tensorProductSubmoduleBasis i

/-- The transition map between two quotients of the usual tensor product. -/
def tensorProductQuotientTransition
    (i j : TensorProductSubmoduleIndex (R := R) (M := M) (N := N))
    (hM : i.1.1 ≤ j.1.1) (hN : i.2.1 ≤ j.2.1) :
    TensorProductQuotient i →ₗ[R] TensorProductQuotient j :=
  (tensorProductSubmoduleBasis i).mapQ (tensorProductSubmoduleBasis j) LinearMap.id
    (by
      change tensorProductSubmodule i.1.1 i.2.1 ≤ tensorProductSubmodule j.1.1 j.2.1
      exact tensorProductSubmodule_mono hM hN)

/-- Compatible families in the quotients
`(M ⊗[R] N) / (P ⊗[R] N + M ⊗[R] Q)`. -/
def tensorProductQuotientLimitSubmodule :
    Submodule R (∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TensorProductQuotient i) where
  carrier := { x | ∀ i j hM hN, tensorProductQuotientTransition i j hM hN (x i) = x j }
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i j hM hN
    simp only [Pi.add_apply, map_add, hx i j hM hN, hy i j hM hN]
  smul_mem' := by
    intro r x hx i j hM hN
    simp only [Pi.smul_apply, map_smul, hx i j hM hN]

/-- The inverse limit of the quotients of the usual tensor product by the
fundamental open submodules. -/
@[sga "3 VIIB 2.3.2" "more general"]
abbrev TensorProductQuotientLimit :=
  tensorProductQuotientLimitSubmodule (R := R) (M := M) (N := N)

/-- A tensor product of quotient modules occurring in the second inverse
limit in Tag 0AMU. -/
abbrev QuotientTensorProduct
    (i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N)) :=
  (M ⧸ i.1.1) ⊗[R] (N ⧸ i.2.1)

/-- The transition map between tensor products of quotient modules. -/
def quotientTensorProductTransition
    (i j : TensorProductSubmoduleIndex (R := R) (M := M) (N := N))
    (hM : i.1.1 ≤ j.1.1) (hN : i.2.1 ≤ j.2.1) :
    QuotientTensorProduct i →ₗ[R] QuotientTensorProduct j :=
  TensorProduct.map
    (i.1.1.mapQ j.1.1 LinearMap.id (by simpa using hM))
    (i.2.1.mapQ j.2.1 LinearMap.id (by simpa using hN))

/-- Compatible families in the tensor products `(M/P) ⊗[R] (N/Q)`. -/
def quotientTensorProductLimitSubmodule :
    Submodule R (∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      QuotientTensorProduct i) where
  carrier := { x | ∀ i j hM hN, quotientTensorProductTransition i j hM hN (x i) = x j }
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i j hM hN
    simp only [Pi.add_apply, map_add, hx i j hM hN, hy i j hM hN]
  smul_mem' := by
    intro r x hx i j hM hN
    simp only [Pi.smul_apply, map_smul, hx i j hM hN]

/-- The inverse limit of tensor products of the quotient modules. -/
abbrev QuotientTensorProductLimit :=
  quotientTensorProductLimitSubmodule (R := R) (M := M) (N := N)

/-- The projective-limit topology on compatible families of quotients of the
usual tensor product.  Each quotient in the system is discrete because its
kernel is one of the prescribed open submodules. -/
instance tensorProductQuotientLimitTopologicalSpace :
    TopologicalSpace (TensorProductQuotientLimit (R := R) (M := M) (N := N)) :=
  TopologicalSpace.induced Subtype.val
    (@Pi.topologicalSpace
      (TensorProductSubmoduleIndex (R := R) (M := M) (N := N))
      (fun i => TensorProductQuotient i) (fun _ => ⊥))

/-- The projective-limit topology on compatible families of tensor products
of quotient modules. -/
instance quotientTensorProductLimitTopologicalSpace :
    TopologicalSpace (QuotientTensorProductLimit (R := R) (M := M) (N := N)) :=
  TopologicalSpace.induced Subtype.val
    (@Pi.topologicalSpace
      (TensorProductSubmoduleIndex (R := R) (M := M) (N := N))
      (fun i => QuotientTensorProduct i) (fun _ => ⊥))

/-- The additive-group filter basis generated by the prescribed images of
tensor products with open submodules. -/
@[instance_reducible]
def tensorProductAddGroupFilterBasis : AddGroupFilterBasis (M ⊗[R] N) :=
  addGroupFilterBasisOfComm
    { U | ∃ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
        U = (tensorProductSubmoduleBasis i : Set (M ⊗[R] N)) }
    (by
      let i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N) :=
        (⟨⊤, isOpen_univ⟩, ⟨⊤, isOpen_univ⟩)
      exact ⟨(tensorProductSubmoduleBasis i : Set (M ⊗[R] N)), i, rfl⟩)
    (by
      rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
      let k : TensorProductSubmoduleIndex (R := R) (M := M) (N := N) :=
        (⟨i.1.1 ⊓ j.1.1, i.1.2.inter j.1.2⟩,
          ⟨i.2.1 ⊓ j.2.1, i.2.2.inter j.2.2⟩)
      refine ⟨(tensorProductSubmoduleBasis k : Set (M ⊗[R] N)), ⟨k, rfl⟩, ?_⟩
      change ∀ x, x ∈ tensorProductSubmoduleBasis k →
        x ∈ tensorProductSubmoduleBasis i ∧ x ∈ tensorProductSubmoduleBasis j
      intro x hx
      exact
        ⟨tensorProductSubmodule_mono inf_le_left inf_le_left hx,
          tensorProductSubmodule_mono inf_le_right inf_le_right hx⟩)
    (by
      rintro _ ⟨i, rfl⟩
      exact (tensorProductSubmoduleBasis i).zero_mem)
    (by
      rintro _ ⟨i, rfl⟩
      refine ⟨(tensorProductSubmoduleBasis i : Set (M ⊗[R] N)), ⟨i, rfl⟩, ?_⟩
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact (tensorProductSubmoduleBasis i).add_mem hx hy)
    (by
      rintro _ ⟨i, rfl⟩
      refine ⟨(tensorProductSubmoduleBasis i : Set (M ⊗[R] N)), ⟨i, rfl⟩, ?_⟩
      intro x hx
      exact (tensorProductSubmoduleBasis i).neg_mem hx)

/-- The topology on the usual tensor product whose fundamental open
submodules are the images of `P ⊗[R] N + M ⊗[R] Q` for open `P` and `Q`. -/
@[instance_reducible, stacks 0AMU "tensor product", ega "0 20.4.1"]
def tensorProductTopology : TopologicalSpace (M ⊗[R] N) :=
  (tensorProductAddGroupFilterBasis (R := R) (M := M) (N := N)).topology

/-- The prescribed submodules form a basis of neighbourhoods of zero for the
tensor product topology. -/
theorem hasBasis_tensorProductTopology :
    (@nhds (M ⊗[R] N) (tensorProductTopology (R := R) (M := M) (N := N)) 0).HasBasis
      (fun _ : TensorProductSubmoduleIndex (R := R) (M := M) (N := N) => True)
      (fun i => (tensorProductSubmoduleBasis i : Set (M ⊗[R] N))) := by
  refine
    (tensorProductAddGroupFilterBasis (R := R) (M := M) (N := N)).nhds_zero_hasBasis.to_hasBasis
      ?_ ?_
  · intro U hU
    rcases hU with ⟨i, rfl⟩
    exact ⟨i, trivial, Subset.rfl⟩
  · intro i _
    exact
      ⟨(tensorProductSubmoduleBasis i : Set (M ⊗[R] N)), ⟨i, rfl⟩, Subset.rfl⟩

/-- The tensor product topology is linear: the submodules `tensorProductSubmoduleBasis i`
form a basis of neighbourhoods of zero. -/
instance tensorProduct_isLinearTopology :
    @IsLinearTopology R (M ⊗[R] N) _ _ _
      (tensorProductTopology (R := R) (M := M) (N := N)) := by
  let _ := tensorProductTopology (R := R) (M := M) (N := N)
  exact IsLinearTopology.mk_of_hasBasis R
    (hasBasis_tensorProductTopology (R := R) (M := M) (N := N))

/-- Tensoring with a fixed element of the second factor is continuous. -/
lemma continuous_tmul_const [IsTopologicalAddGroup M] (n : N) :
    @Continuous M (M ⊗[R] N) _ (tensorProductTopology (R := R) (M := M) (N := N))
      (fun m => m ⊗ₜ[R] n) := by
  let _ := tensorProductTopology (R := R) (M := M) (N := N)
  apply continuous_of_continuousAt_zero ((TensorProduct.mk R M N).flip n)
  show Tendsto (fun m => m ⊗ₜ[R] n) (𝓝 0) (𝓝 (0 ⊗ₜ[R] n))
  rw [TensorProduct.zero_tmul]
  apply hasBasis_tensorProductTopology.tendsto_right_iff.mpr
  intro i _
  filter_upwards [i.1.2.mem_nhds i.1.1.zero_mem] with m hm
  exact Submodule.mem_sup_left ⟨(⟨m, hm⟩ : i.1.1) ⊗ₜ[R] n, rfl⟩

/-- Tensoring with a fixed element of the first factor is continuous. -/
lemma continuous_const_tmul [IsTopologicalAddGroup N] (m : M) :
    @Continuous N (M ⊗[R] N) _ (tensorProductTopology (R := R) (M := M) (N := N))
      (fun n => m ⊗ₜ[R] n) := by
  let _ := tensorProductTopology (R := R) (M := M) (N := N)
  apply continuous_of_continuousAt_zero (TensorProduct.mk R M N m)
  show Tendsto (fun n => m ⊗ₜ[R] n) (𝓝 0) (𝓝 (m ⊗ₜ[R] 0))
  rw [TensorProduct.tmul_zero]
  apply hasBasis_tensorProductTopology.tendsto_right_iff.mpr
  intro i _
  filter_upwards [i.2.2.mem_nhds i.2.1.zero_mem] with n hn
  exact Submodule.mem_sup_right ⟨m ⊗ₜ[R] (⟨n, hn⟩ : i.2.1), rfl⟩

/-- The canonical uniformity of the additive group carrying the tensor product
topology. -/
@[instance_reducible, sga "3 VIIB 0.5.A" "partial"]
def tensorProductUniformSpace : UniformSpace (M ⊗[R] N) :=
  @IsTopologicalAddGroup.rightUniformSpace (M ⊗[R] N) _
    (tensorProductTopology (R := R) (M := M) (N := N))
    ((tensorProductAddGroupFilterBasis (R := R) (M := M) (N := N)).isTopologicalAddGroup)

/-- The tensor product with its tensor product uniformity is a uniform additive group. -/
instance tensorProduct_isUniformAddGroup :
    @IsUniformAddGroup (M ⊗[R] N)
      (tensorProductUniformSpace (R := R) (M := M) (N := N)) _ := by
  let _ := tensorProductTopology (R := R) (M := M) (N := N)
  let _ : IsTopologicalAddGroup (M ⊗[R] N) := by infer_instance
  exact isUniformAddGroup_of_addCommGroup

/-- Scalar multiplication by a fixed element of `R` is uniformly continuous for the tensor
product uniformity. -/
instance tensorProduct_uniformContinuousConstSMul :
    @UniformContinuousConstSMul R (M ⊗[R] N)
      (tensorProductUniformSpace (R := R) (M := M) (N := N)) _ := by
  let _ := tensorProductTopology (R := R) (M := M) (N := N)
  let _ := tensorProductUniformSpace (R := R) (M := M) (N := N)
  constructor
  intro r
  apply uniformContinuous_of_continuousAt_zero (DistribSMul.toAddMonoidHom (M ⊗[R] N) r)
  exact IsLinearTopology.tendsto_smul_zero R (fun _ : M ⊗[R] N => r) id tendsto_id

/-- The completed tensor product of two topologized modules: the uniform
completion of their tensor product with its tensor product topology. -/
@[stacks 0AMU "completed tensor product",
  ega "0 7.7.2" "completed tensor product",
  ega "0 7.7.1",
  ega "0 7.7.5" "completed tensor product",
  sga "3 VIIB 0.3" "def of L⊗̂M",
  sga "3 VIIB 0.5.A" "def of M⊗̂_k N"]
abbrev CompletedTensorProduct :=
  @UniformSpace.Completion (M ⊗[R] N)
    (tensorProductUniformSpace (R := R) (M := M) (N := N))

/-- The uniform completion of a linearly topologized module is linearly topologized. -/
public lemma completion_linearTopology_module
    {S V : Type*} [Ring S] [AddCommGroup V] [Module S V]
    [UniformSpace V] [IsUniformAddGroup V] [UniformContinuousConstSMul S V]
    [IsLinearTopology S V] : IsLinearTopology S (UniformSpace.Completion V) := by
  let f : V →L[S] UniformSpace.Completion V := UniformSpace.Completion.toComplL
  constructor
  refine ⟨fun U => ⟨fun hU => ?_, fun ⟨P, hP, hPU⟩ => mem_of_superset hP hPU⟩⟩
  obtain ⟨C, ⟨hC, hclosed⟩, hCU⟩ := (closed_nhds_basis 0).mem_iff.mp hU
  have hpre : f ⁻¹' C ∈ 𝓝 0 :=
    f.continuous.continuousAt.preimage_mem_nhds (by simpa using hC)
  obtain ⟨P, hP, hPC⟩ := (IsLinearTopology.hasBasis_submodule S).mem_iff.mp hpre
  refine ⟨(P.map f.toLinearMap).topologicalClosure, ?_, ?_⟩
  · have hd : IsDenseInducing f := UniformSpace.Completion.isDenseInducing_coe
    exact hd.closure_image_mem_nhds hP
  · exact (closure_minimal (Set.image_subset_iff.mpr hPC) hclosed).trans hCU

/-- Completion preserves the linear topology of the tensor product. -/
instance completedTensorProduct_isLinearTopology :
    IsLinearTopology R (CompletedTensorProduct (R := R) (M := M) (N := N)) := by
  let _ := tensorProductUniformSpace (R := R) (M := M) (N := N)
  exact completion_linearTopology_module

section Algebras

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

private lemma tensorProductSubmodule_mul_mem (I : Ideal A) (J : Ideal B)
    (x y : A ⊗[R] B)
    (hy : y ∈ tensorProductSubmodule (I.restrictScalars R) (J.restrictScalars R)) :
    x * y ∈ tensorProductSubmodule (I.restrictScalars R) (J.restrictScalars R) := by
  let f := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R J)
  let P := tensorProductSubmodule (I.restrictScalars R) (J.restrictScalars R)
  have hf : f.toLinearMap =
      (TensorProduct.quotientTensorQuotientEquiv
        (I.restrictScalars R) (J.restrictScalars R)).symm.toLinearMap.comp P.mkQ := by
    ext a b
    rfl
  have hker (z : A ⊗[R] B) : f z = 0 ↔ z ∈ P := by
    have hz := LinearMap.congr_fun hf z
    change f z = (TensorProduct.quotientTensorQuotientEquiv
      (I.restrictScalars R) (J.restrictScalars R)).symm (Submodule.Quotient.mk z) at hz
    rw [hz]
    exact (LinearEquiv.map_eq_zero_iff _).trans (Submodule.Quotient.mk_eq_zero P)
  apply (hker (x * y)).mp
  rw [map_mul, (hker y).mpr hy, mul_zero]

variable [TopologicalSpace A] [TopologicalSpace B]
  [ContinuousAdd A] [ContinuousAdd B] [IsLinearTopology A A] [IsLinearTopology B B]

/-- For linearly topologized algebras the tensor topology has a basis of ideals. -/
instance tensorProduct_isLinearTopologyRing :
    @IsLinearTopology (A ⊗[R] B) (A ⊗[R] B) _ _ _
      (tensorProductTopology (R := R) (M := A) (N := B)) := by
  let _ := tensorProductTopology (R := R) (M := A) (N := B)
  have h : (𝓝 (0 : A ⊗[R] B)).HasBasis
      (fun ij : Ideal A × Ideal B => IsOpen (ij.1 : Set A) ∧ IsOpen (ij.2 : Set B))
      (fun ij => (tensorProductSubmodule (ij.1.restrictScalars R)
        (ij.2.restrictScalars R) : Set (A ⊗[R] B))) := by
    refine (hasBasis_tensorProductTopology (R := R) (M := A) (N := B)).to_hasBasis ?_ ?_
    · intro i _
      obtain ⟨I, hI, hIP⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp
        (i.1.2.mem_nhds i.1.1.zero_mem)
      obtain ⟨J, hJ, hJQ⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp
        (i.2.2.mem_nhds i.2.1.zero_mem)
      exact ⟨(I, J), ⟨hI, hJ⟩, tensorProductSubmodule_mono hIP hJQ⟩
    · intro ij hij
      exact ⟨(⟨ij.1.restrictScalars R, hij.1⟩, ⟨ij.2.restrictScalars R, hij.2⟩),
        trivial, Subset.rfl⟩
  let K : Ideal A × Ideal B → Ideal (A ⊗[R] B) := fun ij =>
    { (tensorProductSubmodule (ij.1.restrictScalars R)
        (ij.2.restrictScalars R)).toAddSubmonoid with
      smul_mem' := fun x y hy => tensorProductSubmodule_mul_mem ij.1 ij.2 x y hy }
  exact IsLinearTopology.mk_of_hasBasis (A ⊗[R] B) (s := K) h

/-- Multiplication is continuous for the tensor topology of linearly topologized algebras. -/
instance tensorProduct_isTopologicalRing :
    @IsTopologicalRing (A ⊗[R] B)
      (tensorProductTopology (R := R) (M := A) (N := B)) _ := by
  let _ := tensorProductTopology (R := R) (M := A) (N := B)
  apply IsTopologicalRing.of_addGroup_of_nhds_zero
  · exact IsLinearTopology.tendsto_mul_zero_of_right _ _ tendsto_snd
  · intro x
    exact IsLinearTopology.tendsto_mul_zero_of_right _ _ tendsto_id
  · intro x
    exact IsLinearTopology.tendsto_mul_zero_of_left _ _ tendsto_id

/-- Scalar multiplication from any algebra structure on the tensor product
is uniformly continuous in the tensor variable. In particular, the completion
inherits the algebra structures over both factors. -/
instance tensorProduct_uniformContinuousConstSMul_algebra
    {S : Type*} [CommSemiring S] [Algebra S (A ⊗[R] B)] :
    @UniformContinuousConstSMul S (A ⊗[R] B)
      (tensorProductUniformSpace (R := R) (M := A) (N := B)) _ := by
  let _ := tensorProductUniformSpace (R := R) (M := A) (N := B)
  let : ContinuousConstSMul S (A ⊗[R] B) := ⟨fun s => by
    simpa only [Algebra.smul_def] using continuous_const_mul (algebraMap S (A ⊗[R] B) s)⟩
  exact uniformContinuousConstSMul_of_continuousConstSMul S (A ⊗[R] B)

/-- The uniform completion of a linearly topologized commutative ring is linearly topologized
as a ring. -/
public lemma completion_linearTopology_ring
    {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
    [IsTopologicalRing S] [IsLinearTopology S S] :
    IsLinearTopology (UniformSpace.Completion S) (UniformSpace.Completion S) := by
  let C := UniformSpace.Completion S
  let : IsLinearTopology S C := completion_linearTopology_module
  let K (P : OpenSubmodule S C) : Ideal C :=
    { P.1.toAddSubmonoid with
      smul_mem' := by
        intro x y hy
        refine UniformSpace.Completion.induction_on x
          ((P.1.toAddSubgroup.isClosed_of_isOpen P.2).preimage (continuous_mul_const y)) ?_
        intro r
        show (r : UniformSpace.Completion S) * y ∈ P.1
        simpa only [Algebra.smul_def,
          show algebraMap S C r = (r : UniformSpace.Completion S) from rfl]
          using P.1.smul_mem r hy }
  apply IsLinearTopology.mk_of_hasBasis C (s := K) (p := fun _ => True)
  exact (IsLinearTopology.hasBasis_open_submodule S).to_hasBasis
    (fun P hP => ⟨⟨P, hP⟩, trivial, Subset.rfl⟩)
    (fun P _ => ⟨P.1, P.2, Subset.rfl⟩)

/-- The completed tensor product of linearly topologized algebras is linearly
topologized as a ring, as well as as an `R`-module. -/
instance completedTensorProduct_isLinearTopologyRing :
    IsLinearTopology (CompletedTensorProduct (R := R) (M := A) (N := B))
      (CompletedTensorProduct (R := R) (M := A) (N := B)) := by
  let _ := tensorProductUniformSpace (R := R) (M := A) (N := B)
  exact completion_linearTopology_ring

end Algebras

section TopologicalAlgebras

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] [ContinuousAdd B]
  [IsLinearTopology A A] [IsLinearTopology B B] [TopologicalSpace R] [ContinuousSMul R A]

/-- A continuous scalar algebra map to the first factor gives a continuous
scalar action on the tensor product. -/
instance tensorProduct_continuousSMul :
    @ContinuousSMul R (A ⊗[R] B) _ _
      (tensorProductTopology (R := R) (M := A) (N := B)) := by
  let _ := tensorProductTopology (R := R) (M := A) (N := B)
  apply continuousSMul_of_algebraMap R (A ⊗[R] B)
  exact (continuous_tmul_const (R := R) (1 : B)).comp (continuous_algebraMap R A)

/-- The completed tensor product is a topological `R`-algebra when the first
factor is a topological `R`-algebra. -/
instance completedTensorProduct_continuousSMul :
    ContinuousSMul R (CompletedTensorProduct (R := R) (M := A) (N := B)) := by
  let _ := tensorProductUniformSpace (R := R) (M := A) (N := B)
  apply continuousSMul_of_algebraMap R (CompletedTensorProduct (R := R) (M := A) (N := B))
  exact (UniformSpace.Completion.continuous_coe (A ⊗[R] B)).comp
    (continuous_algebraMap R (A ⊗[R] B))

end TopologicalAlgebras

/-- The quotient-tensor-quotient comparison at one pair of open submodules. -/
@[ega "0 11.8.2" "partial", ega "III 2.1.11" "partial"]
noncomputable abbrev quotientTensorQuotientComponentEquiv
    (i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N)) :
    QuotientTensorProduct i ≃ₗ[R] TensorProductQuotient i :=
  TensorProduct.quotientTensorQuotientEquiv i.1.1 i.2.1

private lemma quotientTensorQuotientEquiv_naturality
    (i j : TensorProductSubmoduleIndex (R := R) (M := M) (N := N))
    (hM : i.1.1 ≤ j.1.1) (hN : i.2.1 ≤ j.2.1) :
    (tensorProductQuotientTransition i j hM hN).comp
        (quotientTensorQuotientComponentEquiv i).toLinearMap =
      (quotientTensorQuotientComponentEquiv j).toLinearMap.comp
        (quotientTensorProductTransition i j hM hN) := by
  ext x y
  rfl

/-- The linear equivalence between the two compatible-family descriptions,
obtained from the quotient-tensor-quotient equivalence in each component. -/
@[implicit_reducible]
noncomputable def quotientTensorProductLimitLinearEquiv :
    QuotientTensorProductLimit (R := R) (M := M) (N := N) ≃ₗ[R]
      TensorProductQuotientLimit (R := R) (M := M) (N := N) where
  toFun x :=
    ⟨fun i => quotientTensorQuotientComponentEquiv i
        ((x : ∀ i, QuotientTensorProduct i) i), by
      intro i j hM hN
      exact LinearMap.congr_fun
        (quotientTensorQuotientEquiv_naturality i j hM hN)
          ((x : ∀ i, QuotientTensorProduct i) i) |>.trans
          (congr_arg
            (TensorProduct.quotientTensorQuotientEquiv j.1.1 j.2.1)
            (x.2 i j hM hN))⟩
  invFun x :=
    ⟨fun i => (quotientTensorQuotientComponentEquiv i).symm
        ((x : ∀ i, TensorProductQuotient i) i), by
      intro i j hM hN
      dsimp only
      apply (quotientTensorQuotientComponentEquiv j).injective
      rw [LinearEquiv.apply_symm_apply]
      change
        quotientTensorQuotientComponentEquiv j
            (quotientTensorProductTransition i j hM hN
              ((quotientTensorQuotientComponentEquiv i).symm
                ((x : ∀ i, TensorProductQuotient i) i))) =
          (x : ∀ i, TensorProductQuotient i) j
      calc
        _ = tensorProductQuotientTransition i j hM hN
              (quotientTensorQuotientComponentEquiv i
                ((quotientTensorQuotientComponentEquiv i).symm
                  ((x : ∀ i, TensorProductQuotient i) i))) :=
            (LinearMap.congr_fun
              (quotientTensorQuotientEquiv_naturality i j hM hN)
              ((quotientTensorQuotientComponentEquiv i).symm
                ((x : ∀ i, TensorProductQuotient i) i))).symm
        _ = tensorProductQuotientTransition i j hM hN
              ((x : ∀ i, TensorProductQuotient i) i) := by
            rw [LinearEquiv.apply_symm_apply]
        _ = (x : ∀ i, TensorProductQuotient i) j := x.2 i j hM hN⟩
  left_inv x := by
    ext i
    exact LinearEquiv.symm_apply_apply _ _
  right_inv x := by
    ext i
    exact LinearEquiv.apply_symm_apply _ _
  map_add' x y := by
    ext i
    exact map_add _ _ _
  map_smul' r x := by
    ext i
    exact (quotientTensorQuotientComponentEquiv i).map_smul r
      ((x : ∀ i, QuotientTensorProduct i) i)

private lemma continuous_quotientTensorProductLimitLinearEquiv :
    Continuous (quotientTensorProductLimitLinearEquiv (R := R) (M := M) (N := N)) := by
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TopologicalSpace (TensorProductQuotient i) := fun _ => ⊥
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TopologicalSpace (QuotientTensorProduct i) := fun _ => ⊥
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      DiscreteTopology (QuotientTensorProduct i) := fun _ => ⟨rfl⟩
  rw [continuous_induced_rng]
  refine continuous_pi fun i => ?_
  show Continuous (fun x : QuotientTensorProductLimit (R := R) (M := M) (N := N) =>
    quotientTensorQuotientComponentEquiv i ((x : ∀ i, QuotientTensorProduct i) i))
  exact continuous_of_discreteTopology.comp
    ((continuous_apply i).comp continuous_subtype_val)

private lemma continuous_quotientTensorProductLimitLinearEquiv_symm :
    Continuous
      (quotientTensorProductLimitLinearEquiv (R := R) (M := M) (N := N)).symm := by
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TopologicalSpace (TensorProductQuotient i) := fun _ => ⊥
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TopologicalSpace (QuotientTensorProduct i) := fun _ => ⊥
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      DiscreteTopology (TensorProductQuotient i) := fun _ => ⟨rfl⟩
  rw [continuous_induced_rng]
  refine continuous_pi fun i => ?_
  show Continuous (fun x : TensorProductQuotientLimit (R := R) (M := M) (N := N) =>
    (quotientTensorQuotientComponentEquiv i).symm
      ((x : ∀ i, TensorProductQuotient i) i))
  exact continuous_of_discreteTopology.comp
    ((continuous_apply i).comp continuous_subtype_val)

/-- The componentwise quotient-tensor-quotient equivalences identify the two
inverse limits in Tag 0AMU.  The specification records that the map is exactly
`TensorProduct.quotientTensorQuotientEquiv` in every component. -/
@[implicit_reducible,
  stacks 0AMU "second inverse-limit identification",
  ega "0 7.7.2" "(M/V)⊗(N/W) identif.",
  ega "0 7.7.1" "lim M/V ⊗ N/W",
  ega "0 7.7.5" "lim M/Mμ ⊗ N/Nν", sga "3 VIIB 0.3" "lim (L/L')⊗(M/M')"]
noncomputable def quotientTensorProductLimitIdentification :
    { e : QuotientTensorProductLimit (R := R) (M := M) (N := N) ≃L[R]
        TensorProductQuotientLimit (R := R) (M := M) (N := N) //
      ∀ x : QuotientTensorProductLimit (R := R) (M := M) (N := N),
        ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
          ((e x : TensorProductQuotientLimit (R := R) (M := M) (N := N)) :
              ∀ j : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
                TensorProductQuotient j) i =
            TensorProduct.quotientTensorQuotientEquiv i.1.1 i.2.1
              (((x : QuotientTensorProductLimit (R := R) (M := M) (N := N)) :
                  ∀ j : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
                    QuotientTensorProduct j) i) } :=
  ⟨{ quotientTensorProductLimitLinearEquiv with
      continuous_toFun := by exact continuous_quotientTensorProductLimitLinearEquiv
      continuous_invFun := by exact continuous_quotientTensorProductLimitLinearEquiv_symm },
    fun _ _ => rfl⟩

/-- The continuous linear equivalence underlying
`quotientTensorProductLimitIdentification`. -/
noncomputable abbrev quotientTensorProductLimitEquiv :=
  (quotientTensorProductLimitIdentification (R := R) (M := M) (N := N)).1

private def tensorProductToQuotientLimit :
    (M ⊗[R] N) →ₗ[R] TensorProductQuotientLimit (R := R) (M := M) (N := N) where
  toFun z := ⟨fun i => Submodule.Quotient.mk z, by
    intro i j hM hN
    rfl⟩
  map_add' x y := by
    ext i
    exact map_add ((tensorProductSubmoduleBasis i).mkQ) x y
  map_smul' r x := by
    ext i
    exact map_smul ((tensorProductSubmoduleBasis i).mkQ) r x

@[instance_reducible]
private def quotientLimitUniformSpace :
    UniformSpace (TensorProductQuotientLimit (R := R) (M := M) (N := N)) := by
  letI : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      UniformSpace (TensorProductQuotient i) := fun _ => ⊥
  exact UniformSpace.comap Subtype.val inferInstance

private lemma quotientLimit_isClosed :
    @IsClosed
      (∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
        TensorProductQuotient i)
      (@Pi.topologicalSpace
        (TensorProductSubmoduleIndex (R := R) (M := M) (N := N))
        (fun i => TensorProductQuotient i) (fun _ => ⊥))
      (tensorProductQuotientLimitSubmodule (R := R) (M := M) (N := N) : Set _) := by
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TopologicalSpace (TensorProductQuotient i) := fun _ => ⊥
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      DiscreteTopology (TensorProductQuotient i) := fun _ => ⟨rfl⟩
  show IsClosed {x : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TensorProductQuotient i |
    ∀ i j hM hN, tensorProductQuotientTransition i j hM hN (x i) = x j}
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  repeat' (apply isClosed_iInter; intro _)
  exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply i))
    (continuous_apply j)

private instance quotientLimit_completeSpace :
    @CompleteSpace (TensorProductQuotientLimit (R := R) (M := M) (N := N))
      (quotientLimitUniformSpace (R := R) (M := M) (N := N)) := by
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      UniformSpace (TensorProductQuotient i) := fun _ => ⊥
  have : IsClosed (tensorProductQuotientLimitSubmodule (R := R) (M := M) (N := N) :
      Set (∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
        TensorProductQuotient i)) := quotientLimit_isClosed
  infer_instance

private instance quotientLimit_t0Space :
    @T0Space (TensorProductQuotientLimit (R := R) (M := M) (N := N))
      (tensorProductQuotientLimitTopologicalSpace (R := R) (M := M) (N := N)) := by
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TopologicalSpace (TensorProductQuotient i) := fun _ => ⊥
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      DiscreteTopology (TensorProductQuotient i) := fun _ => ⟨rfl⟩
  infer_instance

private lemma quotientLimit_commonRefinement
    (s : Finset (TensorProductSubmoduleIndex (R := R) (M := M) (N := N))) :
    ∃ k : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      ∀ i ∈ s, k.1.1 ≤ i.1.1 ∧ k.2.1 ≤ i.2.1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨(⟨⊤, isOpen_univ⟩, ⟨⊤, isOpen_univ⟩), by simp⟩
  | @insert i s hi ih =>
      obtain ⟨k, hk⟩ := ih
      let l : TensorProductSubmoduleIndex (R := R) (M := M) (N := N) :=
        (⟨i.1.1 ⊓ k.1.1, i.1.2.inter k.1.2⟩,
         ⟨i.2.1 ⊓ k.2.1, i.2.2.inter k.2.2⟩)
      refine ⟨l, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨inf_le_left, inf_le_left⟩
      · obtain ⟨hM, hN⟩ := hk j hj
        exact ⟨inf_le_right.trans hM, inf_le_right.trans hN⟩

private lemma quotientLimit_finiteApprox
    (x : TensorProductQuotientLimit (R := R) (M := M) (N := N))
    (s : Finset (TensorProductSubmoduleIndex (R := R) (M := M) (N := N))) :
    ∃ z : M ⊗[R] N, ∀ i ∈ s,
      ((tensorProductToQuotientLimit (R := R) (M := M) (N := N) z :
          TensorProductQuotientLimit (R := R) (M := M) (N := N)) :
          ∀ j, TensorProductQuotient j) i = x.1 i := by
  obtain ⟨k, hk⟩ := quotientLimit_commonRefinement s
  obtain ⟨z, hz⟩ := (tensorProductSubmoduleBasis k).mkQ_surjective (x.1 k)
  refine ⟨z, ?_⟩
  intro i hi
  obtain ⟨hM, hN⟩ := hk i hi
  simpa [tensorProductToQuotientLimit, tensorProductQuotientTransition, ← hz] using
    x.2 k i hM hN

private lemma quotientLimit_denseRange :
    DenseRange (tensorProductToQuotientLimit (R := R) (M := M) (N := N)) := by
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TopologicalSpace (TensorProductQuotient i) := fun _ => ⊥
  intro x
  apply mem_closure_iff.mpr
  intro o ho hxo
  obtain ⟨u, hu, rfl⟩ := isOpen_induced_iff.mp ho
  obtain ⟨s, v, hv, hsub⟩ := isOpen_pi_iff.mp hu x.1 hxo
  obtain ⟨z, hz⟩ := quotientLimit_finiteApprox x s
  refine ⟨tensorProductToQuotientLimit z, ?_, ⟨z, rfl⟩⟩
  apply hsub
  intro i hi
  rw [hz i hi]
  exact (hv i hi).2

private lemma continuous_tensorProductQuotientMap
    (i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N)) :
    @Continuous (M ⊗[R] N) (TensorProductQuotient i)
      (tensorProductTopology (R := R) (M := M) (N := N)) ⊥
      (fun z => Submodule.Quotient.mk z) := by
  let := tensorProductTopology (R := R) (M := M) (N := N)
  let : TopologicalSpace (TensorProductQuotient i) := ⊥
  let : DiscreteTopology (TensorProductQuotient i) := ⟨rfl⟩
  apply continuous_of_continuousAt_zero (tensorProductSubmoduleBasis i).mkQ
  show Tendsto (fun z : M ⊗[R] N => Submodule.Quotient.mk z)
    (𝓝 0) (𝓝 (0 : TensorProductQuotient i))
  rw [show 𝓝 (0 : TensorProductQuotient i) = pure 0 from
    congrFun (nhds_discrete (TensorProductQuotient i)) 0, tendsto_pure]
  apply Filter.mem_of_superset
    ((hasBasis_tensorProductTopology (R := R) (M := M) (N := N)).mem_of_mem (i := i) trivial)
  intro z hz
  exact (Submodule.Quotient.mk_eq_zero (tensorProductSubmoduleBasis i)).mpr hz

private lemma continuous_tensorProductToQuotientLimit :
    @Continuous (M ⊗[R] N)
      (TensorProductQuotientLimit (R := R) (M := M) (N := N))
      (tensorProductTopology (R := R) (M := M) (N := N))
      (tensorProductQuotientLimitTopologicalSpace (R := R) (M := M) (N := N))
      (tensorProductToQuotientLimit (R := R) (M := M) (N := N)) := by
  let := tensorProductTopology (R := R) (M := M) (N := N)
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TopologicalSpace (TensorProductQuotient i) := fun _ => ⊥
  rw [continuous_induced_rng]
  exact continuous_pi fun i => continuous_tensorProductQuotientMap i

private instance quotientLimit_isTopologicalAddGroup :
    @IsTopologicalAddGroup
      (TensorProductQuotientLimit (R := R) (M := M) (N := N))
      (tensorProductQuotientLimitTopologicalSpace (R := R) (M := M) (N := N)) _ := by
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TopologicalSpace (TensorProductQuotient i) := fun _ => ⊥
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      DiscreteTopology (TensorProductQuotient i) := fun _ => ⟨rfl⟩
  infer_instance

private lemma quotientLimit_isInducing :
    @Topology.IsInducing (M ⊗[R] N)
      (TensorProductQuotientLimit (R := R) (M := M) (N := N))
      (tensorProductTopology (R := R) (M := M) (N := N))
      (tensorProductQuotientLimitTopologicalSpace (R := R) (M := M) (N := N))
      (tensorProductToQuotientLimit (R := R) (M := M) (N := N)) := by
  let := tensorProductTopology (R := R) (M := M) (N := N)
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TopologicalSpace (TensorProductQuotient i) := fun _ => ⊥
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      DiscreteTopology (TensorProductQuotient i) := fun _ => ⟨rfl⟩
  apply IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr
  apply le_antisymm
  · apply Filter.tendsto_iff_comap.mp
    simpa using (continuous_tensorProductToQuotientLimit
      (R := R) (M := M) (N := N)).continuousAt (x := (0 : M ⊗[R] N)) |>.tendsto
  · intro U hU
    obtain ⟨i, _, hi⟩ :=
      (hasBasis_tensorProductTopology (R := R) (M := M) (N := N)).mem_iff.mp hU
    let V : Set (TensorProductQuotientLimit (R := R) (M := M) (N := N)) :=
      {x | x.1 i = 0}
    have hproj : Continuous (fun x : TensorProductQuotientLimit (R := R) (M := M) (N := N) =>
        x.1 i) := (continuous_apply i).comp continuous_subtype_val
    have hV : V ∈ 𝓝 (0 : TensorProductQuotientLimit (R := R) (M := M) (N := N)) :=
      ((isOpen_discrete {0}).preimage hproj).mem_nhds (by simp)
    apply Filter.mem_of_superset (Filter.mem_comap.mpr ⟨V, hV, ?_⟩) hi
    intro z hz
    exact (Submodule.Quotient.mk_eq_zero (tensorProductSubmoduleBasis i)).mp hz

private instance quotientLimit_isUniformAddGroup :
    @IsUniformAddGroup
      (TensorProductQuotientLimit (R := R) (M := M) (N := N))
      (quotientLimitUniformSpace (R := R) (M := M) (N := N)) _ := by
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      UniformSpace (TensorProductQuotient i) := fun _ => ⊥
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      DiscreteUniformity (TensorProductQuotient i) := fun _ => inferInstance
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      IsUniformAddGroup (TensorProductQuotient i) := fun _ => inferInstance
  exact (tensorProductQuotientLimitSubmodule
    (R := R) (M := M) (N := N)).toAddSubgroup.isUniformAddGroup

private instance quotientLimit_continuousConstSMul :
    @ContinuousConstSMul R
      (TensorProductQuotientLimit (R := R) (M := M) (N := N))
      (tensorProductQuotientLimitTopologicalSpace (R := R) (M := M) (N := N)) _ := by
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TopologicalSpace (TensorProductQuotient i) := fun _ => ⊥
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      DiscreteTopology (TensorProductQuotient i) := fun _ => ⟨rfl⟩
  constructor
  intro r
  rw [continuous_induced_rng]
  refine continuous_pi fun i => ?_
  change Continuous (fun x : TensorProductQuotientLimit (R := R) (M := M) (N := N) =>
    r • x.1 i)
  exact continuous_of_discreteTopology.comp
    ((continuous_apply i).comp continuous_subtype_val)

private instance quotientLimit_continuousAdd :
    @ContinuousAdd
      (TensorProductQuotientLimit (R := R) (M := M) (N := N))
      (tensorProductQuotientLimitTopologicalSpace (R := R) (M := M) (N := N)) _ := by
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TopologicalSpace (TensorProductQuotient i) := fun _ => ⊥
  let : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      DiscreteTopology (TensorProductQuotient i) := fun _ => ⟨rfl⟩
  constructor
  rw [continuous_induced_rng]
  refine continuous_pi fun i => ?_
  change Continuous (fun p :
    TensorProductQuotientLimit (R := R) (M := M) (N := N) ×
      TensorProductQuotientLimit (R := R) (M := M) (N := N) => p.1.1 i + p.2.1 i)
  exact (((continuous_apply i).comp continuous_subtype_val).comp continuous_fst).add
    (((continuous_apply i).comp continuous_subtype_val).comp continuous_snd)

private lemma quotientLimit_isUniformInducing :
    @IsUniformInducing (M ⊗[R] N)
      (TensorProductQuotientLimit (R := R) (M := M) (N := N))
      (tensorProductUniformSpace (R := R) (M := M) (N := N))
      (quotientLimitUniformSpace (R := R) (M := M) (N := N))
      (tensorProductToQuotientLimit (R := R) (M := M) (N := N)) := by
  let := tensorProductUniformSpace (R := R) (M := M) (N := N)
  let := quotientLimitUniformSpace (R := R) (M := M) (N := N)
  exact AddMonoidHom.isUniformInducing_of_isInducing
    (quotientLimit_isInducing (R := R) (M := M) (N := N))

/-- The completion is canonically topologically linearly isomorphic to the
inverse limit of its discrete quotients. Every component of the identification
extends the usual quotient map. -/
@[stacks 0AMU "first inverse-limit identification",
  ega "0 7.7.2" "lim (M⊗N)/(...) identif.",
  ega "0 7.7.1" "limit identification",
  ega "0 7.7.5" "lim (M⊗N)/(Mμ⊗N+M⊗Nν)",
  sga "3 VIIB 0.3" "P = lim quotients"]
theorem exists_completedTensorProductEquivQuotientLimit :
    ∃ e : CompletedTensorProduct (R := R) (M := M) (N := N) ≃L[R]
        TensorProductQuotientLimit (R := R) (M := M) (N := N),
      ∀ z : M ⊗[R] N,
        ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
          ((e (↑z : CompletedTensorProduct (R := R) (M := M) (N := N)) :
              TensorProductQuotientLimit (R := R) (M := M) (N := N)) :
              ∀ j : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
                TensorProductQuotient j) i = Submodule.Quotient.mk z := by
  let := tensorProductUniformSpace (R := R) (M := M) (N := N)
  let := quotientLimitUniformSpace (R := R) (M := M) (N := N)
  let pkg : AbstractCompletion (M ⊗[R] N) :=
    { space := TensorProductQuotientLimit (R := R) (M := M) (N := N)
      coe := tensorProductToQuotientLimit (R := R) (M := M) (N := N)
      uniformStruct := quotientLimitUniformSpace (R := R) (M := M) (N := N)
      complete := quotientLimit_completeSpace (R := R) (M := M) (N := N)
      separation := quotientLimit_t0Space (R := R) (M := M) (N := N)
      isUniformInducing := quotientLimit_isUniformInducing (R := R) (M := M) (N := N)
      dense := quotientLimit_denseRange (R := R) (M := M) (N := N) }
  let eU : CompletedTensorProduct (R := R) (M := M) (N := N) ≃ᵤ
      TensorProductQuotientLimit (R := R) (M := M) (N := N) :=
    UniformSpace.Completion.cPkg.compareEquiv pkg
  have heU (z : M ⊗[R] N) :
      eU (z : CompletedTensorProduct (R := R) (M := M) (N := N)) =
        tensorProductToQuotientLimit z :=
    UniformSpace.Completion.cPkg.compare_coe pkg z
  have hadd (x y : CompletedTensorProduct (R := R) (M := M) (N := N)) :
      eU (x + y) = eU x + eU y := by
    refine UniformSpace.Completion.induction_on₂
      (p := fun x y => eU (x + y) = eU x + eU y) x y
      (isClosed_eq (eU.continuous.comp (continuous_fst.add continuous_snd))
        ((eU.continuous.comp continuous_fst).add (eU.continuous.comp continuous_snd)))
      fun a b => ?_
    simp only [← UniformSpace.Completion.coe_add, heU]
    exact (tensorProductToQuotientLimit (R := R) (M := M) (N := N)).map_add a b
  have hsmul (r : R) (x : CompletedTensorProduct (R := R) (M := M) (N := N)) :
      eU (r • x) = r • eU x := by
    refine UniformSpace.Completion.induction_on
      (p := fun x => eU (r • x) = r • eU x) x
      (isClosed_eq (eU.continuous.comp (continuous_const_smul r))
        ((continuous_const_smul r).comp eU.continuous)) fun a => ?_
    simpa only [← UniformSpace.Completion.coe_smul, heU] using
      (tensorProductToQuotientLimit (R := R) (M := M) (N := N)).map_smul r a
  exact ⟨{ eU.toEquiv with
      map_add' := hadd
      map_smul' := hsmul
      continuous_toFun := eU.continuous
      continuous_invFun := eU.symm.continuous },
    fun z i => (congrFun (congrArg Subtype.val (heU z)) i).trans rfl⟩

/-- The canonical topological linear identification, together with its
characterization on the dense image of the usual tensor product. -/
@[implicit_reducible, sga "3 VIIB 0.3" "partial"]
noncomputable def completedTensorProductLimitIdentification :
    { e : CompletedTensorProduct (R := R) (M := M) (N := N) ≃L[R]
        TensorProductQuotientLimit (R := R) (M := M) (N := N) //
      ∀ z : M ⊗[R] N,
        ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
          ((e (↑z : CompletedTensorProduct (R := R) (M := M) (N := N)) :
              TensorProductQuotientLimit (R := R) (M := M) (N := N)) :
              ∀ j : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
                TensorProductQuotient j) i = Submodule.Quotient.mk z } :=
  ⟨Classical.choose (exists_completedTensorProductEquivQuotientLimit
      (R := R) (M := M) (N := N)),
    Classical.choose_spec (exists_completedTensorProductEquivQuotientLimit
      (R := R) (M := M) (N := N))⟩

/-- The continuous linear equivalence underlying
`completedTensorProductLimitIdentification`. -/
@[sga "3 VIIB 0.3" "partial"]
noncomputable abbrev completedTensorProductEquivQuotientLimit :=
  (completedTensorProductLimitIdentification (R := R) (M := M) (N := N)).1

/-- The canonical projection from the completed tensor product to one of its
discrete tensor-product quotients. -/
@[implicit_reducible]
noncomputable def completedTensorProductQuotientMap
    (i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N)) :
    CompletedTensorProduct (R := R) (M := M) (N := N) →ₗ[R]
      TensorProductQuotient i :=
  (LinearMap.proj i).comp
    ((tensorProductQuotientLimitSubmodule (R := R) (M := M) (N := N)).subtype.comp
      (completedTensorProductEquivQuotientLimit
        (R := R) (M := M) (N := N)).toLinearEquiv.toLinearMap)

/-- A quotient projection extends the corresponding quotient map on the
usual tensor product. -/
@[simp]
theorem completedTensorProductQuotientMap_coe
    (i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N))
    (z : M ⊗[R] N) :
    completedTensorProductQuotientMap (R := R) (M := M) (N := N) i
        (↑z : CompletedTensorProduct (R := R) (M := M) (N := N)) =
      Submodule.Quotient.mk z :=
  (completedTensorProductLimitIdentification (R := R) (M := M) (N := N)).2 z i

/-- A quotient projection sends the dense image of a pure tensor to its
residue class. -/
@[simp]
theorem completedTensorProductQuotientMap_coe_tmul
    (i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N))
    (x : M) (y : N) :
    completedTensorProductQuotientMap (R := R) (M := M) (N := N) i
        (↑(x ⊗ₜ[R] y) : CompletedTensorProduct (R := R) (M := M) (N := N)) =
      Submodule.Quotient.mk (x ⊗ₜ[R] y) :=
  completedTensorProductQuotientMap_coe i (x ⊗ₜ[R] y)

/-- The quotient projections from the completion form a compatible family. -/
theorem completedTensorProductQuotientMap_compatible
    (i j : TensorProductSubmoduleIndex (R := R) (M := M) (N := N))
    (hM : i.1.1 ≤ j.1.1) (hN : i.2.1 ≤ j.2.1) :
    (tensorProductQuotientTransition i j hM hN).comp
        (completedTensorProductQuotientMap (R := R) (M := M) (N := N) i) =
      completedTensorProductQuotientMap (R := R) (M := M) (N := N) j := by
  ext x
  exact (completedTensorProductEquivQuotientLimit
    (R := R) (M := M) (N := N) x).2 i j hM hN

/-- The canonical quotient projections are continuous for the discrete
topology on the quotients. -/
theorem continuous_completedTensorProductQuotientMap
    (i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N)) :
    @Continuous _ _ inferInstance ⊥
      (completedTensorProductQuotientMap (R := R) (M := M) (N := N) i) := by
  let : ∀ j : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      TopologicalSpace (TensorProductQuotient j) := fun _ => ⊥
  exact ((continuous_apply i).comp continuous_subtype_val).comp
    (completedTensorProductEquivQuotientLimit (R := R) (M := M) (N := N)).continuous

/-- Elements of the completed tensor product are determined by all their
quotient projections. -/
@[ext]
theorem completedTensorProduct_ext
    {x y : CompletedTensorProduct (R := R) (M := M) (N := N)}
    (h : ∀ i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
      completedTensorProductQuotientMap i x = completedTensorProductQuotientMap i y) :
    x = y :=
  (completedTensorProductEquivQuotientLimit (R := R) (M := M) (N := N)).injective
    (Subtype.ext (funext h))

/-- The completed tensor product identified with the inverse limit of tensor
products of quotient modules. -/
noncomputable abbrev completedTensorProductEquivQuotientTensorLimit :=
  (completedTensorProductEquivQuotientLimit (R := R) (M := M) (N := N)).trans
    (quotientTensorProductLimitEquiv (R := R) (M := M) (N := N)).symm

/-- The canonical projection to a tensor product of quotient modules. -/
@[implicit_reducible]
noncomputable def completedTensorProductTensorQuotientMap
    (i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N)) :
    CompletedTensorProduct (R := R) (M := M) (N := N) →ₗ[R]
      QuotientTensorProduct i :=
  (quotientTensorQuotientComponentEquiv i).symm.toLinearMap.comp
    (completedTensorProductQuotientMap i)

/-- The second kind of quotient projection sends a pure tensor to the tensor
of the residue classes of its factors. -/
@[simp]
theorem completedTensorProductTensorQuotientMap_coe_tmul
    (i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N))
    (x : M) (y : N) :
    completedTensorProductTensorQuotientMap (R := R) (M := M) (N := N) i
        (↑(x ⊗ₜ[R] y) : CompletedTensorProduct (R := R) (M := M) (N := N)) =
      Submodule.Quotient.mk x ⊗ₜ[R] Submodule.Quotient.mk y := by
  show (quotientTensorQuotientComponentEquiv i).symm
      (completedTensorProductQuotientMap i ↑(x ⊗ₜ[R] y)) = _
  rw [completedTensorProductQuotientMap_coe_tmul]
  exact TensorProduct.quotientTensorQuotientEquiv_symm_apply_mk_tmul _ _ _ _

/-- The second quotient projection is the corresponding coordinate of the
canonical inverse-limit identification. -/
@[simp]
theorem completedTensorProductEquivQuotientTensorLimit_apply
    (x : CompletedTensorProduct (R := R) (M := M) (N := N))
    (i : TensorProductSubmoduleIndex (R := R) (M := M) (N := N)) :
    ((completedTensorProductEquivQuotientTensorLimit x :
        QuotientTensorProductLimit (R := R) (M := M) (N := N)) :
        ∀ j : TensorProductSubmoduleIndex (R := R) (M := M) (N := N),
          QuotientTensorProduct j) i = completedTensorProductTensorQuotientMap i x := rfl

/-- The projections to tensor products of quotients form a compatible family. -/
theorem completedTensorProductTensorQuotientMap_compatible
    (i j : TensorProductSubmoduleIndex (R := R) (M := M) (N := N))
    (hM : i.1.1 ≤ j.1.1) (hN : i.2.1 ≤ j.2.1) :
    (quotientTensorProductTransition i j hM hN).comp
        (completedTensorProductTensorQuotientMap (R := R) (M := M) (N := N) i) =
      completedTensorProductTensorQuotientMap (R := R) (M := M) (N := N) j := by
  ext x
  exact (completedTensorProductEquivQuotientTensorLimit
    (R := R) (M := M) (N := N) x).2 i j hM hN

end

section

open scoped TensorProduct Pointwise Topology
open Filter Set


private lemma completedTensorProduct_component_eq_zero_of_mem
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (P : Submodule A B) (Q : Submodule A (A ⧸ I))
    (b : B) (hb : b ∈ Submodule.restrictScalars A (Ideal.map (algebraMap A B) I) ⊔ P) :
    (Submodule.Quotient.mk b : B ⧸ P) ⊗ₜ[A]
        (Submodule.Quotient.mk (Ideal.Quotient.mk I (1 : A)) :
          (A ⧸ I) ⧸ Q) = 0 := by
  let φ : B →ₗ[A] (B ⧸ P) ⊗[A] ((A ⧸ I) ⧸ Q) :=
    (TensorProduct.comm A ((A ⧸ I) ⧸ Q) (B ⧸ P)).toLinearMap.comp
      ((TensorProduct.mk A ((A ⧸ I) ⧸ Q) (B ⧸ P)
        (Submodule.Quotient.mk (p := Q) (Ideal.Quotient.mk I (1 : A)))).comp P.mkQ)
  have hP : P ≤ LinearMap.ker φ := by
    intro x hx
    show φ x = 0
    have hmk : P.mkQ x = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    simp [φ, hmk]
  have hI : (I • (⊤ : Submodule A B)) ≤ LinearMap.ker φ := by
    rw [Submodule.smul_le]
    intro a ha x hx
    show φ (a • x) = 0
    show TensorProduct.comm A ((A ⧸ I) ⧸ Q) (B ⧸ P)
      ((Submodule.Quotient.mk (p := Q) (Ideal.Quotient.mk I (1 : A))) ⊗ₜ[A]
        Submodule.Quotient.mk (p := P) (a • x)) = 0
    rw [Submodule.Quotient.mk_smul, TensorProduct.comm_tmul]
    have haQ : a • Submodule.Quotient.mk (p := Q) (Ideal.Quotient.mk I 1) = 0 := by
      rw [← Submodule.Quotient.mk_smul]
      simp [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    calc
      _ = Submodule.Quotient.mk (p := P) x ⊗ₜ[A]
          (a • Submodule.Quotient.mk (p := Q) (Ideal.Quotient.mk I (1 : A))) :=
        TensorProduct.smul_tmul a _ _
      _ = 0 := by rw [haQ, TensorProduct.tmul_zero]
  have hK : Submodule.restrictScalars A (Ideal.map (algebraMap A B) I) ≤ LinearMap.ker φ := by
    rwa [← Ideal.smul_top_eq_map (R := A) (S := B) I]
  have hφ : φ b = 0 := sup_le hK hP hb
  simpa [φ] using hφ

private lemma mem_sup_of_tensor_quotient_eq_zero
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I L : Ideal A) (J : Ideal B)
    (hL : Ideal.map (algebraMap A B) L ≤ J) (b : B)
    (hb : (Submodule.Quotient.mk b : B ⧸ (Submodule.restrictScalars A J)) ⊗ₜ[A]
      (Submodule.Quotient.mk (p := Submodule.restrictScalars A
        (Ideal.map (Ideal.Quotient.mk I) L)) (Ideal.Quotient.mk I (1 : A)) :
        (A ⧸ I) ⧸ (Submodule.restrictScalars A (Ideal.map (Ideal.Quotient.mk I) L))) = 0) :
    b ∈ J ⊔ Ideal.map (algebraMap A B) I := by
  let eQ : ((A ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) L) ≃ₐ[A] A ⧸ (I ⊔ L) :=
    DoubleQuot.quotQuotEquivQuotSupₐ A I L
  let eT : ((B ⧸ J) ⊗[A] ((A ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) L)) ≃ₗ[A]
      (B ⧸ J) ⊗[A] (A ⧸ (I ⊔ L)) :=
    TensorProduct.congr (LinearEquiv.refl A (B ⧸ J)) eQ.toLinearEquiv
  have heQ : eQ (Submodule.Quotient.mk (p := Ideal.map (Ideal.Quotient.mk I) L)
      (Ideal.Quotient.mk I (1 : A))) =
      Ideal.Quotient.mk (I ⊔ L) (1 : A) := by
    show (DoubleQuot.quotQuotEquivQuotSup I L) ((DoubleQuot.quotQuotMk I L) 1) = _
    exact DoubleQuot.quotQuotEquivQuotSup_quotQuotMk I L 1
  have htransport : eT ((Submodule.Quotient.mk b : B ⧸ J) ⊗ₜ[A]
      (Submodule.Quotient.mk (p := Ideal.map (Ideal.Quotient.mk I) L)
        (Ideal.Quotient.mk I (1 : A)) :
        (A ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) L)) =
        (Submodule.Quotient.mk b : B ⧸ J) ⊗ₜ[A]
          (Ideal.Quotient.mk (I ⊔ L) (1 : A)) := by
    show (TensorProduct.congr (LinearEquiv.refl A (B ⧸ J)) eQ.toLinearEquiv)
      ((Submodule.Quotient.mk b : B ⧸ J) ⊗ₜ[A]
        Submodule.Quotient.mk (p := Ideal.map (Ideal.Quotient.mk I) L)
          (Ideal.Quotient.mk I (1 : A))) = _
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    exact congrArg (fun z : A ⧸ (I ⊔ L) =>
      (Submodule.Quotient.mk b : B ⧸ J) ⊗ₜ[A] z) heQ
  have htensor : (Submodule.Quotient.mk b : B ⧸ J) ⊗ₜ[A]
        (Ideal.Quotient.mk (I ⊔ L) (1 : A)) = 0 :=
    htransport.symm.trans ((congrArg eT hb).trans (map_zero eT))
  have hquot0 := congrArg
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (B ⧸ J) (I ⊔ L)).symm htensor
  have hquot : (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
      (B ⧸ J) (I ⊔ L)).symm ((Submodule.Quotient.mk b : B ⧸ J) ⊗ₜ[A]
        Ideal.Quotient.mk (I ⊔ L) (1 : A)) = 0 := by simpa using hquot0
  have hquot' : Ideal.Quotient.mk
      (Ideal.map (algebraMap A (B ⧸ J)) (I ⊔ L)) (Ideal.Quotient.mk J b) = 0 := by
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul] at hquot
    simpa using hquot
  have hbmap : (Ideal.Quotient.mk J b) ∈ Ideal.map (algebraMap A (B ⧸ J)) (I ⊔ L) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hquot'
  have hAlg : (algebraMap A (B ⧸ J) : A →+* B ⧸ J) =
      (Ideal.Quotient.mk J).comp (algebraMap A B) := by
    ext a; simp
  have hmapcomp : Ideal.map (algebraMap A (B ⧸ J)) (I ⊔ L) =
      Ideal.map (Ideal.Quotient.mk J) (Ideal.map (algebraMap A B) (I ⊔ L)) := by
    rw [hAlg, Ideal.map_map]
  have hbcomap : b ∈ (Ideal.map (Ideal.Quotient.mk J)
      (Ideal.map (algebraMap A B) (I ⊔ L))).comap (Ideal.Quotient.mk J) := by
    show (Ideal.Quotient.mk J) b ∈ Ideal.map (Ideal.Quotient.mk J)
      (Ideal.map (algebraMap A B) (I ⊔ L))
    rwa [← hmapcomp]
  rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hbcomap
  have hle : Ideal.map (algebraMap A B) (I ⊔ L) ⊔ J ≤
      J ⊔ Ideal.map (algebraMap A B) I := by
    rw [Ideal.map_sup]
    exact sup_le (sup_le le_sup_right (hL.trans le_sup_left)) le_sup_left
  exact hle hbcomap

/-- The closure of the extension of `I` to `B` is the kernel of the canonical map
`B → B ⊗̂[A] (A ⧸ I)`. -/
@[stacks 0AMZ]
public theorem closure_map_eq_ker_completedTensorProduct
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B]
    [IsLinearTopology A A] [IsLinearTopology B B]
    (h : Continuous (algebraMap A B)) (I : Ideal A) :
    (Ideal.closure (I.map (algebraMap A B)) : Set B) =
      {b : B | (↑(b ⊗ₜ[A] (1 : A ⧸ I)) :
        TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := A ⧸ I)) = 0} := by
  let K : Ideal B := I.map (algebraMap A B)
  have hBasisB : (𝓝 (0 : B)).HasBasis
      (fun J : Ideal B => IsOpen (J : Set B)) (fun J => (J : Set B)) :=
    IsLinearTopology.hasBasis_open_ideal
  ext b
  have hcl : b ∈ closure (K : Set B) ↔
      ∀ J : Ideal B, IsOpen (J : Set B) → b ∈ (K : Set B) + (J : Set B) := by
    rw [← hBasisB.iInter_add_right_eq_closure]
    simp only [Set.mem_iInter]
  constructor
  · intro hb
    have hbOpen := hcl.mp hb
    apply (TopologicalRing.completedTensorProductEquivQuotientTensorLimit
      (R := A) (M := B) (N := A ⧸ I)).injective
    apply Subtype.ext
    funext i
    rw [TopologicalRing.completedTensorProductEquivQuotientTensorLimit_apply]
    rw [TopologicalRing.completedTensorProductTensorQuotientMap_coe_tmul]
    have hPnhds : (i.1.1 : Set B) ∈ 𝓝 (0 : B) :=
      i.1.2.mem_nhds (zero_mem i.1.1)
    obtain ⟨J, hJopen, hJP⟩ :=
      hBasisB.mem_iff.mp hPnhds
    have hbP : b ∈ (K : Set B) + (i.1.1 : Set B) := by
      rcases Set.mem_add.mp (hbOpen J hJopen) with ⟨x, hx, y, hy, rfl⟩
      exact Set.mem_add.mpr ⟨x, hx, y, hJP hy, rfl⟩
    have hbP' : b ∈ Submodule.restrictScalars A (Ideal.map (algebraMap A B) I) ⊔ i.1.1 := by
      rcases Set.mem_add.mp hbP with ⟨x, hx, y, hy, hxy⟩
      have hx' : x ∈ Submodule.restrictScalars A (Ideal.map (algebraMap A B) I) := by
        simpa [K] using hx
      exact Submodule.mem_sup.mpr ⟨x, hx', y, hy, hxy⟩
    calc
      _ = 0 := completedTensorProduct_component_eq_zero_of_mem I i.1.1 i.2.1 b hbP'
      _ = ((TopologicalRing.completedTensorProductEquivQuotientTensorLimit
          (R := A) (M := B) (N := A ⧸ I) 0 :
          TopologicalRing.QuotientTensorProductLimit (R := A) (M := B) (N := A ⧸ I)) :
          ∀ j : TopologicalRing.TensorProductSubmoduleIndex (R := A) (M := B) (N := A ⧸ I),
            TopologicalRing.QuotientTensorProduct j) i := by simp
  · intro hbzero
    refine hcl.mpr fun J hJopen => ?_
    obtain ⟨L, hLopen, hL⟩ :=
      TopologicalRing.exists_isOpen_ideal_map_le
        (algebraMap A B) h J hJopen
    let Q : Ideal (A ⧸ I) := Ideal.map (Ideal.Quotient.mk I) L
    have hQimage : (Q : Set (A ⧸ I)) = Ideal.Quotient.mk I '' (L : Set A) := by
      ext y
      show y ∈ Ideal.map (Ideal.Quotient.mk I) L ↔ y ∈ Ideal.Quotient.mk I '' (L : Set A)
      rw [Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective]
      rfl
    have hQopen : IsOpen (Q : Set (A ⧸ I)) := by
      rw [hQimage]
      exact (Submodule.isOpenMap_mkQ (I : Submodule A A)) (L : Set A) hLopen
    let Pidx : Submodule A B := Submodule.restrictScalars A J
    let Qidx : Submodule A (A ⧸ I) := Submodule.restrictScalars A Q
    let idx : TopologicalRing.TensorProductSubmoduleIndex (R := A) (M := B) (N := A ⧸ I) :=
      (⟨Pidx, hJopen⟩, ⟨Qidx, hQopen⟩)
    have hcoord : TopologicalRing.completedTensorProductTensorQuotientMap idx
        (↑(b ⊗ₜ[A] (1 : A ⧸ I)) :
          TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := A ⧸ I)) = 0 := by
      rw [hbzero]
      simp
    rw [TopologicalRing.completedTensorProductTensorQuotientMap_coe_tmul] at hcoord
    have hbJ := mem_sup_of_tensor_quotient_eq_zero I L J hL b (by
      simpa [idx, Pidx, Qidx, Q] using hcoord)
    rcases Submodule.mem_sup.mp hbJ with ⟨x, hx, y, hy, hxy⟩
    exact Set.mem_add.mpr ⟨y, by simpa [K] using hy, x, hx, by simpa [add_comm] using hxy⟩

end

end TopologicalRing

end
