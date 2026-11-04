module

public import Mathlib.Order.Filter.Pi
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.Constructions
public import StacksFrontier.RingTheory.Nilpotent.Ideal
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# The inverse limit of a sequence of commutative rings

Let `⋯ → R 2 → R 1 → R 0` be a sequence of commutative rings with transition homomorphisms
`t n : R (n + 1) →+* R n`.  Its inverse limit is the ring of families `a n : R n` satisfying
`t n (a (n + 1)) = a n`, topologized as a subspace of the product of the discrete topologies.

The kernels of the projections to the `R n` form a fundamental system of neighbourhoods of `0`
consisting of open ideals, so the limit is a linearly topologized ring; it is complete and
separated, and the projections are surjective as soon as all the transition maps are.  When each
transition map has locally nilpotent kernel the kernels of the projections are weak ideals of
definition, and hence the limit is weakly admissible.
-/

@[expose] public section

namespace TopologicalRing

open Filter

universe u

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (t : ∀ n, R (n + 1) →+* R n)

/-- The families compatible with the transition maps of a sequence of rings form a subring of
the product of that sequence. -/
def SequentialLimit.subring : Subring ((n : ℕ) → R n) where
  carrier := {a | ∀ n, t n (a (n + 1)) = a n}
  mul_mem' ha hb n := by simp [ha n, hb n]
  one_mem' _ := by simp
  add_mem' ha hb n := by simp [ha n, hb n]
  zero_mem' _ := by simp
  neg_mem' ha n := by simp [ha n]

/-- The inverse limit of a sequence of commutative rings `⋯ → R 1 → R 0`: the families
`a n : R n` compatible with the transition maps, in the sense that `t n (a (n + 1)) = a n`. -/
def SequentialLimit : Type u :=
  { a : (n : ℕ) → R n // ∀ n, t n (a (n + 1)) = a n }

namespace SequentialLimit

/-- The inverse limit is a commutative ring, with the operations of the product. -/
instance instCommRing : CommRing (SequentialLimit t) := inferInstanceAs (CommRing (subring t))

/-- The inverse limit is topologized as a subspace of the product of the rings of the
sequence, each of them discrete. -/
instance instTopologicalSpace : TopologicalSpace (SequentialLimit t) :=
  TopologicalSpace.induced Subtype.val (@Pi.topologicalSpace ℕ R fun _ ↦ ⊥)

/-- Addition and multiplication are continuous for the limit topology. -/
instance instIsTopologicalRing : IsTopologicalRing (SequentialLimit t) := by
  let _ : ∀ n, TopologicalSpace (R n) := fun _ ↦ ⊥
  have : ∀ n, DiscreteTopology (R n) := fun _ ↦ ⟨rfl⟩
  exact Subring.instIsTopologicalRing (subring t)

/-- Evaluation at an index, as a ring homomorphism from the inverse limit to the ring sitting
at that index. -/
def proj (n : ℕ) : SequentialLimit t →+* R n where
  toFun a := Subtype.val a n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The transition map takes the component at `n + 1` of a family to its component at `n`. -/
theorem t_proj (n : ℕ) (a : SequentialLimit t) : t n (proj t (n + 1) a) = proj t n a :=
  Subtype.property a n

/-- The projection at `n` is the projection at `n + 1` followed by the transition map. -/
theorem proj_comp (n : ℕ) : (t n).comp (proj t (n + 1)) = proj t n :=
  RingHom.ext fun a ↦ t_proj t n a

/-- The kernels of the projections form a decreasing sequence of ideals. -/
theorem ker_antitone : Antitone (fun n ↦ RingHom.ker (proj t n)) :=
  antitone_nat_of_succ_le fun n a ha ↦ RingHom.mem_ker.mpr <| by
    rw [← t_proj t n a, RingHom.mem_ker.mp ha, map_zero]

/-- The kernels of the projections form a fundamental system of neighbourhoods of `0`: a
neighbourhood of `0` constrains only finitely many components, and compatibility propagates the
vanishing of the component at the largest constrained index to all smaller indices. -/
theorem hasBasis_nhds_zero :
    (nhds (0 : SequentialLimit t)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (RingHom.ker (proj t n) : Set (SequentialLimit t))) := by
  let _ : ∀ n, TopologicalSpace (R n) := fun _ ↦ ⊥
  have : ∀ n, DiscreteTopology (R n) := fun _ ↦ ⟨rfl⟩
  have hb : ∀ i : ℕ, (nhds (0 : R i)).HasBasis (fun _ : Unit ↦ True)
      fun _ ↦ ({0} : Set (R i)) := by
    intro i
    rw [nhds_discrete]
    exact hasBasis_pure 0
  have hnhds : nhds (0 : SequentialLimit t) =
      Filter.comap (fun a : SequentialLimit t ↦ Subtype.val a) (nhds (0 : (n : ℕ) → R n)) :=
    nhds_induced _ _
  rw [hnhds, nhds_pi]
  refine ((Filter.hasBasis_pi hb).comap _).to_hasBasis ?_ ?_
  · intro If hIf
    obtain ⟨N, hN⟩ := hIf.1.bddAbove
    refine ⟨N, trivial, fun a ha i hi ↦ ?_⟩
    exact Set.mem_singleton_iff.mpr (RingHom.mem_ker.mp (ker_antitone t (hN hi) ha))
  · intro n _
    refine ⟨⟨{n}, fun _ ↦ ()⟩, ⟨Set.finite_singleton n, fun i _ ↦ trivial⟩, fun a ha ↦ ?_⟩
    exact RingHom.mem_ker.mpr (Set.mem_singleton_iff.mp (ha n (Set.mem_singleton n)))

/-- The kernel of each projection is an open ideal. -/
theorem isOpen_ker (n : ℕ) :
    IsOpen ((RingHom.ker (proj t n) : Ideal (SequentialLimit t)) : Set (SequentialLimit t)) :=
  (RingHom.ker (proj t n)).toAddSubgroup.isOpen_of_mem_nhds (g := 0)
    ((hasBasis_nhds_zero t).mem_iff.mpr ⟨n, trivial, subset_rfl⟩)

/-- The limit topology is linear: it has a basis of neighbourhoods of `0` made of ideals. -/
instance instIsLinearTopology : IsLinearTopology (SequentialLimit t) (SequentialLimit t) :=
  IsLinearTopology.mk_of_hasBasis _ (hasBasis_nhds_zero t)

/-- A compatible family of elements of the rings of the sequence is realized by exactly one
element of the inverse limit. -/
theorem existsUnique_proj_eq (x : (n : ℕ) → R n) (hx : ∀ n, t n (x (n + 1)) = x n) :
    ∃! a : SequentialLimit t, ∀ n, proj t n a = x n :=
  ⟨⟨x, hx⟩, fun _ ↦ rfl, fun _ hb ↦ Subtype.ext (funext hb)⟩

/-- Every element of a ring of the sequence is the component of a compatible family, provided
all the transition maps are surjective: the family is extended upwards by choosing preimages and
downwards by applying the transition maps. -/
private theorem exists_proj_eq_of_surjective {S : ℕ → Type u} [inst : ∀ k, CommRing (S k)]
    (s : ∀ k, S (k + 1) →+* S k) (hs : ∀ k, Function.Surjective (s k)) (n : ℕ) (x : S n) :
    ∃ a : SequentialLimit s, proj s n a = x := by
  induction n generalizing S with
  | zero =>
    choose u hu using fun (k : ℕ) (z : S k) ↦ hs k z
    exact ⟨⟨fun k ↦ Nat.rec (motive := fun k ↦ S k) x (fun k z ↦ u k z) k, fun k ↦ hu k _⟩, rfl⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih (S := fun k ↦ S (k + 1)) (fun k ↦ s (k + 1)) (fun k ↦ hs (k + 1)) x
    refine ⟨⟨fun m ↦ Nat.rec (motive := fun m ↦ S m) (s 0 (Subtype.val a 0))
      (fun m _ ↦ Subtype.val a m) m, ?_⟩, ha⟩
    intro m
    cases m with
    | zero => rfl
    | succ m => exact Subtype.property a m

/-- If all the transition maps are surjective then so are the projections from the inverse
limit. -/
theorem proj_surjective (ht : ∀ n, Function.Surjective (t n)) (n : ℕ) :
    Function.Surjective (proj t n) :=
  fun x ↦ exists_proj_eq_of_surjective t ht n x

/-- When all the transition maps are surjective, the quotient of the inverse limit by the kernel
of the projection at `n` is the ring at `n`. -/
noncomputable def quotientEquiv (ht : ∀ n, Function.Surjective (t n)) (n : ℕ) :
    (SequentialLimit t ⧸ RingHom.ker (proj t n)) ≃+* R n :=
  RingHom.quotientKerEquivOfSurjective (proj_surjective t ht n)

/-- If the kernel of each transition map is locally nilpotent, then every element of the kernel
of a projection is topologically nilpotent: a power of it dies in the next ring of the sequence,
a power of that one in the one after, and so on. -/
theorem isTopologicallyNilpotent_of_mem_ker
    (hnil : ∀ n, (RingHom.ker (t n)).LocallyNilpotent) {n : ℕ} {a : SequentialLimit t}
    (ha : a ∈ RingHom.ker (proj t n)) : IsTopologicallyNilpotent a := by
  have hstep : ∀ m p : ℕ, a ^ p ∈ RingHom.ker (proj t m) →
      ∃ q, a ^ q ∈ RingHom.ker (proj t (m + 1)) := by
    intro m p hp
    obtain ⟨q, hq⟩ := hnil m (proj t (m + 1) (a ^ p))
      (RingHom.mem_ker.mpr ((t_proj t m _).trans (RingHom.mem_ker.mp hp)))
    refine ⟨p * q, RingHom.mem_ker.mpr ?_⟩
    rwa [pow_mul, map_pow]
  have hpow : ∀ m, ∃ p, a ^ p ∈ RingHom.ker (proj t m) := by
    intro m
    induction m with
    | zero => exact ⟨1, by simpa using ker_antitone t (Nat.zero_le n) ha⟩
    | succ m ih => exact hstep m _ ih.choose_spec
  rw [IsTopologicallyNilpotent, Filter.tendsto_def]
  intro U hU
  obtain ⟨m, -, hsub⟩ := (hasBasis_nhds_zero t).mem_iff.mp hU
  obtain ⟨p, hp⟩ := hpow m
  filter_upwards [Filter.eventually_ge_atTop p] with k hk
  refine hsub ?_
  show a ^ k ∈ (RingHom.ker (proj t m) : Set (SequentialLimit t))
  rw [← Nat.sub_add_cancel hk, pow_add]
  exact (RingHom.ker (proj t m)).mul_mem_left _ hp

/-- The inverse limit is complete and separated for the limit topology: an element with all
components zero is zero, and the components of a Cauchy sequence stabilize to a compatible
family, whose realization in the limit is the limit of the sequence. -/
theorem completeSpace_and_t2Space :
    @CompleteSpace (SequentialLimit t)
        (IsTopologicalAddGroup.rightUniformSpace (SequentialLimit t)) ∧
      T2Space (SequentialLimit t) := by
  classical
  let _ : UniformSpace (SequentialLimit t) :=
    IsTopologicalAddGroup.rightUniformSpace (SequentialLimit t)
  let _ : IsUniformAddGroup (SequentialLimit t) := isUniformAddGroup_of_addCommGroup
  have hker (n : ℕ) : (RingHom.ker (proj t n) : Set (SequentialLimit t)) ∈ nhds 0 :=
    (isOpen_ker t n).mem_nhds (zero_mem _)
  refine ⟨?_, ?_⟩
  · have _ : (nhds (0 : SequentialLimit t)).IsCountablyGenerated :=
      (hasBasis_nhds_zero t).isCountablyGenerated
    have _ : (uniformity (SequentialLimit t)).IsCountablyGenerated := by
      rw [uniformity_eq_comap_nhds_zero]
      exact Filter.comap.isCountablyGenerated _ _
    apply UniformSpace.complete_of_cauchySeq_tendsto
    intro u hu
    have heq (n : ℕ) : ∃ N, ∀ k ≥ N, ∀ l ≥ N, proj t n (u k) = proj t n (u l) := by
      refine (cauchySeq_iff.mp hu) {z : SequentialLimit t × SequentialLimit t |
        proj t n z.1 = proj t n z.2} ?_
      rw [uniformity_eq_comap_nhds_zero]
      refine Filter.mem_comap.mpr ⟨RingHom.ker (proj t n), hker n, fun z hz ↦ ?_⟩
      exact (sub_eq_zero.mp (by simpa using hz)).symm
    choose N hN using heq
    have hcompat (n : ℕ) :
        t n (proj t (n + 1) (u (N (n + 1)))) = proj t n (u (N n)) := by
      rw [hN (n + 1) (N (n + 1)) le_rfl (max (N n) (N (n + 1))) (le_max_right _ _), t_proj]
      exact hN n _ (le_max_left _ _) (N n) le_rfl
    obtain ⟨z, hz, -⟩ := existsUnique_proj_eq t (fun n ↦ proj t n (u (N n))) hcompat
    refine ⟨z, ?_⟩
    have hsub : Tendsto (fun k : ℕ ↦ u k - z) atTop (nhds (0 : SequentialLimit t)) := by
      refine (hasBasis_nhds_zero t).tendsto_right_iff.mpr fun n _ ↦ ?_
      filter_upwards [Filter.eventually_ge_atTop (N n)] with k hk
      exact RingHom.mem_ker.mpr (by rw [map_sub, hz n, hN n k hk (N n) le_rfl, sub_self])
    simpa using hsub.add (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ z) atTop (nhds z))
  · refine IsTopologicalAddGroup.t2Space_of_zero_sep fun a ha ↦ ?_
    obtain ⟨b, -, huniq⟩ := existsUnique_proj_eq t (fun _ ↦ 0) fun n ↦ map_zero _
    have hex : ∃ n, proj t n a ≠ 0 := by
      by_contra! h
      exact ha ((huniq a h).trans (huniq 0 fun _ ↦ map_zero _).symm)
    obtain ⟨n, hn⟩ := hex
    exact ⟨RingHom.ker (proj t n), hker n, fun hz ↦ hn (RingHom.mem_ker.mp hz)⟩

/-- If the kernel of each transition map is locally nilpotent, the kernel of each projection is
a weak ideal of definition. -/
theorem isWeakIdealOfDefinition_ker (hnil : ∀ n, (RingHom.ker (t n)).LocallyNilpotent) (n : ℕ) :
    TopologicalRing.IsWeakIdealOfDefinition (RingHom.ker (proj t n)) :=
  ⟨isOpen_ker t n, fun _ ha ↦ isTopologicallyNilpotent_of_mem_ker t hnil ha⟩

/-- The inverse limit of a sequence of rings whose transition maps have locally nilpotent
kernels is weakly admissible. -/
theorem isWeaklyAdmissible (hnil : ∀ n, (RingHom.ker (t n)).LocallyNilpotent) :
    TopologicalRing.IsWeaklyAdmissible (SequentialLimit t) :=
  ⟨⟨RingHom.ker (proj t 0), isWeakIdealOfDefinition_ker t hnil 0⟩,
    (completeSpace_and_t2Space t).1, (completeSpace_and_t2Space t).2⟩

end SequentialLimit

end TopologicalRing

end
