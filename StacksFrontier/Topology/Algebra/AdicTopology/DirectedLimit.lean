module

public import Mathlib.Data.Finset.Order
public import Mathlib.Order.Filter.Pi
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.Constructions
public import StacksFrontier.RingTheory.Nilpotent.Ideal
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# The inverse limit of a directed system of commutative rings

Let `I` be a preorder, let `R i` be a commutative ring for every `i : I`, and let
`t h : R j →+* R i` be a transition homomorphism for every `h : i ≤ j`.  The inverse limit of this
system is the ring of families `a i : R i` satisfying `t h (a j) = a i` for every `h : i ≤ j`,
topologized as a subspace of the product of the discrete topologies.

When `I` is nonempty and directed the kernels of the projections to the `R i` form a fundamental
system of neighbourhoods of `0` consisting of open ideals, so the limit is a linearly topologized
ring; it is complete and separated.  When the kernel of every transition map is locally nilpotent
the kernels of the projections are weak ideals of definition, and hence the limit is weakly
admissible.

This is where the mathematics of `TopologicalRing.SequentialLimit` lives: that inverse limit is
by definition this one at `I = ℕ`, the transition map between two indices being the composite of
the maps of the sequence between them.  The arguments here replace "take the largest of finitely
many indices" by directedness and "step up one index at a time" by a single comparison.
-/

@[expose] public section

namespace TopologicalRing

open Filter

universe u v

variable {I : Type v} [Preorder I] {R : I → Type u} [∀ i, CommRing (R i)]

/-- The families compatible with the transition maps of a directed system of rings form a subring
of the product of that system. -/
def DirectedLimit.subring (t : ∀ ⦃i j : I⦄, i ≤ j → R j →+* R i) : Subring ((i : I) → R i) where
  carrier := {a | ∀ ⦃i j : I⦄ (h : i ≤ j), t h (a j) = a i}
  mul_mem' := by intro a b ha hb i j h; simp [map_mul, ha h, hb h]
  one_mem' := by intro i j h; simp
  add_mem' := by intro a b ha hb i j h; simp [map_add, ha h, hb h]
  zero_mem' := by intro i j h; simp
  neg_mem' := by intro a ha i j h; simp [map_neg, ha h]

/-- The inverse limit of a system of commutative rings indexed by a preorder `I`, with transition
maps `t h : R j →+* R i` for `h : i ≤ j`: the families `a i : R i` compatible with the transition
maps, in the sense that `t h (a j) = a i` for every `h : i ≤ j`. -/
def DirectedLimit (t : ∀ ⦃i j : I⦄, i ≤ j → R j →+* R i) : Type (max u v) :=
  { a : (i : I) → R i // ∀ ⦃i j : I⦄ (h : i ≤ j), t h (a j) = a i }

namespace DirectedLimit

variable (t : ∀ ⦃i j : I⦄, i ≤ j → R j →+* R i)

/-- The inverse limit is a commutative ring, with the operations of the product. -/
instance instCommRing : CommRing (DirectedLimit t) := inferInstanceAs (CommRing (subring t))

/-- The inverse limit is topologized as a subspace of the product of the rings of the system,
each of them discrete. -/
instance instTopologicalSpace : TopologicalSpace (DirectedLimit t) :=
  TopologicalSpace.induced Subtype.val (@Pi.topologicalSpace I R fun _ ↦ ⊥)

/-- Addition and multiplication are continuous for the limit topology. -/
instance instIsTopologicalRing : IsTopologicalRing (DirectedLimit t) := by
  let _ : ∀ i, TopologicalSpace (R i) := fun _ ↦ ⊥
  have : ∀ i, DiscreteTopology (R i) := fun _ ↦ ⟨rfl⟩
  exact Subring.instIsTopologicalRing (subring t)

/-- Evaluation at an index, as a ring homomorphism from the inverse limit to the ring sitting at
that index. -/
def proj (i : I) : DirectedLimit t →+* R i where
  toFun a := Subtype.val a i
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The transition map attached to `h : i ≤ j` takes the component at `j` of a family to its
component at `i`. -/
theorem t_proj {i j : I} (h : i ≤ j) (a : DirectedLimit t) : t h (proj t j a) = proj t i a :=
  Subtype.property a h

/-- The kernels of the projections decrease as the index grows: `i ≤ j` gives
`RingHom.ker (proj t j) ≤ RingHom.ker (proj t i)`, which is exactly the statement that
`fun i ↦ RingHom.ker (proj t i)` is `Antitone`. -/
theorem ker_antitone : Antitone (fun i ↦ RingHom.ker (proj t i)) := by
  intro i j h a ha
  exact RingHom.mem_ker.mpr (by rw [← t_proj t h a, RingHom.mem_ker.mp ha, map_zero])

/-- The kernels of the projections form a fundamental system of neighbourhoods of `0`: a
neighbourhood of `0` constrains only finitely many components, directedness provides an index
above all of them, and compatibility propagates the vanishing of the component at that index to
all of the constrained ones. -/
theorem hasBasis_nhds_zero [Nonempty I] [IsDirected I (· ≤ ·)] :
    (nhds (0 : DirectedLimit t)).HasBasis (fun _ : I ↦ True)
      (fun i ↦ (RingHom.ker (proj t i) : Set (DirectedLimit t))) := by
  let _ : ∀ i, TopologicalSpace (R i) := fun _ ↦ ⊥
  have : ∀ i, DiscreteTopology (R i) := fun _ ↦ ⟨rfl⟩
  have hb : ∀ i : I, (nhds (0 : R i)).HasBasis (fun _ : Unit ↦ True)
      fun _ ↦ ({0} : Set (R i)) := by
    intro i
    rw [nhds_discrete]
    exact hasBasis_pure 0
  have hnhds : nhds (0 : DirectedLimit t) =
      Filter.comap (fun a : DirectedLimit t ↦ Subtype.val a) (nhds (0 : (i : I) → R i)) :=
    nhds_induced _ _
  rw [hnhds, nhds_pi]
  refine ((Filter.hasBasis_pi hb).comap _).to_hasBasis ?_ ?_
  · intro If hIf
    obtain ⟨j, hj⟩ := Finset.exists_le hIf.1.toFinset
    refine ⟨j, trivial, fun a ha i hi ↦ ?_⟩
    exact Set.mem_singleton_iff.mpr
      (RingHom.mem_ker.mp (ker_antitone t (hj i (hIf.1.mem_toFinset.mpr hi)) ha))
  · intro i _
    refine ⟨⟨{i}, fun _ ↦ ()⟩, ⟨Set.finite_singleton i, fun _ _ ↦ trivial⟩, fun a ha ↦ ?_⟩
    exact RingHom.mem_ker.mpr (Set.mem_singleton_iff.mp (ha i (Set.mem_singleton i)))

/-- The kernel of each projection is an open ideal. -/
theorem isOpen_ker [Nonempty I] [IsDirected I (· ≤ ·)] (i : I) :
    IsOpen ((RingHom.ker (proj t i) : Ideal (DirectedLimit t)) : Set (DirectedLimit t)) :=
  (RingHom.ker (proj t i)).toAddSubgroup.isOpen_of_mem_nhds (g := 0)
    ((hasBasis_nhds_zero t).mem_iff.mpr ⟨i, trivial, subset_rfl⟩)

/-- The limit topology is linear: it has a basis of neighbourhoods of `0` made of ideals. -/
instance instIsLinearTopology [Nonempty I] [IsDirected I (· ≤ ·)] :
    IsLinearTopology (DirectedLimit t) (DirectedLimit t) :=
  IsLinearTopology.mk_of_hasBasis _ (hasBasis_nhds_zero t)

/-- A compatible family of elements of the rings of the system is realized by exactly one element
of the inverse limit. -/
theorem existsUnique_proj_eq (x : (i : I) → R i) (hx : ∀ ⦃i j : I⦄ (h : i ≤ j), t h (x j) = x i) :
    ∃! a : DirectedLimit t, ∀ i, proj t i a = x i :=
  ⟨⟨x, hx⟩, fun _ ↦ rfl, fun _ hb ↦ Subtype.ext (funext hb)⟩

/-- If the kernel of each transition map is locally nilpotent, then every element of the kernel of
a projection is topologically nilpotent: to kill the component at an index `j`, compare `j` and the
index where the element already vanishes inside a common upper bound `k`, where local nilpotency of
the kernel of the transition map provides a power of the element vanishing at `k`, hence at `j`. -/
theorem isTopologicallyNilpotent_of_mem_ker [Nonempty I] [IsDirected I (· ≤ ·)]
    (hnil : ∀ ⦃i j : I⦄ (h : i ≤ j), (RingHom.ker (t h)).LocallyNilpotent) {i : I}
    {a : DirectedLimit t} (ha : a ∈ RingHom.ker (proj t i)) : IsTopologicallyNilpotent a := by
  rw [IsTopologicallyNilpotent, Filter.tendsto_def]
  intro U hU
  obtain ⟨j, -, hsub⟩ := (hasBasis_nhds_zero t).mem_iff.mp hU
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  obtain ⟨q, hq⟩ := hnil hik (proj t k a)
    (RingHom.mem_ker.mpr ((t_proj t hik a).trans (RingHom.mem_ker.mp ha)))
  have hqk : a ^ q ∈ RingHom.ker (proj t k) := RingHom.mem_ker.mpr ((map_pow _ a q).trans hq)
  filter_upwards [Filter.eventually_ge_atTop q] with n hn
  refine hsub ?_
  show a ^ n ∈ (RingHom.ker (proj t j) : Set (DirectedLimit t))
  rw [← Nat.sub_add_cancel hn, pow_add]
  exact (RingHom.ker (proj t j)).mul_mem_left _ (ker_antitone t hjk hqk)

/-- The inverse limit is complete and separated for the limit topology: an element with all
components zero is zero, and a Cauchy filter is eventually constant in each component, so its
componentwise values form a compatible family whose realization in the limit is its limit. -/
theorem completeSpace_and_t2Space [Nonempty I] [IsDirected I (· ≤ ·)] :
    @CompleteSpace (DirectedLimit t)
        (IsTopologicalAddGroup.rightUniformSpace (DirectedLimit t)) ∧
      T2Space (DirectedLimit t) := by
  classical
  let _ : UniformSpace (DirectedLimit t) :=
    IsTopologicalAddGroup.rightUniformSpace (DirectedLimit t)
  let _ : IsUniformAddGroup (DirectedLimit t) := isUniformAddGroup_of_addCommGroup
  have hker (i : I) : (RingHom.ker (proj t i) : Set (DirectedLimit t)) ∈ nhds 0 :=
    (isOpen_ker t i).mem_nhds (zero_mem _)
  refine ⟨⟨fun {f} hf ↦ ?_⟩, ?_⟩
  · have : f.NeBot := hf.1
    have hconst : ∀ i : I, ∃ v : R i, ∀ᶠ a in f, proj t i a = v := by
      intro i
      have hmem : {z : DirectedLimit t × DirectedLimit t |
          proj t i z.1 = proj t i z.2} ∈ f ×ˢ f := by
        refine hf.2 ?_
        rw [uniformity_eq_comap_nhds_zero]
        refine Filter.mem_comap.mpr ⟨RingHom.ker (proj t i), hker i, fun z hz ↦ ?_⟩
        exact (sub_eq_zero.mp (by rwa [← map_sub])).symm
      obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hmem
      obtain ⟨a₀, ha₀⟩ := hf.1.nonempty_of_mem hU
      exact ⟨proj t i a₀,
        Filter.mem_of_superset hV fun b hb ↦ (hUV (Set.mk_mem_prod ha₀ hb)).symm⟩
    choose v hv using hconst
    have hcompat : ∀ ⦃i j : I⦄ (h : i ≤ j), t h (v j) = v i := by
      intro i j h
      obtain ⟨a, hai, haj⟩ := ((hv i).and (hv j)).exists
      rw [← hai, ← haj, t_proj]
    obtain ⟨z, hz, -⟩ := existsUnique_proj_eq t v hcompat
    refine ⟨z, ?_⟩
    have hsub : Tendsto (fun a : DirectedLimit t ↦ a - z) f (nhds 0) := by
      refine (hasBasis_nhds_zero t).tendsto_right_iff.mpr fun i _ ↦ ?_
      filter_upwards [hv i] with a ha
      exact RingHom.mem_ker.mpr (by rw [map_sub, ha, hz i, sub_self])
    exact Filter.tendsto_id'.mp (tendsto_sub_nhds_zero_iff.mp hsub)
  · refine IsTopologicalAddGroup.t2Space_of_zero_sep fun a ha ↦ ?_
    obtain ⟨i, hi⟩ : ∃ i, proj t i a ≠ 0 := by
      by_contra! h
      exact ha (Subtype.ext (funext h))
    exact ⟨RingHom.ker (proj t i), hker i, fun hz ↦ hi (RingHom.mem_ker.mp hz)⟩

/-- If the kernel of each transition map is locally nilpotent, the kernel of each projection is a
weak ideal of definition. -/
theorem isWeakIdealOfDefinition_ker [Nonempty I] [IsDirected I (· ≤ ·)]
    (hnil : ∀ ⦃i j : I⦄ (h : i ≤ j), (RingHom.ker (t h)).LocallyNilpotent) (i : I) :
    TopologicalRing.IsWeakIdealOfDefinition (RingHom.ker (proj t i)) :=
  ⟨isOpen_ker t i, fun _ ha ↦ isTopologicallyNilpotent_of_mem_ker t hnil ha⟩

/-- The inverse limit of a directed system of rings whose transition maps have locally nilpotent
kernels is weakly admissible. -/
theorem isWeaklyAdmissible [Nonempty I] [IsDirected I (· ≤ ·)]
    (hnil : ∀ ⦃i j : I⦄ (h : i ≤ j), (RingHom.ker (t h)).LocallyNilpotent) :
    TopologicalRing.IsWeaklyAdmissible (DirectedLimit t) :=
  ⟨⟨RingHom.ker (proj t (Classical.arbitrary I)),
      isWeakIdealOfDefinition_ker t hnil (Classical.arbitrary I)⟩,
    (completeSpace_and_t2Space t).1, (completeSpace_and_t2Space t).2⟩

end DirectedLimit

end TopologicalRing

end
