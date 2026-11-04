module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Order.Filter.CountablyGenerated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.RigSmoothLocality
public import StacksFrontier.RingTheory.Rig.RigSmoothStability
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeOnReductionsIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.TautIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdic

/-!
# Finite products of weakly admissible topological rings

Let `A i` be a finite family of linearly topologized commutative rings. The product `∀ i, A i`
carries the product topology, and every ideal of it is a product `Ideal.pi I` of ideals of the
factors — this is Mathlib's `Ideal.piOrderIso`, and it fails for an infinite index. The
conditions on a topological ring which Stacks 0AMV, 0AID and 0GXE use to classify affine formal
algebraic spaces are therefore all decided coordinatewise on a finite product, and this file
proves that each of them is inherited: weak admissibility, admissibility, weak adicness, and
adicness together with a finitely generated ideal of definition.

The reason for collecting them is the step of Stacks 0AKX which asks that a finite disjoint
union of affine formal algebraic spaces of a given type again have that type. The presenting
ring of a finite coproduct of affine formal algebraic spaces is the product of the presenting
rings of the summands, so each clause of that step is one of the lemmas below.

## Main results

* `TopologicalRing.isOpen_coe_idealPi`: a product of open ideals is open.
* `TopologicalRing.hasBasis_nhds_zero_pi`: fundamental systems of open ideals of the factors,
  indexed by a common decreasing sequence, multiply to one of the product.
* `TopologicalRing.completeSpace_pi'`: a product of complete topological abelian groups is
  complete for the canonical uniformity.
* `TopologicalRing.isIdealOfDefinition_pi` and
  `TopologicalRing.isWeakIdealOfDefinition_pi_of_topologicalSpace`: a product of (weak) ideals of
  definition is a (weak) ideal of definition.
* `TopologicalRing.isWeaklyAdmissible_pi'`, `TopologicalRing.isAdmissible_pi'`,
  `TopologicalRing.isWeaklyAdic_pi'`, `TopologicalRing.exists_fg_isIdealOfDefinition_pi`: the
  types of Stacks 0AMV, 0AID and 0GXE are inherited by a finite product.
* `TopologicalRing.weakIdealOfDefinitionIndexPiOrderIso`: the weak ideals of definition of a
  finite product are exactly the products of weak ideals of definition of the factors.
* `TopologicalRing.isCountablyGenerated_nhds_zero_pi`: a countable product of rings with a
  countable fundamental system of neighbourhoods of zero has one.

## Implementation notes

Adicness of a finite product is `Rig.isAdic_pi`, which is already in the library; it is used
here rather than reproved, as is `Rig.pi_pow`, the identification of a power of a product of
ideals with the product of the powers, which that proof contains. The recovery of an ideal of a
finite product from its images under the projections is Mathlib's
`Ideal.piOrderIso.symm_apply_apply`.

The product carries no `IsLinearTopology` instance — Mathlib has none for a product and the
library's `pi_isLinearTopology` is a theorem, not an instance. The two statements whose
*conclusion* needs that hypothesis, `TopologicalRing.isWeaklyAdmissible_pi'` and
`TopologicalRing.isWeaklyAdic_pi'`, therefore introduce it with a `letI` in their statement, as
the consumers of this file do.

Openness of a product of open ideals needs the index to be finite, as a product of open sets is
open only then; everything about ideals here inherits that hypothesis.

## References

* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0GXE](https://stacks.math.columbia.edu/tag/0GXE)
-/

@[expose] public section

open Filter

namespace TopologicalRing

universe u

section Ideals

variable {ι : Type*} {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]

/-- A product of open ideals of a finite family of rings carrying topologies is an open ideal
of the product: its underlying set is the product of the underlying sets. No compatibility of
the topologies with the ring structures is needed. -/
theorem isOpen_coe_idealPi {ι : Type*} [Finite ι] {A : ι → Type*} [∀ i, CommRing (A i)]
    [∀ i, TopologicalSpace (A i)] (I : ∀ i, Ideal (A i))
    (hI : ∀ i, IsOpen ((I i : Ideal (A i)) : Set (A i))) :
    IsOpen ((Ideal.pi I : Ideal (∀ i, A i)) : Set (∀ i, A i)) := by
  rw [coe_idealPi]
  exact isOpen_set_pi Set.finite_univ fun i _ ↦ hI i

/-- A product of open ideals of a finite family of topological rings is a neighbourhood of
zero in the product. -/
theorem idealPi_mem_nhds_zero [Finite ι] (I : ∀ i, Ideal (A i))
    (hI : ∀ i, IsOpen ((I i : Ideal (A i)) : Set (A i))) :
    ((Ideal.pi I : Ideal (∀ i, A i)) : Set (∀ i, A i)) ∈ nhds (0 : ∀ i, A i) :=
  (isOpen_coe_idealPi I hI).mem_nhds (Ideal.pi I).zero_mem

/-- If each factor has antitone ideals `s i n` such that every neighbourhood of zero contains
some `s i n`, then every neighbourhood of zero of the finite product contains some
`Ideal.pi fun i ↦ s i n`. -/
private theorem exists_idealPi_subset_of_mem_nhds [Finite ι] (s : ∀ i, ℕ → Ideal (A i))
    (hanti : ∀ i, Antitone (s i))
    (hs : ∀ i, ∀ V ∈ nhds (0 : A i), ∃ n, ((s i n : Ideal (A i)) : Set (A i)) ⊆ V)
    {U : Set (∀ i, A i)} (hU : U ∈ nhds (0 : ∀ i, A i)) :
    ∃ n, ((Ideal.pi fun i ↦ s i n : Ideal (∀ i, A i)) : Set (∀ i, A i)) ⊆ U := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [nhds_pi] at hU
  obtain ⟨T, -, V, hV, hsub⟩ := Filter.mem_pi.mp hU
  choose m hm using fun i ↦ hs i (V i) (hV i)
  refine ⟨Finset.univ.sup m, fun x hx ↦ hsub fun i _ ↦ ?_⟩
  exact hm i (hanti i (Finset.le_sup (Finset.mem_univ i)) ((Ideal.mem_pi _ x).mp hx i))

/-- **A fundamental system of open ideals of a finite product.** If for each factor the ideals
`s i n` are open, decrease in `n` and form a fundamental system of neighbourhoods of zero, then
their products over the factors form one for the product ring. -/
theorem hasBasis_nhds_zero_pi [Finite ι] (s : ∀ i, ℕ → Ideal (A i))
    (hopen : ∀ i n, IsOpen ((s i n : Ideal (A i)) : Set (A i)))
    (hanti : ∀ i, Antitone (s i))
    (hbasis : ∀ i, (nhds (0 : A i)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((s i n : Ideal (A i)) : Set (A i)))) :
    (nhds (0 : ∀ i, A i)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((Ideal.pi (fun i ↦ s i n) : Ideal (∀ i, A i)) : Set (∀ i, A i))) := by
  refine Filter.hasBasis_iff.mpr fun t ↦ ⟨fun ht ↦ ?_, ?_⟩
  · obtain ⟨n, hn⟩ := exists_idealPi_subset_of_mem_nhds s hanti
      (fun i V hV ↦ by simpa using (hbasis i).mem_iff.mp hV) ht
    exact ⟨n, trivial, hn⟩
  · rintro ⟨n, -, hn⟩
    exact Filter.mem_of_superset (idealPi_mem_nhds_zero _ fun i ↦ hopen i n) hn

/-- A product of ideals of definition of a finite family of topological rings is an ideal of
definition of the product: its powers are the products of the powers, and a neighbourhood of
zero in the product contains a product of neighbourhoods of zero. -/
theorem isIdealOfDefinition_pi [Finite ι] (I : ∀ i, Ideal (A i))
    (hI : ∀ i, IsIdealOfDefinition (I i)) :
    IsIdealOfDefinition (Ideal.pi I) := by
  refine ⟨isOpen_coe_idealPi I fun i ↦ (hI i).1, fun U hU ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_idealPi_subset_of_mem_nhds (fun i n ↦ I i ^ n)
    (fun i _ _ h ↦ Ideal.pow_le_pow_right h) (fun i V hV ↦ (hI i).2 V hV) hU
  exact ⟨n, by rwa [Rig.pi_pow']⟩

/-- A product of weak ideals of definition of a finite family of topological rings is a weak
ideal of definition of the product: it is open, and an element of a product of ideals is
topologically nilpotent exactly when each of its coordinates is. -/
theorem isWeakIdealOfDefinition_pi_of_topologicalSpace [Finite ι] (I : ∀ i, Ideal (A i))
    (hI : ∀ i, IsWeakIdealOfDefinition (I i)) :
    IsWeakIdealOfDefinition (Ideal.pi I) :=
  ⟨isOpen_coe_idealPi I fun i ↦ (hI i).1, fun x hx ↦
    isTopologicallyNilpotent_pi_iff.mpr fun i ↦ (hI i).2 _ ((Ideal.mem_pi _ x).mp hx i)⟩

/-- The image of a weak ideal of definition of a finite product under a projection is a weak
ideal of definition of the factor: a projection out of a product is an open map, and every
coordinate of a topologically nilpotent element of a product is topologically nilpotent. -/
theorem isWeakIdealOfDefinition_map_evalRingHom' [Finite ι] {J : Ideal (∀ i, A i)}
    (hJ : IsWeakIdealOfDefinition J) (i : ι) :
    IsWeakIdealOfDefinition (J.map (Pi.evalRingHom A i)) := by
  classical
  have hsurj : Function.Surjective (Pi.evalRingHom A i) := fun a ↦
    ⟨Pi.single i a, Pi.single_eq_same i a⟩
  refine ⟨?_, fun a ha ↦ ?_⟩
  · have hset : ((J.map (Pi.evalRingHom A i) : Ideal (A i)) : Set (A i)) =
        Function.eval i '' ((J : Ideal (∀ i, A i)) : Set (∀ i, A i)) := by
      ext a
      simp only [SetLike.mem_coe, Ideal.mem_map_iff_of_surjective _ hsurj, Set.mem_image]
      rfl
    rw [hset]
    exact isOpenMap_eval i _ hJ.1
  · obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp ha
    exact isTopologicallyNilpotent_pi_iff.mp (hJ.2 x hx) i

/-- **The weak ideals of definition of a finite product.** An ideal of a finite product of rings
is the product of its images under the projections, and it is a weak ideal of definition exactly
when each of those images is one; the identification is an order isomorphism. -/
def weakIdealOfDefinitionIndexPiOrderIso [Finite ι] :
    WeakIdealOfDefinitionIndex (∀ i, A i) ≃o ∀ i, WeakIdealOfDefinitionIndex (A i) where
  toFun J i := ⟨J.1.map (Pi.evalRingHom A i), isWeakIdealOfDefinition_map_evalRingHom' J.2 i⟩
  invFun I := ⟨Ideal.pi fun i ↦ (I i).1,
    isWeakIdealOfDefinition_pi_of_topologicalSpace _ fun i ↦ (I i).2⟩
  left_inv J := Subtype.ext (Ideal.piOrderIso.symm_apply_apply J.1)
  right_inv I := funext fun i ↦ Subtype.ext (Ideal.map_evalRingHom_pi i)
  map_rel_iff' {a b} := by
    refine ⟨fun h ↦ ?_, fun h i ↦ Ideal.map_mono h⟩
    have hle : (Ideal.pi fun i ↦ a.1.map (Pi.evalRingHom A i)) ≤
        Ideal.pi fun i ↦ b.1.map (Pi.evalRingHom A i) :=
      Ideal.pi_le_pi_iff.mpr fun i ↦ h i
    exact (Ideal.piOrderIso.symm_apply_apply a.1).ge.trans
      (hle.trans (Ideal.piOrderIso.symm_apply_apply b.1).le)

omit [∀ i, TopologicalSpace (A i)] in
/-- The identification of the quotient of a product of rings by a product of ideals with the
product of the quotients sends the class of an element to the family of the classes of its
coordinates. -/
@[simp]
theorem piQuotEquiv_mk (I : ∀ i, Ideal (A i)) (x : ∀ i, A i) (i : ι) :
    piQuotEquiv I (Ideal.Quotient.mk _ x) i = Ideal.Quotient.mk (I i) (x i) := by
  rw [piQuotEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

omit [∀ i, TopologicalSpace (A i)] in
/-- A product of finitely generated ideals over a finite index is finitely generated: the
images under the coordinate inclusions of generating sets of the factors generate it, because
an element of the product is the sum of its coordinates. -/
theorem fg_idealPi [Finite ι] (I : ∀ i, Ideal (A i)) (hI : ∀ i, (I i).FG) :
    (Ideal.pi I).FG := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose s hsfin hsspan using fun i ↦ Submodule.fg_def.mp (hI i)
  set T : Set (∀ i, A i) := ⋃ i, (fun a : A i ↦ Pi.single i a) '' s i with hTdef
  have hsingle : ∀ (i : ι) (a : A i), a ∈ Submodule.span (A i) (s i) →
      Pi.single i a ∈ Ideal.span T := by
    intro i a ha
    induction ha using Submodule.span_induction with
    | mem b hb =>
        refine Ideal.subset_span ?_
        rw [hTdef]
        exact Set.mem_iUnion.mpr ⟨i, b, hb, rfl⟩
    | zero => simp
    | add b c _ _ hb hc => rw [Pi.single_add]; exact Submodule.add_mem _ hb hc
    | smul c b _ hb => rw [smul_eq_mul, Pi.single_mul]; exact Ideal.mul_mem_left _ _ hb
  refine Submodule.fg_def.mpr ⟨T, Set.finite_iUnion fun i ↦ (hsfin i).image _,
    le_antisymm (Ideal.span_le.mpr ?_) fun x hx ↦ ?_⟩
  · rintro y hy
    rw [hTdef] at hy
    simp only [Set.mem_iUnion, Set.mem_image] at hy
    obtain ⟨i, a, ha, rfl⟩ := hy
    have hmem : a ∈ Submodule.span (A i) (s i) := Submodule.subset_span ha
    rw [hsspan i] at hmem
    exact Ideal.single_mem_pi hmem
  · rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ ↦ hsingle i (x i) ?_
    rw [hsspan i]
    exact (Ideal.mem_pi _ x).mp hx i

end Ideals

section Complete

variable {ι : Type*} {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalRing (A i)]

/-- A product of complete topological abelian groups is complete for the canonical uniformity
of its additive group: that uniformity is the product uniformity, for which completeness is
coordinatewise. -/
theorem completeSpace_pi'
    (h : ∀ i, @CompleteSpace (A i) (IsTopologicalAddGroup.rightUniformSpace (A i))) :
    @CompleteSpace (∀ i, A i) (IsTopologicalAddGroup.rightUniformSpace (∀ i, A i)) := by
  let : ∀ i, UniformSpace (A i) := fun i ↦ IsTopologicalAddGroup.rightUniformSpace (A i)
  let : ∀ i, IsUniformAddGroup (A i) := fun _ ↦ isUniformAddGroup_of_addCommGroup
  let : ∀ i, CompleteSpace (A i) := h
  let : UniformSpace (∀ i, A i) := Pi.uniformSpace A
  let : IsUniformAddGroup (∀ i, A i) := ⟨by
    rw [uniformContinuous_pi]
    intro i
    exact ((Pi.uniformContinuous_proj A i).comp uniformContinuous_fst).sub
      ((Pi.uniformContinuous_proj A i).comp uniformContinuous_snd)⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact Pi.complete A

omit [∀ i, IsTopologicalRing (A i)] in
/-- A countable product of rings whose filters of neighbourhoods of zero are countably
generated has a countably generated filter of neighbourhoods of zero. -/
theorem isCountablyGenerated_nhds_zero_pi [Countable ι]
    (h : ∀ i, (nhds (0 : A i)).IsCountablyGenerated) :
    (nhds (0 : ∀ i, A i)).IsCountablyGenerated := by
  rw [nhds_pi]
  let (i : ι) : (nhds (0 : A i)).IsCountablyGenerated := h i
  infer_instance

end Complete

section Types

variable {ι : Type*} [Finite ι] {A : ι → Type*} [∀ i, CommRing (A i)]
  [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)]
  [∀ i, IsLinearTopology (A i) (A i)]

/-- **A finite product of weakly admissible topological rings is weakly admissible.** The
product of weak ideals of definition of the factors is one of the product, and a finite product
of complete separated groups is complete and separated. -/
theorem isWeaklyAdmissible_pi' (h : ∀ i, IsWeaklyAdmissible (A i)) :
    letI : IsLinearTopology (∀ i, A i) (∀ i, A i) := pi_isLinearTopology
    IsWeaklyAdmissible (∀ i, A i) := by
  classical
  let : IsLinearTopology (∀ i, A i) (∀ i, A i) := pi_isLinearTopology
  let : ∀ i, T2Space (A i) := fun i ↦ (h i).2.2
  choose I hI using fun i ↦ (h i).1
  exact ⟨⟨Ideal.pi I, isWeakIdealOfDefinition_pi_of_topologicalSpace I hI⟩,
    completeSpace_pi' fun i ↦ (h i).2.1, inferInstance⟩

omit [∀ i, IsLinearTopology (A i) (A i)] in
/-- **A finite product of admissible topological rings is admissible.** The product of ideals
of definition of the factors is one of the product, and a finite product of complete separated
groups is complete and separated. -/
theorem isAdmissible_pi' (h : ∀ i, IsAdmissible (A i)) :
    IsAdmissible (∀ i, A i) := by
  classical
  let : ∀ i, T2Space (A i) := fun i ↦ (h i).2.1
  choose I hI using fun i ↦ (h i).1
  exact ⟨⟨Ideal.pi I, isIdealOfDefinition_pi I hI⟩,
    inferInstance, completeSpace_pi' fun i ↦ (h i).2.2⟩

/-- **A finite product of weakly adic topological rings is weakly adic.** If the closed powers
of `J i` form a fundamental system of open ideals of `A i`, then the closed powers of the
product of the `J i` form one of the product ring: a power of a product of ideals is the
product of the powers, and the closure of a product of ideals is the product of the
closures. -/
theorem isWeaklyAdic_pi' (h : ∀ i, IsWeaklyAdic (A i)) :
    letI : IsLinearTopology (∀ i, A i) (∀ i, A i) := pi_isLinearTopology
    IsWeaklyAdic (∀ i, A i) := by
  classical
  let : IsLinearTopology (∀ i, A i) (∀ i, A i) := pi_isLinearTopology
  let : ∀ i, T2Space (A i) := fun i ↦ (h i).toT2Space
  choose J hJopen hJbasis using fun i ↦ (h i).exists_ideal
  have hcoe : ∀ n : ℕ,
      ((((Ideal.pi J : Ideal (∀ i, A i)) ^ n).topologicalClosure) : Set (∀ i, A i)) =
      ((Ideal.pi (fun i ↦ ((J i ^ n).topologicalClosure : Ideal (A i)))) : Set (∀ i, A i)) := by
    intro n
    rw [Submodule.topologicalClosure_coe, Rig.pi_pow', coe_idealPi, coe_idealPi, closure_pi_set]
    exact Set.pi_congr rfl fun i _ ↦ (Submodule.topologicalClosure_coe (J i ^ n)).symm
  have hopen : ∀ n : ℕ,
      IsOpen ((((Ideal.pi J : Ideal (∀ i, A i)) ^ n).topologicalClosure) :
        Set (∀ i, A i)) := by
    intro n
    rw [hcoe n]
    exact isOpen_coe_idealPi _ fun i ↦ hJopen i n
  have hbasis := hasBasis_nhds_zero_pi
    (A := A) (fun i n ↦ ((J i ^ n).topologicalClosure : Ideal (A i)))
    (fun i n ↦ hJopen i n)
    (fun _ _ _ hab ↦ Submodule.topologicalClosure_mono (Ideal.pow_le_pow_right hab))
    (fun i ↦ hJbasis i)
  have : IsWeaklyPreAdic (∀ i, A i) :=
    ⟨⟨Ideal.pi J, hopen,
      hbasis.to_hasBasis (fun n _ ↦ ⟨n, trivial, (hcoe n).le⟩)
        fun n _ ↦ ⟨n, trivial, (hcoe n).ge⟩⟩⟩
  exact { completeSpace := completeSpace_pi' fun i ↦ (h i).completeSpace }

omit [∀ i, IsTopologicalRing (A i)] [∀ i, IsLinearTopology (A i) (A i)] in
/-- **A finite product of topological rings each having a finitely generated ideal of
definition has one.** The product of the ideals is an ideal of definition and is finitely
generated. -/
theorem exists_fg_isIdealOfDefinition_pi
    (h : ∀ i, ∃ I : Ideal (A i), IsIdealOfDefinition I ∧ I.FG) :
    ∃ I : Ideal (∀ i, A i), IsIdealOfDefinition I ∧ I.FG := by
  classical
  choose I hI hfg using h
  exact ⟨Ideal.pi I, isIdealOfDefinition_pi I hI, fg_idealPi I hfg⟩

end Types

end TopologicalRing

end
