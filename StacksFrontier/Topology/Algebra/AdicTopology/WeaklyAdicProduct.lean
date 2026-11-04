module

public import Mathlib.RingTheory.Ideal.Maps
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeOnReductionsIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.TautIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdic
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Finite products of weakly admissible, admissible and weakly adic rings

A finite product of topological rings carries the product topology, and the ideal `Ideal.pi I`
cut out by a family of ideals of the factors is the rectangular neighbourhood built from them.
This file shows that the three completeness-flavoured classes of linearly topologized rings pass
to a finite product by taking `Ideal.pi` of the witnessing ideals of the factors: weak
admissibility, admissibility and weak adicness.  It also records that the ideals `Ideal.pi I`
for `I i` a weak ideal of definition of the factor `A i` form a fundamental system of
neighbourhoods of zero in the product, so that they are cofinal among the weak ideals of
definition of the product.

## Main results

* `TopologicalRing.isWeaklyAdmissible_pi`: a finite product of weakly admissible rings is
  weakly admissible.
* `TopologicalRing.isAdmissible_pi`: a finite product of admissible rings is admissible.
* `TopologicalRing.isWeaklyAdic_pi`: a finite product of weakly adic rings is weakly adic.
* `TopologicalRing.hasBasis_nhds_zero_idealPi` and
  `TopologicalRing.exists_idealPi_le_of_isWeakIdealOfDefinition`: the products of weak ideals of
  definition of the factors are a neighbourhood basis of zero, hence cofinal among the weak
  ideals of definition of the product.
* `TopologicalRing.isWeakIdealOfDefinition_map_evalRingHom`: conversely, the projections of a
  weak ideal of definition of the product are weak ideals of definition of the factors.

## Implementation notes

Linear topologicity of the product over itself is not an instance and is hypothesised wherever a
statement needs it; `TopologicalRing.pi_isLinearTopology` discharges it.

Openness of `Ideal.pi I` is openness of a product of open sets over a finite index type, and
smallness of its powers rests on the identification of a power of `Ideal.pi I` with the
`Ideal.pi` of the powers, which holds because the ideals of a finite product of rings are
exactly the products of ideals of the factors (`Ideal.piOrderIso`).

Completeness of the product is completeness of a product of complete uniform spaces, once the
canonical uniformity of the additive group of the product is identified with the product of the
canonical uniformities of the factors.

## References

* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0AI3](https://stacks.math.columbia.edu/tag/0AI3)
* [Stacks Project, Tag 07E8](https://stacks.math.columbia.edu/tag/07E8)
* [Stacks Project, Tag 0GXE](https://stacks.math.columbia.edu/tag/0GXE)
-/

@[expose] public section

namespace TopologicalRing

section Pi

open Filter
open scoped Topology

variable {ι : Type*} (A : ι → Type*) [∀ i, CommRing (A i)]
  [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)]

omit [∀ i, IsTopologicalRing (A i)] in
/-- A product of open ideals, over a finite index type, is an open ideal of the product. -/
public theorem isOpen_idealPi [Finite ι] (I : ∀ i, Ideal (A i))
    (hI : ∀ i, IsOpen ((I i : Ideal (A i)) : Set (A i))) :
    IsOpen ((Ideal.pi I : Ideal (∀ i, A i)) : Set (∀ i, A i)) := by
  rw [coe_idealPi]
  exact isOpen_set_pi Set.finite_univ fun i _ ↦ hI i

omit [∀ i, IsTopologicalRing (A i)] in
/-- **A product of weak ideals of definition of the factors, over a finite index type, is a weak
ideal of definition of the product.** It is open by `TopologicalRing.isOpen_idealPi`, and an
element of it is topologically nilpotent because each of its components is
(`TopologicalRing.isTopologicallyNilpotent_pi_iff`). -/
public theorem isWeakIdealOfDefinition_idealPi [Finite ι] (I : ∀ i, Ideal (A i))
    (hI : ∀ i, TopologicalRing.IsWeakIdealOfDefinition (I i)) :
    TopologicalRing.IsWeakIdealOfDefinition (Ideal.pi I : Ideal (∀ i, A i)) :=
  ⟨isOpen_idealPi A I fun i ↦ (hI i).1, fun x hx ↦
    isTopologicallyNilpotent_pi_iff.mpr fun i ↦ (hI i).2 _ (Ideal.mem_pi I x |>.mp hx i)⟩

omit [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)] in
/-- Over a finite index type a power of a product of ideals is the product of their powers:
the ideals of a finite product of rings are exactly the products of ideals of the factors, and
the projection of a power is the power of the projection. -/
private theorem idealPi_pow [Finite ι] (I : ∀ i, Ideal (A i)) (n : ℕ) :
    (Ideal.pi I) ^ n = Ideal.pi fun i ↦ I i ^ n := by
  have hsplit : Ideal.pi (fun i ↦ ((Ideal.pi I) ^ n).map (Pi.evalRingHom A i)) =
      (Ideal.pi I) ^ n := Ideal.piOrderIso.symm_apply_apply _
  rw [← hsplit]
  exact congrArg Ideal.pi (funext fun i ↦ by rw [Ideal.map_pow, Ideal.map_evalRingHom_pi])

/-- A finite product of topological rings whose additive groups are complete for their canonical
uniformities is complete for the canonical uniformity of its own additive group: that uniformity
is the product of the uniformities of the factors, and a product of complete uniform spaces is
complete. -/
public theorem completeSpace_pi [Finite ι]
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

/-- **A finite product of weakly admissible linearly topologized rings is weakly admissible.**
The product of weak ideals of definition of the factors is open, and an element of it is
topologically nilpotent because each of its components is; completeness and separatedness are
those of a finite product. -/
public theorem isWeaklyAdmissible_pi [Finite ι] [∀ i, IsLinearTopology (A i) (A i)]
    [IsLinearTopology (∀ i, A i) (∀ i, A i)]
    (h : ∀ i, TopologicalRing.IsWeaklyAdmissible (A i)) :
    TopologicalRing.IsWeaklyAdmissible (∀ i, A i) := by
  let : ∀ i, T2Space (A i) := fun i ↦ (h i).2.2
  choose I hI using fun i ↦ (h i).1
  refine ⟨⟨Ideal.pi I, isOpen_idealPi A I fun i ↦ (hI i).1, fun x hx ↦ ?_⟩,
    completeSpace_pi A fun i ↦ (h i).2.1, inferInstance⟩
  rw [isTopologicallyNilpotent_pi_iff]
  exact fun i ↦ (hI i).2 (x i) ((Ideal.mem_pi I x).mp hx i)

/-- **A finite product of admissible topological rings is admissible.** The product of ideals of
definition of the factors is open, and a power of it is contained in the product of the
corresponding powers, which a large enough exponent forces inside any rectangular
neighbourhood of zero. -/
public theorem isAdmissible_pi [Finite ι] (h : ∀ i, TopologicalRing.IsAdmissible (A i)) :
    TopologicalRing.IsAdmissible (∀ i, A i) := by
  classical
  cases nonempty_fintype ι
  let : ∀ i, T2Space (A i) := fun i ↦ (h i).2.1
  choose I hI using fun i ↦ (h i).1
  refine ⟨⟨Ideal.pi I, isOpen_idealPi A I fun i ↦ (hI i).1, fun U hU ↦ ?_⟩,
    inferInstance, completeSpace_pi A fun i ↦ (h i).2.2⟩
  rw [nhds_pi] at hU
  obtain ⟨T, -, V, hV, hsub⟩ := Filter.mem_pi.mp hU
  choose m hm using fun i ↦ (hI i).2 (V i) (hV i)
  refine ⟨Finset.univ.sup m, fun x hx ↦ hsub fun i _ ↦ ?_⟩
  rw [idealPi_pow] at hx
  exact hm i (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i))
    ((Ideal.mem_pi _ x).mp hx i))

/-- **A finite product of weakly adic linearly topologized rings is weakly adic.** The closed
powers of the product of the witnessing ideals of the factors are the products of their closed
powers, hence open, and they form a neighbourhood basis of zero because a rectangular
neighbourhood is caught by a single large enough exponent. -/
public theorem isWeaklyAdic_pi [Finite ι] [∀ i, IsLinearTopology (A i) (A i)]
    [IsLinearTopology (∀ i, A i) (∀ i, A i)]
    [∀ i, TopologicalRing.IsWeaklyAdic (A i)] :
    TopologicalRing.IsWeaklyAdic (∀ i, A i) := by
  classical
  cases nonempty_fintype ι
  let : ∀ i, T2Space (A i) := fun i ↦ inferInstance
  choose I hIopen hIbasis using fun i ↦
    TopologicalRing.IsWeaklyPreAdic.exists_ideal (A := A i)
  have hcoe (n : ℕ) : ((((Ideal.pi I) ^ n).topologicalClosure : Ideal (∀ i, A i)) :
      Set (∀ i, A i)) =
        Set.univ.pi fun i ↦ (((I i ^ n).topologicalClosure : Ideal (A i)) : Set (A i)) := by
    rw [Submodule.topologicalClosure_coe, idealPi_pow, coe_idealPi, closure_pi_set]
    simp only [Submodule.topologicalClosure_coe]
  have hopen (n : ℕ) :
      IsOpen ((((Ideal.pi I) ^ n).topologicalClosure : Ideal (∀ i, A i)) : Set (∀ i, A i)) := by
    rw [hcoe n]
    exact isOpen_set_pi Set.finite_univ fun i _ ↦ hIopen i n
  let : TopologicalRing.IsWeaklyPreAdic (∀ i, A i) := by
    refine ⟨Ideal.pi I, hopen, Filter.hasBasis_iff.mpr fun U ↦ ⟨fun hU ↦ ?_, ?_⟩⟩
    · rw [nhds_pi] at hU
      obtain ⟨T, -, V, hV, hsub⟩ := Filter.mem_pi.mp hU
      choose m hm using fun i ↦ (hIbasis i).mem_iff.mp (hV i)
      refine ⟨Finset.univ.sup m, trivial, ?_⟩
      rw [hcoe]
      exact fun x hx ↦ hsub fun i _ ↦ (hm i).2
        (Submodule.topologicalClosure_mono
          (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i)))
          (hx i (Set.mem_univ i)))
    · rintro ⟨n, -, hn⟩
      exact Filter.mem_of_superset ((hopen n).mem_nhds (Submodule.zero_mem _)) hn
  exact TopologicalRing.IsWeaklyAdic.mk
    (completeSpace_pi A fun i ↦ TopologicalRing.IsWeaklyAdic.completeSpace)

/-- **In a finite product of weakly admissible linearly topologized rings the products of weak
ideals of definition of the factors form a fundamental system of neighbourhoods of zero.** Each
such product is an open ideal all of whose elements are topologically nilpotent, and conversely
a rectangular neighbourhood of zero contains one of them because the weak ideals of definition
of each factor are a neighbourhood basis there. -/
public theorem hasBasis_nhds_zero_idealPi [Finite ι] [∀ i, IsLinearTopology (A i) (A i)]
    (h : ∀ i, TopologicalRing.IsWeaklyAdmissible (A i)) :
    (𝓝 (0 : ∀ i, A i)).HasBasis
      (fun I : ∀ i, Ideal (A i) ↦ ∀ i, TopologicalRing.IsWeakIdealOfDefinition (I i))
      (fun I ↦ ((Ideal.pi I : Ideal (∀ i, A i)) : Set (∀ i, A i))) := by
  refine Filter.hasBasis_iff.mpr fun U ↦ ⟨fun hU ↦ ?_, ?_⟩
  · rw [nhds_pi] at hU
    obtain ⟨T, -, V, hV, hsub⟩ := Filter.mem_pi.mp hU
    choose I hI hIsub using fun i ↦
      (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition (h i)).mem_iff.mp (hV i)
    refine ⟨I, hI, ?_⟩
    rw [coe_idealPi]
    exact fun x hx ↦ hsub fun i _ ↦ hIsub i (hx i (Set.mem_univ i))
  · rintro ⟨I, hI, hIU⟩
    exact Filter.mem_of_superset
      ((isOpen_idealPi A I fun i ↦ (hI i).1).mem_nhds (Submodule.zero_mem _)) hIU

/-- **The products of weak ideals of definition of the factors are cofinal among the weak ideals
of definition of a finite product of weakly admissible linearly topologized rings**: every weak
ideal of definition of the product contains one of them. -/
public theorem exists_idealPi_le_of_isWeakIdealOfDefinition [Finite ι]
    [∀ i, IsLinearTopology (A i) (A i)]
    (h : ∀ i, TopologicalRing.IsWeaklyAdmissible (A i)) {K : Ideal (∀ i, A i)}
    (hK : TopologicalRing.IsWeakIdealOfDefinition K) :
    ∃ I : ∀ i, Ideal (A i),
      (∀ i, TopologicalRing.IsWeakIdealOfDefinition (I i)) ∧ Ideal.pi I ≤ K := by
  obtain ⟨I, hI, hIK⟩ := (hasBasis_nhds_zero_idealPi A h).mem_iff.mp
    (hK.1.mem_nhds (Submodule.zero_mem K))
  exact ⟨I, hI, fun _ hx ↦ hIK hx⟩

/-- **The projections of a weak ideal of definition of a finite product of weakly admissible
linearly topologized rings are weak ideals of definition of the factors.** An ideal of a finite
product of rings is the product of its projections, so an element of a projection is carried
back into the ideal by `Pi.single` and is topologically nilpotent there; and the projection
contains the corresponding projection of a product of weak ideals of definition of the factors
below the ideal, which is open. -/
public theorem isWeakIdealOfDefinition_map_evalRingHom [Finite ι]
    [∀ i, IsLinearTopology (A i) (A i)]
    (h : ∀ i, TopologicalRing.IsWeaklyAdmissible (A i)) {K : Ideal (∀ i, A i)}
    (hK : TopologicalRing.IsWeakIdealOfDefinition K) (i : ι) :
    TopologicalRing.IsWeakIdealOfDefinition (K.map (Pi.evalRingHom A i)) := by
  classical
  obtain ⟨I, hI, hIK⟩ := exists_idealPi_le_of_isWeakIdealOfDefinition A h hK
  refine ⟨Ideal.isOpen_of_isOpen_subideal ?_ (hI i).1, fun x hx ↦ ?_⟩
  · calc I i = (Ideal.pi I).map (Pi.evalRingHom A i) := (Ideal.map_evalRingHom_pi i).symm
      _ ≤ K.map (Pi.evalRingHom A i) := Ideal.map_mono hIK
  · have hKpi : Ideal.pi (fun j ↦ K.map (Pi.evalRingHom A j)) = K :=
      Ideal.piOrderIso.symm_apply_apply K
    have hmem : Pi.single i x ∈ K := by
      rw [← hKpi]
      exact Ideal.single_mem_pi hx
    have hnil := isTopologicallyNilpotent_pi_iff.mp (hK.2 _ hmem) i
    rwa [Pi.single_eq_same] at hnil

end Pi

end TopologicalRing

end
