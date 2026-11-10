module

public import Mathlib.Topology.UniformSpace.Equiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.IdealOfDefinition

/-!
# Transport of the admissibility conditions along an isomorphism of topological rings

An isomorphism of topological rings — a ring equivalence which is continuous in both
directions — carries each of the conditions of **Stacks 07E8** and **Stacks 0AMV** on a
topological ring to the same condition on the other ring, taking an ideal of definition to the
image ideal. This file records that transport for every one of them, so that a property proved
for one presenting ring of an affine formal algebraic space can be read off any other.

The conditions come in two families. The ideal-theoretic ones — being an ideal of definition,
being a weak ideal of definition, defining the adic topology — transport because the
isomorphism is a homeomorphism carrying the ideal onto its image and the powers of the ideal
onto the powers of the image. Completeness transports because the right uniformity of a
topological additive group is the pullback of the neighbourhood filter of zero along
subtraction, so an additive homeomorphism is automatically a uniform isomorphism.

## Main results

* `TopologicalRing.isIdealOfDefinition_map_of_ringEquiv` and
  `TopologicalRing.isWeakIdealOfDefinition_map_of_ringEquiv`: the image of an (weak) ideal of
  definition is an (weak) ideal of definition.
* `TopologicalRing.isAdic_map_of_ringEquiv`: the image of an ideal defining the topology
  defines the topology.
* `TopologicalRing.uniformContinuous_of_continuous_ringEquiv`,
  `TopologicalRing.uniformEquivOfRingEquiv` and
  `TopologicalRing.isComplete_of_ringEquiv`: completeness transports.
* `TopologicalRing.isPreAdmissible_of_ringEquiv`,
  `TopologicalRing.isWeaklyPreAdmissible_of_ringEquiv`,
  `TopologicalRing.isAdmissible_of_ringEquiv`,
  `TopologicalRing.isWeaklyAdmissible_of_ringEquiv`,
  `TopologicalRing.isPreAdic_of_ringEquiv` and `TopologicalRing.isAdic_of_ringEquiv`: the five
  conditions of Stacks 07E8 and the weak admissibility of Stacks 0AMV transport.
* `TopologicalRing.exists_fg_isIdealOfDefinition_of_ringEquiv`: having a finitely generated
  ideal of definition transports; with `TopologicalRing.isAdic_of_ringEquiv` this is the
  transport of membership in `WAdm^{adic*}`, condition (4) of **Stacks 0AID**.

## Implementation notes

The hypotheses are a `RingEquiv` together with continuity of it and of its inverse, rather
than a bundled isomorphism in a category of topological rings: that is the shape in which an
isomorphism of presenting rings comes out of Stacks 0AN0, applied in both directions.

`TopologicalRing.IsComplete` is completeness together with separatedness for the right
uniformity of the additive group, which is not an instance; the uniform structures are
therefore named explicitly and the `UniformEquiv` is built by hand from the description of the
uniformity as a pullback along subtraction.

## References

* [Stacks Project, Tag 07E8](https://stacks.math.columbia.edu/tag/07E8)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
-/

@[expose] public section

namespace TopologicalRing

open Filter
open scoped Topology

universe u v

variable {A : Type u} {C : Type v} [CommRing A] [CommRing C]
  [TopologicalSpace A] [TopologicalSpace C]

/-! ### The underlying homeomorphism -/

/-- A ring equivalence which is continuous in both directions, read as a homeomorphism. -/
public def homeomorphOfRingEquiv (e : A ≃+* C) (he : Continuous e)
    (he' : Continuous e.symm) : A ≃ₜ C where
  toEquiv := e.toEquiv
  continuous_toFun := he
  continuous_invFun := he'

omit [TopologicalSpace A] [TopologicalSpace C] in
/-- The image of an ideal under a ring equivalence is, as a set, the image of the underlying
set. -/
public theorem coe_map_ringEquiv (e : A ≃+* C) (I : Ideal A) :
    ((I.map (e : A →+* C) : Ideal C) : Set C) = (e : A → C) '' (I : Set A) :=
  Ideal.map_eq_image_of_surjective _ e.surjective

/-- A continuous ring homomorphism sends the neighbourhood filter of zero into the
neighbourhood filter of zero. -/
public theorem tendsto_nhds_zero_of_continuous (φ : A →+* C) (hφ : Continuous φ) :
    Tendsto φ (𝓝 (0 : A)) (𝓝 (0 : C)) :=
  hφ.tendsto' 0 0 (map_zero φ)

/-! ### The ideal-theoretic conditions -/

/-- The image of an open ideal under a homeomorphic ring equivalence is open. -/
private theorem isOpen_map_ringEquiv (e : A ≃+* C) (he : Continuous e)
    (he' : Continuous e.symm) {J : Ideal A} (hJ : IsOpen (J : Set A)) :
    IsOpen ((J.map (e : A →+* C) : Ideal C) : Set C) := by
  rw [coe_map_ringEquiv e J]
  exact (homeomorphOfRingEquiv e he he').isOpenMap _ hJ

/-- If the powers of `I` are eventually inside every neighbourhood of zero, so are the powers of
its image. -/
private theorem exists_pow_map_subset (e : A ≃+* C) (he : Continuous e) {I : Ideal A}
    (hI : ∀ V ∈ 𝓝 (0 : A), ∃ n, ((I ^ n : Ideal A) : Set A) ⊆ V) {V : Set C} (hV : V ∈ 𝓝 (0 : C)) :
    ∃ n, (((I.map (e : A →+* C)) ^ n : Ideal C) : Set C) ⊆ V := by
  obtain ⟨n, hn⟩ := hI _ (tendsto_nhds_zero_of_continuous (e : A →+* C) he hV)
  refine ⟨n, ?_⟩
  rw [← Ideal.map_pow, coe_map_ringEquiv e (I ^ n)]
  exact Set.image_subset_iff.mpr hn

/-- The image of an ideal of definition under an isomorphism of topological rings is an ideal
of definition: the isomorphism is an open map carrying the ideal onto its image, and it carries
the powers of the ideal onto the powers of the image. -/
public theorem isIdealOfDefinition_map_of_ringEquiv (e : A ≃+* C) (he : Continuous e)
    (he' : Continuous e.symm) {I : Ideal A} (hI : IsIdealOfDefinition I) :
    IsIdealOfDefinition (I.map (e : A →+* C)) := by
  exact ⟨isOpen_map_ringEquiv e he he' hI.1, fun V hV ↦ exists_pow_map_subset e he hI.2 hV⟩

/-- The image of a weak ideal of definition under an isomorphism of topological rings is a weak
ideal of definition: the image is open, and the isomorphism carries the powers of an element to
the powers of its image, so topological nilpotence is preserved. -/
public theorem isWeakIdealOfDefinition_map_of_ringEquiv (e : A ≃+* C) (he : Continuous e)
    (he' : Continuous e.symm) {I : Ideal A} (hI : IsWeakIdealOfDefinition I) :
    IsWeakIdealOfDefinition (I.map (e : A →+* C)) := by
  refine ⟨isOpen_map_ringEquiv e he he' hI.1, fun y hy ↦ ?_⟩
  · rw [← SetLike.mem_coe, coe_map_ringEquiv e I] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxnil : Tendsto (x ^ ·) atTop (𝓝 (0 : A)) := hI.2 x hx
    have hcomp := (tendsto_nhds_zero_of_continuous (e : A →+* C) he).comp hxnil
    rw [IsTopologicallyNilpotent]
    simpa [Function.comp_def] using hcomp

/-- The image of an ideal whose powers define the topology under an isomorphism of topological
rings is an ideal whose powers define the topology. -/
public theorem isAdic_map_of_ringEquiv [IsTopologicalRing A] [IsTopologicalRing C]
    (e : A ≃+* C) (he : Continuous e) (he' : Continuous e.symm) {I : Ideal A}
    (hI : _root_.IsAdic I) : _root_.IsAdic (I.map (e : A →+* C)) := by
  rw [_root_.isAdic_iff] at hI ⊢
  exact ⟨fun n ↦ by rw [← Ideal.map_pow]; exact isOpen_map_ringEquiv e he he' (hI.1 n),
    fun V hV ↦ exists_pow_map_subset e he hI.2 hV⟩

omit [TopologicalSpace A] [TopologicalSpace C] in
/-- The image of a finitely generated ideal under a ring equivalence is finitely generated. -/
public theorem fg_map_of_ringEquiv (e : A ≃+* C) {I : Ideal A} (hI : I.FG) :
    (I.map (e : A →+* C)).FG :=
  hI.map (e : A →+* C)

/-! ### Completeness -/

section Complete

variable [IsTopologicalRing A] [IsTopologicalRing C]

/-- An isomorphism of topological rings is uniformly continuous for the right uniformities of
the additive groups: those uniformities are the pullbacks of the neighbourhood filters of zero
along subtraction, which the isomorphism respects. -/
public theorem uniformContinuous_of_continuous_ringEquiv (e : A ≃+* C) (he : Continuous e) :
    @UniformContinuous A C (IsTopologicalAddGroup.rightUniformSpace A)
      (IsTopologicalAddGroup.rightUniformSpace C) e := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
  rw [uniformContinuous_def]
  intro V hV
  rw [uniformity_eq_comap_nhds_zero' C] at hV
  obtain ⟨U, hU, hUV⟩ := Filter.mem_comap.mp hV
  rw [uniformity_eq_comap_nhds_zero' A]
  refine Filter.mem_comap.mpr ⟨(e : A → C) ⁻¹' U,
    he.continuousAt.preimage_mem_nhds (by simpa using hU), fun p hp ↦ ?_⟩
  refine hUV ?_
  change e p.2 + -e p.1 ∈ U
  rw [← map_neg, ← map_add]
  exact hp

/-- An isomorphism of topological rings is a uniform isomorphism for the right uniformities of
the additive groups. -/
public def uniformEquivOfRingEquiv (e : A ≃+* C) (he : Continuous e)
    (he' : Continuous e.symm) :
    @UniformEquiv A C (IsTopologicalAddGroup.rightUniformSpace A)
      (IsTopologicalAddGroup.rightUniformSpace C) :=
  @UniformEquiv.mk A C (IsTopologicalAddGroup.rightUniformSpace A)
    (IsTopologicalAddGroup.rightUniformSpace C) e.toEquiv
    (uniformContinuous_of_continuous_ringEquiv e he)
    (uniformContinuous_of_continuous_ringEquiv e.symm he')

/-- Completeness together with separatedness transports along an isomorphism of topological
rings. -/
public theorem isComplete_of_ringEquiv (e : A ≃+* C) (he : Continuous e)
    (he' : Continuous e.symm) (hA : IsComplete A) : IsComplete C := by
  obtain ⟨hT2, hcs⟩ := hA
  let : T2Space A := hT2
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
  refine ⟨(homeomorphOfRingEquiv e he he').symm.isEmbedding.t2Space, ?_⟩
  exact (uniformEquivOfRingEquiv e he he').completeSpace_iff.mp hcs

end Complete

/-! ### The conditions of Stacks 07E8 and Stacks 0AMV -/

/-- Pre-admissibility transports along an isomorphism of topological rings. -/
public theorem isPreAdmissible_of_ringEquiv (e : A ≃+* C) (he : Continuous e)
    (he' : Continuous e.symm) (hA : IsPreAdmissible A) : IsPreAdmissible C :=
  ⟨hA.choose.map (e : A →+* C),
    isIdealOfDefinition_map_of_ringEquiv e he he' hA.choose_spec⟩

/-- Weak pre-admissibility transports along an isomorphism of topological rings. -/
public theorem isWeaklyPreAdmissible_of_ringEquiv (e : A ≃+* C) (he : Continuous e)
    (he' : Continuous e.symm) (hA : IsWeaklyPreAdmissible A) : IsWeaklyPreAdmissible C :=
  ⟨hA.choose.map (e : A →+* C),
    isWeakIdealOfDefinition_map_of_ringEquiv e he he' hA.choose_spec⟩

/-- Admissibility transports along an isomorphism of topological rings. -/
public theorem isAdmissible_of_ringEquiv [IsTopologicalRing A] [IsTopologicalRing C]
    (e : A ≃+* C) (he : Continuous e) (he' : Continuous e.symm) (hA : IsAdmissible A) :
    IsAdmissible C :=
  ⟨isPreAdmissible_of_ringEquiv e he he' hA.1, isComplete_of_ringEquiv e he he' hA.2⟩

/-- Being pre-adic transports along an isomorphism of topological rings. -/
public theorem isPreAdic_of_ringEquiv [IsTopologicalRing A] [IsTopologicalRing C]
    (e : A ≃+* C) (he : Continuous e) (he' : Continuous e.symm) (hA : IsPreAdic A) :
    IsPreAdic C := by
  obtain ⟨I, hIdef, hIadic⟩ := hA
  exact ⟨I.map (e : A →+* C), isIdealOfDefinition_map_of_ringEquiv e he he' hIdef,
    isAdic_map_of_ringEquiv e he he' hIadic⟩

/-- Being adic transports along an isomorphism of topological rings. -/
public theorem isAdic_of_ringEquiv [IsTopologicalRing A] [IsTopologicalRing C]
    (e : A ≃+* C) (he : Continuous e) (he' : Continuous e.symm) (hA : IsAdic A) : IsAdic C :=
  ⟨isPreAdic_of_ringEquiv e he he' hA.1, isComplete_of_ringEquiv e he he' hA.2⟩

/-- Weak admissibility transports along an isomorphism of topological rings. -/
public theorem isWeaklyAdmissible_of_ringEquiv [IsTopologicalRing A] [IsLinearTopology A A]
    [IsTopologicalRing C] [IsLinearTopology C C] (e : A ≃+* C) (he : Continuous e)
    (he' : Continuous e.symm) (hA : IsWeaklyAdmissible A) : IsWeaklyAdmissible C := by
  refine ⟨isWeaklyPreAdmissible_of_ringEquiv e he he' hA.1, ?_, ?_⟩
  · exact (isComplete_of_ringEquiv e he he' ⟨hA.2.2, hA.2.1⟩).2
  · exact (isComplete_of_ringEquiv e he he' ⟨hA.2.2, hA.2.1⟩).1

/-- **Transport of condition (4) of Stacks 0AID.** Having a finitely generated ideal of
definition transports along an isomorphism of topological rings. Together with
`TopologicalRing.isAdic_of_ringEquiv` this says that membership in `WAdm^{adic*}` depends only
on the isomorphism class of the topological ring. -/
public theorem exists_fg_isIdealOfDefinition_of_ringEquiv (e : A ≃+* C) (he : Continuous e)
    (he' : Continuous e.symm) (hA : ∃ I : Ideal A, IsIdealOfDefinition I ∧ I.FG) :
    ∃ J : Ideal C, IsIdealOfDefinition J ∧ J.FG := by
  obtain ⟨I, hIdef, hIfg⟩ := hA
  exact ⟨I.map (e : A →+* C), isIdealOfDefinition_map_of_ringEquiv e he he' hIdef,
    fg_map_of_ringEquiv e hIfg⟩

end TopologicalRing

end
