module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Generic points, their local schemes, and local finiteness

The generic-point decomposition of the sheaf of meromorphic functions (Stacks Tags 0EMF, 02OW,
0EMH) compares that sheaf with the family of pushforwards `η_* 𝒪_{X, η}` indexed by the generic
points of the irreducible components. This file records the two structural facts that family
has, for an arbitrary scheme.

First, each member is a skyscraper: the local scheme `Spec 𝒪_{X, η}` at a generic point has
exactly one point, lying over `η`, so the preimage of an open set is everything or nothing
according to whether that open set contains `η`. No reducedness is needed; what makes the
local scheme a point is that a generic point has no proper generalization.

Second, the family is locally finite, under the hypothesis that quasi-compact opens have
finitely many irreducible components: every point has an open neighbourhood in which every
generic point of `X` specializes to it, and consequently the set of generic points lying in an
open set is *constant* on the opens between that neighbourhood and the point.

## Main results

* `Stacks.AlgebraicGeometry.GenericPointGluing.range_fromSpecStalk_genericPoint`: the range of
  `Spec 𝒪_{X, η} ⟶ X` at a generic point is `{η}`.
* `Stacks.AlgebraicGeometry.GenericPointGluing.fromSpecStalk_preimage_eq_top` and
  `fromSpecStalk_preimage_eq_bot`: the resulting preimages of open sets.
* `Stacks.AlgebraicGeometry.GenericPointGluing.subsingleton_specStalk`: `Spec 𝒪_{X, η}` has at
  most one point.
* `Stacks.AlgebraicGeometry.GenericPointGluing.exists_open_generic_specializes_scheme`: the
  local-finiteness neighbourhood.
* `Stacks.AlgebraicGeometry.GenericPointGluing.genericPoints_mem_eq_of_le`: the set of generic
  points in an open set is constant between that neighbourhood and the point.
* `Stacks.AlgebraicGeometry.GenericPointGluing.finite_genericPoints_specializes`: only finitely
  many generic points specialize to a given point.

## Implementation notes

The topological lemma `exists_open_generic_specializes` and the transport
`mem_genericPoints_subtype` duplicate two `private` lemmas of
`StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalksWeaklyAssociated` (of the same names
there). They are reproved here rather than imported because `private` declarations are not
accessible across modules; if that file ever makes them public, these should be deleted in
favour of them.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GenericPointGluing

section Topology

variable {Y : Type*} [TopologicalSpace Y]

/-- A generic point of `Y` lying in an open set is a generic point of that open set. -/
theorem mem_genericPoints_subtype (U : Opens Y) (y : U) (hy : (y : Y) ∈ genericPoints Y) :
    y ∈ genericPoints U := by
  show closure {y} ∈ irreducibleComponents U
  rw [U.isOpen.isOpenEmbedding_subtypeVal.isEmbedding.isInducing.closure_eq_preimage_closure_image,
    Set.image_singleton]
  exact preimage_mem_irreducibleComponents hy U.isOpen.isOpenEmbedding_subtypeVal
    ⟨y.1, subset_closure (Set.mem_singleton y.1), ⟨y, rfl⟩⟩

/-- If an open set has finitely many irreducible components then it contains only finitely
many generic points of the ambient space. -/
theorem finite_genericPoints_mem [T0Space Y] (U : Opens Y)
    (h : (irreducibleComponents U).Finite) :
    {y | y ∈ genericPoints Y ∧ y ∈ U}.Finite := by
  refine ((genericPoints.finite h).image Subtype.val).subset ?_
  rintro y ⟨hy, hyU⟩
  exact ⟨⟨y, hyU⟩, mem_genericPoints_subtype U ⟨y, hyU⟩ hy, rfl⟩

/-- Around any point there is an open set in which every generic point of the ambient space
specializes to that point: delete the finitely many irreducible components missing the point. -/
theorem exists_open_generic_specializes (hfinite : (irreducibleComponents Y).Finite) (x : Y) :
    ∃ V : Opens Y, x ∈ V ∧ ∀ y ∈ V, y ∈ genericPoints Y → y ⤳ x := by
  classical
  let B := {Z ∈ irreducibleComponents Y | x ∉ Z}
  have hB : B.Finite := hfinite.subset fun _ h ↦ h.1
  let V : Opens Y := ⟨(⋃ Z ∈ B, Z)ᶜ, (hB.isClosed_biUnion fun Z hZ ↦
    isClosed_of_mem_irreducibleComponents Z hZ.1).isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  · show x ∉ ⋃ Z ∈ B, Z
    simpa only [Set.mem_iUnion, not_exists] using fun Z hZ ↦ hZ.2
  · intro y hy hyg
    by_contra h
    exact hy (Set.mem_iUnion.2 ⟨closure {y}, Set.mem_iUnion.2
      ⟨⟨hyg, fun hx ↦ h (specializes_iff_mem_closure.2 hx)⟩,
        subset_closure (Set.mem_singleton y)⟩⟩)

end Topology

variable {X : Scheme.{u}}

/-- The only generalization of a generic point is itself: the closure of a generalization is an
irreducible closed set containing an irreducible component, hence equal to it, and schemes are
`T0`. -/
theorem eq_of_specializes_genericPoint {η y : X} (hη : η ∈ genericPoints X) (h : y ⤳ η) :
    y = η :=
  (h.antisymm (specializes_iff_mem_closure.2
    (hη.2 isIrreducible_singleton.closure h.closure_subset (subset_closure rfl)))).eq

/-- The range of `Spec 𝒪_{X, η} ⟶ X` at a generic point is the single point `η`. -/
theorem range_fromSpecStalk_genericPoint {η : X} (hη : η ∈ genericPoints X) :
    Set.range (X.fromSpecStalk η).base = {η} := by
  rw [Scheme.range_fromSpecStalk]
  exact Set.eq_singleton_iff_unique_mem.2
    ⟨specializes_rfl, fun y hy ↦ eq_of_specializes_genericPoint hη hy⟩

/-- Every point of `Spec 𝒪_{X, η}` maps to the generic point `η`. -/
private theorem base_fromSpecStalk_genericPoint {η : X} (hη : η ∈ genericPoints X)
    (z : Spec (X.presheaf.stalk η)) : (X.fromSpecStalk η).base z = η := by
  have hz := Set.mem_range_self (f := (X.fromSpecStalk η).base) z
  rwa [range_fromSpecStalk_genericPoint hη, Set.mem_singleton_iff] at hz

/-- An open set containing a generic point pulls back to everything along `Spec 𝒪_{X, η} ⟶ X`. -/
theorem fromSpecStalk_preimage_eq_top {η : X} (hη : η ∈ genericPoints X) {U : X.Opens}
    (hU : η ∈ U) : (X.fromSpecStalk η) ⁻¹ᵁ U = ⊤ := by
  refine Opens.ext (Set.eq_univ_iff_forall.2 fun z ↦ ?_)
  show (X.fromSpecStalk η).base z ∈ U
  rwa [base_fromSpecStalk_genericPoint hη z]

/-- An open set missing a generic point pulls back to nothing along `Spec 𝒪_{X, η} ⟶ X`. -/
theorem fromSpecStalk_preimage_eq_bot {η : X} (hη : η ∈ genericPoints X) {U : X.Opens}
    (hU : η ∉ U) : (X.fromSpecStalk η) ⁻¹ᵁ U = ⊥ := by
  refine Opens.ext (Set.eq_empty_iff_forall_notMem.2 fun z hz ↦ ?_)
  exact hU (Set.mem_of_eq_of_mem (base_fromSpecStalk_genericPoint hη z).symm hz)

/-- At a generic point the local scheme `Spec 𝒪_{X, η}` has at most one point; equivalently the
stalk there has at most one prime ideal. -/
theorem subsingleton_specStalk {η : X} (hη : η ∈ genericPoints X) :
    Subsingleton (Spec (X.presheaf.stalk η)) := by
  refine ⟨fun a b ↦ (X.fromSpecStalk η).isEmbedding.injective ?_⟩
  exact (base_fromSpecStalk_genericPoint hη a).trans (base_fromSpecStalk_genericPoint hη b).symm

/-- Every point has an open neighbourhood with finitely many irreducible components. -/
private theorem exists_open_mem_finite_irreducibleComponents (X : Scheme.{u})
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    ∃ W : X.Opens, x ∈ W ∧ (irreducibleComponents W).Finite := by
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  exact ⟨W, hxW, hfinite W hW.isCompact⟩

/-- Only finitely many generic points specialize to a given point: they all lie in any affine
open neighbourhood of it, which has finitely many irreducible components. -/
theorem finite_genericPoints_specializes (X : Scheme.{u})
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    {η | η ∈ genericPoints X ∧ η ⤳ x}.Finite := by
  obtain ⟨W, hxW, hW⟩ := exists_open_mem_finite_irreducibleComponents X hfinite x
  refine (finite_genericPoints_mem W hW).subset ?_
  rintro η ⟨hη, hspec⟩
  exact ⟨hη, hspec.mem_open W.isOpen hxW⟩

/-- The scheme form of `exists_open_generic_specializes`: around any point of a scheme whose
quasi-compact opens have finitely many irreducible components there is an open set in which
every generic point specializes to that point. -/
theorem exists_open_generic_specializes_scheme (X : Scheme.{u})
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∀ y ∈ V, y ∈ genericPoints X → y ⤳ x := by
  obtain ⟨W, hxW, hW⟩ := exists_open_mem_finite_irreducibleComponents X hfinite x
  obtain ⟨V, hxV, hV⟩ := exists_open_generic_specializes hW (⟨x, hxW⟩ : W)
  refine ⟨⟨Subtype.val '' (V : Set W), W.isOpenEmbedding.isOpenMap _ V.isOpen⟩,
    ⟨⟨x, hxW⟩, hxV, rfl⟩, ?_⟩
  rintro y ⟨z, hz, rfl⟩ hyg
  exact (hV z hz (mem_genericPoints_subtype W z hyg)).map continuous_subtype_val

/-- Local constancy of the family: between the neighbourhood supplied by
`exists_open_generic_specializes_scheme` and the point itself, the set of generic points
contained in an open set does not change. This is what makes the family of generic-point
contributions locally finite, hence its coproduct and product agree. -/
theorem genericPoints_mem_eq_of_le {x : X} {V W : X.Opens}
    (hV : ∀ y ∈ V, y ∈ genericPoints X → y ⤳ x) (hxW : x ∈ W) (hWV : W ≤ V) :
    {η | η ∈ genericPoints X ∧ η ∈ W} = {η | η ∈ genericPoints X ∧ η ∈ V} :=
  Set.ext fun η ↦ ⟨fun h ↦ ⟨h.1, hWV h.2⟩, fun h ↦ ⟨h.1, (hV η h.2 h.1).mem_open W.isOpen hxW⟩⟩

end Stacks.AlgebraicGeometry.GenericPointGluing
