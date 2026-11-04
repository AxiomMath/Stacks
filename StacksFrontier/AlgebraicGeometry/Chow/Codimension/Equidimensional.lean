module

public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.WeilDivisors
public import StacksCore.Tactic.StacksAttribute

/-!
# Local equidimensionality for an integer-valued function on a scheme

Chapter 42 of the Stacks Project grades cycles by codimension as well as by dimension, but only
on a scheme on which the dimension function `δ` takes a single value on all the components
through any given point. Three ways of saying this are equivalent on a locally Noetherian
scheme:

1. the scheme decomposes into open and closed subschemes `X_n`, `n : ℤ`, such that every
   irreducible component of `X_n` has `δ`-value `n` at its generic point;
2. every point has an open neighbourhood on whose irreducible components `δ` takes a single
   value at the generic points;
3. for every point, all irreducible components of the whole scheme through that point have the
   same `δ`-value at their generic points.

The three conditions are stated for an arbitrary function `δ : X → ℤ`: nothing about the
relative dimension function of a Chow situation is used, and stating them this way lets the two
sufficient conditions of the source — normality and Cohen--Macaulayness — be proved where they
naturally live.

## Main definitions

* `Stacks.Chow.HasDimensionDecomposition` — condition (1), the decomposition into
  pure-dimensional open and closed subschemes.
* `Stacks.Chow.IsLocallyPureDimensional` — condition (2), the neighbourhood condition.
* `Stacks.Chow.IsLocallyEquidimensional` — condition (3), equality of the values at the generic
  points of all components through a point.

## Main results

* `Stacks.Chow.locallyEquidimensional_tfae` — the three conditions are equivalent.

## Implementation notes

Condition (1) is phrased with `Stacks.Chow.IsClopenDecomposition`, the notion of a decomposition
into open and closed subschemes already used throughout this development: a pairwise disjoint
family of open subschemes covering the scheme. Closedness of the pieces is automatic and is
`Stacks.Chow.IsClopenDecomposition.isClopen`, so it need not be required separately.

The implication (3) ⇒ (1) is the only one with content. The function sending a point to the
common value of `δ` on the components through it is constant on each irreducible component, and
the irreducible components of a locally Noetherian scheme form a locally finite family of closed
sets, so that function is continuous for the discrete topology on `ℤ`; the pieces `X_n` are its
fibres.

## References

* [Stacks Project, Tag 0FE3](https://stacks.math.columbia.edu/tag/0FE3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Generic points of irreducible components of an open subset -/

/-- A generic point of an irreducible component of an open subset of a topological space is, as a
point of the ambient space, the generic point of an irreducible component of that space. -/
@[ega "0 2.1.6" "partial"]
private theorem exists_mem_irreducibleComponents_isGenericPoint_val {α : Type*}
    [TopologicalSpace α] (U : Opens α) {Z : Set U} (hZ : Z ∈ irreducibleComponents U) (ξ : U)
    (hξ : IsGenericPoint ξ Z) :
    ∃ C ∈ irreducibleComponents α, IsGenericPoint (ξ : α) C := by
  have hj : Topology.IsOpenEmbedding (Subtype.val : U → α) :=
    U.isOpen.isOpenEmbedding_subtypeVal
  obtain ⟨C, hC, hsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (Subtype.val '' Z)
      (hZ.1.image _ continuous_subtype_val.continuousOn)
  have hZC : Z ⊆ Subtype.val ⁻¹' C := fun z hz ↦ hsub ⟨z, hz, rfl⟩
  have hξC : (ξ : α) ∈ C := hsub ⟨ξ, hξ.mem, rfl⟩
  have hcl : closure (Subtype.val '' Z) = C := by
    rw [hZC.antisymm (hZ.2 (preimage_mem_irreducibleComponents hC hj ⟨ξ, hξC, ⟨ξ, rfl⟩⟩).1 hZC)]
    exact closure_image_preimage_of_isPreirreducible _ hj.isOpenMap C
      ⟨ξ, hξC⟩ hC.1.2 (isClosed_of_mem_irreducibleComponents C hC)
  exact ⟨C, hC, hcl ▸ hξ.image continuous_subtype_val⟩

/-- A point of an open subset which is the generic point of a subset of the ambient space is the
generic point of the part of that subset lying in the open subset. -/
private theorem isGenericPoint_val_preimage {α : Type*} [TopologicalSpace α] (U : Opens α)
    {Z : Set α} {ξ : α} (hξ : IsGenericPoint ξ Z) (hξU : ξ ∈ U) :
    IsGenericPoint (⟨ξ, hξU⟩ : U) (Subtype.val ⁻¹' Z) := by
  show closure ({(⟨ξ, hξU⟩ : U)} : Set U) = Subtype.val ⁻¹' Z
  ext z
  rw [closure_subtype]
  simp [Set.image_singleton, hξ.def]

/-! ### The three conditions -/

/-- **Stacks 0FE3 (1).** An integer-valued function `δ` on a scheme *has a dimension
decomposition* if the scheme decomposes into open and closed subschemes `X_n`, indexed by the
integers, such that `δ` takes the value `n` at the generic point of every irreducible component
of `X_n`. -/
def HasDimensionDecomposition {X : Scheme.{u}} (δ : X → ℤ) : Prop :=
  ∃ U : ℤ → X.Opens, IsClopenDecomposition U ∧
    ∀ n : ℤ, ∀ Z ∈ irreducibleComponents (U n), ∀ ξ : U n, IsGenericPoint ξ Z → δ ξ = n

/-- **Stacks 0FE3 (2).** An integer-valued function `δ` on a scheme is *locally pure
dimensional* if every point has an open neighbourhood on all of whose irreducible components `δ`
takes one and the same value at the generic point. -/
def IsLocallyPureDimensional {X : Scheme.{u}} (δ : X → ℤ) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ n : ℤ,
    ∀ Z ∈ irreducibleComponents U, ∀ ξ : U, IsGenericPoint ξ Z → δ ξ = n

/-- **Stacks 0FE3 (3).** An integer-valued function `δ` on a scheme is *locally
equidimensional* if, for every point, `δ` takes one and the same value at the generic points of
all the irreducible components of the scheme through that point. -/
@[sga "6 X 7.14" "more general"]
def IsLocallyEquidimensional {X : Scheme.{u}} (δ : X → ℤ) : Prop :=
  ∀ x : X, ∃ n : ℤ, ∀ Z ∈ irreducibleComponents X, x ∈ Z → ∀ ξ : X,
    IsGenericPoint ξ Z → δ ξ = n

/-! ### The implications between them -/

/-- A dimension decomposition exhibits, for each point, an open neighbourhood on whose
components the function is constant at the generic points: the piece containing the point. -/
theorem IsLocallyPureDimensional.of_hasDimensionDecomposition {X : Scheme.{u}} {δ : X → ℤ}
    (h : HasDimensionDecomposition δ) : IsLocallyPureDimensional δ := by
  obtain ⟨U, hU, hpure⟩ := h
  intro x
  obtain ⟨n, hn⟩ := hU.exists_mem x
  exact ⟨U n, hn, n, hpure n⟩

/-- Local purity implies local equidimensionality: a component of the whole scheme through the
point meets the neighbourhood, and its part there is a component of the neighbourhood with the
same generic point. -/
theorem IsLocallyEquidimensional.of_isLocallyPureDimensional {X : Scheme.{u}} {δ : X → ℤ}
    (h : IsLocallyPureDimensional δ) : IsLocallyEquidimensional δ := by
  intro x
  obtain ⟨U, hxU, n, hU⟩ := h x
  refine ⟨n, fun Z hZ hxZ ξ hξ ↦ ?_⟩
  have hξU : ξ ∈ U := (hξ.mem_open_set_iff U.isOpen).2 ⟨x, hxZ, hxU⟩
  exact hU _ (preimage_mem_irreducibleComponents hZ U.isOpen.isOpenEmbedding_subtypeVal
    ⟨x, hxZ, ⟨⟨x, hxU⟩, rfl⟩⟩) ⟨ξ, hξU⟩ (isGenericPoint_val_preimage U hξ hξU)

/-- Local equidimensionality implies the existence of a dimension decomposition: on a locally
Noetherian scheme the common value of the function on the components through a point is a
locally constant function of that point, and the decomposition is given by its fibres. -/
theorem HasDimensionDecomposition.of_isLocallyEquidimensional {X : Scheme.{u}}
    [IsLocallyNoetherian X] {δ : X → ℤ} (h : IsLocallyEquidimensional δ) :
    HasDimensionDecomposition δ := by
  classical
  let g : X → ℤ := fun x ↦ (h x).choose
  have hg : ∀ (x : X) (C : Set X), C ∈ irreducibleComponents X → x ∈ C →
      ∀ ξ : X, IsGenericPoint ξ C → δ ξ = g x := fun x ↦ (h x).choose_spec
  have hconst : ∀ C : irreducibleComponents X, ∀ x ∈ (C : Set X), ∀ y ∈ (C : Set X),
      g x = g y := by
    intro C x hx y hy
    have hη := genericPoints.isGenericPoint_ofComponent C
    exact (hg x C C.2 hx _ hη).symm.trans (hg y C C.2 hy _ hη)
  have hfinite : LocallyFinite fun C : irreducibleComponents X ↦ (C : Set X) := by
    simpa using locallyFinite_irreducibleComponents_image (𝟙 X)
  have hcontinuous : Continuous g := by
    refine hfinite.continuous ?_ (fun C ↦ isClosed_of_mem_irreducibleComponents (C : Set X) C.2)
      fun C ↦ ?_
    · simpa [Set.sUnion_eq_biUnion] using sUnion_irreducibleComponents (X := X)
    · obtain ⟨y, hy⟩ := C.2.1.1
      exact continuousOn_const.congr fun x hx ↦ hconst C x hx y hy
  refine ⟨fun n ↦ ⟨g ⁻¹' {n}, (isOpen_discrete {n}).preimage hcontinuous⟩, ⟨?_, ?_⟩, ?_⟩
  · intro m n hmn
    refine disjoint_iff_inf_le.2 fun x hx ↦ ?_
    exact absurd ((hx.1 : g x = m).symm.trans hx.2) hmn
  · exact le_antisymm le_top fun x _ ↦ Opens.mem_iSup.2 ⟨g x, rfl⟩
  · intro n Z hZ ξ hξ
    obtain ⟨C, hC, hξC⟩ := exists_mem_irreducibleComponents_isGenericPoint_val _ hZ ξ hξ
    exact (hg (ξ : X) C hC hξC.mem (ξ : X) hξC).trans ξ.property

/-- **Stacks 0FE3.** For an integer-valued function on a locally Noetherian scheme, having a
decomposition into pure-dimensional open and closed subschemes, being locally pure dimensional,
and being locally equidimensional are equivalent. -/
@[stacks 0FE3 "equivalent_conditions"]
theorem locallyEquidimensional_tfae (X : Scheme.{u}) [IsLocallyNoetherian X] (δ : X → ℤ) :
    List.TFAE [
      HasDimensionDecomposition δ,
      IsLocallyPureDimensional δ,
      IsLocallyEquidimensional δ] := by
  tfae_have 1 → 2 := IsLocallyPureDimensional.of_hasDimensionDecomposition
  tfae_have 2 → 3 := IsLocallyEquidimensional.of_isLocallyPureDimensional
  tfae_have 3 → 1 := HasDimensionDecomposition.of_isLocallyEquidimensional
  tfae_finish

end Stacks.Chow

end
