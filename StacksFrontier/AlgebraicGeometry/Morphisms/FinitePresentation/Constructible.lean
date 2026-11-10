module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Constructible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible
public import StacksFrontier.Topology.Spectral.AsDirectedInverseLimit
public import StacksFrontier.Topology.Spectral.BijectionHomeomorph
public import StacksFrontier.Topology.Spectral.ConstructiblyClosedStable

/-!
# Constructible subsets and morphisms of schemes

The inverse image of a locally constructible subset under a morphism of schemes is again
locally constructible: locally on affine opens of source and target the morphism restricts to a
morphism of affine schemes, where Mathlib's `AlgebraicGeometry.Scheme.Hom.isConstructible_preimage`
applies.

A locally constructible subset `E` of a scheme is moreover a neighbourhood of every point `x`
all of whose generalizations it contains. Indeed `E` is constructible on an affine open
neighbourhood of `x`, that neighbourhood is a spectral space, and on a spectral space every
point in the closure of a constructible set is a specialization of a point of that set; so `x`
cannot lie in the closure of the complement of `E`.

## Main results

* `AlgebraicGeometry.isLocallyConstructible_preimage`: the inverse image of a locally
  constructible subset is locally constructible.
* `AlgebraicGeometry.mem_nhds_of_isLocallyConstructible_of_specializes_subset`: a locally
  constructible set containing every generalization of a point contains an open neighbourhood of
  that point.

## Implementation notes

Mathlib already contains the constructible case of the inverse image statement, with its Stacks
tag; the corresponding local assertion is stated separately, since the two conclusions are
independent.

The neighbourhood conclusion is expressed as membership in the neighbourhood filter. This is
equivalent to the existence of an open set containing the point and contained in `E`.

## References

* [Stacks Project, Tag 054I](https://stacks.math.columbia.edu/tag/054I)
* [Stacks Project, Tag 05LW](https://stacks.math.columbia.edu/tag/05LW)
-/

@[expose] public section

open CategoryTheory Topology
open scoped Set.Notation

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 054I.** The inverse image of a locally constructible
subset under a morphism of schemes is locally constructible. -/
@[stacks 054I "locally constructible case",
  ega "IV 1.8.2" "locally constructible",
  ega "IV 9.2.2" "Forward implication only"]
public lemma isLocallyConstructible_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    {s : Set Y} (hs : IsLocallyConstructible s) :
    IsLocallyConstructible (f ⁻¹' s) := by
  intro x
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨B, hB, rfl⟩, hxB, hBA⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (by simpa using hxA)
      (f ⁻¹ᵁ A).isOpen
  refine ⟨B, B.2.mem_nhds hxB, B.2, ?_⟩
  have hsets : (f.resLE A B hBA) ⁻¹' ((A.1 : Set Y) ↓∩ s) =
      (B : Set X) ↓∩ (f ⁻¹' s) := by
    ext z
    change ((f.resLE A B hBA z).1 ∈ s) ↔ f z.1 ∈ s
    rw [f.coe_resLE_apply hBA z]
  rw [← hsets]
  exact (f.resLE A B hBA).isConstructible_preimage
    ((isLocallyConstructible_iff_forall_affineOpens s).mp hs ⟨A, hA⟩)

/-- **Stacks Project, Tag 05LW.** A locally constructible subset of a scheme that contains every
generalization of `x` contains an open neighbourhood of `x`. -/
@[stacks 05LW, ega "0 9.2.5" "sufficiency", sga "3 XV 3.3" "partial"]
public theorem mem_nhds_of_isLocallyConstructible_of_specializes_subset
    {X : Scheme.{u}} {E : Set X} {x : X} (hE : IsLocallyConstructible E)
    (h : {x' : X | x' ⤳ x} ⊆ E) :
    E ∈ 𝓝 x := by
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
  let : SpectralSpace (U.1 : Set X) := spectralSpace_affineOpen U
  let F : Set (U.1 : Set X) := (U.1 : Set X) ↓∩ Eᶜ
  have hF : IsConstructible F := by
    simpa [F] using ((isLocallyConstructible_iff_forall_affineOpens E).mp hE U).compl
  let xU : (U.1 : Set X) := ⟨x, hxU⟩
  have hxNotClosure : x ∉ closure Eᶜ := by
    intro hxClosure
    have hxUClosure : xU ∈ closure F := by
      have hEmb := (U : X.Opens).2.isOpenEmbedding_subtypeVal.isEmbedding
      rw [hEmb.closure_eq_preimage_closure_image]
      change x ∈ closure
        ((Subtype.val : (U.1 : Set X) → X) ''
          ((Subtype.val : (U.1 : Set X) → X) ⁻¹' Eᶜ))
      rw [Subtype.image_preimage_coe]
      simpa [Set.inter_comm] using
        ((U : X.Opens).2.closure_inter (s := Eᶜ) ⟨hxClosure, hxU⟩)
    obtain ⟨y, hyF, hyspec⟩ :=
      mem_closure_iff_exists_specializes_of_isClosed_constructibleTopology
        (IsConstructible.isClosed_constructibleTopology hF) hxUClosure
    have hyspec' : (y : X) ⤳ x := (subtype_specializes_iff y xU).mp hyspec
    exact (show (y : X) ∉ E by simpa [F] using hyF) (h hyspec')
  refine Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hxNotClosure) ?_
  intro y hy
  by_contra hyE
  exact hy (subset_closure hyE)

end AlgebraicGeometry

end
