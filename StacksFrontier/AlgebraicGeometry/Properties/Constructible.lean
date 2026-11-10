module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Constructible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Spectral.ConstructiblyClosedStable
public import StacksFrontier.Topology.Spectral.LimitGeneralizations

/-!
# Locally constructible subsets of schemes

A subset of a scheme is locally constructible exactly when its restriction to every affine open
subscheme is constructible. Near a generic point of an irreducible component, a locally
constructible subset either contains an open neighbourhood of that point or is avoided by one.
On a quasi-compact and quasi-separated scheme the constructible sets are governed by the
quasi-compact opens, because the underlying space is spectral.

## Main results

* `AlgebraicGeometry.spectralSpace_affineOpen`: an affine open of a scheme is a spectral space.
* `AlgebraicGeometry.isLocallyConstructible_iff_forall_affineOpens` characterizes locally
  constructible subsets by their restrictions to affine opens.
* `AlgebraicGeometry.compl_mem_nhds_of_isLocallyConstructible_of_mem_genericPoints`: a generic
  point outside the subset has an open neighbourhood disjoint from it.
* `AlgebraicGeometry.mem_nhds_of_isLocallyConstructible_of_mem_genericPoints`: a generic point
  inside the subset has an open neighbourhood contained in it.
* `AlgebraicGeometry.spectralSpace_of_compactSpace_of_quasiSeparatedSpace`: a quasi-compact and
  quasi-separated scheme has spectral underlying space.

## Implementation notes

An affine open `U` is represented as an element of `X.affineOpens`; its intersection with `E`,
regarded as a subset of `U`, is the subtype restriction `U.1 ↓∩ E`. Mathlib's `genericPoints X`
is the set of generic points of the irreducible components of `X`, and the existence of an open
neighbourhood disjoint from `E` is expressed by `Eᶜ ∈ 𝓝 ξ`.

## References

* [Stacks Project, Tag 054C](https://stacks.math.columbia.edu/tag/054C)
* [Stacks Project, Tag 094L](https://stacks.math.columbia.edu/tag/094L)
* [Stacks Project, Tag 0AAW](https://stacks.math.columbia.edu/tag/0AAW)
-/

@[expose] public section

open Topology TopologicalSpace
open scoped Set.Notation

universe u

namespace AlgebraicGeometry

/-- An affine open of a scheme is a spectral space: it is quasi-compact, quasi-separated,
sober and prespectral, each inherited from the affine scheme it carries. -/
public theorem spectralSpace_affineOpen {X : Scheme.{u}} (U : X.affineOpens) :
    SpectralSpace (U.1 : Set X) :=
  let : IsAffine (U : Scheme) := U.property
  { toT0Space := (U : X.Opens).2.isOpenEmbedding_subtypeVal.isEmbedding.t0Space
    toCompactSpace := isCompact_iff_compactSpace.mp U.property.isCompact
    toQuasiSober := (U : X.Opens).2.isOpenEmbedding_subtypeVal.quasiSober
    toQuasiSeparatedSpace := AlgebraicGeometry.quasiSeparatedSpace_of_isAffine (U : Scheme)
    toPrespectralSpace := (U : X.Opens).2.isOpenEmbedding_subtypeVal.prespectralSpace }

/-- A subset of a scheme is locally constructible if and only if
its restriction to every affine open subscheme is constructible. -/
@[stacks 054C, sga "3 VIB 3.7" "(iii), special case"]
public theorem isLocallyConstructible_iff_forall_affineOpens
    {X : Scheme.{u}} (E : Set X) :
    Topology.IsLocallyConstructible E ↔
      ∀ U : X.affineOpens, Topology.IsConstructible ((U.1 : Set X) ↓∩ E) := by
  rw [Topology.IsLocallyConstructible.iff_of_isOpenCover
    (U := fun U : X.affineOpens ↦ U) (by exact iSup_affineOpens_eq_top X)]
  refine ⟨fun h i ↦ ?_, fun h i ↦ (h i).isLocallyConstructible⟩
  have := Topology.IsOpenEmbedding.prespectralSpace i.1.2.isOpenEmbedding_subtypeVal
  have : QuasiSeparatedSpace (i.1 : Set X) := @quasiSeparatedSpace_of_isAffine _ i.property
  have := isCompact_iff_compactSpace.mp i.property.isCompact
  exact (h i).isConstructible

/-- In a T0 space, a point specializing to a generic point of an irreducible component equals
it. -/
private lemma eq_of_specializes_genericPoint {X : Type*} [TopologicalSpace X]
    [T0Space X] {ξ y : X} (hξ : ξ ∈ genericPoints X) (hyξ : y ⤳ ξ) : y = ξ :=
  (hyξ.antisymm <| specializes_iff_closure_subset.mpr <|
    hξ.2 isIrreducible_singleton.closure (specializes_iff_closure_subset.mp hyξ)).eq

/-- A generic point of an irreducible component which is not in a
locally constructible subset has an open neighbourhood disjoint from that subset. -/
@[stacks 0AAW "neighborhood_disjoint"]
public theorem compl_mem_nhds_of_isLocallyConstructible_of_mem_genericPoints
    {X : Scheme.{u}} {E : Set X} {ξ : X} (hE : IsLocallyConstructible E)
    (hξ : ξ ∈ genericPoints X) (hξE : ξ ∉ E) :
    Eᶜ ∈ 𝓝 ξ := by
  obtain ⟨U, hξU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ ξ))
  let : SpectralSpace (U.1 : Set X) := spectralSpace_affineOpen U
  let F : Set (U.1 : Set X) := (Subtype.val : (U.1 : Set X) → X) ⁻¹' E
  have hEc : IsConstructible F :=
    (hE.preimage_of_isOpenEmbedding
      (U : X.Opens).2.isOpenEmbedding_subtypeVal).isConstructible
  let ξU : (U.1 : Set X) := ⟨ξ, hξU⟩
  have hξnotcl : ξ ∉ closure E := by
    intro hξclGlobal
    have hξUcl : ξU ∈ closure F := by
      rw [(U : X.Opens).2.isOpenEmbedding_subtypeVal.isEmbedding.closure_eq_preimage_closure_image]
      change ξ ∈ closure ((Subtype.val : (U.1 : Set X) → X) ''
        ((Subtype.val : (U.1 : Set X) → X) ⁻¹' E))
      rw [Subtype.image_preimage_coe]
      simpa [Set.inter_comm] using
        (U : X.Opens).2.closure_inter (s := E) ⟨hξclGlobal, hξU⟩
    obtain ⟨y, hyE, hyξ⟩ :=
      mem_closure_iff_exists_specializes_of_isClosed_constructibleTopology
        (IsConstructible.isClosed_constructibleTopology hEc) hξUcl
    exact hξE (eq_of_specializes_genericPoint hξ
      ((subtype_specializes_iff y ξU).mp hyξ) ▸ hyE)
  exact Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hξnotcl)
    (Set.compl_subset_compl.mpr subset_closure)

/-- A locally constructible set containing the generic point of an irreducible component
contains an open neighbourhood of that point. -/
@[stacks 0AAW "neighborhood_contained"]
public theorem mem_nhds_of_isLocallyConstructible_of_mem_genericPoints
    {X : Scheme.{u}} {E : Set X} {ξ : X} (hE : IsLocallyConstructible E)
    (hξ : ξ ∈ genericPoints X) (hξE : ξ ∈ E) :
    E ∈ 𝓝 ξ := by
  simpa only [compl_compl] using
    compl_mem_nhds_of_isLocallyConstructible_of_mem_genericPoints
      (E := Eᶜ) (by
        intro x; obtain ⟨U, hxU, hU, hUE⟩ := hE x
        exact ⟨U, hxU, hU, by convert hUE.compl using 1; ext y; simp⟩) hξ (by simpa using hξE)

/-- The underlying topological space of a quasi-compact and
quasi-separated scheme is a spectral space: it is sober and quasi-compact, the quasi-compact
opens form a basis, and any two of them meet in a quasi-compact open. -/
@[stacks 094L, sga "4 IV 4.2.1" "special case"]
public instance spectralSpace_of_compactSpace_of_quasiSeparatedSpace (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] : SpectralSpace X where

end AlgebraicGeometry

end
