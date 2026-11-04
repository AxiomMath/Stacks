module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Components
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveIdeal

/-!
# The components of the closure of the complement of a closed subscheme of a curve

Let `k` be a field, let `X` be a proper scheme over `k` which is equidimensional of dimension
one with at-worst-nodal singularities, and let `I ⊆ X` be a closed subscheme. The
scheme-theoretic closure `X'` of the complement of `I` is the reduced union of the irreducible
components of `X` not contained in `I`, so each of its irreducible components *is* one of those
components of `X`, and therefore has dimension one. Consequently `X'` is equidimensional, and it
has dimension one as soon as it is nonempty.

## Main results

* `Stacks.Curves.coe_support_complementaryCurveIdeal_eq_iUnion` — the support of the closure of
  the complement is the union of the ambient irreducible components not contained in the
  subscheme.
* `Stacks.Curves.topologicalKrullDim_irreducibleComponent_complementaryCurve_eq_one` — every
  irreducible component of that closure has dimension one.
* `Stacks.Curves.equidimensional_complementaryCurve` — the closure of the complement is
  equidimensional.
* `Stacks.Curves.topologicalKrullDim_complementaryCurve_eq_one` — a nonempty such closure is
  one-dimensional.

## Implementation notes

The support identity is `Stacks.Curves.complementaryCurveIdeal_eq_union_irreducibleComponents`
read through `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal`, the union of
the closures of a locally finite family of closed sets being their union.

An irreducible component `W` of `X'` has irreducible image in `X`, contained in that union;
the ambient space is Noetherian, being proper over a field, so the union is finite and the image
lies in a single ambient component `A`. Then `W` is contained in the preimage of `A`, which is
irreducible because `A` lies inside the range of the closed immersion `X' ⟶ X`; maximality of
`W` forces the two to agree, so `W` has the dimension of `A`, which is one by
`Stacks.Curves.topologicalKrullDim_irreducibleComponent_eq_one`.

## References

* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]

/-- **The closure of the complement of a closed subscheme of a reduced curve is supported on the
union of the ambient irreducible components not contained in that subscheme.** -/
theorem coe_support_complementaryCurveIdeal_eq_iUnion
    (hnodal : HasAtWorstNodalSingularities k X) (I : X.IdealSheafData) :
    ((complementaryCurveIdeal I).support : Set X) =
      ⋃ A : {A : Set X // A ∈ irreducibleComponents X ∧ ¬ A ⊆ (I.support : Set X)},
        (A.1 : Set X) := by
  have hLN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  set Zcomps := {A : Set X // A ∈ irreducibleComponents X ∧ ¬ A ⊆ (I.support : Set X)}
  have hcomponents : LocallyFinite (fun A : irreducibleComponents X => (A : Set X)) := by
    simpa using locallyFinite_irreducibleComponents_image (𝟙 X)
  have hUnionClosed : IsClosed (⋃ A : Zcomps, (A.1 : Set X)) :=
    (locallyFinite_component_subfamily hcomponents _).isClosed_iUnion fun A =>
      isClosed_of_mem_irreducibleComponents A.1 A.2.1
  have hSup : (↑(⨆ A : Zcomps, Closeds.closure A.1) : Set X) = ⋃ A : Zcomps, (A.1 : Set X) :=
    coe_iSup_closure_eq_iUnion_of_isClosed (fun A : Zcomps => A.1)
      (fun A => isClosed_of_mem_irreducibleComponents A.1 A.2.1) hUnionClosed
  rw [show complementaryCurveIdeal I =
    Scheme.IdealSheafData.vanishingIdeal (⨆ A : Zcomps, Closeds.closure A.1) from
      complementaryCurveIdeal_eq_union_irreducibleComponents hnodal I,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, hSup]

/-- **Every irreducible component of the closure of the complement of a closed subscheme of a
one-dimensional equidimensional nodal curve has dimension one.** -/
theorem topologicalKrullDim_irreducibleComponent_complementaryCurve_eq_one
    (hXeq : Equidimensional X) (hXdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) (I : X.IdealSheafData)
    (W : Set (complementaryCurve I)) (hW : W ∈ irreducibleComponents (complementaryCurve I)) :
    topologicalKrullDim W = 1 := by
  classical
  have hLN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have hCS : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have hN : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have hNS : NoetherianSpace X := inferInstance
  set ι := (complementaryCurveι I).base with hι
  have hemb : Topology.IsEmbedding ι :=
    (complementaryCurveι I).isClosedEmbedding.isEmbedding
  have himg : IsIrreducible (ι '' W) := hW.1.image ι (by fun_prop)
  have hfin : {A : Set X | A ∈ irreducibleComponents X ∧
      ¬ A ⊆ (I.support : Set X)}.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset fun A hA => hA.1
  have hrange : Set.range ι = ⋃₀ {A : Set X | A ∈ irreducibleComponents X ∧
      ¬ A ⊆ (I.support : Set X)} := by
    rw [hι, Scheme.IdealSheafData.range_subschemeι, Set.sUnion_eq_iUnion]
    exact coe_support_complementaryCurveIdeal_eq_iUnion hnodal I
  obtain ⟨A, hAmem, hWA⟩ := isIrreducible_iff_sUnion_isClosed.mp himg hfin.toFinset
    (fun A hA => isClosed_of_mem_irreducibleComponents A (hfin.mem_toFinset.mp hA).1)
    (by rw [hfin.coe_toFinset, ← hrange]; exact Set.image_subset_range _ _)
  rw [hfin.mem_toFinset] at hAmem
  have hArange : A ⊆ Set.range ι := hrange ▸ Set.subset_sUnion_of_mem hAmem
  have hAirr : IsIrreducible (ι ⁻¹' A) := by
    rw [isIrreducible_iff_irreducibleSpace,
      (hemb.homeomorphOfSubsetRange hArange).irreducibleSpace_iff,
      ← isIrreducible_iff_irreducibleSpace]
    exact hAmem.1.1
  have hWpre : W ⊆ ι ⁻¹' A := fun w hw => hWA ⟨w, hw, rfl⟩
  have hWeq : W = ι ⁻¹' A := Set.Subset.antisymm hWpre (hW.2 hAirr hWpre)
  rw [hWeq, IsHomeomorph.topologicalKrullDim_eq _
    (hemb.homeomorphOfSubsetRange hArange).isHomeomorph]
  exact topologicalKrullDim_irreducibleComponent_eq_one (X ↘ Spec (.of k)) hXeq hXdim A hAmem.1

/-- **The closure of the complement of a closed subscheme of a one-dimensional equidimensional
nodal curve is equidimensional.** -/
theorem equidimensional_complementaryCurve
    (hXeq : Equidimensional X) (hXdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) (I : X.IdealSheafData) :
    Equidimensional (complementaryCurve I) :=
  TopologicalSpace.Equidimensional.of_forall_topologicalKrullDim_eq fun W hW =>
    topologicalKrullDim_irreducibleComponent_complementaryCurve_eq_one hXeq hXdim hnodal I W hW

/-- **The closure of the complement of a closed subscheme of a one-dimensional equidimensional
nodal curve is one-dimensional, as soon as it is nonempty.** -/
theorem topologicalKrullDim_complementaryCurve_eq_one
    (hXeq : Equidimensional X) (hXdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) (I : X.IdealSheafData)
    (hne : Nonempty (complementaryCurve I)) :
    topologicalKrullDim (complementaryCurve I) = 1 := by
  obtain ⟨y⟩ := hne
  refine le_antisymm ?_ ?_
  · rw [← hXdim]
    exact (complementaryCurveι I).isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  · rw [← topologicalKrullDim_irreducibleComponent_complementaryCurve_eq_one hXeq hXdim hnodal I
      (irreducibleComponent y) (irreducibleComponent_mem_irreducibleComponents y)]
    exact topologicalKrullDim_subspace_le _ _

end Stacks.Curves
