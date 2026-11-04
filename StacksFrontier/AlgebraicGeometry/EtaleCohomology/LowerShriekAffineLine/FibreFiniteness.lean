module
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.UnibranchLocallyIrreducible
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable

public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksFrontier.Topology.Dimension.NowhereDense
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeDimensionOne.GenericFibre

/-!
# Complements of fibrewise dense opens in families of curves are quasi-finite

Let `p : X ⟶ V` be a quasi-compact morphism locally of finite type all of whose fibres have
dimension at most one, and let `W ⊆ X` be an open subset which is dense in every fibre of `p`.
Then the complement of `W` meets every fibre in a finite set, so every immersion into `X` with
image in the complement of `W` is locally quasi-finite over `V`. This is the step "the fibres of
`Z → V` have dimension `0` (as `W` is dense in the fibres) and hence `Z → V` is quasi-finite" of
the proof of Tag 0GKX.

## Main results

* `AlgebraicGeometry.finite_preimage_singleton_inter_compl_of_dense` — the complement of `W` meets
  every fibre of `p` in a finite set.
* `AlgebraicGeometry.locallyQuasiFinite_comp_of_dense_fiber` — an immersion `i : Z ⟶ X` with image
  outside `W` is locally quasi-finite after composing with `p`.

## References

* [Stacks Project, Tag 0GKX](https://stacks.math.columbia.edu/tag/0GKX)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X V : Scheme.{u}}

/-- **The complement of a fibrewise dense open meets every fibre in a finite set**, for a
quasi-compact morphism locally of finite type whose fibres have dimension at most one: in the
fibre, a Noetherian space of dimension at most one, the complement is closed and nowhere dense,
so it contains no irreducible component and is finite. -/
theorem finite_preimage_singleton_inter_compl_of_dense (p : X ⟶ V) [LocallyOfFiniteType p]
    [QuasiCompact p] (s : V) (hdim : topologicalKrullDim (p.fiber s) ≤ 1) {W : Set X}
    (hWo : IsOpen W) (hW : Dense ((p.fiberι s) ⁻¹' W)) :
    ((p : X → V) ⁻¹' {s} ∩ Wᶜ).Finite := by
  have : IsNoetherian (p.fiber s) :=
    isNoetherian_of_locallyOfFiniteType_of_quasiCompact (V.residueField s)
      (p.fiberToSpecResidueField s)
  have ho : IsOpen ((p.fiberι s) ⁻¹' W) := hWo.preimage (p.fiberι s).continuous
  have hcl : IsClosed ((p.fiberι s) ⁻¹' Wᶜ) := ho.isClosed_compl
  have hnd : IsNowhereDense ((p.fiberι s) ⁻¹' Wᶜ) := by
    refine (isClosed_isNowhereDense_iff_compl.2 ⟨?_, ?_⟩).2 <;>
      rw [Set.preimage_compl, compl_compl]
    exacts [ho, hW]
  have hfin : ((p.fiberι s) ⁻¹' Wᶜ).Finite :=
    Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hdim hcl
      ((hcl.isNowhereDense_iff_forall_irreducibleComponents_not_subset).1 hnd)
  refine (hfin.image (p.fiberι s)).subset ?_
  rintro x ⟨hxs, hxW⟩
  have hx : p.fiberι s ((p.fiberHomeo s).symm ⟨x, hxs⟩) = x := by
    rw [← Scheme.Hom.fiberHomeo_apply, Homeomorph.apply_symm_apply]
  exact ⟨_, by rwa [Set.mem_preimage, hx], hx⟩

/-- **An immersion with image outside a fibrewise dense open is quasi-finite over the base.** Let
`p : X ⟶ V` be quasi-compact and locally of finite type with fibres of dimension at most one, let
`W ⊆ X` be open and dense in every fibre of `p`, and let `i : Z ⟶ X` be an immersion whose image
does not meet `W`. Then `i ≫ p` is locally quasi-finite. -/
theorem locallyQuasiFinite_comp_of_dense_fiber {Z : Scheme.{u}} (p : X ⟶ V)
    [LocallyOfFiniteType p] [QuasiCompact p] (hdim : ∀ s, topologicalKrullDim (p.fiber s) ≤ 1)
    (W : X.Opens) (hW : ∀ s, Dense ((p.fiberι s) ⁻¹' (W : Set X))) (i : Z ⟶ X) [IsImmersion i]
    (hi : Set.range i.base ⊆ (W : Set X)ᶜ) : LocallyQuasiFinite (i ≫ p) := by
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun s ↦ ?_
  refine ((finite_preimage_singleton_inter_compl_of_dense p s (hdim s) W.isOpen (hW s)).preimage
    i.isEmbedding.injective.injOn).subset fun z hz ↦ ⟨hz, hi ⟨z, rfl⟩⟩

end AlgebraicGeometry

end
