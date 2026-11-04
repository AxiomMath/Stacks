module

public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints
public import StacksFrontier.Topology.Noetherian.GenericPointsDenseOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dimension of a scheme of finite type over a field with a dense open subscheme

Let `Z` be a quasi-compact scheme locally of finite type over a field `k`, and let `ι : X ⟶ Z`
be an open immersion with dense image. Then `dim Z ≤ dim X`, so the two are equal. By
[Stacks, Tag 0A21] the dimension of a scheme locally of finite type over `k` is the supremum of
the transcendence degrees of the residue fields at the generic points of its irreducible
components. Every such generic point of `Z` lies in the dense open `ι(X)`, `Z` being a Noetherian
space, and is the image of a generic point of `X` with the same residue field over `k`.

This is the bound used for the closure of a curve in a compactification: the scheme-theoretic
closure of `X` in a compactification has the same dimension as `X`.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_le_of_isOpenImmersion_of_denseRange`: `dim Z ≤ dim X`.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A dense open of a scheme of finite type over a field carries its dimension.** Let
`πZ : Z ⟶ Spec k` be quasi-compact and locally of finite type and `ι : X ⟶ Z` an open immersion
with dense image. Then `dim Z ≤ dim X`. -/
@[ega "IV 10.6.2" "partial", ega "IV 5.2.5" "special case"]
theorem topologicalKrullDim_le_of_isOpenImmersion_of_denseRange (k : Type u) [Field k]
    {X Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType πZ] [QuasiCompact πZ]
    (ι : X ⟶ Z) [IsOpenImmersion ι] (hι : DenseRange ι.base) :
    topologicalKrullDim Z ≤ topologicalKrullDim X := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian πZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace πZ
  have : IsNoetherian Z := {}
  rw [topologicalKrullDim_eq_iSup_trdeg_residueField k Z πZ,
    topologicalKrullDim_eq_iSup_trdeg_residueField k X (ι ≫ πZ)]
  refine iSup_le fun ⟨η, hη⟩ ↦ ?_
  obtain ⟨x, rfl⟩ : η ∈ Set.range ι.base :=
    TopologicalSpace.NoetherianSpace.mem_of_mem_genericPoints_of_dense
      ι.isOpenEmbedding.isOpen_range hι hη
  refine le_iSup_of_le ⟨x, genericPoints_preimage_of_isOpenImmersion ι hη⟩ ?_
  rw [trdeg_residueField_of_surjectiveOnStalks k πZ ι x]

end AlgebraicGeometry

end
