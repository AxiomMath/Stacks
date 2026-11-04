module

public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.UnramifiedCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
import all StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.UnramifiedCodimensionOne

/-!
# Étaleness from flatness at a point and unramifiedness in codimension one

A morphism of locally Noetherian schemes which is quasi-finite and flat at a point that is not
the generic point of an irreducible component of its source is étale at that point as soon as it
is unramified at every one-dimensional generization of the point.

## Main results

* `AlgebraicGeometry.etaleAt_of_isFlatAt_of_unramifiedAt_codimensionOne` is the criterion
  `AlgebraicGeometry.etaleAt_of_flat_of_unramifiedAt_codimensionOne` with flatness asked for only
  at the point, rather than of the whole morphism: the flat locus of a morphism of finite
  presentation is open ([Stacks, Tag 0399]), so a point of flatness has an open neighbourhood
  over which the morphism is flat, and the generizations of the point all lie in that
  neighbourhood.

## Implementation notes

The reduction to the affine opens on which the morphism is of finite type, and the transfer of
étaleness and unramifiedness along the open immersions, use the private lemmas of
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.UnramifiedCodimensionOne`,
which is therefore imported with `import all`.

## References

* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 0BJH](https://stacks.math.columbia.edu/tag/0BJH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Étaleness from flatness at the point and unramifiedness in codimension one.** A morphism
of locally Noetherian schemes which is quasi-finite and flat at a point that is not the generic
point of an irreducible component of its source is étale at that point, provided it is
unramified at every one-dimensional generization of the point.

This is `AlgebraicGeometry.etaleAt_of_flat_of_unramifiedAt_codimensionOne` with flatness asked
for only at the point. Quasi-finiteness provides affine opens on which the morphism is of finite
type, hence of finite presentation over the locally Noetherian target, so the flat locus of the
restriction is open by [Stacks, Tag 0399] and contains an affine open neighbourhood `W` of the
point. Every generization of a point lies in each of its open neighbourhoods, so the
codimension-one hypothesis survives the passage to `W`, over which the morphism is flat. -/
public theorem etaleAt_of_isFlatAt_of_unramifiedAt_codimensionOne
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (x : X) (hqf : quasiFiniteAt f x) (hflat : (f.stalkMap x).hom.Flat)
    (hgen : x ∉ genericPoints X)
    (hunr : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 → UnramifiedAt f x') :
    EtaleAt f x := by
  classical
  obtain ⟨U, V, hxV, hVU, hft⟩ := hqf.1
  have _ : IsAffine V.1.toScheme := V.2
  have _ : IsAffine U.1.toScheme := U.2
  have _ : LocallyOfFiniteType (f.resLE U.1 V.1 hVU) :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).2
      ((RingHom.finiteType_respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f U.1 V.1 hVU)).mpr hft)
  set f₀ := f.resLE U.1 V.1 hVU with hf₀
  set x₀ : V.1.toScheme := ⟨x, hxV⟩ with hx₀
  -- Replace the assertion by the corresponding one for the restriction to the affine opens.
  refine etaleAt_of_etaleAt_comp V.1.ι f x₀ ?_
  rw [← Scheme.Hom.resLE_comp_ι f hVU]
  refine etaleAt_comp_of_etaleAt f₀ U.1.ι x₀ ?_
  -- The restriction is of finite presentation, so its flat locus is open; choose an affine open
  -- neighbourhood of the point inside it.
  have hflat₀ : (f₀.stalkMap x₀).hom.Flat :=
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff (f.resLEStalkMap hVU x₀)).mpr hflat
  obtain ⟨W, hx₀W, hflatW⟩ := exists_isOpen_flat_of_isFlatAt f₀ x₀ hflat₀
  have _ : Flat (W.ι ≫ f₀) := hflatW
  set x₁ : W.toScheme := ⟨x₀, hx₀W⟩ with hx₁
  refine etaleAt_of_etaleAt_comp W.ι f₀ x₁ ?_
  -- Dimensions of local rings are unchanged by the two open immersions.
  have hdimW : ∀ z : W.toScheme, ringKrullDim (W.toScheme.presheaf.stalk z) =
      ringKrullDim (X.presheaf.stalk (V.1.ι (W.ι z))) := fun z =>
    (ringKrullDim_stalk_eq_of_etale W.ι z).trans (ringKrullDim_stalk_eq_of_etale V.1.ι (W.ι z))
  refine etaleAt_of_flat_of_unramifiedAt_codimensionOne (W.ι ≫ f₀) x₁ ⟨?_, ?_⟩ ?_ ?_
  · exact finiteTypeAt_of_locallyOfFiniteType (W.ι ≫ f₀) x₁
  · refine Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mpr ?_
    exact (RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff (f.resLEStalkMap hVU x₀)).mpr hqf.2
  · intro hmem
    refine hgen ((ringKrullDim_stalk_eq_zero_iff_mem_genericPoints X x).mp ?_)
    exact (hdimW x₁).symm.trans
      ((ringKrullDim_stalk_eq_zero_iff_mem_genericPoints W.toScheme x₁).mpr hmem)
  · intro z hz hd
    refine (unramifiedAt_comp_ι_iff f₀ W z).mpr ?_
    refine unramifiedAt_resLE_of_unramifiedAt f U.1 V.1 hVU (W.ι z) ?_
    exact hunr (V.1.ι (W.ι z))
      (V.1.ι.base.hom.map_specializes (W.ι.base.hom.map_specializes hz))
      ((hdimW z).symm.trans hd)

end AlgebraicGeometry

end
