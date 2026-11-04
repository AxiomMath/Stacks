module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptySiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace

/-!
# Affine open subspaces of a scheme-like algebraic space

An algebraic space over `S` whose functor of points is representable — a *scheme* — is covered
by the open subspaces cut out by the affine opens of its representing scheme. This file builds
those open subspaces and shows that every point of the space lies in one of them.

## Main definitions

* `AlgebraicGeometry.Space.openSubspaceOfRepr`: the open subspace of a representable presheaf
  cut out by an open of the representing scheme.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_openSubspaceOfRepr` and
  `.isRepresentable_openSubspaceOfRepr`: it is an open subspace, and is a scheme.
* `AlgebraicGeometry.Space.isAffineSpace_openSubspaceOfRepr` and
  `.isQuasiCompactSpace_openSubspaceOfRepr`: for an *affine* open it is an affine algebraic
  space, and in particular quasi-compact.
* `AlgebraicGeometry.Space.exists_affineOpen_mem_openSubspaceOfRepr`: every point of the space
  lies in the open subspace cut out by some affine open.

## Implementation notes

The open subspace is the image subfunctor of
`yoneda (openSiteObject reprX U) ⟶ yoneda reprX ≅ F`.
The first map is an open immersion of presheaves because it is `yoneda` of a morphism of the
site which is an open immersion of schemes
(`AlgebraicGeometry.Space.isOpenImmersion_yoneda_map`, fed by
`AlgebraicGeometry.Space.map_openSiteObjectHom`), and composing with an isomorphism
preserves that; everything else is then
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentableOpenSubspace.lean`, which identifies the
image subfunctor of such a morphism with the representing object.

The last result is the reason the file exists: it supplies the "every point of the limit is
seen by some stage" hypothesis of
`AlgebraicGeometry.Space.exists_eq_top_of_covering_limit` when that is applied to the
schematic loci of the stages of a limit situation. Its proof transports the given point of `F`
to a point of the representing scheme along the homeomorphism of Stacks 03BX (1), chooses an
affine open containing it (`AlgebraicGeometry.iSup_affineOpens_eq_top`), and transports a
preimage of it back; the transport is
`AlgebraicGeometry.Space.schemePointsHomeomorph_symm_toScheme_map`.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Points and isomorphisms -/

/-- The map on points induced by an isomorphism is surjective. -/
alias surjective_pointsMap_of_isIso := AlgebraicGeometry.Space.pointsMap_surjective_of_iso

/-! ### The open subspace cut out by an open of the representing scheme -/

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [F.IsRepresentable]

variable (F) in
/-- The morphism presenting the open subspace of a representable presheaf cut out by an open
of the representing scheme. -/
noncomputable def openSubspaceOfReprHom
    (U : ((BigFppfOver.toScheme B S hS).obj F.reprX).Opens) :
    yoneda.obj (openSiteObject B S hS F.reprX U) ⟶ F :=
  yoneda.map (openSiteObjectHom B S hS F.reprX U) ≫ F.reprW.hom

variable (F) in
/-- The open subspace of a representable presheaf cut out by an open of the representing
scheme. -/
noncomputable def openSubspaceOfRepr
    (U : ((BigFppfOver.toScheme B S hS).obj F.reprX).Opens) : Subfunctor F :=
  Subfunctor.range (openSubspaceOfReprHom B S hS F U)

/-- The presenting morphism is an open immersion of presheaves. -/
theorem isOpenImmersion_openSubspaceOfReprHom
    (U : ((BigFppfOver.toScheme B S hS).obj F.reprX).Opens) :
    IsOpenImmersion B S hS (openSubspaceOfReprHom B S hS F U) := by
  have hUι : _root_.AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι U) := inferInstance
  have hj : IsOpenImmersion B S hS (yoneda.map (openSiteObjectHom B S hS F.reprX U)) :=
    isOpenImmersion_yoneda_map B S hS (openSiteObjectHom B S hS F.reprX U)
      (by rw [map_openSiteObjectHom]; exact hUι)
  exact MorphismProperty.RespectsIso.postcomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
    F.reprW.hom _ hj

/-- The subspace cut out by an open of the representing scheme is an open subspace. -/
theorem isOpenSubspace_openSubspaceOfRepr
    (U : ((BigFppfOver.toScheme B S hS).obj F.reprX).Opens) :
    IsOpenSubspace B S hS (openSubspaceOfRepr B S hS F U) :=
  isOpenSubspace_range_of_isOpenImmersion _ _
    (isOpenImmersion_openSubspaceOfReprHom B S hS U)

/-- The subspace cut out by an open of the representing scheme is a scheme. -/
theorem isRepresentable_openSubspaceOfRepr
    (U : ((BigFppfOver.toScheme B S hS).obj F.reprX).Opens) :
    (openSubspaceOfRepr B S hS F U).toFunctor.IsRepresentable :=
  isRepresentable_range_of_isOpenImmersion _ _
    (isOpenImmersion_openSubspaceOfReprHom B S hS U)

/-- The site object cut out by an affine open of the representing scheme is affine. -/
private theorem isAffine_toScheme_openSiteObject
    (U : ((BigFppfOver.toScheme B S hS).obj F.reprX).affineOpens) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (openSiteObject B S hS F.reprX U.1)) := U.2

/-- The subspace cut out by an *affine* open of the representing scheme is an affine
algebraic space. -/
theorem isAffineSpace_openSubspaceOfRepr
    (U : ((BigFppfOver.toScheme B S hS).obj F.reprX).affineOpens) :
    IsAffineSpace B S hS (openSubspaceOfRepr B S hS F U.1).toFunctor := by
  exact ⟨openSiteObject B S hS F.reprX U.1, isAffine_toScheme_openSiteObject B S hS U,
    ⟨(rangeIsoOfIsOpenImmersion _ (openSubspaceOfReprHom B S hS F U.1)
      (isOpenImmersion_openSubspaceOfReprHom B S hS U.1)).symm⟩⟩

/-- The subspace cut out by an affine open of the representing scheme is quasi-compact. -/
theorem isQuasiCompactSpace_openSubspaceOfRepr
    (U : ((BigFppfOver.toScheme B S hS).obj F.reprX).affineOpens) :
    IsQuasiCompactSpace B S hS (openSubspaceOfRepr B S hS F U.1).toFunctor := by
  exact isQuasiCompactSpace_of_iso B S hS
    (rangeIsoOfIsOpenImmersion _ (openSubspaceOfReprHom B S hS F U.1)
      (isOpenImmersion_openSubspaceOfReprHom B S hS U.1))
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS _
      (isAffine_toScheme_openSiteObject B S hS U))

/-! ### Every point lies in an affine open subspace -/

/-- **Every point of a scheme-like algebraic space lies in an affine open subspace.** For a
representable presheaf `F` and a point `x` of it, there is an affine open `U` of the
representing scheme with `x` in the range of the points of `openSubspaceOfRepr F U`. -/
theorem exists_affineOpen_mem_openSubspaceOfRepr (x : points B S hS F) :
    ∃ U : ((BigFppfOver.toScheme B S hS).obj F.reprX).affineOpens,
      x ∈ Set.range (pointsMap B S hS (openSubspaceOfRepr B S hS F U.1).toFunctor
        (openSubspaceOfRepr B S hS F U.1).ι) := by
  classical
  -- Transport `x` to a point of the representing scheme.
  set x₀ : points B S hS (yoneda.obj F.reprX) :=
    pointsMap B S hS F F.reprW.inv x with hx₀
  set z : (BigFppfOver.toScheme B S hS).obj F.reprX :=
    schemePointsHomeomorph B S hS F.reprX x₀ with hz
  -- Choose an affine open containing it.
  have hmem : z ∈ (⨆ U : ((BigFppfOver.toScheme B S hS).obj F.reprX).affineOpens,
      (U : ((BigFppfOver.toScheme B S hS).obj F.reprX).Opens)) := by
    rw [iSup_affineOpens_eq_top]; trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨U, ?_⟩
  -- A preimage of `z` on the open, as a point of the site object it cuts out.
  have hrange : z ∈ Set.range ((BigFppfOver.toScheme B S hS).map
      (openSiteObjectHom B S hS F.reprX U.1)) := by
    show z ∈ Set.range (Scheme.Opens.ι U.1).base
    rw [Scheme.Opens.range_ι]
    exact hU
  obtain ⟨y, hy⟩ := hrange
  have _ : Mono (openSubspaceOfReprHom B S hS F U.1) :=
    mono_of_presheaf_isOpenImmersion (isOpenImmersion_openSubspaceOfReprHom B S hS U.1)
  -- Pushing that point forward along the presenting morphism returns `x`.
  have hstep : pointsMap B S hS (yoneda.obj (openSiteObject B S hS F.reprX U.1))
      (yoneda.map (openSiteObjectHom B S hS F.reprX U.1))
      ((schemePointsHomeomorph B S hS (openSiteObject B S hS F.reprX U.1)).symm y) = x₀ := by
    rw [← schemePointsHomeomorph_symm_toScheme_map, hy, hz, Homeomorph.symm_apply_apply]
  have hmemrange : x ∈ Set.range (pointsMap B S hS
      (yoneda.obj (openSiteObject B S hS F.reprX U.1))
      (openSubspaceOfReprHom B S hS F U.1)) := by
    refine ⟨(schemePointsHomeomorph B S hS (openSiteObject B S hS F.reprX U.1)).symm y, ?_⟩
    show pointsMap B S hS (yoneda.obj (openSiteObject B S hS F.reprX U.1))
      (yoneda.map (openSiteObjectHom B S hS F.reprX U.1) ≫ F.reprW.hom)
      ((schemePointsHomeomorph B S hS (openSiteObject B S hS F.reprX U.1)).symm y) = x
    rw [pointsMap_comp, Function.comp_apply, hstep, hx₀,
      ← Function.comp_apply (f := pointsMap B S hS (yoneda.obj F.reprX) F.reprW.hom),
      ← pointsMap_comp, F.reprW.inv_hom_id]
    exact pointsMap_id' B S hS F x
  show x ∈ Set.range (pointsMap B S hS
    (Subfunctor.range (openSubspaceOfReprHom B S hS F U.1)).toFunctor
    (Subfunctor.range (openSubspaceOfReprHom B S hS F U.1)).ι)
  rw [range_pointsMap_ι_range]
  exact hmemrange

end AlgebraicGeometry.Space

end
