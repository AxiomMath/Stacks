module

public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace

/-!
# An open subspace of a representable algebraic space is representable

An algebraic space over `S` which is representable by an object of the big fppf site is a
scheme in the site, and an open subspace of it is an open subscheme, hence again an object of
the site. This file proves that, in the two forms in which it is met: for a subspace of a
presheaf which is literally `yoneda.obj V`, and for a subspace of a presheaf which is only
assumed representable.

The correspondence between open subspaces of `yoneda.obj V` and opens of the representing
scheme is already available: `AlgebraicGeometry.Space.subspaceOfOpens` cuts a subspace out of
an open of the scheme, `AlgebraicGeometry.Space.eq_of_image_pointsToScheme_eq` says an open
subspace of `yoneda.obj V` is determined by its set of scheme points, and
`AlgebraicGeometry.Space.range_yoneda_map_eq_subspaceOfOpens` identifies the image of an open
immersion of the site with the subspace of its image open. What is added here is the resulting
representability, and its transport along a representing isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.opensOfOpenSubspace`: the open of the representing scheme attached
  to an open subspace of `yoneda.obj V`, namely the image of its set of points.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_subspaceOfOpens`: the open subspace of
  `yoneda.obj V` cut out by an open of the representing scheme is representable — by the open
  subscheme `AlgebraicGeometry.BigFppfOver.openSubObj`.
* `AlgebraicGeometry.Space.subspaceOfOpens_opensOfOpenSubspace`: every open subspace of
  `yoneda.obj V` is cut out by an open of the representing scheme.
* `AlgebraicGeometry.Space.isRepresentable_of_isOpenSubspace_yoneda`: an open subspace of
  `yoneda.obj V` is representable.
* `AlgebraicGeometry.Space.isRepresentable_of_isOpenSubspace`: an open subspace of a
  representable presheaf is representable.
* `AlgebraicGeometry.Space.exists_openImmersion_of_isOpenImmersion_ι` and
  `AlgebraicGeometry.Space.exists_openImmersion_of_isOpenSubspace`: the representability in the
  form its consumers use — an open immersion of site objects `V ⟶ U` together with an
  isomorphism of `yoneda.obj V` with the subspace over `yoneda.obj U`, so that a section of the
  subspace is a morphism factoring through `V`.

## What is and is not proved

No declaration here carries a Stacks attribute. The correspondence of Stacks 03BZ between open
subspaces and open point sets is already carried by
`AlgebraicGeometry.Space.openSubspacesOrderIso` and, for a chart, by
`AlgebraicGeometry.Space.isOpenSubspace_subspaceOfOpens`; the containment of an open subscheme
of an object of the site in the site is `AlgebraicGeometry.BigFppfOver.contains_opens`, that is
Stacks 000R (2). The statements proved here are the unlabelled combination of the two.

Nothing is said about *quasi-compactness* of the open subspace, which is false in general, nor
about the subspace being an algebraic space, which is part of the hypothesis
`AlgebraicGeometry.Space.IsOpenSubspace`.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The open subspace of a chart cut out by an open of the representing scheme is
representable.** It is the image of the open immersion
`AlgebraicGeometry.BigFppfOver.openSubHom` of the open subscheme, and the image of a
representable open immersion is representable by
`AlgebraicGeometry.Space.isRepresentable_range_of_isOpenImmersion`. -/
theorem isRepresentable_subspaceOfOpens (V : BigFppfOver B S hS)
    (Q : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    (subspaceOfOpens B S hS V Q).toFunctor.IsRepresentable := by
  have hoi : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (BigFppfOver.openSubHom B S hS V Q)) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion Q.ι)
  have hpre : IsOpenImmersion B S hS
      (yoneda.map (BigFppfOver.openSubHom B S hS V Q)) :=
    (presheaf_yoneda_map_iff B S hS inferInstance _).2 hoi
  have hrep := isRepresentable_range_of_isOpenImmersion
    (BigFppfOver.openSubObj B S hS V Q) _ hpre
  rwa [range_yoneda_map_eq_subspaceOfOpens B S hS
    (BigFppfOver.openSubHom B S hS V Q) hoi Q Q.range_ι] at hrep

/-- The open of the representing scheme attached to an open subspace of `yoneda.obj V`: the
image of its set of points under the comparison
`AlgebraicGeometry.Space.pointsToScheme`, which is open by
`AlgebraicGeometry.Space.isOpen_pointTopology_yoneda_iff_isOpen_image`. -/
def opensOfOpenSubspace (V : BigFppfOver B S hS) (A : Subfunctor (yoneda.obj V))
    (hA : IsOpenSubspace B S hS A) : ((BigFppfOver.toScheme B S hS).obj V).Opens where
  carrier := pointsToScheme B S hS V '' Set.range (pointsMap B S hS A.toFunctor A.ι)
  is_open' := by
    rw [← isOpen_pointTopology_yoneda_iff_isOpen_image]
    exact isOpen_range_pointsMap_of_isOpenImmersion B S hS A.ι hA.2

/-- **Every open subspace of a chart is cut out by an open of the representing scheme.** The
two open subspaces have the same set of scheme points, so
`AlgebraicGeometry.Space.eq_of_image_pointsToScheme_eq` identifies them. -/
theorem subspaceOfOpens_opensOfOpenSubspace (V : BigFppfOver B S hS)
    (A : Subfunctor (yoneda.obj V)) (hA : IsOpenSubspace B S hS A) :
    subspaceOfOpens B S hS V (opensOfOpenSubspace B S hS V A hA) = A := by
  refine eq_of_image_pointsToScheme_eq B S hS
    (isOpenSubspace_subspaceOfOpens B S hS V _) hA ?_
  rw [range_pointsMap_subspaceOfOpens,
    Set.image_preimage_eq _ (surjective_pointsToScheme B S hS V)]
  rfl

/-- **An open subspace of a chart is representable.** It is cut out by an open of the
representing scheme by
`AlgebraicGeometry.Space.subspaceOfOpens_opensOfOpenSubspace`, and such a subspace is
representable by `AlgebraicGeometry.Space.isRepresentable_subspaceOfOpens`. -/
theorem isRepresentable_of_isOpenSubspace_yoneda (V : BigFppfOver B S hS)
    (A : Subfunctor (yoneda.obj V)) (hA : IsOpenSubspace B S hS A) :
    A.toFunctor.IsRepresentable := by
  have hrep := isRepresentable_subspaceOfOpens B S hS V (opensOfOpenSubspace B S hS V A hA)
  rwa [subspaceOfOpens_opensOfOpenSubspace B S hS V A hA] at hrep

/-- **An open subspace of a representable algebraic space over `S` is representable.** Transport
the subspace along a representing isomorphism `r : yoneda.obj V ≅ F`: its inverse image is an
open subspace of the chart, hence representable by
`AlgebraicGeometry.Space.isRepresentable_of_isOpenSubspace_yoneda`, and its image under `r` is
the subspace one started from, because `r` is bijective on points.

This is what puts the open subspaces cut out of a fibre power of an étale chart — the
complement of the diagonals of Stacks 089J among them — back into the big fppf site. -/
theorem isRepresentable_of_isOpenSubspace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : F.IsRepresentable) (A : Subfunctor F) (hA : IsOpenSubspace B S hS A) :
    A.toFunctor.IsRepresentable := by
  have _ := hF
  have hFs : IsAlgebraicSpace B S hS F :=
    (isAlgebraicSpace_yoneda B S hS F.reprX).of_iso F.reprW
  have hr : IsOpenImmersion B S hS F.reprW.hom := isOpenImmersion_of_isIso B S hS _
  have hA' : IsOpenSubspace B S hS (A.preimage F.reprW.hom) :=
    isOpenSubspace_preimage B S hS _ _ hFs (isAlgebraicSpace_yoneda B S hS F.reprX) hA
  have hA'rep : (A.preimage F.reprW.hom).toFunctor.IsRepresentable :=
    isRepresentable_of_isOpenSubspace_yoneda B S hS F.reprX _ hA'
  have hkey := isRepresentable_openSubspaceOfPoints_range_comp_of_isOpenImmersion
    B S hS hr hA' hA'rep
  have hsets : Set.range (pointsMap B S hS (A.preimage F.reprW.hom).toFunctor
        ((A.preimage F.reprW.hom).ι ≫ F.reprW.hom)) =
      Set.range (pointsMap B S hS A.toFunctor A.ι) := by
    rw [pointsMap_comp, Set.range_comp, pointsRange_preimage,
      Set.image_preimage_eq _ (bijective_pointsMap_of_isIso B S hS F.reprW.hom).2]
  have hfix : openSubspaceOfPoints B S hS F
      (Set.range (pointsMap B S hS A.toFunctor A.ι)) = A := by
    have hopen : IsOpen (Set.range (pointsMap B S hS A.toFunctor A.ι)) :=
      isOpen_range_pointsMap_of_isOpenImmersion B S hS A.ι hA.2
    have hcut := isOpenSubspace_openSubspaceOfPoints B S hS hFs _ hopen
    have hrange := range_pointsMap_ι_openSubspaceOfPoints B S hS (F := F)
      (Set.range (pointsMap B S hS A.toFunctor A.ι))
    exact le_antisymm (le_of_range_pointsMap_ι_subset B S hS hA hrange.le)
      (le_of_range_pointsMap_ι_subset B S hS hcut hrange.ge)
  rw [hsets, hfix] at hkey
  exact hkey

/-- **An open subspace of a presheaf isomorphic to a chart is cut out by an open immersion of
site objects.**  Its sections over a test object are therefore the morphisms to the representing
object which factor through that open immersion.

The open immersion is not constructed: it is the represented base change of the inclusion
`A.ι` along the isomorphism, which relative representability supplies.  What has to be seen is
that this base change is *all* of `A`, and that is because the morphism base-changed along is an
isomorphism, so the base change is one as well. -/
theorem exists_openImmersion_of_isOpenImmersion_ι
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (A : Subfunctor F)
    (hA : IsOpenImmersion B S hS A.ι) {U : BigFppfOver B S hS} (r : yoneda.obj U ≅ F) :
    ∃ (V : BigFppfOver B S hS) (j : V ⟶ U) (e : yoneda.obj V ≅ A.toFunctor),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      e.hom ≫ A.ι = yoneda.map j ≫ r.hom := by
  have h := hA.rep.isPullback r.hom
  have _ : IsIso (hA.rep.fst r.hom) := h.isIso_fst_of_isIso
  exact ⟨hA.rep.pullback r.hom, hA.rep.snd r.hom, asIso (hA.rep.fst r.hom),
    hA.property_snd r.hom, h.w⟩

/-- **An open subspace of a chart is cut out by an open immersion of site objects.** -/
theorem exists_openImmersion_of_isOpenSubspace (U : BigFppfOver B S hS)
    (A : Subfunctor (yoneda.obj U)) (hA : IsOpenSubspace B S hS A) :
    ∃ (V : BigFppfOver B S hS) (j : V ⟶ U) (e : yoneda.obj V ≅ A.toFunctor),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      e.hom ≫ A.ι = yoneda.map j := by
  obtain ⟨V, j, e, hj, he⟩ :=
    exists_openImmersion_of_isOpenImmersion_ι B S hS A hA.2 (Iso.refl (yoneda.obj U))
  exact ⟨V, j, e, hj, by simpa using he⟩

end AlgebraicGeometry.Space

end
