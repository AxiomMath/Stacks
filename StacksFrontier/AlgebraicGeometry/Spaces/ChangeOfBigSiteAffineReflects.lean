module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteEnlargement
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine

/-!
# Affineness of a morphism of algebraic spaces reflects along a change of big site

Let `B ⊆ B'` be big fppf sites and `S` a scheme of `B`. A morphism `f : X ⟶ Y` of algebraic
spaces over `S` defined using `B` is affine (Stacks 03WF) as soon as its image under the inverse
image `AlgebraicGeometry.changeBigSite` (Stacks 04W1) is.

## Main results

* `AlgebraicGeometry.isAffineHom_of_isAffineHom_changeBigSite`: affineness reflects along
  `AlgebraicGeometry.changeBigSite`.

## Implementation notes

Given an affine object `Z` of `B` over `S` and a map `g : h_Z ⟶ Y`, the fibre product
`X ×_Y h_Z` is an algebraic space, and the inverse image carries its cartesian square to a
cartesian square (`AlgebraicGeometry.isPullback_hom_map_fibreProduct_changeBigSite`). The inverse
image of `h_Z` is `h_Z` read in `B'` (`AlgebraicGeometry.changeBigSiteYonedaIso`), so the
hypothesis represents the inverse image of `X ×_Y h_Z` by an affine object of `B'`. An algebraic
space whose inverse image is representable is representable
(`AlgebraicGeometry.isRepresentable_of_isRepresentable_changeBigSite`), and its representing
object has the same underlying scheme as the affine object above, by Yoneda; so it is affine.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- **Affineness reflects along enlarging the big fppf site.** A morphism of algebraic spaces
over `S` is affine as soon as its inverse image on the enlarged big fppf site is. -/
theorem isAffineHom_of_isAffineHom_changeBigSite {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : Space.IsAffineHom B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).map f).hom) :
    Space.IsAffineHom B S hS f.hom := by
  intro Z g
  let hS' : B'.Contains S := largerContains h hS
  let F := changeBigSite B B' h S hS
  let i := inclusionOver h S hS
  let Zo : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj Z
  let gA : (schemeSpaceFunctor B S hS).obj Zo ⟶ Y := ObjectProperty.homMk g
  let P := AlgebraicSpaces.fiberProduct B S hS f gA
  let Z' : BigAffineFppf B' S hS' := ⟨i.obj Zo, Z.property⟩
  let eZ := changeBigSiteYonedaIso B B' h S hS Zo
  let g' : yoneda.obj ((BigAffineFppf.inclusion B' S hS').obj Z') ⟶ (F.obj Y).obj :=
    eZ.hom ≫ (F.map gA).hom
  obtain ⟨W', p', q', hW'⟩ := hf Z' g'
  have sq' : IsPullback
      (F.map (ObjectProperty.homMk (pullback.fst f.hom gA.hom) : P ⟶ X)).hom
      ((F.map (ObjectProperty.homMk (pullback.snd f.hom gA.hom) : P ⟶ _)).hom ≫ eZ.inv)
      (F.map f).hom g' :=
    (isPullback_hom_map_fibreProduct_changeBigSite B B' h S hS f gA).of_iso (Iso.refl _)
      (Iso.refl _) eZ.symm (Iso.refl _) rfl ((Category.id_comp _).symm) rfl
      (Iso.inv_hom_id_assoc eZ _).symm
  let e : (F.obj P).obj ≅ yoneda.obj ((BigAffineFppf.inclusion B' S hS').obj W') :=
    sq'.isoIsPullback _ _ hW'
  have hrep : P.obj.IsRepresentable :=
    isRepresentable_of_isRepresentable_changeBigSite B B' h S hS P
      (Functor.IsRepresentable.mk' e.symm)
  let T : BigFppfOver B S hS := P.obj.reprX
  let eT : yoneda.obj T ≅ P.obj := P.obj.reprW
  let eP : (schemeSpaceFunctor B S hS).obj T ≅ P := ObjectProperty.isoMk _ eT
  let eY : yoneda.obj (i.obj T) ≅ yoneda.obj ((BigAffineFppf.inclusion B' S hS').obj W') :=
    changeBigSiteYonedaIso B B' h S hS T ≪≫
      (ObjectProperty.ι (fun G => IsAlgebraicSpace B' S hS' G)).mapIso (F.mapIso eP) ≪≫ e
  let eTW : i.obj T ≅ (BigAffineFppf.inclusion B' S hS').obj W' :=
    Yoneda.fullyFaithful.preimageIso eY
  have hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
    @IsAffine.of_isIso _ _ ((BigFppfOver.toScheme B' S hS').mapIso eTW).hom (Iso.isIso_hom _)
      W'.property
  let W : BigAffineFppf B S hS := ⟨T, hTaff⟩
  refine ⟨W, eT.hom ≫ pullback.fst f.hom g,
    Yoneda.fullyFaithful.preimage (eT.hom ≫ pullback.snd f.hom g), ?_⟩
  refine (IsPullback.of_hasPullback f.hom g).of_iso eT.symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Iso.inv_hom_id_assoc eT _).symm ?_ (by simp) (by simp)
  rw [Yoneda.fullyFaithful.map_preimage]
  exact (Iso.inv_hom_id_assoc eT _).symm

end AlgebraicGeometry

end
