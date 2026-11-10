module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.IntersectionEmbedding
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SectionsRingOnSubsetFunctorial

/-!
# Functoriality of the restriction of a scheme to a subset, and naturality of Stacks 0API

`AlgebraicGeometry.subsetLocallyRingedSpace` restricts a locally ringed space to an arbitrary
subset, and `AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap` makes its ring of global sections
contravariantly functorial in the scheme. This file upgrades that to functoriality of the
restricted *space*: a morphism of schemes `g : X ⟶ Y` and subsets `E ⊆ Y`, `E' ⊆ X` with
`E' ⊆ g⁻¹(E)` induce a morphism of locally ringed spaces `(E', 𝒪_X|_{E'}) ⟶ (E, 𝒪_Y|_E)` whose
map on global sections is the induced map on sections over a subset.

Consequently the canonical embedding `j` of
[Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API) — the unit
`AlgebraicGeometry.LocallyRingedSpace.toΓSpec` of the `Γ`–`Spec` adjunction read at the
restricted space — is *natural*: the square relating `j` for `E'` to `j` for `E` along `g` commutes,
both as morphisms of locally ringed spaces and on points. That naturality is the compatibility of
`j` with the projections which step 5 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) reads off its commutative diagram;
the implementation notes of `StacksFrontier.AlgebraicGeometry.Descent.IntersectionOpenImage` record
that it was previously unavailable.

## Main definitions

* `AlgebraicGeometry.subsetPresheafedSpaceMap` is the induced morphism of presheafed spaces: on
  spaces the restriction `AlgebraicGeometry.subsetBaseMap` of `g`, on sheaves the adjoint map
  `AlgebraicGeometry.inverseImageSheafMap` whose value at `⊤` is
  `AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap`.
* `AlgebraicGeometry.subsetLocallyRingedSpaceMap` is the same morphism as a morphism of locally
  ringed spaces.

## Main results

* `AlgebraicGeometry.isLocalHom_stalkMap_subsetPresheafedSpaceMap` : the induced morphism of
  restrictions is local on stalks. This is what makes
  `AlgebraicGeometry.subsetLocallyRingedSpaceMap` a morphism of *locally* ringed spaces.
* `AlgebraicGeometry.subsetLocallyRingedSpaceMap_comp_toΓSpec` : **naturality of the canonical
  embedding of Stacks 0API**, as morphisms of locally ringed spaces.
* `AlgebraicGeometry.toΓSpec_base_sectionsRingOnSubsetMap` : the same naturality on points, which
  is the form in which a statement about images and preimages of subsets of `Spec` consumes it.

## Implementation notes

*Where the stalk comparison comes from.* The locality of the induced morphism on stalks is read
off the commutative square `AlgebraicGeometry.subsetPresheafedSpaceMap_comp_ofSubset` together
with the fact that the two vertical maps `AlgebraicGeometry.ofSubset` are isomorphisms on stalks.
That fact is `AlgebraicGeometry.isIso_ofSubset_stalkMap`, proved alongside the restriction itself
in `StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.IntersectionEmbedding`.

*Why locality is not checked directly.* The stalk of the restricted structure sheaf is the stalk
of a sheafification of a left Kan extension, so there is no formula for one of its elements; the
only available handle is the stalk map of `AlgebraicGeometry.ofSubset`, which is why the argument
goes through surjectivity of that map on one side and locality of its inverse on the other rather
than through a computation with germs of sections of the restriction.

*Naturality is the unit of an adjunction.* Once the morphism of locally ringed spaces exists,
naturality of `j` is `AlgebraicGeometry.identityToΓSpec.naturality`, since `Γ` of the induced
morphism is `AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap` by construction — the latter is the
value at `⊤` of the sheaf map used as the sheaf component.

No tag is placed. Tag 0API is carried by
`AlgebraicGeometry.exists_iInter_iso_iInter_in_specΓ` and
`AlgebraicGeometry.isOpen_image_toΓSpec_of_isOpen`; naturality of the construction is a property
of the unit of the `Γ`–`Spec` adjunction and not one of the assertions of that tag.

## References

* [Stacks Project, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The morphism of presheafed spaces between the restrictions to subsets induced by a morphism
of schemes `g : X ⟶ Y` and subsets `E ⊆ Y`, `E' ⊆ X` with `E' ⊆ g⁻¹(E)`: on spaces the
restriction `AlgebraicGeometry.subsetBaseMap` of `g`, on sheaves the map
`AlgebraicGeometry.inverseImageSheafMap` whose value at `⊤` is
`AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap`. -/
def subsetPresheafedSpaceMap {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Set Y) (E' : Set X)
    (h : E' ⊆ g.base ⁻¹' E) :
    (subsetLocallyRingedSpace X.toLocallyRingedSpace E').toPresheafedSpace ⟶
      (subsetLocallyRingedSpace Y.toLocallyRingedSpace E).toPresheafedSpace where
  base := subsetBaseMap g E E' h
  c := (inverseImageSheafMap g E E' h).hom

/-- The induced morphism of restrictions commutes with the canonical morphisms to the ambient
spaces. This is the defining property of `AlgebraicGeometry.inverseImageSheafMap` read as a
square of presheafed spaces. -/
lemma subsetPresheafedSpaceMap_comp_ofSubset {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Set Y)
    (E' : Set X) (h : E' ⊆ g.base ⁻¹' E) :
    subsetPresheafedSpaceMap g E E' h ≫ ofSubset Y.toLocallyRingedSpace E =
      ofSubset X.toLocallyRingedSpace E' ≫ g.toLRSHom.toHom := by
  refine PresheafedSpace.ext _ _ rfl ?_
  change (subsetPresheafedSpaceMap g E E' h ≫ ofSubset Y.toLocallyRingedSpace E).c ≫
      Functor.whiskerRight (𝟙 _) _ = _
  rw [Functor.whiskerRight_id']
  exact (Category.comp_id _).trans (congrArg (fun z : Y.toSheafedSpace.sheaf ⟶ _ => z.hom)
    (unit_comp_inverseImageSheafMap g E E' h))

/-- The square of stalk maps obtained from
`AlgebraicGeometry.subsetPresheafedSpaceMap_comp_ofSubset`: through the stalk maps of the two
canonical morphisms to the ambient spaces, the stalk map of the induced morphism of restrictions
is the stalk map of `g`. -/
lemma stalkMap_subsetPresheafedSpaceMap {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Set Y)
    (E' : Set X) (h : E' ⊆ g.base ⁻¹' E) (x : E') :
    (ofSubset Y.toLocallyRingedSpace E).stalkMap ((subsetPresheafedSpaceMap g E E' h).base x) ≫
        (subsetPresheafedSpaceMap g E E' h).stalkMap x =
      g.toLRSHom.toHom.stalkMap x.1 ≫ (ofSubset X.toLocallyRingedSpace E').stalkMap x := by
  have H1 := PresheafedSpace.stalkMap.comp (subsetPresheafedSpaceMap g E E' h)
    (ofSubset Y.toLocallyRingedSpace E) x
  have H2 := PresheafedSpace.stalkMap.comp (ofSubset X.toLocallyRingedSpace E')
    g.toLRSHom.toHom x
  have H := PresheafedSpace.stalkMap.congr_hom _ _
    (subsetPresheafedSpaceMap_comp_ofSubset g E E' h) x
  refine H1.symm.trans (H.trans ?_)
  change (𝟙 _ : _ ⟶ _) ≫ _ = _
  exact (Category.id_comp _).trans H2

/-- **The induced morphism of restrictions is local on stalks.** Its stalk map is, through the
isomorphisms `AlgebraicGeometry.isIso_ofSubset_stalkMap`, the stalk map of `g`, which is local
because `g` is a morphism of schemes. -/
lemma isLocalHom_stalkMap_subsetPresheafedSpaceMap {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Set Y)
    (E' : Set X) (h : E' ⊆ g.base ⁻¹' E) (x : E') :
    IsLocalHom ((subsetPresheafedSpaceMap g E E' h).stalkMap x).hom := by
  have hY := isIso_ofSubset_stalkMap Y.toLocallyRingedSpace E
    ((subsetPresheafedSpaceMap g E E' h).base x)
  have hX := isIso_ofSubset_stalkMap X.toLocallyRingedSpace E' x
  have hsurj := (ConcreteCategory.bijective_of_isIso
    ((ofSubset Y.toLocallyRingedSpace E).stalkMap
      ((subsetPresheafedSpaceMap g E E' h).base x))).2
  have hlocX := isLocalHom_of_isIso ((ofSubset X.toLocallyRingedSpace E').stalkMap x)
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := hsurj a
  have key : ((subsetPresheafedSpaceMap g E E' h).stalkMap x).hom
        ((((ofSubset Y.toLocallyRingedSpace E).stalkMap
          ((subsetPresheafedSpaceMap g E E' h).base x)).hom) b) =
      (((ofSubset X.toLocallyRingedSpace E').stalkMap x).hom)
        (((g.toLRSHom.toHom.stalkMap x.1).hom) b) :=
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (stalkMap_subsetPresheafedSpaceMap g E E' h x)) b
  rw [key] at ha
  have h1 : IsUnit (((g.toLRSHom.toHom.stalkMap x.1).hom) b) := hlocX.1 _ ha
  have h2 : IsUnit b :=
    (LocallyRingedSpace.isLocalHomStalkMap g.toLRSHom x.1).1 _ h1
  exact h2.map ((ofSubset Y.toLocallyRingedSpace E).stalkMap
    ((subsetPresheafedSpaceMap g E E' h).base x)).hom

/-- **Functoriality of the restriction of a scheme to a subset.** A morphism of schemes
`g : X ⟶ Y` and subsets `E ⊆ Y`, `E' ⊆ X` with `E' ⊆ g⁻¹(E)` induce a morphism of locally ringed
spaces `(E', 𝒪_X|_{E'}) ⟶ (E, 𝒪_Y|_E)`, whose map on global sections is
`AlgebraicGeometry.Scheme.sectionsRingOnSubsetMap`. -/
def subsetLocallyRingedSpaceMap {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Set Y) (E' : Set X)
    (h : E' ⊆ g.base ⁻¹' E) :
    subsetLocallyRingedSpace X.toLocallyRingedSpace E' ⟶
      subsetLocallyRingedSpace Y.toLocallyRingedSpace E :=
  ⟨subsetPresheafedSpaceMap g E E' h,
    fun x => isLocalHom_stalkMap_subsetPresheafedSpaceMap g E E' h x⟩

/-- **Naturality of the canonical embedding of
[Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API).** The embedding
`j : (E, 𝒪_Y|_E) ⟶ Spec Γ(E, 𝒪_Y|_E)` commutes with the morphisms induced by a morphism of
schemes `g : X ⟶ Y` carrying `E'` into `E`. -/
lemma subsetLocallyRingedSpaceMap_comp_toΓSpec {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Set Y)
    (E' : Set X) (h : E' ⊆ g.base ⁻¹' E) :
    subsetLocallyRingedSpaceMap g E E' h ≫
        (subsetLocallyRingedSpace Y.toLocallyRingedSpace E).toΓSpec =
      (subsetLocallyRingedSpace X.toLocallyRingedSpace E').toΓSpec ≫
        Spec.locallyRingedSpaceMap (Scheme.sectionsRingOnSubsetMap g E E' h) :=
  identityToΓSpec.naturality (subsetLocallyRingedSpaceMap g E E' h)

/-- **Naturality of the canonical embedding of
[Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API) on points.** The image under `j` of
a point of `E'` pushed into `Spec Γ(E, 𝒪_Y|_E)` along the induced map on sections is the image
under `j` of the point of `E` it maps to. -/
theorem toΓSpec_base_sectionsRingOnSubsetMap {X Y : Scheme.{u}} (g : X ⟶ Y) (E : Set Y)
    (E' : Set X) (h : E' ⊆ g.base ⁻¹' E) (x : E') :
    (Spec.map (Scheme.sectionsRingOnSubsetMap g E E' h)).base
        ((subsetLocallyRingedSpace X.toLocallyRingedSpace E').toΓSpec.base x) =
      (subsetLocallyRingedSpace Y.toLocallyRingedSpace E).toΓSpec.base ⟨g.base x.1, h x.2⟩ :=
  (congrArg
    (fun m : subsetLocallyRingedSpace X.toLocallyRingedSpace E' ⟶
        Spec.toLocallyRingedSpace.obj
          (op (LocallyRingedSpace.Γ.obj
            (op (subsetLocallyRingedSpace Y.toLocallyRingedSpace E)))) => m.base x)
    (subsetLocallyRingedSpaceMap_comp_toΓSpec g E E' h)).symm

end AlgebraicGeometry

end

end
