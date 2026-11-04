module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion

/-!
# The morphism of Hilbert functors induced by a closed immersion (Stacks 0DPF)

Let `π : X ⟶ Y` be a closed immersion of algebraic spaces over an algebraic space `A`, with
structure morphisms `bX : X ⟶ A` and `bY : Y ⟶ A` satisfying `π ≫ bY = bX`. Over a scheme `T`
of the site lying over `A` the base change `π_T : X_T ⟶ Y_T` is again a closed immersion, so a
closed subspace `Z ⊆ X_T` has an image `π_T(Z) ⊆ Y_T`, which is closed and isomorphic to `Z`,
hence of finite presentation, flat and proper over `T` with `Z`. Sending a family to its image
is the morphism of Hilbert functors `Hilb_{X/A} ⟶ Hilb_{Y/A}` of the first sentence of the proof
of Stacks 0DPF.

It is a monomorphism because `π_T` is, and a family `Z ⊆ Y_T` of `Y/A` is in its image exactly
when `Z` is contained in `X_T`, in which case it is the image of its inverse image in `X_T`.

## Main definitions

* `AlgebraicGeometry.Space.hilbertFamilyImageOfClosed` is the image of a family.
* `AlgebraicGeometry.Space.hilbertFamilyPreimageOfClosed` is the inverse image of a family of
  `Y/A` whose closed subspace lands in `X_T`.
* `AlgebraicGeometry.Space.hilbertPresheafMapOfClosed`: **Stacks 0DPF**, the induced morphism of
  Hilbert functors.
* `AlgebraicGeometry.Space.hilbertModelMapOfClosed` is that morphism read in given models of the
  two Hilbert functors.

## Main results

* `AlgebraicGeometry.Space.mono_hilbertModelMapOfClosed`: **Stacks 0DPF**, the induced morphism is
  a monomorphism.
* `AlgebraicGeometry.Space.mem_range_hilbertModelMapOfClosed_iff`: a family of `Y/A` is in the
  image exactly when its closed subspace lands in `X_T`.
* `AlgebraicGeometry.Space.isClosedImmersion_of_isClosedImmersion_range_preimage`: a
  monomorphism of presheaves is a closed immersion as soon as the inverse image of its range
  under every scheme-valued point of the target has a closed immersion as its inclusion.

## Implementation notes

The base change `AlgebraicGeometry.Space.schemeBaseChangeOfMap` and its cartesian squares are
those of an arbitrary morphism over the base. The image of a closed subspace is closed because its
inclusion is a composite of closed immersions, so no separatedness is needed.

Being a closed immersion is a property of a morphism of presheaves of `Type u`, while the Hilbert
functor takes values in `Type (u + 1)`; the morphism is therefore also read in *given* models
(`AlgebraicGeometry.Space.HilbertPresheafModel`) of the two Hilbert functors.

## References

* [Stacks Project, Tag 0DPF](https://stacks.math.columbia.edu/tag/0DPF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Closed immersions with an arbitrary source -/

/-- A closed immersion precomposed with an isomorphism of presheaves is a closed immersion. -/
private theorem isClosedImmersion_comp_of_isIso {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ⟶ G) [IsIso e] (f : G ⟶ H) (hf : IsClosedImmersion B S hS f) :
    IsClosedImmersion B S hS (e ≫ f) := by
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  exact MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) e f hf

/-- **A monomorphism of presheaves is a closed immersion as soon as the inverse image of its
range under every scheme-valued point of the target has a closed immersion as its inclusion.**
The base change of the monomorphism along a scheme-valued point is identified with the inclusion
of that inverse image. -/
theorem isClosedImmersion_of_isClosedImmersion_range_preimage
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) [Mono f]
    (h : ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ G),
      IsClosedImmersion B S hS ((Subfunctor.range f).preimage g).ι) :
    IsClosedImmersion B S hS f := by
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  apply MorphismProperty.presheaf_of_forall_presheaf_pullback_snd
  intro T g
  have _ : Mono (pullback.snd f g) := pullback.snd_of_mono
  have hr : Subfunctor.range (pullback.snd f g) = (Subfunctor.range f).preimage g :=
    Subfunctor.range_eq_preimage_of_isPullback (IsPullback.of_hasPullback f g).flip
  have hι : IsClosedImmersion B S hS (Subfunctor.range (pullback.snd f g)).ι := hr ▸ h T g
  have hcomp := isClosedImmersion_comp_of_isIso (Subfunctor.toRange (pullback.snd f g)) _ hι
  rwa [Subfunctor.toRange_ι] at hcomp

variable {X Y A : AlgebraicSpaces B S hS} {π : X ⟶ Y} {bX : X ⟶ A} {bY : Y ⟶ A}

/-- A property of morphisms of algebraic spaces respecting isomorphisms holds for a morphism
precomposed with an isomorphism of the underlying presheaves as soon as it holds for the
morphism. -/
theorem morphismProperty_homMk_comp_of_isIso
    (P : MorphismProperty (AlgebraicSpaces B S hS)) (hP : P.RespectsIso)
    {V W Z : AlgebraicSpaces B S hS} (e : V.obj ⟶ W.obj) [IsIso e] (g : W.obj ⟶ Z.obj)
    (hg : P (ObjectProperty.homMk g)) :
    P (ObjectProperty.homMk (X := V) (Y := Z) (e ≫ g)) := by
  have := hP
  exact MorphismProperty.RespectsIso.precomp P (ObjectProperty.isoMk _ (asIso e)).hom
    (ObjectProperty.homMk g) hg

/-! ### The base change of a closed immersion over the base -/

section BaseChange

variable (hπ : π ≫ bY = bX) (hclosed : IsClosedImmersion B S hS π.hom)

include hπ hclosed

/-- The base change of a closed immersion over the base is a closed immersion. -/
theorem isClosedImmersion_schemeBaseChangeOfMap (T : SchemesOverPresheaf B S hS A) :
    IsClosedImmersion B S hS (schemeBaseChangeOfMap hπ T) := by
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_schemeBaseChangeOfMap hπ T).flip hclosed

/-- The base change of a closed immersion over the base is a monomorphism. -/
theorem mono_schemeBaseChangeOfMap_of_isClosedImmersion (T : SchemesOverPresheaf B S hS A) :
    Mono (schemeBaseChangeOfMap hπ T) :=
  mono_of_isClosedImmersion B S hS _ (isClosedImmersion_schemeBaseChangeOfMap hπ hclosed T)

end BaseChange

/-! ### The image of a family -/

section Image

variable (hπ : π ≫ bY = bX) (hclosed : IsClosedImmersion B S hS π.hom)

include hπ hclosed

/-- The image of a closed subspace of `X_T` along the base change of a closed immersion is an
algebraic space: the comparison with the image is an isomorphism. -/
theorem isAlgebraicSpace_image_Z_of_isClosedImmersion (T : SchemesOverPresheaf B S hS A)
    (Z : Subfunctor (schemeBaseChange bX T)) (hZ : IsClosedSubspace B S hS Z) :
    IsAlgebraicSpace B S hS (Z.image (schemeBaseChangeOfMap hπ T)).toFunctor := by
  have := mono_schemeBaseChangeOfMap_of_isClosedImmersion hπ hclosed T
  exact hZ.1.of_iso (asIso (Z.toImage (schemeBaseChangeOfMap hπ T)))

/-- The inclusion of the image is the inverse of the comparison with the image followed by the
inclusion of the subspace and the base change of `π`. -/
theorem inv_toImage_comp_of_isClosedImmersion (T : SchemesOverPresheaf B S hS A)
    (Z : Subfunctor (schemeBaseChange bX T)) :
    haveI := mono_schemeBaseChangeOfMap_of_isClosedImmersion hπ hclosed T
    inv (Z.toImage (schemeBaseChangeOfMap hπ T)) ≫ (Z.ι ≫ schemeBaseChangeOfMap hπ T) =
      (Z.image (schemeBaseChangeOfMap hπ T)).ι := by
  rw [← Subfunctor.toImage_ι Z (schemeBaseChangeOfMap hπ T), IsIso.inv_hom_id_assoc]

/-- **The image of a closed subspace of `X_T` along the base change of a closed immersion is a
closed subspace of `Y_T`**: its inclusion is a closed immersion followed by a closed immersion,
up to the isomorphism with the image. -/
theorem isClosedSubspace_image_of_isClosedImmersion (T : SchemesOverPresheaf B S hS A)
    (Z : Subfunctor (schemeBaseChange bX T)) (hZ : IsClosedSubspace B S hS Z) :
    IsClosedSubspace B S hS (Z.image (schemeBaseChangeOfMap hπ T)) := by
  have := mono_schemeBaseChangeOfMap_of_isClosedImmersion hπ hclosed T
  refine ⟨isAlgebraicSpace_image_Z_of_isClosedImmersion hπ hclosed T Z hZ, ?_⟩
  have hcomp : IsClosedImmersion B S hS (Z.ι ≫ schemeBaseChangeOfMap hπ T) :=
    isClosedImmersion_comp B S hS _ _ hZ.2 (isClosedImmersion_schemeBaseChangeOfMap hπ hclosed T)
  have h := isClosedImmersion_comp_of_isIso (inv (Z.toImage (schemeBaseChangeOfMap hπ T))) _ hcomp
  rwa [inv_toImage_comp_of_isClosedImmersion hπ hclosed T Z] at h

/-- The range of the base change of a closed immersion is a closed subspace of `Y_T`. -/
theorem isClosedSubspace_range_schemeBaseChangeOfMap (T : SchemesOverPresheaf B S hS A) :
    IsClosedSubspace B S hS (Subfunctor.range (schemeBaseChangeOfMap hπ T)) := by
  have := mono_schemeBaseChangeOfMap_of_isClosedImmersion hπ hclosed T
  refine ⟨(isAlgebraicSpace_schemeBaseChange bX T).of_iso
    (asIso (Subfunctor.toRange (schemeBaseChangeOfMap hπ T))), ?_⟩
  have h := isClosedImmersion_comp_of_isIso
    (asIso (Subfunctor.toRange (schemeBaseChangeOfMap hπ T))).inv _
    (isClosedImmersion_schemeBaseChangeOfMap hπ hclosed T)
  rwa [inv_toRange_comp] at h

/-- The structure morphism of the image of a family over the test scheme is that of the family,
precomposed with the inverse of the comparison with the image. -/
theorem image_ι_comp_snd_of_isClosedImmersion (T : SchemesOverPresheaf B S hS A)
    (z : HilbertFamily bX T) :
    haveI := mono_schemeBaseChangeOfMap_of_isClosedImmersion hπ hclosed T
    (z.Z.image (schemeBaseChangeOfMap hπ T)).ι ≫ pullback.snd bY.hom T.hom =
      inv (z.Z.toImage (schemeBaseChangeOfMap hπ T)) ≫ (z.Z.ι ≫ pullback.snd bX.hom T.hom) := by
  rw [← inv_toImage_comp_of_isClosedImmersion hπ hclosed T z.Z, Category.assoc, Category.assoc,
    schemeBaseChangeOfMap_snd]

/-- **Stacks 0DPF**, the construction on families: the image of a family of closed subspaces of
`X_T` under the base change of a closed immersion over the base is a family of closed subspaces
of `Y_T`. -/
def hilbertFamilyImageOfClosed (T : SchemesOverPresheaf B S hS A) (z : HilbertFamily bX T) :
    HilbertFamily bY T := by
  have := mono_schemeBaseChangeOfMap_of_isClosedImmersion hπ hclosed T
  have hV := isAlgebraicSpace_image_Z_of_isClosedImmersion hπ hclosed T z.Z z.closed
  refine ⟨z.Z.image (schemeBaseChangeOfMap hπ T),
    isClosedSubspace_image_of_isClosedImmersion hπ hclosed T z.Z z.closed, ?_, ?_, ?_⟩
  · rw [image_ι_comp_snd_of_isClosedImmersion hπ hclosed T z]
    have := isFinitePresentation_isStableUnderBaseChange B S hS
    exact morphismProperty_homMk_comp_of_isIso (V := ⟨_, hV⟩) (W := z.space)
      (Z := schemeOverSpace T)
      (fun ⦃V W : AlgebraicSpaces B S hS⦄ (k : V ⟶ W) => IsFinitePresentation B S hS k.hom)
      MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ z.finitePresentation
  · rw [image_ι_comp_snd_of_isClosedImmersion hπ hclosed T z]
    have := isFlat_isStableUnderBaseChange B S hS
    exact morphismProperty_homMk_comp_of_isIso (V := ⟨_, hV⟩) (W := z.space)
      (Z := schemeOverSpace T)
      (fun ⦃V W : AlgebraicSpaces B S hS⦄ (k : V ⟶ W) => IsFlat B S hS k.hom)
      MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ z.flat
  · rw [image_ι_comp_snd_of_isClosedImmersion hπ hclosed T z]
    have := isProper_isStableUnderBaseChange B S hS
    exact morphismProperty_homMk_comp_of_isIso (V := ⟨_, hV⟩) (W := z.space)
      (Z := schemeOverSpace T)
      (fun ⦃V W : AlgebraicSpaces B S hS⦄ (k : V ⟶ W) => IsProper B S hS k.hom)
      MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ z.proper

/-- The closed subspace of the image of a family is the image of its closed subspace. -/
@[simp]
theorem hilbertFamilyImageOfClosed_Z (T : SchemesOverPresheaf B S hS A)
    (z : HilbertFamily bX T) :
    (hilbertFamilyImageOfClosed hπ hclosed T z).Z = z.Z.image (schemeBaseChangeOfMap hπ T) :=
  rfl

end Image

/-! ### The inverse image of a family landing in the closed subspace -/

section Preimage

variable (hπ : π ≫ bY = bX) (hclosed : IsClosedImmersion B S hS π.hom)

include hπ hclosed

omit hclosed in
/-- The structure morphism of the inverse image of a family over the test scheme is the
comparison with the family followed by the structure morphism of the family. -/
theorem preimage_ι_comp_snd_of_isClosedImmersion (T : SchemesOverPresheaf B S hS A)
    (z : HilbertFamily bY T) :
    (z.Z.preimage (schemeBaseChangeOfMap hπ T)).ι ≫ pullback.snd bX.hom T.hom =
      z.Z.fromPreimage (schemeBaseChangeOfMap hπ T) ≫ (z.Z.ι ≫ pullback.snd bY.hom T.hom) := by
  rw [← Category.assoc, Subfunctor.fromPreimage_ι, Category.assoc, schemeBaseChangeOfMap_snd]

/-- **Stacks 0DPF**, the inverse construction on families: a family of closed subspaces of `Y_T`
whose closed subspace is contained in the image of `X_T` has an inverse image, which is a family
of closed subspaces of `X_T`. -/
def hilbertFamilyPreimageOfClosed (T : SchemesOverPresheaf B S hS A) (z : HilbertFamily bY T)
    (hz : z.Z ≤ Subfunctor.range (schemeBaseChangeOfMap hπ T)) : HilbertFamily bX T := by
  have := mono_schemeBaseChangeOfMap_of_isClosedImmersion hπ hclosed T
  have : IsIso (z.Z.fromPreimage (schemeBaseChangeOfMap hπ T)) :=
    Subfunctor.isIso_fromPreimage_of_le_range z.Z _ hz
  have hc := isClosedSubspace_hilbertFamilyPreimage hπ T z
  refine ⟨z.Z.preimage (schemeBaseChangeOfMap hπ T), hc, ?_, ?_, ?_⟩
  · rw [preimage_ι_comp_snd_of_isClosedImmersion hπ T z]
    have := isFinitePresentation_isStableUnderBaseChange B S hS
    exact morphismProperty_homMk_comp_of_isIso (V := ⟨_, hc.1⟩) (W := z.space)
      (Z := schemeOverSpace T)
      (fun ⦃V W : AlgebraicSpaces B S hS⦄ (k : V ⟶ W) => IsFinitePresentation B S hS k.hom)
      MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ z.finitePresentation
  · rw [preimage_ι_comp_snd_of_isClosedImmersion hπ T z]
    have := isFlat_isStableUnderBaseChange B S hS
    exact morphismProperty_homMk_comp_of_isIso (V := ⟨_, hc.1⟩) (W := z.space)
      (Z := schemeOverSpace T)
      (fun ⦃V W : AlgebraicSpaces B S hS⦄ (k : V ⟶ W) => IsFlat B S hS k.hom)
      MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ z.flat
  · rw [preimage_ι_comp_snd_of_isClosedImmersion hπ T z]
    have := isProper_isStableUnderBaseChange B S hS
    exact morphismProperty_homMk_comp_of_isIso (V := ⟨_, hc.1⟩) (W := z.space)
      (Z := schemeOverSpace T)
      (fun ⦃V W : AlgebraicSpaces B S hS⦄ (k : V ⟶ W) => IsProper B S hS k.hom)
      MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ z.proper

/-- The closed subspace of the inverse image of a family is the inverse image of its closed
subspace. -/
@[simp]
theorem hilbertFamilyPreimageOfClosed_Z (T : SchemesOverPresheaf B S hS A)
    (z : HilbertFamily bY T) (hz : z.Z ≤ Subfunctor.range (schemeBaseChangeOfMap hπ T)) :
    (hilbertFamilyPreimageOfClosed hπ hclosed T z hz).Z =
      z.Z.preimage (schemeBaseChangeOfMap hπ T) := rfl

end Preimage

/-! ### The morphism of Hilbert functors -/

section PresheafMap

variable (hπ : π ≫ bY = bX) (hclosed : IsClosedImmersion B S hS π.hom)

include hπ hclosed

/-- The image of a family over a scheme of the site: the same morphism to the base, and the
image of its closed subspace. -/
def hilbertFamilyOverImageOfClosed (T : BigFppfOver B S hS) (x : HilbertFamilyOver bX T) :
    HilbertFamilyOver bY T where
  toBase := x.toBase
  family := hilbertFamilyImageOfClosed hπ hclosed (CostructuredArrow.mk x.toBase) x.family

/-- The image of a family over a scheme of the site has the same morphism to the base. -/
@[simp]
theorem hilbertFamilyOverImageOfClosed_toBase (T : BigFppfOver B S hS)
    (x : HilbertFamilyOver bX T) :
    (hilbertFamilyOverImageOfClosed hπ hclosed T x).toBase = x.toBase := rfl

/-- The closed subspace of the image of a family over a scheme of the site is the image of its
closed subspace. -/
@[simp]
theorem hilbertFamilyOverImageOfClosed_family_Z (T : BigFppfOver B S hS)
    (x : HilbertFamilyOver bX T) :
    (hilbertFamilyOverImageOfClosed hπ hclosed T x).family.Z =
      x.family.Z.image (schemeBaseChangeOfMap hπ (CostructuredArrow.mk x.toBase)) := rfl

/-- Taking the image of a family commutes with base change: the two base changes of `π` to two
test schemes form a cartesian square, across which image and inverse image of subfunctors
commute. -/
theorem hilbertFamilyOverImageOfClosed_baseChange {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : HilbertFamilyOver bX T) :
    hilbertFamilyOverImageOfClosed hπ hclosed T' (x.baseChange g) =
      (hilbertFamilyOverImageOfClosed hπ hclosed T x).baseChange g :=
  HilbertFamilyOver.ext rfl (heq_of_eq
    (Subfunctor.image_preimage_of_isPullback
      (isPullback_schemeBaseChangeOfMap_comm hπ (HilbertFamilyOver.restrict g x.toBase))
      x.family.Z))

/-- A closed immersion `π : X ⟶ Y` of algebraic spaces over `A` induces a
morphism of Hilbert functors `Hilb_{X/A} ⟶ Hilb_{Y/A}`, sending a family of closed subspaces of
`X_T` to its image in `Y_T`. -/
@[stacks 0DPF "the induced morphism of Hilbert functors"]
def hilbertPresheafMapOfClosed : hilbertPresheaf bX ⟶ hilbertPresheaf bY where
  app T := TypeCat.ofHom fun x => hilbertFamilyOverImageOfClosed hπ hclosed T.unop x
  naturality _ _ g := ConcreteCategory.hom_ext _ _ fun x =>
    hilbertFamilyOverImageOfClosed_baseChange hπ hclosed g.unop x

/-- The induced morphism of Hilbert functors sends a family to its image. -/
@[simp]
theorem hilbertPresheafMapOfClosed_app_apply (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : (hilbertPresheaf bX).obj T) :
    (hilbertPresheafMapOfClosed hπ hclosed).app T x =
      hilbertFamilyOverImageOfClosed hπ hclosed T.unop x := rfl

/-- Taking the image of a family is injective: the base change of `π` is a monomorphism, so
taking the image of a subfunctor along it is injective. -/
theorem hilbertFamilyOverImageOfClosed_injective (T : BigFppfOver B S hS) :
    Function.Injective (hilbertFamilyOverImageOfClosed hπ hclosed T) := by
  rintro ⟨ab, af⟩ ⟨bb, bf⟩ hab
  have hbase := congrArg HilbertFamilyOver.toBase hab
  change ab = bb at hbase
  subst hbase
  have := mono_schemeBaseChangeOfMap_of_isClosedImmersion hπ hclosed (CostructuredArrow.mk ab)
  have hZ : af.Z = bf.Z :=
    Subfunctor.image_injective_of_mono (schemeBaseChangeOfMap hπ (CostructuredArrow.mk ab))
      (eq_of_heq (HilbertFamilyOver.family_Z_heq hab))
  exact HilbertFamilyOver.ext rfl (heq_of_eq hZ)

/-- A family of closed subspaces of `Y_T` is the image of a family of closed subspaces of `X_T`
exactly when its closed subspace is contained in `X_T`. -/
theorem exists_hilbertFamilyOverImageOfClosed_iff (T : BigFppfOver B S hS)
    (y : HilbertFamilyOver bY T) :
    (∃ x, hilbertFamilyOverImageOfClosed hπ hclosed T x = y) ↔
      y.family.Z ≤
        Subfunctor.range (schemeBaseChangeOfMap hπ (CostructuredArrow.mk y.toBase)) := by
  constructor
  · rintro ⟨x, rfl⟩ U a ha
    obtain ⟨b, -, hb⟩ := ha
    exact ⟨b, hb⟩
  · exact fun hy => ⟨⟨y.toBase, hilbertFamilyPreimageOfClosed hπ hclosed
      (CostructuredArrow.mk y.toBase) y.family hy⟩, HilbertFamilyOver.ext rfl
      (heq_of_eq (Subfunctor.image_preimage_eq_of_le_range y.family.Z _ hy))⟩

end PresheafMap

/-! ### Reading the morphism in models of the Hilbert functors -/

section Model

variable (hπ : π ≫ bY = bX) (hclosed : IsClosedImmersion B S hS π.hom)

include hπ hclosed

/-- The morphism of Hilbert functors induced by a closed immersion over the base, read in given
models of the two Hilbert functors. -/
def hilbertModelMapOfClosed (MX : HilbertPresheafModel bX) (MY : HilbertPresheafModel bY) :
    MX.presheaf ⟶ MY.presheaf :=
  MY.mapFrom (MX.iso.hom ≫ hilbertPresheafMapOfClosed hπ hclosed)

/-- The morphism of models is the morphism of Hilbert functors: on a section of the model of
`Hilb_{X/A}` it takes the image of the corresponding family. -/
theorem familyEquiv_hilbertModelMapOfClosed (MX : HilbertPresheafModel bX)
    (MY : HilbertPresheafModel bY) (T : BigFppfOver B S hS)
    (z : MX.presheaf.obj (Opposite.op T)) :
    MY.familyEquiv T ((hilbertModelMapOfClosed hπ hclosed MX MY).app (Opposite.op T) z) =
      hilbertFamilyOverImageOfClosed hπ hclosed T (MX.familyEquiv T z) :=
  types_congr_hom (MY.iso.inv_hom_id_app (Opposite.op T))
    ((MX.iso.hom ≫ hilbertPresheafMapOfClosed hπ hclosed).app (Opposite.op T) (ULift.up z))

/-- The morphism of Hilbert functors induced by a closed immersion over the base is a
monomorphism. -/
@[stacks 0DPF "the induced morphism is a monomorphism"]
theorem mono_hilbertModelMapOfClosed (MX : HilbertPresheafModel bX)
    (MY : HilbertPresheafModel bY) :
    Mono (hilbertModelMapOfClosed hπ hclosed MX MY) := by
  refine (NatTrans.mono_iff_mono_app _).2 fun T => (mono_iff_injective _).2 fun a b hab => ?_
  have h := congrArg (MY.familyEquiv T.unop) hab
  rw [familyEquiv_hilbertModelMapOfClosed, familyEquiv_hilbertModelMapOfClosed] at h
  exact (MX.familyEquiv T.unop).injective
    (hilbertFamilyOverImageOfClosed_injective hπ hclosed T.unop h)

/-- A section of the model of `Hilb_{Y/A}` is in the image of the induced morphism exactly when
the closed subspace of the family it corresponds to is contained in `X_T`. -/
theorem mem_range_hilbertModelMapOfClosed_iff (MX : HilbertPresheafModel bX)
    (MY : HilbertPresheafModel bY) (T : BigFppfOver B S hS)
    (z : MY.presheaf.obj (Opposite.op T)) :
    z ∈ Set.range ((hilbertModelMapOfClosed hπ hclosed MX MY).app (Opposite.op T)) ↔
      (MY.familyEquiv T z).family.Z ≤ Subfunctor.range (schemeBaseChangeOfMap hπ
        (CostructuredArrow.mk (MY.familyEquiv T z).toBase)) := by
  rw [← exists_hilbertFamilyOverImageOfClosed_iff hπ hclosed T (MY.familyEquiv T z)]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨MX.familyEquiv T w, (familyEquiv_hilbertModelMapOfClosed hπ hclosed MX MY T w).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨(MX.familyEquiv T).symm x, ?_⟩
    apply (MY.familyEquiv T).injective
    rw [familyEquiv_hilbertModelMapOfClosed, Equiv.apply_symm_apply, hx]

end Model

end AlgebraicGeometry.Space

end
