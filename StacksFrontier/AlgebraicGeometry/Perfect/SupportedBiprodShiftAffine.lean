module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedBiprodShiftLift

/-!
# Lifting a supported perfect object off a quasi-compact open of a general affine scheme

[Stacks, Tag 08EK] is proved at `X = Spec A`. Its consumer, the two-open step of
[Stacks, Tag 09IM], applies it at an *affine open* of a general scheme, so it is wanted at any
space isomorphic to `Spec A` rather than at `Spec A` itself. This module transports it along
such an isomorphism, and reads the result off at an affine scheme through
`AlgebraicGeometry.Scheme.isoSpec`.

Let `e : X ≅ Y` be an isomorphism of ringed spaces and `U` an open of `X`. The image of `U`
in `Y` is the preimage of `U` under the inverse, and the open subspaces `X|_U` and `Y|_{e(U)}`
are isomorphic: both present the same open of `Y` through an open immersion, so
`PresheafedSpace.IsOpenImmersion.isoOfRangeEq` identifies them. Everything else follows from
that isomorphism and its compatibility with the two inclusions into `Y`: perfectness and
cohomological support transport by the derived pullback along an isomorphism, and restriction
to `U` of a derived pullback along `e` is the derived pullback of the restriction to `e(U)`,
by the composition isomorphism of [Stacks, Tag 0D5S] applied to the compatibility square.

## Main definitions and results

* `Stacks.Perfect.SupportedBiprodShiftAffine.imageOpenOfIso`: the image of an open of `X` in
  `Y`, written as the preimage under `e.inv`.
* `Stacks.Perfect.SupportedBiprodShiftAffine.restrictIsoOfIso`: **the isomorphism of open
  subspaces `X|_U ≅ Y|_{e(U)}`** induced by `e`, with
  `Stacks.Perfect.SupportedBiprodShiftAffine.restrictIsoOfIso_hom_comp_ofRestrict` and
  `Stacks.Perfect.SupportedBiprodShiftAffine.restrictIsoOfIso_inv_comp_ofRestrict` its
  compatibility with the inclusions of `U` and of `e(U)`.
* `Stacks.Perfect.SupportedBiprodShiftAffine.derivedRestrictModulesObjIsoOfIso`: restricting a
  derived pullback along `e` to `U` is the derived pullback, along `X|_U ≅ Y|_{e(U)}`, of the
  restriction to `e(U)`.
* `Stacks.Perfect.SupportedBiprodShiftAffine.biprodShiftIsoOfObjIso`: for an additive,
  shift-commuting `H` and an isomorphism `H G ≅ Z`, an isomorphism `H (G ⊕ G[1]) ≅ Z ⊕ Z[1]`.
* `exists_isPerfect_supported_biprod_shift_iso_restrict_of_isoSpec`, in this namespace:
  **[Stacks, Tag 08EK] at any ringed space isomorphic to `Spec A`.**
* `exists_isPerfect_supported_biprod_shift_iso_restrict_of_isAffine`, in this namespace: the
  same at an affine scheme. For an affine open `V` of a general scheme this is applied at
  `V.toScheme`, which is affine by `AlgebraicGeometry.IsAffineOpen.isAffine_toScheme`.

The registration of [Stacks, Tag 08EK] is on another declaration, so no tag
attribute is placed here.

## Implementation notes

**One functor rather than two.** The last step — that the derived pullback along `X|_U ≅ Y|_{e(U)}`
distributes over `G ⊕ G[1]` — is
`Stacks.Perfect.SupportedBiprodShift.biprodShiftIsoOfFunctorIso` with the second functor the
identity. Passing the identity functor at the application site fails: the additivity and the
shift-commutation of `𝟭 C` are then demanded while the `Preadditive C` and `HasShift C ℤ`
arguments of that lemma are still unassigned metavariables, and instance search reports a
failure that no reordering of the arguments at the geometry repairs. Inside
`Stacks.Perfect.SupportedBiprodShiftAffine.biprodShiftIsoOfObjIso` those arguments are
hypotheses, so the two instances are found; both resolve on their own at the concrete category,
which is how the diagnosis was made.

**Why the open subspace isomorphism is built rather than taken from the restricted morphism.**
`AlgebraicGeometry.RingedSpace.restrictHom e.hom V` is the morphism `X|_{e⁻¹V} ⟶ Y|_V`, and its
compatibility square is
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism_comp_openSubspaceInclusion`; but nothing
records that it is an isomorphism when `e` is, and `Stacks.Cohomology.TransportAlongIso`'s
transports of perfectness need an isomorphism of ringed spaces. Building the isomorphism from
`PresheafedSpace.IsOpenImmersion.isoOfRangeEq`, as
`Stacks.Cohomology.ClosedSupportPerfect.nestedOpenToAmbientIso` does for a nested open, gives
the compatibility square at the same time, from
`PresheafedSpace.IsOpenImmersion.lift_fac`.

For the same reason the comparison of restriction with derived pullback is rebuilt here at an
isomorphism rather than taken from
`Stacks.Cohomology.DerivedRestrictionPullback.derivedRestrictPullbackIso`, which is the same
square for an arbitrary morphism but has `f|_{f⁻¹V}` where this needs an isomorphism, so neither
`Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_iff` nor
`Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackInvHomIso` applies to it. The
relationship between the two is the one
`Stacks.Perfect.SupportedBiprodShift.derivedRestrictNestedObjIso` already stands in for a nested
open.

**`HasDerivedCategory.standard`** is a local instance at priority `10000`, as in
[Stacks, Tag 08EK]'s own module: without the priority a different derived-category model is
selected and `Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_iff` is then stated
about a different category, with no error that names the cause.

## References

* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Perfect.SupportedBiprodShiftAffine

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (e : X ≅ Y) (U : Opens X)

/-! ### The image of an open under an isomorphism of ringed spaces -/

/-- **The image of an open `U` of `X` under an isomorphism `e : X ≅ Y`**, written as the
preimage of `U` under the underlying map of `e.inv`. The two descriptions agree because the two
underlying maps are mutually inverse; that identification is
`Stacks.Perfect.SupportedBiprodShiftAffine.preimage_inv_base_eq_image`. -/
def imageOpenOfIso : Opens Y := (Opens.map e.inv.hom.base).obj U

/-- The underlying map of `e.inv` undoes that of `e.hom`. -/
theorem inv_base_hom_base (x : X.carrier) : e.inv.hom.base (e.hom.hom.base x) = x :=
  congrArg (fun φ : X ⟶ X => φ.hom.base x) e.hom_inv_id

/-- The underlying map of `e.hom` undoes that of `e.inv`. -/
theorem hom_base_inv_base (y : Y.carrier) : e.hom.hom.base (e.inv.hom.base y) = y :=
  congrArg (fun φ : Y ⟶ Y => φ.hom.base y) e.inv_hom_id

/-- **The complement of a preimage under `e.inv` is the image of the complement under `e.hom`.**
Stated at the complement because that is the form the quasi-compactness hypothesis of
[Stacks, Tag 08EK] is in: `Tᶜ` compact has to be carried to `(e(T))ᶜ` compact, and the image of
a compact set under a continuous map is compact. -/
theorem compl_preimage_inv_base_eq_image (S : Set X) :
    (e.inv.hom.base ⁻¹' S)ᶜ = e.hom.hom.base '' Sᶜ := by
  ext y
  constructor
  · intro hy
    exact ⟨e.inv.hom.base y, hy, hom_base_inv_base e y⟩
  · rintro ⟨x, hx, rfl⟩
    rwa [Set.mem_compl_iff, Set.mem_preimage, inv_base_hom_base]

/-- **A preimage under `e.inv` is an image under `e.hom`**, so a quasi-compact open of `X` has
quasi-compact image in `Y`. -/
theorem preimage_inv_base_eq_image (S : Set X) :
    e.inv.hom.base ⁻¹' S = e.hom.hom.base '' S := by
  simpa using congrArg (fun Z : Set Y.carrier => Zᶜ) (compl_preimage_inv_base_eq_image e Sᶜ)

/-! ### The induced isomorphism of open subspaces -/

/-- **`U ⟶ X ⟶ Y` and `e(U) ⟶ Y` have the same range.** Both are the set of points of `Y` whose
image under `e.inv` lies in `U`. -/
theorem range_ofRestrict_comp_eq :
    Set.range (SheafedSpace.forgetToPresheafedSpace.map
        (X.ofRestrict U.isOpenEmbedding ≫ e.hom)).base =
      Set.range (SheafedSpace.forgetToPresheafedSpace.map
        (Y.ofRestrict (imageOpenOfIso e U).isOpenEmbedding)).base := by
  change Set.range (X.ofRestrict U.isOpenEmbedding ≫ e.hom).hom.base =
    Set.range (Y.ofRestrict (imageOpenOfIso e U).isOpenEmbedding).hom.base
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨e.hom.hom.base x.1, ?_⟩, rfl⟩
    change e.inv.hom.base (e.hom.hom.base x.1) ∈ U
    rw [inv_base_hom_base]
    exact x.2
  · rintro ⟨z, rfl⟩
    refine ⟨⟨e.inv.hom.base z.1, z.2⟩, ?_⟩
    change e.hom.hom.base (e.inv.hom.base z.1) = z.1
    rw [hom_base_inv_base]

/-- **`X|_U ≅ Y|_{e(U)}`** for an isomorphism `e : X ≅ Y` of ringed spaces and an open `U` of
`X`: the two open immersions into `Y` have the same range by
`Stacks.Perfect.SupportedBiprodShiftAffine.range_ofRestrict_comp_eq`, so
`PresheafedSpace.IsOpenImmersion.isoOfRangeEq` identifies their sources. -/
def restrictIsoOfIso :
    X.restrict U.isOpenEmbedding ≅ Y.restrict (imageOpenOfIso e U).isOpenEmbedding :=
  (SheafedSpace.fullyFaithfulForgetToPresheafedSpace (C := CommRingCat.{u})).preimageIso
    (PresheafedSpace.IsOpenImmersion.isoOfRangeEq _ _ (range_ofRestrict_comp_eq e U))

/-- **The isomorphism `X|_U ≅ Y|_{e(U)}` is compatible with the inclusions into `Y`:** followed
by the inclusion of `e(U)` it is the inclusion of `U` followed by `e`. -/
theorem restrictIsoOfIso_hom_comp_ofRestrict :
    (restrictIsoOfIso e U).hom ≫ Y.ofRestrict (imageOpenOfIso e U).isOpenEmbedding =
      X.ofRestrict U.isOpenEmbedding ≫ e.hom := by
  apply SheafedSpace.forgetToPresheafedSpace.map_injective
  rw [Functor.map_comp]
  simp only [restrictIsoOfIso, Functor.FullyFaithful.preimageIso_hom]
  exact PresheafedSpace.IsOpenImmersion.lift_fac _ _ (range_ofRestrict_comp_eq e U).le

/-- **The same compatibility read on the inverse:** `Y|_{e(U)} ⟶ X|_U ⟶ X` is the inclusion of
`e(U)` followed by `e.inv`. -/
theorem restrictIsoOfIso_inv_comp_ofRestrict :
    (restrictIsoOfIso e U).inv ≫ X.ofRestrict U.isOpenEmbedding =
      Y.ofRestrict (imageOpenOfIso e U).isOpenEmbedding ≫ e.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, restrictIsoOfIso_hom_comp_ofRestrict, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **The isomorphism `Y|_{e(U)} ≅ X|_U` moves points by `e.inv`.** This is
`Stacks.Perfect.SupportedBiprodShiftAffine.restrictIsoOfIso_inv_comp_ofRestrict` read at a
point, the inclusions of open subspaces being the subtype inclusions. It is what identifies the
preimage of a closed subset of `X` in `Y|_{e(U)}` with the preimage of its image. -/
theorem restrictIsoOfIso_inv_base_val
    (z : (Y.restrict (imageOpenOfIso e U).isOpenEmbedding).carrier) :
    Subtype.val ((restrictIsoOfIso e U).inv.hom.base z) = e.inv.hom.base (Subtype.val z) :=
  congrArg (fun φ : Y.restrict (imageOpenOfIso e U).isOpenEmbedding ⟶ X => φ.hom.base z)
    (restrictIsoOfIso_inv_comp_ofRestrict e U)

/-! ### Restriction of a derived pullback along an isomorphism -/

/-- **Restricting to `U` a derived pullback along `e` is pulling back the restriction to `e(U)`**,
at one object, along `X|_U ≅ Y|_{e(U)}`.

Each derived restriction is the derived pullback along the inclusion of its open, derived
pullbacks along composable morphisms compose by [Stacks, Tag 0D5S], and the two routes from
`X|_U` to `Y` agree by
`Stacks.Perfect.SupportedBiprodShiftAffine.restrictIsoOfIso_hom_comp_ofRestrict`. -/
def derivedRestrictModulesObjIsoOfIso (Q : DerivedCategory (OXMod.{u, u} Y)) :
    (AlgebraicGeometry.RingedSpace.derivedRestrictModules X U).obj
        ((derivedPullback e.hom).obj Q) ≅
      (derivedPullback (restrictIsoOfIso e U).hom).obj
        ((AlgebraicGeometry.RingedSpace.derivedRestrictModules Y (imageOpenOfIso e U)).obj Q) :=
  (AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback X U).app _ ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (X.ofRestrict U.isOpenEmbedding) e.hom).app Q ≪≫
    eqToIso (congrArg (fun f : X.restrict U.isOpenEmbedding ⟶ Y => (derivedPullback f).obj Q)
      (restrictIsoOfIso_hom_comp_ofRestrict e U).symm) ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (restrictIsoOfIso e U).hom
        (Y.ofRestrict (imageOpenOfIso e U).isOpenEmbedding)).app Q).symm ≪≫
    (derivedPullback (restrictIsoOfIso e U).hom).mapIso
      ((AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback Y
        (imageOpenOfIso e U)).app Q).symm

/-! ### One functor carried to `· ⊕ ·⟦1⟧` -/

/-- **An additive, shift-commuting functor taking `G` to `Z` takes `G ⊕ G[1]` to `Z ⊕ Z[1]`.**
This is `Stacks.Perfect.SupportedBiprodShift.biprodShiftIsoOfFunctorIso` with the second functor
the identity of the codomain; see the implementation notes of this module for why the identity
is supplied here rather than at the geometry. -/
def biprodShiftIsoOfObjIso {C₁ C₃ : Type*} [Category C₁] [Category C₃]
    [Preadditive C₁] [Preadditive C₃]
    [HasBinaryBiproducts C₁] [HasBinaryBiproducts C₃]
    [HasShift C₁ ℤ] [HasShift C₃ ℤ]
    (H : C₁ ⥤ C₃) (hH : H.Additive) (cH : H.CommShift ℤ) {G : C₁} {Z : C₃}
    (i : H.obj G ≅ Z) :
    H.obj (G ⊞ G⟦(1 : ℤ)⟧) ≅ Z ⊞ Z⟦(1 : ℤ)⟧ :=
  Stacks.Perfect.SupportedBiprodShift.biprodShiftIsoOfFunctorIso H (𝟭 C₃) hH inferInstance
    cH inferInstance i

/-! ### The conclusion at a general affine scheme -/

/-- **`F ⊕ F[1]` is the restriction of a perfect object supported on `T`, at any ringed space
isomorphic to `Spec A`.** Let `e : X ≅ Spec A` be an isomorphism of ringed spaces, let `T ⊆ X`
be closed with `X ∖ T` quasi-compact, and let `U ⊆ X` be a quasi-compact open. For every perfect
object `F` of `D(𝒪_U)` whose cohomology is supported on `T ∩ U` there is a perfect object `P` of
`D(𝒪_X)` whose cohomology is supported on `T`, with `F ⊕ F[1] ≅ P|_U`.

Everything is carried to `Spec A` along `e`: the closed set and the open become their images,
`Stacks.Perfect.SupportedBiprodShiftAffine.compl_preimage_inv_base_eq_image` and
`Stacks.Perfect.SupportedBiprodShiftAffine.preimage_inv_base_eq_image` turning the two
quasi-compactness hypotheses into statements about images of compact sets; `F` becomes its
derived pullback along `Y|_{e(U)} ≅ X|_U`, which is perfect by
`Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_iff` and keeps its support by
`Stacks.Cohomology.SupportedComplexes.cohomologySupportedOn_derivedPullback`, the support set
being identified by
`Stacks.Perfect.SupportedBiprodShiftAffine.restrictIsoOfIso_inv_base_val`. The object produced
by [Stacks, Tag 08EK] over `Spec A` is pulled back along `e`, which preserves perfectness and
support by the same two lemmas, and its restriction to `U` is computed by
`Stacks.Perfect.SupportedBiprodShiftAffine.derivedRestrictModulesObjIsoOfIso` together with
`Stacks.Perfect.SupportedBiprodShiftAffine.biprodShiftIsoOfObjIso`.

The registration of [Stacks, Tag 08EK] is on another declaration, so no tag
attribute is placed here. -/
theorem exists_isPerfect_supported_biprod_shift_iso_restrict_of_isoSpec {A : CommRingCat.{u}}
    {X : RingedSpace.{u, u}} (e : X ≅ (Spec A).toRingedSpace)
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (U : Opens X) (hU : IsCompact ((U : Opens X) : Set X))
    (F : DerivedCategory (OXMod.{u, u} (X.restrict U.isOpenEmbedding)))
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := X.restrict U.isOpenEmbedding) F)
    (hFT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (X.restrict U.isOpenEmbedding)) (Subtype.val ⁻¹' T) F) :
    ∃ P : DerivedCategory (OXMod.{u, u} X),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) P ∧
        AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) T P ∧
          Nonempty ((F ⊞ F⟦(1 : ℤ)⟧) ≅
            (AlgebraicGeometry.RingedSpace.derivedRestrictModules X U).obj P) := by
  have hT' : IsClosed (e.inv.hom.base ⁻¹' T) := hT.preimage e.inv.hom.base.hom.continuous
  have hTc' : IsCompact (e.inv.hom.base ⁻¹' T)ᶜ := by
    rw [compl_preimage_inv_base_eq_image e T]
    exact hTc.image e.hom.hom.base.hom.continuous
  have hU' : IsCompact ((imageOpenOfIso e U : Opens (Spec A).toRingedSpace) :
      Set (Spec A).toRingedSpace) := by
    change IsCompact (e.inv.hom.base ⁻¹' (U : Set X))
    rw [preimage_inv_base_eq_image e (U : Set X)]
    exact hU.image e.hom.hom.base.hom.continuous
  have hG : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec A).toRingedSpace.restrict (imageOpenOfIso e U).isOpenEmbedding)
      ((derivedPullback (restrictIsoOfIso e U).inv).obj F) :=
    (Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_iff
      (restrictIsoOfIso e U).symm F).2 hF
  have hGT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing
        ((Spec A).toRingedSpace.restrict (imageOpenOfIso e U).isOpenEmbedding))
      (Subtype.val ⁻¹' (e.inv.hom.base ⁻¹' T))
      ((derivedPullback (restrictIsoOfIso e U).inv).obj F) := by
    have h := Stacks.Cohomology.SupportedComplexes.cohomologySupportedOn_derivedPullback
      (restrictIsoOfIso e U).inv (Subtype.val ⁻¹' T) F hFT
    have hset : Stacks.Cohomology.SupportedComplexes.closedSubsetPreimage
        (restrictIsoOfIso e U).inv (Subtype.val ⁻¹' T) =
        Subtype.val ⁻¹' (e.inv.hom.base ⁻¹' T) := by
      ext z
      change Subtype.val ((restrictIsoOfIso e U).inv.hom.base z) ∈ T ↔
        e.inv.hom.base (Subtype.val z) ∈ T
      rw [restrictIsoOfIso_inv_base_val]
    exact hset ▸ h
  obtain ⟨Q, hQ, hQT, ⟨eQ⟩⟩ :=
    Stacks.Perfect.SupportedBiprodShift.exists_isPerfect_supported_biprod_shift_iso_restrict
      (e.inv.hom.base ⁻¹' T) hT' hTc' (imageOpenOfIso e U) hU'
      ((derivedPullback (restrictIsoOfIso e U).inv).obj F) hG hGT
  refine ⟨(derivedPullback e.hom).obj Q,
    (Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_iff e Q).2 hQ, ?_, ?_⟩
  · have h := Stacks.Cohomology.SupportedComplexes.cohomologySupportedOn_derivedPullback
      e.hom (e.inv.hom.base ⁻¹' T) Q hQT
    have hset : Stacks.Cohomology.SupportedComplexes.closedSubsetPreimage
        e.hom (e.inv.hom.base ⁻¹' T) = T := by
      ext x
      change e.inv.hom.base (e.hom.hom.base x) ∈ T ↔ x ∈ T
      rw [inv_base_hom_base]
    exact hset ▸ h
  · exact ⟨(biprodShiftIsoOfObjIso (derivedPullback (restrictIsoOfIso e U).hom)
        (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackAdditive
          (restrictIsoOfIso e U).hom)
        (Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift
          (restrictIsoOfIso e U).hom)
        ((Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackInvHomIso
          (restrictIsoOfIso e U)).app F)).symm ≪≫
      (derivedPullback (restrictIsoOfIso e U).hom).mapIso eQ ≪≫
      (derivedRestrictModulesObjIsoOfIso e U Q).symm⟩

/-- **[Stacks, Tag 08EK] at a general affine scheme.** Let `W` be an affine scheme, let `T ⊆ W`
be closed with `W ∖ T` quasi-compact, and let `U ⊆ W` be a quasi-compact open. For every perfect
object `F` of `D(𝒪_U)` whose cohomology is supported on `T ∩ U` there is a perfect object `P` of
`D(𝒪_W)` whose cohomology is supported on `T`, with `F ⊕ F[1] ≅ P|_U`.

This is `exists_isPerfect_supported_biprod_shift_iso_restrict_of_isoSpec`, in this namespace,
along `AlgebraicGeometry.Scheme.isoSpec`, read on underlying ringed spaces by
`Stacks.Cohomology.TransportAlongIso.ringedSpaceIsoOfSchemeIso`. The two-open step of
[Stacks, Tag 09IM] applies it at an affine open `V` of a general scheme, that is at
`W = V.toScheme`.

The registration of [Stacks, Tag 08EK] is on another declaration, so no tag
attribute is placed here. -/
theorem exists_isPerfect_supported_biprod_shift_iso_restrict_of_isAffine (W : Scheme.{u})
    [IsAffine W] (T : Set W) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (U : W.Opens) (hU : IsCompact ((U : W.Opens) : Set W))
    (F : DerivedCategory (OXMod.{u, u} (W.toRingedSpace.restrict U.isOpenEmbedding)))
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := W.toRingedSpace.restrict U.isOpenEmbedding) F)
    (hFT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (W.toRingedSpace.restrict U.isOpenEmbedding))
      (Subtype.val ⁻¹' T) F) :
    ∃ P : DerivedCategory (OXMod.{u, u} W.toRingedSpace),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) P ∧
        AlgebraicGeometry.CohomologySupportedOn (structureSheafRing W.toRingedSpace) T P ∧
          Nonempty ((F ⊞ F⟦(1 : ℤ)⟧) ≅
            (AlgebraicGeometry.RingedSpace.derivedRestrictModules W.toRingedSpace U).obj P) :=
  exists_isPerfect_supported_biprod_shift_iso_restrict_of_isoSpec
    (Stacks.Cohomology.TransportAlongIso.ringedSpaceIsoOfSchemeIso W.isoSpec)
    T hT hTc U hU F hF hFT

end Stacks.Perfect.SupportedBiprodShiftAffine

end
