module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFactorizationLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# An open immersion induces an open immersion of Hilbert functors (Stacks 0DPE)

Let `π : X ⟶ Y` be an open immersion of algebraic spaces over an algebraic space `A`, with
structure morphisms `bX : X ⟶ A` and `bY : Y ⟶ A` satisfying `π ≫ bY = bX`. Over a scheme `T`
of the site lying over `A` the base change `π_T : X_T ⟶ Y_T` is again an open immersion, so a
closed subspace `Z ⊆ X_T` has an image `π_T(Z) ⊆ Y_T` isomorphic to `Z`; the image is closed
because `Z` is proper over `T` and `Y_T` is separated over `T`, and it inherits flatness, finite
presentation and properness over `T` from `Z` along that isomorphism. Sending a family to its
image is the morphism of Hilbert functors `Hilb_{X/A} ⟶ Hilb_{Y/A}` of Stacks 0DPE, and it is an
open immersion.

Being an open immersion is a property of a morphism of presheaves of `Type u`, while the Hilbert
functor takes values in `Type (u + 1)`, so the open immersion statement is made about the
morphism induced on models (`AlgebraicGeometry.Space.HilbertPresheafModel`) of the two Hilbert
functors.

## Main definitions

* `AlgebraicGeometry.Space.schemeBaseChangeOfMap` is the base change `π_T : X_T ⟶ Y_T`.
* `AlgebraicGeometry.Space.hilbertFamilyImage` is the image of a family.
* `AlgebraicGeometry.Space.hilbertFamilyPreimage` is the inverse image of a family of `Y/A`
  whose closed subspace lands in `X_T`.
* `AlgebraicGeometry.Space.hilbertPresheafMap`: the induced morphism of Hilbert functors.
* `AlgebraicGeometry.Space.hilbertModelMap` is that morphism read in given models of the two
  Hilbert functors.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_hilbertModelMap`: the induced morphism is an open
  immersion, read in any models of the two Hilbert functors.
* `AlgebraicGeometry.Space.exists_hilbertFamilyOverImage_iff`: a family of `Y/A` is in the image
  exactly when its closed subspace lands in `X_T`.

## References

* [Stacks Project, Tag 0DPE](https://stacks.math.columbia.edu/tag/0DPE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y A : AlgebraicSpaces B S hS} {π : X ⟶ Y} {bX : X ⟶ A} {bY : Y ⟶ A}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_hilbertFunctorOpenImmersion
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Generalities -/

/-- A morphism factors through one leg of a cartesian square exactly when its composite with
the opposite leg factors through the other. -/
private theorem factorsThrough_pullback_iff {C : Type*} [Category C] {P Q D E Z : C}
    {a : P ⟶ Q} {b : P ⟶ D} {c : Q ⟶ E} {d : D ⟶ E}
    (sq : IsPullback a b c d) (r : Z ⟶ D) :
    (∃ k : Z ⟶ P, k ≫ b = r) ↔ ∃ k : Z ⟶ Q, k ≫ c = r ≫ d := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k ≫ a, by rw [Category.assoc, sq.w, ← Category.assoc, hk]⟩
  · rintro ⟨k, hk⟩
    exact ⟨sq.lift k r hk, sq.lift_snd _ _ _⟩

/-- A property of morphisms respecting isomorphisms does not distinguish two morphisms to a
common target whose sources are identified by an isomorphism over that target. -/
private theorem property_iff_of_sourceIso {C : Type*} [Category C] (P : MorphismProperty C)
    (hP : P.RespectsIso) {V W Z : C} (e : V ≅ W) (a : V ⟶ Z) (b : W ⟶ Z)
    (he : e.hom ≫ b = a) : P a ↔ P b := by
  have _ := hP
  rw [← he]
  refine ⟨fun h => ?_, MorphismProperty.RespectsIso.precomp P e.hom b⟩
  simpa using MorphismProperty.RespectsIso.precomp P e.inv _ h

/-! ### The base change of a morphism over the base -/

section BaseChange

variable (hπ : π ≫ bY = bX)

include hπ

/-- A commuting triangle of algebraic spaces over `S` commutes on the underlying presheaves. -/
theorem hom_comp_hom_of_comp_eq : π.hom ≫ bY.hom = bX.hom := by rw [← hπ]; rfl

/-- The base change `π_T : X_T ⟶ Y_T` of a morphism over the base to a scheme over the base. -/
def schemeBaseChangeOfMap (T : SchemesOverPresheaf B S hS A) :
    schemeBaseChange bX T ⟶ schemeBaseChange bY T :=
  pullback.lift (pullback.fst bX.hom T.hom ≫ π.hom) (pullback.snd bX.hom T.hom) (by
    rw [Category.assoc, hom_comp_hom_of_comp_eq hπ]
    exact pullback.condition)

/-- The base change `π_T` followed by the projection `Y_T ⟶ Y` is the projection `X_T ⟶ X`
followed by `π`. -/
@[simp]
theorem schemeBaseChangeOfMap_fst (T : SchemesOverPresheaf B S hS A) :
    schemeBaseChangeOfMap hπ T ≫ pullback.fst bY.hom T.hom =
      pullback.fst bX.hom T.hom ≫ π.hom :=
  pullback.lift_fst _ _ _

/-- The base change `π_T` is a morphism over `T`. -/
@[simp]
theorem schemeBaseChangeOfMap_snd (T : SchemesOverPresheaf B S hS A) :
    schemeBaseChangeOfMap hπ T ≫ pullback.snd bY.hom T.hom =
      pullback.snd bX.hom T.hom :=
  pullback.lift_snd _ _ _

/-- The base change of a morphism over the base is a base change in the strict sense: `X_T` is
the fibre product of `Y_T` and `X` over `Y`. -/
theorem isPullback_schemeBaseChangeOfMap (T : SchemesOverPresheaf B S hS A) :
    IsPullback (schemeBaseChangeOfMap hπ T) (pullback.fst bX.hom T.hom)
      (pullback.fst bY.hom T.hom) π.hom := by
  have outer : IsPullback (schemeBaseChangeOfMap hπ T ≫ pullback.snd bY.hom T.hom)
      (pullback.fst bX.hom T.hom) T.hom (π.hom ≫ bY.hom) := by
    rw [schemeBaseChangeOfMap_snd, hom_comp_hom_of_comp_eq hπ]
    exact (IsPullback.of_hasPullback bX.hom T.hom).flip
  exact outer.of_right (schemeBaseChangeOfMap_fst hπ T)
    (IsPullback.of_hasPullback bY.hom T.hom).flip

/-- The base change of an open immersion over the base is an open immersion. -/
theorem isOpenImmersion_schemeBaseChangeOfMap (hopen : IsOpenImmersion B S hS π.hom)
    (T : SchemesOverPresheaf B S hS A) :
    IsOpenImmersion B S hS (schemeBaseChangeOfMap hπ T) := by
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_schemeBaseChangeOfMap hπ T).flip hopen

/-- The base change of an open immersion over the base is a monomorphism. -/
theorem mono_schemeBaseChangeOfMap (hopen : IsOpenImmersion B S hS π.hom)
    (T : SchemesOverPresheaf B S hS A) : Mono (schemeBaseChangeOfMap hπ T) :=
  mono_of_presheaf_isOpenImmersion (isOpenImmersion_schemeBaseChangeOfMap hπ hopen T)

/-- The base changes of a morphism over the base to two schemes over the base, together with
the transition morphisms of the base changes, form a cartesian square. -/
theorem isPullback_schemeBaseChangeOfMap_comm {T T' : SchemesOverPresheaf B S hS A}
    (g : T' ⟶ T) :
    IsPullback (schemeBaseChangeMap bX g) (schemeBaseChangeOfMap hπ T')
      (schemeBaseChangeOfMap hπ T) (schemeBaseChangeMap bY g) := by
  have hcomm : schemeBaseChangeMap bX g ≫ schemeBaseChangeOfMap hπ T =
      schemeBaseChangeOfMap hπ T' ≫ schemeBaseChangeMap bY g := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, schemeBaseChangeOfMap_fst, schemeBaseChangeMap_fst]
      rw [← Category.assoc, schemeBaseChangeMap_fst]
    · simp only [Category.assoc, schemeBaseChangeOfMap_snd, schemeBaseChangeMap_snd]
      rw [← Category.assoc, schemeBaseChangeOfMap_snd]
  refine IsPullback.of_right ?_ hcomm (isPullback_schemeBaseChangeOfMap hπ T).flip
  rw [schemeBaseChangeMap_fst bX g, schemeBaseChangeMap_fst bY g]
  exact (isPullback_schemeBaseChangeOfMap hπ T').flip

end BaseChange


/-! ### The image of a family -/

section Image

variable (hπ : π ≫ bY = bX)

include hπ

/-- The comparison with the image is compatible with the structure morphisms to the test
scheme. -/
private theorem toImage_comp_ι_comp_snd (T : SchemesOverPresheaf B S hS A)
    (z : HilbertFamily bX T) :
    z.Z.toImage (schemeBaseChangeOfMap hπ T) ≫
        ((z.Z.image (schemeBaseChangeOfMap hπ T)).ι ≫ pullback.snd bY.hom T.hom) =
      z.Z.ι ≫ pullback.snd bX.hom T.hom := by
  rw [← Category.assoc, Subfunctor.toImage_ι, Category.assoc, schemeBaseChangeOfMap_snd]

variable (hopen : IsOpenImmersion B S hS π.hom)

include hopen

/-- The image of the closed subspace of a family is an algebraic space over `S`. -/
theorem isAlgebraicSpace_image_Z (T : SchemesOverPresheaf B S hS A) (z : HilbertFamily bX T) :
    IsAlgebraicSpace B S hS (z.Z.image (schemeBaseChangeOfMap hπ T)).toFunctor := by
  have := mono_schemeBaseChangeOfMap hπ hopen T
  exact z.closed.1.of_iso (asIso (z.Z.toImage (schemeBaseChangeOfMap hπ T)))

/-- A property of morphisms of algebraic spaces over `S` stable under base change holds for the
structure morphism of the image of a family exactly when it holds for the structure morphism of
the family. -/
private theorem property_image_iff (T : SchemesOverPresheaf B S hS A) (z : HilbertFamily bX T)
    {P : MorphismProperty (AlgebraicSpaces B S hS)} (hP : P.IsStableUnderBaseChange) :
    P (ObjectProperty.homMk (X := (⟨z.Z.toFunctor, z.closed.1⟩ : AlgebraicSpaces B S hS))
        (Y := schemeOverSpace T) (z.Z.ι ≫ pullback.snd bX.hom T.hom)) ↔
      P (ObjectProperty.homMk
        (X := (⟨(z.Z.image (schemeBaseChangeOfMap hπ T)).toFunctor,
          isAlgebraicSpace_image_Z hπ hopen T z⟩ : AlgebraicSpaces B S hS))
        (Y := schemeOverSpace T)
        ((z.Z.image (schemeBaseChangeOfMap hπ T)).ι ≫ pullback.snd bY.hom T.hom)) := by
  have := mono_schemeBaseChangeOfMap hπ hopen T
  refine property_iff_of_sourceIso P hP.respectsIso
    (ObjectProperty.isoMk _ (asIso (z.Z.toImage (schemeBaseChangeOfMap hπ T)))) _ _ ?_
  exact ObjectProperty.hom_ext _ (toImage_comp_ι_comp_snd hπ T z)

/-- The image of the closed subspace of a family is of finite presentation over the test
scheme. -/
theorem isFinitePresentation_image_Z (T : SchemesOverPresheaf B S hS A)
    (z : HilbertFamily bX T) :
    IsFinitePresentation B S hS
      ((z.Z.image (schemeBaseChangeOfMap hπ T)).ι ≫ pullback.snd bY.hom T.hom) := by
  exact (property_image_iff hπ hopen T z
    (isFinitePresentation_isStableUnderBaseChange B S hS)).1 z.finitePresentation

/-- The image of the closed subspace of a family is flat over the test scheme. -/
theorem isFlat_image_Z (T : SchemesOverPresheaf B S hS A) (z : HilbertFamily bX T) :
    IsFlat B S hS
      ((z.Z.image (schemeBaseChangeOfMap hπ T)).ι ≫ pullback.snd bY.hom T.hom) := by
  exact (property_image_iff hπ hopen T z
    (isFlat_isStableUnderBaseChange B S hS)).1 z.flat

/-- The image of the closed subspace of a family is proper over the test scheme. -/
theorem isProper_image_Z (T : SchemesOverPresheaf B S hS A) (z : HilbertFamily bX T) :
    IsProper B S hS
      ((z.Z.image (schemeBaseChangeOfMap hπ T)).ι ≫ pullback.snd bY.hom T.hom) := by
  exact (property_image_iff hπ hopen T z
    (isProper_isStableUnderBaseChange B S hS)).1 z.proper

variable (hsep : IsSeparated B S hS bY.hom)

include hsep

/-- The image of the closed subspace of a family is a closed subspace of `Y_T`. -/
theorem isClosedSubspace_hilbertFamilyImage (T : SchemesOverPresheaf B S hS A)
    (z : HilbertFamily bX T) :
    IsClosedSubspace B S hS (z.Z.image (schemeBaseChangeOfMap hπ T)) := by
  have := mono_schemeBaseChangeOfMap hπ hopen T
  have hj := isOpenImmersion_schemeBaseChangeOfMap hπ hopen T
  have hYT : IsAlgebraicSpace B S hS (schemeBaseChange bY T) :=
    isAlgebraicSpace_schemeBaseChange bY T
  have hT : IsAlgebraicSpace B S hS (yoneda.obj T.left) := isAlgebraicSpace_yoneda B S hS T.left
  have hinv : inv (z.Z.toImage (schemeBaseChangeOfMap hπ T)) ≫
      (z.Z.ι ≫ schemeBaseChangeOfMap hπ T) =
      (z.Z.image (schemeBaseChangeOfMap hπ T)).ι := by
    rw [← Subfunctor.toImage_ι z.Z (schemeBaseChangeOfMap hπ T), IsIso.inv_hom_id_assoc]
  refine ⟨isAlgebraicSpace_image_Z hπ hopen T z, ?_⟩
  have himm : IsImmersion B S hS (z.Z.ι ≫ schemeBaseChangeOfMap hπ T) :=
    isImmersion_comp B S hS _ _ (isImmersion_of_isClosedImmersion B S hS z.closed.2)
      (isImmersion_of_isOpenImmersion B S hS hj)
  have hιimm : IsImmersion B S hS (z.Z.image (schemeBaseChangeOfMap hπ T)).ι := by
    have h := MorphismProperty.RespectsIso.precomp
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      (inv (z.Z.toImage (schemeBaseChangeOfMap hπ T))) _ himm
    rwa [hinv] at h
  refine (isClosedImmersion_iff_isClosed_range_pointsMap B S hS hYT _ hιimm).2 ?_
  rw [← hinv, range_pointsMap_comp_isIso]
  have huc : UniversallyClosed B S hS
      ((z.Z.ι ≫ schemeBaseChangeOfMap hπ T) ≫ pullback.snd bY.hom T.hom) := by
    rw [Category.assoc, schemeBaseChangeOfMap_snd]
    exact z.proper.2.2
  exact isClosed_range_of_comp_of_isSeparated B S hS z.closed.1 hYT hT _
    (pullback.snd bY.hom T.hom) huc (isSeparated_pullback B S hS bY.hom T.hom hsep)

/-- The image of a family of closed subspaces of `X_T` under the base change of an open
immersion over the base, as a family of closed subspaces of `Y_T`. -/
def hilbertFamilyImage (T : SchemesOverPresheaf B S hS A) (z : HilbertFamily bX T) :
    HilbertFamily bY T where
  Z := z.Z.image (schemeBaseChangeOfMap hπ T)
  closed := isClosedSubspace_hilbertFamilyImage hπ hopen hsep T z
  finitePresentation := isFinitePresentation_image_Z hπ hopen T z
  flat := isFlat_image_Z hπ hopen T z
  proper := isProper_image_Z hπ hopen T z

/-- The closed subspace of the image of a family is the image of its closed subspace. -/
@[simp]
theorem hilbertFamilyImage_Z (T : SchemesOverPresheaf B S hS A) (z : HilbertFamily bX T) :
    (hilbertFamilyImage hπ hopen hsep T z).Z = z.Z.image (schemeBaseChangeOfMap hπ T) := rfl

end Image

/-! ### The inverse image of a family landing in the open subspace -/

section Preimage

variable (hπ : π ≫ bY = bX)

include hπ

/-- The inverse image in `X_T` of the closed subspace of a family of `Y/A` is a closed subspace
of `X_T`. -/
theorem isClosedSubspace_hilbertFamilyPreimage (T : SchemesOverPresheaf B S hS A)
    (z : HilbertFamily bY T) :
    IsClosedSubspace B S hS (z.Z.preimage (schemeBaseChangeOfMap hπ T)) :=
  isClosedSubspace_preimage B S hS (schemeBaseChangeOfMap hπ T) z.Z
    (isAlgebraicSpace_schemeBaseChange bY T) (isAlgebraicSpace_schemeBaseChange bX T) z.closed

/-- The comparison of the inverse image with the family is compatible with the structure
morphisms to the test scheme. -/
private theorem fromPreimage_comp_ι_comp_snd (T : SchemesOverPresheaf B S hS A)
    (z : HilbertFamily bY T) :
    z.Z.fromPreimage (schemeBaseChangeOfMap hπ T) ≫ (z.Z.ι ≫ pullback.snd bY.hom T.hom) =
      (z.Z.preimage (schemeBaseChangeOfMap hπ T)).ι ≫ pullback.snd bX.hom T.hom := by
  rw [← Category.assoc, Subfunctor.fromPreimage_ι, Category.assoc, schemeBaseChangeOfMap_snd]

variable (hopen : IsOpenImmersion B S hS π.hom)

include hopen

/-- A property of morphisms of algebraic spaces over `S` stable under base change holds for the
structure morphism of the inverse image of a family whose closed subspace lands in `X_T` exactly
when it holds for the structure morphism of the family. -/
private theorem property_preimage_iff (T : SchemesOverPresheaf B S hS A)
    (z : HilbertFamily bY T) (hz : z.Z ≤ Subfunctor.range (schemeBaseChangeOfMap hπ T))
    {P : MorphismProperty (AlgebraicSpaces B S hS)} (hP : P.IsStableUnderBaseChange) :
    P (ObjectProperty.homMk (X := (⟨(z.Z.preimage (schemeBaseChangeOfMap hπ T)).toFunctor,
          (isClosedSubspace_hilbertFamilyPreimage hπ T z).1⟩ : AlgebraicSpaces B S hS))
        (Y := schemeOverSpace T)
        ((z.Z.preimage (schemeBaseChangeOfMap hπ T)).ι ≫ pullback.snd bX.hom T.hom)) ↔
      P (ObjectProperty.homMk (X := (⟨z.Z.toFunctor, z.closed.1⟩ : AlgebraicSpaces B S hS))
        (Y := schemeOverSpace T) (z.Z.ι ≫ pullback.snd bY.hom T.hom)) := by
  have := mono_schemeBaseChangeOfMap hπ hopen T
  have : IsIso (z.Z.fromPreimage (schemeBaseChangeOfMap hπ T)) :=
    Subfunctor.isIso_fromPreimage_of_le_range z.Z _ hz
  refine property_iff_of_sourceIso P hP.respectsIso
    (ObjectProperty.isoMk _ (asIso (z.Z.fromPreimage (schemeBaseChangeOfMap hπ T)))) _ _ ?_
  exact ObjectProperty.hom_ext _ (fromPreimage_comp_ι_comp_snd hπ T z)

/-- The inverse image of the closed subspace of a family landing in `X_T` is of finite
presentation over the test scheme. -/
theorem isFinitePresentation_preimage_Z (T : SchemesOverPresheaf B S hS A)
    (z : HilbertFamily bY T) (hz : z.Z ≤ Subfunctor.range (schemeBaseChangeOfMap hπ T)) :
    IsFinitePresentation B S hS
      ((z.Z.preimage (schemeBaseChangeOfMap hπ T)).ι ≫ pullback.snd bX.hom T.hom) := by
  exact (property_preimage_iff hπ hopen T z hz
    (isFinitePresentation_isStableUnderBaseChange B S hS)).2 z.finitePresentation

/-- The inverse image of the closed subspace of a family landing in `X_T` is flat over the test
scheme. -/
theorem isFlat_preimage_Z (T : SchemesOverPresheaf B S hS A) (z : HilbertFamily bY T)
    (hz : z.Z ≤ Subfunctor.range (schemeBaseChangeOfMap hπ T)) :
    IsFlat B S hS
      ((z.Z.preimage (schemeBaseChangeOfMap hπ T)).ι ≫ pullback.snd bX.hom T.hom) := by
  exact (property_preimage_iff hπ hopen T z hz
    (isFlat_isStableUnderBaseChange B S hS)).2 z.flat

/-- The inverse image of the closed subspace of a family landing in `X_T` is proper over the
test scheme. -/
theorem isProper_preimage_Z (T : SchemesOverPresheaf B S hS A) (z : HilbertFamily bY T)
    (hz : z.Z ≤ Subfunctor.range (schemeBaseChangeOfMap hπ T)) :
    IsProper B S hS
      ((z.Z.preimage (schemeBaseChangeOfMap hπ T)).ι ≫ pullback.snd bX.hom T.hom) := by
  exact (property_preimage_iff hπ hopen T z hz
    (isProper_isStableUnderBaseChange B S hS)).2 z.proper

/-- The inverse image of a family of closed subspaces of `Y_T` whose closed subspace is
contained in the image of `X_T`, as a family of closed subspaces of `X_T`. -/
def hilbertFamilyPreimage (T : SchemesOverPresheaf B S hS A) (z : HilbertFamily bY T)
    (hz : z.Z ≤ Subfunctor.range (schemeBaseChangeOfMap hπ T)) : HilbertFamily bX T where
  Z := z.Z.preimage (schemeBaseChangeOfMap hπ T)
  closed := isClosedSubspace_hilbertFamilyPreimage hπ T z
  finitePresentation := isFinitePresentation_preimage_Z hπ hopen T z hz
  flat := isFlat_preimage_Z hπ hopen T z hz
  proper := isProper_preimage_Z hπ hopen T z hz

/-- The closed subspace of the inverse image of a family is the inverse image of its closed
subspace. -/
@[simp]
theorem hilbertFamilyPreimage_Z (T : SchemesOverPresheaf B S hS A) (z : HilbertFamily bY T)
    (hz : z.Z ≤ Subfunctor.range (schemeBaseChangeOfMap hπ T)) :
    (hilbertFamilyPreimage hπ hopen T z hz).Z =
      z.Z.preimage (schemeBaseChangeOfMap hπ T) := rfl

end Preimage

/-! ### The morphism of Hilbert functors -/

section PresheafMap

variable (hπ : π ≫ bY = bX) (hopen : IsOpenImmersion B S hS π.hom)
    (hsep : IsSeparated B S hS bY.hom)

include hπ hopen hsep

/-- The image of a family over a scheme of the site: the same morphism to the base, and the
image of its closed subspace. -/
def hilbertFamilyOverImage (T : BigFppfOver B S hS) (x : HilbertFamilyOver bX T) :
    HilbertFamilyOver bY T where
  toBase := x.toBase
  family := hilbertFamilyImage hπ hopen hsep (CostructuredArrow.mk x.toBase) x.family

/-- The image of a family has the same morphism to the base. -/
@[simp]
theorem hilbertFamilyOverImage_toBase (T : BigFppfOver B S hS) (x : HilbertFamilyOver bX T) :
    (hilbertFamilyOverImage hπ hopen hsep T x).toBase = x.toBase := rfl

/-- The closed subspace of the image of a family over a scheme is the image of its closed
subspace. -/
@[simp]
theorem hilbertFamilyOverImage_family_Z (T : BigFppfOver B S hS)
    (x : HilbertFamilyOver bX T) :
    (hilbertFamilyOverImage hπ hopen hsep T x).family.Z =
      x.family.Z.image (schemeBaseChangeOfMap hπ (CostructuredArrow.mk x.toBase)) := rfl

/-- Taking the image of a family commutes with base change. -/
theorem hilbertFamilyOverImage_baseChange {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : HilbertFamilyOver bX T) :
    hilbertFamilyOverImage hπ hopen hsep T' (x.baseChange g) =
      (hilbertFamilyOverImage hπ hopen hsep T x).baseChange g :=
  HilbertFamilyOver.ext rfl (heq_of_eq
    (Subfunctor.image_preimage_of_isPullback
      (isPullback_schemeBaseChangeOfMap_comm hπ (HilbertFamilyOver.restrict g x.toBase))
      x.family.Z))

/-- An open immersion `π : X ⟶ Y` of algebraic spaces over `A` induces a
morphism of Hilbert functors `Hilb_{X/A} ⟶ Hilb_{Y/A}`, sending a family of closed subspaces of
`X_T` to its image in `Y_T`. -/
@[stacks 0DPE "the induced morphism of Hilbert functors"]
def hilbertPresheafMap : hilbertPresheaf bX ⟶ hilbertPresheaf bY where
  app T := TypeCat.ofHom fun x => hilbertFamilyOverImage hπ hopen hsep T.unop x
  naturality _ _ g :=
    ConcreteCategory.hom_ext _ _ fun x => hilbertFamilyOverImage_baseChange hπ hopen hsep g.unop x

/-- The morphism of Hilbert functors sends a family to its image. -/
@[simp]
theorem hilbertPresheafMap_app_apply (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : (hilbertPresheaf bX).obj T) :
    (hilbertPresheafMap hπ hopen hsep).app T x =
      hilbertFamilyOverImage hπ hopen hsep T.unop x := rfl

/-- Taking the image of a family is injective. -/
theorem hilbertFamilyOverImage_injective (T : BigFppfOver B S hS) :
    Function.Injective (hilbertFamilyOverImage hπ hopen hsep T) := by
  rintro ⟨ab, af⟩ ⟨bb, bf⟩ hab
  have hbase := congrArg HilbertFamilyOver.toBase hab
  change ab = bb at hbase
  subst hbase
  have := mono_schemeBaseChangeOfMap hπ hopen (CostructuredArrow.mk ab)
  have hZ : af.Z = bf.Z :=
    Subfunctor.image_injective_of_mono (schemeBaseChangeOfMap hπ (CostructuredArrow.mk ab))
      (eq_of_heq (HilbertFamilyOver.family_Z_heq hab))
  exact HilbertFamilyOver.ext rfl (heq_of_eq hZ)

/-- A family of closed subspaces of `Y_T` is the image of a family of closed subspaces of `X_T`
exactly when its closed subspace is contained in the image of `X_T`. -/
theorem exists_hilbertFamilyOverImage_iff (T : BigFppfOver B S hS)
    (y : HilbertFamilyOver bY T) :
    (∃ x, hilbertFamilyOverImage hπ hopen hsep T x = y) ↔
      y.family.Z ≤
        Subfunctor.range (schemeBaseChangeOfMap hπ (CostructuredArrow.mk y.toBase)) := by
  refine ⟨fun ⟨x, hx⟩ => hx ▸ fun U a ⟨b, _, hb⟩ => ⟨b, hb⟩, fun hy => ?_⟩
  exact ⟨⟨y.toBase, hilbertFamilyPreimage hπ hopen (CostructuredArrow.mk y.toBase) y.family hy⟩,
    HilbertFamilyOver.ext rfl
      (heq_of_eq (Subfunctor.image_preimage_eq_of_le_range y.family.Z _ hy))⟩

end PresheafMap

/-! ### Reading the morphism in models of the Hilbert functors -/

namespace HilbertPresheafModel

variable {V W : AlgebraicSpaces B S hS} {f : V ⟶ W}

/-- A section of a model of the Hilbert functor of `f` over a scheme of the site is the same
thing as a family classified by the Hilbert functor over that scheme. -/
def familyEquiv (M : HilbertPresheafModel f) (T : BigFppfOver B S hS) :
    M.presheaf.obj (Opposite.op T) ≃ HilbertFamilyOver f T :=
  Equiv.ulift.symm.trans (M.iso.app (Opposite.op T)).toEquiv

/-- The identification of the sections of a model with the families, applied to a section. -/
theorem familyEquiv_apply (M : HilbertPresheafModel f) (T : BigFppfOver B S hS)
    (z : M.presheaf.obj (Opposite.op T)) :
    M.familyEquiv T z = M.iso.hom.app (Opposite.op T) (ULift.up z) := rfl

/-- The identification of the sections of a model with the families is compatible with
restriction. -/
theorem familyEquiv_map (M : HilbertPresheafModel f) {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (z : M.presheaf.obj (Opposite.op T)) :
    M.familyEquiv T' (M.presheaf.map g.op z) = (M.familyEquiv T z).baseChange g := by
  exact types_congr_hom (M.iso.hom.naturality g.op) (ULift.up.{u + 1} z)

end HilbertPresheafModel

section Model

variable (hπ : π ≫ bY = bX) (hopen : IsOpenImmersion B S hS π.hom)
    (hsep : IsSeparated B S hS bY.hom)

include hπ hopen hsep

/-- The morphism of Hilbert functors induced by an open immersion over the base, read in given
models of the two Hilbert functors. -/
def hilbertModelMap (MX : HilbertPresheafModel bX) (MY : HilbertPresheafModel bY) :
    MX.presheaf ⟶ MY.presheaf :=
  MY.mapFrom (MX.iso.hom ≫ hilbertPresheafMap hπ hopen hsep)

/-- The morphism of models is the morphism of Hilbert functors: on a section of the model of
`Hilb_{X/A}` it takes the image of the corresponding family. -/
theorem familyEquiv_hilbertModelMap (MX : HilbertPresheafModel bX)
    (MY : HilbertPresheafModel bY) (T : BigFppfOver B S hS)
    (z : MX.presheaf.obj (Opposite.op T)) :
    MY.familyEquiv T ((hilbertModelMap hπ hopen hsep MX MY).app (Opposite.op T) z) =
      hilbertFamilyOverImage hπ hopen hsep T (MX.familyEquiv T z) :=
  types_congr_hom (MY.iso.inv_hom_id_app (Opposite.op T))
    ((MX.iso.hom ≫ hilbertPresheafMap hπ hopen hsep).app (Opposite.op T) (ULift.up z))

/-- The morphism of models induced by an open immersion over the base is a monomorphism. -/
theorem mono_hilbertModelMap (MX : HilbertPresheafModel bX) (MY : HilbertPresheafModel bY) :
    Mono (hilbertModelMap hπ hopen hsep MX MY) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  rw [mono_iff_injective]
  intro a b hab
  have h := congrArg (MY.familyEquiv T.unop) hab
  rw [familyEquiv_hilbertModelMap, familyEquiv_hilbertModelMap] at h
  exact (MX.familyEquiv T.unop).injective
    (hilbertFamilyOverImage_injective hπ hopen hsep T.unop h)

/-- A section of the model of `Hilb_{Y/A}` is in the image of the induced morphism exactly when
the closed subspace of the family it corresponds to is contained in the image of `X_T`. -/
theorem mem_range_hilbertModelMap_iff (MX : HilbertPresheafModel bX)
    (MY : HilbertPresheafModel bY) (T : BigFppfOver B S hS)
    (z : MY.presheaf.obj (Opposite.op T)) :
    z ∈ Set.range ((hilbertModelMap hπ hopen hsep MX MY).app (Opposite.op T)) ↔
      (MY.familyEquiv T z).family.Z ≤ Subfunctor.range (schemeBaseChangeOfMap hπ
        (CostructuredArrow.mk (MY.familyEquiv T z).toBase)) := by
  rw [← exists_hilbertFamilyOverImage_iff hπ hopen hsep T (MY.familyEquiv T z)]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨MX.familyEquiv T w, (familyEquiv_hilbertModelMap hπ hopen hsep MX MY T w).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨(MX.familyEquiv T).symm x, ?_⟩
    apply (MY.familyEquiv T).injective
    rw [familyEquiv_hilbertModelMap, Equiv.apply_symm_apply, hx]

/-- The morphism of Hilbert functors induced by an open immersion `π : X ⟶ Y` of algebraic
spaces over `A`, with `Y` separated over `A`, is an open immersion, read in any models of the two
Hilbert functors. -/
@[stacks 0DPE "the induced morphism is an open immersion"]
theorem isOpenImmersion_hilbertModelMap (MX : HilbertPresheafModel bX)
    (MY : HilbertPresheafModel bY) :
    IsOpenImmersion B S hS (hilbertModelMap hπ hopen hsep MX MY) := by
  have := mono_hilbertModelMap hπ hopen hsep MX MY
  apply isOpenImmersion_of_isOpenSubspace_range_preimage
  intro T q
  set Z := MY.familyEquiv T (yonedaEquiv q) with hZ
  set Ta : SchemesOverPresheaf B S hS A := CostructuredArrow.mk Z.toBase with hTa
  have hT : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  have hXT : IsAlgebraicSpace B S hS (schemeBaseChange bX Ta) :=
    isAlgebraicSpace_schemeBaseChange bX Ta
  have hYT : IsAlgebraicSpace B S hS (schemeBaseChange bY Ta) :=
    isAlgebraicSpace_schemeBaseChange bY Ta
  have hj := isOpenImmersion_schemeBaseChangeOfMap hπ hopen Ta
  have hqq : IsClosedMorphism B S hS (Z.family.Z.ι ≫ pullback.snd bY.hom Ta.hom) :=
    isClosed_of_universallyClosed B S hS hT _ Z.family.proper.2.2
  have hEq : (Subfunctor.range (hilbertModelMap hπ hopen hsep MX MY)).preimage q =
      factorizationLocus B S hS (schemeBaseChangeOfMap hπ Ta) Z.family.Z.ι
        (Z.family.Z.ι ≫ pullback.snd bY.hom Ta.hom) := by
    ext U g
    have hqg : q.app U g = MY.presheaf.map (Quiver.Hom.op g) (yonedaEquiv q) := by
      have h := NatTrans.naturality_apply q (Quiver.Hom.op g) (𝟙 T)
      rw [yonedaEquiv_apply]
      simpa using h
    have hmono := mono_schemeBaseChangeOfMap hπ hopen
      (CostructuredArrow.mk (yoneda.map g ≫ Z.toBase))
    have hsq := (Subfunctor.isPullback_preimage
        (schemeBaseChangeMap bY (HilbertFamilyOver.restrict g Z.toBase))
        Z.family.Z).paste_vert
      (isPullback_schemeBaseChangeMap bY (HilbertFamilyOver.restrict g Z.toBase))
    set e := hsq.isoIsPullback _ _
      (IsPullback.of_hasPullback (Z.family.Z.ι ≫ pullback.snd bY.hom Ta.hom) (yoneda.map g))
      with he
    have hefst : e.hom ≫ pullback.fst (Z.family.Z.ι ≫ pullback.snd bY.hom Ta.hom)
        (yoneda.map g) =
        Z.family.Z.fromPreimage
          (schemeBaseChangeMap bY (HilbertFamilyOver.restrict g Z.toBase)) :=
      hsq.isoIsPullback_hom_fst _ _ _
    change q.app U g ∈ Set.range ((hilbertModelMap hπ hopen hsep MX MY).app U) ↔
      g ∈ (factorizationLocus B S hS (schemeBaseChangeOfMap hπ Ta) Z.family.Z.ι
        (Z.family.Z.ι ≫ pullback.snd bY.hom Ta.hom)).obj U
    rw [hqg, mem_range_hilbertModelMap_iff, HilbertPresheafModel.familyEquiv_map]
    change Z.family.Z.preimage
          (schemeBaseChangeMap bY (HilbertFamilyOver.restrict g Z.toBase)) ≤
        Subfunctor.range (schemeBaseChangeOfMap hπ
          (CostructuredArrow.mk (yoneda.map g ≫ Z.toBase))) ↔
      g ∈ (factorizationLocus B S hS (schemeBaseChangeOfMap hπ Ta) Z.family.Z.ι
        (Z.family.Z.ι ≫ pullback.snd bY.hom Ta.hom)).obj U
    rw [Subfunctor.mem_yoneda_iff,
      factorsThrough_factorizationLocus_iff B S hS hXT hYT Z.family.closed.1 hT hj
        Z.family.Z.ι hqq (isAlgebraicSpace_yoneda B S hS U.unop) (yoneda.map g),
      ← Subfunctor.factorsThrough_iff_le_range,
      factorsThrough_pullback_iff (isPullback_schemeBaseChangeOfMap_comm hπ
        (HilbertFamilyOver.restrict g Z.toBase)),
      ← Subfunctor.fromPreimage_ι]
    exact ⟨fun ⟨k, hk⟩ => ⟨e.inv ≫ k, by
        rw [Category.assoc, hk, ← hefst, Category.assoc, Iso.inv_hom_id_assoc]⟩,
      fun ⟨k, hk⟩ => ⟨e.hom ≫ k, by rw [Category.assoc, hk, ← Category.assoc, hefst]⟩⟩
  rw [hEq]
  exact isOpenSubspace_factorizationLocus B S hS hT hj _ hqq

end Model

end AlgebraicGeometry.Space

end
