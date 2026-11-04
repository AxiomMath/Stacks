module

public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.SpanOverBase
public import StacksFrontier.CategoryTheory.TwoFibreProductOver
public import StacksFrontier.Deformation.Examples.Geometric.OpenSubschemes
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSource
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Deformations of a scheme covered by two opens

Let `X` be a scheme over the residue field `k` and let `U₁`, `U₂` be two opens of `X`. A
deformation of `X` restricts to a deformation of `U₁`, to a deformation of `U₂` and to a
deformation of `U₁ ⊓ U₂`, and the two ways of reaching `U₁ ⊓ U₂` agree because both compute
the open of the total space cut out by `U₁ ⊓ U₂`. The resulting comparison functor goes from
the deformation category of `X` to the 2-fibre product
`Def_{U₁} ×_{Def_{U₁ ⊓ U₂}} Def_{U₂}` of deformation categories over `𝒞_Λ`.

In the other direction, if the two opens cover `X`, an object of that 2-fibre product is glued
back into a deformation of `X`: the two total spaces are glued along the comparison
isomorphism of their overlap charts, the glued scheme is flat over the base because flatness
is local on the source and each chart is flat, and its special fibre is `X` because being
cartesian is local on the target and each chart cuts out one of the two opens. This is the
glueing construction the proof of 0DYZ uses for the quasi-inverse of the comparison functor.

## Main definitions

* `Deformation.Examples.transportDeformationFunctor`: transport of deformations along an
  isomorphism of the scheme being deformed.
* `Deformation.Examples.openIsoPreimage`: for opens `V ≤ U` of a scheme, the identification
  of `V` with the preimage of `V` in `U`.
* `Deformation.Examples.openRestrictionLEFunctor`: restriction of deformations of an open `U`
  to deformations of a smaller open `V`.
* `Deformation.Examples.nestedOpenIso`: inside the total space of a deformation of `X`, the
  open cut out by `V` inside the open cut out by `U` is the open cut out by `V`.
* `Deformation.Examples.restrictDeformationLEIso`: restricting a deformation of `X` to `U` and
  then to `V ≤ U` gives the restriction to `V`.
* `Deformation.Examples.twoOpenComparisonFunctor`: the comparison functor from the deformation
  category of `X` to the 2-fibre product of the deformation categories of two opens over the
  deformation category of their intersection.
* `Deformation.Examples.TwoOpenDeformations`: that 2-fibre product.
* `Deformation.Examples.glueDiagram`: the two deformations with the overlap chart mapping into
  both, as a diagram of open immersions whose colimit glues them.
* `Deformation.Examples.glueScheme` and `Deformation.Examples.glueToBase`: the glued scheme and
  its structure morphism.
* `Deformation.Examples.coverOfTwoOpens`: two opens covering `X`, as an open cover of `X`.
* `Deformation.Examples.glueSpecialMap`: the special-fibre immersion of the glued scheme,
  glued from the two special-fibre immersions.
* `Deformation.Examples.glueDeformation`: the deformation of `X` glued from an object of the
  2-fibre product.
* `Deformation.Examples.restrictGlueDeformationLeft` and
  `Deformation.Examples.restrictGlueDeformationRight`: restricting the glued deformation to
  `U₁` (resp. `U₂`) gives back the chart of the datum it was glued from.
* `Deformation.Examples.GluingSituation.glueDeformation`: the same construction in
  Situation 0DYY.

## Main results

* `Deformation.Examples.restrictDeformationLEIso_hom_naturality` and
  `Deformation.Examples.restrictDeformationLEIso_inv_naturality`: the comparison of the two
  restrictions is natural in the deformation.
* `Deformation.Examples.twoOpenComparisonFunctor_comp_structureFunctor`: the comparison
  functor is strictly over `𝒞_Λ`.
* `Deformation.Examples.GluingSituation.comparisonFunctor`: the comparison functor of the
  two-open cover of Situation 0DYY.
* `Deformation.Examples.flat_glueToBase`: the glued scheme is flat over the base.
* `Deformation.Examples.glueSpecialMap_preimage_glueι₁` and
  `Deformation.Examples.glueSpecialMap_preimage_glueι₂`: each chart of the glued scheme cuts
  out the corresponding open on the special fibre.
* `Deformation.Examples.glueSpecialMap_isPullback`: the special fibre of the glued scheme
  is `X`.
* `Deformation.Examples.restrictedOpen_glueDeformation_left` and
  `Deformation.Examples.restrictedOpen_glueDeformation_right`: the open that `U₁` (resp. `U₂`)
  cuts out in the glued deformation is the corresponding chart.
* `Deformation.Examples.isPullback_of_iSup_eq_top`: a commuting square of schemes is cartesian
  as soon as it is cartesian over each member of an open cover of the target of its top edge.
* `Deformation.Examples.residueSpecMap_comp_baseSpecMap`: the closed point of the spectrum of
  an object of `𝒞_Λ` is compatible with morphisms of `𝒞_Λ`.

## Implementation notes

The total space of `restrictDeformation U P` is the open `restrictedOpen P U` of the total
space of `P`, but only up to unfolding a semireducible definition, which unification below
default transparency does not do. The morphisms `restrictDeformationι` and `nestedι` are
therefore declared with their types written through the deformations rather than through the
opens; this is the only way to pin the *middle* object of a composition, and without it
neither open-immersion instances nor `Category.assoc` apply to these composites.

No hypothesis that the two opens cover `X`, and no affineness, is used for the comparison
functor; the covering hypothesis enters in the glueing construction, which needs it both for
the open cover `coverOfTwoOpens` of `X` out of which `glueSpecialMap` is glued and for the
identification of the special fibre. No affineness is used anywhere in this file.

The glueing is Mathlib's colimit of a locally directed diagram of open immersions
(`AlgebraicGeometry.Scheme.IsLocallyDirected`), indexed by `WidePushoutShape Bool`: the
instance that a wide-pushout diagram of open immersions is locally directed makes the colimit
exist, its canonical maps open immersions, and `Scheme.IsLocallyDirected.ι_eq_ι_iff` describes
when two points of the glued scheme agree — which is what identifies the overlap of the two
charts and so pins down the special fibre. The glued scheme is a colimit, not a choice from an
existence statement.

The datum being glued is an object of the 2-fibre product, so the two deformations need not
live over literally the same object of `𝒞_Λ`: they live over the two objects identified by the
base morphism of the comparison isomorphism, and the glued deformation is taken over
`Q.y.base`, the structure morphism of the first chart being twisted by `baseSpecMap` of that
morphism. No verticality of the comparison isomorphism is used.

### What of 0DYZ is proved here

Tag 0DYZ asserts an *equivalence* `Def_X = Def_{P_1} ×_{Def_{P_12}} Def_{P_2}`. What is proved
here is the comparison functor into the 2-fibre product of the deformation categories of the
two opens, and the glueing construction of the proof's quasi-inverse on objects
(`glueDeformation`, with its flatness and its special fibre), together with the two
isomorphisms `restrictGlueDeformationLeft` and `restrictGlueDeformationRight` recovering the
charts of the datum from the glued deformation. That the comparison functor is an equivalence,
which is the assertion of the tag, is
`Deformation.Examples.isEquivalence_twoOpenComparisonFunctor` in
`StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCoverEquivalence`, where the two
chart isomorphisms are shown compatible with the comparison isomorphism of the datum and
morphisms of deformations of `X` are shown to glue from their two restrictions; the source says
only "we omit the verification". Passing from `Def_{U_i}` to `Def_{P_i}` is
`Deformation.Examples.SchemeRingDeformation.equivalenceOver`, which is unconditional:
[Stacks Project, Tag 06AD] in arbitrary order is available as
`Stacks.Thickenings.isAffine_of_isThickening`, and the ring-side form of 0DYZ, with the
deformation categories `Def_{P_i}` of the coordinate rings, is
`Deformation.Examples.GluingSituation.deformationCategories_equivalence` in
`StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCoverRings`.

## References

* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 0DYW](https://stacks.math.columbia.edu/tag/0DYW)
* [Stacks Project, Tag 0DYY](https://stacks.math.columbia.edu/tag/0DYY)
* [Stacks Project, Tag 0DYZ](https://stacks.math.columbia.edu/tag/0DYZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### Transport along an isomorphism of the scheme being deformed -/

section Transport

variable {X Y : Over (Spec (.of k))} (i : Y.left ⟶ X.left) [IsIso i]
  (hi : i ≫ X.hom = Y.hom)

/-- A deformation of `X` is a deformation of `Y` along an isomorphism `i : Y ⟶ X` over
`Spec k`: only the identification of the special fibre changes. -/
def transportDeformation (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    SchemeDeformationCategory (Λ := Λ) (k := k) Y where
  base := P.base
  scheme := P.scheme
  toBase := P.toBase
  flat := P.flat
  specialMap := i ≫ P.specialMap
  specialCartesian := by
    have hsq : IsPullback i Y.hom X.hom (𝟙 (Spec (.of k))) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hi]⟩
    simpa using hsq.paste_horiz P.specialCartesian

/-- Transporting a morphism of deformations of `X` to a morphism of deformations of `Y`. -/
def transportDeformationHom {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q) :
    transportDeformation i hi P ⟶ transportDeformation i hi Q where
  base := f.base
  map := f.map
  cartesian := f.cartesian
  special_compat := by
    change (i ≫ Q.specialMap) ≫ f.map = i ≫ P.specialMap
    rw [Category.assoc, f.special_compat]

/-- Transport along an isomorphism of the scheme being deformed, as a functor of deformation
categories over `𝒞_Λ`. -/
def transportDeformationFunctor :
    SchemeDeformationCategory (Λ := Λ) (k := k) X ⥤
      SchemeDeformationCategory (Λ := Λ) (k := k) Y where
  obj := transportDeformation i hi
  map := transportDeformationHom i hi
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Transport commutes with the projections to `𝒞_Λ`. -/
theorem transportDeformationFunctor_comp_projection :
    transportDeformationFunctor (Λ := Λ) (k := k) i hi ⋙
        schemeDeformationCategoryProjection (Λ := Λ) (k := k) Y =
      schemeDeformationCategoryProjection (Λ := Λ) (k := k) X :=
  rfl

end Transport

/-! ### An open subscheme of an open subscheme -/

/-- The inclusion of an open `U` of a scheme carries the preimage of a smaller open `V`
onto `V`. -/
theorem image_coe_preimage_of_le {Z : Scheme.{u}} {U V : Z.Opens} (h : V ≤ U) :
    (⇑U.ι) '' ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U.toScheme) = (V : Set Z) := by
  rw [show ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U.toScheme) = ⇑U.ι ⁻¹' (V : Set Z) from rfl,
    Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
  exact Set.inter_eq_left.mpr h

/-- For opens `V ≤ U` of a scheme, the open subscheme `V` is identified with the preimage of
`V` in the open subscheme `U`. -/
def openIsoPreimage {Z : Scheme.{u}} {U V : Z.Opens} (h : V ≤ U) :
    V.toScheme ≅ (U.ι ⁻¹ᵁ V).toScheme :=
  IsOpenImmersion.isoOfRangeEq V.ι ((U.ι ⁻¹ᵁ V).ι ≫ U.ι) <| by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    simp only [Scheme.Opens.range_ι]
    exact (image_coe_preimage_of_le h).symm

/-- The identification of `V` with its preimage in `U` is compatible with the inclusions of
both into the ambient scheme. -/
@[reassoc (attr := simp)]
theorem openIsoPreimage_hom_comp {Z : Scheme.{u}} {U V : Z.Opens} (h : V ≤ U) :
    (openIsoPreimage h).hom ≫ (U.ι ⁻¹ᵁ V).ι ≫ U.ι = V.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-! ### The total space of a restricted deformation -/

variable {X : Over (Spec (.of k))}

/-- The open immersion of the total space of the restriction of a deformation `P` of `X` to an
open `U` into the total space of `P`. -/
def restrictDeformationι (U : X.left.Opens) (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    (restrictDeformation U P).scheme ⟶ P.scheme :=
  (restrictedOpen P U).ι

/-- The inclusion of the total space of a restricted deformation is an open immersion. -/
instance isOpenImmersion_restrictDeformationι (U : X.left.Opens)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    IsOpenImmersion (restrictDeformationι U P) :=
  inferInstanceAs (IsOpenImmersion (restrictedOpen P U).ι)

/-- The restricted total space is the open of the total space of `P` cut out by `U`. -/
theorem range_restrictDeformationι (U : X.left.Opens)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    Set.range (restrictDeformationι U P) = ((restrictedOpen P U : P.scheme.Opens) : Set _) :=
  Scheme.Opens.range_ι _

/-- The special fibre of a restricted deformation sits inside the special fibre of the
original one. -/
@[reassoc]
theorem restrictDeformation_specialMap_comp_ι (U : X.left.Opens)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    (restrictDeformation U P).specialMap ≫ restrictDeformationι U P = U.ι ≫ P.specialMap :=
  Scheme.Hom.resLE_comp_ι P.specialMap (le_specialMap_preimage_restrictedOpen P U)

/-- Restriction of a morphism of deformations is compatible with the inclusions of the
restricted total spaces. -/
@[reassoc]
theorem restrictDeformationHom_map_comp_restrictDeformationι (U : X.left.Opens)
    {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q) :
    (restrictDeformationHom U f).map ≫ restrictDeformationι U P =
      restrictDeformationι U Q ≫ f.map :=
  restrictDeformationHom_map_comp_ι U f

/-! ### Restriction along an inclusion of opens -/

section RestrictionLE

variable {U V : X.left.Opens} (h : V ≤ U)

/-- For opens `V ≤ U` of `X`, restriction of deformations of the open subscheme `U` to
deformations of the open subscheme `V`. -/
@[sga "7 VI 4.1(d)" "partial"]
def openRestrictionLEFunctor :
    SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk (U.ι ≫ X.hom)) ⥤
      SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk (V.ι ≫ X.hom)) :=
  (openRestrictionFunctor (Over.mk (U.ι ≫ X.hom)) (U.ι ⁻¹ᵁ V)).toFunctor ⋙
    transportDeformationFunctor (openIsoPreimage h).hom (by
      change (openIsoPreimage h).hom ≫ (U.ι ⁻¹ᵁ V).ι ≫ U.ι ≫ X.hom = V.ι ≫ X.hom
      exact openIsoPreimage_hom_comp_assoc h X.hom)

/-- Restricting deformations along an inclusion of opens commutes with the projections
to `𝒞_Λ`. -/
theorem openRestrictionLEFunctor_comp_projection :
    openRestrictionLEFunctor (Λ := Λ) (k := k) h ⋙
        schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (V.ι ≫ X.hom)) =
      schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U.ι ≫ X.hom)) :=
  rfl

end RestrictionLE

/-! ### Restricting twice -/

section Nested

variable (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) {U V : X.left.Opens} (h : V ≤ U)

/-- The open immersion of the total space of the twice-restricted deformation into the total
space of the once-restricted one. -/
def nestedι :
    ((openRestrictionLEFunctor h).obj (restrictDeformation U P)).scheme ⟶
      (restrictDeformation U P).scheme :=
  (restrictedOpen (restrictDeformation U P) (U.ι ⁻¹ᵁ V)).ι

/-- The inclusion of the twice-restricted total space into the once-restricted one is an open
immersion. -/
instance isOpenImmersion_nestedι : IsOpenImmersion (nestedι P h) :=
  inferInstanceAs (IsOpenImmersion (restrictedOpen (restrictDeformation U P) (U.ι ⁻¹ᵁ V)).ι)

/-- The twice-restricted total space is the open cut out by `V` in the once-restricted one. -/
theorem range_nestedι :
    Set.range (nestedι P h) =
      ((restrictedOpen (restrictDeformation U P) (U.ι ⁻¹ᵁ V) :
        (restrictDeformation U P).scheme.Opens) : Set _) :=
  Scheme.Opens.range_ι _

/-- The structure morphism of the twice-restricted deformation. -/
theorem nested_toBase :
    ((openRestrictionLEFunctor h).obj (restrictDeformation U P)).toBase =
      nestedι P h ≫ restrictDeformationι U P ≫ P.toBase :=
  rfl

/-- The special fibre of the twice-restricted deformation is the open `V` of the special
fibre of `P`. -/
theorem nested_specialMap_comp_ι :
    ((openRestrictionLEFunctor h).obj (restrictDeformation U P)).specialMap ≫
        (nestedι P h ≫ restrictDeformationι U P) = V.ι ≫ P.specialMap := by
  have key : ((openIsoPreimage h).hom ≫
        Scheme.Hom.resLE (restrictDeformation U P).specialMap
          (restrictedOpen (restrictDeformation U P) (U.ι ⁻¹ᵁ V)) (U.ι ⁻¹ᵁ V)
          (le_specialMap_preimage_restrictedOpen (restrictDeformation U P) (U.ι ⁻¹ᵁ V))) ≫
      ((restrictedOpen (restrictDeformation U P) (U.ι ⁻¹ᵁ V)).ι ≫
        restrictDeformationι U P) = V.ι ≫ P.specialMap := by
    simp only [Category.assoc]
    rw [Scheme.Hom.resLE_comp_ι_assoc, restrictDeformation_specialMap_comp_ι,
      openIsoPreimage_hom_comp_assoc]
  exact key

/-- Inside the total space of a deformation `P` of `X`, the open cut out by `V ≤ U` inside the
open cut out by `U` is the open cut out by `V`. -/
def nestedOpenIso :
    ((openRestrictionLEFunctor h).obj (restrictDeformation U P)).scheme ≅
      (restrictDeformation V P).scheme :=
  IsOpenImmersion.isoOfRangeEq (nestedι P h ≫ restrictDeformationι U P)
      (restrictDeformationι V P) <| by
    have hpt : ∀ x : U.toScheme,
        restrictDeformationι U P ((restrictDeformation U P).specialMap x) =
          P.specialMap (U.ι x) := fun x => by
      simpa using congrArg (fun m : U.toScheme ⟶ P.scheme => m x)
        (restrictDeformation_specialMap_comp_ι U P)
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_nestedι,
      range_restrictDeformationι]
    calc (⇑(restrictDeformationι U P)) ''
          ((⇑(restrictDeformation U P).specialMap) ''
            ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U.toScheme))
        = (fun x => (restrictDeformationι U P) ((restrictDeformation U P).specialMap x)) ''
            ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U.toScheme) := Set.image_image _ _ _
      _ = (fun x => P.specialMap (U.ι x)) ''
            ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U.toScheme) := Set.image_congr' hpt
      _ = (⇑P.specialMap) ''
            ((⇑U.ι) '' ((U.ι ⁻¹ᵁ V : U.toScheme.Opens) : Set U.toScheme)) :=
          (Set.image_image _ _ _).symm
      _ = (⇑P.specialMap) '' (V : Set X.left) := by rw [image_coe_preimage_of_le h]

/-- The identification of the twice-restricted open with the open cut out by `V`, as a
statement about the inclusions into the total space of `P`. -/
@[reassoc (attr := simp)]
theorem nestedOpenIso_hom_comp :
    (nestedOpenIso P h).hom ≫ restrictDeformationι V P =
      nestedι P h ≫ restrictDeformationι U P :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The inverse identification, as a statement about the inclusions into the total space
of `P`. -/
@[reassoc (attr := simp)]
theorem nestedOpenIso_inv_comp :
    (nestedOpenIso P h).inv ≫ nestedι P h ≫ restrictDeformationι U P =
      restrictDeformationι V P := by
  rw [← nestedOpenIso_hom_comp P h, Iso.inv_hom_id_assoc]

/-- **Restricting twice is restricting once.** Restricting a deformation of `X` to an open `U`
and then to a smaller open `V` is the restriction of that deformation to `V`. -/
def restrictDeformationLEIso :
    (openRestrictionLEFunctor h).obj (restrictDeformation U P) ≅ restrictDeformation V P where
  hom :=
    { base := 𝟙 P.base
      map := (nestedOpenIso P h).inv
      cartesian := by
        change IsPullback (nestedOpenIso P h).inv (restrictDeformationι V P ≫ P.toBase)
          (nestedι P h ≫ restrictDeformationι U P ≫ P.toBase) (baseSpecMap (𝟙 P.base))
        rw [baseSpecMap_id]
        refine IsPullback.of_horiz_isIso ⟨?_⟩
        rw [Category.comp_id, nestedOpenIso_inv_comp_assoc]
      special_compat := by
        have h₁ : (restrictDeformation V P).specialMap ≫
            (nestedOpenIso P h).inv ≫ nestedι P h ≫ restrictDeformationι U P =
            V.ι ≫ P.specialMap := by
          rw [nestedOpenIso_inv_comp, restrictDeformation_specialMap_comp_ι]
        refine (cancel_mono (nestedι P h ≫ restrictDeformationι U P)).mp ?_
        rw [Category.assoc, h₁, nested_specialMap_comp_ι] }
  inv :=
    { base := 𝟙 P.base
      map := (nestedOpenIso P h).hom
      cartesian := by
        change IsPullback (nestedOpenIso P h).hom
          (nestedι P h ≫ restrictDeformationι U P ≫ P.toBase)
          (restrictDeformationι V P ≫ P.toBase) (baseSpecMap (𝟙 P.base))
        rw [baseSpecMap_id]
        refine IsPullback.of_horiz_isIso ⟨?_⟩
        rw [Category.comp_id, nestedOpenIso_hom_comp_assoc]
      special_compat := by
        have h₁ : ((openRestrictionLEFunctor h).obj (restrictDeformation U P)).specialMap ≫
            (nestedOpenIso P h).hom ≫ restrictDeformationι V P = V.ι ≫ P.specialMap := by
          rw [nestedOpenIso_hom_comp, nested_specialMap_comp_ι]
        refine (cancel_mono (restrictDeformationι V P)).mp ?_
        rw [Category.assoc, h₁, restrictDeformation_specialMap_comp_ι] }
  hom_inv_id := by
    refine SchemeDeformationCategory.Hom.ext ?_ ?_
    · change 𝟙 P.base ≫ 𝟙 P.base = 𝟙 P.base
      rw [Category.id_comp]
    · change (nestedOpenIso P h).hom ≫ (nestedOpenIso P h).inv =
        𝟙 ((openRestrictionLEFunctor h).obj (restrictDeformation U P)).scheme
      rw [Iso.hom_inv_id]
  inv_hom_id := by
    refine SchemeDeformationCategory.Hom.ext ?_ ?_
    · change 𝟙 P.base ≫ 𝟙 P.base = 𝟙 P.base
      rw [Category.id_comp]
    · change (nestedOpenIso P h).inv ≫ (nestedOpenIso P h).hom =
        𝟙 (restrictDeformation V P).scheme
      rw [Iso.inv_hom_id]

end Nested

/-! ### Naturality of the comparison -/

section Naturality

variable {U V : X.left.Opens} (h : V ≤ U)
  {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q)

/-- The inclusions of the twice-restricted total spaces are natural in the deformation. -/
theorem nestedι_naturality :
    ((openRestrictionLEFunctor h).map (restrictDeformationHom U f)).map ≫
        (nestedι P h ≫ restrictDeformationι U P) =
      (nestedι Q h ≫ restrictDeformationι U Q) ≫ f.map := by
  have key : Scheme.Hom.resLE (restrictDeformationHom U f).map
        (restrictedOpen (restrictDeformation U P) (U.ι ⁻¹ᵁ V))
        (restrictedOpen (restrictDeformation U Q) (U.ι ⁻¹ᵁ V))
        (le_map_preimage_restrictedOpen (restrictDeformationHom U f)) ≫
      ((restrictedOpen (restrictDeformation U P) (U.ι ⁻¹ᵁ V)).ι ≫ restrictDeformationι U P) =
      ((restrictedOpen (restrictDeformation U Q) (U.ι ⁻¹ᵁ V)).ι ≫
        restrictDeformationι U Q) ≫ f.map := by
    rw [Scheme.Hom.resLE_comp_ι_assoc,
      restrictDeformationHom_map_comp_restrictDeformationι, Category.assoc]
  exact key

/-- The comparison of restricting twice with restricting once is natural in the
deformation. -/
theorem restrictDeformationLEIso_hom_naturality :
    (openRestrictionLEFunctor h).map (restrictDeformationHom U f) ≫
        (restrictDeformationLEIso Q h).hom =
      (restrictDeformationLEIso P h).hom ≫ restrictDeformationHom V f := by
  refine SchemeDeformationCategory.Hom.ext ?_ ?_
  · show f.base ≫ 𝟙 Q.base = 𝟙 P.base ≫ f.base
    rw [Category.comp_id, Category.id_comp]
  · show (nestedOpenIso Q h).inv ≫
        ((openRestrictionLEFunctor h).map (restrictDeformationHom U f)).map =
      (restrictDeformationHom V f).map ≫ (nestedOpenIso P h).inv
    refine (cancel_mono (nestedι P h ≫ restrictDeformationι U P)).mp ?_
    rw [Category.assoc, nestedι_naturality, ← Category.assoc, nestedOpenIso_inv_comp,
      Category.assoc, nestedOpenIso_inv_comp,
      restrictDeformationHom_map_comp_restrictDeformationι]

/-- The inverse comparison of restricting twice with restricting once is natural in the
deformation. -/
theorem restrictDeformationLEIso_inv_naturality :
    restrictDeformationHom V f ≫ (restrictDeformationLEIso Q h).inv =
      (restrictDeformationLEIso P h).inv ≫
        (openRestrictionLEFunctor h).map (restrictDeformationHom U f) := by
  rw [Iso.comp_inv_eq, Category.assoc, restrictDeformationLEIso_hom_naturality h f,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end Naturality

/-! ### The comparison functor of a two-open cover -/

/-- Let `X` be a scheme over `k` with two opens `U₁` and `U₂`. Restricting a deformation of `X`
to `U₁` and to `U₂`, together with the identification of the two induced deformations of
`U₁ ⊓ U₂`, is a functor from the deformation category of `X` to the 2-fibre product
`Def_{U₁} ×_{Def_{U₁ ⊓ U₂}} Def_{U₂}` over `𝒞_Λ`. -/
@[stacks 0DYZ "the comparison functor Def_X ⥤ Def_{U_1} ×_{Def_{U_12}} Def_{U_2} only; it is \
not shown to be an equivalence (that needs the glueing quasi-inverse of the proof) and the \
translation into the ring deformation categories Def_{P_i} is not included"]
def twoOpenComparisonFunctor (X : Over (Spec (.of k))) (U₁ U₂ : X.left.Opens) :
    SchemeDeformationCategory (Λ := Λ) (k := k) X ⥤
      TwoFibreProductOver
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U₁.ι ≫ X.hom)))
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U₂.ι ≫ X.hom)))
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk ((U₁ ⊓ U₂).ι ≫ X.hom)))
        (openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
        (openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) where
  obj P :=
    { base := P.base
      x := restrictDeformation U₁ P
      y := restrictDeformation U₂ P
      hx := rfl
      hy := rfl
      iso := restrictDeformationLEIso P inf_le_left ≪≫
        (restrictDeformationLEIso P inf_le_right).symm
      vertical := by
        refine IsHomLift.of_fac' _ (𝟙 P.base) _ rfl rfl ?_
        change (𝟙 P.base ≫ 𝟙 P.base : P.base ⟶ P.base) =
          eqToHom (rfl : P.base = P.base) ≫ 𝟙 P.base ≫ eqToHom (rfl : P.base = P.base)
        simp }
  map := fun {P Q} f =>
    { hbase := f.base
      a := restrictDeformationHom U₁ f
      b := restrictDeformationHom U₂ f
      ha := by
        refine IsHomLift.of_fac' _ f.base _ rfl rfl ?_
        change f.base = eqToHom (rfl : P.base = P.base) ≫ f.base ≫
          eqToHom (rfl : Q.base = Q.base)
        simp
      hb := by
        refine IsHomLift.of_fac' _ f.base _ rfl rfl ?_
        change f.base = eqToHom (rfl : P.base = P.base) ≫ f.base ≫
          eqToHom (rfl : Q.base = Q.base)
        simp
      w := by
        simp only [Iso.trans_hom, Iso.symm_hom]
        rw [← Category.assoc, restrictDeformationLEIso_hom_naturality, Category.assoc,
          Category.assoc, restrictDeformationLEIso_inv_naturality] }
  map_id P := TwoFibreProductOver.Hom.ext'
    ((openRestrictionFunctor X U₁).toFunctor.map_id P)
    ((openRestrictionFunctor X U₂).toFunctor.map_id P)
  map_comp := fun f g => TwoFibreProductOver.Hom.ext'
    ((openRestrictionFunctor X U₁).toFunctor.map_comp f g)
    ((openRestrictionFunctor X U₂).toFunctor.map_comp f g)

/-- The comparison functor of a two-open cover is strictly over `𝒞_Λ`. -/
@[stacks 0DYZ "the comparison functor Def_X ⥤ Def_{U_1} ×_{Def_{U_12}} Def_{U_2} is a \
functor over 𝒞_Λ; it is not shown to be an equivalence and the ring deformation categories \
Def_{P_i} are not involved"]
theorem twoOpenComparisonFunctor_comp_structureFunctor (X : Over (Spec (.of k)))
    (U₁ U₂ : X.left.Opens) :
    twoOpenComparisonFunctor (Λ := Λ) (k := k) X U₁ U₂ ⋙
        TwoFibreProductOver.structureFunctor
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U₁.ι ≫ X.hom)))
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U₂.ι ≫ X.hom)))
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k)
            (Over.mk ((U₁ ⊓ U₂).ι ≫ X.hom)))
          (openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
          (openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) =
      schemeDeformationCategoryProjection (Λ := Λ) (k := k) X :=
  rfl

/-- The comparison functor of the two-open cover of a glueing situation. -/
@[stacks 0DYZ "the comparison functor in Situation 0DYY; it is not shown to be an \
equivalence and the translation into the ring deformation categories Def_{P_i} is not \
included"]
def GluingSituation.comparisonFunctor (S : GluingSituation Λ k) :
    SchemeDeformationCategory (Λ := Λ) (k := k) S.X ⥤
      TwoFibreProductOver
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (S.U₁.ι ≫ S.X.hom)))
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (S.U₂.ι ≫ S.X.hom)))
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k)
          (Over.mk ((S.U₁ ⊓ S.U₂).ι ≫ S.X.hom)))
        (openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_left : S.U₁ ⊓ S.U₂ ≤ S.U₁))
        (openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_right : S.U₁ ⊓ S.U₂ ≤ S.U₂)) :=
  twoOpenComparisonFunctor S.X S.U₁ S.U₂

/-! ### The glueing quasi-inverse -/

section QuasiInverse

/-- The closed point of the spectrum of an object of `𝒞_Λ` is compatible with morphisms. -/
theorem residueSpecMap_comp_baseSpecMap {A B : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ B) :
    residueSpecMap B ≫ baseSpecMap f = residueSpecMap A :=
  residueSpecMap_naturality f

/-- A commuting square of schemes is cartesian as soon as it becomes cartesian over each
member of an open cover of the target of its top edge. -/
theorem isPullback_of_iSup_eq_top {Y Z S T : Scheme.{u}} {f : Y ⟶ Z} {g : Y ⟶ T}
    {p : Z ⟶ S} {r : T ⟶ S} (w : f ≫ p = g ≫ r)
    {ι : Type*} (O : ι → Z.Opens) (hO : iSup O = ⊤)
    (h : ∀ i, IsPullback (f ∣_ O i) ((f ⁻¹ᵁ O i).ι ≫ g) ((O i).ι ≫ p) r) :
    IsPullback f g p r := by
  have hPB : IsPullback (pullback.fst p r) (pullback.snd p r) p r := IsPullback.of_hasPullback p r
  set φ : Y ⟶ pullback p r := pullback.lift f g w with hφ
  have hφ₁ : φ ≫ pullback.fst p r = f := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd p r = g := pullback.lift_snd _ _ _
  have hiso : IsIso φ := by
    show (MorphismProperty.isomorphisms Scheme) φ
    refine IsZariskiLocalAtTarget.of_iSup_eq_top
      (fun i => pullback.fst p r ⁻¹ᵁ O i) (Scheme.Hom.iSup_preimage_eq_top _ hO) ?_
    intro i
    have e₁ : φ ⁻¹ᵁ (pullback.fst p r ⁻¹ᵁ O i) = f ⁻¹ᵁ O i := by
      rw [← hφ₁]; rfl
    have PB2 : IsPullback (pullback.fst p r ∣_ O i)
        ((pullback.fst p r ⁻¹ᵁ O i).ι ≫ pullback.snd p r) ((O i).ι ≫ p) r :=
      (isPullback_morphismRestrict (pullback.fst p r) (O i)).paste_vert hPB
    set d := (h i).isoIsPullback _ _ PB2 with hd
    have key : φ ∣_ (pullback.fst p r ⁻¹ᵁ O i) = (Y.isoOfEq e₁).hom ≫ d.hom := by
      refine PB2.hom_ext ?_ ?_
      · rw [Category.assoc, IsPullback.isoIsPullback_hom_fst, ← cancel_mono (O i).ι]
        simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
          Scheme.isoOfEq_hom_ι_assoc, hφ₁]
      · rw [Category.assoc, IsPullback.isoIsPullback_hom_snd]
        simp only [morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc, hφ₂]
    show IsIso (φ ∣_ _)
    rw [key]
    infer_instance
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso φ) hφ₁ hφ₂

/-- The 2-fibre product `Def_{U₁} ×_{Def_{U₁ ⊓ U₂}} Def_{U₂}` over `𝒞_Λ`. -/
abbrev TwoOpenDeformations (X : Over (Spec (.of k))) (U₁ U₂ : X.left.Opens) :=
  TwoFibreProductOver
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U₁.ι ≫ X.hom)))
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U₂.ι ≫ X.hom)))
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk ((U₁ ⊓ U₂).ι ≫ X.hom)))
    (openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
    (openRestrictionLEFunctor (Λ := Λ) (k := k) (inf_le_right : U₁ ⊓ U₂ ≤ U₂))

variable (X) (U₁ U₂ : X.left.Opens) (Q : TwoOpenDeformations (Λ := Λ) X U₁ U₂)

/-- The open immersion of the overlap chart of the first deformation into it. -/
def glueOverlapι₁ :
    ((openRestrictionLEFunctor (Λ := Λ) (k := k)
      (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).obj Q.x).scheme ⟶ Q.x.scheme :=
  (restrictedOpen Q.x (U₁.ι ⁻¹ᵁ (U₁ ⊓ U₂))).ι

/-- The open immersion of the overlap chart of the second deformation into it. -/
def glueOverlapι₂ :
    ((openRestrictionLEFunctor (Λ := Λ) (k := k)
      (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).obj Q.y).scheme ⟶ Q.y.scheme :=
  (restrictedOpen Q.y (U₂.ι ⁻¹ᵁ (U₁ ⊓ U₂))).ι

/-- The inclusion of the overlap chart into the first deformation is an open immersion. -/
instance isOpenImmersion_glueOverlapι₁ : IsOpenImmersion (glueOverlapι₁ X U₁ U₂ Q) :=
  inferInstanceAs (IsOpenImmersion (restrictedOpen Q.x (U₁.ι ⁻¹ᵁ (U₁ ⊓ U₂))).ι)

/-- The inclusion of the overlap chart into the second deformation is an open immersion. -/
instance isOpenImmersion_glueOverlapι₂ : IsOpenImmersion (glueOverlapι₂ X U₁ U₂ Q) :=
  inferInstanceAs (IsOpenImmersion (restrictedOpen Q.y (U₂.ι ⁻¹ᵁ (U₁ ⊓ U₂))).ι)

/-- The overlap chart of the first deformation is the open cut out by `U₁ ⊓ U₂`. -/
theorem range_glueOverlapι₁ : Set.range (glueOverlapι₁ X U₁ U₂ Q) =
    ((restrictedOpen Q.x (U₁.ι ⁻¹ᵁ (U₁ ⊓ U₂)) : Q.x.scheme.Opens) : Set Q.x.scheme) :=
  Scheme.Opens.range_ι _

/-- The overlap chart of the second deformation is the open cut out by `U₁ ⊓ U₂`. -/
theorem range_glueOverlapι₂ : Set.range (glueOverlapι₂ X U₁ U₂ Q) =
    ((restrictedOpen Q.y (U₂.ι ⁻¹ᵁ (U₁ ⊓ U₂)) : Q.y.scheme.Opens) : Set Q.y.scheme) :=
  Scheme.Opens.range_ι _

/-- The special fibre of the open of a deformation of `U` cut out by `V ≤ U` is `V` inside the
special fibre. -/
private theorem specialMap_restrictedOpen_ι_comp {W : Over (Spec (.of k))}
    {U V : W.left.Opens} (h : V ≤ U)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk (U.ι ≫ W.hom))) :
    ((openRestrictionLEFunctor (Λ := Λ) (k := k) h).obj P).specialMap ≫
        (restrictedOpen P (U.ι ⁻¹ᵁ V)).ι = W.left.homOfLE h ≫ P.specialMap := by
  have hm : (openIsoPreimage h).hom ≫ (U.ι ⁻¹ᵁ V).ι = W.left.homOfLE h := by
    rw [← cancel_mono U.ι, Category.assoc, openIsoPreimage_hom_comp, Scheme.homOfLE_ι]
  have key : ((openIsoPreimage h).hom ≫
      Scheme.Hom.resLE P.specialMap (restrictedOpen P (U.ι ⁻¹ᵁ V)) (U.ι ⁻¹ᵁ V)
        (le_specialMap_preimage_restrictedOpen P (U.ι ⁻¹ᵁ V))) ≫
      (restrictedOpen P (U.ι ⁻¹ᵁ V)).ι = W.left.homOfLE h ≫ P.specialMap := by
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hm]
  exact key

/-- The special fibre of the overlap chart of the first deformation is `U₁ ⊓ U₂` inside the
special fibre of the first deformation. -/
theorem glueOverlap_specialMap_comp_ι₁ :
    ((openRestrictionLEFunctor (Λ := Λ) (k := k)
        (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).obj Q.x).specialMap ≫ glueOverlapι₁ X U₁ U₂ Q =
      X.left.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫ Q.x.specialMap :=
  specialMap_restrictedOpen_ι_comp _ Q.x

/-- The special fibre of the overlap chart of the second deformation is `U₁ ⊓ U₂` inside the
special fibre of the second deformation. -/
theorem glueOverlap_specialMap_comp_ι₂ :
    ((openRestrictionLEFunctor (Λ := Λ) (k := k)
        (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).obj Q.y).specialMap ≫ glueOverlapι₂ X U₁ U₂ Q =
      X.left.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂) ≫ Q.y.specialMap :=
  specialMap_restrictedOpen_ι_comp _ Q.y

/-- The transition isomorphism between the two overlap charts. -/
def glueTransition :
    ((openRestrictionLEFunctor (Λ := Λ) (k := k)
        (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).obj Q.x).scheme ⟶
      ((openRestrictionLEFunctor (Λ := Λ) (k := k)
        (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).obj Q.y).scheme :=
  Q.iso.inv.map

/-- The transition morphism between the two overlap charts is an isomorphism. -/
instance isIso_glueTransition : IsIso (glueTransition X U₁ U₂ Q) :=
  ⟨Q.iso.hom.map, congrArg SchemeDeformationCategory.Hom.map Q.iso.hom_inv_id,
    congrArg SchemeDeformationCategory.Hom.map Q.iso.inv_hom_id⟩

/-- The isomorphism of bases underlying the transition isomorphism. -/
def glueBaseIso : Q.y.base ⟶ Q.x.base := Q.iso.inv.base

/-- The morphism of bases underlying the transition isomorphism is an isomorphism. -/
instance isIso_glueBaseIso : IsIso (glueBaseIso X U₁ U₂ Q) :=
  ⟨Q.iso.hom.base, congrArg SchemeDeformationCategory.Hom.base Q.iso.inv_hom_id,
    congrArg SchemeDeformationCategory.Hom.base Q.iso.hom_inv_id⟩

/-- The transition isomorphism is compatible with the two structure morphisms. -/
theorem glueTransition_comp_toBase :
    glueTransition X U₁ U₂ Q ≫ glueOverlapι₂ X U₁ U₂ Q ≫ Q.y.toBase =
      (glueOverlapι₁ X U₁ U₂ Q ≫ Q.x.toBase) ≫ baseSpecMap (glueBaseIso X U₁ U₂ Q) :=
  Q.iso.inv.cartesian.w

/-- The transition isomorphism is compatible with the two special fibres. -/
theorem glueTransition_specialMap :
    ((openRestrictionLEFunctor (Λ := Λ) (k := k)
        (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).obj Q.x).specialMap ≫ glueTransition X U₁ U₂ Q =
      ((openRestrictionLEFunctor (Λ := Λ) (k := k)
        (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).obj Q.y).specialMap :=
  Q.iso.inv.special_compat

/-! ### The glued scheme -/

/-- The glueing diagram: the two deformations, with the overlap chart mapping into both. This is
`AlgebraicGeometry.SpanGlue.diagram` for the span `Q.x ⟵ Q.x|_{U₁ ⊓ U₂} ⟶ Q.y`, the second leg
taken through the transition isomorphism. -/
def glueDiagram : WidePushoutShape Bool ⥤ Scheme.{u} :=
  AlgebraicGeometry.SpanGlue.diagram (glueOverlapι₁ X U₁ U₂ Q)
    (glueTransition X U₁ U₂ Q ≫ glueOverlapι₂ X U₁ U₂ Q)

/-- Every map of the glueing diagram is an open immersion. -/
instance isOpenImmersion_glueDiagram_map :
    ∀ {i j : WidePushoutShape Bool} (f : i ⟶ j),
      IsOpenImmersion ((glueDiagram X U₁ U₂ Q).map f) :=
  AlgebraicGeometry.SpanGlue.isOpenImmersion_diagram_map _ _

/-- The scheme glued from the two deformations along the transition isomorphism. -/
def glueScheme : Scheme.{u} :=
  AlgebraicGeometry.SpanGlue.glued (glueOverlapι₁ X U₁ U₂ Q)
    (glueTransition X U₁ U₂ Q ≫ glueOverlapι₂ X U₁ U₂ Q)

/-- The first deformation as an open subscheme of the glued scheme. -/
def glueι₁ : Q.x.scheme ⟶ glueScheme X U₁ U₂ Q :=
  AlgebraicGeometry.SpanGlue.ι₁ (glueOverlapι₁ X U₁ U₂ Q)
    (glueTransition X U₁ U₂ Q ≫ glueOverlapι₂ X U₁ U₂ Q)

/-- The second deformation as an open subscheme of the glued scheme. -/
def glueι₂ : Q.y.scheme ⟶ glueScheme X U₁ U₂ Q :=
  AlgebraicGeometry.SpanGlue.ι₂ (glueOverlapι₁ X U₁ U₂ Q)
    (glueTransition X U₁ U₂ Q ≫ glueOverlapι₂ X U₁ U₂ Q)

/-- The overlap chart as an open subscheme of the glued scheme. -/
def glueι₀ :
    ((openRestrictionLEFunctor (Λ := Λ) (k := k)
      (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).obj Q.x).scheme ⟶ glueScheme X U₁ U₂ Q :=
  colimit.ι (glueDiagram X U₁ U₂ Q) none

/-- The first chart of the glued scheme is an open immersion. -/
instance isOpenImmersion_glueι₁ : IsOpenImmersion (glueι₁ X U₁ U₂ Q) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (glueDiagram X U₁ U₂ Q) (some false)))

/-- The second chart of the glued scheme is an open immersion. -/
instance isOpenImmersion_glueι₂ : IsOpenImmersion (glueι₂ X U₁ U₂ Q) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (glueDiagram X U₁ U₂ Q) (some true)))

/-- The overlap chart included through the first deformation is the overlap chart of the glued
scheme. -/
@[reassoc]
theorem glueOverlapι₁_comp_glueι₁ :
    glueOverlapι₁ X U₁ U₂ Q ≫ glueι₁ X U₁ U₂ Q = glueι₀ X U₁ U₂ Q :=
  colimit.w (glueDiagram X U₁ U₂ Q) (WidePushoutShape.Hom.init false)

/-- The overlap chart included through the transition isomorphism and the second deformation is
the overlap chart of the glued scheme. -/
@[reassoc]
theorem glueOverlapι₂_comp_glueι₂ :
    glueTransition X U₁ U₂ Q ≫ glueOverlapι₂ X U₁ U₂ Q ≫ glueι₂ X U₁ U₂ Q =
      glueι₀ X U₁ U₂ Q :=
  (Category.assoc _ _ _).symm.trans
    (colimit.w (glueDiagram X U₁ U₂ Q) (WidePushoutShape.Hom.init true))

/-- The structure morphism of the glued scheme: `AlgebraicGeometry.SpanGlue.desc` applied to the
two structure morphisms, which agree on the overlap by `glueTransition_comp_toBase`. -/
def glueToBase : glueScheme X U₁ U₂ Q ⟶ baseSpec Q.y.base :=
  AlgebraicGeometry.SpanGlue.desc (glueOverlapι₁ X U₁ U₂ Q)
    (glueTransition X U₁ U₂ Q ≫ glueOverlapι₂ X U₁ U₂ Q)
    (Q.x.toBase ≫ baseSpecMap (glueBaseIso X U₁ U₂ Q)) Q.y.toBase
    (by simpa using (glueTransition_comp_toBase X U₁ U₂ Q).symm)

/-- On the first chart, the structure morphism of the glued scheme is that of the first
deformation followed by the isomorphism of bases. -/
@[reassoc (attr := simp)]
theorem glueι₁_comp_glueToBase :
    glueι₁ X U₁ U₂ Q ≫ glueToBase X U₁ U₂ Q =
      Q.x.toBase ≫ baseSpecMap (glueBaseIso X U₁ U₂ Q) :=
  AlgebraicGeometry.SpanGlue.ι₁_desc _ _ _ _ _

/-- On the second chart, the structure morphism of the glued scheme is that of the second
deformation. -/
@[reassoc (attr := simp)]
theorem glueι₂_comp_glueToBase :
    glueι₂ X U₁ U₂ Q ≫ glueToBase X U₁ U₂ Q = Q.y.toBase :=
  AlgebraicGeometry.SpanGlue.ι₂_desc _ _ _ _ _

/-- The two charts cover the glued scheme. -/
theorem glueι_opensRange_sup_eq_top :
    (glueι₁ X U₁ U₂ Q).opensRange ⊔ (glueι₂ X U₁ U₂ Q).opensRange = ⊤ :=
  AlgebraicGeometry.SpanGlue.opensRange_ι₁_sup_opensRange_ι₂ _ _

/-- The glued scheme is flat over the base. -/
theorem flat_glueToBase : Flat (glueToBase X U₁ U₂ Q) := by
  have : Flat Q.x.toBase := Q.x.flat
  have : Flat Q.y.toBase := Q.y.flat
  exact AlgebraicGeometry.SpanGlue.flat_desc _ _ _ _ _

/-! ### The special fibre of the glued scheme -/

variable (hcover : U₁ ⊔ U₂ = ⊤)

/-- Two opens covering `X`, as an open cover of `X`. -/
def coverOfTwoOpens : X.left.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b => bif b then U₂.toScheme else U₁.toScheme)
    (fun b => Bool.rec U₁.ι U₂.ι b)
    (fun x => by
      have hx : x ∈ U₁ ⊔ U₂ := by rw [hcover]; trivial
      rcases hx with h | h
      · exact ⟨false, ⟨x, h⟩, rfl⟩
      · exact ⟨true, ⟨x, h⟩, rfl⟩)
    (fun b => by cases b <;> exact inferInstance)

/-- The two special-fibre immersions agree on the overlap. -/
theorem glueSpecialMap_compat :
    pullback.fst U₁.ι U₂.ι ≫ Q.x.specialMap ≫ glueι₁ X U₁ U₂ Q =
      pullback.snd U₁.ι U₂.ι ≫ Q.y.specialMap ≫ glueι₂ X U₁ U₂ Q := by
  have key : X.left.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫ Q.x.specialMap ≫
        glueι₁ X U₁ U₂ Q =
      X.left.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂) ≫ Q.y.specialMap ≫
        glueι₂ X U₁ U₂ Q := by
    rw [← Category.assoc, ← glueOverlap_specialMap_comp_ι₁, Category.assoc,
      glueOverlapι₁_comp_glueι₁, ← Category.assoc, ← glueOverlap_specialMap_comp_ι₂,
      Category.assoc, ← glueTransition_specialMap, Category.assoc,
      glueOverlapι₂_comp_glueι₂]
  rw [← cancel_epi (isPullback_opens_inf U₁ U₂).isoPullback.hom]
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]
  simpa only [Category.assoc] using key

/-- The special-fibre immersion of the glued deformation: the two special-fibre immersions
glued along the open cover of `X`. -/
def glueSpecialMap : X.left ⟶ glueScheme X U₁ U₂ Q :=
  (coverOfTwoOpens X U₁ U₂ hcover).glueMorphisms
    (fun b => Bool.rec (Q.x.specialMap ≫ glueι₁ X U₁ U₂ Q)
      (Q.y.specialMap ≫ glueι₂ X U₁ U₂ Q) b)
    (by
      intro b b'
      cases b <;> cases b'
      · change pullback.fst U₁.ι U₁.ι ≫ _ = pullback.snd U₁.ι U₁.ι ≫ _
        rw [(cancel_mono U₁.ι).mp (pullback.condition (f := U₁.ι) (g := U₁.ι))]
      · change pullback.fst U₁.ι U₂.ι ≫ Q.x.specialMap ≫ glueι₁ X U₁ U₂ Q =
          pullback.snd U₁.ι U₂.ι ≫ Q.y.specialMap ≫ glueι₂ X U₁ U₂ Q
        exact glueSpecialMap_compat X U₁ U₂ Q
      · change pullback.fst U₂.ι U₁.ι ≫ Q.y.specialMap ≫ glueι₂ X U₁ U₂ Q =
          pullback.snd U₂.ι U₁.ι ≫ Q.x.specialMap ≫ glueι₁ X U₁ U₂ Q
        rw [← cancel_epi (pullbackSymmetry U₁.ι U₂.ι).hom]
        simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst,
          pullbackSymmetry_hom_comp_snd]
        simpa only [Category.assoc] using (glueSpecialMap_compat X U₁ U₂ Q).symm
      · change pullback.fst U₂.ι U₂.ι ≫ _ = pullback.snd U₂.ι U₂.ι ≫ _
        rw [(cancel_mono U₂.ι).mp (pullback.condition (f := U₂.ι) (g := U₂.ι))])

/-- On `U₁`, the special-fibre immersion of the glued deformation is that of the first
deformation followed by the first chart. -/
@[reassoc]
theorem glueSpecialMap_comp₁ :
    U₁.ι ≫ glueSpecialMap X U₁ U₂ Q hcover = Q.x.specialMap ≫ glueι₁ X U₁ U₂ Q :=
  (coverOfTwoOpens X U₁ U₂ hcover).ι_glueMorphisms _ _ false

/-- On `U₂`, the special-fibre immersion of the glued deformation is that of the second
deformation followed by the second chart. -/
@[reassoc]
theorem glueSpecialMap_comp₂ :
    U₂.ι ≫ glueSpecialMap X U₁ U₂ Q hcover = Q.y.specialMap ≫ glueι₂ X U₁ U₂ Q :=
  (coverOfTwoOpens X U₁ U₂ hcover).ι_glueMorphisms _ _ true

/-- The special-fibre immersion of the glued deformation lies over the closed point. -/
theorem glueSpecialMap_comp_glueToBase :
    glueSpecialMap X U₁ U₂ Q hcover ≫ glueToBase X U₁ U₂ Q =
      X.hom ≫ residueSpecMap Q.y.base := by
  refine (coverOfTwoOpens X U₁ U₂ hcover).hom_ext _ _ ?_
  intro b
  cases b
  · show U₁.ι ≫ glueSpecialMap X U₁ U₂ Q hcover ≫ glueToBase X U₁ U₂ Q =
      U₁.ι ≫ X.hom ≫ residueSpecMap Q.y.base
    rw [glueSpecialMap_comp₁_assoc, glueι₁_comp_glueToBase, ← Category.assoc,
      Q.x.specialCartesian.w, Category.assoc, residueSpecMap_comp_baseSpecMap]
    rfl
  · show U₂.ι ≫ glueSpecialMap X U₁ U₂ Q hcover ≫ glueToBase X U₁ U₂ Q =
      U₂.ι ≫ X.hom ≫ residueSpecMap Q.y.base
    rw [glueSpecialMap_comp₂_assoc, glueι₂_comp_glueToBase, ← Category.assoc,
      Q.y.specialCartesian.w]
    rfl

/-- A commuting square of morphisms of schemes gives equal images of a point. -/
private theorem apply_eq_of_comp_eq {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C}
    {d : C ⟶ D} (h : a ≫ b = c ≫ d) (x : A) : b (a x) = d (c x) := by
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]

/-- Points of the two charts with the same image in the glued scheme lie in the overlap charts. -/
private theorem mem_restrictedOpen_of_glueι_eq {a : Q.x.scheme} {b : Q.y.scheme}
    (h : glueι₁ X U₁ U₂ Q a = glueι₂ X U₁ U₂ Q b) :
    a ∈ restrictedOpen Q.x (U₁.ι ⁻¹ᵁ (U₁ ⊓ U₂)) ∧ b ∈ restrictedOpen Q.y (U₂.ι ⁻¹ᵁ (U₁ ⊓ U₂)) := by
  obtain ⟨kk, fi, fj, z, hz₁, hz₂⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff (glueDiagram X U₁ U₂ Q)).mp h
  obtain - | b := kk
  · cases fi
    cases fj
    refine ⟨?_, ?_⟩
    · change a ∈ ((restrictedOpen Q.x (U₁.ι ⁻¹ᵁ (U₁ ⊓ U₂)) : Q.x.scheme.Opens) : Set _)
      rw [← range_glueOverlapι₁ X U₁ U₂ Q]
      exact ⟨z, hz₁⟩
    · change b ∈ ((restrictedOpen Q.y (U₂.ι ⁻¹ᵁ (U₁ ⊓ U₂)) : Q.y.scheme.Opens) : Set _)
      rw [← range_glueOverlapι₂ X U₁ U₂ Q]
      exact ⟨glueTransition X U₁ U₂ Q z, hz₂⟩
  · cases fi
    cases fj

/-- The first chart of the glued scheme cuts out `U₁` on the special fibre. -/
theorem glueSpecialMap_preimage_glueι₁ :
    glueSpecialMap X U₁ U₂ Q hcover ⁻¹ᵁ (glueι₁ X U₁ U₂ Q).opensRange = U₁ := by
  refine TopologicalSpace.Opens.ext (Set.eq_of_subset_of_subset ?_ ?_)
  · rintro x ⟨y, hy⟩
    have hx : x ∈ U₁ ⊔ U₂ := by rw [hcover]; trivial
    rcases hx with h | h
    · exact h
    · have heq := hy.trans (apply_eq_of_comp_eq (glueSpecialMap_comp₂ X U₁ U₂ Q hcover) ⟨x, h⟩)
      have hmem : (⟨x, h⟩ : U₂.toScheme) ∈
          Q.y.specialMap ⁻¹ᵁ restrictedOpen Q.y (U₂.ι ⁻¹ᵁ (U₁ ⊓ U₂)) :=
        (mem_restrictedOpen_of_glueι_eq X U₁ U₂ Q heq).2
      rw [specialMap_preimage_restrictedOpen] at hmem
      exact hmem.1
  · intro x hx
    exact ⟨Q.x.specialMap ⟨x, hx⟩,
      (apply_eq_of_comp_eq (glueSpecialMap_comp₁ X U₁ U₂ Q hcover) ⟨x, hx⟩).symm⟩

/-- The second chart of the glued scheme cuts out `U₂` on the special fibre. -/
theorem glueSpecialMap_preimage_glueι₂ :
    glueSpecialMap X U₁ U₂ Q hcover ⁻¹ᵁ (glueι₂ X U₁ U₂ Q).opensRange = U₂ := by
  refine TopologicalSpace.Opens.ext (Set.eq_of_subset_of_subset ?_ ?_)
  · rintro x ⟨y, hy⟩
    have hx : x ∈ U₁ ⊔ U₂ := by rw [hcover]; trivial
    rcases hx with h | h
    · have heq := (hy.trans (apply_eq_of_comp_eq (glueSpecialMap_comp₁ X U₁ U₂ Q hcover)
        ⟨x, h⟩)).symm
      have hmem : (⟨x, h⟩ : U₁.toScheme) ∈
          Q.x.specialMap ⁻¹ᵁ restrictedOpen Q.x (U₁.ι ⁻¹ᵁ (U₁ ⊓ U₂)) :=
        (mem_restrictedOpen_of_glueι_eq X U₁ U₂ Q heq).1
      rw [specialMap_preimage_restrictedOpen] at hmem
      exact hmem.2
    · exact h
  · intro x hx
    exact ⟨Q.y.specialMap ⟨x, hx⟩,
      (apply_eq_of_comp_eq (glueSpecialMap_comp₂ X U₁ U₂ Q hcover) ⟨x, hx⟩).symm⟩

/-- **The special fibre of the glued scheme is `X`.** -/
theorem glueSpecialMap_isPullback :
    IsPullback (glueSpecialMap X U₁ U₂ Q hcover) X.hom (glueToBase X U₁ U₂ Q)
      (residueSpecMap Q.y.base) := by
  refine isPullback_of_iSup_eq_top (glueSpecialMap_comp_glueToBase X U₁ U₂ Q hcover)
    (fun b : Bool => bif b then (glueι₂ X U₁ U₂ Q).opensRange
      else (glueι₁ X U₁ U₂ Q).opensRange) ?_ ?_
  · rw [iSup_bool_eq, sup_comm]
    exact glueι_opensRange_sup_eq_top X U₁ U₂ Q
  · intro b
    cases b
    · show IsPullback (glueSpecialMap X U₁ U₂ Q hcover ∣_ (glueι₁ X U₁ U₂ Q).opensRange)
        ((glueSpecialMap X U₁ U₂ Q hcover ⁻¹ᵁ (glueι₁ X U₁ U₂ Q).opensRange).ι ≫ X.hom)
        ((glueι₁ X U₁ U₂ Q).opensRange.ι ≫ glueToBase X U₁ U₂ Q) (residueSpecMap Q.y.base)
      refine Q.x.specialCartesian.of_iso
        (X.left.isoOfEq (glueSpecialMap_preimage_glueι₁ X U₁ U₂ Q hcover)).symm
        (Scheme.Hom.isoOpensRange (glueι₁ X U₁ U₂ Q)) (Iso.refl _)
        (asIso (baseSpecMap (glueBaseIso X U₁ U₂ Q))) ?_ ?_ ?_ ?_
      · rw [← cancel_mono (glueι₁ X U₁ U₂ Q).opensRange.ι]
        simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, morphismRestrict_ι,
          Iso.symm_hom, Scheme.isoOfEq_inv_ι_assoc, glueSpecialMap_comp₁]
      · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Scheme.isoOfEq_inv_ι_assoc]
        rfl
      · simp only [asIso_hom, ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
        rw [glueι₁_comp_glueToBase]
      · simp only [asIso_hom, Iso.refl_hom, Category.id_comp]
        exact residueSpecMap_comp_baseSpecMap (glueBaseIso X U₁ U₂ Q)
    · show IsPullback (glueSpecialMap X U₁ U₂ Q hcover ∣_ (glueι₂ X U₁ U₂ Q).opensRange)
        ((glueSpecialMap X U₁ U₂ Q hcover ⁻¹ᵁ (glueι₂ X U₁ U₂ Q).opensRange).ι ≫ X.hom)
        ((glueι₂ X U₁ U₂ Q).opensRange.ι ≫ glueToBase X U₁ U₂ Q) (residueSpecMap Q.y.base)
      refine Q.y.specialCartesian.of_iso
        (X.left.isoOfEq (glueSpecialMap_preimage_glueι₂ X U₁ U₂ Q hcover)).symm
        (Scheme.Hom.isoOpensRange (glueι₂ X U₁ U₂ Q)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      · rw [← cancel_mono (glueι₂ X U₁ U₂ Q).opensRange.ι]
        simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, morphismRestrict_ι,
          Iso.symm_hom, Scheme.isoOfEq_inv_ι_assoc, glueSpecialMap_comp₂]
      · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Scheme.isoOfEq_inv_ι_assoc]
        rfl
      · simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc,
          Scheme.Hom.isoOpensRange_hom_ι]
        rw [glueι₂_comp_glueToBase]
      · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- Let `X` be a scheme over `k` covered by two opens `U₁` and `U₂`. An object of the 2-fibre
product `Def_{U₁} ×_{Def_{U₁ ⊓ U₂}} Def_{U₂}` consists of a deformation of `U₁`, a deformation
of `U₂` and an isomorphism of their restrictions to `U₁ ⊓ U₂`; glueing the two total spaces
along that isomorphism gives a deformation of `X` over the same object of `𝒞_Λ`. -/
@[stacks 0DYZ "the glueing construction of the proof, on objects only: an object of the \
2-fibre product Def_{U_1} ×_{Def_{U_12}} Def_{U_2} is glued to a deformation of X over the \
same object of 𝒞_Λ, flat over it, with special fibre X, and restricting to U_1 and U_2 gives \
the two charts back. Not shown functorial in the datum, so not yet a quasi-inverse of \
twoOpenComparisonFunctor; neither the equivalence nor the Def_{P_i} form is proved"]
def glueDeformation : SchemeDeformationCategory (Λ := Λ) (k := k) X where
  base := Q.y.base
  scheme := glueScheme X U₁ U₂ Q
  toBase := glueToBase X U₁ U₂ Q
  flat := flat_glueToBase X U₁ U₂ Q
  specialMap := glueSpecialMap X U₁ U₂ Q hcover
  specialCartesian := glueSpecialMap_isPullback X U₁ U₂ Q hcover

/-- The glued deformation lies over the object of `𝒞_Λ` of the given datum. -/
theorem glueDeformation_base : (glueDeformation X U₁ U₂ Q hcover).base = Q.base := Q.hy

/-- If a chart `ι` of a deformation `D` of `W` contains the special fibre of a deformation `P` of
`U` compatibly with that of `D`, then `U` cuts out exactly the range of `ι` in `D`. -/
private theorem restrictedOpen_eq_opensRange {W : Over (Spec (.of k))} {U : W.left.Opens}
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk (U.ι ≫ W.hom)))
    (D : SchemeDeformationCategory (Λ := Λ) (k := k) W) (ι : P.scheme ⟶ D.scheme)
    [hι : IsOpenImmersion ι] (h : U.ι ≫ D.specialMap = P.specialMap ≫ ι) :
    restrictedOpen D U = ι.opensRange := by
  refine TopologicalSpace.Opens.ext (Set.eq_of_subset_of_subset ?_ ?_)
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨P.specialMap ⟨x, hx⟩, (apply_eq_of_comp_eq h ⟨x, hx⟩).symm⟩
  · rintro y ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := deformationSpecialMap_surjective P z
    exact ⟨U.ι x, x.2, by rw [← hx]; exact apply_eq_of_comp_eq h x⟩

/-- The open that `U₁` cuts out in the glued deformation is its first chart. -/
theorem restrictedOpen_glueDeformation_left :
    restrictedOpen (glueDeformation X U₁ U₂ Q hcover) U₁ = (glueι₁ X U₁ U₂ Q).opensRange :=
  restrictedOpen_eq_opensRange Q.x (glueDeformation X U₁ U₂ Q hcover)
    (hι := isOpenImmersion_glueι₁ X U₁ U₂ Q)
    (h := glueSpecialMap_comp₁ X U₁ U₂ Q hcover)

/-- The open that `U₂` cuts out in the glued deformation is its second chart. -/
theorem restrictedOpen_glueDeformation_right :
    restrictedOpen (glueDeformation X U₁ U₂ Q hcover) U₂ = (glueι₂ X U₁ U₂ Q).opensRange :=
  restrictedOpen_eq_opensRange Q.y (glueDeformation X U₁ U₂ Q hcover)
    (hι := isOpenImmersion_glueι₂ X U₁ U₂ Q)
    (h := glueSpecialMap_comp₂ X U₁ U₂ Q hcover)

/-! #### The glued deformation restricts to the given charts -/

/-- The first chart of the glued scheme and the open cut out by `U₁` have the same range. -/
theorem range_glueι₁_eq :
    Set.range (glueι₁ X U₁ U₂ Q) =
      Set.range (restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover)) := by
  rw [range_restrictDeformationι, restrictedOpen_glueDeformation_left]
  exact (Scheme.Hom.coe_opensRange _).symm

/-- The second chart of the glued scheme and the open cut out by `U₂` have the same range. -/
theorem range_glueι₂_eq :
    Set.range (glueι₂ X U₁ U₂ Q) =
      Set.range (restrictDeformationι U₂ (glueDeformation X U₁ U₂ Q hcover)) := by
  rw [range_restrictDeformationι, restrictedOpen_glueDeformation_right]
  exact (Scheme.Hom.coe_opensRange _).symm

/-- The total space of the first chart is the total space of the restriction of the glued
deformation to `U₁`. -/
def glueChartLeftIso : Q.x.scheme ≅
    (restrictDeformation U₁ (glueDeformation X U₁ U₂ Q hcover)).scheme :=
  @IsOpenImmersion.isoOfRangeEq _ _ _ (glueι₁ X U₁ U₂ Q)
    (restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover))
    (isOpenImmersion_glueι₁ X U₁ U₂ Q) (isOpenImmersion_restrictDeformationι U₁ _)
    (range_glueι₁_eq X U₁ U₂ Q hcover)

/-- The total space of the second chart is the total space of the restriction of the glued
deformation to `U₂`. -/
def glueChartRightIso : Q.y.scheme ≅
    (restrictDeformation U₂ (glueDeformation X U₁ U₂ Q hcover)).scheme :=
  @IsOpenImmersion.isoOfRangeEq _ _ _ (glueι₂ X U₁ U₂ Q)
    (restrictDeformationι U₂ (glueDeformation X U₁ U₂ Q hcover))
    (isOpenImmersion_glueι₂ X U₁ U₂ Q) (isOpenImmersion_restrictDeformationι U₂ _)
    (range_glueι₂_eq X U₁ U₂ Q hcover)

/-- `glueChartLeftIso` identifies the first chart with the open of the glued deformation cut out
by `U₁`. -/
@[reassoc]
theorem glueChartLeftIso_hom_comp_ι :
    (glueChartLeftIso X U₁ U₂ Q hcover).hom ≫
        restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover) =
      glueι₁ X U₁ U₂ Q :=
  @IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _ (glueι₁ X U₁ U₂ Q)
    (restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover))
    (isOpenImmersion_glueι₁ X U₁ U₂ Q) (isOpenImmersion_restrictDeformationι U₁ _)
    (range_glueι₁_eq X U₁ U₂ Q hcover)

/-- `glueChartRightIso` identifies the second chart with the open of the glued deformation cut
out by `U₂`. -/
@[reassoc]
theorem glueChartRightIso_hom_comp_ι :
    (glueChartRightIso X U₁ U₂ Q hcover).hom ≫
        restrictDeformationι U₂ (glueDeformation X U₁ U₂ Q hcover) =
      glueι₂ X U₁ U₂ Q :=
  @IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _ (glueι₂ X U₁ U₂ Q)
    (restrictDeformationι U₂ (glueDeformation X U₁ U₂ Q hcover))
    (isOpenImmersion_glueι₂ X U₁ U₂ Q) (isOpenImmersion_restrictDeformationι U₂ _)
    (range_glueι₂_eq X U₁ U₂ Q hcover)

/-- `glueChartLeftIso` is compatible with the structure morphisms, up to the isomorphism of
bases. -/
theorem glueChartLeftIso_hom_comp_toBase :
    (glueChartLeftIso X U₁ U₂ Q hcover).hom ≫
        (restrictDeformation U₁ (glueDeformation X U₁ U₂ Q hcover)).toBase =
      Q.x.toBase ≫ baseSpecMap (glueBaseIso X U₁ U₂ Q) := by
  have h : (glueChartLeftIso X U₁ U₂ Q hcover).hom ≫
      restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover) ≫
        (glueDeformation X U₁ U₂ Q hcover).toBase =
      Q.x.toBase ≫ baseSpecMap (glueBaseIso X U₁ U₂ Q) := by
    rw [glueChartLeftIso_hom_comp_ι_assoc]
    exact glueι₁_comp_glueToBase X U₁ U₂ Q
  exact h

/-- `glueChartRightIso` is compatible with the structure morphisms. -/
theorem glueChartRightIso_hom_comp_toBase :
    (glueChartRightIso X U₁ U₂ Q hcover).hom ≫
        (restrictDeformation U₂ (glueDeformation X U₁ U₂ Q hcover)).toBase = Q.y.toBase := by
  have h : (glueChartRightIso X U₁ U₂ Q hcover).hom ≫
      restrictDeformationι U₂ (glueDeformation X U₁ U₂ Q hcover) ≫
        (glueDeformation X U₁ U₂ Q hcover).toBase = Q.y.toBase := by
    rw [glueChartRightIso_hom_comp_ι_assoc]
    exact glueι₂_comp_glueToBase X U₁ U₂ Q
  exact h

/-- `glueChartLeftIso` is compatible with the special-fibre immersions. -/
theorem glueChartLeftIso_specialMap :
    Q.x.specialMap ≫ (glueChartLeftIso X U₁ U₂ Q hcover).hom =
      (restrictDeformation U₁ (glueDeformation X U₁ U₂ Q hcover)).specialMap := by
  refine (cancel_mono (restrictDeformationι U₁ (glueDeformation X U₁ U₂ Q hcover))).mp ?_
  rw [Category.assoc, glueChartLeftIso_hom_comp_ι, restrictDeformation_specialMap_comp_ι]
  exact (glueSpecialMap_comp₁ X U₁ U₂ Q hcover).symm

/-- `glueChartRightIso` is compatible with the special-fibre immersions. -/
theorem glueChartRightIso_specialMap :
    Q.y.specialMap ≫ (glueChartRightIso X U₁ U₂ Q hcover).hom =
      (restrictDeformation U₂ (glueDeformation X U₁ U₂ Q hcover)).specialMap := by
  refine (cancel_mono (restrictDeformationι U₂ (glueDeformation X U₁ U₂ Q hcover))).mp ?_
  rw [Category.assoc, glueChartRightIso_hom_comp_ι, restrictDeformation_specialMap_comp_ι]
  exact (glueSpecialMap_comp₂ X U₁ U₂ Q hcover).symm

/-- The inverse of the isomorphism of bases underlying the transition isomorphism. -/
def glueBaseIsoInv : Q.x.base ⟶ Q.y.base := Q.iso.hom.base

/-- `glueBaseIsoInv` is a left inverse of `glueBaseIso`. -/
@[reassoc]
theorem glueBaseIsoInv_comp_glueBaseIso :
    glueBaseIsoInv X U₁ U₂ Q ≫ glueBaseIso X U₁ U₂ Q = 𝟙 Q.x.base :=
  congrArg SchemeDeformationCategory.Hom.base Q.iso.hom_inv_id

/-- `glueBaseIsoInv` is a right inverse of `glueBaseIso`. -/
@[reassoc]
theorem glueBaseIso_comp_glueBaseIsoInv :
    glueBaseIso X U₁ U₂ Q ≫ glueBaseIsoInv X U₁ U₂ Q = 𝟙 Q.y.base :=
  congrArg SchemeDeformationCategory.Hom.base Q.iso.inv_hom_id

/-- The isomorphism of base spectra underlying the transition isomorphism. -/
def glueBaseSpecIso : baseSpec Q.x.base ≅ baseSpec Q.y.base where
  hom := baseSpecMap (glueBaseIso X U₁ U₂ Q)
  inv := baseSpecMap (glueBaseIsoInv X U₁ U₂ Q)
  hom_inv_id := by
    rw [← baseSpecMap_comp, glueBaseIsoInv_comp_glueBaseIso, baseSpecMap_id]
  inv_hom_id := by
    rw [← baseSpecMap_comp, glueBaseIso_comp_glueBaseIsoInv, baseSpecMap_id]

/-- The comparison morphism from the restriction of the glued deformation to `U₁` to the
first chart of the datum. -/
def restrictGlueDeformationLeftHom :
    restrictDeformation U₁ (glueDeformation X U₁ U₂ Q hcover) ⟶ Q.x where
  base := glueBaseIso X U₁ U₂ Q
  map := (glueChartLeftIso X U₁ U₂ Q hcover).hom
  cartesian := by
    refine (IsPullback.of_id_fst (f := Q.x.toBase)).of_iso (Iso.refl Q.x.scheme)
      (glueChartLeftIso X U₁ U₂ Q hcover) (Iso.refl (baseSpec Q.x.base))
      (glueBaseSpecIso X U₁ U₂ Q) ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact (glueChartLeftIso_hom_comp_toBase X U₁ U₂ Q hcover).symm
    · exact Category.id_comp _
  special_compat := glueChartLeftIso_specialMap X U₁ U₂ Q hcover

/-- The comparison morphism from the first chart of the datum to the restriction of the glued
deformation to `U₁`. -/
def restrictGlueDeformationLeftInv :
    Q.x ⟶ restrictDeformation U₁ (glueDeformation X U₁ U₂ Q hcover) where
  base := glueBaseIsoInv X U₁ U₂ Q
  map := (glueChartLeftIso X U₁ U₂ Q hcover).inv
  cartesian := by
    refine (IsPullback.of_id_fst (f := Q.x.toBase)).of_iso
      (glueChartLeftIso X U₁ U₂ Q hcover) (Iso.refl Q.x.scheme)
      (glueBaseSpecIso X U₁ U₂ Q) (Iso.refl (baseSpec Q.x.base)) ?_ ?_ ?_ ?_
    · simp
    · exact (glueChartLeftIso_hom_comp_toBase X U₁ U₂ Q hcover).symm
    · simp
    · exact (glueBaseSpecIso X U₁ U₂ Q).hom_inv_id.symm
  special_compat := by
    rw [← glueChartLeftIso_specialMap X U₁ U₂ Q hcover, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

/-- **The glued deformation restricts on `U₁` to the first chart of the datum.** -/
def restrictGlueDeformationLeft :
    restrictDeformation U₁ (glueDeformation X U₁ U₂ Q hcover) ≅ Q.x where
  hom := restrictGlueDeformationLeftHom X U₁ U₂ Q hcover
  inv := restrictGlueDeformationLeftInv X U₁ U₂ Q hcover
  hom_inv_id := SchemeDeformationCategory.Hom.ext
    (glueBaseIso_comp_glueBaseIsoInv X U₁ U₂ Q)
    ((glueChartLeftIso X U₁ U₂ Q hcover).inv_hom_id)
  inv_hom_id := SchemeDeformationCategory.Hom.ext
    (glueBaseIsoInv_comp_glueBaseIso X U₁ U₂ Q)
    ((glueChartLeftIso X U₁ U₂ Q hcover).hom_inv_id)

/-- The comparison morphism from the restriction of the glued deformation to `U₂` to the
second chart of the datum. -/
def restrictGlueDeformationRightHom :
    restrictDeformation U₂ (glueDeformation X U₁ U₂ Q hcover) ⟶ Q.y where
  base := 𝟙 Q.y.base
  map := (glueChartRightIso X U₁ U₂ Q hcover).hom
  cartesian := by
    refine (IsPullback.of_id_fst (f := Q.y.toBase)).of_iso (Iso.refl Q.y.scheme)
      (glueChartRightIso X U₁ U₂ Q hcover) (Iso.refl (baseSpec Q.y.base))
      (Iso.refl (baseSpec Q.y.base)) ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact (Category.comp_id _).trans
        (glueChartRightIso_hom_comp_toBase X U₁ U₂ Q hcover).symm
    · exact (Category.id_comp _).trans (baseSpecMap_id Q.y.base).symm
  special_compat := glueChartRightIso_specialMap X U₁ U₂ Q hcover

/-- The comparison morphism from the second chart of the datum to the restriction of the glued
deformation to `U₂`. -/
def restrictGlueDeformationRightInv :
    Q.y ⟶ restrictDeformation U₂ (glueDeformation X U₁ U₂ Q hcover) where
  base := 𝟙 Q.y.base
  map := (glueChartRightIso X U₁ U₂ Q hcover).inv
  cartesian := by
    refine (IsPullback.of_id_fst (f := Q.y.toBase)).of_iso
      (glueChartRightIso X U₁ U₂ Q hcover) (Iso.refl Q.y.scheme)
      (Iso.refl (baseSpec Q.y.base)) (Iso.refl (baseSpec Q.y.base)) ?_ ?_ ?_ ?_
    · simp
    · exact (Category.comp_id _).trans
        (glueChartRightIso_hom_comp_toBase X U₁ U₂ Q hcover).symm
    · simp
    · exact (baseSpecMap_id Q.y.base).symm.trans (Category.id_comp _).symm
  special_compat := by
    rw [← glueChartRightIso_specialMap X U₁ U₂ Q hcover, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

/-- **The glued deformation restricts on `U₂` to the second chart of the datum.** -/
def restrictGlueDeformationRight :
    restrictDeformation U₂ (glueDeformation X U₁ U₂ Q hcover) ≅ Q.y where
  hom := restrictGlueDeformationRightHom X U₁ U₂ Q hcover
  inv := restrictGlueDeformationRightInv X U₁ U₂ Q hcover
  hom_inv_id := SchemeDeformationCategory.Hom.ext (Category.comp_id _)
    ((glueChartRightIso X U₁ U₂ Q hcover).inv_hom_id)
  inv_hom_id := SchemeDeformationCategory.Hom.ext (Category.comp_id _)
    ((glueChartRightIso X U₁ U₂ Q hcover).hom_inv_id)

/-! #### The glueing construction in Situation 0DYY -/

/-- In a glueing situation the two affine opens cover the scheme, and an object of the 2-fibre
product of their deformation categories is glued to a deformation of the scheme itself. -/
@[stacks 0DYZ "the glueing construction of the proof in Situation 0DYY, on objects only; see \
`glueDeformation` for the precise content and for what the equivalence still needs"]
def GluingSituation.glueDeformation (S : GluingSituation Λ k)
    (Q : TwoOpenDeformations (Λ := Λ) S.X S.U₁ S.U₂) :
    SchemeDeformationCategory (Λ := Λ) (k := k) S.X :=
  Deformation.Examples.glueDeformation S.X S.U₁ S.U₂ Q S.cover

end QuasiInverse

end Deformation.Examples

end
