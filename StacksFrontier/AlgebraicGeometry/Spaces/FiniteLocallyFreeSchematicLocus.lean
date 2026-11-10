module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleCluster.QuasiAffineAndImmersion
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.FppfQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotientCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphicFieldRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae

/-!
# The schematic locus under a surjective finite locally free morphism

Tag 0BA1 says that, for a surjective finite locally free morphism `f : X ⟶ Y` of algebraic
spaces over a scheme `S` and a point `y` of `Y`, the point `y` lies in the schematic locus of
`Y` exactly when some affine open of `X` contains the whole fibre of `y`.

## Main results

* `AlgebraicGeometry.Space.mem_range_pointsMap_schematicLocus_iff`: a point lies in the point
  set of the schematic locus of Tag 03JH exactly when it lies in the point set of some
  representable open subspace.
* `AlgebraicGeometry.Space.exists_affineChart_pointsMap_eq`: a field-valued point of a
  presheaf represented by an object `U` of the site is the image of a field-valued point of
  one of the affine charts of `U`.
* `AlgebraicGeometry.Space.isRepresentable_of_presheafSurjective_presheafFiniteLocallyFree`:
  an algebraic space with a surjective finite locally free chart out of a scheme whose finite
  subsets lie in affine opens is a scheme.
* `AlgebraicGeometry.Space.exists_isAffine_isOpenImmersion_of_mem_schematicLocus` and
  `AlgebraicGeometry.Space.mem_range_pointsMap_schematicLocus_of_exists_isAffine`: the two
  implications of Tag 0BA1.
* `AlgebraicGeometry.Space.mem_range_pointsMap_schematicLocus_iff_exists_isAffine_isOpenImmersion`:
  **Stacks 0BA1**.

## Main definitions

* `AlgebraicGeometry.Space.affineChart` and `AlgebraicGeometry.Space.affineChartι`: a member
  of the standard affine cover of the underlying scheme of an object of the site, as an object
  of the site, and its open immersion into that object.

## Implementation notes

*The two spellings of finite local freeness.* The hypothesis on `f` is finite local freeness
in the **representable** sense — `f` is representable and every represented base change of it
is a finite locally free morphism of schemes — which is condition (1) of Tag 03ZW. The
source's Definition 03ZV, condition (2) of that tag, is
`AlgebraicGeometry.Space.IsFiniteLocallyFree`, stated through the direct image of the
structure sheaf on the small étale ringed site of `Y`. The two are equivalent, and the
equivalence is Tag 03ZU, `AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree` in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableChart`, which is proved; the
form without a representability hypothesis is
`AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree`. Neither is cited
below: condition (1) is the spelling every piece of machinery used here is stated for — base
change, descent, Tag 05VM, Tag 07S6 — and condition (2) is used nowhere, so nothing below
mentions Tag 03ZU.

*Tag 03JH is not needed.* The forward implication does not use the two unconditional clauses
of Tag 03JH, which the library has only under a cofinality hypothesis
(`AlgebraicGeometry.Space.isRepresentable_schematicLocus`). The schematic locus is by
definition the supremum of the representable open subspaces, and a supremum of subfunctors is
the object-wise union, so a point of it is already a point of one member of the family: that
is `AlgebraicGeometry.Space.mem_range_pointsMap_schematicLocus_iff`, and it is all the forward
implication consumes.

*The reverse implication.* The source forms `R = X ×_Y X` and removes from `X` the closed set
`t(Z)` of points `R`-equivalent to a point outside the affine open `U`. The argument here does
the same thing one step later, on `Y` rather than on `R`: the open subspace is cut out by
`|Y| \ f(|X| \ |U|)`, whose preimage is contained in `|U|` by construction and is a full
preimage, hence automatically `R`-invariant. Closedness of the image is finiteness of `f`
through Tag 0414, Tag 0415 and
`AlgebraicGeometry.Space.universallyClosed_of_presheaf_universallyClosed`; the passage between
open subsets of the point set of Tag 03BX and open subspaces is the correspondence of
Tag 03BZ, `AlgebraicGeometry.Space.openSubspacesOrderIso`. Openness of `f` (Tag 042S) and
Tag 03H4 are therefore not used in this direction, and Tag 03H4 is used only in the forward
one.

*Where Tag 07S6 enters.* The restricted chart is a surjective finite locally free morphism
from a scheme open in an affine scheme, and
`AlgebraicGeometry.Space.isRepresentable_of_presheafSurjective_presheafFiniteLocallyFree` is
the fppf counterpart of the étale representability statement of
`StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusBoundedChart`: Tag 07S6 in the form
`AlgebraicGeometry.GroupoidScheme.exists_schemeQuotient_of_isFiniteLocallyFree_relation`
builds the quotient, Tag 01ZY supplies its affine-orbit hypothesis, and the étale hypothesis
of the model statement is replaced by Tag 05VM for a surjective flat chart locally of finite
presentation — which is the only place étaleness was used there, through the coequalizer
clause of Tag 0262.

## References

* [Stacks Project, Tag 0BA1](https://stacks.math.columbia.edu/tag/0BA1)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_FiniteLocallyFreeSchematicLocus :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_FiniteLocallyFreeSchematicLocus
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_FiniteLocallyFreeSchematicLocus B S hS).has_limit _

/-! ### Toolkit -/

/-- A monomorphism whose image subfunctor is an open subspace is an open immersion. -/
private theorem isOpenImmersion_of_isOpenSubspace_range
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G) [Mono g]
    (hg : IsOpenImmersion B S hS (Subfunctor.range g).ι) :
    IsOpenImmersion B S hS g := by
  set e : F ≅ (Subfunctor.range g).toFunctor := asIso (Subfunctor.toRange g)
  have hcomp : e.hom ≫ (Subfunctor.range g).ι = g := Subfunctor.toRange_ι g
  have h := MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) e.hom (Subfunctor.range g).ι hg
  rwa [hcomp] at h

/-- A presheaf admitting an open immersion into a representable presheaf is representable. -/
private theorem isRepresentable_of_isOpenImmersion_to_yoneda
    (U : BigFppfOver B S hS) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : F ⟶ yoneda.obj U) (hg : IsOpenImmersion B S hS g) : F.IsRepresentable := by
  have hiso : IsIso (hg.rep.fst (𝟙 (yoneda.obj U))) :=
    (hg.rep.isPullback (𝟙 (yoneda.obj U))).isIso_fst_of_isIso
  exact isRepresentable_of_natIso _ (asIso (hg.rep.fst (𝟙 (yoneda.obj U))))

/-- A representable finite locally free morphism of presheaves is universally closed in the
relative sense: every represented base change is a finite morphism of schemes, hence
universally closed. -/
private theorem presheaf_universallyClosed_of_presheaf_isFiniteLocallyFree
    {A A' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : A ⟶ A'}
    (hf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  refine ⟨hf.1, ?_⟩
  intro a b g fst snd hpb
  have h := (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    ((BigFppfOver.toScheme B S hS).map snd)).mp (hf.2 g fst snd hpb)
  have _ : AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map snd) := h.1
  change AlgebraicGeometry.UniversallyClosed ((BigFppfOver.toScheme B S hS).map snd)
  infer_instance

/-- The map on points of a universally closed morphism of algebraic spaces is a closed map:
take the base change along the identity. -/
private theorem isClosedMap_pointsMap_of_universallyClosed'
    {A A' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hA' : IsAlgebraicSpace B S hS A')
    {f : A ⟶ A'} (hf : UniversallyClosed B S hS f) :
    letI := pointTopology B S hS A
    letI := pointTopology B S hS A'
    IsClosedMap (pointsMap B S hS A f) :=
  isClosedMap_pointsMap_of_pullback_fst_id B S hS f (hf A' hA' (𝟙 A'))

/-! ### Points of the schematic locus, and affine charts -/

/-- A point of a presheaf lies in the point set of the schematic locus of Tag 03JH exactly
when it lies in the point set of one representable open subspace.

The schematic locus is the supremum of the representable open subspaces, and the supremum of
subfunctors is the object-wise union, so a field-valued point of it takes its value in one
member of the family. -/
@[stacks 03JH "points of the schematic locus"]
theorem mem_range_pointsMap_schematicLocus_iff
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (y : points B S hS F) :
    y ∈ Set.range (pointsMap B S hS (schematicLocus B S hS F).toFunctor
        (schematicLocus B S hS F).ι) ↔
      ∃ G : Subfunctor F, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
        y ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) := by
  refine ⟨?_, fun ⟨G, hG, hGrep, hy⟩ =>
    range_pointsMap_ι_le_schematicLocus B S hS G hG hGrep hy⟩
  rintro ⟨w, rfl⟩
  induction w using Quot.inductionOn with
  | _ p =>
    obtain ⟨-, ⟨G, hG, rfl⟩, hmem⟩ := p.value.2
    exact ⟨G, hG.1, hG.2, ⟨Quot.mk _
      { carrier := p.carrier
        contained := p.contained
        toBase := p.toBase
        value := ⟨p.value.1, hmem⟩ }, rfl⟩⟩

section AffineChart

variable (U : BigFppfOver B S hS)
    (i : ((BigFppfOver.toScheme B S hS).obj U).affineCover.I₀)

/-- A member of the standard affine cover of the underlying scheme of an object of the site is
again small enough for the site. -/
theorem size_affineCover_lt :
    (((BigFppfOver.toScheme B S hS).obj U).affineCover.X i).size < B.cutoff :=
  Scheme.size_lt_of_isOpenImmersion
    (((BigFppfOver.toScheme B S hS).obj U).affineCover.f i) U.left.property

/-- The inclusion, inside the site's category of schemes, of a member of the standard affine
cover of the underlying scheme of `U`. -/
noncomputable def standardAffineCoverMap :
    B.obj (size_affineCover_lt B S hS U i) ⟶ U.left :=
  B.inclusion.preimage
    (show B.inclusion.obj (B.obj (size_affineCover_lt B S hS U i)) ⟶ B.inclusion.obj U.left from
      ((BigFppfOver.toScheme B S hS).obj U).affineCover.f i)

/-- The image of `standardAffineCoverMap` in schemes is the corresponding member of the standard
affine cover. -/
@[simp]
theorem inclusion_map_standardAffineCoverMap :
    B.inclusion.map (standardAffineCoverMap B S hS U i) =
      ((BigFppfOver.toScheme B S hS).obj U).affineCover.f i :=
  B.inclusion.map_preimage _

/-- An affine chart of an object of the big fppf site over `S`: the object given by a member of
the standard affine cover of its underlying scheme. -/
noncomputable def affineChart : BigFppfOver B S hS :=
  Over.mk (standardAffineCoverMap B S hS U i ≫ U.hom)

/-- The open immersion of an affine chart of `U` into `U`. -/
noncomputable def affineChartι : affineChart B S hS U i ⟶ U :=
  Over.homMk (standardAffineCoverMap B S hS U i)

/-- The underlying morphism of schemes of `affineChartι` is `standardAffineCoverMap`. -/
@[simp]
theorem affineChartι_left :
    (affineChartι B S hS U i).left = standardAffineCoverMap B S hS U i := rfl

/-- The structure morphism of an affine chart is the composite of `standardAffineCoverMap` with
the structure morphism of `U`. -/
@[simp]
theorem affineChart_hom :
    (affineChart B S hS U i).hom = standardAffineCoverMap B S hS U i ≫ U.hom := rfl

/-- The underlying morphism of schemes of `affineChartι` is the corresponding member of the
standard affine cover of the underlying scheme of `U`. -/
@[simp]
theorem toScheme_map_affineChartι :
    (BigFppfOver.toScheme B S hS).map (affineChartι B S hS U i) =
      ((BigFppfOver.toScheme B S hS).obj U).affineCover.f i :=
  inclusion_map_standardAffineCoverMap B S hS U i

/-- The underlying scheme of an affine chart is affine. -/
instance isAffine_affineChart :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (affineChart B S hS U i)) :=
  inferInstanceAs
    (IsAffine (((BigFppfOver.toScheme B S hS).obj U).affineCover.X i))

/-- The underlying morphism of schemes of a morphism of the big fppf site over `S`. -/
theorem toScheme_map_eq_inclusion_map_left {T T' : BigFppfOver B S hS} (g : T ⟶ T') :
    (BigFppfOver.toScheme B S hS).map g = B.inclusion.map g.left := rfl

/-- The composite of an arrow into an affine chart of `U` with the chart's inclusion, read in
schemes. -/
theorem inclusion_map_comp_standardAffineCoverMap {T : B.Schemes}
    (l : T ⟶ B.obj (size_affineCover_lt B S hS U i)) :
    B.inclusion.map (l ≫ standardAffineCoverMap B S hS U i) =
      B.inclusion.map l ≫ ((BigFppfOver.toScheme B S hS).obj U).affineCover.f i := by
  rw [Functor.map_comp, inclusion_map_standardAffineCoverMap]

/-- The underlying morphism of schemes of `affineChartι` is an open immersion. -/
theorem isOpenImmersion_toScheme_map_affineChartι :
    _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (affineChartι B S hS U i)) := by
  rw [toScheme_map_affineChartι]
  exact ((BigFppfOver.toScheme B S hS).obj U).affineCover.map_prop i

end AffineChart

/-- A field-valued point of a presheaf represented by an object `U` of the site is the image of
a field-valued point of one of the affine charts of `U`. -/
theorem exists_affineChart_pointsMap_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : BigFppfOver B S hS) (e : yoneda.obj U ≅ F) (p : FieldValuedPoint B S hS F) :
    ∃ (i : ((BigFppfOver.toScheme B S hS).obj U).affineCover.I₀)
      (q : FieldValuedPoint B S hS (yoneda.obj (affineChart B S hS U i))),
      pointsMap B S hS (yoneda.obj (affineChart B S hS U i))
          (yoneda.map (affineChartι B S hS U i) ≫ e.hom)
          (q.class B S hS (yoneda.obj (affineChart B S hS U i))) =
        p.class B S hS F := by
  obtain ⟨i, z, hz⟩ :=
    ((BigFppfOver.toScheme B S hS).obj U).affineCover.exists_eq
      (schemePoint B S hS U (FieldValuedPoint.map B S hS F e.inv p))
  refine ⟨i, ?_⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : (FieldValuedPoint.map B S hS F e.inv p).siteObject.left ⟶
      B.obj (size_affineCover_lt B S hS U i),
      ℓ ≫ standardAffineCoverMap B S hS U i =
        (FieldValuedPoint.map B S hS F e.inv p).value.left := by
    have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj
        (FieldValuedPoint.map B S hS F e.inv p).siteObject) := by
      change Subsingleton (PrimeSpectrum (CommRingCat.of p.carrier))
      exact (PrimeSpectrum.subsingleton_iff_isField_of_isReduced
        (R := CommRingCat.of p.carrier)).2 (Field.toIsField p.carrier)
    have hrange : Set.range ((BigFppfOver.toScheme B S hS).map
          (FieldValuedPoint.map B S hS F e.inv p).value).base ⊆
        Set.range (((BigFppfOver.toScheme B S hS).obj U).affineCover.f i).base := by
      rintro w ⟨w', rfl⟩
      rw [hsub.elim w' (IsLocalRing.closedPoint p.carrier)]
      exact ⟨z, hz⟩
    refine ⟨B.inclusion.preimage (_root_.AlgebraicGeometry.IsOpenImmersion.lift
      (((BigFppfOver.toScheme B S hS).obj U).affineCover.f i)
      ((BigFppfOver.toScheme B S hS).map
        (FieldValuedPoint.map B S hS F e.inv p).value)
      (H := ((BigFppfOver.toScheme B S hS).obj U).affineCover.map_prop i) hrange), ?_⟩
    apply B.inclusion.map_injective
    rw [inclusion_map_comp_standardAffineCoverMap, B.inclusion.map_preimage,
      ← toScheme_map_eq_inclusion_map_left]
    exact _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have hover : ℓ ≫ (affineChart B S hS U i).hom =
      (FieldValuedPoint.map B S hS F e.inv p).siteObject.hom := by
    rw [show ℓ ≫ (affineChart B S hS U i).hom =
        (ℓ ≫ standardAffineCoverMap B S hS U i) ≫ U.hom from (Category.assoc _ _ _).symm, hℓ]
    exact Over.w (FieldValuedPoint.map B S hS F e.inv p).value
  have hcomp : (Over.homMk ℓ hover :
        (FieldValuedPoint.map B S hS F e.inv p).siteObject ⟶ affineChart B S hS U i) ≫
      affineChartι B S hS U i = (FieldValuedPoint.map B S hS F e.inv p).value :=
    Over.OverMorphism.ext hℓ
  refine ⟨{ carrier := p.carrier
            contained := p.contained
            toBase := p.toBase
            value := Over.homMk ℓ hover }, ?_⟩
  rw [pointsMap_class]
  apply FieldValuedPoint.class_eq_class_of_hasCommonExtension
  refine ⟨p, ⟨𝟙 _, ?_⟩, FieldValuedPoint.dominates_refl B S hS F p⟩
  refine Eq.trans (Functor.map_id_apply F _ _) ?_
  change (yoneda.map (affineChartι B S hS U i) ≫ e.hom).app _ _ = p.value
  rw [NatTrans.comp_app, types_comp_apply]
  change e.hom.app _ ((Over.homMk ℓ hover : _ ⟶ affineChart B S hS U i) ≫
    affineChartι B S hS U i) = p.value
  rw [hcomp]
  change (e.inv ≫ e.hom).app _ p.value = p.value
  rw [e.inv_hom_id]
  rfl


/-! ### The forward implication -/

/-- A property of represented morphisms of presheaves is inherited by the second projection of
a pullback square along the first. -/
private theorem presheaf_snd_of_isPullback (P : MorphismProperty Scheme.{u})
    {A X' Y' T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {fst : T ⟶ X'} {snd : T ⟶ Y'}
    {f : X' ⟶ A} {g : Y' ⟶ A} (hpb : IsPullback fst snd f g)
    (hf : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf snd :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb hf

/-- **Stacks 0BA1, (1) implies (2).** If `y` lies in the schematic locus of `Y` then some
affine open of `X` contains the fibre of `y`.

A representable open subspace of `Y` whose point set contains `y` is a scheme, so `y` has an
affine open neighbourhood `W` in it, which is then an affine open subspace of `Y`.  The base
change of `f` along `W` is represented by an object of the site, affine because `f` is affine
and `W` is affine, and it is an open subspace of `X` because open immersions are stable under
base change.  Tag 03H4 puts every point of `X` above `y` into it. -/
theorem exists_isAffine_isOpenImmersion_of_mem_schematicLocus
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom)
    (y : points B S hS Y.obj)
    (hy : y ∈ Set.range (pointsMap B S hS (schematicLocus B S hS Y.obj).toFunctor
      (schematicLocus B S hS Y.obj).ι)) :
    ∃ (U : BigFppfOver B S hS) (i : yoneda.obj U ⟶ X.obj),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧ IsOpenImmersion B S hS i ∧
      ∀ x : points B S hS X.obj, pointsMap B S hS X.obj f.hom x = y →
        x ∈ Set.range (pointsMap B S hS (yoneda.obj U) i) := by
  classical
  obtain ⟨G, hGopen, hGrep, ⟨w, hw⟩⟩ :=
    (mem_range_pointsMap_schematicLocus_iff B S hS Y.obj y).mp hy
  obtain ⟨pt, hpt⟩ := Quot.exists_rep w
  obtain ⟨jj, qq, hqq⟩ := exists_affineChart_pointsMap_eq B S hS
    G.toFunctor.reprX G.toFunctor.reprW pt
  set ι₀ : yoneda.obj (affineChart B S hS G.toFunctor.reprX jj) ⟶ G.toFunctor :=
    yoneda.map (affineChartι B S hS G.toFunctor.reprX jj) ≫ G.toFunctor.reprW.hom
  set α : yoneda.obj (affineChart B S hS G.toFunctor.reprX jj) ⟶ Y.obj :=
    ι₀ ≫ G.ι with hαdef
  have hαopen : IsOpenImmersion B S hS α := by
    refine MorphismProperty.comp_mem _ ι₀ G.ι ?_ hGopen.2
    refine MorphismProperty.RespectsIso.postcomp _ G.toFunctor.reprW.hom _ ?_
    exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsOpenImmersion.{u}) _).2
      (isOpenImmersion_toScheme_map_affineChartι B S hS G.toFunctor.reprX jj)
  have hptw : pt.class B S hS G.toFunctor = w := hpt
  have hαy : pointsMap B S hS (yoneda.obj (affineChart B S hS G.toFunctor.reprX jj)) α
      (qq.class B S hS (yoneda.obj (affineChart B S hS G.toFunctor.reprX jj))) = y := by
    rw [hαdef, pointsMap_comp_apply B S hS ι₀ G.ι, hqq, hptw]
    exact hw
  -- The base change of `f` along the affine chart.
  have hsq : IsPullback (hflf.rep.fst α) (yoneda.map (hflf.rep.snd α)) f.hom α :=
    hflf.rep.isPullback α
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (affineChart B S hS G.toFunctor.reprX jj)) :=
    isAffine_affineChart B S hS G.toFunctor.reprX jj
  have _ : Stacks.Morphisms.IsFiniteLocallyFree
      ((BigFppfOver.toScheme B S hS).map (hflf.rep.snd α)) :=
    hflf.2 α (hflf.rep.fst α) (hflf.rep.snd α) hsq
  have hU₀aff : IsAffine ((BigFppfOver.toScheme B S hS).obj (hflf.rep.pullback α)) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (hflf.rep.snd α))
  have hi₀open : IsOpenImmersion B S hS (hflf.rep.fst α) :=
    presheaf_snd_of_isPullback B S hS _ hsq.flip hαopen
  refine ⟨hflf.rep.pullback α, hflf.rep.fst α, hU₀aff, hi₀open, fun x hx => ?_⟩
  -- Tag 03H4 on that square, read in algebraic spaces.
  have hsqsp : IsPullback
      (ObjectProperty.homMk (P := algebraicSpaceProperty B S hS)
        (X := (⟨yoneda.obj (hflf.rep.pullback α),
          isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨yoneda.obj (affineChart B S hS G.toFunctor.reprX jj),
          isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS))
        (yoneda.map (hflf.rep.snd α)))
      (ObjectProperty.homMk (P := algebraicSpaceProperty B S hS) (Y := X) (hflf.rep.fst α))
      (ObjectProperty.homMk (P := algebraicSpaceProperty B S hS) (Y := Y) α) f :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hsq.flip.w) hsq.flip
  obtain ⟨z, -, hz⟩ := exists_point_of_isPullback B S hS hsqsp
    (qq.class B S hS (yoneda.obj (affineChart B S hS G.toFunctor.reprX jj))) x
    (hαy.trans hx.symm)
  exact ⟨z, hz⟩

/-! ### Representability from a surjective finite locally free chart -/

/-- A locally surjective morphism from a representable presheaf into a sheaf, whose kernel
pair is represented by two morphisms of the site, exhibits the sheaf as the coequalizer of
those two morphisms in sheaves of sets.

This is `AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale`, Tag 0262 part (3), with
local surjectivity assumed rather than deduced from surjectivity and étaleness: the étale
hypothesis there is used only through Tag 05VM. -/
private theorem nonempty_isColimitCofork_of_isLocallySurjective
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ F) (t s : R ⟶ U)
    (hR : IsPullback (yoneda.map t) (yoneda.map s) f f)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    let J := BigFppfOver.topology B S hS
    ∃ (hRsh : Presheaf.IsSheaf J (yoneda.obj R))
      (hUsh : Presheaf.IsSheaf J (yoneda.obj U)),
      let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
      let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
      let FF : Sheaf J (Type u) := ⟨F, hF⟩
      let tf : RF ⟶ UF := ⟨yoneda.map t⟩
      let sf : RF ⟶ UF := ⟨yoneda.map s⟩
      let ff : UF ⟶ FF := ⟨f⟩
      let w : tf ≫ ff = sf ≫ ff := Sheaf.hom_ext hR.w
      Nonempty (IsColimit (Cofork.ofπ ff w)) := by
  classical
  have hRsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj R) :=
    BigFppfOver.isSheaf_yoneda_obj B S hS R
  have hUsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj U) :=
    BigFppfOver.isSheaf_yoneda_obj B S hS U
  refine ⟨hRsh, hUsh, ?_⟩
  have hker : ∀ ⦃T : BigFppfOver B S hS⦄
      (x y : (yoneda.obj U).obj (Opposite.op T)),
      f.app (Opposite.op T) x = f.app (Opposite.op T) y →
      ∃ r : (yoneda.obj R).obj (Opposite.op T),
        (yoneda.map t).app (Opposite.op T) r = x ∧
          (yoneda.map s).app (Opposite.op T) r = y := by
    intro T x y hxy
    have hxy' : yoneda.map x ≫ f = yoneda.map y ≫ f := by
      apply yonedaEquiv.injective
      simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using hxy
    refine ⟨yonedaEquiv (hR.lift (yoneda.map x) (yoneda.map y) hxy'), ?_, ?_⟩
    · rw [← yonedaEquiv_comp]
      exact (congrArg yonedaEquiv (hR.lift_fst _ _ hxy')).trans (yonedaEquiv_yoneda_map x)
    · rw [← yonedaEquiv_comp]
      exact (congrArg yonedaEquiv (hR.lift_snd _ _ hxy')).trans (yonedaEquiv_yoneda_map y)
  exact Sheaf.nonempty_isColimitCoforkOfKernelPair
    (⟨yoneda.map t⟩ : (⟨yoneda.obj R, hRsh⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
      ⟨yoneda.obj U, hUsh⟩)
    ⟨yoneda.map s⟩ (⟨f⟩ : (⟨yoneda.obj U, hUsh⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨F, hF⟩) _ hker hls

/-- The two projections of the self base change of a morphism out of a representable presheaf
are interchanged by the symmetry of the fibre product, so one is finite locally free as soon
as the other is. -/
private theorem isFiniteLocallyFree_map_fst'_self
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : BigFppfOver B S hS} {ψ : yoneda.obj W ⟶ Z}
    (hrep : yoneda.relativelyRepresentable ψ)
    (hs : Stacks.Morphisms.IsFiniteLocallyFree
      ((BigFppfOver.toScheme B S hS).map (hrep.snd ψ))) :
    Stacks.Morphisms.IsFiniteLocallyFree
      ((BigFppfOver.toScheme B S hS).map (hrep.fst' ψ)) := by
  have he : (BigFppfOver.toScheme B S hS).map (hrep.symmetry hrep) ≫
      (BigFppfOver.toScheme B S hS).map (hrep.snd ψ) =
      (BigFppfOver.toScheme B S hS).map (hrep.fst' ψ) := by
    rw [← Functor.map_comp, hrep.symmetry_snd hrep]
  rw [← he]
  exact MorphismProperty.RespectsIso.precomp
    (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) _ _ hs

/-- A surjective finite locally free morphism from a representable presheaf to a sheaf is
locally surjective for the fppf topology (Tag 05VM). -/
theorem isLocallySurjective_of_presheafSurjective_presheafFiniteLocallyFree
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z)
    {W : BigFppfOver B S hS} (ψ : yoneda.obj W ⟶ Z)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (hflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) ψ := by
  have hcomb : (MorphismProperty.inverseImage
      ((fun _ _ g => Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g) :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ := by
    refine ⟨hflf.rep, fun a b g fst snd hpb => ?_⟩
    have h := (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map snd)).mp (hflf.2 g fst snd hpb)
    exact ⟨h.2.1, h.2.2, hsurj.2 g fst snd hpb⟩
  exact isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
    B S hS (⟨ψ⟩ : (⟨yoneda.obj W, BigFppfOver.isSheaf_yoneda_obj B S hS W⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨Z, hZ⟩) hcomb

/-- **An algebraic space with a surjective finite locally free chart out of a scheme whose
finite subsets lie in affine opens is a scheme.**

This is the fppf counterpart of the étale statement
`isRepresentable_of_presheafSurjective_presheafEtale_of_isFiniteLocallyFree_relation` of
`StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusBoundedChart`, proved the same way.
The relation `R = W ×_Z W` is an equivalence relation with finite locally
free projections by Tag 0262 part (1), so Tag 07S6 in the form
`AlgebraicGeometry.GroupoidScheme.exists_schemeQuotient_of_isFiniteLocallyFree_relation`
produces a quotient scheme `M` no larger than `W`, and
`AlgebraicGeometry.Space.exists_mono_yoneda_of_isPullback` descends the chart to a
monomorphism `d : h_M ⟶ Z`. That `d` is an isomorphism because the chart exhibits `Z` as the
coequalizer of the two projections: that step is the only place the étale version uses
étaleness, and here local surjectivity comes from Tag 05VM for a surjective flat chart
locally of finite presentation instead. -/
theorem isRepresentable_of_presheafSurjective_presheafFiniteLocallyFree
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    {W : BigFppfOver B S hS} (ψ : yoneda.obj W ⟶ Z)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (hflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (haffine : ∀ E : Set ((BigFppfOver.toScheme B S hS).obj W), E.Finite →
      ∃ O : ((BigFppfOver.toScheme B S hS).obj W).Opens, IsAffineOpen O ∧ E ⊆ O) :
    Z.IsRepresentable := by
  classical
  let _ : EssentiallySmall.{u} (BigFppfOver B S hS) :=
    inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (𝟭 B.Schemes) (B.obj hS)))
  let _ : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} (BigFppfOver.topology B S hS) _
  set t : hflf.rep.pullback ψ ⟶ W := hflf.rep.fst' ψ
  set s : hflf.rep.pullback ψ ⟶ W := hflf.rep.snd ψ
  have hR : IsPullback (yoneda.map t) (yoneda.map s) ψ ψ := hflf.rep.isPullback' ψ
  have hflfs : Stacks.Morphisms.IsFiniteLocallyFree
      ((BigFppfOver.toScheme B S hS).map s) :=
    hflf.2 ψ (hflf.rep.fst ψ) (hflf.rep.snd ψ) (hflf.rep.isPullback ψ)
  have hflft : Stacks.Morphisms.IsFiniteLocallyFree
      ((BigFppfOver.toScheme B S hS).map t) :=
    isFiniteLocallyFree_map_fst'_self B S hS hflf.rep hflfs
  obtain ⟨M, π, hsize, hflfπ, hsurjπ, hpbπ⟩ :=
    GroupoidScheme.exists_schemeQuotient_of_isFiniteLocallyFree_relation B S hS
      ((Over.post (X := B.obj hS) B.inclusion).map t)
      ((Over.post (X := B.obj hS) B.inclusion).map s) hflft hflfs
      (isEquivalenceRelation_of_isPullback B S hS ψ t s hR) W.left.2 haffine
  have hM : B.Contains M.left := lt_of_le_of_lt hsize W.left.2
  obtain ⟨m, d, hmπ, hmono, hfd⟩ :=
    exists_mono_yoneda_of_isPullback B S hS hZ.isSheaf ψ t s hR
      (U' := (Over.mk (⟨M.hom⟩ : B.obj hM ⟶ B.obj hS) : BigFppfOver B S hS)) π
      (Stacks.Morphisms.IsFiniteLocallyFree.flat π.left)
      (Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation π.left)
      hsurjπ hpbπ
  have hts : t ≫ m = s ≫ m := by
    refine (Over.post (X := B.obj hS) B.inclusion).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, hmπ]
    exact hpbπ.w
  obtain ⟨hRsh, hUsh, hcolim⟩ :=
    nonempty_isColimitCofork_of_isLocallySurjective B S hS ψ t s hR hZ.isSheaf
      (isLocallySurjective_of_presheafSurjective_presheafFiniteLocallyFree B S hS
        hZ.isSheaf ψ hsurj hflf)
  obtain ⟨hcolim⟩ := hcolim
  set J := BigFppfOver.topology B S hS
  let RF : Sheaf J (Type u) := ⟨yoneda.obj (hflf.rep.pullback ψ), hRsh⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj W, hUsh⟩
  let MF : Sheaf J (Type u) :=
    ⟨yoneda.obj (Over.mk (⟨M.hom⟩ : B.obj hM ⟶ B.obj hS) : BigFppfOver B S hS),
      BigFppfOver.isSheaf_yoneda_obj B S hS _⟩
  let ZF : Sheaf J (Type u) := ⟨Z, hZ.isSheaf⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let ff : UF ⟶ ZF := ⟨ψ⟩
  let mf : UF ⟶ MF := ⟨yoneda.map m⟩
  let dS : MF ⟶ ZF := ⟨d⟩
  have hwm : tf ≫ mf = sf ≫ mf := by
    refine Sheaf.hom_ext ?_
    change yoneda.map t ≫ yoneda.map m = yoneda.map s ≫ yoneda.map m
    rw [← Functor.map_comp, ← Functor.map_comp, hts]
  have hwf : tf ≫ ff = sf ≫ ff := Sheaf.hom_ext hR.w
  have hcolim' : IsColimit (Cofork.ofπ ff hwf) := hcolim
  have hc : ff ≫ hcolim'.desc (Cofork.ofπ mf hwm) = mf := by
    simpa only [Cofork.π_ofπ] using
      Cofork.IsColimit.π_desc (t := Cofork.ofπ mf hwm) hcolim'
  have hmd : mf ≫ dS = ff := Sheaf.hom_ext hfd
  have hsplit : hcolim'.desc (Cofork.ofπ mf hwm) ≫ dS = 𝟙 ZF := by
    refine Cofork.IsColimit.hom_ext hcolim' ?_
    simp only [Cofork.π_ofπ, ← Category.assoc, hc, hmd]
    exact (Category.comp_id ff).symm
  have hsplit' : (hcolim'.desc (Cofork.ofπ mf hwm)).hom ≫ d = 𝟙 Z :=
    Sheaf.hom_ext_iff.mp hsplit
  have _ : Mono d := hmono
  have _ : IsSplitEpi d := IsSplitEpi.mk' ⟨(hcolim'.desc (Cofork.ofπ mf hwm)).hom, hsplit'⟩
  have _ : IsIso d := isIso_of_mono_of_isSplitEpi d
  exact Functor.IsRepresentable.mk' (asIso d)

/-! ### The reverse implication -/

section Reverse

attribute [local instance] pointTopology

/-- **Stacks 0BA1, (2) implies (1).** If some affine open of `X` contains the fibre of `y`
then `y` lies in the schematic locus of `Y`.

Write `U` for the affine open and `|U|` for its point set. Since `f` is finite it is closed on
the points of Tag 03BX, so `V = |Y| \ f(|X| \ |U|)` is open, it contains `y` because the whole
fibre of `y` lies in `|U|`, and its preimage lies in `|U|` by construction; it is therefore an
open subspace of `Y` by the correspondence of Tag 03BZ. The base change `P = X ×_Y V` is then
an open subspace of `X` whose point set lies in `|U|`, hence — through the same
correspondence — an open subspace of `U`, hence a scheme `W` immersed in the affine `U`. The
projection `P ⟶ V` is a surjective finite locally free chart of `V` out of `W`, so every
finite subset of `W` lies in an affine open by Tag 01ZY and `V` is representable. Being a
representable open subspace, `V` is contained in the schematic locus, which therefore contains
`y`. -/
theorem mem_range_pointsMap_schematicLocus_of_exists_isAffine
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom)
    (hflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom)
    (y : points B S hS Y.obj)
    (U : BigFppfOver B S hS) (i : yoneda.obj U ⟶ X.obj)
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hi : IsOpenImmersion B S hS i)
    (hfiber : ∀ x : points B S hS X.obj, pointsMap B S hS X.obj f.hom x = y →
      x ∈ Set.range (pointsMap B S hS (yoneda.obj U) i)) :
    y ∈ Set.range (pointsMap B S hS (schematicLocus B S hS Y.obj).toFunctor
      (schematicLocus B S hS Y.obj).ι) := by
  classical
  have _ : Mono i := mono_of_presheaf_isOpenImmersion hi
  -- The map on points of `f` is closed, `f` being finite.
  have hclosed : IsClosedMap (pointsMap B S hS X.obj f.hom) :=
    isClosedMap_pointsMap_of_universallyClosed' B S hS Y.property
      (universallyClosed_of_presheaf_universallyClosed B S hS X.property Y.property hflf.rep
        (presheaf_universallyClosed_of_presheaf_isFiniteLocallyFree B S hS hflf))
  -- The point set of the affine open is open.
  have hI : IsOpenSubspace B S hS (Subfunctor.range i) :=
    isOpenSubspace_range_of_isAlgebraicSpace B S hS (isAlgebraicSpace_yoneda B S hS U) i hi
  have hcar : ∀ {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : A ⟶ X.obj) [Mono g]
      (hg : IsOpenSubspace B S hS (Subfunctor.range g)),
      ((openSubspacesOrderIso B S hS X.obj X.property) ⟨Subfunctor.range g, hg⟩).carrier =
        Set.range (pointsMap B S hS A g) := fun g _ hg => by
    rw [openSubspacesOrderIso_apply B S hS X.obj X.property ⟨Subfunctor.range g, hg⟩]
    exact range_pointsMap_ι_range B S hS g
  have hIcarrier := hcar i hI
  have hIopen : IsOpen (Set.range (pointsMap B S hS (yoneda.obj U) i)) := by
    rw [← hIcarrier]
    exact ((openSubspacesOrderIso B S hS X.obj X.property)
      ⟨Subfunctor.range i, hI⟩).is_open'
  -- The open subspace of `Y` away from the image of the complement.
  have hVYopen : IsOpen ((pointsMap B S hS X.obj f.hom ''
      (Set.range (pointsMap B S hS (yoneda.obj U) i))ᶜ)ᶜ) :=
    (hclosed _ hIopen.isClosed_compl).isOpen_compl
  obtain ⟨V, hV, hVcarrier⟩ :
      ∃ (V : Subfunctor Y.obj) (_ : IsOpenSubspace B S hS V),
        Set.range (pointsMap B S hS V.toFunctor V.ι) =
          (pointsMap B S hS X.obj f.hom ''
            (Set.range (pointsMap B S hS (yoneda.obj U) i))ᶜ)ᶜ := by
    refine ⟨((openSubspacesOrderIso B S hS Y.obj Y.property).symm ⟨_, hVYopen⟩).1,
      ((openSubspacesOrderIso B S hS Y.obj Y.property).symm ⟨_, hVYopen⟩).2, ?_⟩
    rw [← openSubspacesOrderIso_apply B S hS Y.obj Y.property
      ((openSubspacesOrderIso B S hS Y.obj Y.property).symm ⟨_, hVYopen⟩),
      OrderIso.apply_symm_apply]
  have hyV : y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) := by
    rw [hVcarrier]
    rintro ⟨x, hx, hxy⟩
    exact hx (hfiber x hxy)
  have hpre : ∀ x : points B S hS X.obj,
      pointsMap B S hS X.obj f.hom x ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) →
      x ∈ Set.range (pointsMap B S hS (yoneda.obj U) i) := by
    intro x hx
    rw [hVcarrier] at hx
    by_contra hxU
    exact hx ⟨x, hxU, rfl⟩
  -- The base change of `f` along `V`.
  have hPalg : IsAlgebraicSpace B S hS (pullback f.hom V.ι) :=
    isAlgebraicSpace_pullback B S hS f.hom V.ι X.property hV.1 Y.property
  have hpb : IsPullback (pullback.fst f.hom V.ι) (pullback.snd f.hom V.ι) f.hom V.ι :=
    IsPullback.of_hasPullback f.hom V.ι
  have hpopen : IsOpenImmersion B S hS (pullback.fst f.hom V.ι) :=
    presheaf_snd_of_isPullback B S hS _ hpb.flip hV.2
  have _ : Mono (pullback.fst f.hom V.ι) := mono_of_presheaf_isOpenImmersion hpopen
  have hPimg : IsOpenSubspace B S hS (Subfunctor.range (pullback.fst f.hom V.ι)) :=
    isOpenSubspace_range_of_isAlgebraicSpace B S hS hPalg _ hpopen
  have hsub : Set.range (pointsMap B S hS (pullback f.hom V.ι) (pullback.fst f.hom V.ι)) ⊆
      Set.range (pointsMap B S hS (yoneda.obj U) i) := by
    rintro x ⟨z, rfl⟩
    refine hpre _ ⟨pointsMap B S hS _ (pullback.snd f.hom V.ι) z, ?_⟩
    rw [← pointsMap_comp_apply B S hS (pullback.snd f.hom V.ι) V.ι z,
      ← pointsMap_comp_apply B S hS (pullback.fst f.hom V.ι) f.hom z, pullback.condition]
  have hle : Subfunctor.range (pullback.fst f.hom V.ι) ≤ Subfunctor.range i := by
    have hleS : (⟨Subfunctor.range (pullback.fst f.hom V.ι), hPimg⟩ :
        {G : Subfunctor X.obj // IsOpenSubspace B S hS G}) ≤ ⟨Subfunctor.range i, hI⟩ := by
      rw [← (openSubspacesOrderIso B S hS X.obj X.property).le_iff_le]
      intro z hz
      have hz' : z ∈ ((openSubspacesOrderIso B S hS X.obj X.property)
          ⟨Subfunctor.range (pullback.fst f.hom V.ι), hPimg⟩).carrier := hz
      rw [hcar] at hz'
      exact hIcarrier.symm.subset (hsub hz')
    exact hleS
  have _ : Mono (Subfunctor.homOfLe hle) := mono_of_mono_fac (Subfunctor.homOfLe_ι hle)
  have hsubOpen : IsOpenImmersion B S hS (Subfunctor.homOfLe hle) :=
    isOpenImmersion_of_isOpenSubspace_range B S hS (Subfunctor.homOfLe hle)
      (isOpenSubspace_of_le B S hS _ _ hPimg hle).2
  -- `P` is an open subspace of the affine `U`, hence a scheme immersed in it.
  set k := (asIso (Subfunctor.toRange (pullback.fst f.hom V.ι))).hom ≫
    Subfunctor.homOfLe hle ≫ (asIso (Subfunctor.toRange i)).inv
  have hkopen : IsOpenImmersion B S hS k :=
    MorphismProperty.RespectsIso.precomp _ _ _
      (MorphismProperty.RespectsIso.postcomp _ _ _ hsubOpen)
  have hPrep : (pullback f.hom V.ι).IsRepresentable :=
    isRepresentable_of_isOpenImmersion_to_yoneda B S hS U _ hkopen
  set κ := yoneda.preimage ((pullback f.hom V.ι).reprW.hom ≫ k)
  have hκopen : IsOpenImmersion B S hS (yoneda.map κ) := by
    rw [yoneda.map_preimage]
    exact MorphismProperty.RespectsIso.precomp _ _ _ hkopen
  have _ : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map κ) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsOpenImmersion.{u}) _).1 hκopen
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUaff
  have haffine : ∀ E : Set ((BigFppfOver.toScheme B S hS).obj (pullback f.hom V.ι).reprX),
      E.Finite → ∃ O : ((BigFppfOver.toScheme B S hS).obj
        (pullback f.hom V.ι).reprX).Opens, IsAffineOpen O ∧ E ⊆ O := fun E hE =>
    Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_immersion_affine
      ((BigFppfOver.toScheme B S hS).map κ) hE
  -- The projection to `V` is a surjective finite locally free chart out of that scheme.
  have hβ : ∀ P : MorphismProperty Scheme.{u},
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf f.hom →
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
        ((pullback f.hom V.ι).reprW.hom ≫ pullback.snd f.hom V.ι) := fun P hP =>
    (MorphismProperty.relative_isStableUnderBaseChange _).respectsIso.precomp _ _
      _ (presheaf_snd_of_isPullback B S hS P hpb hP)
  have hVrep : V.toFunctor.IsRepresentable :=
    isRepresentable_of_presheafSurjective_presheafFiniteLocallyFree B S hS hV.1 _
      (hβ _ hsurj) (hβ _ hflf) haffine
  -- A representable open subspace lies in the schematic locus.
  obtain ⟨v, hv⟩ := hyV
  refine ⟨pointsMap B S hS V.toFunctor
    (Subfunctor.homOfLe (le_schematicLocus B S hS Y.obj V hV hVrep)) v, ?_⟩
  rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]
  exact hv

end Reverse

/-! ### Stacks 0BA1 -/

/-- **Stacks 0BA1.** Let `X ⟶ Y` be a surjective finite locally free morphism of algebraic
spaces over a scheme `S`, and let `y` be a point of `Y`. Then the following are equivalent:

1. `y` lies in the schematic locus of `Y` — the point set of
   `AlgebraicGeometry.Space.schematicLocus`, the largest open subspace of `Y` which is a
   scheme (Tag 03JH); and
2. there is an affine open subspace of `X`, presented as an open immersion `i : h_U ⟶ X`
   from an affine object `U` of the site, whose point set contains the whole fibre of `y`.

Finite local freeness of `f` is taken in the representable sense: `f` is representable and
every represented base change of it is a finite locally free morphism of schemes.  That is
condition (1) of Tag 03ZW, which the source's Definition 03ZV — condition (2) of that tag —
is equivalent to.  Surjectivity is likewise taken after representable base change, which is
condition (1) of Tag 02YN.

The two implications are
`AlgebraicGeometry.Space.exists_isAffine_isOpenImmersion_of_mem_schematicLocus` and
`AlgebraicGeometry.Space.mem_range_pointsMap_schematicLocus_of_exists_isAffine`; see their
docstrings for the two arguments. -/
@[stacks 0BA1]
theorem mem_range_pointsMap_schematicLocus_iff_exists_isAffine_isOpenImmersion
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom)
    (hflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom)
    (y : points B S hS Y.obj) :
    y ∈ Set.range (pointsMap B S hS (schematicLocus B S hS Y.obj).toFunctor
        (schematicLocus B S hS Y.obj).ι) ↔
      ∃ (U : BigFppfOver B S hS) (i : yoneda.obj U ⟶ X.obj),
        IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧ IsOpenImmersion B S hS i ∧
        ∀ x : points B S hS X.obj, pointsMap B S hS X.obj f.hom x = y →
          x ∈ Set.range (pointsMap B S hS (yoneda.obj U) i) :=
  ⟨exists_isAffine_isOpenImmersion_of_mem_schematicLocus B S hS f hflf y,
    fun ⟨U, i, hUaff, hi, hfiber⟩ =>
      mem_range_pointsMap_schematicLocus_of_exists_isAffine B S hS f hsurj hflf y U i
        hUaff hi hfiber⟩

end AlgebraicGeometry.Space

end
