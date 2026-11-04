module

public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.DiscreteRepresentingSchemeSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSpacesDerealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize

/-!
# Properties of the morphisms a groupoid in algebraic spaces de-realizes

`AlgebraicGeometry.GroupoidInAlgebraicSpaces.derealization` carries a groupoid in algebraic
spaces whose object and arrow spaces are representable to a groupoid scheme.  Its five structure
morphisms are morphisms of *schemes*, while the hypotheses one has in hand are properties of the
structure morphisms of *presheaves* that the groupoid carries.  This file crosses that gap: for
each property a de-realized structure morphism may be asked to have, it reads that property off
the corresponding morphism of algebraic spaces.

Every transfer goes through one observation.  For a property of morphisms of schemes which is
étale local on the source and the target, the every-étale-chart condition of **Stacks 03MJ** on
a represented morphism of algebraic spaces is the property itself, which is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_schemeSpaceMap_iff`; and a de-realized structure
morphism represents the corresponding structure morphism of the groupoid, which is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.yoneda_derealization_source` and its companion.
What is left is the two identifications of the presentation, which are isomorphisms and so are
absorbed by invariance of the chart condition under isomorphism.

The pre-relation `j = (t, s)` needs one thing more.  Its de-realization is a morphism into the
binary product of the object scheme with itself taken in `CategoryTheory.Over S`, while the
hypothesis is about the morphism into the binary product of the object *space* with itself taken
in presheaves.  `AlgebraicGeometry.Space.yonedaSchemeProdIso` compares the two — Yoneda carries
the one product to the other — and
`AlgebraicGeometry.Space.yoneda_schemeSiteMap_prodLift` says the de-realized pre-relation is the
pre-relation of the groupoid read through that comparison.  This is the product counterpart of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.pairComparison`, which does the
same for the fibre product of composable pairs.

Separatedness is not a chart condition of this shape — it is a condition on the relative
diagonal — so it is transferred on its own, through
`AlgebraicGeometry.Space.isSeparated_schemeSpaceMap_iff` and
`AlgebraicGeometry.Space.isSeparated_respectsIso`.

Separatedness of the pre-relation is also *produced* here, rather than only transferred: once the
de-realized arrow scheme is zero-dimensional it has discrete underlying space, hence is a
separated scheme, and every morphism out of the arrow space is then separated. That is
`…isSeparated_of_isLocallyArtinian_derealization_arrows`, which asks nothing of the object space,
of the base, or of the morphism.

## Main definitions

* `AlgebraicGeometry.Space.schemeSiteProdFan` and `…schemeSiteProdFan_isLimit`: a binary product
  in the slice over `S` of two schemes which the site contains is a binary product in the site.
* `AlgebraicGeometry.Space.yonedaSchemeProdIso`: **Yoneda carries that product to the binary
  product of the represented presheaves.**
* `AlgebraicGeometry.Space.representingSchemeIsoOfIso`: **the chosen representing scheme of a
  presheaf already presented as the presheaf of a scheme of the site is isomorphic to that
  scheme.**

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_schemeSpaceMap_iff`: for a property étale
  local on the source and the target, the chart condition on a represented morphism of algebraic
  spaces is the property of the morphism of schemes.
* `AlgebraicGeometry.Space.yoneda_schemeSiteMap_prodLift`: the product comparison is compatible
  with the lift of a pair of morphisms.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.holdsOnEveryEtaleChart_derealization_source`,
  `…holdsOnEveryEtaleChart_derealization_target` and
  `…holdsOnEveryEtaleChart_prodLift_derealization`: the three transfers, for an arbitrary
  property étale local on the source and the target.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.locallyOfFiniteType_derealization_source`,
  `…locallyOfFiniteType_derealization_target`,
  `…unramified_prodLift_derealization`, `…isSeparated_prodLift_derealization`,
  `…locallyOfFiniteType_prodLift_derealization` and
  `…locallyQuasiFinite_prodLift_derealization`: the six transfers of the properties the division
  of **Stacks 04S4** by the piece through the identity consumes.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isLocallyArtinian_derealization_arrows`: the
  arrow scheme of the de-realization is zero-dimensional as soon as the source of the groupoid
  is locally quasi-finite and the object scheme of the de-realization is the spectrum of a
  field, and
  `…isLocallyArtinian_derealization_arrows_of_dimension_le_zero`: the same from the vanishing of
  the dimension of the arrow space, which is the form **Stacks 06FF** delivers.
* `GroupoidInAlgebraicSpaces.isSeparated_of_isLocallyArtinian_derealization_arrows`: **every
  morphism out of the arrow space is separated once the de-realized arrow scheme is
  zero-dimensional** — in particular the pre-relation is, with nothing asked of the object space
  or of the base.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.derealizationObjectsIso`: **the object scheme of
  the de-realization is the scheme whose presheaf the object space is identified with.**

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (C : BigFppfSite.{u}) {S : Scheme.{u}} (hS : C.Contains S)

/-! ### Chart-local properties across the site -/

/-- **For a property of morphisms of schemes which is étale local on the source and the target,
the every-étale-chart condition of Stacks 03MJ on the morphism of algebraic spaces represented
by a morphism of schemes over `S` is that property of the morphism of schemes.**

This is `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff` phrased for the
represented morphism of algebraic spaces, which is the shape in which the properties of a
groupoid in algebraic spaces are given. -/
theorem holdsOnEveryEtaleChart_schemeSpaceMap_iff {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P) {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (f : X ⟶ Y) :
    HoldsOnEveryEtaleChart C S hS P (siteSchemeSpaceMap C hS hX hY f).hom ↔ P f.left := by
  have h : (siteSchemeSpaceMap C hS hX hY f).hom = yoneda.map (schemeSiteMap C hS hX hY f) := rfl
  rw [h, holdsOnEveryEtaleChart_yoneda_map_iff C S hS hP, toScheme_map_schemeSiteMap_eq]
  exact Iff.rfl

/-- A morphism of the big fppf site of `S` is unramified as a morphism of algebraic spaces
exactly when the morphism of schemes underlying it is unramified.

This is `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff` at unramifiedness, which
is étale local on the source and the target by **Stacks 04R3**; the forward direction alone is
`AlgebraicGeometry.Space.isUnramified_yoneda_map`. -/
theorem isUnramified_yoneda_map_iff {U V : BigFppfOver C S hS} (k : U ⟶ V) :
    IsUnramified C S hS (yoneda.map k) ↔
      _root_.AlgebraicGeometry.Unramified ((BigFppfOver.toScheme C S hS).map k) :=
  holdsOnEveryEtaleChart_yoneda_map_iff C S hS unramified_isEtaleLocalOnSourceAndTarget k

/-- A morphism of schemes over `S` between two schemes which the site contains is unramified
exactly when the morphism of algebraic spaces it represents is. -/
theorem isUnramified_schemeSpaceMap_iff {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (f : X ⟶ Y) :
    IsUnramified C S hS (siteSchemeSpaceMap C hS hX hY f).hom ↔
      _root_.AlgebraicGeometry.Unramified f.left :=
  holdsOnEveryEtaleChart_schemeSpaceMap_iff C hS unramified_isEtaleLocalOnSourceAndTarget hX hY f

/-- A morphism of schemes over `S` between two schemes which the site contains is locally of
finite type exactly when the morphism of algebraic spaces it represents is. -/
theorem isLocallyOfFiniteType_schemeSpaceMap_iff {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (f : X ⟶ Y) :
    IsLocallyOfFiniteType C S hS (siteSchemeSpaceMap C hS hX hY f).hom ↔
      _root_.AlgebraicGeometry.LocallyOfFiniteType f.left :=
  holdsOnEveryEtaleChart_schemeSpaceMap_iff C hS
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget hX hY f

/-- A morphism of schemes over `S` between two schemes which the site contains is locally
quasi-finite exactly when the morphism of schemes under it is locally of finite type and locally
quasi-finite.

Local quasi-finiteness of a morphism of algebraic spaces is **Stacks 03XJ**, part (1), which
asks local finite type of the charts as well. -/
theorem isLocallyQuasiFinite_schemeSpaceMap_iff {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (f : X ⟶ Y) :
    IsLocallyQuasiFinite C S hS (siteSchemeSpaceMap C hS hX hY f).hom ↔
      _root_.AlgebraicGeometry.LocallyOfFiniteType f.left ∧
        _root_.AlgebraicGeometry.LocallyQuasiFinite f.left :=
  holdsOnEveryEtaleChart_schemeSpaceMap_iff C hS
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget hX hY f

/-! ### Binary products of schemes of the site -/

/-- A binary product in the slice over `S` of two schemes which the site contains, regarded in
the site, with its two projections. -/
def schemeSiteProdFan {X Y : Over S} (hX : C.Contains X.left) (hY : C.Contains Y.left)
    (hP : C.Contains (X ⨯ Y : Over S).left) :
    BinaryFan (schemeSiteObject C hS hX) (schemeSiteObject C hS hY) :=
  BinaryFan.mk (schemeSiteMap C hS hP hX prod.fst) (schemeSiteMap C hS hP hY prod.snd)

/-- That fan is a binary product in the site, because the comparison functor to schemes over `S`
is fully faithful — hence reflects limits — and returns the fan unchanged. -/
def schemeSiteProdFan_isLimit {X Y : Over S} (hX : C.Contains X.left) (hY : C.Contains Y.left)
    (hP : C.Contains (X ⨯ Y : Over S).left) :
    IsLimit (schemeSiteProdFan C hS hX hY hP) := by
  have key : IsLimit (BinaryFan.mk
      ((siteToOver C hS).map (schemeSiteMap C hS hP hX prod.fst))
      ((siteToOver C hS).map (schemeSiteMap C hS hP hY prod.snd))) := by
    simp only [siteToOver_map_schemeSiteMap]
    exact prodIsProd X Y
  exact isLimitOfReflectsOfMapIsLimit (siteToOver C hS) _ _ key

/-- Yoneda carries the binary product fan of two schemes which the site contains to a binary
product fan of the represented presheaves. -/
def yonedaSchemeProdFan_isLimit {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (hP : C.Contains (X ⨯ Y : Over S).left) :
    IsLimit (BinaryFan.mk (yoneda.map (schemeSiteMap C hS hP hX prod.fst))
      (yoneda.map (schemeSiteMap C hS hP hY prod.snd))) :=
  mapIsLimitOfPreservesOfIsLimit yoneda _ _ (schemeSiteProdFan_isLimit C hS hX hY hP)

/-- **Yoneda carries a binary product in the slice over `S` of two schemes which the site
contains to the binary product of the represented presheaves.**

The forward direction is the lift of the two represented projections, so that compatibility with
the projections is `CategoryTheory.Limits.prod.lift_fst` and its companion; the inverse is the
lift of the two projections of the presheaf product through the limit. -/
def yonedaSchemeProdIso {X Y : Over S} (hX : C.Contains X.left) (hY : C.Contains Y.left)
    (hP : C.Contains (X ⨯ Y : Over S).left) :
    yoneda.obj (schemeSiteObject C hS hP) ≅
      (yoneda.obj (schemeSiteObject C hS hX) ⨯ yoneda.obj (schemeSiteObject C hS hY) :
        (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) where
  hom := prod.lift (yoneda.map (schemeSiteMap C hS hP hX prod.fst))
    (yoneda.map (schemeSiteMap C hS hP hY prod.snd))
  inv := (yonedaSchemeProdFan_isLimit C hS hX hY hP).lift (BinaryFan.mk prod.fst prod.snd)
  hom_inv_id := by
    refine (yonedaSchemeProdFan_isLimit C hS hX hY hP).hom_ext ?_
    rintro ⟨(_ | _)⟩
    · have hfac : (yonedaSchemeProdFan_isLimit C hS hX hY hP).lift
            (BinaryFan.mk prod.fst prod.snd) ≫
          yoneda.map (schemeSiteMap C hS hP hX prod.fst) = prod.fst :=
        (yonedaSchemeProdFan_isLimit C hS hX hY hP).fac _ ⟨WalkingPair.left⟩
      change (prod.lift _ _ ≫ _) ≫ yoneda.map (schemeSiteMap C hS hP hX prod.fst) =
        𝟙 _ ≫ yoneda.map (schemeSiteMap C hS hP hX prod.fst)
      rw [Category.assoc, hfac, prod.lift_fst, Category.id_comp]
    · have hfac : (yonedaSchemeProdFan_isLimit C hS hX hY hP).lift
            (BinaryFan.mk prod.fst prod.snd) ≫
          yoneda.map (schemeSiteMap C hS hP hY prod.snd) = prod.snd :=
        (yonedaSchemeProdFan_isLimit C hS hX hY hP).fac _ ⟨WalkingPair.right⟩
      change (prod.lift _ _ ≫ _) ≫ yoneda.map (schemeSiteMap C hS hP hY prod.snd) =
        𝟙 _ ≫ yoneda.map (schemeSiteMap C hS hP hY prod.snd)
      rw [Category.assoc, hfac, prod.lift_snd, Category.id_comp]
  inv_hom_id := by
    refine prod.hom_ext ?_ ?_
    · have hfac : (yonedaSchemeProdFan_isLimit C hS hX hY hP).lift
            (BinaryFan.mk prod.fst prod.snd) ≫
          yoneda.map (schemeSiteMap C hS hP hX prod.fst) = prod.fst :=
        (yonedaSchemeProdFan_isLimit C hS hX hY hP).fac _ ⟨WalkingPair.left⟩
      rw [Category.assoc, prod.lift_fst, hfac, Category.id_comp]
    · have hfac : (yonedaSchemeProdFan_isLimit C hS hX hY hP).lift
            (BinaryFan.mk prod.fst prod.snd) ≫
          yoneda.map (schemeSiteMap C hS hP hY prod.snd) = prod.snd :=
        (yonedaSchemeProdFan_isLimit C hS hX hY hP).fac _ ⟨WalkingPair.right⟩
      rw [Category.assoc, prod.lift_snd, hfac, Category.id_comp]

/-- The identification of `AlgebraicGeometry.Space.yonedaSchemeProdIso` is compatible with the
first projection. -/
theorem yonedaSchemeProdIso_hom_fst {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (hP : C.Contains (X ⨯ Y : Over S).left) :
    (yonedaSchemeProdIso C hS hX hY hP).hom ≫ prod.fst =
      yoneda.map (schemeSiteMap C hS hP hX prod.fst) :=
  prod.lift_fst _ _

/-- The identification of `AlgebraicGeometry.Space.yonedaSchemeProdIso` is compatible with the
second projection. -/
theorem yonedaSchemeProdIso_hom_snd {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (hP : C.Contains (X ⨯ Y : Over S).left) :
    (yonedaSchemeProdIso C hS hX hY hP).hom ≫ prod.snd =
      yoneda.map (schemeSiteMap C hS hP hY prod.snd) :=
  prod.lift_snd _ _

/-- **The product comparison carries the lift of a pair of morphisms of schemes over `S` to the
lift of the pair of represented morphisms of presheaves.**  This is the product counterpart of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.pairComparison`. -/
theorem yoneda_schemeSiteMap_prodLift {X Y Z : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (hZ : C.Contains Z.left)
    (hP : C.Contains (X ⨯ Y : Over S).left) (f : Z ⟶ X) (g : Z ⟶ Y) :
    yoneda.map (schemeSiteMap C hS hZ hP (prod.lift f g)) ≫
        (yonedaSchemeProdIso C hS hX hY hP).hom =
      prod.lift (yoneda.map (schemeSiteMap C hS hZ hX f))
        (yoneda.map (schemeSiteMap C hS hZ hY g)) := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, yonedaSchemeProdIso_hom_fst, prod.lift_fst, ← yoneda.map_comp,
      ← schemeSiteMap_comp, prod.lift_fst]
  · rw [Category.assoc, yonedaSchemeProdIso_hom_snd, prod.lift_snd, ← yoneda.map_comp,
      ← schemeSiteMap_comp, prod.lift_snd]

/-! ### The chosen representing scheme against a given one -/

/-- **The chosen representing scheme of a presheaf already presented as the presheaf of a scheme
of the site is isomorphic to that scheme.**

`AlgebraicGeometry.Space.representingScheme` is a *choice*, so an identification of the presheaf
with the presheaf of a particular scheme does not make that scheme the representing one; the two
are nevertheless isomorphic, because Yoneda and the comparison functor from the site to schemes
over `S` are both fully faithful. -/
def representingSchemeIsoOfIso (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) [F.IsRepresentable]
    {V : Over S} (hV : C.Contains V.left)
    (e : F ≅ yoneda.obj (schemeSiteObject C hS hV)) :
    representingScheme C hS F ≅ V :=
  (siteToOver C hS).mapIso (yoneda.preimageIso ((representingSchemeIso C hS F).symm ≪≫ e))

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  [G.objects.obj.IsRepresentable] [G.arrows.obj.IsRepresentable]

/-! ### The source and the target -/

/-- The de-realized source, as a morphism of algebraic spaces, is the source of the groupoid
read through the two identifications of the presentation. -/
theorem siteSchemeSpaceMap_derealization_source :
    (Space.siteSchemeSpaceMap C hS (Space.contains_representingScheme C hS G.arrows.obj)
        (Space.contains_representingScheme C hS G.objects.obj) (derealization G).source).hom =
      (Space.representingSchemeIso C hS G.arrows.obj).inv ≫ G.source.hom ≫
        (Space.representingSchemeIso C hS G.objects.obj).hom :=
  yoneda_derealization_source G

/-- The de-realized target, as a morphism of algebraic spaces, is the target of the groupoid
read through the two identifications of the presentation. -/
theorem siteSchemeSpaceMap_derealization_target :
    (Space.siteSchemeSpaceMap C hS (Space.contains_representingScheme C hS G.arrows.obj)
        (Space.contains_representingScheme C hS G.objects.obj) (derealization G).target).hom =
      (Space.representingSchemeIso C hS G.arrows.obj).inv ≫ G.target.hom ≫
        (Space.representingSchemeIso C hS G.objects.obj).hom :=
  yoneda_derealization_target G

/-- A morphism of presheaves that becomes `u` after composing with isomorphisms on all sides has
any property respecting isomorphisms that `u` has. -/
private theorem property_of_comp_eq_iso_comp
    {Q : MorphismProperty ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u)} [Q.RespectsIso]
    {A A' B B' B'' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (m : A ⟶ B') (c : B' ≅ B'')
    (a : A ≅ A') (u : A' ⟶ B) (b : B ≅ B'') (h : m ≫ c.hom = a.hom ≫ u ≫ b.hom) (hu : Q u) :
    Q m :=
  (MorphismProperty.cancel_right_of_respectsIso Q m c.hom).1
    (h ▸ MorphismProperty.RespectsIso.precomp _ _ _
      (MorphismProperty.RespectsIso.postcomp _ _ _ hu))

/-- **A property étale local on the source and the target transfers from the source of the
groupoid to the source map of the de-realization.** -/
theorem holdsOnEveryEtaleChart_derealization_source {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (h : Space.HoldsOnEveryEtaleChart C S hS P G.source.hom) :
    P (derealization G).source.left := by
  let : MorphismProperty.RespectsIso
      (fun ⦃F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ F') =>
        Space.HoldsOnEveryEtaleChart C S hS P f) :=
    Space.holdsOnEveryEtaleChart_respectsIso_presheaf C S hS P
  refine (Space.holdsOnEveryEtaleChart_schemeSpaceMap_iff C hS hP
    (Space.contains_representingScheme C hS G.arrows.obj)
    (Space.contains_representingScheme C hS G.objects.obj) (derealization G).source).1 ?_
  exact property_of_comp_eq_iso_comp _ (Iso.refl _) (Space.representingSchemeIso C hS _).symm _
    (Space.representingSchemeIso C hS _)
    ((Category.comp_id _).trans (siteSchemeSpaceMap_derealization_source G)) h

/-- **A property étale local on the source and the target transfers from the target of the
groupoid to the target map of the de-realization.** -/
theorem holdsOnEveryEtaleChart_derealization_target {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (h : Space.HoldsOnEveryEtaleChart C S hS P G.target.hom) :
    P (derealization G).target.left := by
  let : MorphismProperty.RespectsIso
      (fun ⦃F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ F') =>
        Space.HoldsOnEveryEtaleChart C S hS P f) :=
    Space.holdsOnEveryEtaleChart_respectsIso_presheaf C S hS P
  refine (Space.holdsOnEveryEtaleChart_schemeSpaceMap_iff C hS hP
    (Space.contains_representingScheme C hS G.arrows.obj)
    (Space.contains_representingScheme C hS G.objects.obj) (derealization G).target).1 ?_
  exact property_of_comp_eq_iso_comp _ (Iso.refl _) (Space.representingSchemeIso C hS _).symm _
    (Space.representingSchemeIso C hS _)
    ((Category.comp_id _).trans (siteSchemeSpaceMap_derealization_target G)) h

/-- **The source map of the de-realization is locally of finite type as soon as the source of
the groupoid is.** -/
theorem locallyOfFiniteType_derealization_source
    (h : Space.IsLocallyOfFiniteType C S hS G.source.hom) :
    LocallyOfFiniteType (derealization G).source.left :=
  holdsOnEveryEtaleChart_derealization_source G
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget h

/-- **The target map of the de-realization is locally of finite type as soon as the target of
the groupoid is.** -/
theorem locallyOfFiniteType_derealization_target
    (h : Space.IsLocallyOfFiniteType C S hS G.target.hom) :
    LocallyOfFiniteType (derealization G).target.left :=
  holdsOnEveryEtaleChart_derealization_target G
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget h

/-! ### The pre-relation -/

/-- The site contains the product of the object scheme of the de-realization with itself. -/
theorem contains_prod_derealization_objects :
    C.Contains ((derealization G).objects ⨯ (derealization G).objects : Over S).left :=
  C.contains_prod_left _ _ (Space.contains_representingScheme C hS G.objects.obj)
    (Space.contains_representingScheme C hS G.objects.obj)

/-- **The de-realized pre-relation, as a morphism of algebraic spaces, is the pre-relation of
the groupoid read through the two identifications of the presentation and the product
comparison.**

This is the product counterpart of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.pairComparison`: the de-realized
pre-relation lands in the binary product taken in `CategoryTheory.Over S`, and
`AlgebraicGeometry.Space.yonedaSchemeProdIso` identifies the presheaf that product represents
with the binary product of presheaves in which the pre-relation of the groupoid lands. -/
theorem siteSchemeSpaceMap_prodLift_derealization :
    (Space.siteSchemeSpaceMap C hS (Space.contains_representingScheme C hS G.arrows.obj)
          (contains_prod_derealization_objects G)
          (prod.lift (derealization G).target (derealization G).source)).hom ≫
        (Space.yonedaSchemeProdIso C hS (Space.contains_representingScheme C hS G.objects.obj)
          (Space.contains_representingScheme C hS G.objects.obj)
          (contains_prod_derealization_objects G)).hom =
      (Space.representingSchemeIso C hS G.arrows.obj).inv ≫
        prod.lift G.target.hom G.source.hom ≫
          prod.map (Space.representingSchemeIso C hS G.objects.obj).hom
            (Space.representingSchemeIso C hS G.objects.obj).hom := by
  have hlift := Space.yoneda_schemeSiteMap_prodLift C hS
    (Space.contains_representingScheme C hS G.objects.obj)
    (Space.contains_representingScheme C hS G.objects.obj)
    (Space.contains_representingScheme C hS G.arrows.obj)
    (contains_prod_derealization_objects G)
    (derealization G).target (derealization G).source
  refine hlift.trans ?_
  rw [yoneda_derealization_target G, yoneda_derealization_source G]
  simp

/-- **A property étale local on the source and the target transfers from the pre-relation of the
groupoid to the pre-relation of the de-realization.** -/
theorem holdsOnEveryEtaleChart_prodLift_derealization {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (h : Space.HoldsOnEveryEtaleChart C S hS P (prod.lift G.target.hom G.source.hom)) :
    P (prod.lift (derealization G).target (derealization G).source).left := by
  let : MorphismProperty.RespectsIso
      (fun ⦃F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ F') =>
        Space.HoldsOnEveryEtaleChart C S hS P f) :=
    Space.holdsOnEveryEtaleChart_respectsIso_presheaf C S hS P
  refine (Space.holdsOnEveryEtaleChart_schemeSpaceMap_iff C hS hP
    (Space.contains_representingScheme C hS G.arrows.obj)
    (contains_prod_derealization_objects G)
    (prod.lift (derealization G).target (derealization G).source)).1 ?_
  exact property_of_comp_eq_iso_comp _
    (Space.yonedaSchemeProdIso C hS (Space.contains_representingScheme C hS G.objects.obj)
      (Space.contains_representingScheme C hS G.objects.obj)
      (contains_prod_derealization_objects G))
    (Space.representingSchemeIso C hS _).symm _ (prod.mapIso (Space.representingSchemeIso C hS _)
      (Space.representingSchemeIso C hS _))
    (siteSchemeSpaceMap_prodLift_derealization G) h

/-- **The pre-relation of the de-realization is unramified as soon as the pre-relation of the
groupoid is.** -/
theorem unramified_prodLift_derealization
    (h : Space.IsUnramified C S hS (prod.lift G.target.hom G.source.hom)) :
    Unramified (prod.lift (derealization G).target (derealization G).source).left :=
  holdsOnEveryEtaleChart_prodLift_derealization G unramified_isEtaleLocalOnSourceAndTarget h

/-- **The pre-relation of the de-realization is locally of finite type as soon as the
pre-relation of the groupoid is.** -/
theorem locallyOfFiniteType_prodLift_derealization
    (h : Space.IsLocallyOfFiniteType C S hS (prod.lift G.target.hom G.source.hom)) :
    LocallyOfFiniteType (prod.lift (derealization G).target (derealization G).source).left :=
  holdsOnEveryEtaleChart_prodLift_derealization G
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget h

/-- **The pre-relation of the de-realization is locally quasi-finite as soon as the pre-relation
of the groupoid is.** -/
theorem locallyQuasiFinite_prodLift_derealization
    (h : Space.IsLocallyQuasiFinite C S hS (prod.lift G.target.hom G.source.hom)) :
    LocallyQuasiFinite (prod.lift (derealization G).target (derealization G).source).left :=
  (holdsOnEveryEtaleChart_prodLift_derealization G
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget h).2

/-- **The pre-relation of the de-realization is separated as soon as the pre-relation of the
groupoid is.**

Separatedness is a condition on the relative diagonal rather than a chart condition, so this
does not go through
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.holdsOnEveryEtaleChart_prodLift_derealization`; the
comparison absorbed is the same one. -/
theorem isSeparated_prodLift_derealization
    (h : Space.IsSeparated C S hS (prod.lift G.target.hom G.source.hom)) :
    IsSeparated (prod.lift (derealization G).target (derealization G).source).left := by
  let : MorphismProperty.RespectsIso (@Space.IsSeparated C S hS) :=
    Space.isSeparated_respectsIso C S hS
  refine (Space.isSeparated_schemeSpaceMap_iff C hS
    (Space.contains_representingScheme C hS G.arrows.obj)
    (contains_prod_derealization_objects G)
    (prod.lift (derealization G).target (derealization G).source)).1 ?_
  exact property_of_comp_eq_iso_comp _
    (Space.yonedaSchemeProdIso C hS (Space.contains_representingScheme C hS G.objects.obj)
      (Space.contains_representingScheme C hS G.objects.obj)
      (contains_prod_derealization_objects G))
    (Space.representingSchemeIso C hS _).symm _ (prod.mapIso (Space.representingSchemeIso C hS _)
      (Space.representingSchemeIso C hS _))
    (siteSchemeSpaceMap_prodLift_derealization G) h

/-! ### The object scheme and the arrow scheme -/

/-- **The object scheme of the de-realization is the scheme whose presheaf the object space is
identified with.**  The chosen representing scheme need not *be* that scheme, but is isomorphic
to it. -/
def derealizationObjectsIso {V : Over S} (hV : C.Contains V.left)
    (e : G.objects.obj ≅ yoneda.obj (Space.schemeSiteObject C hS hV)) :
    (derealization G).objects ≅ V :=
  Space.representingSchemeIsoOfIso C hS G.objects.obj hV e

/-- **The arrow scheme of the de-realization is zero-dimensional** as soon as the source of the
groupoid is locally quasi-finite and the object scheme of the de-realization is the spectrum of
a field.

Local quasi-finiteness of the source over a field-valued object space is the reading through
**Stacks 0ACA** of the vanishing of the dimension of the arrow space, which is what
**Stacks 06FF** delivers; from it the arrow scheme is locally quasi-finite over the spectrum of
a field, hence zero-dimensional. -/
theorem isLocallyArtinian_derealization_arrows (k : Type u) [Field k]
    (iso : (derealization G).objects.left ≅ Spec (.of k))
    (h : Space.IsLocallyQuasiFinite C S hS G.source.hom) :
    IsLocallyArtinian (derealization G).arrows.left := by
  have : LocallyQuasiFinite (derealization G).source.left :=
    (holdsOnEveryEtaleChart_derealization_source G
      locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget h).2
  have : IsLocallyArtinian (derealization G).objects.left :=
    IsLocallyArtinian.of_isImmersion iso.hom
  exact IsLocallyArtinian.of_locallyQuasiFinite (derealization G).source.left

/-- **The arrow scheme of the de-realization is zero-dimensional** as soon as the arrow space of
the groupoid has dimension at most zero, the source of the groupoid is locally of finite type,
the object space is the presheaf of a scheme of the site with at most one point, and the object
scheme of the de-realization is the spectrum of a field.

This is the form in which **Stacks 06FF** delivers the hypothesis: that tag computes the
*dimension* of the arrow space, and **Stacks 0ACA**, condition (4) equivalent to condition (5),
turns the vanishing of that dimension into local quasi-finiteness of the source over the
object space, which is what
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isLocallyArtinian_derealization_arrows` consumes.

Only that the scheme of the object space has at most one point is used of it, which is the
hypothesis `AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_dimension_le_zero` is stated at. -/
theorem isLocallyArtinian_derealization_arrows_of_dimension_le_zero
    (K : BigFppfOver C S hS) (e : G.objects.obj ≅ yoneda.obj K)
    (hK : Subsingleton ((BigFppfOver.toScheme C S hS).obj K))
    (hsrc : Space.IsLocallyOfFiniteType C S hS G.source.hom)
    (hdim : Space.dimension C S hS G.arrows.obj G.arrows.property ≤ 0)
    (k : Type u) [Field k]
    (iso : (derealization G).objects.left ≅ Spec (.of k)) :
    IsLocallyArtinian (derealization G).arrows.left := by
  let : MorphismProperty.RespectsIso
      (fun ⦃F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ F') =>
        Space.HoldsOnEveryEtaleChart C S hS
          (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) f) :=
    Space.holdsOnEveryEtaleChart_respectsIso_presheaf C S hS _
  let : MorphismProperty.RespectsIso
      (fun ⦃F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ F') =>
        Space.HoldsOnEveryEtaleChart C S hS
          ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
            (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) f) :=
    Space.holdsOnEveryEtaleChart_respectsIso_presheaf C S hS _
  have hlft : Space.IsLocallyOfFiniteType C S hS (G.source.hom ≫ e.hom) :=
    MorphismProperty.RespectsIso.postcomp _ e.hom _ hsrc
  have hqf : Space.IsLocallyQuasiFinite C S hS (G.source.hom ≫ e.hom) :=
    (Space.isLocallyQuasiFinite_iff_dimension_le_zero C S hS G.arrows.property hK
      (G.source.hom ≫ e.hom) hlft).2 hdim
  exact isLocallyArtinian_derealization_arrows G k iso
    ((MorphismProperty.cancel_right_of_respectsIso
      (fun ⦃F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ F') =>
        Space.HoldsOnEveryEtaleChart C S hS
          ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
            (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) f)
      G.source.hom e.hom).1 hqf)

/-- **Every morphism out of the arrow space of a groupoid in algebraic spaces whose de-realized
arrow scheme is zero-dimensional is separated.** A locally Artinian scheme has discrete
underlying space, a scheme with discrete underlying space is a separated scheme, and a presheaf
identified with the one represented by such a scheme is separated over `S`, so every morphism out
of it is separated by **Stacks 04ZI** part (4).

Applied to the pre-relation `j = (t, s)` this gives its separatedness outright, with no condition
on the object space, on the base, or on `j`: a zero-dimensional arrow scheme is a disjoint union
of spectra of Artinian local rings, over which `j` is separated componentwise. -/
theorem isSeparated_of_isLocallyArtinian_derealization_arrows
    {H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : G.arrows.obj ⟶ H)
    (h : IsLocallyArtinian (derealization G).arrows.left) :
    Space.IsSeparated C S hS f :=
  Space.isSeparated_of_discreteTopology_yoneda_iso C S hS
    (Space.schemeSiteObject C hS (Space.contains_representingScheme C hS G.arrows.obj))
    (Space.representingSchemeIso C hS G.arrows.obj)
    (@IsLocallyArtinian.discreteTopology _ h) f

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
