module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.OverAField
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.BaseLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackFactorizationPresentation
public import StacksFrontier.Topology.Dimension.Equidimensional
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDimension
import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.RelativeDimensionDecomposition
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartOpenSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange

/-!
# Cohen–Macaulay families of curves (Stacks 0E0I and 0E1F)

Stacks 0E0I produces the open substack `Curves^{CM} ⊂ Curves` of Cohen–Macaulay families of
curves, and Stacks 0E1F the open substack `Curves^{CM,1} ⊂ Curves` of those which moreover have
relative dimension one. The unconditional ingredients of those statements are proved here: for a
family of curves `f : X → S` the locus of points of the base over which `f` is Cohen–Macaulay is
open and commutes with arbitrary base change; for a Cohen–Macaulay family the locus over which
it moreover has relative dimension one is open, and that locus too commutes with arbitrary base
change; and each of the two conditions is invariant under isomorphism of families, so that it
cuts out a strictly full subcategory of the category of families of curves.

## Main definitions

* `AlgebraicGeometry.IsCohenMacaulayFamily`: the defining condition of `Curves^{CM}`.
* `AlgebraicGeometry.CurvesCM`: the strictly full subcategory `Curves^{CM}` of families of
  curves cut out by that condition.
* `AlgebraicGeometry.IsCohenMacaulayDimOneFamily`: the defining condition of `Curves^{CM,1}`,
  Cohen–Macaulayness together with relative dimension one in the sense of part (2) of Tag 06LR.
* `AlgebraicGeometry.CurvesCM1`: the strictly full subcategory `Curves^{CM,1}`.
* `AlgebraicGeometry.CurveFamily.relativeDimensionOneBaseLocus` and
  `AlgebraicGeometry.CurveFamily.cohenMacaulayDimOneBaseLocus`: the locus in the base over
  which a family of curves has relative dimension one, and the locus over which it is moreover
  Cohen–Macaulay.

## Main results

* `AlgebraicGeometry.CurveFamily.isOpen_cohenMacaulayBaseLocus`: **Stacks 0E0I**, the open
  locus in the base.
* `AlgebraicGeometry.CurveFamily.preimage_cohenMacaulayBaseLocus`: **Stacks 0E0I**, that locus
  commutes with base change along a morphism of families.
* `AlgebraicGeometry.CurveFamily.isCohenMacaulayFamily_of_hom` and
  `AlgebraicGeometry.isCohenMacaulayFamily_iff_forall_hom`: a family of curves is
  Cohen–Macaulay exactly when every family of curves mapping to it is.
* `AlgebraicGeometry.curvesCM_isStrictlyFull`: **Stacks 0E0I**, strict fullness of
  `Curves^{CM}`.
* `AlgebraicGeometry.isCohenMacaulay_schemeSpaceMap_iff_of_target_eq_spec`: over the spectrum
  of a field, the structure morphism of a family whose total space is a scheme is
  Cohen–Macaulay exactly when that scheme is.
* `AlgebraicGeometry.factorsThroughCurvesCM_iff`: the factorization criterion for
  `Curves^{CM}`, granted an algebraic stack of curves carrying `Curves^{CM}` as an open
  substack.
* `AlgebraicGeometry.CurveFamily.isOpen_relativeDimensionOneBaseLocus` and
  `AlgebraicGeometry.CurveFamily.isOpen_cohenMacaulayDimOneBaseLocus`: **Stacks 0E1F**, for a
  Cohen–Macaulay family of curves the locus in the base of relative dimension one is open.
* `AlgebraicGeometry.CurveFamily.preimage_cohenMacaulayDimOneBaseLocus`: **Stacks 0E1F**, that
  locus commutes with base change along a morphism of families.
* `AlgebraicGeometry.isCohenMacaulayDimOneFamily_iff_cohenMacaulayDimOneBaseLocus_eq_univ`: a
  family of curves satisfies the defining condition of `Curves^{CM,1}` exactly when that locus
  is the whole base.
* `AlgebraicGeometry.curvesCM1_isStrictlyFull`: **Stacks 0E1F**, strict fullness of
  `Curves^{CM,1}`.
* `AlgebraicGeometry.hasRelativeDimension_schemeSpaceMap_iff_of_target_eq_spec` and
  `AlgebraicGeometry.hasRelativeDimension_schemeSpaceMap_iff_equidimensional`: over the spectrum
  of a field, the structure morphism of a family whose total space is a scheme has relative
  dimension `d` exactly when that scheme has constant local dimension `d`, equivalently — for a
  nonempty source — exactly when it is equidimensional of dimension `d`.
* `AlgebraicGeometry.factorsThroughCurvesCM1_iff`: the factorization criterion for
  `Curves^{CM,1}`, granted an algebraic stack of curves carrying `Curves^{CM,1}` as an open
  substack.

## Implementation notes

The base is a scheme of the big fppf site and the total space an algebraic space, so the locus
lives in the point space of Tag 03BU of the algebraic space of the base scheme, with the
topology of Tag 03BX. Openness and base change are the space-level statements
`AlgebraicGeometry.Space.isOpen_cohenMacaulayBaseLocus_of_isProper` and
`AlgebraicGeometry.Space.preimage_cohenMacaulayBaseLocus_of_isPullback`, whose hypotheses are
four of the fields of a family of curves; the cartesian square of a morphism of families is
cartesian in presheaves by `AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`.

Strict fullness needs no separate argument: an isomorphism of families of curves is in
particular a morphism of families, so base-change invariance of Cohen–Macaulayness applied to
its inverse already carries the condition across.

Clause (2) of the source compares Cohen–Macaulayness of a family over a field with
Cohen–Macaulayness of the proper scheme itself. That comparison is
`AlgebraicGeometry.isCohenMacaulay_schemeSpaceMap_iff_of_target_eq_spec`: the fibres of a
morphism to the spectrum of a field are the source
(`AlgebraicGeometry.isCohenMacaulay_iff_forall_fiber_of_field`), and
`AlgebraicGeometry.Space.isCohenMacaulay_yoneda_map_iff` of Tag 0E0W reads Cohen–Macaulayness
of the induced morphism of algebraic spaces off the fibres.

The last two conditions making `Curves^{CM}` an open substack — that it is an algebraic stack
and that its inclusion is an open immersion — rest on the algebraicity of the stack of curves
(Stacks 0D5A), which this library does not have, and are not proved here. Accordingly
`AlgebraicGeometry.factorsThroughCurvesCM_iff` takes the algebraic stack of curves, the
identification of its objects with families of curves and the open substack as hypotheses and
carries no tag: what it adds to `AlgebraicGeometry.Stack.exists_based_factorization_iff` of
Stacks 0507 is only the translation of membership of the substack into Cohen–Macaulayness of
the corresponding family. The same applies to
`AlgebraicGeometry.factorsThroughCurvesCM1_iff`.

Openness of the locus of relative dimension one is only proved for a family which is already
Cohen–Macaulay, which is how the source argues: it is there that Tag 0E11 decomposes the total
space into open-and-closed subspaces of constant relative dimension, so that the locus of
relative dimension one in the total space is open and its complement closed, and properness
carries that complement to a closed subset of the base. Without Cohen–Macaulayness the locus of
relative dimension one in the total space is closed — by Tag 04NT its complement, the locus of
relative dimension zero, is open — but need not be open. Base change of the locus needs no
Cohen–Macaulayness: it is part (1) of Tag 04NS applied to the cartesian square of a morphism of
families.

Clause (2) of Stacks 0E1F compares relative dimension one of a family over a field with
equidimensionality of dimension one of the proper scheme itself. Over a field the set-theoretic
fibre of a morphism through a point is the whole source, so relative dimension `d` is constancy
of the local dimension of the source, which is
`AlgebraicGeometry.hasRelativeDimension_schemeSpaceMap_iff_of_target_eq_spec`; for a nonempty
source locally of finite type over the field that is equidimensionality of dimension `d`. The
source has to be assumed nonempty for the second form: the empty scheme has relative dimension
`d` vacuously for every `d`, while its dimension is `-∞`.

## References

* [Stacks Project, Tag 0E0I](https://stacks.math.columbia.edu/tag/0E0I)
* [Stacks Project, Tag 0E10](https://stacks.math.columbia.edu/tag/0E10)
* [Stacks Project, Tag 0E11](https://stacks.math.columbia.edu/tag/0E11)
* [Stacks Project, Tag 0E1F](https://stacks.math.columbia.edu/tag/0E1F)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u w

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The defining condition of `Curves^{CM}`: the structure morphism of the family of curves is
Cohen–Macaulay in the sense of Tag 0E0V. -/
abbrev IsCohenMacaulayFamily (X : CurveFamily B hZ) : Prop :=
  Space.IsCohenMacaulay B integerBase hZ X.toBase.hom

/-- **Stacks 0E0I.** The locus of points of the base of a family of curves over which the
family is Cohen–Macaulay is open.

The family is flat and locally of finite presentation, so its Cohen–Macaulay locus in the
total space is open by Tag 0E10, and it is proper, so the image of the complement of that
locus is closed in the base. -/
@[stacks 0E0I "the open locus in the base"]
theorem CurveFamily.isOpen_cohenMacaulayBaseLocus (X : CurveFamily B hZ) :
    IsOpen (Space.cohenMacaulayBaseLocus B integerBase hZ X.toBase.hom) :=
  Space.isOpen_cohenMacaulayBaseLocus_of_isProper B integerBase hZ X.total.property
    (schemeSpace X.base).property X.toBase.hom X.flat X.finitePresentation.1 X.proper

/-- **Stacks 0E0I.** The open locus in the base over which a family of curves is
Cohen–Macaulay commutes with base change: for a morphism of families of curves, the locus of
the source is the inverse image of the locus of the target under the morphism of base
schemes. -/
@[stacks 0E0I "base change of the open locus in the base", ega "IV 6.8.2" "partial"]
theorem CurveFamily.preimage_cohenMacaulayBaseLocus {X Y : CurveFamily B hZ} (φ : X ⟶ Y) :
    Space.pointsMap B integerBase hZ (schemeSpace X.base).obj (schemeSpaceMap φ.baseMap).hom ⁻¹'
        Space.cohenMacaulayBaseLocus B integerBase hZ Y.toBase.hom =
      Space.cohenMacaulayBaseLocus B integerBase hZ X.toBase.hom :=
  Space.preimage_cohenMacaulayBaseLocus_of_isPullback B integerBase hZ Y.toBase
    (schemeSpaceMap φ.baseMap) (AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian)
    Y.flat Y.finitePresentation.1

/-- A family of curves mapping to a Cohen–Macaulay family of curves is Cohen–Macaulay: it is a
base change of it, and Cohen–Macaulayness of a flat morphism locally of finite presentation is
stable under base change. -/
@[ega "IV 6.8.2" "partial"]
theorem CurveFamily.isCohenMacaulayFamily_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsCohenMacaulayFamily B hZ Y) : IsCohenMacaulayFamily B hZ X :=
  Space.isCohenMacaulay_of_isPullback B integerBase hZ Y.toBase (schemeSpaceMap φ.baseMap)
    (AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian) Y.flat
    Y.finitePresentation.1 hY

/-- A family of curves is Cohen–Macaulay exactly when every family of curves mapping to it is
Cohen–Macaulay; that is, exactly when every base change of it is Cohen–Macaulay. -/
theorem isCohenMacaulayFamily_iff_forall_hom (X : CurveFamily B hZ) :
    IsCohenMacaulayFamily B hZ X ↔
      ∀ Y : CurveFamily B hZ, (Y ⟶ X) → IsCohenMacaulayFamily B hZ Y :=
  ⟨fun hX _ φ => CurveFamily.isCohenMacaulayFamily_of_hom B hZ φ hX,
    fun h => h X (𝟙 X)⟩

/-- **Stacks 0E0I.** The condition that a family of curves be Cohen–Macaulay is invariant under
isomorphism, so `Curves^{CM}` is a strictly full subcategory of the category of families of
curves: the first of the three conditions making it an open substack.

An isomorphism of families of curves is a morphism of families, so this is base-change
invariance of Cohen–Macaulayness applied to the inverse isomorphism. -/
@[stacks 0E0I "strict fullness of the Cohen–Macaulay subcategory"]
theorem curvesCM_isStrictlyFull :
    (show ObjectProperty (CurveFamily B hZ) from
      IsCohenMacaulayFamily B hZ).IsClosedUnderIsomorphisms :=
  ⟨fun ee hX => CurveFamily.isCohenMacaulayFamily_of_hom B hZ ee.inv hX⟩

/-- **Stacks 0E0I.** The subcategory `Curves^{CM}`: the strictly full subcategory of families
of curves whose structure morphism is Cohen–Macaulay. -/
@[stacks 0E0I "the Cohen–Macaulay subcategory of the category of curves"]
abbrev CurvesCM :=
  (show ObjectProperty (CurveFamily B hZ) from IsCohenMacaulayFamily B hZ).FullSubcategory

/-- **The Cohen–Macaulay condition over a field.** For a flat morphism of the big fppf site of
the integers with locally Noetherian fibres whose target is the spectrum of a field, the
induced morphism of algebraic spaces is Cohen–Macaulay exactly when its source scheme is
Cohen–Macaulay.

The structure morphism of the family of curves attached to such a morphism of schemes is this
induced morphism of algebraic spaces, so this identifies the two sides of clause (2) of Stacks
0E0I: Cohen–Macaulayness of the family and Cohen–Macaulayness of the proper scheme over the
field. -/
theorem isCohenMacaulay_schemeSpaceMap_iff_of_target_eq_spec
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U) (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k))
    [Flat ((BigFppfOver.toScheme B integerBase hZ).map g)]
    (hfib : ∀ v : (BigFppfOver.toScheme B integerBase hZ).obj U,
      IsLocallyNoetherian (((BigFppfOver.toScheme B integerBase hZ).map g).fiber v)) :
    Space.IsCohenMacaulay B integerBase hZ (schemeSpaceMap g).hom ↔
      IsCohenMacaulay ((BigFppfOver.toScheme B integerBase hZ).obj T) := by
  refine (Space.isCohenMacaulay_yoneda_map_iff B integerBase hZ T U g hfib).trans ?_
  refine isCohenMacaulay_iff_forall_fiber_of_isIso_fromSpecResidueField
    ((BigFppfOver.toScheme B integerBase hZ).map g) ?_ ?_
  · exact hU ▸ (inferInstance : Nonempty (Spec (CommRingCat.of k)))
  · exact hU ▸ isIso_fromSpecResidueField_of_field k

/-- **The factorization criterion for `Curves^{CM}`.** Let `𝒳` be an algebraic stack over the
big fppf site of the integers whose objects are identified with families of curves by `Φ`, and
let `U` be an open substack of `𝒳` whose objects are exactly those identified with
Cohen–Macaulay families. Then a 1-morphism into `𝒳` from a category over the site factors
through `U`, over the site and up to a 2-isomorphism, if and only if every family of curves in
its image is Cohen–Macaulay.

This result **assumes** what Stacks 0D5A would supply and this library does not have: an
algebraic stack of curves, and the fact that the Cohen–Macaulay condition cuts an open
substack out of it. Granted those, it is the left-hand side of the criterion of Stacks 0507,
which `AlgebraicGeometry.Stack.factorsThroughSubstack_iff_presentation` converts into a
condition on a presentation. -/
theorem factorsThroughCurvesCM_iff
    {𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
    (Φ : 𝒳.val.val.obj ⥤ CurveFamily B hZ) (U : Stack.OpenSubstack 𝒳)
    (hU : ∀ Z : 𝒳.val.val.obj, U.property Z ↔ IsCohenMacaulayFamily B hZ (Φ.obj Z))
    {𝒟 : BasedCategory.{u, u + 1} (BigFppfOver B integerBase hZ)} (f : 𝒟 ⥤ᵇ 𝒳.val.val) :
    (∃ g : 𝒟 ⥤ᵇ Stack.fullSubcategoryBased 𝒳 U.property,
        Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion 𝒳 U.property) ≅ f)) ↔
      ∀ Y : 𝒟.obj, IsCohenMacaulayFamily B hZ (Φ.obj (f.obj Y)) := by
  have := U.strictlyFull
  exact (Stack.exists_based_factorization_iff f).trans
    (forall_congr' fun Y => hU (f.obj Y))

/-- **The factorization criterion for `Curves^{CM}`, for a 1-morphism of algebraic stacks.**
The left-hand side is verbatim the left-hand side of the criterion of Stacks 0507, so
`AlgebraicGeometry.Stack.factorsThroughSubstack_iff_presentation` rewrites it as the
corresponding condition on a presentation of `𝒳`.

Like `AlgebraicGeometry.factorsThroughCurvesCM_iff` this **assumes** an algebraic stack of
curves and that the Cohen–Macaulay condition cuts an open substack out of it; neither is
available in this library, Stacks 0D5A not being proved here. -/
theorem factorsThroughCurvesCM_iff_hom
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
    (Φ : 𝒳.val.val.obj ⥤ CurveFamily B hZ) (U : Stack.OpenSubstack 𝒳)
    (hU : ∀ Z : 𝒳.val.val.obj, U.property Z ↔ IsCohenMacaulayFamily B hZ (Φ.obj Z))
    (f : 𝒴 ⟶ 𝒳) :
    (∃ g : 𝒴.val.val ⥤ᵇ Stack.fullSubcategoryBased 𝒳 U.property,
        Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion 𝒳 U.property) ≅ f.hom.hom)) ↔
      ∀ Y : 𝒴.val.val.obj, IsCohenMacaulayFamily B hZ (Φ.obj (f.hom.hom.obj Y)) :=
  factorsThroughCurvesCM_iff B hZ Φ U hU f.hom.hom

/-! ### Cohen–Macaulay families of relative dimension one -/

/-- The defining condition of `Curves^{CM,1}`: the structure morphism of the family of curves
is Cohen–Macaulay in the sense of Tag 0E0V and has relative dimension one in the sense of part
(2) of Tag 06LR. -/
abbrev IsCohenMacaulayDimOneFamily (X : CurveFamily B hZ) : Prop :=
  IsCohenMacaulayFamily B hZ X ∧ Space.HasRelativeDimension 1 B integerBase hZ X.toBase.hom

/-- The locus of points of the base of a family of curves over which the family has relative
dimension one: those points of the base all of whose preimages in the total space are points
at which the relative dimension of the structure morphism is one. -/
def CurveFamily.relativeDimensionOneBaseLocus (X : CurveFamily B hZ) :
    Set (Space.points B integerBase hZ (schemeSpace X.base).obj) :=
  {y | ∀ x : Space.points B integerBase hZ X.total.obj,
    Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom x = y →
      Space.HasRelativeDimensionAt ((1 : ℕ) : ℕ∞) B integerBase hZ X.toBase.hom x}

/-- The locus of points of the base of a family of curves over which the family is
Cohen–Macaulay and has relative dimension one. -/
def CurveFamily.cohenMacaulayDimOneBaseLocus (X : CurveFamily B hZ) :
    Set (Space.points B integerBase hZ (schemeSpace X.base).obj) :=
  Space.cohenMacaulayBaseLocus B integerBase hZ X.toBase.hom ∩
    CurveFamily.relativeDimensionOneBaseLocus B hZ X

/-- The relative dimension of a family of curves at a point of its total space is the relative
dimension of any family it maps to, at the image point: the square of a morphism of families is
cartesian, and relative dimension is unchanged by base change (part (1) of Tag 04NS). -/
theorem CurveFamily.hasRelativeDimensionAt_iff_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (d : ℕ∞) (x : Space.points B integerBase hZ X.total.obj) :
    Space.HasRelativeDimensionAt d B integerBase hZ X.toBase.hom x ↔
      Space.HasRelativeDimensionAt d B integerBase hZ Y.toBase.hom
        (Space.pointsMap B integerBase hZ X.total.obj φ.totalMap.hom x) :=
  Space.hasRelativeDimensionAt_iff_of_isPullback' B integerBase hZ d
    (AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian).flip Y.total.property
    (schemeSpace Y.base).property (schemeSpace X.base).property
    (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
      Y.finitePresentation.1) x

/-- **Stacks 0E1F.** The locus in the base over which a family of curves has relative dimension
one commutes with base change: for a morphism of families of curves, the locus of the source is
the inverse image of the locus of the target under the morphism of base schemes. -/
theorem CurveFamily.preimage_relativeDimensionOneBaseLocus {X Y : CurveFamily B hZ} (φ : X ⟶ Y) :
    Space.pointsMap B integerBase hZ (schemeSpace X.base).obj (schemeSpaceMap φ.baseMap).hom ⁻¹'
        CurveFamily.relativeDimensionOneBaseLocus B hZ Y =
      CurveFamily.relativeDimensionOneBaseLocus B hZ X := by
  have sq := (AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian).flip
  ext y
  simp only [relativeDimensionOneBaseLocus, Set.mem_preimage, Set.mem_ofPred_eq]
  refine ⟨fun hy x hx => ?_, fun hy x hx => ?_⟩
  · refine (CurveFamily.hasRelativeDimensionAt_iff_hom B hZ φ _ x).mpr (hy _ ?_)
    rw [← Space.pointsMap_apply_comm B integerBase hZ sq.w x, hx]
  · obtain ⟨w, hw, hwx⟩ := Space.exists_points_of_isPullback B integerBase hZ sq y x hx.symm
    exact hwx ▸ (CurveFamily.hasRelativeDimensionAt_iff_hom B hZ φ _ w).mp (hy w hw)

/-- **Stacks 0E1F.** The locus in the base over which a family of curves is Cohen–Macaulay and
has relative dimension one commutes with base change: for a morphism of families of curves, the
locus of the source is the inverse image of the locus of the target under the morphism of base
schemes. -/
@[stacks 0E1F "base change of the locus in the base of Cohen–Macaulay relative dimension one"]
theorem CurveFamily.preimage_cohenMacaulayDimOneBaseLocus {X Y : CurveFamily B hZ} (φ : X ⟶ Y) :
    Space.pointsMap B integerBase hZ (schemeSpace X.base).obj (schemeSpaceMap φ.baseMap).hom ⁻¹'
        CurveFamily.cohenMacaulayDimOneBaseLocus B hZ Y =
      CurveFamily.cohenMacaulayDimOneBaseLocus B hZ X := by
  rw [cohenMacaulayDimOneBaseLocus, cohenMacaulayDimOneBaseLocus, Set.preimage_inter,
    CurveFamily.preimage_cohenMacaulayBaseLocus B hZ φ,
    CurveFamily.preimage_relativeDimensionOneBaseLocus B hZ φ]

/-- Two values which are both the relative dimension of a morphism of algebraic spaces at a
point are equal: on one pointed étale chart at the point both are the local dimension of the
same fibre. -/
theorem eq_of_hasRelativeDimensionAt
    {F G : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B integerBase hZ F) (hG : IsAlgebraicSpace B integerBase hZ G)
    (f : F ⟶ G) (x : Space.points B integerBase hZ F) {d e : ℕ∞}
    (hd : Space.HasRelativeDimensionAt d B integerBase hZ f x)
    (he : Space.HasRelativeDimensionAt e B integerBase hZ f x) : d = e := by
  obtain ⟨c, hc⟩ := (Space.holdsOnEveryEtaleChartAtPoint_iff_some B integerBase hZ
    (@HasFiberDimensionAt.{u} e)
    (fiberDimensionAt_isEtaleLocalOnSourceAndTarget e) hF hG f x).mp he
  have hce := (hasFiberDimensionAt_ofSchemeHom_iff _ _ _).mp hc
  have hcd := (hasFiberDimensionAt_ofSchemeHom_iff _ _ _).mp (hd c)
  exact_mod_cast hcd.symm.trans hce

/-- **Stacks 0E1F.** For a Cohen–Macaulay family of curves the locus in the base over which the
family has relative dimension one is open.

By Tag 0E11 the total space is the disjoint union of open-and-closed subspaces of constant
relative dimension, and since relative dimension at a point is unique the locus of relative
dimension one in the total space is the point set of the piece of relative dimension one. That
set is open, so its complement is closed, and the family is proper, so the image of that
complement — the complement of the locus in the base — is closed. -/
@[stacks 0E1F "the open locus in the base of relative dimension one, for a Cohen–Macaulay family"]
theorem CurveFamily.isOpen_relativeDimensionOneBaseLocus (X : CurveFamily B hZ)
    (hX : IsCohenMacaulayFamily B hZ X) :
    IsOpen (CurveFamily.relativeDimensionOneBaseLocus B hZ X) := by
  obtain ⟨Xd, hclopen, hcover, -, hdim⟩ :=
    Space.exists_clopen_relativeDimension_decomposition B integerBase hZ X.total.property
      (schemeSpace X.base).property X.toBase.hom X.finitePresentation.1 hX
  have hpiece : ∀ (d : ℕ) (x' : Space.points B integerBase hZ (Xd d).toFunctor),
      Space.HasRelativeDimensionAt (d : ℕ∞) B integerBase hZ X.toBase.hom
        (Space.pointsMap B integerBase hZ (Xd d).toFunctor (Xd d).ι x') := fun d x' =>
    (Space.hasRelativeDimensionAt_comp_iff B integerBase hZ (d : ℕ∞) (Xd d).ι X.toBase.hom
      (AlgebraicGeometry.Space.presheaf_etale_ι_of_isOpenSubspace B integerBase hZ _
        (hclopen d).1) (hclopen d).1.1
      (schemeSpace X.base).property x').mp (hdim d x')
  set S : Set (Space.points B integerBase hZ X.total.obj) :=
    {x | Space.HasRelativeDimensionAt ((1 : ℕ) : ℕ∞) B integerBase hZ X.toBase.hom x} with hS
  have hrange : S = Set.range (Space.pointsMap B integerBase hZ (Xd 1).toFunctor (Xd 1).ι) := by
    ext x
    simp only [hS, Set.mem_ofPred_eq]
    refine ⟨fun hx => ?_, fun ⟨x', hx'⟩ => hx' ▸ hpiece 1 x'⟩
    obtain ⟨d, x', hx'⟩ := hcover x
    obtain rfl : d = 1 := by
      exact_mod_cast eq_of_hasRelativeDimensionAt B hZ X.total.property
        (schemeSpace X.base).property X.toBase.hom x (hx' ▸ hpiece d x') hx
    exact ⟨x', hx'⟩
  rw [← isClosed_compl_iff]
  have hcompl : (CurveFamily.relativeDimensionOneBaseLocus B hZ X)ᶜ =
      Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom '' Sᶜ := by
    ext y
    simp only [hS, relativeDimensionOneBaseLocus, Set.mem_compl_iff, Set.mem_ofPred_eq,
      Set.mem_image, not_forall]
    exact ⟨fun ⟨x, hx, hd⟩ => ⟨x, hd, hx⟩, fun ⟨x, hd, hx⟩ => ⟨x, hx, hd⟩⟩
  rw [hcompl, hrange]
  exact Space.isClosed_of_universallyClosed B integerBase hZ (schemeSpace X.base).property
    X.toBase.hom X.proper.universallyClosed _
    (Space.isOpen_range_pointsMap_of_isOpenImmersion B integerBase hZ (Xd 1).ι
      (hclopen 1).1.2).isClosed_compl

/-- **Stacks 0E1F.** For a Cohen–Macaulay family of curves the locus in the base over which the
family is Cohen–Macaulay and has relative dimension one is open: the Cohen–Macaulay locus is
then the whole base. -/
@[stacks 0E1F
  "the open locus in the base of Cohen–Macaulay relative dimension one, for a CM family"]
theorem CurveFamily.isOpen_cohenMacaulayDimOneBaseLocus (X : CurveFamily B hZ)
    (hX : IsCohenMacaulayFamily B hZ X) :
    IsOpen (CurveFamily.cohenMacaulayDimOneBaseLocus B hZ X) := by
  have hall : Space.cohenMacaulayBaseLocus B integerBase hZ X.toBase.hom = Set.univ :=
    Set.eq_univ_of_forall fun _ x _ => hX x
  rw [cohenMacaulayDimOneBaseLocus, hall, Set.univ_inter]
  exact CurveFamily.isOpen_relativeDimensionOneBaseLocus B hZ X hX

/-- A family of curves is Cohen–Macaulay of relative dimension one exactly when the locus in its
base of Cohen–Macaulay relative dimension one is the whole base. -/
theorem isCohenMacaulayDimOneFamily_iff_cohenMacaulayDimOneBaseLocus_eq_univ
    (X : CurveFamily B hZ) :
    IsCohenMacaulayDimOneFamily B hZ X ↔
      CurveFamily.cohenMacaulayDimOneBaseLocus B hZ X = Set.univ := by
  rw [CurveFamily.cohenMacaulayDimOneBaseLocus, Set.eq_univ_iff_forall]
  exact ⟨fun hX y => ⟨fun x _ => hX.1 x, fun x _ => hX.2 x⟩, fun hX =>
    ⟨fun x => (hX (Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom x)).1 x rfl,
      fun x => (hX (Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom x)).2 x rfl⟩⟩

/-- A family of curves mapping to a Cohen–Macaulay family of curves of relative dimension one is
Cohen–Macaulay of relative dimension one: it is a base change of it, and both conditions are
stable under base change. -/
theorem CurveFamily.isCohenMacaulayDimOneFamily_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsCohenMacaulayDimOneFamily B hZ Y) : IsCohenMacaulayDimOneFamily B hZ X :=
  ⟨CurveFamily.isCohenMacaulayFamily_of_hom B hZ φ hY.1,
    fun x => (CurveFamily.hasRelativeDimensionAt_iff_hom B hZ φ _ x).mpr (hY.2 _)⟩

/-- A family of curves is Cohen–Macaulay of relative dimension one exactly when every family of
curves mapping to it is; that is, exactly when every base change of it is. -/
theorem isCohenMacaulayDimOneFamily_iff_forall_hom (X : CurveFamily B hZ) :
    IsCohenMacaulayDimOneFamily B hZ X ↔
      ∀ Y : CurveFamily B hZ, (Y ⟶ X) → IsCohenMacaulayDimOneFamily B hZ Y :=
  ⟨fun hX _ φ => CurveFamily.isCohenMacaulayDimOneFamily_of_hom B hZ φ hX, fun h => h X (𝟙 X)⟩

/-- **Stacks 0E1F.** The condition that a family of curves be Cohen–Macaulay of relative
dimension one is invariant under isomorphism, so `Curves^{CM,1}` is a strictly full subcategory
of the category of families of curves: the first of the three conditions making it an open
substack.

An isomorphism of families of curves is a morphism of families, so this is base-change
invariance of the condition applied to the inverse isomorphism. -/
@[stacks 0E1F "strict fullness of the Cohen–Macaulay subcategory of relative dimension one"]
theorem curvesCM1_isStrictlyFull :
    (show ObjectProperty (CurveFamily B hZ) from
      IsCohenMacaulayDimOneFamily B hZ).IsClosedUnderIsomorphisms :=
  ⟨fun ee hX => CurveFamily.isCohenMacaulayDimOneFamily_of_hom B hZ ee.inv hX⟩

/-- **Stacks 0E1F.** The subcategory `Curves^{CM,1}`: the strictly full subcategory of families
of curves whose structure morphism is Cohen–Macaulay of relative dimension one. -/
@[stacks 0E1F "the Cohen–Macaulay subcategory of relative dimension one"]
abbrev CurvesCM1 :=
  (show ObjectProperty (CurveFamily B hZ) from IsCohenMacaulayDimOneFamily B hZ).FullSubcategory

/-- Every point of a scheme of the big fppf site is the point determined by a point of the
presheaf it represents: the canonical representative above it is one. -/
private theorem exists_pointsToScheme_eq (T : BigFppfOver B integerBase hZ)
    (t : (BigFppfOver.toScheme B integerBase hZ).obj T) :
    ∃ x : Space.points B integerBase hZ (yoneda.obj T),
      Space.pointsToScheme B integerBase hZ T x = t :=
  ⟨(Space.schemePointRepresentative B integerBase hZ T t).class B integerBase hZ (yoneda.obj T),
    Space.schemePointRepresentative_point B integerBase hZ T t⟩

/-- **Relative dimension over a field.** For a morphism of the big fppf site of the integers
whose target scheme is the spectrum of a field, the induced morphism of algebraic spaces has
relative dimension `d` in the sense of part (2) of Tag 06LR exactly when the source scheme has
local dimension `d` at every one of its points.

Over a field the set-theoretic fibre of a morphism through a point is the whole source, so the
germ-level fibre-dimension condition of Tag 04NL at a point of the source is the local dimension
of the source there. -/
theorem hasRelativeDimension_schemeSpaceMap_iff_of_target_eq_spec (d : ℕ)
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U) (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k)) :
    Space.HasRelativeDimension d B integerBase hZ (schemeSpaceMap g).hom ↔
      ∀ t : (BigFppfOver.toScheme B integerBase hZ).obj T,
        topologicalKrullDimAt ((BigFppfOver.toScheme B integerBase hZ).obj T) t =
          (d : WithBot ℕ∞) := by
  set F := BigFppfOver.toScheme B integerBase hZ
  have hgen : ∀ (Y : Scheme.{u}) (_ : Y = Spec (.of k)) (h : F.obj T ⟶ Y) (t : F.obj T),
      topologicalKrullDimAt (h.fiber (h t)) (h.asFiber t) =
        topologicalKrullDimAt (F.obj T) t := by
    intro Y hY h t
    subst hY
    exact topologicalKrullDimAt_fiber_eq_of_field h t
  have hfib := hgen _ hU (F.map g)
  have hchart := fun x : Space.points B integerBase hZ (yoneda.obj T) =>
    Space.holdsOnEveryEtaleChartAtPoint_yoneda_map_iff B integerBase hZ
      (@HasFiberDimensionAt.{u} (d : ℕ∞))
      (fiberDimensionAt_isEtaleLocalOnSourceAndTarget (d : ℕ∞)) g x
  refine ⟨fun h t => ?_, fun h x => (hchart x).mpr
    ((hasFiberDimensionAt_ofSchemeHom_iff _ _ _).mpr ((hfib _).trans (h _)))⟩
  obtain ⟨x, hx⟩ := exists_pointsToScheme_eq B hZ T t
  rw [← hx, ← hfib]
  exact (hasFiberDimensionAt_ofSchemeHom_iff _ _ _).mp ((hchart x).mp (h x))

/-- **Relative dimension over a field, as equidimensionality.** For a morphism of the big fppf
site of the integers which is locally of finite type, whose target scheme is the spectrum of a
field and whose source scheme is nonempty, the induced morphism of algebraic spaces has relative
dimension `d` exactly when the source scheme is equidimensional of dimension `d`.

The source is assumed nonempty because an empty source has relative dimension `d` vacuously
while its dimension is `-∞`. -/
theorem hasRelativeDimension_schemeSpaceMap_iff_equidimensional (d : ℕ)
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U) (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k))
    (hft : LocallyOfFiniteType ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hne : Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj T)) :
    Space.HasRelativeDimension d B integerBase hZ (schemeSpaceMap g).hom ↔
      TopologicalSpace.Equidimensional ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) =
          (d : WithBot ℕ∞) := by
  set F := BigFppfOver.toScheme B integerBase hZ
  rw [hasRelativeDimension_schemeSpaceMap_iff_of_target_eq_spec B hZ d g k hU]
  have hgen : ∀ (Y : Scheme.{u}) (_ : Y = Spec (.of k)) (h : F.obj T ⟶ Y),
      LocallyOfFiniteType h →
      ((∀ t : F.obj T, topologicalKrullDimAt (F.obj T) t = (d : WithBot ℕ∞)) ↔
        TopologicalSpace.Equidimensional (F.obj T) ∧
          topologicalKrullDim (F.obj T) = (d : WithBot ℕ∞)) := by
    intro Y hY h hh
    subst hY
    have _ : LocallyOfFiniteType h := hh
    refine ⟨fun hd => ⟨equidimensional_of_topologicalKrullDimAt_eq k (F.obj T) h hd, ?_⟩,
      fun hd t => topologicalKrullDimAt_eq_of_equidimensional k (F.obj T) h hd.1 hd.2 t⟩
    have hloc : ∀ t : F.obj T,
        TopologicalSpace.localKrullDim (F.obj T) t = (d : WithBot ℕ∞) := fun t => by
      simpa only [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim] using hd t
    rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    simp [hloc]
  exact hgen _ hU (F.map g) hft

/-- **The factorization criterion for `Curves^{CM,1}`.** Let `𝒳` be an algebraic stack over the
big fppf site of the integers whose objects are identified with families of curves by `Φ`, and
let `U` be an open substack of `𝒳` whose objects are exactly those identified with
Cohen–Macaulay families of relative dimension one. Then a 1-morphism into `𝒳` from a category
over the site factors through `U`, over the site and up to a 2-isomorphism, if and only if every
family of curves in its image is Cohen–Macaulay of relative dimension one.

This result **assumes** what Stacks 0D5A would supply and this library does not have: an
algebraic stack of curves, and the fact that the condition cuts an open substack out of it.
Granted those, it is the left-hand side of the criterion of Stacks 0507, which
`AlgebraicGeometry.Stack.factorsThroughSubstack_iff_presentation` converts into a condition on
a presentation. -/
theorem factorsThroughCurvesCM1_iff
    {𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
    (Φ : 𝒳.val.val.obj ⥤ CurveFamily B hZ) (U : Stack.OpenSubstack 𝒳)
    (hU : ∀ Z : 𝒳.val.val.obj, U.property Z ↔ IsCohenMacaulayDimOneFamily B hZ (Φ.obj Z))
    {𝒟 : BasedCategory.{u, u + 1} (BigFppfOver B integerBase hZ)} (f : 𝒟 ⥤ᵇ 𝒳.val.val) :
    (∃ g : 𝒟 ⥤ᵇ Stack.fullSubcategoryBased 𝒳 U.property,
        Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion 𝒳 U.property) ≅ f)) ↔
      ∀ Y : 𝒟.obj, IsCohenMacaulayDimOneFamily B hZ (Φ.obj (f.obj Y)) := by
  have := U.strictlyFull
  exact (Stack.exists_based_factorization_iff f).trans (forall_congr' fun Y => hU (f.obj Y))

/-- **The factorization criterion for `Curves^{CM,1}`, for a 1-morphism of algebraic stacks.**
The left-hand side is verbatim the left-hand side of the criterion of Stacks 0507, so
`AlgebraicGeometry.Stack.factorsThroughSubstack_iff_presentation` rewrites it as the
corresponding condition on a presentation of `𝒳`.

Like `AlgebraicGeometry.factorsThroughCurvesCM1_iff` this **assumes** an algebraic stack of
curves and that the condition cuts an open substack out of it; neither is available in this
library, Stacks 0D5A not being proved here. -/
theorem factorsThroughCurvesCM1_iff_hom
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
    (Φ : 𝒳.val.val.obj ⥤ CurveFamily B hZ) (U : Stack.OpenSubstack 𝒳)
    (hU : ∀ Z : 𝒳.val.val.obj, U.property Z ↔ IsCohenMacaulayDimOneFamily B hZ (Φ.obj Z))
    (f : 𝒴 ⟶ 𝒳) :
    (∃ g : 𝒴.val.val ⥤ᵇ Stack.fullSubcategoryBased 𝒳 U.property,
        Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion 𝒳 U.property) ≅ f.hom.hom)) ↔
      ∀ Y : 𝒴.val.val.obj, IsCohenMacaulayDimOneFamily B hZ (Φ.obj (f.hom.hom.obj Y)) :=
  factorsThroughCurvesCM1_iff B hZ Φ U hU f.hom.hom

end AlgebraicGeometry

end
