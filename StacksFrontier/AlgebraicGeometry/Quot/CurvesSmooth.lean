module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulay.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackFactorizationPresentation
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartOpenSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionLocalConstancy
import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
import StacksFrontier.Topology.Dimension.Equidimensional

/-!
# Smooth families of curves (Stacks 0DZZ)

Stacks 0DZZ produces the open substacks `Curves^{smooth,1} ⊂ Curves^{smooth} ⊂ Curves` of
families of curves whose structure morphism is smooth, respectively smooth of relative dimension
one. The unconditional ingredients of that statement are proved here: for a family of curves
`f : X → S` the locus of points of the base over which `f` is smooth is open and commutes with
arbitrary base change, and the same holds for the locus over which `f` is moreover of relative
dimension one; each locus is the point set of an open subspace of the base through which the
morphism of base schemes of a second family factors exactly when that family has the property,
which is the open `S' ⊂ S` the source's proof produces; each of the two conditions is invariant
under isomorphism of families, so that it cuts out a strictly full subcategory of the category of
families of curves; `Curves^{smooth,1}` is the intersection of `Curves^{smooth}` with
`Curves^{CM,1}`; and part (2) of the source holds in full — over a field the two conditions are
smoothness of the proper scheme, respectively smoothness together with equidimensionality of
dimension one.

## Main definitions

* `AlgebraicGeometry.IsSmoothFamily`: the defining condition of `Curves^{smooth}`.
* `AlgebraicGeometry.CurvesSmooth`: the strictly full subcategory `Curves^{smooth}` of families
  of curves cut out by that condition.
* `AlgebraicGeometry.IsSmoothDimOneFamily`: the defining condition of `Curves^{smooth,1}`,
  smoothness together with relative dimension one in the sense of part (2) of Tag 06LR.
* `AlgebraicGeometry.CurvesSmooth1`: the strictly full subcategory `Curves^{smooth,1}`.
* `AlgebraicGeometry.CurveFamily.smoothBaseLocus` and
  `AlgebraicGeometry.CurveFamily.smoothDimOneBaseLocus`: the locus in the base over which a
  family of curves is smooth, and the locus over which it is moreover of relative dimension one.

## Main results

* `AlgebraicGeometry.CurveFamily.isOpen_smoothBaseLocus`: **Stacks 0DZZ**, the open locus in the
  base.
* `AlgebraicGeometry.CurveFamily.preimage_smoothBaseLocus`: **Stacks 0DZZ**, that locus commutes
  with base change along a morphism of families.
* `AlgebraicGeometry.isSmoothFamily_iff_smoothBaseLocus_eq_univ`: a family of curves is smooth
  exactly when that locus is the whole base.
* `AlgebraicGeometry.curvesSmooth_isStrictlyFull`: **Stacks 0DZZ**, strict fullness of
  `Curves^{smooth}`.
* `AlgebraicGeometry.CurveFamily.exists_isOpenSubspace_smooth`: **Stacks 0DZZ**, the open
  subspace of the base over which a family becomes smooth, compatibly with base change — the
  open `S' ⊂ S` the source's proof produces.
* `AlgebraicGeometry.CurveFamily.isOpen_smoothDimOneBaseLocus`,
  `AlgebraicGeometry.CurveFamily.isOpen_smoothDimOneBaseLocus_of_any` and
  `AlgebraicGeometry.CurveFamily.preimage_smoothDimOneBaseLocus`: **Stacks 0DZZ**, the same two
  statements for the locus of smooth relative dimension one, the second of them for an arbitrary
  family of curves.
* `AlgebraicGeometry.CurveFamily.exists_isOpenSubspace_smoothDimOne`: **Stacks 0DZZ**, the open
  subspace of the base over which a family becomes smooth of relative dimension one.
* `AlgebraicGeometry.curvesSmooth1_isStrictlyFull`: **Stacks 0DZZ**, strict fullness of
  `Curves^{smooth,1}`.
* `AlgebraicGeometry.curvesSmooth1_le_curvesSmooth`: **Stacks 0DZZ**, the chain of subcategories
  `Curves^{smooth,1} ⊂ Curves^{smooth}`.
* `AlgebraicGeometry.isSmoothDimOneFamily_iff_isSmoothFamily_and_isCohenMacaulayDimOneFamily`:
  **Stacks 0DZZ**, `Curves^{smooth,1} = Curves^{smooth} ∩ Curves^{CM,1}`.
* `AlgebraicGeometry.isSmoothFamily_curveFamilyOfSchemeMorphism_iff` and
  `AlgebraicGeometry.isSmoothDimOneFamily_curveFamilyOfSchemeMorphism_iff_irreducibleComponents`:
  **Stacks 0DZZ**, part (2), for the family of curves attached to a proper flat morphism of
  schemes of finite presentation whose source has dimension at most one.
  `AlgebraicGeometry.isSmoothDimOneFamily_curveFamilyOfSchemeMorphism_iff` is the same statement
  with "equidimensional of dimension one" spelled as a global dimension, which forces a
  non-emptiness hypothesis on the source.
* `AlgebraicGeometry.forall_topologicalKrullDimAt_eq_iff_forall_irreducibleComponents` and
  `AlgebraicGeometry.hasRelativeDimension_schemeSpaceMap_iff_forall_irreducibleComponents`:
  relative dimension `d` over a field is "every irreducible component has dimension `d`".
* `AlgebraicGeometry.factorsThroughCurvesSmooth_iff` and
  `AlgebraicGeometry.factorsThroughCurvesSmooth1_iff`: the factorization criteria, granted an
  algebraic stack of curves carrying the respective condition as an open substack.

## Implementation notes

The base is a scheme of the big fppf site and the total space an algebraic space, so the locus
lives in the point space of Tag 03BU of the algebraic space of the base scheme, with the topology
of Tag 03BX. Openness of the locus is the smooth locus of Tag 0DZI in the total space together
with properness: the set of points at which the structure morphism is smooth is open, so its
complement is closed, and the image of that complement — the complement of the locus in the base
— is closed. Base change of the locus is
`AlgebraicGeometry.Space.isSmoothAt_iff_isSmoothAt_of_isPullback`, the flat case of Tag 02V4 read
at a point, applied to the cartesian square of a morphism of families; the structure morphism of
a family of curves being flat and locally of finite presentation, no hypothesis on the morphism
of base schemes is needed.

Strict fullness needs no separate argument: an isomorphism of families of curves is in particular
a morphism of families, so base-change invariance of smoothness (Tag 03ZE) applied to its inverse
already carries the condition across.

Openness of the locus of smooth relative dimension one has two proofs here. For a family which
is Cohen–Macaulay it is the intersection of two open loci, the relative-dimension-one one being
open because Tag 0E11 decomposes the total space into open-and-closed subspaces of constant
relative dimension; a smooth family is Cohen–Macaulay by
`AlgebraicGeometry.Space.isCohenMacaulay_of_isSmooth`, which is Tags 00T5 and 00SB read
chartwise, so that hypothesis holds on `Curves^{smooth}`, and `Curves^{smooth,1}` is the
intersection of `Curves^{smooth}` with `Curves^{CM,1}` exactly as in the source. For an arbitrary
family of curves it is again properness applied to a locus in the total space, namely the set of
points at which the structure morphism is both smooth and of relative dimension one. That set is
open without any hypothesis on the family, and in particular without restricting the family over
the open locus of smoothness in its base, which this library does not construct: smoothness at a
point is smoothness on an open subspace through it (part (2) of Tag 03ZC), the relative dimension
of a smooth morphism is locally constant (part (2) of Tag 0DRQ) and determined by its value at
one point, the inclusion of an open subspace is étale so relative dimension at a point of the
subspace is relative dimension at its image, and that inclusion is open on points by part (1) of
Tag 03BZ.

Each of the two loci is turned into an open subspace of the base by Tag 03BZ, and factoring
through it is having image in it by Tag 03IE; base change of the locus then says that the second
family has the property exactly when its morphism of base schemes factors through the subspace.
That is the open `S' ⊂ S` of the source's proof together with its compatibility with arbitrary
base change, which is what the source needs in order to cut the substack out.

The last two conditions making `Curves^{smooth}` an open substack — that it is an algebraic stack
and that its inclusion is an open immersion — rest on the algebraicity of the stack of curves
(Stacks 0D5A), which this library does not have, and are not proved here. Accordingly
`AlgebraicGeometry.factorsThroughCurvesSmooth_iff` takes the algebraic stack of curves, the
identification of its objects with families of curves and the open substack as hypotheses and
carries no tag: what it adds to `AlgebraicGeometry.Stack.exists_based_factorization_iff` of Stacks
0507 is only the translation of membership of the substack into smoothness of the corresponding
family.

Clause (2) of the source compares the two conditions on a family over a field with conditions on
the proper scheme itself. Smoothness of the family is smoothness of the morphism of schemes by
Tag 03MJ, with no hypothesis on the base; relative dimension one over a field is constancy of the
local dimension of the source, which for a source locally of finite type over the field is
equidimensionality of dimension one. "Equidimensional of dimension one" is read componentwise,
as the definition of Tag 0058 reads it: every irreducible component has dimension one. That is
the reading under which clause (2) needs no non-emptiness hypothesis on the source — the empty
scheme is smooth of relative dimension one and has no irreducible component, whereas its
`topologicalKrullDim` is `⊥`, so spelling the condition as a global dimension instead would make
the biconditional fail there. The two readings agree for a nonempty source, by Tag 0A21: the
local dimension at a point is the largest dimension of an irreducible component through it.

## References

* [Stacks Project, Tag 0DZZ](https://stacks.math.columbia.edu/tag/0DZZ)
* [Stacks Project, Tag 0DZI](https://stacks.math.columbia.edu/tag/0DZI)
* [Stacks Project, Tag 0E1F](https://stacks.math.columbia.edu/tag/0E1F)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 03ZF](https://stacks.math.columbia.edu/tag/03ZF)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0DRQ](https://stacks.math.columbia.edu/tag/0DRQ)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 0058](https://stacks.math.columbia.edu/tag/0058)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u w

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The defining condition of `Curves^{smooth}`: the structure morphism of the family of curves
is smooth in the sense of part (1) of Tag 03ZC. -/
abbrev IsSmoothFamily (X : CurveFamily B hZ) : Prop :=
  Space.IsSmooth B integerBase hZ X.toBase.hom

/-- The locus of points of the base of a family of curves over which the family is smooth: those
points of the base all of whose preimages in the total space are points at which the structure
morphism is smooth. -/
def CurveFamily.smoothBaseLocus (X : CurveFamily B hZ) :
    Set (Space.points B integerBase hZ (schemeSpace X.base).obj) :=
  {y | ∀ x : Space.points B integerBase hZ X.total.obj,
    Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom x = y →
      Space.IsSmoothAt B integerBase hZ X.toBase.hom x}

/-- For a proper family of curves, the points of the base all of whose preimages in the total
space satisfy an open condition form an open set: the image of the closed complement is closed. -/
private theorem isOpen_setOf_forall_pointsMap_eq (X : CurveFamily B hZ)
    (P : Space.points B integerBase hZ X.total.obj → Prop) (hP : IsOpen {x | P x}) :
    IsOpen {y : Space.points B integerBase hZ (schemeSpace X.base).obj |
      ∀ x, Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom x = y → P x} := by
  rw [← isClosed_compl_iff]
  have hcompl : {y : Space.points B integerBase hZ (schemeSpace X.base).obj |
        ∀ x, Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom x = y → P x}ᶜ =
      Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom '' {x | P x}ᶜ := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_image, not_forall]
    exact ⟨fun ⟨x, hx, hsm⟩ => ⟨x, hsm, hx⟩, fun ⟨x, hsm, hx⟩ => ⟨x, hx, hsm⟩⟩
  rw [hcompl]
  exact Space.isClosed_of_universallyClosed B integerBase hZ (schemeSpace X.base).property
    X.toBase.hom X.proper.universallyClosed _ hP.isClosed_compl

/-- **Stacks 0DZZ.** The locus of points of the base of a family of curves over which the family
is smooth is open.

The set of points of the total space at which the structure morphism is smooth is open by Tag
0DZI, so its complement is closed, and the family is proper, so the image of that complement —
the complement of the locus in the base — is closed. -/
@[stacks 0DZZ "the open locus in the base of smoothness"]
theorem CurveFamily.isOpen_smoothBaseLocus (X : CurveFamily B hZ) :
    IsOpen (CurveFamily.smoothBaseLocus B hZ X) :=
  isOpen_setOf_forall_pointsMap_eq B hZ X _
    (Space.isOpen_setOf_isSmoothAt B integerBase hZ X.total.property X.toBase.hom)

/-- The structure morphism of a family of curves is smooth at a point of its total space exactly
when the structure morphism of any family it maps to is smooth at the image point: the square of a
morphism of families is cartesian and the structure morphism is flat and locally of finite
presentation, so the flat case of Tag 02V4 applies. -/
theorem CurveFamily.isSmoothAt_iff_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (x : Space.points B integerBase hZ X.total.obj) :
    Space.IsSmoothAt B integerBase hZ X.toBase.hom x ↔
      Space.IsSmoothAt B integerBase hZ Y.toBase.hom
        (Space.pointsMap B integerBase hZ X.total.obj φ.totalMap.hom x) :=
  Space.isSmoothAt_iff_isSmoothAt_of_isPullback B integerBase hZ φ.cartesian Y.flat
    Y.finitePresentation.1 x

/-- **Stacks 0DZZ.** The open locus in the base over which a family of curves is smooth commutes
with base change: for a morphism of families of curves, the locus of the source is the inverse
image of the locus of the target under the morphism of base schemes. -/
@[stacks 0DZZ "base change of the open locus in the base of smoothness"]
theorem CurveFamily.preimage_smoothBaseLocus {X Y : CurveFamily B hZ} (φ : X ⟶ Y) :
    Space.pointsMap B integerBase hZ (schemeSpace X.base).obj (schemeSpaceMap φ.baseMap).hom ⁻¹'
        CurveFamily.smoothBaseLocus B hZ Y =
      CurveFamily.smoothBaseLocus B hZ X := by
  have sq := (AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian).flip
  ext y
  simp only [smoothBaseLocus, Set.mem_preimage, Set.mem_ofPred_eq]
  refine ⟨fun hy x hx => ?_, fun hy x hx => ?_⟩
  · refine (CurveFamily.isSmoothAt_iff_hom B hZ φ x).mpr (hy _ ?_)
    rw [← Space.pointsMap_apply_comm B integerBase hZ sq.w x, hx]
  · obtain ⟨w, hw, hwx⟩ := Space.exists_points_of_isPullback B integerBase hZ sq y x hx.symm
    exact hwx ▸ (CurveFamily.isSmoothAt_iff_hom B hZ φ w).mp (hy w hw)

/-- A family of curves is smooth exactly when the locus in its base of smoothness is the whole
base: smoothness of a morphism of algebraic spaces is smoothness at every point of its source, by
Tag 03ZF. -/
theorem isSmoothFamily_iff_smoothBaseLocus_eq_univ (X : CurveFamily B hZ) :
    IsSmoothFamily B hZ X ↔ CurveFamily.smoothBaseLocus B hZ X = Set.univ := by
  have htfae := (Space.isSmooth_tfae B integerBase hZ X.total.property
    (schemeSpace X.base).property X.toBase.hom).out 1 2
  rw [Set.eq_univ_iff_forall]
  exact ⟨fun hX _ x _ => htfae.mp hX x, fun hX => htfae.mpr fun x => hX _ x rfl⟩

/-- **Stacks 0DZZ.** The open subspace of the base of a family of curves over which the family
becomes smooth, in the form the source's proof produces it: for a family of curves `G` there is
an open subspace `W` of its base such that a family `F` mapping to `G` is smooth exactly when
the morphism of base schemes factors through `W`.

This is the open `S' ⊂ S` of the source, and the equivalence is its compatibility with arbitrary
base change: `W` is the open locus of smoothness of `G` in its base, factoring through it is
having image in that locus, and the locus of `F` is the inverse image of the locus of `G`. -/
@[stacks 0DZZ "the open subspace of the base over which a family becomes smooth, \
compatibly with base change"]
theorem CurveFamily.exists_isOpenSubspace_smooth (G : CurveFamily B hZ) :
    ∃ W : Subfunctor (schemeSpace G.base).obj,
      Space.IsOpenSubspace B integerBase hZ W ∧
      ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
        IsSmoothFamily B hZ F ↔
          ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
            t ≫ W.ι = (schemeSpaceMap a.baseMap).hom := by
  refine ⟨Space.openSubspaceOfPoints B integerBase hZ (schemeSpace G.base).obj
      (CurveFamily.smoothBaseLocus B hZ G),
    Space.isOpenSubspace_openSubspaceOfPoints B integerBase hZ (schemeSpace G.base).property _
      (CurveFamily.isOpen_smoothBaseLocus B hZ G), fun F a => ?_⟩
  rw [Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace G.base).property (schemeSpace F.base).property _
      (Space.isOpenSubspace_openSubspaceOfPoints B integerBase hZ (schemeSpace G.base).property _
        (CurveFamily.isOpen_smoothBaseLocus B hZ G)),
    Space.range_pointsMap_ι_openSubspaceOfPoints,
    isSmoothFamily_iff_smoothBaseLocus_eq_univ,
    ← CurveFamily.preimage_smoothBaseLocus B hZ a]
  simp only [Set.range_subset_iff, Set.eq_univ_iff_forall, Set.mem_preimage]

/-- A family of curves mapping to a smooth family of curves is smooth: it is a base change of it,
and smoothness is stable under base change by Tag 03ZE. -/
theorem CurveFamily.isSmoothFamily_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsSmoothFamily B hZ Y) : IsSmoothFamily B hZ X :=
  have h : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B integerBase hZ⦄ (k : F ⟶ G) =>
        Space.IsSmooth B integerBase hZ k.hom) :=
    Space.isSmooth_isStableUnderBaseChange B integerBase hZ
  h.of_isPullback φ.cartesian hY

/-- A family of curves is smooth exactly when every family of curves mapping to it is smooth;
that is, exactly when every base change of it is smooth. -/
theorem isSmoothFamily_iff_forall_hom (X : CurveFamily B hZ) :
    IsSmoothFamily B hZ X ↔ ∀ Y : CurveFamily B hZ, (Y ⟶ X) → IsSmoothFamily B hZ Y :=
  ⟨fun hX _ φ => CurveFamily.isSmoothFamily_of_hom B hZ φ hX, fun h => h X (𝟙 X)⟩

/-- **Stacks 0DZZ.** The condition that a family of curves be smooth is invariant under
isomorphism, so `Curves^{smooth}` is a strictly full subcategory of the category of families of
curves: the first of the three conditions making it an open substack.

An isomorphism of families of curves is a morphism of families, so this is base-change invariance
of smoothness applied to the inverse isomorphism. -/
@[stacks 0DZZ "strict fullness of the smooth subcategory"]
theorem curvesSmooth_isStrictlyFull :
    (show ObjectProperty (CurveFamily B hZ) from
      IsSmoothFamily B hZ).IsClosedUnderIsomorphisms :=
  ⟨fun ee hX => CurveFamily.isSmoothFamily_of_hom B hZ ee.inv hX⟩

/-- **Stacks 0DZZ.** The subcategory `Curves^{smooth}`: the strictly full subcategory of families
of curves whose structure morphism is smooth. -/
@[stacks 0DZZ "the smooth subcategory of the category of curves"]
abbrev CurvesSmooth :=
  (show ObjectProperty (CurveFamily B hZ) from IsSmoothFamily B hZ).FullSubcategory

/-! ### Smooth families of relative dimension one -/

/-- The defining condition of `Curves^{smooth,1}`: the structure morphism of the family of curves
is smooth in the sense of part (1) of Tag 03ZC and has relative dimension one in the sense of part
(2) of Tag 06LR. -/
abbrev IsSmoothDimOneFamily (X : CurveFamily B hZ) : Prop :=
  IsSmoothFamily B hZ X ∧ Space.HasRelativeDimension 1 B integerBase hZ X.toBase.hom

/-- A smooth family of curves is Cohen–Macaulay: a smooth morphism of algebraic spaces is
Cohen–Macaulay, its fibres being smooth over residue fields and so Cohen–Macaulay by Tags 00T5
and 00SB. -/
theorem CurveFamily.isCohenMacaulayFamily_of_isSmoothFamily (X : CurveFamily B hZ)
    (hX : IsSmoothFamily B hZ X) : IsCohenMacaulayFamily B hZ X :=
  Space.isCohenMacaulay_of_isSmooth B integerBase hZ X.toBase.hom hX

/-- **Stacks 0DZZ.** `Curves^{smooth,1}` is the intersection of `Curves^{smooth}` with
`Curves^{CM,1}`: a family of curves is smooth of relative dimension one exactly when it is smooth
and is Cohen–Macaulay of relative dimension one. -/
@[stacks 0DZZ "Curves^{smooth,1} is Curves^{smooth} intersected with Curves^{CM,1}"]
theorem isSmoothDimOneFamily_iff_isSmoothFamily_and_isCohenMacaulayDimOneFamily
    (X : CurveFamily B hZ) :
    IsSmoothDimOneFamily B hZ X ↔
      IsSmoothFamily B hZ X ∧ IsCohenMacaulayDimOneFamily B hZ X :=
  ⟨fun hX => ⟨hX.1, CurveFamily.isCohenMacaulayFamily_of_isSmoothFamily B hZ X hX.1, hX.2⟩,
    fun hX => ⟨hX.1, hX.2.2⟩⟩

/-- The locus of points of the base of a family of curves over which the family is smooth and has
relative dimension one. -/
def CurveFamily.smoothDimOneBaseLocus (X : CurveFamily B hZ) :
    Set (Space.points B integerBase hZ (schemeSpace X.base).obj) :=
  CurveFamily.smoothBaseLocus B hZ X ∩ CurveFamily.relativeDimensionOneBaseLocus B hZ X

/-- **Stacks 0DZZ.** For a Cohen–Macaulay family of curves the locus in the base over which the
family is smooth and has relative dimension one is open: the locus of smoothness is open, and so
is the locus of relative dimension one by Tag 0E1F. -/
@[stacks 0DZZ "the open locus in the base of smooth relative dimension one"]
theorem CurveFamily.isOpen_smoothDimOneBaseLocus (X : CurveFamily B hZ)
    (hX : IsCohenMacaulayFamily B hZ X) :
    IsOpen (CurveFamily.smoothDimOneBaseLocus B hZ X) :=
  (CurveFamily.isOpen_smoothBaseLocus B hZ X).inter
    (CurveFamily.isOpen_relativeDimensionOneBaseLocus B hZ X hX)

/-- **Stacks 0DZZ.** For a smooth family of curves the locus in the base over which the family is
smooth and has relative dimension one is open: a smooth family is Cohen–Macaulay. -/
@[stacks 0DZZ "the open locus in the base of smooth relative dimension one, for a smooth family"]
theorem CurveFamily.isOpen_smoothDimOneBaseLocus_of_isSmoothFamily (X : CurveFamily B hZ)
    (hX : IsSmoothFamily B hZ X) :
    IsOpen (CurveFamily.smoothDimOneBaseLocus B hZ X) :=
  CurveFamily.isOpen_smoothDimOneBaseLocus B hZ X
    (CurveFamily.isCohenMacaulayFamily_of_isSmoothFamily B hZ X hX)

/-- The locus of points at which a smooth morphism of algebraic spaces has relative dimension
`d` is open: the relative dimension of a smooth morphism is locally constant by part (2) of
Tag 0DRQ, and the value at a point determines it. -/
private theorem isOpen_setOf_hasRelativeDimensionAt_of_isSmooth
    {F G : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B integerBase hZ F) (hG : IsAlgebraicSpace B integerBase hZ G)
    (f : F ⟶ G) (hf : Space.IsSmooth B integerBase hZ f) (d : ℕ∞) :
    IsOpen {x : Space.points B integerBase hZ F |
      Space.HasRelativeDimensionAt d B integerBase hZ f x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨W, d', hW, hxW, hconst⟩ :=
    Space.exists_isOpen_forall_hasRelativeDimensionAt_of_isSmooth B integerBase hZ hF hG f hf x
  obtain rfl : d' = d :=
    eq_of_hasRelativeDimensionAt B hZ hF hG f x (hconst x hxW) hx
  exact ⟨W, fun y hy => hconst y hy, hW, hxW⟩

/-- The set of points of the total space of a family of curves at which the structure morphism
is smooth and has relative dimension one is open.

Smoothness at a point is smoothness on an open subspace through it, by part (2) of Tag 03ZC, so
the set is the union over the open subspaces on which the structure morphism is smooth of the
image of the locus of relative dimension one there. On each such subspace the structure morphism
is smooth, so that locus is open by part (2) of Tag 0DRQ; the inclusion of an open subspace is
étale, so relative dimension at a point of the subspace is relative dimension at its image; and
the inclusion is open on points by part (1) of Tag 03BZ, so each image is open. -/
private theorem isOpen_setOf_isSmoothAt_and_hasRelativeDimensionAt (X : CurveFamily B hZ) :
    IsOpen {x : Space.points B integerBase hZ X.total.obj |
      Space.IsSmoothAt B integerBase hZ X.toBase.hom x ∧
        Space.HasRelativeDimensionAt ((1 : ℕ) : ℕ∞) B integerBase hZ X.toBase.hom x} := by
  have hEq : {x : Space.points B integerBase hZ X.total.obj |
        Space.IsSmoothAt B integerBase hZ X.toBase.hom x ∧
          Space.HasRelativeDimensionAt ((1 : ℕ) : ℕ∞) B integerBase hZ X.toBase.hom x} =
      ⋃ V : {V : Subfunctor X.total.obj // Space.IsOpenSubspace B integerBase hZ V ∧
          Space.IsSmooth B integerBase hZ (V.ι ≫ X.toBase.hom)},
        Space.pointsMap B integerBase hZ V.1.toFunctor V.1.ι ''
          {v : Space.points B integerBase hZ V.1.toFunctor |
            Space.HasRelativeDimensionAt ((1 : ℕ) : ℕ∞) B integerBase hZ
              (V.1.ι ≫ X.toBase.hom) v} := by
    ext x
    constructor
    · rintro ⟨⟨V, hV, p, hp, hVf⟩, hdim⟩
      refine Set.mem_iUnion.mpr ⟨⟨V, hV, hVf⟩, p, ?_, hp⟩
      exact (Space.hasRelativeDimensionAt_comp_iff B integerBase hZ _ V.ι X.toBase.hom
        (AlgebraicGeometry.Space.presheaf_etale_ι_of_isOpenSubspace B integerBase hZ _ hV) hV.1
        (schemeSpace X.base).property p).mpr (hp ▸ hdim)
    · intro hx
      obtain ⟨V, p, hdim, hp⟩ := Set.mem_iUnion.mp hx
      refine ⟨⟨V.1, V.2.1, p, hp, V.2.2⟩, hp ▸ ?_⟩
      exact (Space.hasRelativeDimensionAt_comp_iff B integerBase hZ _ V.1.ι X.toBase.hom
        (AlgebraicGeometry.Space.presheaf_etale_ι_of_isOpenSubspace B integerBase hZ _ V.2.1)
        V.2.1.1 (schemeSpace X.base).property p).mp hdim
  rw [hEq]
  exact isOpen_iUnion fun V =>
    Space.isOpenMap_pointsMap_of_isOpenImmersion B integerBase hZ V.1.ι V.2.1.2 _
      (isOpen_setOf_hasRelativeDimensionAt_of_isSmooth B hZ V.2.1.1
        (schemeSpace X.base).property (V.1.ι ≫ X.toBase.hom) V.2.2 _)

/-- **Stacks 0DZZ.** For any family of curves the locus in the base over which the family is
smooth and has relative dimension one is open.

This needs no hypothesis on the family: the set of points of the total space at which the
structure morphism is smooth and has relative dimension one is open, so its complement is
closed, and the family is proper, so the image of that complement — the complement of the locus
in the base — is closed. -/
@[stacks 0DZZ "the open locus in the base of smooth relative dimension one, for any family"]
theorem CurveFamily.isOpen_smoothDimOneBaseLocus_of_any (X : CurveFamily B hZ) :
    IsOpen (CurveFamily.smoothDimOneBaseLocus B hZ X) := by
  have hlocus : CurveFamily.smoothDimOneBaseLocus B hZ X =
      {y | ∀ x, Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom x = y →
        Space.IsSmoothAt B integerBase hZ X.toBase.hom x ∧
          Space.HasRelativeDimensionAt ((1 : ℕ) : ℕ∞) B integerBase hZ X.toBase.hom x} :=
    Set.ext fun _ => ⟨fun hy x hx => ⟨hy.1 x hx, hy.2 x hx⟩,
      fun hy => ⟨fun x hx => (hy x hx).1, fun x hx => (hy x hx).2⟩⟩
  rw [hlocus]
  exact isOpen_setOf_forall_pointsMap_eq B hZ X _
    (isOpen_setOf_isSmoothAt_and_hasRelativeDimensionAt B hZ X)

/-- **Stacks 0DZZ.** The locus in the base over which a family of curves is smooth and has
relative dimension one commutes with base change: for a morphism of families of curves, the locus
of the source is the inverse image of the locus of the target under the morphism of base
schemes. -/
@[stacks 0DZZ "base change of the locus in the base of smooth relative dimension one"]
theorem CurveFamily.preimage_smoothDimOneBaseLocus {X Y : CurveFamily B hZ} (φ : X ⟶ Y) :
    Space.pointsMap B integerBase hZ (schemeSpace X.base).obj (schemeSpaceMap φ.baseMap).hom ⁻¹'
        CurveFamily.smoothDimOneBaseLocus B hZ Y =
      CurveFamily.smoothDimOneBaseLocus B hZ X := by
  rw [smoothDimOneBaseLocus, smoothDimOneBaseLocus, Set.preimage_inter,
    CurveFamily.preimage_smoothBaseLocus B hZ φ,
    CurveFamily.preimage_relativeDimensionOneBaseLocus B hZ φ]

/-- A family of curves is smooth of relative dimension one exactly when the locus in its base of
smooth relative dimension one is the whole base. -/
theorem isSmoothDimOneFamily_iff_smoothDimOneBaseLocus_eq_univ (X : CurveFamily B hZ) :
    IsSmoothDimOneFamily B hZ X ↔ CurveFamily.smoothDimOneBaseLocus B hZ X = Set.univ := by
  have htfae := (Space.isSmooth_tfae B integerBase hZ X.total.property
    (schemeSpace X.base).property X.toBase.hom).out 1 2
  rw [CurveFamily.smoothDimOneBaseLocus, Set.eq_univ_iff_forall]
  refine ⟨fun hX _ => ⟨fun x _ => htfae.mp hX.1 x, fun x _ => hX.2 x⟩,
    fun hX => ⟨htfae.mpr fun x => (hX _).1 x rfl, fun x => (hX _).2 x rfl⟩⟩

/-- **Stacks 0DZZ.** The open subspace of the base of a family of curves over which the family
becomes smooth of relative dimension one, in the form the source's proof produces it: for a
family of curves `G` there is an open subspace `W` of its base such that a family `F` mapping to
`G` is smooth of relative dimension one exactly when the morphism of base schemes factors
through `W`.

This is the open `S' ⊂ S` of the source for `Curves^{smooth,1}`, and the equivalence is its
compatibility with arbitrary base change. -/
@[stacks 0DZZ "the open subspace of the base over which a family becomes smooth of relative \
dimension one, compatibly with base change"]
theorem CurveFamily.exists_isOpenSubspace_smoothDimOne (G : CurveFamily B hZ) :
    ∃ W : Subfunctor (schemeSpace G.base).obj,
      Space.IsOpenSubspace B integerBase hZ W ∧
      ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
        IsSmoothDimOneFamily B hZ F ↔
          ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
            t ≫ W.ι = (schemeSpaceMap a.baseMap).hom := by
  refine ⟨Space.openSubspaceOfPoints B integerBase hZ (schemeSpace G.base).obj
      (CurveFamily.smoothDimOneBaseLocus B hZ G),
    Space.isOpenSubspace_openSubspaceOfPoints B integerBase hZ (schemeSpace G.base).property _
      (CurveFamily.isOpen_smoothDimOneBaseLocus_of_any B hZ G), fun F a => ?_⟩
  rw [Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace G.base).property (schemeSpace F.base).property _
      (Space.isOpenSubspace_openSubspaceOfPoints B integerBase hZ (schemeSpace G.base).property _
        (CurveFamily.isOpen_smoothDimOneBaseLocus_of_any B hZ G)),
    Space.range_pointsMap_ι_openSubspaceOfPoints,
    isSmoothDimOneFamily_iff_smoothDimOneBaseLocus_eq_univ,
    ← CurveFamily.preimage_smoothDimOneBaseLocus B hZ a]
  simp only [Set.range_subset_iff, Set.eq_univ_iff_forall, Set.mem_preimage]

/-- A family of curves mapping to a smooth family of curves of relative dimension one is smooth of
relative dimension one: it is a base change of it, and both conditions are stable under base
change. -/
theorem CurveFamily.isSmoothDimOneFamily_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsSmoothDimOneFamily B hZ Y) : IsSmoothDimOneFamily B hZ X :=
  ⟨CurveFamily.isSmoothFamily_of_hom B hZ φ hY.1,
    fun x => (CurveFamily.hasRelativeDimensionAt_iff_hom B hZ φ _ x).mpr (hY.2 _)⟩

/-- A family of curves is smooth of relative dimension one exactly when every family of curves
mapping to it is; that is, exactly when every base change of it is. -/
theorem isSmoothDimOneFamily_iff_forall_hom (X : CurveFamily B hZ) :
    IsSmoothDimOneFamily B hZ X ↔
      ∀ Y : CurveFamily B hZ, (Y ⟶ X) → IsSmoothDimOneFamily B hZ Y :=
  ⟨fun hX _ φ => CurveFamily.isSmoothDimOneFamily_of_hom B hZ φ hX, fun h => h X (𝟙 X)⟩

/-- **Stacks 0DZZ.** The condition that a family of curves be smooth of relative dimension one is
invariant under isomorphism, so `Curves^{smooth,1}` is a strictly full subcategory of the category
of families of curves: the first of the three conditions making it an open substack. -/
@[stacks 0DZZ "strict fullness of the smooth subcategory of relative dimension one"]
theorem curvesSmooth1_isStrictlyFull :
    (show ObjectProperty (CurveFamily B hZ) from
      IsSmoothDimOneFamily B hZ).IsClosedUnderIsomorphisms :=
  ⟨fun ee hX => CurveFamily.isSmoothDimOneFamily_of_hom B hZ ee.inv hX⟩

/-- **Stacks 0DZZ.** The subcategory `Curves^{smooth,1}`: the strictly full subcategory of
families of curves whose structure morphism is smooth of relative dimension one. -/
@[stacks 0DZZ "the smooth subcategory of relative dimension one"]
abbrev CurvesSmooth1 :=
  (show ObjectProperty (CurveFamily B hZ) from IsSmoothDimOneFamily B hZ).FullSubcategory

/-- **Stacks 0DZZ.** The chain `Curves^{smooth,1} ⊂ Curves^{smooth}`: a family of curves which is
smooth of relative dimension one is smooth. -/
@[stacks 0DZZ "the chain of subcategories"]
theorem curvesSmooth1_le_curvesSmooth :
    (show ObjectProperty (CurveFamily B hZ) from IsSmoothDimOneFamily B hZ) ≤
      (show ObjectProperty (CurveFamily B hZ) from IsSmoothFamily B hZ) :=
  fun _ hX => hX.1

/-! ### Equidimensionality of a given dimension, read componentwise -/

/-- For a scheme locally of finite type over a field, the local dimension is `d` at every point
exactly when every irreducible component has dimension `d`.

The right-hand side is "equidimensional of dimension `d`" read componentwise, as the definition
of Tag 0058 reads it. The two sides match because the local dimension at a point is the largest
dimension of an irreducible component through that point, by Tag 0A21. Both sides hold for the
empty scheme, which has no point and no irreducible component. -/
@[ega "IV 10.6.3" "special case"]
theorem forall_topologicalKrullDimAt_eq_iff_forall_irreducibleComponents
    (k : Type u) [Field k] (Z : Scheme.{u}) (q : Z ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    {d : ℕ} :
    (∀ z : Z, topologicalKrullDimAt Z z = (d : WithBot ℕ∞)) ↔
      ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = (d : WithBot ℕ∞) := by
  constructor
  · intro hd W hW
    have hηW : IsGenericPoint hW.1.genericPoint W :=
      hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
    have honly : ∀ V ∈ irreducibleComponents Z, hW.1.genericPoint ∈ V → V = W := by
      intro V hV hηV
      have hWV : W ⊆ V := hηW ▸ closure_minimal (Set.singleton_subset_iff.mpr hηV)
        (isClosed_of_mem_irreducibleComponents V hV)
      exact (hWV.antisymm (hW.2 hV.1 hWV)).symm
    have hlocal : topologicalKrullDimAt Z hW.1.genericPoint = topologicalKrullDim W := by
      rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k Z q hW.1.genericPoint]
      refine le_antisymm (iSup_le fun V => iSup_le fun hV => by rw [honly V hV.1 hV.2]) ?_
      exact le_iSup_of_le W (le_iSup_of_le ⟨hW, hηW.mem⟩ le_rfl)
    exact hlocal.symm.trans (hd _)
  · intro hcomp z
    rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k Z q z]
    refine le_antisymm (iSup_le fun W => iSup_le fun hW => (hcomp W hW.1).le) ?_
    exact le_iSup_of_le (irreducibleComponent z)
      (le_iSup_of_le ⟨irreducibleComponent_mem_irreducibleComponents z, mem_irreducibleComponent⟩
        (by rw [hcomp _ (irreducibleComponent_mem_irreducibleComponents z)]))

/-- **Relative dimension over a field, read componentwise.** For a morphism of the big fppf site
of the integers which is locally of finite type and whose target scheme is the spectrum of a
field, the induced morphism of algebraic spaces has relative dimension `d` exactly when every
irreducible component of the source scheme has dimension `d`.

This is `AlgebraicGeometry.hasRelativeDimension_schemeSpaceMap_iff_equidimensional` with
"equidimensional of dimension `d`" read componentwise, which is how Tag 0058 reads it. Read that
way no non-emptiness hypothesis on the source is needed: the empty scheme has relative dimension
`d` and has no irreducible component, whereas its `topologicalKrullDim` is `⊥`. -/
theorem hasRelativeDimension_schemeSpaceMap_iff_forall_irreducibleComponents (d : ℕ)
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U) (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k))
    (hft : LocallyOfFiniteType ((BigFppfOver.toScheme B integerBase hZ).map g)) :
    Space.HasRelativeDimension d B integerBase hZ (schemeSpaceMap g).hom ↔
      ∀ W ∈ irreducibleComponents ((BigFppfOver.toScheme B integerBase hZ).obj T),
        topologicalKrullDim W = (d : WithBot ℕ∞) := by
  set F := BigFppfOver.toScheme B integerBase hZ
  rw [hasRelativeDimension_schemeSpaceMap_iff_of_target_eq_spec B hZ d g k hU]
  have hgen : ∀ (Y : Scheme.{u}) (_ : Y = Spec (.of k)) (h : F.obj T ⟶ Y),
      LocallyOfFiniteType h →
      ((∀ t : F.obj T, topologicalKrullDimAt (F.obj T) t = (d : WithBot ℕ∞)) ↔
        ∀ W ∈ irreducibleComponents (F.obj T), topologicalKrullDim W = (d : WithBot ℕ∞)) := by
    intro Y hY h hh
    subst hY
    have _ : LocallyOfFiniteType h := hh
    exact forall_topologicalKrullDimAt_eq_iff_forall_irreducibleComponents k (F.obj T) h
  exact hgen _ hU (F.map g) hft

/-! ### The two conditions on a proper scheme over a field -/

/-- **Stacks 0DZZ, part (2).** The family of curves attached to a proper flat morphism of schemes
of finite presentation whose source has dimension at most one is smooth exactly when that morphism
of schemes is smooth. -/
@[stacks 0DZZ "part (2): smoothness of the proper scheme"]
theorem isSmoothFamily_curveFamilyOfSchemeMorphism_iff
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    IsSmoothFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      Smooth ((BigFppfOver.toScheme B integerBase hZ).map g) :=
  Space.isSmooth_yoneda_map_iff B integerBase hZ g

/-- **Stacks 0DZZ, part (2).** For a proper flat morphism of schemes of finite presentation with
nonempty source of dimension at most one onto the spectrum of a field, the attached family of
curves is smooth of relative dimension one exactly when the source is smooth over the field and
equidimensional of dimension one.

The source is assumed nonempty because an empty source has relative dimension one vacuously while
its dimension is `-∞`. -/
@[stacks 0DZZ "part (2): the proper scheme is smooth and equidimensional of dimension one"]
theorem isSmoothDimOneFamily_curveFamilyOfSchemeMorphism_iff
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k))
    (hne : Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj T)) :
    IsSmoothDimOneFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      (Smooth ((BigFppfOver.toScheme B integerBase hZ).map g) ∧
        Equidimensional ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) =
          (1 : WithBot ℕ∞)) := by
  have hsm := Space.isSmooth_yoneda_map_iff B integerBase hZ g
  have hft : LocallyOfFiniteType ((BigFppfOver.toScheme B integerBase hZ).map g) :=
    have _ : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g) := hlfp
    inferInstance
  have hdimOne := hasRelativeDimension_schemeSpaceMap_iff_equidimensional B hZ 1 g k hU hft hne
  rw [show ((1 : ℕ) : WithBot ℕ∞) = (1 : WithBot ℕ∞) by norm_num] at hdimOne
  exact ⟨fun hX => ⟨hsm.mp hX.1, hdimOne.mp (by exact_mod_cast hX.2)⟩,
    fun hX => ⟨hsm.mpr hX.1, by exact_mod_cast hdimOne.mpr hX.2⟩⟩

/-- **Stacks 0DZZ, part (2).** For a proper flat morphism of schemes of finite presentation
whose source has dimension at most one onto the spectrum of a field, the attached family of
curves is smooth of relative dimension one exactly when the source is smooth over the field and
equidimensional of dimension one — that is, every irreducible component of the source has
dimension one.

This is the whole of part (2) for `Curves^{smooth,1}`, with no hypothesis beyond those of the
source: "equidimensional of dimension one" is read componentwise, as the definition of Tag 0058
reads it, and so the equivalence also holds for an empty source, which is smooth of relative
dimension one and has no irreducible component. -/
@[stacks 0DZZ "part (2): the proper scheme is smooth and every irreducible component of it has \
dimension one"]
theorem isSmoothDimOneFamily_curveFamilyOfSchemeMorphism_iff_irreducibleComponents
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k)) :
    IsSmoothDimOneFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      (Smooth ((BigFppfOver.toScheme B integerBase hZ).map g) ∧
        TopologicalSpace.Equidimensional ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        ∀ W ∈ irreducibleComponents ((BigFppfOver.toScheme B integerBase hZ).obj T),
          topologicalKrullDim W = (1 : WithBot ℕ∞)) := by
  have hsm := Space.isSmooth_yoneda_map_iff B integerBase hZ g
  have hft : LocallyOfFiniteType ((BigFppfOver.toScheme B integerBase hZ).map g) :=
    have _ : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g) := hlfp
    inferInstance
  have hdimOne :=
    hasRelativeDimension_schemeSpaceMap_iff_forall_irreducibleComponents B hZ 1 g k hU hft
  rw [show ((1 : ℕ) : WithBot ℕ∞) = (1 : WithBot ℕ∞) by norm_num] at hdimOne
  refine ⟨fun hX => ?_, fun hX => ⟨hsm.mpr hX.1, by exact_mod_cast hdimOne.mpr hX.2.2⟩⟩
  have hcomp := hdimOne.mp (by exact_mod_cast hX.2)
  exact ⟨hsm.mp hX.1, fun C hC D hD => (hcomp C hC).trans (hcomp D hD).symm, hcomp⟩

/-! ### The factorization criteria -/

/-- **The factorization criterion for `Curves^{smooth}`.** Let `𝒳` be an algebraic stack over the
big fppf site of the integers whose objects are identified with families of curves by `Φ`, and let
`U` be an open substack of `𝒳` whose objects are exactly those identified with smooth families.
Then a 1-morphism into `𝒳` from a category over the site factors through `U`, over the site and up
to a 2-isomorphism, if and only if every family of curves in its image is smooth.

This result **assumes** what Stacks 0D5A would supply and this library does not have: an algebraic
stack of curves, and the fact that smoothness cuts an open substack out of it. Granted those, it
is the left-hand side of the criterion of Stacks 0507. -/
theorem factorsThroughCurvesSmooth_iff
    {𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
    (Φ : 𝒳.val.val.obj ⥤ CurveFamily B hZ) (U : Stack.OpenSubstack 𝒳)
    (hU : ∀ Z : 𝒳.val.val.obj, U.property Z ↔ IsSmoothFamily B hZ (Φ.obj Z))
    {𝒟 : BasedCategory.{u, u + 1} (BigFppfOver B integerBase hZ)} (f : 𝒟 ⥤ᵇ 𝒳.val.val) :
    (∃ g : 𝒟 ⥤ᵇ Stack.fullSubcategoryBased 𝒳 U.property,
        Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion 𝒳 U.property) ≅ f)) ↔
      ∀ Y : 𝒟.obj, IsSmoothFamily B hZ (Φ.obj (f.obj Y)) := by
  have := U.strictlyFull
  exact (Stack.exists_based_factorization_iff f).trans (forall_congr' fun Y => hU (f.obj Y))

/-- **The factorization criterion for `Curves^{smooth}`, for a 1-morphism of algebraic stacks.**

Like `AlgebraicGeometry.factorsThroughCurvesSmooth_iff` this **assumes** an algebraic stack of
curves and that smoothness cuts an open substack out of it; neither is available in this library,
Stacks 0D5A not being proved here. -/
theorem factorsThroughCurvesSmooth_iff_hom
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
    (Φ : 𝒳.val.val.obj ⥤ CurveFamily B hZ) (U : Stack.OpenSubstack 𝒳)
    (hU : ∀ Z : 𝒳.val.val.obj, U.property Z ↔ IsSmoothFamily B hZ (Φ.obj Z))
    (f : 𝒴 ⟶ 𝒳) :
    (∃ g : 𝒴.val.val ⥤ᵇ Stack.fullSubcategoryBased 𝒳 U.property,
        Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion 𝒳 U.property) ≅ f.hom.hom)) ↔
      ∀ Y : 𝒴.val.val.obj, IsSmoothFamily B hZ (Φ.obj (f.hom.hom.obj Y)) :=
  factorsThroughCurvesSmooth_iff B hZ Φ U hU f.hom.hom

/-- **The factorization criterion for `Curves^{smooth,1}`.** Let `𝒳` be an algebraic stack over
the big fppf site of the integers whose objects are identified with families of curves by `Φ`, and
let `U` be an open substack of `𝒳` whose objects are exactly those identified with smooth families
of relative dimension one. Then a 1-morphism into `𝒳` from a category over the site factors
through `U`, over the site and up to a 2-isomorphism, if and only if every family of curves in its
image is smooth of relative dimension one.

This result **assumes** what Stacks 0D5A would supply and this library does not have: an algebraic
stack of curves, and the fact that the condition cuts an open substack out of it. -/
theorem factorsThroughCurvesSmooth1_iff
    {𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
    (Φ : 𝒳.val.val.obj ⥤ CurveFamily B hZ) (U : Stack.OpenSubstack 𝒳)
    (hU : ∀ Z : 𝒳.val.val.obj, U.property Z ↔ IsSmoothDimOneFamily B hZ (Φ.obj Z))
    {𝒟 : BasedCategory.{u, u + 1} (BigFppfOver B integerBase hZ)} (f : 𝒟 ⥤ᵇ 𝒳.val.val) :
    (∃ g : 𝒟 ⥤ᵇ Stack.fullSubcategoryBased 𝒳 U.property,
        Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion 𝒳 U.property) ≅ f)) ↔
      ∀ Y : 𝒟.obj, IsSmoothDimOneFamily B hZ (Φ.obj (f.obj Y)) := by
  have := U.strictlyFull
  exact (Stack.exists_based_factorization_iff f).trans (forall_congr' fun Y => hU (f.obj Y))

/-- **The factorization criterion for `Curves^{smooth,1}`, for a 1-morphism of algebraic
stacks.**

Like `AlgebraicGeometry.factorsThroughCurvesSmooth1_iff` this **assumes** an algebraic stack of
curves and that the condition cuts an open substack out of it; neither is available in this
library, Stacks 0D5A not being proved here. -/
theorem factorsThroughCurvesSmooth1_iff_hom
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
    (Φ : 𝒳.val.val.obj ⥤ CurveFamily B hZ) (U : Stack.OpenSubstack 𝒳)
    (hU : ∀ Z : 𝒳.val.val.obj, U.property Z ↔ IsSmoothDimOneFamily B hZ (Φ.obj Z))
    (f : 𝒴 ⟶ 𝒳) :
    (∃ g : 𝒴.val.val ⥤ᵇ Stack.fullSubcategoryBased 𝒳 U.property,
        Nonempty (g.comp (Stack.fullSubcategoryBasedInclusion 𝒳 U.property) ≅ f.hom.hom)) ↔
      ∀ Y : 𝒴.val.val.obj, IsSmoothDimOneFamily B hZ (Φ.obj (f.hom.hom.obj Y)) :=
  factorsThroughCurvesSmooth1_iff B hZ Φ U hU f.hom.hom

end AlgebraicGeometry

end
