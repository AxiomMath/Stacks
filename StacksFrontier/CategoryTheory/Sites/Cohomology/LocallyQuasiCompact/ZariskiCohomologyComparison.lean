module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiDerivedUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.LocallyQuasiCompactTerminalOpen

/-!
# Cohomology across the Zariski comparison morphism

Let `X` be an object of the locally quasi-compact Zariski site and let
`π_X : Sh(LC_Zar/X) → Sh(X_Zar)` be the comparison morphism of topoi. For an abelian sheaf `F`
on the space `X`, the cohomology of the localized Zariski site with coefficients in `π_X^{-1}F`
agrees with the cohomology of the space `X` with coefficients in `F`:

`H^n_{Zar}(X, π_X^{-1}F) ≅ H^n(X, F)`,

naturally in `F`. This is `zariskiCohomologyComparisonIso`.

Sheaf cohomology is `Ext` out of the constant abelian sheaf `ℤ`, so the comparison is an
instance of the general transport of `Ext` out of a fixed object along an exact functor which
preserves injectives, `Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso`. Its two
inputs are available for the comparison adjunction `π_X^{-1} ⊣ π_{X,*}`: the direct image is
exact and preserves injectives, the latter because its left adjoint is exact. What that general
transport gives is the comparison read on the direct image,

`H^n_{Zar}(X, G) ≅ H^n(X, π_{X,*}G)`,

and the statement about the inverse image follows because the unit of the comparison adjunction
is an isomorphism.

The remaining input is the identification `π_X^{-1}ℤ ≅ ℤ` of the inverse image of the constant
sheaf with the constant sheaf, `constantSheafCompComparisonInverseImageIso`. It holds by
uniqueness of left adjoints: the constant sheaf functor of a site is left adjoint to sections
over a terminal object, `π_X^{-1}` is left adjoint to `π_{X,*}`, and the composite right adjoint
`π_{X,*}` followed by sections over `⊤ ⊆ X` *is* sections over the terminal object
`opensToSlice ⊤` of the slice site, because the underlying presheaf of `π_{X,*}G` is `G`
restricted along `opensToSlice`.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.constantSheafCompComparisonInverseImageIso`:
  the comparison inverse image carries the constant abelian sheaf to the constant abelian sheaf.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonDirectImageCohomologyIso`:
  cohomology of the localized Zariski site, computed on the space through the direct image.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonDirectImage_comp_sheafSections`:
  the two global-sections functors agree.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.isGrothendieckAbelian_sheafOnSpace` and
  `isGrothendieckAbelian_sheafOnSlice`: both sheaf categories are Grothendieck abelian.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.enoughInjectives_zariskiSliceSheaf`:
  abelian sheaves on the localized Zariski site have enough injectives.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiCohomologyComparisonIso`: the
  cohomology comparison.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiCohomologyComparisonIso_unconditional`
  is the same with the sheafifications, the injective resolutions and the universe of the
  `Ext`-groups discharged rather than assumed. It is registered for the tag beside the form
  above.

## Implementation notes

The equality of cohomology groups asserted by the source is recorded as an isomorphism of
cohomology *functors*, which keeps the naturality in the coefficient sheaf that the source's
canonical identification has.

The `Ext`-universe is the morphism universe of the two sheaf categories rather than an arbitrary
universe admitting `HasExt`, because the transport of `Ext` along an exact functor is proved
through right derived functors; for the same reason injective resolutions in both sheaf
categories are assumed, as they are in
`StacksFrontier/Cotangent/CohomologyPresheaf/SiteSectionsComparison.lean`. A statement at an
arbitrary `HasExt` universe would have to be transported along
`CategoryTheory.Abelian.Ext.chgUniv`, which Mathlib has only as an `Equiv`. Those two
assumptions are not restrictions: `isGrothendieckAbelian_sheafOnSpace` and
`isGrothendieckAbelian_sheafOnSlice` discharge both, since a Grothendieck abelian category has
enough injectives and `Ext`-groups in its morphism universe. They are kept as assumptions
because `HasExt` is a `Prop`-valued abbreviation and so cannot be found by instance search from
those theorems.

Stacks 0DCU numbers seven clauses, the last of which the source splits into (7a) and (7b).
`zariskiCohomologyComparisonIso` below is clause (1) and carries the tag for it. The remaining
claims are `abelianComparisonDirectImage_exact` (2), `abelianComparisonAdjunction_unit_isIso`
(3), `abelianDerivedComparisonAdjunction_unit_isIso` (4), `zariskiComparisonSquareIso` (5),
`relativeZariskiCohomologyIso` (6), `properDirectImageComparisonIsoOfProperMap` (7a) and
`properDerivedImageComparison_isIso` (7b), each of which carries the tag where it is stated.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open Stacks.Cohomology.ExtComparison

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v a b

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- Sections of the comparison direct image over the top open subset of `X` are sections over
the terminal object of the Zariski slice site. The underlying presheaf of `π_{X,*}G` is `G`
restricted along `opensToSlice`, so the two global-sections functors are equal, not merely
isomorphic. -/
theorem comparisonDirectImage_comp_sheafSections
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (A : Type a) [Category.{b} A] :
    S.comparisonDirectImage X A ⋙
        (sheafSections (Opens.grothendieckTopology X.obj) A).obj (op ⊤) =
      (sheafSections (S.zariskiTopology.over X) A).obj (op ((S.opensToSlice X).1.obj ⊤)) :=
  rfl

variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
  [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]

/-- The comparison inverse image carries the constant abelian sheaf on the space `X` to the
constant abelian sheaf on the localized Zariski site, naturally in the abelian group of values.

Both functors are left adjoint to sections over a terminal object: on the right-hand side
directly, and on the left-hand side because `π_{X,*}` followed by sections over `⊤ ⊆ X` is
sections over the terminal object `opensToSlice ⊤` of the slice site. -/
def constantSheafCompComparisonInverseImageIso :
    constantSheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} ⋙
        S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ≅
      constantSheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v} :=
  Adjunction.leftAdjointUniq
    (show constantSheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} ⋙
          S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ⊣
        (sheafSections (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}).obj
          (op ((S.opensToSlice X).1.obj ⊤)) from
      (constantSheafAdj (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}
          isTerminalTop).comp (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X))
    (constantSheafAdj (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}
      (opensToSlice_top_isTerminal S X))

/-- The comparison direct image preserves injective abelian sheaves: its left adjoint, the
comparison inverse image, is exact and so preserves monomorphisms. -/
instance abelianComparisonDirectImage_preservesInjectiveObjects :
    (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X)

/-- Abelian sheaves on an essentially small site form a Grothendieck abelian category. -/
private theorem isGrothendieckAbelian_sheaf_of_essentiallySmall.{t} {C : Type*} [Category* C]
    [EssentiallySmall.{t} C] (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{t}] :
    IsGrothendieckAbelian.{t} (Sheaf J AddCommGrpCat.{t}) :=
  have _ : PreservesLimits (forget AddCommGrpCat.{t}) := AddCommGrpCat.forget_preservesLimits
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ AddCommGrpCat.{t}

omit [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}] in
/-- Abelian sheaves on the space of an object of the Zariski site form a Grothendieck abelian
category, because the site of open subsets of a space is essentially small. In particular that
category has enough injectives and its `Ext`-groups live in its morphism universe. -/
theorem isGrothendieckAbelian_sheafOnSpace :
    IsGrothendieckAbelian.{max (u + 1) v}
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) := by
  have _ : EssentiallySmall.{max (u + 1) v} (Opens X.obj) :=
    EssentiallySmall.mk' (AsSmall.equiv.{u, u, max (u + 1) v} (C := Opens X.obj))
  exact isGrothendieckAbelian_sheaf_of_essentiallySmall _

omit [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}] in
/-- Abelian sheaves on the localized Zariski site of an object form a Grothendieck abelian
category, because the slice of the bounded site over that object is essentially small. In
particular that category has enough injectives and its `Ext`-groups live in its morphism
universe. -/
theorem isGrothendieckAbelian_sheafOnSlice :
    IsGrothendieckAbelian.{max (u + 1) v}
      (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}) := by
  have _ : EssentiallySmall.{max (u + 1) v} (Over X) :=
    EssentiallySmall.mk' (AsSmall.equiv.{u, u + 1, max (u + 1) v} (C := Over X))
  exact isGrothendieckAbelian_sheaf_of_essentiallySmall _

omit [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}] in
/-- Abelian sheaves on the localized Zariski site form a category with enough injectives, being
a Grothendieck abelian category. -/
theorem enoughInjectives_zariskiSliceSheaf :
    EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}) := by
  have : IsGrothendieckAbelian.{max (u + 1) v}
      (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}) :=
    isGrothendieckAbelian_sheafOnSlice S X
  infer_instance

omit [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}] in
/-- **Abelian sheaves on the space of an object have enough injectives**, being a Grothendieck
abelian category (`isGrothendieckAbelian_sheafOnSpace`). This is the space-side counterpart of
`enoughInjectives_zariskiSliceSheaf`; the sheafification it needs is not assumed but supplied by
`hasSheafify_opensSite`. -/
theorem enoughInjectives_spaceSheaf :
    letI := hasSheafify_opensSite.{u, w, v} S X
    EnoughInjectives
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) := by
  let := hasSheafify_opensSite.{u, w, v} S X
  let := hasSheafify_zariskiSlice.{u, w, v} S X
  have := isGrothendieckAbelian_sheafOnSpace.{u, w, v} S X
  infer_instance

omit [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}] in
/-- **Abelian sheaves on the space of an object have injective resolutions**, having enough
injectives. -/
theorem hasInjectiveResolutions_spaceSheaf :
    letI := hasSheafify_opensSite.{u, w, v} S X
    HasInjectiveResolutions
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) := by
  let := hasSheafify_opensSite.{u, w, v} S X
  let := hasSheafify_zariskiSlice.{u, w, v} S X
  have := enoughInjectives_spaceSheaf.{u, w, v} S X
  infer_instance

omit [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}] in
/-- **Abelian sheaves on the localized Zariski site of an object have injective resolutions**,
having enough injectives (`enoughInjectives_zariskiSliceSheaf`). -/
theorem hasInjectiveResolutions_zariskiSliceSheaf :
    letI := hasSheafify_zariskiSlice.{u, w, v} S X
    HasInjectiveResolutions
      (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}) := by
  let := hasSheafify_opensSite.{u, w, v} S X
  let := hasSheafify_zariskiSlice.{u, w, v} S X
  have := enoughInjectives_zariskiSliceSheaf.{u, w, v} S X
  infer_instance

omit [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}] in
/-- **The `Ext`-groups of abelian sheaves on the space of an object live in the morphism universe
of that category**, because it is Grothendieck abelian. -/
theorem hasExt_spaceSheaf :
    letI := hasSheafify_opensSite.{u, w, v} S X
    HasExt.{max (u + 1) v}
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) := by
  let := hasSheafify_opensSite.{u, w, v} S X
  let := hasSheafify_zariskiSlice.{u, w, v} S X
  have := isGrothendieckAbelian_sheafOnSpace.{u, w, v} S X
  exact IsGrothendieckAbelian.hasExt _

omit [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}] in
/-- **The `Ext`-groups of abelian sheaves on the localized Zariski site of an object live in the
morphism universe of that category**, because it is Grothendieck abelian. -/
theorem hasExt_zariskiSliceSheaf :
    letI := hasSheafify_zariskiSlice.{u, w, v} S X
    HasExt.{max (u + 1) v}
      (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}) := by
  let := hasSheafify_opensSite.{u, w, v} S X
  let := hasSheafify_zariskiSlice.{u, w, v} S X
  have := isGrothendieckAbelian_sheafOnSlice.{u, w, v} S X
  exact IsGrothendieckAbelian.hasExt _

variable
  [HasExt.{max (u + 1) v}
    (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{max (u + 1) v} (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]
  [HasInjectiveResolutions
    (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [HasInjectiveResolutions
    (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]

/-- Cohomology of the localized Zariski site is the cohomology of the space `X` with
coefficients in the comparison direct image:

`H^n_{Zar}(X, G) ≅ H^n(X, π_{X,*}G)`,

naturally in the abelian sheaf `G` on the localized site. Cohomology is `Ext` out of the
constant sheaf `ℤ`, the direct image is exact and preserves injectives, and it carries the
constant sheaf of the space to the constant sheaf of the slice site. -/
def comparisonDirectImageCohomologyIso (n : ℕ) :
    Sheaf.functorH (S.zariskiTopology.over X) n ≅
      S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v} ⋙
        Sheaf.functorH (Opens.grothendieckTopology X.obj) n :=
  extFunctorObjIsoCompOfIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X)
    ((constantSheafCompComparisonInverseImageIso.{u, w, v} S X).app
      (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) n

/-- **The cohomology comparison for the Zariski comparison morphism.** For an abelian sheaf `F`
on the space of an object `X` of the locally quasi-compact Zariski site, the cohomology of the
localized Zariski site with coefficients in `π_X^{-1}F` is the cohomology of the space `X` with
coefficients in `F`:

`H^n_{Zar}(X, π_X^{-1}F) ≅ H^n(X, F)`,

naturally in `F`. This is clause (1) of Stacks 0DCU. -/
@[stacks 0DCU "cohomology_comparison"]
def zariskiCohomologyComparisonIso (n : ℕ) :
    S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ⋙
        Sheaf.functorH (S.zariskiTopology.over X) n ≅
      Sheaf.functorH (Opens.grothendieckTopology X.obj) n :=
  have _ : IsIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit :=
    abelianComparisonAdjunction_unit_isIso.{u, w, v} S X
  Functor.isoWhiskerLeft _ (comparisonDirectImageCohomologyIso.{u, w, v} S X n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
          (asIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit).symm _ ≪≫
        Functor.leftUnitor _

omit [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{max (u + 1) v}
    (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{max (u + 1) v} (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]
  [HasInjectiveResolutions
    (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [HasInjectiveResolutions
    (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})] in
/-- **The cohomology comparison for the Zariski comparison morphism, with no hypothesis.** For
an abelian sheaf `F` on the space of an object `X` of the locally quasi-compact Zariski site,

`H^n_{Zar}(X, π_X^{-1}F) ≅ H^n(X, F)`,

naturally in `F`. This is clause (1) of Stacks 0DCU.

Nothing is assumed of the two sites: both are essentially small at this coefficient universe, so
the sheafifications, the injective resolutions and the universe of the `Ext`-groups that
`Sheaf.functorH` is built from are supplied by `hasSheafify_opensSite`,
`hasSheafify_zariskiSlice`, `hasInjectiveResolutions_spaceSheaf`,
`hasInjectiveResolutions_zariskiSliceSheaf`, `hasExt_spaceSheaf` and
`hasExt_zariskiSliceSheaf`. -/
@[stacks 0DCU "cohomology_comparison, with the sheafifications, the injective resolutions and \
the universe of the Ext-groups discharged rather than assumed"]
def zariskiCohomologyComparisonIso_unconditional (n : ℕ) :
    letI := hasSheafify_opensSite.{u, w, v} S X
    letI := hasSheafify_zariskiSlice.{u, w, v} S X
    letI := hasExt_spaceSheaf.{u, w, v} S X
    letI := hasExt_zariskiSliceSheaf.{u, w, v} S X
    letI := hasInjectiveResolutions_spaceSheaf.{u, w, v} S X
    letI := hasInjectiveResolutions_zariskiSliceSheaf.{u, w, v} S X
    S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ⋙
        Sheaf.functorH (S.zariskiTopology.over X) n ≅
      Sheaf.functorH (Opens.grothendieckTopology X.obj) n :=
  letI := hasSheafify_opensSite.{u, w, v} S X
  letI := hasSheafify_zariskiSlice.{u, w, v} S X
  letI := hasExt_spaceSheaf.{u, w, v} S X
  letI := hasExt_zariskiSliceSheaf.{u, w, v} S X
  letI := hasInjectiveResolutions_spaceSheaf.{u, w, v} S X
  letI := hasInjectiveResolutions_zariskiSliceSheaf.{u, w, v} S X
  zariskiCohomologyComparisonIso.{u, w, v} S X n

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
