module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits

/-!
# Restricting a module on an algebraic space to an étale chart

Let `F` be a presheaf on the big fppf site of `S` and let `U` be an étale chart of `F`, with
underlying scheme `chartScheme U`.  The Zariski opens of that scheme are themselves étale
charts of `F` — `AlgebraicGeometry.Space.openChart` — and this file packages that assignment
as a *functor* `(chartScheme U).Opens ⥤ SmallEtale B S hS F`, which is what is needed to
transport sheaves from the small étale site of `F` to the Zariski site of the chart.

Restriction of an `𝒪_F`-module to the chart is then the composite of three steps: restrict
the sections along that functor, change scalars along the identification of the structure
presheaf of the chart with the global functions on its opens
(`AlgebraicGeometry.Scheme.restrictFunctorΓ`), and sheafify for the Zariski topology.  The
result is a sheaf of modules on `(chartScheme U).ringCatSheaf`, so the scheme-level notions —
quasi-coherence, local projectivity of Stacks 05JP, and the rest — apply to it verbatim.

## Main definitions

* `AlgebraicGeometry.Space.openChartHomOfLE` is the inclusion of étale charts induced by an
  inclusion of Zariski opens of the chart scheme, and
  `AlgebraicGeometry.Space.openChartFunctor` the functor it makes of
  `AlgebraicGeometry.Space.openChart`.
* `AlgebraicGeometry.Space.openSubSchemeHomOfLE`, `AlgebraicGeometry.Space.openSubHomOfLE`:
  the same inclusion read in `Sch_κ` and in the big fppf category over `S`.
* `AlgebraicGeometry.Space.chartSchemeRestrictionRingHom` is the change-of-scalars map used by the
  restriction: the structure sheaf of the chart scheme maps to the global functions on its
  opens read as étale charts of `F`.
* `AlgebraicGeometry.Space.restrictToChartScheme` is the restriction of an `𝒪_F`-module to the
  chart scheme, as a sheaf of modules on that scheme, and
  `AlgebraicGeometry.Space.restrictToChartSchemeFunctor` is the same construction as a functor,
  so that an isomorphism of `𝒪_F`-modules may be transported to the chart.

## Main results

* `AlgebraicGeometry.Space.restrictToChartSchemeFunctor_obj`: the functorial restriction agrees
  with `AlgebraicGeometry.Space.restrictToChartScheme` on objects, by `rfl`.
* `AlgebraicGeometry.Space.openChartFunctor_comp_toScheme`: the underlying schemes of the
  charts produced by `openChartFunctor` are the open subschemes themselves, functorially, by `rfl`.
* `AlgebraicGeometry.Space.openSubHomOfLE_comp_openSubHom`,
  `AlgebraicGeometry.Space.openSubHomOfLE_refl` and
  `AlgebraicGeometry.Space.openSubHomOfLE_trans` are the three identities the functor laws and
  the triangle over `F` reduce to.

## Implementation notes

The morphisms of `openChartFunctor` are built with `CategoryTheory.ObjectProperty.homMk`
rather than with the fullness inverse `CategoryTheory.Functor.preimage` used by
`AlgebraicGeometry.Space.openSubHom`.  That choice is forced: the image of a morphism of the
functor under the passage to schemes must be the open inclusion `Scheme.homOfLE`
*definitionally*, since `chartSchemeRestrictionRingHom` is nothing but
`AlgebraicGeometry.Scheme.restrictFunctorΓ` read through
`openChartFunctor_comp_toScheme`, and `Functor.map_preimage` is only a propositional equality.
The commutation of the resulting triangle over `F` is then proved rather than definitional,
which is harmless because it is a proposition.

The module universe `m` of the input is independent of the universe `u` of the schemes, while
Zariski sheafification of modules needs the sections and the coefficients in one universe; the
sections are therefore raised by `SheafOfModules.uliftForPresentation` to `max u m` before
sheafifying, which is why the output is a `SheafOfModules.{max u m}`.  The two sheafification
instances for the Zariski site come from its essential smallness
(`CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`) and are
local to the construction.

`AlgebraicGeometry.Space.chartSchemeRestrictionRingHom` names the structure sheaf of the small
étale site as `AlgebraicGeometry.Space.structurePresheaf ⋙ forget₂ CommRingCat RingCat` rather
than as `(AlgebraicGeometry.RingedSite.ringSheaf (smallEtaleRingedSite ...)).obj`, to which it is
definitionally equal.  The two readings carry *different* `Category` instance terms on the
same category — the full-subcategory instance of
`AlgebraicGeometry.Space.SmallEtale` against the `category` field of the ringed site — and
with the ringed-site reading instance search fails to find
`Category (PresheafOfModules ...)` at the pushforward, the same obstruction that
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over` restates its instances
for.  The ringed site therefore does not appear in this signature at all, and
`AlgebraicGeometry.Space.restrictToChartScheme` still accepts an `AlgebraicGeometry.Space.Modules`
because the two presheaves of rings are the same.

## References

* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 060Q](https://stacks.math.columbia.edu/tag/060Q)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

variable {B S hS F} in
/-- The morphism of `Sch_κ` underlying `AlgebraicGeometry.Space.openSubHomOfLE`: the open
inclusion, read in the full subcategory cut out by the size bound. -/
noncomputable def openSubSchemeHomOfLE (A : BigFppfOver B S hS)
    {O O' : ((BigFppfOver.toScheme B S hS).obj A).Opens} (h : O ≤ O') :
    (openSub A O).left ⟶ (openSub A O').left :=
  ObjectProperty.homMk (((BigFppfOver.toScheme B S hS).obj A).homOfLE h)

variable {B S hS F} in
/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.openSubSchemeHomOfLE` is
the inclusion of the smaller open. -/
theorem inclusion_map_openSubSchemeHomOfLE (A : BigFppfOver B S hS)
    {O O' : ((BigFppfOver.toScheme B S hS).obj A).Opens} (h : O ≤ O') :
    B.inclusion.map (openSubSchemeHomOfLE A h) =
      ((BigFppfOver.toScheme B S hS).obj A).homOfLE h :=
  rfl

variable {B S hS F} in
/-- `AlgebraicGeometry.Space.openSubSchemeHomOfLE` followed by the inclusion of the larger
open is the inclusion of the smaller one. -/
theorem openSubSchemeHomOfLE_comp_left (A : BigFppfOver B S hS)
    {O O' : ((BigFppfOver.toScheme B S hS).obj A).Opens} (h : O ≤ O') :
    openSubSchemeHomOfLE A h ≫ (openSubHom A O').left = (openSubHom A O).left := by
  apply B.inclusion.map_injective
  rw [B.inclusion.map_comp]
  change B.inclusion.map (openSubSchemeHomOfLE A h) ≫
      (BigFppfOver.toScheme B S hS).map (openSubHom A O') =
      (BigFppfOver.toScheme B S hS).map (openSubHom A O)
  rw [toScheme_map_openSubHom, toScheme_map_openSubHom,
    inclusion_map_openSubSchemeHomOfLE]
  exact Scheme.homOfLE_ι _ h

variable {B S hS F} in
/-- An inclusion of Zariski opens of the scheme underlying an object `A` of the big fppf site
induces a morphism of the open subobjects of `A` that they define. -/
noncomputable def openSubHomOfLE (A : BigFppfOver B S hS)
    {O O' : ((BigFppfOver.toScheme B S hS).obj A).Opens} (h : O ≤ O') :
    openSub A O ⟶ openSub A O' :=
  Over.homMk (openSubSchemeHomOfLE A h) (by
    change openSubSchemeHomOfLE A h ≫ (openSubHom A O').left ≫ A.hom =
      (openSubHom A O).left ≫ A.hom
    rw [← Category.assoc, openSubSchemeHomOfLE_comp_left])

variable {B S hS F} in
/-- `AlgebraicGeometry.Space.openSubHomOfLE` is a morphism over the ambient object. -/
theorem openSubHomOfLE_comp_openSubHom (A : BigFppfOver B S hS)
    {O O' : ((BigFppfOver.toScheme B S hS).obj A).Opens} (h : O ≤ O') :
    openSubHomOfLE A h ≫ openSubHom A O' = openSubHom A O :=
  Over.OverMorphism.ext (openSubSchemeHomOfLE_comp_left A h)

variable {B S hS F} in
/-- `AlgebraicGeometry.Space.openSubHomOfLE` at a reflexive inclusion is the identity. -/
theorem openSubHomOfLE_refl (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) :
    openSubHomOfLE A (le_refl O) = 𝟙 (openSub A O) := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact Scheme.homOfLE_rfl _ O

variable {B S hS F} in
/-- `AlgebraicGeometry.Space.openSubHomOfLE` is compatible with composition of inclusions. -/
theorem openSubHomOfLE_trans (A : BigFppfOver B S hS)
    {O O' O'' : ((BigFppfOver.toScheme B S hS).obj A).Opens} (h : O ≤ O') (h' : O' ≤ O'') :
    openSubHomOfLE A (h.trans h') = openSubHomOfLE A h ≫ openSubHomOfLE A h' := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact (Scheme.homOfLE_homOfLE _ h h').symm

/-- An inclusion of Zariski opens of the scheme underlying an étale chart `U` of `F` induces a
morphism of the étale charts of `F` that they define. -/
noncomputable def openChartHomOfLE (U : SmallEtale B S hS F)
    {O O' : (chartScheme U).Opens} (h : O ≤ O') :
    openChart B S hS F U O ⟶ openChart B S hS F U O' :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (openSubHomOfLE ((SmallEtale.toOver B S hS F).obj U) h)
    (by
      change yoneda.map (openSubHomOfLE ((SmallEtale.toOver B S hS F).obj U) h) ≫
          yoneda.map (openSubHom ((SmallEtale.toOver B S hS F).obj U) O') ≫ U.1.hom =
          yoneda.map (openSubHom ((SmallEtale.toOver B S hS F).obj U) O) ≫ U.1.hom
      rw [← Category.assoc, ← yoneda.map_comp,
        openSubHomOfLE_comp_openSubHom ((SmallEtale.toOver B S hS F).obj U) h]))

/-- The Zariski opens of the scheme underlying an étale chart `U` of `F`, read as étale charts
of `F`, functorially in the open. -/
noncomputable def openChartFunctor (U : SmallEtale B S hS F) :
    (chartScheme U).Opens ⥤ SmallEtale B S hS F where
  obj O := openChart B S hS F U O
  map {O O'} i := openChartHomOfLE B S hS F U i.le
  map_id O := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    change openSubHomOfLE ((SmallEtale.toOver B S hS F).obj U) (le_refl O) = 𝟙 _
    exact openSubHomOfLE_refl _ O
  map_comp {O O' O''} i j := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    change openSubHomOfLE ((SmallEtale.toOver B S hS F).obj U) (i.le.trans j.le) =
      openSubHomOfLE ((SmallEtale.toOver B S hS F).obj U) i.le ≫
        openSubHomOfLE ((SmallEtale.toOver B S hS F).obj U) j.le
    exact openSubHomOfLE_trans _ i.le j.le

/-- The schemes underlying the charts of `AlgebraicGeometry.Space.openChartFunctor` are the
open subschemes themselves, functorially and definitionally. -/
theorem openChartFunctor_comp_toScheme (U : SmallEtale B S hS F) :
    openChartFunctor B S hS F U ⋙ SmallEtale.toOver B S hS F ⋙
        BigFppfOver.toScheme B S hS =
      (chartScheme U).restrictFunctor ⋙ Over.forget _ :=
  rfl

/-- The change-of-scalars map restricting the structure sheaf of an étale chart's scheme to
the global functions on its Zariski opens read as étale charts of `F`.

It is `AlgebraicGeometry.Scheme.restrictFunctorΓ` read through
`AlgebraicGeometry.Space.openChartFunctor_comp_toScheme`, with commutativity forgotten. -/
noncomputable def chartSchemeRestrictionRingHom (U : SmallEtale B S hS F) :
    (chartScheme U).ringCatSheaf.obj ⟶
      (openChartFunctor B S hS F U).op ⋙
        (structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat) :=
  Functor.whiskerRight (Scheme.restrictFunctorΓ (X := chartScheme U)).inv
    (forget₂ CommRingCat RingCat)

/-- The restriction of an `𝒪_F`-module to the scheme underlying an étale chart of `F`: restrict
the sections to the Zariski opens of the chart, change scalars along
`AlgebraicGeometry.Space.chartSchemeRestrictionRingHom`, and sheafify for the Zariski topology.

The sections are first raised to the universe `max u m` by
`SheafOfModules.uliftForPresentation`, so that the scheme and module universes may be
independent. -/
noncomputable def restrictToChartScheme (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, m} B S hS F hF) (U : SmallEtale B S hS F) :
    SheafOfModules.{max u m} (chartScheme U).ringCatSheaf := by
  letI : HasSheafify (Opens.grothendieckTopology (chartScheme U))
      AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite _ _
  letI : (Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective
      AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  exact (PresheafOfModules.sheafification
      (𝟙 (chartScheme U).ringCatSheaf.obj)).obj
    ((PresheafOfModules.pushforward
        (chartSchemeRestrictionRingHom B S hS F U)).obj
      (SheafOfModules.uliftForPresentation M).val)

/-- `AlgebraicGeometry.Space.restrictToChartScheme`, functorially in the module: each of its
three steps — raising the universe of the sections, changing scalars along
`AlgebraicGeometry.Space.chartSchemeRestrictionRingHom`, and Zariski sheafification — is a
functor, and this is their composite. -/
noncomputable def restrictToChartSchemeFunctor (hF : IsAlgebraicSpace B S hS F)
    (U : SmallEtale B S hS F) :
    Modules.{u, m} B S hS F hF ⥤ SheafOfModules.{max u m} (chartScheme U).ringCatSheaf := by
  letI : HasSheafify (Opens.grothendieckTopology (chartScheme U))
      AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite _ _
  letI : (Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective
      AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  exact SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, m, u} ⋙
    SheafOfModules.forget _ ⋙
    PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F U) ⋙
    PresheafOfModules.sheafification (𝟙 (chartScheme U).ringCatSheaf.obj)

/-- The functorial restriction to an étale chart's scheme agrees with
`AlgebraicGeometry.Space.restrictToChartScheme` on objects. -/
theorem restrictToChartSchemeFunctor_obj (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, m} B S hS F hF) (U : SmallEtale B S hS F) :
    (restrictToChartSchemeFunctor B S hS F hF U).obj M = restrictToChartScheme B S hS F hF M U :=
  rfl

/-- The restriction `AlgebraicGeometry.Space.restrictToChartScheme` of a module of module
universe `u` to the scheme of an étale chart, as an object of
`AlgebraicGeometry.Scheme.Modules`.

`AlgebraicGeometry.Scheme.Modules` is not reducible, so the declared type `SheafOfModules` of
`restrictToChartScheme` never unfolds to it during instance search, and the module structure of
its sections over `Γ(chartScheme U, O)` is not found there.  This `abbrev` is reducible, so the
structure is found on it. -/
noncomputable abbrev restrictToChartSchemeModules (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) (U : SmallEtale B S hS F) :
    (chartScheme U).Modules :=
  restrictToChartScheme B S hS F hF M U

end AlgebraicGeometry.Space

end
