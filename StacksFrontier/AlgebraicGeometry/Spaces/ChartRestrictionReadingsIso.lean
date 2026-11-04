module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadings
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent

/-!
# The index functor of the chart restriction, up to isomorphism and on the nose

This development restricts an `𝒪_X`-module to an étale scheme chart `U` of an algebraic space
twice over, by sheafifying its sections along two index functors from the Zariski opens of the
chart's scheme to the small étale site of `X`: `AlgebraicGeometry.Space.chartOpens`, used by
`AlgebraicGeometry.Space.restrictToChart`, and `AlgebraicGeometry.Space.openChartFunctor`, used
by `AlgebraicGeometry.Space.restrictToChartScheme`.

This file identifies the two index functors up to isomorphism, with no transport, and reads
`restrictToChart` as a direct image along its own index functor; and it identifies the two
*restrictions* on the nose, as an equality of modules on the Zariski site of the chart's scheme.

The equality of the two index functors itself is
`AlgebraicGeometry.Space.chartOpens_eq_openChartFunctor`, proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionReadingsFunctor.lean`, which also carries
it up to the isomorphism `AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme` of
the two restrictions, stated there for modules whose sections live in any universe.

## Main definitions

* `AlgebraicGeometry.Space.chartOpensIsoOpenChartFunctor`: the two index functors are isomorphic
  by an isomorphism whose every component is the identity on the underlying open subscheme.
* `AlgebraicGeometry.Space.chartRestrictionSheafHom` and
  `AlgebraicGeometry.Space.restrictToChartIsoPushforward`: `restrictToChart` as a direct image
  along `AlgebraicGeometry.Space.chartOpens`.
* `AlgebraicGeometry.Space.chartOpensOfIncl` is the inclusion of the Zariski opens of an étale
  chart into the small étale site of `X` built from an arbitrary family of inclusions of those
  opens as morphisms of `Sch_κ`, and `AlgebraicGeometry.Space.restrictAlong` is the restriction
  of a module along an arbitrary such inclusion.

## Main results

* `AlgebraicGeometry.Space.isContinuous_chartOpens`: the index functor of `restrictToChart` is
  continuous.
* `AlgebraicGeometry.Space.restrictToChart_eq_restrictToChartScheme`: **the two parallel
  restrictions of an `𝒪_X`-module to the scheme of an étale chart are equal.**

## Implementation notes

The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionReadings.lean` record what was owed for
this comparison: the two index functors send a Zariski open of the chart's scheme to the same
open subscheme, read as an étale chart of `X` through two readings of the open immersion as a
morphism of the size-bounded category of schemes — `CategoryTheory.ObjectProperty.homMk` for
`AlgebraicGeometry.Space.chartOpenOverι` and `CategoryTheory.Functor.preimage` for
`AlgebraicGeometry.Space.openSubHom` — and the identification of the two charts is therefore
type-correct only after a transport.

The transport is avoided in the isomorphism.  The two charts have the *same* underlying object
of the size-bounded category of schemes, so the identity of that object is a morphism between
them in both directions as soon as the two structure morphisms to `X` are known to agree, which
is `AlgebraicGeometry.Space.homMk_opens_ι_eq_preimage`.  That gives an isomorphism of index
functors rather than an equality, with no `CategoryTheory.eqToHom` anywhere; its naturality and
the two triangle identities are all instances of
`AlgebraicGeometry.Space.hom_ext_of_toScheme_map_eq`, a morphism of étale charts being
determined by its underlying morphism of schemes.

With the isomorphism in hand the index functor is continuous, and `restrictToChart` is presented
as a direct image along it exactly as
`AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward` presents `restrictToChartScheme`:
the two are built from the same change-of-scalars map, by
`AlgebraicGeometry.Space.chartRestrictionRingHom_eq`.

The *equality* of the two restrictions is reached a second way, through
`AlgebraicGeometry.Space.chartOpensOfIncl`: the same index functor built from an arbitrary
family of inclusions of the opens as morphisms of `Sch_κ`, together with the two facts about
that family which the construction consumes — compatibility with the inclusions of the opens
among themselves, and the étale-chart property of the resulting charts.  Both named index
functors are that functor on the nose, at the two families which
`AlgebraicGeometry.Space.homMk_opens_ι_eq_preimage` identifies; the two remaining arguments are
propositions, so the equality of the families is the whole content.

Abstracting the family at the level of morphisms of `Sch_κ` rather than of the big fppf category
over `S` is what makes this work: the two objects of the big fppf category differ — only
propositionally, by `AlgebraicGeometry.Space.chartOpenOver_eq_openSub` — whereas the two objects
of `Sch_κ` are one and the same, so the two families have the same type and their equality is an
equality and not a heterogeneous one.

The restrictions are compared the same way, through `AlgebraicGeometry.Space.restrictAlong`,
which is the common construction with its index functor and its change-of-scalars map as
arguments.  The two changes of scalars are already known to be equal, by
`AlgebraicGeometry.Space.chartRestrictionRingHom_eq`; since their type mentions the index functor
the equality has to enter as a heterogeneous one, after which substituting the index functor
reduces it to an equality.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u m

namespace AlgebraicGeometry.Space

section IndexFunctorIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### The two index functors of the chart restriction -/

/-- The identity of an open subscheme of the scheme of an étale chart `U`, read as a morphism
from the object of the big fppf category over `S` which
`AlgebraicGeometry.Space.restrictToChart` attaches to the open to the one which
`AlgebraicGeometry.Space.restrictToChartScheme` attaches to it.

The two have the same underlying object of the size-bounded category of schemes; what has to be
checked is that their structure morphisms agree, and that is
`AlgebraicGeometry.Space.homMk_opens_ι_eq_preimage`. -/
noncomputable def chartOpenOverHomOpenSub (U : SmallEtale B S hS X)
    (O : (etaleChartScheme B S hS U).Opens) :
    chartOpenOver B S hS U O ⟶ openSub ((SmallEtale.toOver B S hS X).obj U) O :=
  Over.homMk (𝟙 _)
    ((Category.id_comp _).trans
      (congrArg (fun k ↦ k ≫ ((SmallEtale.toOver B S hS X).obj U).hom)
        (homMk_opens_ι_eq_preimage B S hS ((SmallEtale.toOver B S hS X).obj U) O).symm))

/-- `AlgebraicGeometry.Space.chartOpenOverHomOpenSub`, in the other direction. -/
noncomputable def openSubHomChartOpenOver (U : SmallEtale B S hS X)
    (O : (etaleChartScheme B S hS U).Opens) :
    openSub ((SmallEtale.toOver B S hS X).obj U) O ⟶ chartOpenOver B S hS U O :=
  Over.homMk (𝟙 _)
    ((Category.id_comp _).trans
      (congrArg (fun k ↦ k ≫ ((SmallEtale.toOver B S hS X).obj U).hom)
        (homMk_opens_ι_eq_preimage B S hS ((SmallEtale.toOver B S hS X).obj U) O)))

/-- `AlgebraicGeometry.Space.chartOpenOverHomOpenSub` is a morphism over the étale chart. -/
theorem chartOpenOverHomOpenSub_comp_openSubHom (U : SmallEtale B S hS X)
    (O : (etaleChartScheme B S hS U).Opens) :
    chartOpenOverHomOpenSub B S hS X U O ≫ openSubHom ((SmallEtale.toOver B S hS X).obj U) O =
      chartOpenOverι B S hS U O :=
  Over.OverMorphism.ext
    ((Category.id_comp _).trans
      (homMk_opens_ι_eq_preimage B S hS ((SmallEtale.toOver B S hS X).obj U) O).symm)

/-- `AlgebraicGeometry.Space.openSubHomChartOpenOver` is a morphism over the étale chart. -/
theorem openSubHomChartOpenOver_comp_chartOpenOverι (U : SmallEtale B S hS X)
    (O : (etaleChartScheme B S hS U).Opens) :
    openSubHomChartOpenOver B S hS X U O ≫ chartOpenOverι B S hS U O =
      openSubHom ((SmallEtale.toOver B S hS X).obj U) O :=
  Over.OverMorphism.ext
    ((Category.id_comp _).trans
      (homMk_opens_ι_eq_preimage B S hS ((SmallEtale.toOver B S hS X).obj U) O))

/-- The identity of an open subscheme of the scheme of an étale chart `U`, read as a morphism
from its reading as an étale chart through `AlgebraicGeometry.Space.chartOpenOverι` to its
reading through `AlgebraicGeometry.Space.openSubHom`. -/
noncomputable def chartOpensHomOpenChart (U : SmallEtale B S hS X)
    (O : (etaleChartScheme B S hS U).Opens) :
    (chartOpens B S hS U).obj O ⟶ openChart B S hS X U O :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (chartOpenOverHomOpenSub B S hS X U O)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k ↦ k ≫ U.obj.hom)
        ((yoneda.map_comp _ _).symm.trans
          (congrArg yoneda.map
            (chartOpenOverHomOpenSub_comp_openSubHom B S hS X U O))))))

/-- The identity of an open subscheme of the scheme of an étale chart, read in the other
direction; see `AlgebraicGeometry.Space.chartOpensHomOpenChart`. -/
noncomputable def openChartHomChartOpens (U : SmallEtale B S hS X)
    (O : (etaleChartScheme B S hS U).Opens) :
    openChart B S hS X U O ⟶ (chartOpens B S hS U).obj O :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (openSubHomChartOpenOver B S hS X U O)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k ↦ k ≫ U.obj.hom)
        ((yoneda.map_comp _ _).symm.trans
          (congrArg yoneda.map
            (openSubHomChartOpenOver_comp_chartOpenOverι B S hS X U O))))))

/-- **The two index functors of the chart restriction are isomorphic.**  Every component is the
identity on the underlying open subscheme of the chart's scheme.

The two triangle identities and naturality are all equalities of morphisms of étale charts, so
each is checked on the underlying morphism of the size-bounded category of schemes, where every
component is an identity and the two maps induced by an inclusion of opens are one and the same
`AlgebraicGeometry.Scheme.homOfLE`. -/
noncomputable def chartOpensIsoOpenChartFunctor (U : SmallEtale B S hS X) :
    chartOpens B S hS U ≅ openChartFunctor B S hS X U :=
  NatIso.ofComponents
    (fun O ↦
      { hom := chartOpensHomOpenChart B S hS X U O
        inv := openChartHomChartOpens B S hS X U O
        hom_inv_id := ObjectProperty.hom_ext _
          (CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (Category.id_comp _)))
        inv_hom_id := ObjectProperty.hom_ext _
          (CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (Category.id_comp _))) })
    (fun _ ↦ ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
      (Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm))))

/-- **The index functor of `AlgebraicGeometry.Space.restrictToChart` is continuous**, from the
small Zariski site of the chart's scheme to the small étale site of the algebraic space: it is
isomorphic to the index functor of `AlgebraicGeometry.Space.restrictToChartScheme`, which is
continuous. -/
theorem isContinuous_chartOpens (hX : IsAlgebraicSpace B S hS X)
    (U : SmallEtale B S hS X) :
    (chartOpens B S hS U).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme U))
      (SmallEtale.topology B S hS X) :=
  let : (openChartFunctor B S hS X U).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme U)) (SmallEtale.topology B S hS X) :=
    isContinuous_openChartFunctor B S hS ⟨X, hX⟩ U
  Functor.isContinuous_of_iso (chartOpensIsoOpenChartFunctor B S hS X U).symm _ _

/-! ### The chart restriction as a direct image -/

section Pushforward

variable {X} (hX : IsAlgebraicSpace B S hS X) (U : SmallEtale B S hS X)

/-- The change-of-scalars map of `AlgebraicGeometry.Space.restrictToChart`, spelled with the
structure presheaf of the small étale site rather than with the ring sheaf of its ringed-site
reading.  This is `AlgebraicGeometry.Space.chartRestrictionRingHom`; only the spelling of the
target differs, and the two spellings are definitionally equal. -/
noncomputable def chartOpensRestrictionRingHom :
    (chartScheme U).ringCatSheaf.obj ⟶
      (chartOpens B S hS U).op ⋙
        (structurePresheaf B S hS X ⋙ forget₂ CommRingCat RingCat) :=
  chartRestrictionRingHom B S hS hX U

section Continuous

variable [(chartOpens B S hS U).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme U)) (SmallEtale.topology B S hS X)]

/-- The morphism of sheaves of rings along which `AlgebraicGeometry.Space.restrictToChart`
extends scalars, read over its continuous index functor.  This is
`AlgebraicGeometry.Space.chartRestrictionRingHom`. -/
noncomputable def chartRestrictionSheafHom :
    (chartScheme U).ringCatSheaf ⟶
      ((chartOpens B S hS U).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥(chartScheme U))
        (SmallEtale.topology B S hS X)).obj (smallEtaleRingSheaf B S hS X hX) :=
  ⟨chartOpensRestrictionRingHom B S hS hX U⟩

/-- **`AlgebraicGeometry.Space.restrictToChart` is a direct image.**  This is
`AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward` for the other index functor, with
the same proof: the universe lift of the sections is undone by
`SheafOfModules.uliftForPresentationSelfIso` and the restricted presheaf is already a sheaf, so
the sheafification is the counit of
`CategoryTheory.PresheafOfModules.sheafificationAdjunction`. -/
noncomputable def restrictToChartIsoPushforward (G : Modules.{u, u} B S hS X hX) :
    restrictToChart B S hS hX G U ≅
      (SheafOfModules.pushforward.{u} (chartRestrictionSheafHom B S hS hX U)).obj G :=
  (PresheafOfModules.sheafification (𝟙 (chartScheme U).ringCatSheaf.obj)).mapIso
      ((PresheafOfModules.pushforward (chartOpensRestrictionRingHom B S hS hX U)).mapIso
        ((SheafOfModules.forget _).mapIso (SheafOfModules.uliftForPresentationSelfIso G))) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (chartScheme U).ringCatSheaf.obj)).counit).app
      ((SheafOfModules.pushforward.{u} (chartRestrictionSheafHom B S hS hX U)).obj G)

end Continuous

end Pushforward

end IndexFunctorIso

section RestrictionEquality

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-! ### The Zariski opens of a chart, read through an arbitrary family of inclusions -/

/-- The object of `Sch_κ` underlying a Zariski open of an étale chart of `X`: the open
subscheme, whose size the size bound of the chart's scheme bounds in turn. -/
abbrev chartOpenSchemes (U : SmallEtale B S hS X) (O : (etaleChartScheme B S hS U).Opens) :
    B.Schemes :=
  ⟨(O : Scheme), lt_of_le_of_lt (Scheme.size_coe_opens_le _ O) U.obj.left.left.property⟩

/-- A Zariski open of an étale chart `U` of `X`, read as an object of the big fppf category over
`S` through a family `ι` of inclusions of the opens as morphisms of `Sch_κ`: it is taken over
`S` through the inclusion followed by the structure morphism of the chart. -/
abbrev inclOpenOver (U : SmallEtale B S hS X)
    (ι : ∀ O : (etaleChartScheme B S hS U).Opens,
      chartOpenSchemes B S hS U O ⟶ U.obj.left.left)
    (O : (etaleChartScheme B S hS U).Opens) : BigFppfOver B S hS :=
  Over.mk (ι O ≫ U.obj.left.hom)

/-- The inclusion of `AlgebraicGeometry.Space.inclOpenOver` into the object of the chart, as a
morphism over the base. -/
noncomputable def inclOpenOverι (U : SmallEtale B S hS X)
    (ι : ∀ O : (etaleChartScheme B S hS U).Opens,
      chartOpenSchemes B S hS U O ⟶ U.obj.left.left)
    (O : (etaleChartScheme B S hS U).Opens) :
    inclOpenOver B S hS U ι O ⟶ U.obj.left :=
  Over.homMk (ι O) rfl

/-- The morphism over the base induced by an inclusion of Zariski opens of a chart, read through
a family `ι` of inclusions compatible with the inclusions of the opens among themselves. -/
noncomputable def inclOpenOverMap (U : SmallEtale B S hS X)
    (ι : ∀ O : (etaleChartScheme B S hS U).Opens,
      chartOpenSchemes B S hS U O ⟶ U.obj.left.left)
    (hι : ∀ {O O' : (etaleChartScheme B S hS U).Opens} (h : O ≤ O'),
      ObjectProperty.homMk ((etaleChartScheme B S hS U).homOfLE h) ≫ ι O' = ι O)
    {O O' : (etaleChartScheme B S hS U).Opens} (h : O ≤ O') :
    inclOpenOver B S hS U ι O ⟶ inclOpenOver B S hS U ι O' :=
  Over.homMk (ObjectProperty.homMk ((etaleChartScheme B S hS U).homOfLE h))
    (show ObjectProperty.homMk ((etaleChartScheme B S hS U).homOfLE h) ≫
        ι O' ≫ U.obj.left.hom = ι O ≫ U.obj.left.hom by
      rw [← Category.assoc, hι h])

/-- `AlgebraicGeometry.Space.inclOpenOverMap` is compatible with the inclusions of the opens
into the chart. -/
theorem inclOpenOverMap_comp_ι (U : SmallEtale B S hS X)
    (ι : ∀ O : (etaleChartScheme B S hS U).Opens,
      chartOpenSchemes B S hS U O ⟶ U.obj.left.left)
    (hι : ∀ {O O' : (etaleChartScheme B S hS U).Opens} (h : O ≤ O'),
      ObjectProperty.homMk ((etaleChartScheme B S hS U).homOfLE h) ≫ ι O' = ι O)
    {O O' : (etaleChartScheme B S hS U).Opens} (h : O ≤ O') :
    inclOpenOverMap B S hS U ι hι h ≫ inclOpenOverι B S hS U ι O' =
      inclOpenOverι B S hS U ι O :=
  Over.OverMorphism.ext (hι h)

/-- The inclusion of the Zariski opens of an étale chart `U` of `X` into the small étale site of
`X`, built from an arbitrary family `ι` of inclusions of those opens as morphisms of `Sch_κ`
which is compatible with the inclusions of the opens among themselves and lands in étale
charts.

`AlgebraicGeometry.Space.chartOpens` and `AlgebraicGeometry.Space.openChartFunctor` are this
functor at two such families. -/
noncomputable def chartOpensOfIncl (U : SmallEtale B S hS X)
    (ι : ∀ O : (etaleChartScheme B S hS U).Opens,
      chartOpenSchemes B S hS U O ⟶ U.obj.left.left)
    (hι : ∀ {O O' : (etaleChartScheme B S hS U).Opens} (h : O ≤ O'),
      ObjectProperty.homMk ((etaleChartScheme B S hS U).homOfLE h) ≫ ι O' = ι O)
    (hprop : ∀ O : (etaleChartScheme B S hS U).Opens,
      IsEtaleChart B S hS X
        (CostructuredArrow.mk (yoneda.map (inclOpenOverι B S hS U ι O) ≫ U.obj.hom))) :
    (etaleChartScheme B S hS U).Opens ⥤ SmallEtale B S hS X where
  obj O := ⟨CostructuredArrow.mk (yoneda.map (inclOpenOverι B S hS U ι O) ≫ U.obj.hom), hprop O⟩
  map {O O'} i := ObjectProperty.homMk (CostructuredArrow.homMk
    (inclOpenOverMap B S hS U ι hι i.le) (by
      change yoneda.map (inclOpenOverMap B S hS U ι hι i.le) ≫
          yoneda.map (inclOpenOverι B S hS U ι O') ≫ U.obj.hom =
        yoneda.map (inclOpenOverι B S hS U ι O) ≫ U.obj.hom
      rw [← Category.assoc, ← yoneda.map_comp, inclOpenOverMap_comp_ι]))
  map_id _ := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    (Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.homOfLE_rfl _ _))))
  map_comp i j := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext
    (ObjectProperty.hom_ext _ (Scheme.homOfLE_homOfLE _ i.le j.le).symm)))

/-- `AlgebraicGeometry.Space.chartOpensOfIncl` depends only on its family of inclusions: its two
remaining arguments are propositions. -/
theorem chartOpensOfIncl_congr (U : SmallEtale B S hS X)
    {ι ι' : ∀ O : (etaleChartScheme B S hS U).Opens,
      chartOpenSchemes B S hS U O ⟶ U.obj.left.left}
    {hι hprop} {hι' hprop'} (h : ι = ι') :
    chartOpensOfIncl B S hS U ι hι hprop = chartOpensOfIncl B S hS U ι' hι' hprop' := by
  subst h
  rfl

/-- `AlgebraicGeometry.Space.chartOpens` is `AlgebraicGeometry.Space.chartOpensOfIncl` at the
family of open immersions read with `CategoryTheory.ObjectProperty.homMk`. -/
theorem chartOpens_eq_chartOpensOfIncl (U : SmallEtale B S hS X) :
    chartOpens B S hS U =
      chartOpensOfIncl B S hS U (fun O ↦ ObjectProperty.homMk O.ι)
        (fun h ↦ by
          apply ObjectProperty.hom_ext
          exact Scheme.homOfLE_ι _ h)
        (chartOpen_isEtaleChart B S hS U) :=
  rfl

/-- `AlgebraicGeometry.Space.openChartFunctor` is
`AlgebraicGeometry.Space.chartOpensOfIncl` at the family of open immersions read with the
fullness inverse of the inclusion of `Sch_κ` into all schemes. -/
theorem openChartFunctor_eq_chartOpensOfIncl (U : SmallEtale B S hS X) :
    openChartFunctor B S hS X U =
      chartOpensOfIncl B S hS U
        (fun O ↦ B.inclusion.preimage
          (show B.inclusion.obj (chartOpenSchemes B S hS U O) ⟶
            B.inclusion.obj U.obj.left.left from O.ι))
        (fun h ↦ by
          apply B.inclusion.map_injective
          rw [B.inclusion.map_comp, Functor.map_preimage, Functor.map_preimage]
          exact Scheme.homOfLE_ι _ h)
        (fun O ↦ (openChart B S hS X U O).property) :=
  rfl

/-! ### The two restrictions -/

/-- The sections of an `𝒪_X`-module on the Zariski opens of an étale chart `U`, read through an
arbitrary inclusion of those opens into the small étale site of `X` with scalars extended along
an arbitrary change of scalars over it, and with the universe of the sections raised so that
they can be sheafified on `U`.

This is `AlgebraicGeometry.Space.chartRestrictionPresheaf` with its index functor and its change
of scalars as arguments. -/
noncomputable def restrictAlongPresheaf (U : SmallEtale B S hS X)
    (Φ : (etaleChartScheme B S hS U).Opens ⥤ SmallEtale B S hS X)
    (φ : (etaleChartScheme B S hS U).ringCatSheaf.obj ⟶
      Φ.op ⋙ ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).obj)
    (G : Modules.{u, m} B S hS X hX) :
    PresheafOfModules.{max u m} (etaleChartScheme B S hS U).ringCatSheaf.obj :=
  let catSpaceModules : Category (PresheafOfModules.{max u m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).obj) :=
    inferInstance
  let catChartModules : Category (PresheafOfModules.{max u m}
      (etaleChartScheme B S hS U).ringCatSheaf.obj) := inferInstance
  @Functor.obj _ catSpaceModules _ catChartModules
    (PresheafOfModules.pushforward.{max u m} φ)
    (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u} G).val

/-- The restriction of an `𝒪_X`-module to the Zariski site of the scheme of an étale chart `U`,
built from an arbitrary inclusion of the Zariski opens of `U` into the small étale site of `X`
and an arbitrary change of scalars along it: restrict the sections, extend scalars, sheafify.

`AlgebraicGeometry.Space.restrictToChart` and
`AlgebraicGeometry.Space.restrictToChartScheme` are this construction at the two inclusions of
`AlgebraicGeometry.Space.chartOpens_eq_openChartFunctor`. -/
noncomputable def restrictAlong (U : SmallEtale B S hS X)
    (Φ : (etaleChartScheme B S hS U).Opens ⥤ SmallEtale B S hS X)
    (φ : (etaleChartScheme B S hS U).ringCatSheaf.obj ⟶
      Φ.op ⋙ ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).obj)
    (G : Modules.{u, m} B S hS X hX) :
    SheafOfModules.{max u m} (etaleChartScheme B S hS U).ringCatSheaf := by
  let : HasSheafify (Opens.grothendieckTopology (etaleChartScheme B S hS U))
      AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u m} _ _
  let : (Opens.grothendieckTopology (etaleChartScheme B S hS U)).WEqualsLocallyBijective
      AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u m} _
  exact (PresheafOfModules.sheafification.{max u m}
    (𝟙 (etaleChartScheme B S hS U).ringCatSheaf.obj)).obj
    (restrictAlongPresheaf B S hS hX U Φ φ G)

/-- `AlgebraicGeometry.Space.restrictAlong` at equal index functors and equal changes of scalars
gives equal restrictions. -/
theorem restrictAlong_congr (U : SmallEtale B S hS X)
    {Φ Φ' : (etaleChartScheme B S hS U).Opens ⥤ SmallEtale B S hS X} (h : Φ = Φ')
    {φ : (etaleChartScheme B S hS U).ringCatSheaf.obj ⟶
      Φ.op ⋙ ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).obj}
    {φ' : (etaleChartScheme B S hS U).ringCatSheaf.obj ⟶
      Φ'.op ⋙ ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).obj}
    (hφ : HEq φ φ') (G : Modules.{u, m} B S hS X hX) :
    restrictAlong B S hS hX U Φ φ G = restrictAlong B S hS hX U Φ' φ' G := by
  subst h
  obtain rfl := eq_of_heq hφ
  rfl

/-- `AlgebraicGeometry.Space.restrictToChart` is
`AlgebraicGeometry.Space.restrictAlong` at `AlgebraicGeometry.Space.chartOpens`. -/
theorem restrictToChart_eq_restrictAlong (G : Modules.{u, m} B S hS X hX)
    (U : SmallEtale B S hS X) :
    restrictToChart B S hS hX G U =
      restrictAlong B S hS hX U (chartOpens B S hS U)
        (chartRestrictionRingHom B S hS hX U) G :=
  rfl

/-- `AlgebraicGeometry.Space.restrictToChartScheme` is
`AlgebraicGeometry.Space.restrictAlong` at `AlgebraicGeometry.Space.openChartFunctor`. -/
theorem restrictToChartScheme_eq_restrictAlong (G : Modules.{u, m} B S hS X hX)
    (U : SmallEtale B S hS X) :
    restrictToChartScheme B S hS X hX G U =
      restrictAlong B S hS hX U (openChartFunctor B S hS X U)
        (chartSchemeRestrictionRingHom B S hS X U) G :=
  rfl

/-- **The two parallel restrictions of an `𝒪_X`-module to the scheme of an étale chart are
equal.**  `AlgebraicGeometry.Space.restrictToChart`, which the chartwise properties of a module
are read on, is `AlgebraicGeometry.Space.restrictToChartScheme`, which the comparisons of the
chart restriction with base change are stated for.

The two index functors agree by
`AlgebraicGeometry.Space.chartOpens_eq_openChartFunctor` and the two changes of scalars by
`AlgebraicGeometry.Space.chartRestrictionRingHom_eq`. -/
theorem restrictToChart_eq_restrictToChartScheme (G : Modules.{u, m} B S hS X hX)
    (U : SmallEtale B S hS X) :
    restrictToChart B S hS hX G U = restrictToChartScheme B S hS X hX G U :=
  (restrictToChart_eq_restrictAlong B S hS hX G U).trans
    ((restrictAlong_congr B S hS hX U (chartOpens_eq_openChartFunctor B S hS U)
        (heq_of_eq (chartRestrictionRingHom_eq B S hS hX U)) G).trans
      (restrictToChartScheme_eq_restrictAlong B S hS hX G U).symm)

end RestrictionEquality

end AlgebraicGeometry.Space

end
