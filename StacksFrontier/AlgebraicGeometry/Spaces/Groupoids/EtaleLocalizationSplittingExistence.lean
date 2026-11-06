module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationSplittingCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.EtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace

/-!
# The étale neighbourhood and the point of Stacks 03FM

Stacks 03FM says that in the strong splitting situation of Stacks 04RL there exist an algebraic
space `U'`, an étale morphism `U' ⟶ U` and a point `u' : Spec κ(u) ⟶ U'` lying over
`u : Spec κ(u) ⟶ U` such that the restriction `R' = R|_{U'}` is *strongly split* over `u'`;
Stacks 0DTC says the same, with *split* in place of *strongly split*, in the splitting situation
of Stacks 0DTB.  Both proofs open the same way: `U'` is the object space of the finite part
`(U', Z_univ, s', t', c')` of Stacks 04RU, the étale morphism is its projection `g : U' ⟶ U`, and
the point `u'` is the pair `(u, Z_u)` coming from a decomposition
`F_u = Z_u ⨿ Rest` of the fibre `F_u = R ×_{s, U} Spec κ(u)` of the source over `u` into open and
closed pieces with `Z_u` finite over `κ(u)`.

This file carries out that opening in the strong splitting situation and proves **three of the
four assertions of Stacks 03FM**: the algebraic space `U'`, the étale morphism `g : U' ⟶ U` and
the point `u'` over `u` are all produced, with nothing about them assumed.  The fourth assertion,
that `R|_{U'}` is strongly split over `u'`, is not reached *here*; it is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationArrowContainment.lean`, as
`AlgebraicGeometry.Space.exists_stronglySplit_of_strongSplittingSituation`, which is where the
`@[stacks 03FM]` attribute sits.  Stacks 0DTC is likewise not reached here; it is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationStabilizerContainment.lean`, as
`Stacks.Groupoids.GroupoidScheme.exists_split_of_splittingSituation`, which carries the
`@[stacks 0DTC]` attribute.  What this file does and does not reach is described in the
implementation notes below, and no attribute here claims either tag.

The construction of the point is the content.  Writing `T₀ = Spec κ(u)` for the residue field
point read in the site over `S`, the finite part of the source has, as its `T₀`-valued sections,
the pairs consisting of a morphism `T₀ ⟶ U` and an open subspace of `T₀ ×_U R` finite over `T₀`
containing the unit section (Stacks 04PC, 04PE and 04RR).  So a point of `U'` over `u` is exactly
an open `Z_u` of the fibre `F_u` which is finite over `κ(u)` and contains `e(u)`, and the étale
localization of Stacks 04RL supplies one:
`AlgebraicGeometry.Space.StrongSplittingSituation.exists_fiberOpens_stabilizer` produces the open
and closed piece of `F_u` supported on the arrows whose source and target are both `u`.  Three
comparisons turn that scheme-level open into a section of the finite part: the fibre formed in the
site has the scheme-theoretic fibre `F_u` as its underlying scheme, an open subscheme of a scheme
of the site is again a scheme of the site, and the range of the resulting monomorphism of
presheaves is an open subspace of the ambient fibre product finite over `T₀`.

## Main results

* `AlgebraicGeometry.Space.realizationFinitePart`: **Stacks 04RU, clauses (1) and (2)** for the
  realization of a groupoid scheme whose source and target are separated and locally of finite
  type as morphisms of schemes.  Its `objects` is `U'`, its `objectProjection` the étale
  `g : U' ⟶ U`, and `AlgebraicGeometry.Space.FinitePartUniversalOpen.groupoid` and
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.hom` upgrade it to the groupoid
  `(U', Z_univ, s', t', c')` with its canonical morphism to `(U, R, s, t, c)`.
* `AlgebraicGeometry.Space.fibreFiniteOpenSubspace`: the pair `(u, Z_u)` of Stacks 04PC attached
  to an open of `F_u` finite over `κ(u)`.
* `AlgebraicGeometry.Space.containsSection_fibreFiniteOpenSubspace`: that pair contains the unit,
  which is the condition of Stacks 04RQ placing it in `(R_s/U, e)_fin`.
* `AlgebraicGeometry.Space.etaleLocalFibrePoint` and
  `AlgebraicGeometry.Space.lies_over_fibrePoint`: **the
  point `u'`** of `U'`, and the fact that it lies over `u`.
* `AlgebraicGeometry.Space.exists_etale_point_of_strongSplittingSituation`: **Stacks 03FM**, in
  the weaker form just described — the étale neighbourhood and the point, not the splitting.

## Implementation notes

### Carried hypotheses

Beyond the standing hypotheses of Situation 04RL, which are the fields of
`AlgebraicGeometry.Space.StrongSplittingSituation` and are all consumed, the statements carry
only hypotheses that the big fppf site is large enough to see the schemes involved: `hS`, `hU`,
`hR`, `hP` that the site contains the base scheme, the object scheme, the arrow scheme and the
scheme of composable pairs — the same four that
`Stacks.Groupoids.GroupoidScheme.realization` needs in order to exist at all — and `hK` that it
contains `Spec κ(u)`.  Nothing about `U'`, about the étale morphism or about the point is
assumed: `U'` is `AlgebraicGeometry.Space.realizationFinitePart`, which is built from the
separatedness and local finite type hypotheses of the situation through
`AlgebraicGeometry.Space.finitePartUniversalOpen`, and the point is built from the fibre
decomposition.  No hypothesis is placed on the fibre of the source beyond Situation 04RL: the
finiteness of the set of arrows from `u` to itself and the quasi-finiteness of `s` along it enter
exactly once, through `exists_fiberOpens_stabilizer`.

The unit of a finite part is *not* assumed to be the Yoneda image of the identity `e : U ⟶ R` of
the groupoid scheme.  It is whatever morphism the structure
`AlgebraicGeometry.Space.FinitePartUniversalOpen` carries, namely the pointwise identity of the
realization, and only two facts about it are used: that it is a section of the source
(`unit_source`, a field) and a section of the target
(`AlgebraicGeometry.Space.FinitePartUniversalOpen.unit_comp_target`).  That is enough here,
because the open `Z_u` of Situation 04RL is characterized by its arrows having target `u`.

### What is not reached here, and where it is reached

*The splitting condition of Stacks 03FM.*  Stacks derives it by exhibiting `Z_univ` as an open
subspace of the arrow space of `R|_{U'}`: since `Z_univ ⊂ R ×_{s, U, g} U'` is open and
`R' → R ×_{s, U, g} U'` is étale, being a base change of `g`, the morphism `Z_univ → R'` is an
open immersion, so that `Z_univ` becomes the `arrows` field of an
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid` of `R|_{U'}`, which is what
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.StrongSplitting` asks for; the remaining step is
that every arrow of `R'` with both endpoints `u'` lifts to `Z_univ`, via the triple
`(s ∘ z, Z_u ×_{Spec κ(u)} Spec k, z)`.  Neither step is carried out in this file; both are
carried out in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationStrongSplitting.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationArrowContainment.lean`, which
assemble Stacks 03FM.  The conditional derivation of the splitting from an open finite
subgroupoid cut out by an open of `U` is in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationSplittingCriterion.lean`, and
this file does not feed it either: its hypothesis bundles `U'` and the subgroupoid together, so
the `U'` produced here is not the `U'` that statement assumes.

*Stacks 0DTC.*  Not reached here in any form, and no attribute of this file mentions it.  The
obstruction for this file is specific: the point produced here needs the chosen open `Z_u` to
contain the unit arrow at `u`, and in Situation 0DTB the open supplied by
`AlgebraicGeometry.Space.SplittingSituation.exists_fiberOpens_stabilizer` is supported on the
fibre of the *stabilizer* over `u`.  Seeing that the unit arrow lies there means identifying the
unit of the finite part — the pointwise identity of the realization — with the Yoneda image of
the identity `e : U ⟶ R` of the groupoid scheme, since a point of the arrow scheme with both
endpoints `u` need not lie on the stabilizer (the remark on
`AlgebraicGeometry.Space.StrongSplittingSituation.toSplittingSituation`).  That identification is
not proved here — and, as
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationStabilizerMembership.lean`
shows, it is not what the tag needs: the unit is a *section*, so
`AlgebraicGeometry.exists_stabilizer_lift` factors it through the stabilizer group scheme
directly.  Stacks 0DTC itself is
`Stacks.Groupoids.GroupoidScheme.exists_split_of_splittingSituation` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationStabilizerContainment.lean`.

*The unit of the finite part and the identity of the groupoid scheme.*  The unit is the
pointwise identity of the realization, and that it is the Yoneda image of the identity
`e : U ⟶ R` of the groupoid scheme is
`Stacks.Groupoids.GroupoidScheme.unit_hom_eq_yoneda_map_identity` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationQuasiSplittingPoint.lean`.
Nothing in this file uses it: only `unit_source` and
`AlgebraicGeometry.Space.FinitePartUniversalOpen.unit_comp_target` are needed here.

*Finiteness of `s'` and `t'`.*  Not needed: `AlgebraicGeometry.Space` `.FinitePartUniversalOpen`
`.source_finite` and the target side of the assembled groupoid are about `Z_univ` over `U'`, and
no statement of this file mentions them.

### Restated private declarations

The following is `private` in the module which proves it, so it is restated here, with its
statement unchanged and its proof transcribed; only the name differs, by a prime, to keep the
two copies distinguishable.  It comes from
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/EtaleCover.lean`:
`isFinite_of_presheaf_isFinite`.  Finiteness being Zariski local on the base and invariant
under isomorphism are taken from `Stacks.Morphisms` instead.  Two further private declarations
of that file are restated as definitions rather than as the existence statements they are
there, so that the data they produce is available on the nose:
`AlgebraicGeometry.Space.finiteOpenSubspaceOfRange'` for
`exists_finiteOpenSubspace_of_represented_open`, and
`AlgebraicGeometry.Space.etaleLocalSiteOpenObject`
together with `AlgebraicGeometry.Space.siteOpenMap` for `exists_site_open_immersion`.  They are
public here because the module system does not let a public declaration mention a private one.

### Why the Stacks 03FM attribute is withheld

Stacks 03FM is a single existential assertion whose substance is that the restriction `R|_{U'}`
is *strongly split* over `u'`. It is not a tag with separable numbered conditions, so there is no
clause of it that the statement below proves: what is proved is the étale localization -- the
existence of `U'`, of the étale `g : U' ⟶ U` and of the point `u'` -- which is an *input* to 03FM
rather than one of its assertions.

This repository distinguishes the two cases, and the distinction is what decides this file. A
qualified attribute is used where a declaration proves one of a tag's separable assertions, as in
`@[stacks 0FSC "condition (1) only — flatness of the underlying right graded module"]` or
`@[stacks 0BGY "the base-change functor is faithful"]`. The attribute is *withheld* where what is
proved is an input or a strictly weaker statement: see
`StacksFrontier/AlgebraicGeometry/ProjTwists/Basic.lean`, whose implementation notes say that tagging
such inputs "would report the tag as formalized when its assertions are not", and
`StacksFrontier/AlgebraicGeometry/SectionExtensionAffineCover/Basic.lean`, which withholds
`@[stacks 01PW]` because one half of that tag is unproved. This file is the second case.

What is missing from *this file* is the presentation of `Z_univ` as the arrow space of an open
finite subgroupoid of `R|_{U'}`, and the containment
`{r' : s'(r') = u', t'(r') = u'} ⊆ |Z_univ|`.  Both are supplied elsewhere in the library —
the first in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationStrongSplitting.lean`, the
second in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationArrowContainment.lean` — and it
is the latter file, which has them both, that carries `@[stacks 03FM]`.

## References

* [Stacks Project, Tag 03FM](https://stacks.math.columbia.edu/tag/03FM)
* [Stacks Project, Tag 0DTC](https://stacks.math.columbia.edu/tag/0DTC)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RL](https://stacks.math.columbia.edu/tag/04RL)
* [Stacks Project, Tag 04RQ](https://stacks.math.columbia.edu/tag/04RQ)
* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 0DTB](https://stacks.math.columbia.edu/tag/0DTB)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
  (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
  (hR : C.Contains G.arrows.left) (hP : C.Contains (pullback G.source G.target).left)

/-- The source morphism of the realization of a groupoid scheme is separated as a morphism of
algebraic spaces as soon as the source of the groupoid scheme is separated as a morphism of
schemes. -/
theorem isSeparated_realization_source [AlgebraicGeometry.IsSeparated G.source.left] :
    IsSeparated C S hS (G.realization C hS hU hR hP).source.hom :=
  (isSeparated_yoneda_map_iff C S hS (schemeSiteMap C hS hR hU G.source)).2
    (show AlgebraicGeometry.IsSeparated G.source.left from inferInstance)

/-- The target morphism of the realization of a groupoid scheme is separated as a morphism of
algebraic spaces as soon as the target of the groupoid scheme is separated as a morphism of
schemes. -/
theorem isSeparated_realization_target [AlgebraicGeometry.IsSeparated G.target.left] :
    IsSeparated C S hS (G.realization C hS hU hR hP).target.hom :=
  (isSeparated_yoneda_map_iff C S hS (schemeSiteMap C hS hR hU G.target)).2
    (show AlgebraicGeometry.IsSeparated G.target.left from inferInstance)

/-- The source morphism of the realization of a groupoid scheme is locally of finite type as a
morphism of algebraic spaces as soon as the source of the groupoid scheme is locally of finite
type as a morphism of schemes. -/
theorem isLocallyOfFiniteType_realization_source
    [AlgebraicGeometry.LocallyOfFiniteType G.source.left] :
    IsLocallyOfFiniteType C S hS (G.realization C hS hU hR hP).source.hom :=
  (holdsOnEveryEtaleChart_yoneda_map_iff C S hS
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    (schemeSiteMap C hS hR hU G.source)).2
    (show LocallyOfFiniteType G.source.left from inferInstance)

/-- The target morphism of the realization of a groupoid scheme is locally of finite type as a
morphism of algebraic spaces as soon as the target of the groupoid scheme is locally of finite
type as a morphism of schemes. -/
theorem isLocallyOfFiniteType_realization_target
    [AlgebraicGeometry.LocallyOfFiniteType G.target.left] :
    IsLocallyOfFiniteType C S hS (G.realization C hS hU hR hP).target.hom :=
  (holdsOnEveryEtaleChart_yoneda_map_iff C S hS
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    (schemeSiteMap C hS hR hU G.target)).2
    (show LocallyOfFiniteType G.target.left from inferInstance)

/-- **Stacks 04RU, clauses (1) and (2)** for the realization of a groupoid scheme whose source
and target are separated and locally of finite type as morphisms of schemes: the object space
`U' = (R_s/U, e)_fin` with its étale projection `g : U' ⟶ U`, and the universal open and closed
subspace `Z_univ ⊂ R ×_{s, U, g} U'` finite over `U'` which contains the base change of the
unit. -/
def realizationFinitePart [AlgebraicGeometry.IsSeparated G.source.left]
    [AlgebraicGeometry.IsSeparated G.target.left]
    [AlgebraicGeometry.LocallyOfFiniteType G.source.left]
    [AlgebraicGeometry.LocallyOfFiniteType G.target.left] :
    FinitePartUniversalOpen (G.realization C hS hU hR hP) :=
  finitePartUniversalOpen _ (isSeparated_realization_source G C hS hU hR hP)
    (isSeparated_realization_target G C hS hU hR hP)
    (isLocallyOfFiniteType_realization_source G C hS hU hR hP)
    (isLocallyOfFiniteType_realization_target G C hS hU hR hP)

/-! ### Restated private helpers -/

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_EtaleLocalizationSplittingExistence
    (B : BigFppfSite.{u}) (T : Scheme.{u}) (hT : B.Contains T) :
    HasPullbacks ((BigFppfOver B T hT)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_EtaleLocalizationSplittingExistence
    {B : BigFppfSite.{u}} {T : Scheme.{u}} {hT : B.Contains T}
    {X Y Z : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

attribute [local instance] AlgebraicGeometry.schemeSizeBelow_isClosedUnderIsomorphisms
  AlgebraicGeometry.schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan
  AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes
  AlgebraicGeometry.Space.preservesLimitsOfShape_walkingCospan_toScheme
  Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
  Stacks.Morphisms.isFinite_respectsIso

/-- A relatively representable morphism of presheaves whose base changes to schemes are finite
is a finite morphism of algebraic spaces.  Restated from the private declaration of the same
statement in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/EtaleCover.lean`. -/
theorem isFinite_of_presheaf_isFinite'
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsFinite B S hS f := by
  intro U hU ξ
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hp : AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map (hf.rep.snd ξ)) :=
    hf.property_snd ξ
  exact ⟨_, hf.rep.snd ξ, hf.rep.fst ξ,
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (hf.rep.snd ξ)), hp,
    hf.rep.isPullback ξ⟩

/-- **Stacks 04PC** from a represented open: the range of a monomorphism of presheaves out of
a representable, which is an open immersion into the ambient fibre product and whose projection
to the base is finite, is a finite open subspace of that fibre product.  This is the content of
the private existence statement `exists_finiteOpenSubspace_of_represented_open` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/EtaleCover.lean`, restated as a
definition so that the pair it produces is the range on the nose. -/
def finiteOpenSubspaceOfRange'
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (U W : BigFppfOver B S hS)
    (a : schemeSpace U ⟶ Y)
    (j : yoneda.obj W ⟶ pullback a.hom f.hom) (hmono : Mono j)
    (hj : IsOpenImmersion B S hS j)
    (hfin : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (j ≫ pullback.fst a.hom f.hom)) :
    FiniteOpenSubspace B S hS f (schemeSpace U) := by
  have := hmono
  let Z := Subfunctor.range j
  have hZ : IsAlgebraicSpace B S hS Z.toFunctor :=
    AlgebraicGeometry.Space.isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange j))
      (isAlgebraicSpace_yoneda B S hS W)
  have hopen : IsOpenImmersion B S hS Z.ι := by
    change (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS)).presheaf Z.ι
    rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) (Subfunctor.toRange j)]
    simpa [Z] using hj
  have hfinite : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsFinite.{u}) (BigFppfOver.toScheme B S hS)).presheaf
      (Z.ι ≫ pullback.fst a.hom f.hom) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := (MorphismProperty.inverseImage (@AlgebraicGeometry.IsFinite.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) (Subfunctor.toRange j)]
    simpa [← Category.assoc, Z] using hfin
  exact ⟨a, Z, ⟨hZ, hopen⟩, isFinite_of_presheaf_isFinite' B S hS _ hfinite⟩

/-- An open subscheme of the underlying scheme of an object of the site, as an object of the
site: it lies in the site because an open immersion is a monomorphism locally of finite
presentation, by Stacks 000R (3).  This is the data produced by the private existence statement
`exists_site_open_immersion` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/EtaleCover.lean`, restated as a
definition so that the comparison with the open subscheme is an equality. -/
def etaleLocalSiteOpenObject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    {W : Scheme.{u}} (j : W ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hj : AlgebraicGeometry.IsOpenImmersion j) : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (j ≫ T.hom.hom) :
    B.obj (show B.Contains W from by
      let := hj
      exact Scheme.size_lt_of_isOpenImmersion j T.left.property) ⟶ B.obj hS)

/-- The inclusion of that object of the site into the ambient one. -/
def siteOpenMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    {W : Scheme.{u}} (j : W ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hj : AlgebraicGeometry.IsOpenImmersion j) :
    etaleLocalSiteOpenObject B S hS T j hj ⟶ T :=
  Over.homMk (ObjectProperty.homMk j) (by rfl)

/-- The underlying morphism of schemes of that inclusion is the given open immersion. -/
theorem toScheme_map_siteOpenMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    {W : Scheme.{u}} (j : W ⟶ (BigFppfOver.toScheme B S hS).obj T)
    (hj : AlgebraicGeometry.IsOpenImmersion j) :
    (BigFppfOver.toScheme B S hS).map (siteOpenMap B S hS T j hj) = j := rfl

/-! ### The fibre of the source over a residue field point -/

section Fibre

variable {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
  (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
  (hR : C.Contains G.arrows.left) (u : G.objects.left)
  (hK : C.Contains (Spec (G.objects.left.residueField u)))

/-- The spectrum of the residue field at a point `u` of the object scheme, as a scheme over `S`
through the canonical morphism to the object scheme. -/
abbrev residueOver : Over S :=
  Over.mk (G.objects.left.fromSpecResidueField u ≫ G.objects.hom)

/-- The canonical morphism `Spec κ(u) ⟶ U` of schemes over `S`. -/
abbrev residuePoint : residueOver G u ⟶ G.objects :=
  Over.homMk (G.objects.left.fromSpecResidueField u)

/-- The canonical morphism `Spec κ(u) ⟶ U`, read as a morphism of the site over `S`. -/
abbrev residueSiteMap :
    schemeSiteObject C hS (X := residueOver G u) hK ⟶
      schemeSiteObject C hS (X := G.objects) hU :=
  schemeSiteMap C hS (X := residueOver G u) (Y := G.objects) hK hU (residuePoint G u)

/-- The source morphism `s : R ⟶ U` of the groupoid scheme, read as a morphism of the site
over `S`. -/
abbrev sourceSiteMap :
    schemeSiteObject C hS (X := G.arrows) hR ⟶ schemeSiteObject C hS (X := G.objects) hU :=
  schemeSiteMap C hS (X := G.arrows) (Y := G.objects) hR hU G.source

/-- The fibre `Spec κ(u) ×_{u, U, s} R` of the source over the residue field point, formed in
the site over `S`. -/
abbrev fibreSiteObject : BigFppfOver C S hS :=
  pullback (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)

/-- The underlying scheme of the fibre formed in the site is the scheme-theoretic fibre
`F_u = R ×_{s, U} Spec κ(u)` of the source over `u`: the comparison functor to schemes preserves
fibre products, and the two fibre products are formed in opposite orders. -/
def etaleLocalFibreIso :
    (BigFppfOver.toScheme C S hS).obj (fibreSiteObject G C hS hU hR u hK) ≅
      G.source.left.fiber u :=
  (PreservesPullback.iso (BigFppfOver.toScheme C S hS)
      (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)).trans
    (pullbackSymmetry _ _)

/-- Under the comparison with the scheme-theoretic fibre, the projection of the fibre formed in
the site to the arrow scheme is the inclusion of the scheme-theoretic fibre. -/
theorem fibreIso_hom_comp_fiberι :
    (etaleLocalFibreIso G C hS hU hR u hK).hom ≫ G.source.left.fiberι u =
      (BigFppfOver.toScheme C S hS).map
        (pullback.snd (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)) := by
  show (PreservesPullback.iso (BigFppfOver.toScheme C S hS)
      (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)).hom ≫
    (pullbackSymmetry _ _).hom ≫ pullback.fst _ _ = _
  rw [pullbackSymmetry_hom_comp_fst, PreservesPullback.iso_hom_snd]

/-- Under the comparison with the scheme-theoretic fibre, the projection of the fibre formed in
the site to `Spec κ(u)` is the structure morphism of the scheme-theoretic fibre. -/
theorem fibreIso_hom_comp_fiberToSpecResidueField :
    (etaleLocalFibreIso G C hS hU hR u hK).hom ≫ G.source.left.fiberToSpecResidueField u =
      (BigFppfOver.toScheme C S hS).map
        (pullback.fst (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)) := by
  show (PreservesPullback.iso (BigFppfOver.toScheme C S hS)
      (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)).hom ≫
    (pullbackSymmetry _ _).hom ≫ pullback.snd _ _ = _
  rw [pullbackSymmetry_hom_comp_snd, PreservesPullback.iso_hom_fst]

/-- The target morphism `t : R ⟶ U` of the groupoid scheme, read as a morphism of the site
over `S`. -/
abbrev targetSiteMap :
    schemeSiteObject C hS (X := G.arrows) hR ⟶ schemeSiteObject C hS (X := G.objects) hU :=
  schemeSiteMap C hS (X := G.arrows) (Y := G.objects) hR hU G.target

/-! ### The unit section of the fibre -/

variable (hP : C.Contains (pullback G.source G.target).left)
  (F : FinitePartUniversalOpen (G.realization C hS hU hR hP))

/-- The unit arrow `e(u) : Spec κ(u) ⟶ R` of the finite part at the residue field point: the
unique morphism of the site whose Yoneda image is the canonical point of `U` followed by the
unit of the finite part.

The unit is not assumed to be the Yoneda image of the identity of the groupoid scheme; it is
whatever morphism the finite part carries, and only the two identities
`AlgebraicGeometry.Space.unitArrowSite_comp_source` and
`AlgebraicGeometry.Space.unitArrowSite_comp_target` are used about it. -/
def unitArrowSite :
    schemeSiteObject C hS (X := residueOver G u) hK ⟶ schemeSiteObject C hS (X := G.arrows) hR :=
  yoneda.preimage (yoneda.map (residueSiteMap G C hS hU u hK) ≫ F.unit.hom)

/-- The defining property of the unit arrow: its Yoneda image is the canonical point of `U`
followed by the unit of the finite part. -/
theorem yoneda_map_unitArrowSite :
    yoneda.map (unitArrowSite G C hS hU hR u hK hP F) =
      yoneda.map (residueSiteMap G C hS hU u hK) ≫ F.unit.hom :=
  yoneda.map_preimage _

/-- A morphism of the site that the unit of the finite part is a section of is a section of the
unit arrow at `u` over the canonical point of `U`. -/
private theorem unitArrowSite_comp_of_unit_comp
    (q : schemeSiteObject C hS (X := G.arrows) hR ⟶ schemeSiteObject C hS (X := G.objects) hU)
    (h : F.unit.hom ≫ yoneda.map q = 𝟙 _) :
    unitArrowSite G C hS hU hR u hK hP F ≫ q = residueSiteMap G C hS hU u hK :=
  yoneda.map_injective (by
    rw [yoneda.map_comp, yoneda_map_unitArrowSite]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => yoneda.map (residueSiteMap G C hS hU u hK) ≫ k) h).trans
        (Category.comp_id _)))

/-- The unit arrow at `u` has source `u`, because the unit of a finite part is a section of the
source. -/
theorem unitArrowSite_comp_source :
    unitArrowSite G C hS hU hR u hK hP F ≫ sourceSiteMap G C hS hU hR =
      residueSiteMap G C hS hU u hK :=
  unitArrowSite_comp_of_unit_comp G C hS hU hR u hK hP F _ F.unit_source

/-- The unit arrow at `u` has target `u`, because the unit of a finite part is a section of the
target. -/
theorem unitArrowSite_comp_target :
    unitArrowSite G C hS hU hR u hK hP F ≫ targetSiteMap G C hS hU hR =
      residueSiteMap G C hS hU u hK :=
  unitArrowSite_comp_of_unit_comp G C hS hU hR u hK hP F _ F.unit_comp_target

/-- The unit section `Spec κ(u) ⟶ Spec κ(u) ×_{u, U, s} R` of the fibre: the identity in the
first component and the unit arrow in the second. -/
def unitFibreSection :
    schemeSiteObject C hS (X := residueOver G u) hK ⟶ fibreSiteObject G C hS hU hR u hK :=
  pullback.lift (𝟙 _) (unitArrowSite G C hS hU hR u hK hP F)
    (by rw [Category.id_comp, unitArrowSite_comp_source])

/-- The arrow component of the unit section is the unit arrow. -/
theorem unitFibreSection_comp_snd :
    unitFibreSection G C hS hU hR u hK hP F ≫
        pullback.snd (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR) =
      unitArrowSite G C hS hU hR u hK hP F := pullback.lift_snd _ _ _

/-- The unit section is a section of the fibre over `Spec κ(u)`. -/
theorem unitFibreSection_comp_fst :
    unitFibreSection G C hS hU hR u hK hP F ≫
        pullback.fst (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR) =
      𝟙 _ := pullback.lift_fst _ _ _

/-- On schemes, the unit arrow at `u` followed by the target is the canonical morphism
`Spec κ(u) ⟶ U`. -/
theorem toScheme_map_unitArrowSite_comp_target :
    (BigFppfOver.toScheme C S hS).map (unitArrowSite G C hS hU hR u hK hP F) ≫
        G.target.left = G.objects.left.fromSpecResidueField u := by
  have h : (BigFppfOver.toScheme C S hS).map
      (unitArrowSite G C hS hU hR u hK hP F ≫ targetSiteMap G C hS hU hR) =
      (BigFppfOver.toScheme C S hS).map (residueSiteMap G C hS hU u hK) :=
    congrArg _ (unitArrowSite_comp_target G C hS hU hR u hK hP F)
  rw [Functor.map_comp] at h
  exact h

/-- The unit section, read in the scheme-theoretic fibre and followed by the inclusion of the
fibre into the arrow scheme, is the unit arrow. -/
theorem unitFibrePoint_comp_fiberι :
    ((BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) ≫
        (etaleLocalFibreIso G C hS hU hR u hK).hom) ≫ G.source.left.fiberι u =
      (BigFppfOver.toScheme C S hS).map (unitArrowSite G C hS hU hR u hK hP F) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => (BigFppfOver.toScheme C S hS).map
          (unitFibreSection G C hS hU hR u hK hP F) ≫ k)
        (fibreIso_hom_comp_fiberι G C hS hU hR u hK)).trans
      (((BigFppfOver.toScheme C S hS).map_comp
            (unitFibreSection G C hS hU hR u hK hP F)
            (pullback.snd (residueSiteMap G C hS hU u hK)
              (sourceSiteMap G C hS hU hR))).symm.trans
        (congrArg (BigFppfOver.toScheme C S hS).map
          (unitFibreSection_comp_snd G C hS hU hR u hK hP F))))

/-- The unit section, read in the scheme-theoretic fibre and followed by the inclusion of the
fibre and the target, is the canonical morphism `Spec κ(u) ⟶ U`. -/
theorem unitFibrePoint_comp_target :
    ((BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) ≫
        (etaleLocalFibreIso G C hS hU hR u hK).hom) ≫
        (G.source.left.fiberι u ≫ G.target.left) =
      G.objects.left.fromSpecResidueField u :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ G.target.left)
        (unitFibrePoint_comp_fiberι G C hS hU hR u hK hP F)).trans
      (toScheme_map_unitArrowSite_comp_target G C hS hU hR u hK hP F))

/-! ### The finite open subspace cut out by an open of the fibre -/

variable (W : (G.source.left.fiber u).Opens)

/-- **The point of the fibre carried by the unit section lies in `Z_u`.** For an open `W` of
the scheme-theoretic fibre whose points are exactly the arrows whose target is `u` — which is
what the étale localization of Stacks 04RL produces — the unit section lands in `W`, because the
target of the unit arrow at `u` is `u`. -/
theorem unitFibrePoint_mem
    (hW : ∀ x : G.source.left.fiber u,
      x ∈ W ↔ G.target.left (G.source.left.fiberι u x) = u)
    (y : (BigFppfOver.toScheme C S hS).obj
      (schemeSiteObject C hS (X := residueOver G u) hK)) :
    (etaleLocalFibreIso G C hS hU hR u hK).hom
      ((BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) y) ∈ W := by
  rw [hW]
  have h := congrArg (fun k => k y) (unitFibrePoint_comp_target G C hS hU hR u hK hP F)
  simp only [Scheme.Hom.comp_apply] at h
  rw [h]
  have hr : (G.objects.left.fromSpecResidueField u) y ∈
      Set.range (G.objects.left.fromSpecResidueField u) := ⟨y, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at hr
  exact hr

/-- An open `W` of the scheme-theoretic fibre, read as an open immersion into the underlying
scheme of the fibre formed in the site. -/
abbrev fibreOpenImmersion :
    W.toScheme ⟶ (BigFppfOver.toScheme C S hS).obj (fibreSiteObject G C hS hU hR u hK) :=
  W.ι ≫ (etaleLocalFibreIso G C hS hU hR u hK).inv

/-- That morphism is an open immersion: it is the open immersion of `W` followed by an
isomorphism. -/
theorem isOpenImmersion_fibreOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion (fibreOpenImmersion G C hS hU hR u hK W) :=
  inferInstance

/-- Composing that open immersion with the projection of the fibre formed in the site to
`Spec κ(u)` is the structure morphism of `W` over the residue field. -/
theorem fibreOpenImmersion_comp_fst :
    fibreOpenImmersion G C hS hU hR u hK W ≫ (BigFppfOver.toScheme C S hS).map
        (pullback.fst (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)) =
      W.ι ≫ G.source.left.fiberToSpecResidueField u := by
  rw [← fibreIso_hom_comp_fiberToSpecResidueField G C hS hU hR u hK]
  show W.ι ≫ (etaleLocalFibreIso G C hS hU hR u hK).inv ≫
    (etaleLocalFibreIso G C hS hU hR u hK).hom ≫ G.source.left.fiberToSpecResidueField u = _
  rw [Iso.inv_hom_id_assoc]

/-- The open `W` of the fibre, as an object of the site over `S`. Its underlying scheme is `W`
itself, and it lies in the site because an open subscheme of a scheme of the site does. -/
abbrev fibreOpenSite : BigFppfOver C S hS :=
  etaleLocalSiteOpenObject C S hS (fibreSiteObject G C hS hU hR u hK)
    (fibreOpenImmersion G C hS hU hR u hK W)
    (isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W)

/-- The inclusion of that object into the fibre formed in the site. -/
abbrev fibreOpenSiteMap : fibreOpenSite G C hS hU hR u hK W ⟶ fibreSiteObject G C hS hU hR u hK :=
  siteOpenMap C S hS (fibreSiteObject G C hS hU hR u hK)
    (fibreOpenImmersion G C hS hU hR u hK W)
    (isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W)

/-- Yoneda carries the fibre formed in the site to the fibre product of the presheaves. -/
abbrev fibreYonedaIso :
    yoneda.obj (fibreSiteObject G C hS hU hR u hK) ≅
      pullback (yoneda.map (residueSiteMap G C hS hU u hK))
        (yoneda.map (sourceSiteMap G C hS hU hR)) :=
  ((IsPullback.of_hasPullback (residueSiteMap G C hS hU u hK)
    (sourceSiteMap G C hS hU hR)).map yoneda).isoPullback

/-- The open `W` of the fibre, as a morphism of presheaves into the ambient fibre product
`Spec κ(u) ×_{u, U, s} R`. -/
abbrev fibreOpenPresheafMap :
    yoneda.obj (fibreOpenSite G C hS hU hR u hK W) ⟶
      pullback (yoneda.map (residueSiteMap G C hS hU u hK))
        (yoneda.map (sourceSiteMap G C hS hU hR)) :=
  yoneda.map (fibreOpenSiteMap G C hS hU hR u hK W) ≫ (fibreYonedaIso G C hS hU hR u hK).hom

/-- That morphism is a monomorphism: the underlying morphism of schemes of the inclusion of
`W` is an open immersion, hence a monomorphism, and the comparison functor to schemes and Yoneda
both reflect and preserve monomorphisms. -/
theorem mono_fibreOpenPresheafMap : Mono (fibreOpenPresheafMap G C hS hU hR u hK W) := by
  have h₀ : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme C S hS).map
      (fibreOpenSiteMap G C hS hU hR u hK W)) :=
    isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W
  let := h₀
  have h₁ : Mono ((BigFppfOver.toScheme C S hS).map
      (fibreOpenSiteMap G C hS hU hR u hK W)) := inferInstance
  have h₂ : Mono (fibreOpenSiteMap G C hS hU hR u hK W) :=
    (BigFppfOver.toScheme C S hS).mono_of_mono_map h₁
  have h₃ : Mono (yoneda.map (fibreOpenSiteMap G C hS hU hR u hK W)) :=
    Functor.map_mono yoneda _
  exact @mono_comp _ _ _ _ _ _ h₃ _ (IsIso.mono_of_iso _)

/-- That morphism is an open immersion of algebraic spaces, being the Yoneda image of a
morphism of the site whose underlying morphism of schemes is an open immersion, followed by an
isomorphism. -/
theorem isOpenImmersion_fibreOpenPresheafMap :
    IsOpenImmersion C S hS (fibreOpenPresheafMap G C hS hU hR u hK W) :=
  MorphismProperty.RespectsIso.postcomp _ _ _
    (FinitePartChart.presheaf_yoneda_map C S hS _ (fibreOpenSiteMap G C hS hU hR u hK W)
      (isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W))

/-- Composing it with the projection to `Spec κ(u)` is the Yoneda image of the corresponding
composition in the site. -/
theorem fibreOpenPresheafMap_comp_fst :
    fibreOpenPresheafMap G C hS hU hR u hK W ≫
        pullback.fst (yoneda.map (residueSiteMap G C hS hU u hK))
          (yoneda.map (sourceSiteMap G C hS hU hR)) =
      yoneda.map (fibreOpenSiteMap G C hS hU hR u hK W ≫
        pullback.fst (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)) := by
  simp only [fibreOpenPresheafMap, fibreYonedaIso, Category.assoc, Functor.map_comp,
    IsPullback.isoPullback_hom_fst]

/-- Composing it with the projection to `R` is the Yoneda image of the corresponding
composition in the site. -/
theorem fibreOpenPresheafMap_comp_snd :
    fibreOpenPresheafMap G C hS hU hR u hK W ≫
        pullback.snd (yoneda.map (residueSiteMap G C hS hU u hK))
          (yoneda.map (sourceSiteMap G C hS hU hR)) =
      yoneda.map (fibreOpenSiteMap G C hS hU hR u hK W ≫
        pullback.snd (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)) := by
  simp only [fibreOpenPresheafMap, fibreYonedaIso, Category.assoc, Functor.map_comp,
    IsPullback.isoPullback_hom_snd]

/-- When `W` is finite over the residue field, its projection to `Spec κ(u)` inside the ambient
fibre product is finite in the relatively representable sense tested on representables. -/
theorem presheaf_isFinite_fibreOpenPresheafMap
    (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u)) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf
      (fibreOpenPresheafMap G C hS hU hR u hK W ≫
        pullback.fst (yoneda.map (residueSiteMap G C hS hU u hK))
          (yoneda.map (sourceSiteMap G C hS hU hR))) := by
  rw [fibreOpenPresheafMap_comp_fst]
  refine FinitePartChart.presheaf_yoneda_map C S hS _ _ ?_
  have hmap : (BigFppfOver.toScheme C S hS).map
      (fibreOpenSiteMap G C hS hU hR u hK W ≫
        pullback.fst (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)) =
      W.ι ≫ G.source.left.fiberToSpecResidueField u := by
    rw [Functor.map_comp, toScheme_map_siteOpenMap]
    exact fibreOpenImmersion_comp_fst G C hS hU hR u hK W
  rw [hmap]
  exact hWfin

/-- The unit section factors through `W` set-theoretically, for an open `W` whose points are
exactly the arrows whose target is `u`: the spectrum of a field has one point, and the point of
the fibre the unit section carries lies in `W`. -/
theorem unitFibreSection_range_le
    (hW : ∀ x : G.source.left.fiber u,
      x ∈ W ↔ G.target.left (G.source.left.fiberι u x) = u) :
    Set.range ((BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F)) ⊆
      Set.range (fibreOpenImmersion G C hS hU hR u hK W) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨⟨(etaleLocalFibreIso G C hS hU hR u hK).hom
      ((BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) y),
    unitFibrePoint_mem G C hS hU hR u hK hP F W hW y⟩, ?_⟩
  show (etaleLocalFibreIso G C hS hU hR u hK).inv
      ((etaleLocalFibreIso G C hS hU hR u hK).hom
        ((BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) y)) =
    (BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) y
  rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

/-- **The pair `(u, Z_u)` of Stacks 04PC** attached to an open `W` of the fibre `F_u` finite
over `κ(u)`: the canonical morphism `Spec κ(u) ⟶ U` together with `W` read as an open subspace
of `Spec κ(u) ×_{u, U, s} R` whose projection to `Spec κ(u)` is finite. -/
def fibreFiniteOpenSubspace
    (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u)) :
    FiniteOpenSubspace C S hS (G.realization C hS hU hR hP).source
      (schemeSpace (schemeSiteObject C hS (X := residueOver G u) hK)) :=
  finiteOpenSubspaceOfRange' C S hS (G.realization C hS hU hR hP).source
    (schemeSiteObject C hS (X := residueOver G u) hK)
    (fibreOpenSite G C hS hU hR u hK W)
    (ObjectProperty.homMk (yoneda.map (residueSiteMap G C hS hU u hK)))
    (fibreOpenPresheafMap G C hS hU hR u hK W)
    (mono_fibreOpenPresheafMap G C hS hU hR u hK W)
    (isOpenImmersion_fibreOpenPresheafMap G C hS hU hR u hK W)
    (presheaf_isFinite_fibreOpenPresheafMap G C hS hU hR u hK W hWfin)

/-! ### The unit section lands in the open -/

variable (hW : ∀ x : G.source.left.fiber u,
  x ∈ W ↔ G.target.left (G.source.left.fiberι u x) = u)

/-- The factorization of the unit section through the open `W`, which exists by the universal
property of an open immersion because the point of the fibre the unit section carries lies in
`W`. -/
def unitOpenLift :
    (BigFppfOver.toScheme C S hS).obj (schemeSiteObject C hS (X := residueOver G u) hK) ⟶
      (BigFppfOver.toScheme C S hS).obj (fibreOpenSite G C hS hU hR u hK W) :=
  AlgebraicGeometry.IsOpenImmersion.lift
    (H := isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W)
    (fibreOpenImmersion G C hS hU hR u hK W)
    ((BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F))
    (unitFibreSection_range_le G C hS hU hR u hK hP F W hW)

/-- That morphism is a factorization of the unit section through `W`. -/
theorem unitOpenLift_fac :
    unitOpenLift G C hS hU hR u hK hP F W hW ≫ fibreOpenImmersion G C hS hU hR u hK W =
      (BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) :=
  AlgebraicGeometry.IsOpenImmersion.lift_fac
    (H := isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W) _ _ _

/-- The factorization of the unit section through `W`, as a morphism of the site over `S`. -/
def unitOpenSection :
    schemeSiteObject C hS (X := residueOver G u) hK ⟶ fibreOpenSite G C hS hU hR u hK W :=
  Over.homMk (ObjectProperty.homMk (unitOpenLift G C hS hU hR u hK hP F W hW)) (by
    apply ObjectProperty.hom_ext
    change unitOpenLift G C hS hU hR u hK hP F W hW ≫
      (fibreOpenImmersion G C hS hU hR u hK W ≫
        (fibreSiteObject G C hS hU hR u hK).hom.hom) = _
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ (fibreSiteObject G C hS hU hR u hK).hom.hom)
        (unitOpenLift_fac G C hS hU hR u hK hP F W hW))).trans
      (congrArg (fun k => k.hom) (Over.w (unitFibreSection G C hS hU hR u hK hP F))))

/-- That morphism of the site is a factorization of the unit section. -/
theorem unitOpenSection_comp :
    unitOpenSection G C hS hU hR u hK hP F W hW ≫ fibreOpenSiteMap G C hS hU hR u hK W =
      unitFibreSection G C hS hU hR u hK hP F :=
  (BigFppfOver.toScheme C S hS).map_injective
    (((BigFppfOver.toScheme C S hS).map_comp _ _).trans
      ((congrArg (fun k => (BigFppfOver.toScheme C S hS).map
            (unitOpenSection G C hS hU hR u hK hP F W hW) ≫ k)
          (toScheme_map_siteOpenMap C S hS (fibreSiteObject G C hS hU hR u hK)
            (fibreOpenImmersion G C hS hU hR u hK W)
            (isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W))).trans
        (unitOpenLift_fac G C hS hU hR u hK hP F W hW)))

/-- Composing it with the inclusion of `W` and the projection to `Spec κ(u)` is the
identity. -/
theorem unitOpenSection_comp_fst :
    unitOpenSection G C hS hU hR u hK hP F W hW ≫ (fibreOpenSiteMap G C hS hU hR u hK W ≫
        pullback.fst (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)) = 𝟙 _ := by
  rw [← Category.assoc, unitOpenSection_comp]
  exact unitFibreSection_comp_fst G C hS hU hR u hK hP F

/-- Composing it with the inclusion of `W` and the projection to `R` is the unit arrow. -/
theorem unitOpenSection_comp_snd :
    unitOpenSection G C hS hU hR u hK hP F W hW ≫ (fibreOpenSiteMap G C hS hU hR u hK W ≫
        pullback.snd (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)) =
      unitArrowSite G C hS hU hR u hK hP F := by
  rw [← Category.assoc, unitOpenSection_comp]
  exact unitFibreSection_comp_snd G C hS hU hR u hK hP F

include hW in
/-- **The pair `(u, Z_u)` contains the unit**, which is the condition of Stacks 04RQ placing it
in the finite part with section `(R_s/U, e)_fin`: the unit arrow at `u` has target `u`, so the
point of the fibre it carries lies in `W`, and the unit section of the ambient fibre product
therefore factors through `W`. -/
theorem containsSection_fibreFiniteOpenSubspace
    (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u)) :
    ContainsSection C S hS (G.realization C hS hU hR hP).source F.unit F.unit_source
      (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin) := by
  refine ⟨yoneda.map (unitOpenSection G C hS hU hR u hK hP F W hW) ≫
    Subfunctor.toRange (fibreOpenPresheafMap G C hS hU hR u hK W), ?_⟩
  refine ((Category.assoc _ _ _).trans
    (congrArg (fun k => yoneda.map (unitOpenSection G C hS hU hR u hK hP F W hW) ≫ k)
      (Subfunctor.toRange_ι (fibreOpenPresheafMap G C hS hU hR u hK W)))).trans
    (pullback.hom_ext ?_ ?_)
  · exact ((Category.assoc _ _ _).trans
      ((congrArg (fun k => yoneda.map (unitOpenSection G C hS hU hR u hK hP F W hW) ≫ k)
          (fibreOpenPresheafMap_comp_fst G C hS hU hR u hK W)).trans
        (((yoneda.map_comp _ _).symm.trans
            (congrArg yoneda.map
              (unitOpenSection_comp_fst G C hS hU hR u hK hP F W hW))).trans
          (yoneda.map_id _)))).trans (pullback.lift_fst _ _ _).symm
  · exact ((Category.assoc _ _ _).trans
      ((congrArg (fun k => yoneda.map (unitOpenSection G C hS hU hR u hK hP F W hW) ≫ k)
          (fibreOpenPresheafMap_comp_snd G C hS hU hR u hK W)).trans
        (((yoneda.map_comp _ _).symm.trans
            (congrArg yoneda.map
              (unitOpenSection_comp_snd G C hS hU hR u hK hP F W hW))).trans
          (yoneda_map_unitArrowSite G C hS hU hR u hK hP F)))).trans
      (pullback.lift_snd _ _ _).symm

/-! ### The point of the finite part over the residue field point -/

/-- The pair `(u, Z_u)` read as a `Spec κ(u)`-valued section of the finite part of the source,
through the bijection of Stacks 04PE. -/
def fibrePresheafSection
    (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u)) :
    (finiteOpenSubspacePresheaf C S hS (G.realization C hS hU hR hP).source).toFunctor.obj
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) :=
  yonedaEquiv ((finiteOpenSubspaceEquiv C S hS (G.realization C hS hU hR hP).source
    (schemeSpace (schemeSiteObject C hS (X := residueOver G u) hK))).1.symm
    (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin))

/-- That section of the finite part lies over the canonical morphism `Spec κ(u) ⟶ U`. -/
theorem baseMap_fibrePresheafSection
    (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u)) :
    (finiteOpenSubspacePresheaf C S hS (G.realization C hS hU hR hP).source).baseMap.app
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (fibrePresheafSection G C hS hU hR u hK hP W hWfin) =
      residueSiteMap G C hS hU u hK := by
  have h := finiteOpenSubspaceEquiv_toBase (G.realization C hS hU hR hP).source
    ((finiteOpenSubspaceEquiv C S hS (G.realization C hS hU hR hP).source
      (schemeSpace (schemeSiteObject C hS (X := residueOver G u) hK))).1.symm
      (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin))
  rw [Equiv.apply_symm_apply] at h
  have h2 := congrArg (fun k => k.app
    (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
    (𝟙 (schemeSiteObject C hS (X := residueOver G u) hK))) h
  exact h2.symm.trans (Category.id_comp (residueSiteMap G C hS hU u hK))

include hW in
/-- That section of the finite part lies in the open subspace `(R_s/U, e)_fin` cut out by
containing the unit, by Stacks 04RR. -/
theorem mem_finitePartWithSection
    (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u)) :
    fibrePresheafSection G C hS hU hR u hK hP W hWfin ∈
      (finitePartWithSection C S hS (G.realization C hS hU hR hP).source F.unit
        F.unit_source).toSubfunctor.obj
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) := by
  rw [(finitePartWithSection C S hS (G.realization C hS hU hR hP).source F.unit
    F.unit_source).mem_iff]
  refine containsSection_restrict (G.realization C hS hU hR hP).source F.unit F.unit_source
    ((finiteOpenSubspaceEquiv C S hS (G.realization C hS hU hR hP).source
      (schemeSpace (schemeSiteObject C hS (X := residueOver G u) hK))).1.symm
      (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin))
    ?_ (schemeSiteObject C hS (X := residueOver G u) hK)
    (𝟙 (schemeSiteObject C hS (X := residueOver G u) hK))
  rw [Equiv.apply_symm_apply]
  exact containsSection_fibreFiniteOpenSubspace G C hS hU hR u hK hP F W hW hWfin

include hW in
/-- **The point `u' : Spec κ(u) ⟶ U'`.** The pair `(u, Z_u)`, read as a `Spec κ(u)`-valued
point of the object space of the finite part of the groupoid. -/
def etaleLocalFibrePoint
    (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u)) :
    F.objects.obj.obj (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) :=
  F.objectsEquiv.inv.app _
    ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
      mem_finitePartWithSection G C hS hU hR u hK hP F W hW hWfin⟩

include hW in
/-- The image of that point under the projection `g : U' ⟶ U` is the canonical morphism
`Spec κ(u) ⟶ U`, read in the site. -/
theorem objectProjection_fibrePoint
    (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u)) :
    F.objectProjection.hom.app
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin) =
      residueSiteMap G C hS hU u hK := by
  have h1 := congrArg (fun k : F.objects.obj ⟶ (G.realization C hS hU hR hP).objects.obj =>
      k.app (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))
    F.objectProjection_spec
  have h2 : F.objectsEquiv.hom.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin) =
      ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
        mem_finitePartWithSection G C hS hU hR u hK hP F W hW hWfin⟩ :=
    congrArg (fun k => k.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
        mem_finitePartWithSection G C hS hU hR u hK hP F W hW hWfin⟩)
      F.objectsEquiv.inv_hom_id
  refine h1.trans ((congrArg (fun z =>
    (finiteOpenSubspacePresheaf C S hS (G.realization C hS hU hR hP).source).baseMap.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      ((finitePartWithSection C S hS (G.realization C hS hU hR hP).source F.unit
        F.unit_source).toSubfunctor.ι.app
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) z)) h2).trans ?_)
  exact baseMap_fibrePresheafSection G C hS hU hR u hK hP W hWfin

include hW in
/-- **The point `u'` lies over `u`**: its composition with the étale projection `g : U' ⟶ U`
is the canonical morphism `Spec κ(u) ⟶ U`. -/
theorem lies_over_fibrePoint
    (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u)) :
    (yonedaSchemePointEquiv C hS hU
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (F.objectProjection.hom.app _
          (etaleLocalFibrePoint G C hS hU hR u hK hP F W hW hWfin))).left =
      G.objects.left.fromSpecResidueField u := by
  rw [objectProjection_fibrePoint G C hS hU hR u hK hP F W hW hWfin]
  exact congrArg Over.Hom.left (siteToOver_map_schemeSiteMap C hS
    (X := residueOver G u) (Y := G.objects) hK hU (residuePoint G u))

end Fibre

/-! ### Stacks 03FM: the étale neighbourhood and the point over `u` -/

/-- **Stacks Project, Tag 03FM, weaker: the étale neighbourhood and the point, not the
splitting.**

In the strong splitting situation of Stacks 04RL there is an algebraic space `U'`, an étale
morphism `g : U' ⟶ U` of algebraic spaces, and a point `u' : Spec κ(u) ⟶ U'` lying over
`u : Spec κ(u) ⟶ U`.

`U'` is the finite part `(R_s/U, e)_fin` of Stacks 04RU, `g` its étale projection, and `u'` the
pair `(u, Z_u)` where `Z_u` is the open and closed piece of the fibre `F_u = R ×_{s, U} Spec κ(u)`
supported on the arrows from `u` to itself, which is finite over `κ(u)` by
`AlgebraicGeometry.Space.StrongSplittingSituation.exists_fiberOpens_stabilizer`.

What Stacks 03FM asserts beyond this — that the restriction `R|_{U'}` is *strongly split* over
`u'` — is **not** proved here; see the implementation notes of this file. -/
theorem exists_etale_point_of_strongSplittingSituation
    (D : StrongSplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u))) :
    ∃ (U' : AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      IsEtale C D.S hS g.hom ∧
      ∃ v : U'.obj.obj (Opposite.op
          (residueFieldSiteObject C hS (X := D.groupoid.objects) D.u hK)),
        (yonedaSchemePointEquiv C hS hU (Opposite.op
            (residueFieldSiteObject C hS (X := D.groupoid.objects) D.u hK))
            (g.hom.app _ v)).left =
          D.groupoid.objects.left.fromSpecResidueField D.u := by
  obtain ⟨W, hW, _, hWfin⟩ := D.exists_fiberOpens_stabilizer
  exact ⟨(realizationFinitePart D.groupoid C hS hU hR hP).objects,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection_etale,
    etaleLocalFibrePoint D.groupoid C hS hU hR D.u hK hP
      (realizationFinitePart D.groupoid C hS hU hR hP) W hW hWfin,
    lies_over_fibrePoint D.groupoid C hS hU hR D.u hK hP
      (realizationFinitePart D.groupoid C hS hU hR hP) W hW hWfin⟩

end AlgebraicGeometry.Space

end
