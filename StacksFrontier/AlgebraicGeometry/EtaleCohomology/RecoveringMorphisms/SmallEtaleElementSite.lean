module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.SmallEtalePostcompose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.ToposLocalization

/-!
# Stacks 04IE for the small étale site, as an identification of ringed topoi

Let `S` be a scheme of a big étale site and `U` an object of its small étale site, i.e. a scheme
étale over `S`. Stacks 04IE localizes the small étale ringed topos of `S` at a sheaf; taking that
sheaf to be the one represented by `U`, the localization is the small étale ringed topos of the
scheme of `U`.

The route taken here is the one the small étale site makes available and a general site does not.
The small étale topology is subcanonical (`AlgebraicGeometry.SmallEtale.topology_subcanonical`),
so a section of `h_U` over `T` *is* a morphism `T ⟶ U`, and therefore the site of elements of
`h_U` is the slice `(S_étale)/U` as a category: the identification of the two topoi is
**restriction along a functor of sites**. Restriction of a restriction being restriction along
the composite, and the composite `U_étale ⥤ elementSite(h_U) ⥤ S_étale` being
`AlgebraicGeometry.SmallEtale.postcompose`, which leaves the underlying scheme of an object
alone, the comparison of the two structure sheaves is an *equality* of sheaves of commutative
rings.

## Main definitions

* `AlgebraicGeometry.SmallEtale.representableSheaf`: the sheaf on the small étale site of `S`
  represented by `U`, a sheaf because the topology is subcanonical.
* `AlgebraicGeometry.SmallEtale.overToElementSite`: the slice `(S_étale)/U` as the site of
  elements of that sheaf, and `AlgebraicGeometry.SmallEtale.toElementSite`: the small étale site
  of the scheme of `U` as that site of elements.
* `AlgebraicGeometry.SmallEtale.elementSiteSheafEquivalence`: the resulting identification of the
  small étale topos of the scheme of `U` with the topos of the localization, as restriction along
  that functor of sites, and `.localizedToposMorphism`: the same read as a morphism of topoi.
* `AlgebraicGeometry.SmallEtale.localizedStructureSheafIso`: the comparison of the two structure
  sheaves, in inverse-image form.
* `AlgebraicGeometry.SmallEtale.localizedRingedToposHom`: **Stacks 04IE for the small étale site,
  as a morphism of ringed topoi.**

## Main results

* `AlgebraicGeometry.SmallEtale.functorPushforward_mem_elementTopology_iff`: the comparison of
  the two topologies — a sieve of the slice is covering for the slice topology exactly when its
  image in the site of elements is covering for the restricted topology of Stacks 0791.
* `AlgebraicGeometry.SmallEtale.toElementSite_comp_elementProjection`: the composite functor of
  sites down to the small étale site of `S` is `AlgebraicGeometry.SmallEtale.postcompose`.
* `AlgebraicGeometry.SmallEtale.sheafPushforward_localizedRingedTopos_O`: **the structure sheaf
  of the localization, restricted to the small étale site of the scheme of `U`, is its structure
  sheaf** — an equality, which is what the previous two buy.

## Implementation notes

The sheaf represented by `U` is given as `⟨yoneda.obj U, _⟩` rather than as the sheafification
`(presheafToSheaf _ _).obj (yoneda.obj U)` or as `(SmallEtale.topology B S hS).yoneda.obj U`.
That is not a convenience. The site of elements is `CostructuredArrow yoneda F.obj`, and only at
this spelling does `F.obj` reduce to `yoneda.obj U` for `rw` and for instance search;
the comparison of topologies below fails to rewrite at either of the other two spellings, which
are `def`s, and the `IsDenseSubsite` instance's three default fields then fail to synthesize as
well.

Both halves of the functor of sites are equivalences, so the size condition of
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` is free: a structured-arrow category over an
equivalence has an initial object, hence limits of its shape exist in any category
(`AlgebraicGeometry.SmallEtale.hasLimitsOfShape_structuredArrow_toElementSite`). Nothing here
needs the sections universe above the universe `u` of the schemes, and nothing raises a heartbeat
limit.

**How the universes were settled.** Putting the equality into inverse-image form, through
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, fails outright if the universes are left
to be inferred: `Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor` takes its
`HasSheafCompose` hypotheses before the morphism of topoi that would determine the two sites, so
instance search runs while they are metavariables and the `UnivLE` side conditions get stuck on
`u =?= max (u + 1) ?u`.  Four things had to be right, each found by building and the last by
`pp.universes` in a throwaway probe:

* the binder order is that of the `universe ww ww' vv uu vv' uu'` command of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposCommRingImageAdjunction.lean`, giving
  `inverseImageCommRingFunctor.{u, u, u, u + 1, u, max (u + 1) u}` and
  `restrictionCommRingIso.{u, u, u + 1, u, max (u + 1) u}`;
* the second site's object universe must be written `max (u + 1) u`, not `u + 1`;
* the localization must be pinned `RingedTopos.localizedRingedTopos.{u, u + 1}` throughout, or
  its sections universe comes back as the `?u` above;
* the topology handed to `restrictionCommRingIso` must be spelled
  `(RingedTopos.localizedRingedTopos.{u, u + 1} _ _).J` and not the definitionally equal
  `RingedTopos.elementTopology.{u, u + 1} _ _`, since the `HasSheafCompose` instances exist only
  at the localization's spelling — and the continuity instance at that spelling must be *passed
  explicitly*, because `restrictionCommRingIso` asks for it while its functor argument is still a
  metavariable, so a global instance, a `haveI` and a `letI` are all too late.

`CategoryTheory.Functor.IsContinuous` has **four** universe parameters and none of them is the
sheaf-value universe: `IsContinuous.{vC, vD, uC, uD}`, the morphisms and then the objects of the
two sites.  Both spellings of the topology carry the same four here,
`IsContinuous.{u, u, u + 1, u + 1}`, which is what makes
`AlgebraicGeometry.SmallEtale.isContinuous_toElementSite_localized` a transfer between
discrimination-tree keys and nothing more.

**What is left before input (1) of the Stacks 04I7 gluing closes.** One step. The three
topos-level forms of Stacks 04IE in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/OpenLocalization.lean` are
stated at the *sheafification* spelling of the represented sheaf, which is the spelling Stacks
04IF's half of that input localizes at, whereas the ringed identification above is at the
representable spelling `⟨yoneda.obj U, _⟩`.  Carrying it across needs the **ring-level** transport
of a localization along an isomorphism of sheaves, where
`AlgebraicGeometry.RingedTopos.localizedToposEquivalenceOfIso` gives only the topos-level one.
That transport is of the same shape as the construction here — post-composition with an
isomorphism of the target does not change the projection from the site of elements, so
`CategoryTheory.CostructuredArrow.mapIso` is again a functor of sites over `S_étale`, its two
topologies are compared by the same `mem_topology_iff` argument, and the two structure sheaves
are again restrictions along equal composites — so it should reuse this module's shape rather
than introduce a new device.

## References

* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS)

/-- **The sheaf on the small étale site of `S` represented by an object `U` of that site.** The
presheaf `T ↦ Mor_S(T, U)` is a sheaf because the small étale topology is subcanonical
(`AlgebraicGeometry.SmallEtale.isSheaf_yoneda_obj`).

It is a reducible abbreviation, and its underlying presheaf is `yoneda.obj U` on the nose; that
is what makes the site of elements of it literally `CostructuredArrow yoneda (yoneda.obj U)`. -/
abbrev representableSheaf : (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)).Topos :=
  ⟨yoneda.obj U, (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_yoneda_obj B S hS U)⟩

/-- **The slice of the small étale site of `S` at `U` is the site of elements of `h_U`.** An
object of the site of elements is a pair `(T, s)` with `s` a section of `h_U` over `T`, which by
subcanonicality is a morphism `T ⟶ U`, i.e. an object of the slice; this is that identification,
as a functor. -/
def overToElementSite : Over U ⥤
    RingedTopos.elementSite.{u, u + 1} (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
      (representableSheaf B S hS U) where
  obj T := CostructuredArrow.mk (yoneda.map T.hom)
  map {T T'} g := CostructuredArrow.homMk g.left (by
    change yoneda.map g.left ≫ yoneda.map T'.hom = yoneda.map T.hom
    rw [← yoneda.map_comp, Over.w])

/-- The identification above commutes with the two projections to the small étale site of `S`:
the projection from the site of elements of `h_U` is the forgetful functor of the slice. -/
theorem overToElementSite_comp_elementProjection :
    overToElementSite B S hS U ⋙
        RingedTopos.elementProjection.{u, u + 1}
          (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
          (representableSheaf B S hS U) =
      Over.forget U :=
  rfl

/-- The functor `overToElementSite` is faithful. -/
instance : (overToElementSite B S hS U).Faithful where
  map_injective {T T'} g g' h := by
    apply Over.OverMorphism.ext
    exact congrArg (fun k => k.left) h

/-- The functor `overToElementSite` is full. -/
instance : (overToElementSite B S hS U).Full where
  map_surjective φ :=
    ⟨Over.homMk φ.left
      (yoneda.map_injective ((yoneda.map_comp _ _).trans (CostructuredArrow.w φ))),
      CostructuredArrow.hom_ext _ _ rfl⟩

/-- The functor `overToElementSite` is essentially surjective. -/
instance : (overToElementSite B S hS U).EssSurj where
  mem_essImage Z := by
    refine ⟨Over.mk (yoneda.preimage Z.hom), ⟨CostructuredArrow.isoMk (Iso.refl _) ?_⟩⟩
    change yoneda.map (𝟙 _) ≫ Z.hom = yoneda.map (yoneda.preimage Z.hom)
    simp

/-- The functor `overToElementSite` is an equivalence between the slice `(S_étale)/U` and the site
of elements of `h_U`. -/
instance : (overToElementSite B S hS U).IsEquivalence where

/-- **The comparison of the two topologies.** A sieve of the slice `(S_étale)/U` is covering for
the slice topology exactly when its image in the site of elements of `h_U` is covering for the
restricted topology of Stacks 0791.

Both conditions say the same thing about the same sieve of the small étale site of `S`: that the
image of the sieve under the projection is covering there. For the slice that is
`CategoryTheory.GrothendieckTopology.mem_over_iff`, for the site of elements it is Stacks 0791's
first assertion, and the two projections agree by
`AlgebraicGeometry.SmallEtale.overToElementSite_comp_elementProjection`. -/
theorem functorPushforward_mem_elementTopology_iff (Y : Over U) (T : Sieve Y) :
    Sieve.functorPushforward (overToElementSite B S hS U) T ∈
        RingedTopos.elementTopology.{u, u + 1}
          (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
          (representableSheaf B S hS U) ((overToElementSite B S hS U).obj Y) ↔
      T ∈ (SmallEtale.topology B S hS).over U Y := by
  rw [GrothendieckTopology.mem_over_iff]
  simp only [RingedTopos.elementTopology, RingedTopos.elementProjection]
  rw [Stacks.Topos.Localized.restrictedTopology_eq_topology,
    Stacks.Topos.Localized.mem_topology_iff, ← Sieve.functorPushforward_comp]
  rfl

/-- The slice of the small étale site of `S` at `U` is a **dense subsite** of the site of
elements of `h_U`, being equivalent to it compatibly with the topologies. -/
instance overToElementSite_isDenseSubsite : (overToElementSite B S hS U).IsDenseSubsite
    ((SmallEtale.topology B S hS).over U)
    (RingedTopos.elementTopology.{u, u + 1} (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
      (representableSheaf B S hS U)) where
  functorPushforward_mem_iff := functorPushforward_mem_elementTopology_iff B S hS U _ _

/-- **The small étale site of the scheme of `U` is the site of elements of `h_U`**: the
equivalence `AlgebraicGeometry.SmallEtale.localizationEquivalence` with the slice, followed by
the identification of the slice with the site of elements. -/
abbrev toElementSite : SmallEtale B U.obj.left.obj U.obj.left.property ⥤
    RingedTopos.elementSite.{u, u + 1} (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
      (representableSheaf B S hS U) :=
  (SmallEtale.localizationEquivalence B S hS U).functor ⋙ overToElementSite B S hS U

/-- **The composite functor of sites down to the small étale site of `S` is post-composition
with the structure morphism of `U`.** This is the identity that makes the comparison of the two
structure sheaves an equality: both are the restriction of `𝒪_S` along this functor. -/
theorem toElementSite_comp_elementProjection :
    toElementSite B S hS U ⋙
        RingedTopos.elementProjection.{u, u + 1}
          (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
          (representableSheaf B S hS U) =
      SmallEtale.postcompose B S hS U :=
  rfl

/-- The small étale site of the scheme of `U` is a dense subsite of the site of elements of
`h_U`: both halves of the composite are. -/
instance toElementSite_isDenseSubsite : (toElementSite B S hS U).IsDenseSubsite
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (RingedTopos.elementTopology.{u, u + 1} (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
      (representableSheaf B S hS U)) where
  functorPushforward_mem_iff := by
    intro Y T
    rw [Sieve.functorPushforward_comp]
    exact (functorPushforward_mem_elementTopology_iff B S hS U _ _).trans
      (Functor.IsDenseSubsite.functorPushforward_mem_iff
        (G := (SmallEtale.localizationEquivalence B S hS U).functor)
        (J := SmallEtale.topology B U.obj.left.obj U.obj.left.property)
        (K := (SmallEtale.topology B S hS).over U))

/-- **The size condition of `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` is free here.**
The functor of sites is an equivalence, so each structured-arrow category over it has an initial
object, and a category with an initial object has all limits in any category — in particular in
`Type u`, at the sections universe of the small étale ringed topos and not above it. -/
theorem hasLimitsOfShape_structuredArrow_toElementSite (A : Type*) [Category A]
    (T : (RingedTopos.elementSite.{u, u + 1}
      (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
      (representableSheaf B S hS U))ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow T (toElementSite B S hS U).op) A :=
  have := (mkInitialOfLeftAdjoint (toElementSite B S hS U).op
    (toElementSite B S hS U).asEquivalence.op.symm.toAdjunction T).hasInitial
  ⟨fun _ => inferInstance⟩

/-- **Stacks 04IE for the small étale site, on the topoi, by restriction along a functor of
sites.** The small étale topos of the scheme of `U` is the topos of the localization of the small
étale ringed topos of `S` at the sheaf `U` represents, and the identification is restriction
along `AlgebraicGeometry.SmallEtale.toElementSite`.

That it is a restriction, and not merely an equivalence, is the whole point: the three
topos-level forms in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/OpenLocalization.lean` factor
through Stacks 00Y1, whose functor is a lower shriek, and so carry no comparison of structure
sheaves; this one does, and the comparison is
`AlgebraicGeometry.SmallEtale.sheafPushforward_localizedRingedTopos_O`. -/
@[stacks 04IE "for the small étale site of an object `U` of the small étale site of `S`, with the
  identification given as restriction along a functor of sites: the small étale topos of the
  scheme of `U` is the topos of the localization of the small étale ringed topos of `S` at the
  sheaf `U` represents.  The functor of sites is the equivalence of the small étale site of the
  scheme of `U` with the slice at `U`, followed by the identification of that slice with the site
  of elements of the represented sheaf, which is available because the small étale topology is
  subcanonical; the comparison of the two topologies is
  `AlgebraicGeometry.SmallEtale.functorPushforward_mem_elementTopology_iff`"]
def elementSiteSheafEquivalence :
    Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property) (Type u) ≌
      (RingedTopos.localizedRingedTopos.{u, u + 1}
        (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
        (representableSheaf B S hS U)).Topos :=
  have := hasLimitsOfShape_structuredArrow_toElementSite B S hS U (Type u)
  Functor.IsDenseSubsite.sheafEquiv
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (RingedTopos.elementTopology.{u, u + 1} (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
      (representableSheaf B S hS U))
    (toElementSite B S hS U) (Type u)

/-- **The structure sheaf of the localization, restricted to the small étale site of the scheme
of `U`, is its structure sheaf.** This is the cheap presheaf identity, and it is an *equality*:
the structure sheaf of the localization is the restriction of `𝒪_S` along the projection from
the site of elements, restricting that along `toElementSite` restricts along the composite
(`AlgebraicGeometry.SmallEtale.toElementSite_comp_elementProjection`), the composite is
`AlgebraicGeometry.SmallEtale.postcompose`, and
`AlgebraicGeometry.SmallEtale.commRingStructurePresheaf` is
`(SmallEtale.toScheme B S hS).op ⋙ Scheme.Γ`, which `postcompose` leaves alone.

This is the comparison that the topos-level forms of Stacks 04IE do not carry, and the reason
this route was taken. -/
@[stacks 04IE "the comparison of the two structure sheaves, for the small étale site: the
  structure sheaf of the localization of the small étale ringed topos of `S` at the sheaf an
  object `U` represents, restricted along the functor of sites identifying the small étale site
  of the scheme of `U` with the site of elements, IS the structure sheaf of the small étale site
  of the scheme of `U`.  An equality of sheaves of commutative rings, both being the restriction
  of the structure sheaf of `S` along post-composition with the structure morphism of `U`"]
theorem sheafPushforward_localizedRingedTopos_O :
    ((toElementSite B S hS U).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
        (RingedTopos.elementTopology.{u, u + 1}
          (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
          (representableSheaf B S hS U))).obj
      (RingedTopos.localizedRingedTopos.{u, u + 1}
        (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
        (representableSheaf B S hS U)).O =
    SmallEtale.commRingStructureSheaf B U.obj.left.obj U.obj.left.property :=
  rfl


/-! ### Stacks 04IE for the small étale site, as a morphism of ringed topoi -/

/-- **Continuity of the functor of sites at the spelling `(localizedRingedTopos _ _).J`.**
`AlgebraicGeometry.SmallEtale.toElementSite_isDenseSubsite` gives continuity for
`RingedTopos.elementTopology _ _`, and the inverse-image form of the structure-sheaf comparison
asks for it at `(RingedTopos.localizedRingedTopos _ _).J` instead: the morphism of topoi whose
inverse image that form is taken along has the topos of the localization as its target.  The two
topologies are definitionally equal and carry the *same* universes
(`Functor.IsContinuous.{u, u, u + 1, u + 1}` on both sides), but they have different
discrimination-tree keys — the same duplication recorded for the `HasSheafCompose` pair
of the topos localization, and resolved the same way, by stating the instance at both spellings. -/
instance isContinuous_toElementSite_localized :
    Functor.IsContinuous.{u, u, u + 1, u + 1} (toElementSite B S hS U)
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      (RingedTopos.localizedRingedTopos.{u, u + 1}
        (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
        (representableSheaf B S hS U)).J :=
  inferInstanceAs (Functor.IsContinuous.{u, u, u + 1, u + 1} (toElementSite B S hS U)
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (RingedTopos.elementTopology.{u, u + 1}
      (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
      (representableSheaf B S hS U)))

/-- **The identification of the two topoi, read as a morphism of topoi.** Its inverse image is
restriction along `AlgebraicGeometry.SmallEtale.toElementSite`, i.e. the inverse of
`AlgebraicGeometry.SmallEtale.elementSiteSheafEquivalence`, which is left exact because an
equivalence is. -/
def localizedToposMorphism :
    MorphismOfTopoi (Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property) (Type u))
      (RingedTopos.localizedRingedTopos.{u, u + 1}
        (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
        (representableSheaf B S hS U)).Topos where
  inverseImage := (elementSiteSheafEquivalence B S hS U).inverse
  pushforward := (elementSiteSheafEquivalence B S hS U).functor
  adj := (elementSiteSheafEquivalence B S hS U).symm.toAdjunction
  preservesFiniteLimits :=
    haveI := (elementSiteSheafEquivalence B S hS U).symm.toAdjunction.rightAdjoint_preservesLimits
    ⟨fun _ _ _ ↦ inferInstance⟩

/-- **The comparison of the two structure sheaves, in inverse-image form.** The inverse image of
the localized structure sheaf along the identification is the structure sheaf of the small étale
site of the scheme of `U`.

It is `Stacks.Sheaves.ToposPullback.restrictionCommRingIso` — for a continuous functor of sites
the inverse image of a sheaf of commutative rings *is* its restriction — composed with the
equality `AlgebraicGeometry.SmallEtale.sheafPushforward_localizedRingedTopos_O`, which is why the
right-hand side below is already the structure sheaf and no further comparison appears.

**Universes.** They are supplied positionally, as
`AlgebraicGeometry.RingedToposHom.localizedPushforwardCommRingIso` has to supply them for the
same family: `Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor` takes its
`HasSheafCompose` hypotheses before the morphism of topoi that would determine the two sites, so
left to be inferred they are still metavariables when instance search runs, and the `UnivLE` side
conditions get stuck on `u =?= max (u + 1) ?u`.  The binder order is that of the
`universe ww ww' vv uu vv' uu'` command of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposCommRingImageAdjunction.lean`; the second
site's object universe has to be written `max (u + 1) u`; and the continuity instance is passed
explicitly, because `restrictionCommRingIso` asks for it while its functor argument is still a
metavariable. -/
def localizedStructureSheafIso :
    (inverseImageCommRingFunctor.{u, u, u, u + 1, u, max (u + 1) u}
          (localizedToposMorphism B S hS U)).obj
        (RingedTopos.localizedRingedTopos.{u, u + 1}
          (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
          (representableSheaf B S hS U)).O ≅
      (RingedSite.toRingedTopos
        (smallEtaleRingedSite B U.obj.left.obj U.obj.left.property)).O :=
  @restrictionCommRingIso.{u, u, u + 1, u, max (u + 1) u} _ _ _ _
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (RingedTopos.localizedRingedTopos.{u, u + 1}
      (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
      (representableSheaf B S hS U)).J
    _
    (toElementSite B S hS U)
    (isContinuous_toElementSite_localized B S hS U)
    (RingedTopos.localizedRingedTopos.{u, u + 1}
      (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
      (representableSheaf B S hS U)).O

/-- **Stacks 04IE for the small étale site, as a morphism of ringed topoi.** The small étale
ringed topos of the scheme of an object `U` of the small étale site of `S` is the localization of
the small étale ringed topos of `S` at the sheaf `U` represents — structure sheaves included.

The morphism of topoi is the identification of the two topoi, an equivalence; the structure map
is the adjunct of `AlgebraicGeometry.SmallEtale.localizedStructureSheafIso`, so it is an
isomorphism, and the two ringed topoi are identified and not merely compared. -/
@[stacks 04IE "for the small étale site, as a morphism of RINGED topoi: the small étale ringed
  topos of the scheme of an object `U` of the small étale site of `S` is the localization of the
  small étale ringed topos of `S` at the sheaf `U` represents, structure sheaves included.  The
  morphism of topoi is restriction along the functor of sites identifying the small étale site of
  the scheme of `U` with the site of elements of that sheaf, and the structure map is the adjunct
  of the comparison of the two structure sheaves, which is an isomorphism because the comparison
  is — the two structure sheaves being equal, both the restriction of the structure sheaf of `S`
  along post-composition with the structure morphism of `U`"]
def localizedRingedToposHom :
    RingedToposHom (RingedSite.toRingedTopos
        (smallEtaleRingedSite B U.obj.left.obj U.obj.left.property))
      (RingedTopos.localizedRingedTopos.{u, u + 1}
        (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
        (representableSheaf B S hS U)) where
  toToposHom := localizedToposMorphism B S hS U
  fSharp := (commRingImageAdjunction (localizedToposMorphism B S hS U)).homEquiv _ _
    (localizedStructureSheafIso B S hS U).hom

end AlgebraicGeometry.SmallEtale

end
