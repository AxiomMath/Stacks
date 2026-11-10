module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleInverseImageReflectsZero
public import StacksFrontier.AlgebraicGeometry.Etale.SmallEtalePostcompose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.ZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.OpenEqualityLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ExistenceClause
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.SmallEtaleElementSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubterminalSheaves
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizationOfIso
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposMorphismLocalization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.OpenEqualityLocusSupplement

/-!
# Restricting a morphism of small étale ringed topoi to a pair of opens

Let `X` and `Y` be schemes of a big étale site and let
`(g, g^♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of ringed topoi between
their small étale ringed topoi.  For an open subscheme `V` of `Y`, Stacks 04IF localizes `g` at
the sheaf `h_V^#` represented by `V`: it produces a morphism of ringed topoi from the
localization of `(Sh(X_étale), 𝒪_X)` at `g⁻¹h_V^#` to the localization of
`(Sh(Y_étale), 𝒪_Y)` at `h_V^#`.  That is the *restriction of `g` to a pair of opens* of the
Zariski gluing in the proof of Stacks 04I7, and this module states it at the universes of the
small étale ringed topos.

## Main definitions

* `AlgebraicGeometry.localizedOverOpen`: **Stacks 04IF** at these universes — the restriction of
  `g` to the localizations at `h_V^#` and at `g⁻¹h_V^#`.
* `AlgebraicGeometry.inverseImageOpenLocalizedToposEquivalence`: the source of that restriction
  is the localization at the open subscheme `AlgebraicGeometry.inverseImageOpen` of `X`.
* `AlgebraicGeometry.SmallEtale.localizationSheafEquivalence`: the small étale topos of an object
  `U` of the small étale site of `S` is the topos of the slice of that site at `U`.
* `AlgebraicGeometry.SmallEtale.localizedToposEquivalence` and `.openLocalizedToposEquivalence`:
  **Stacks 04IE for the small étale site** — the small étale topos of `U`, and of an open
  subscheme `V` of `S`, is the topos of the localization of the small étale ringed topos of `S`
  at the sheaf it represents.
* `AlgebraicGeometry.SmallEtale.openRepresentableSheafIsoYoneda`,
  `.openRepresentableSheafIso` and `.openRepresentableLocalizedToposEquivalence`: the same at the
  `AlgebraicGeometry.openRepresentable'` spelling of that sheaf, which is the spelling Stacks
  04IF's half uses.
* `AlgebraicGeometry.SmallEtale.openLocalizedRingedToposHom`: **Stacks 04IE for an open
  subscheme as a morphism of ringed topoi**, at that spelling — with which input (1) of the
  Zariski gluing of Stacks 04I7 is closed.

## Implementation notes

That Stacks 04IF *applies* here is the content of `localizedOverOpen`, and it did not until the
localization tower of `StacksFrontier/CategoryTheory/Sites/Modules/Localization/` was given an
independent universe for the objects of the site.  The small étale ringed site of a scheme is a
`AlgebraicGeometry.RingedSite.{u + 1, u, u}` — its objects are of `Type (u + 1)` while its
morphisms and the sections of its structure sheaf are of `Type u` — so its ringed topos is a
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`, whereas
`AlgebraicGeometry.RingedToposHom.localized` was stated for `RingedTopos.{u, u, u}`.  It is now
stated for `X Y : RingedTopos.{v, u, v}` with `[EssentiallySmall.{v} X.C]` and
`[EssentiallySmall.{v} Y.C]`, the localizations landing in `RingedTopos.{v, max u v, v}`; that
hypothesis is what buys the direct image of a localization whose site of elements lies above
its sections, and for the small étale site it is discharged by the instance
`AlgebraicGeometry.SmallEtale.essentiallySmall`.  So the definition below carries no hypothesis
of its own: `g` and `V` are its only data, exactly as in Stacks 04IF.

**Stacks 04IE for the étale site does not need the ringed-site localization.** The two halves of
the identification sought here are
`AlgebraicGeometry.SmallEtale.localizationEquivalence` — the small étale site of an object `U` of
the small étale site of `S` is the slice `(S_étale)/U` — and Stacks 00Y1,
`CategoryTheory.OverShriek.sheafEquivalence`, which carries the topos of a slice site to the
slice of the topos at the represented sheaf; the third step, from the slice of the topos to the
localization at the sheaf, is `AlgebraicGeometry.RingedTopos.localizationEquivalence`, already
stated at `RingedTopos.{v, u, v}`.  All three have the universe of the site objects free, so
`localizedToposEquivalence` is formed at the sections universe `u` of the small étale ringed
topos directly.  The two conditions Stacks 00Y1 asks of the site at that universe are the
instances `AlgebraicGeometry.SmallEtale.hasSheafify_type'` and
`AlgebraicGeometry.SmallEtale.wEqualsLocallyBijective_type`, both supplied by essential
smallness of the site one universe below Mathlib's unconditional ones; the second is why
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleInverseImageReflectsZero.lean`
is imported.  What is *not* available at these universes is the bundled form of the first two,
`AlgebraicGeometry.RingedSite.representableLocalizationEquivalence`: it is stated over
`AlgebraicGeometry.RingedSite.ringedTopos`, which is itself stated for
`X : RingedSite.{u, v, max u v w}`, so a small étale ringed site would need
`max (u + 1) v w = u`.  What forces that is the *ringed-site* localization, whose morphism of
topoi `AlgebraicGeometry.RingedSite.overMorphismOfTopoi` is stated with its topoi at
`Type (max u v w)` because the right Kan extension computing its direct image is a limit indexed
by structured arrows over `Over U`.  That is the same obstruction `[EssentiallySmall.{v} X.C]`
removed for the ringed-*topos* localization, and removing it here would be the same
generalization applied to the ringed-site tower; it is not done here, and nothing above needs it.

**The two spellings of the represented sheaf are reconciled.**  Stacks 04IE as formed here
localizes at the sheafification of `yoneda.obj U` for `U` an object of the small étale site,
whereas Stacks 04IF's half and `AlgebraicGeometry.inverseImageOpen` localize at the
sheafification of `AlgebraicGeometry.openRepresentable'`, the restriction to the small étale site
of the presheaf the open represents in the big étale slice, with its sections raised by
`CategoryTheory.uliftYoneda`.  `AlgebraicGeometry.SmallEtale.openRepresentableSheafIsoYoneda`
identifies them and
`AlgebraicGeometry.SmallEtale.openRepresentableLocalizedToposEquivalence` is 04IE stated at the
second spelling, so the two halves now meet.  The construction was already in the tree and is
not duplicated: `AlgebraicGeometry.SmallEtale.representablePresheafIso` and
`.openRepresentableIso` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/OpenEqualityLocus.lean` were `private` and stated
at the sections universe `max (u + 1) v`; they are now public with their sections universe free,
and the private functor they were stated over has been replaced by the already-public
`AlgebraicGeometry.SmallEtale.toOver`, of which it was a second copy.

**Input (1) of the Zariski gluing of Stacks 04I7 is closed here.**  Stacks 04IE is identified on
the topoi by the three declarations above and as a morphism of **ringed** topoi by
`AlgebraicGeometry.SmallEtale.openLocalizedRingedToposHom`, at the
`AlgebraicGeometry.openRepresentable'` spelling of the represented sheaf — which is the spelling
Stacks 04IF's half, `AlgebraicGeometry.localizedOverOpen`, localizes at.

The structure-sheaf comparison that made this possible was once called cheap in these notes on
the ground that `AlgebraicGeometry.SmallEtale.commRingStructurePresheaf` is
`(SmallEtale.toScheme B S hS).op ⋙ Scheme.Γ` and `AlgebraicGeometry.SmallEtale.postcompose`
leaves the underlying scheme of an object alone.  That was true of the *presheaf identity* and
was not the whole of the comparison, because the identification of the topoi formed above goes
through Stacks 00Y1, whose functor is a lower shriek, so moving a sheaf of commutative rings
across it is an inverse image and not a restriction.  The fix was to identify the two topoi *by
restriction along a functor of sites* instead, which the small étale site allows and a general
site does not — its topology is subcanonical, so a section of `h_U` over `T` is a morphism
`T ⟶ U` and the site of elements of `h_U` *is* the slice `(S_étale)/U`.  That is
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/SmallEtaleElementSite.lean`,
where the comparison is then the cheap presheaf identity and an *equality*; and moving the result
between the two spellings of the sheaf, again as a morphism of ringed topoi, is
`AlgebraicGeometry.RingedTopos.localizedRingedToposHomOfIso`, built the same way.

What this does *not* close is the rest of Stacks 04I7's existence clause.  Inputs (2) and (3) of
the gluing — the existence clause of Stacks 04I6 over affine charts of the two opens, which is
steps (3) and (4) of 04I6's proof and carries that tag, and the gluing of the 2-isomorphisms,
which rests on (1) and (2) — are untouched; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/ExistenceClause.lean`.

## References

* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- **Stacks 04IF for the small étale ringed topoi: the restriction of a morphism of ringed
topoi to a pair of opens.**

For schemes `X` and `Y` of a big étale site, a morphism of ringed topoi
`g : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` and an open subscheme `V` of `Y`, this is the
localization of `g` at the sheaf `h_V^#` represented by `V`: the morphism of ringed topoi
```
  (Sh(X_étale)/g⁻¹h_V^#, (𝒪_X)_{g⁻¹h_V^#}) ⟶ (Sh(Y_étale)/h_V^#, (𝒪_Y)_{h_V^#})
```
of Stacks 04IF, whose inverse image is `(H ⟶ h_V^#) ↦ (g⁻¹H ⟶ g⁻¹h_V^#)`.

It carries no hypothesis beyond `g` and `V`: the essential smallness of the small étale site
that Stacks 04IF's localization needs is the instance
`AlgebraicGeometry.SmallEtale.essentiallySmall`.  This is the first input of the Zariski gluing
in the proof of Stacks 04I7; the identification of the source with the small étale ringed topos
of the open subscheme of `X` representing `g⁻¹h_V^#` is Stacks 04IE for the étale site and is
not carried here, so this is not yet that gluing's input in full. -/
@[stacks 04IF "the localization of a morphism of ringed topoi at the sheaf represented by an
  open subscheme `V` of the target, for the small étale ringed topoi of two schemes: the
  morphism of ringed topoi from the localization of the source at the inverse image of that
  sheaf to the localization of the target at it, with the structure map of 04IF.  This is the
  instance of 04IF at `RingedTopos.{u, u + 1, u}`, the universes of the small étale ringed
  topos, which is what the Zariski gluing of 04I7 restricts along; it is *not* a morphism
  between the small étale ringed topoi of two open subschemes, that identification being 04IE
  for the étale site, which is not carried"]
def localizedOverOpen (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (V : Y.obj.Opens) :
    RingedToposHom
      ((RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).localizedRingedTopos
        (g.toToposHom.inverseImage.obj
          ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).obj
            (openRepresentable'.{u, u} B Y.obj Y.property V))))
      ((RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)).localizedRingedTopos
        ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).obj
          (openRepresentable'.{u, u} B Y.obj Y.property V))) :=
  g.localized ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).obj
    (openRepresentable'.{u, u} B Y.obj Y.property V))

/-! ### The source of the restriction is the localization at an open of the source -/

/-- **The source of `AlgebraicGeometry.localizedOverOpen` is the localization at an open
subscheme of the source.** The restriction of `g` of Stacks 04IF localizes the small étale ringed
topos of `X` at `g⁻¹h_V^#`, and `AlgebraicGeometry.inverseImageOpen` is the unique open `W` of
`X` with `g⁻¹h_V^# ≅ h_W^#`; this moves the localization from the one spelling to the other.

It carries no hypothesis beyond `g` and `V`. The isomorphism
`AlgebraicGeometry.nonempty_iso_inverseImageOpen` supplies is only `Nonempty`, but it is
*unique* where it exists, both of its sides being subterminal objects
(`AlgebraicGeometry.isSubterminal_inverseImage_openRepresentableSheaf` and
`AlgebraicGeometry.isSubterminal_openRepresentableSheaf`) and
`CategoryTheory.IsSubterminal` asserting exactly that any two morphisms into the object are
equal; so choosing it is not a choice, and no hypothesis has to be carried to get hold of it.
The transport itself is `AlgebraicGeometry.RingedTopos.localizedToposEquivalenceOfIso`.

This is the source half of input (1) of the Zariski gluing of Stacks 04I7. Joining it to
`AlgebraicGeometry.SmallEtale.openLocalizedToposEquivalence`, and so to the small étale topos of
`W` itself, needs the comparison of `AlgebraicGeometry.openRepresentable'` with the presheaf `W`
represents in the small étale site; see this module's implementation notes. -/
def inverseImageOpenLocalizedToposEquivalence (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (V : Y.obj.Opens) :
    ((RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).localizedRingedTopos
        (g.toToposHom.inverseImage.obj
          ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).obj
            (openRepresentable'.{u, u} B Y.obj Y.property V)))).Topos ≌
      ((RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).localizedRingedTopos
        ((presheafToSheaf (SmallEtale.topology B X.obj X.property) (Type u)).obj
          (openRepresentable'.{u, u} B X.obj X.property
            (inverseImageOpen B X Y g V)))).Topos :=
  RingedTopos.localizedToposEquivalenceOfIso _
    (nonempty_iso_inverseImageOpen B X Y g V).some

/-! ### Stacks 04IE for the small étale site -/

namespace SmallEtale

variable (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS)

/-- **`Type u` has limits of the shape of the structured-arrow categories over the localization
equivalence.** This is the size hypothesis of
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`, and here it is free of any size argument:
`AlgebraicGeometry.SmallEtale.localizationEquivalence` is an *equivalence*, so each
`StructuredArrow T e.functor.op` has an initial object, and a category with an initial object
has all limits in any category.

It serves `AlgebraicGeometry.SmallEtale.localizationSheafEquivalence`, where without it the
limits would have to be taken over a shape built from the objects of the small étale site, of
`Type (u + 1)`, in `Type u`. -/
theorem hasLimitsOfShape_structuredArrow_localizationEquivalence (T : (Over U)ᵒᵖ) :
    HasLimitsOfShape
      (StructuredArrow T (SmallEtale.localizationEquivalence B S hS U).functor.op) (Type u) :=
  have := (mkInitialOfLeftAdjoint (SmallEtale.localizationEquivalence B S hS U).functor.op
    (SmallEtale.localizationEquivalence B S hS U).op.symm.toAdjunction T).hasInitial
  ⟨fun _ => inferInstance⟩

/-- **The small étale topos of an object `U` of the small étale site of `S` is the topos of the
slice of that site at `U`.** This is the sheaf-level form of
`AlgebraicGeometry.SmallEtale.localizationEquivalence`, the equivalence of *sites* between the
small étale site of the scheme of `U` and the slice `(S_étale)/U`: that equivalence is a dense
subsite inclusion for the two topologies
(`AlgebraicGeometry.SmallEtale.isDenseSubsite_localizationEquivalence_functor`, which rests on
`AlgebraicGeometry.SmallEtale.localizationEquivalence_topology`), so restriction along it is an
equivalence of sheaf categories by Stacks 03A0.

Sections are taken in the universe `u` of the sections of the small étale ringed topos, one
below the universe of the objects of the site; nothing about the comparison needs them higher,
the only size condition being
`hasLimitsOfShape_structuredArrow_localizationEquivalence`. -/
noncomputable def localizationSheafEquivalence :
    Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property) (Type u) ≌
      Sheaf ((SmallEtale.topology B S hS).over U) (Type u) :=
  have := hasLimitsOfShape_structuredArrow_localizationEquivalence B S hS U
  Functor.IsDenseSubsite.sheafEquiv
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    ((SmallEtale.topology B S hS).over U)
    (SmallEtale.localizationEquivalence B S hS U).functor (Type u)

/-- **Stacks 04IE for the small étale site: the small étale topos of an object `U` of the small
étale site of `S` is the localization of the small étale topos of `S` at the sheaf `h_U^#`.**

The three steps of the identification are each proved elsewhere and none of them is rebuilt here.
The small étale site of the scheme of `U` is the slice `(S_étale)/U`, so their topoi agree
(`AlgebraicGeometry.SmallEtale.localizationSheafEquivalence`, which is
`AlgebraicGeometry.SmallEtale.localizationEquivalence` read on sheaves); the topos of a slice
site is the slice of the topos at the represented sheaf, which is Stacks 00Y1
(`CategoryTheory.OverShriek.sheafEquivalence`); and the slice of a topos at a sheaf is the
localization of the ringed topos at that sheaf, which is Stacks 04IE in the generality it is
formalized in (`AlgebraicGeometry.RingedTopos.localizationEquivalence`).

What this is *not*: an identification of **ringed** topoi. It identifies the two topoi only.
Upgrading it needs the comparison of the two structure sheaves — the structure sheaf of the
localization is the restriction of `𝒪_S` along the projection from the site of elements of
`h_U^#`, and the structure sheaf of the small étale site of the scheme of `U` is its own sheaf
of global functions — and that comparison is not carried here. -/
@[stacks 04IE "for the small étale site: the topos of the small étale site of an object `U` of
  the small étale site of `S` is the topos of the localization of the small étale ringed topos
  of `S` at the sheaf represented by `U`.  This form identifies the two topoi; the identification
  of the two RINGED topoi, structure sheaves included, is
  `AlgebraicGeometry.SmallEtale.localizedRingedToposHom`.  It is the composite of three
  equivalences: the equivalence of sites
  between the small étale site of the scheme of `U` and the slice of the small étale site of `S`
  at `U`, read on sheaves; Stacks 00Y1 for the slice site; and the equivalence of the
  localization at a sheaf with the slice of the topos"]
noncomputable def localizedToposEquivalence :
    Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property) (Type u) ≌
      (RingedTopos.localizedRingedTopos
        (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
        ((presheafToSheaf (SmallEtale.topology B S hS) (Type u)).obj (yoneda.obj U))).Topos :=
  (localizationSheafEquivalence B S hS U).trans
    ((CategoryTheory.OverShriek.sheafEquivalence (U := U) (SmallEtale.topology B S hS)).trans
      (RingedTopos.localizationEquivalence
        (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
        ((presheafToSheaf (SmallEtale.topology B S hS) (Type u)).obj (yoneda.obj U))).symm)

/-- **Stacks 04IE for an open subscheme: the small étale topos of an open subscheme `V` of `S`
is the localization of the small étale topos of `S` at the sheaf represented by `V`.**

This is `AlgebraicGeometry.SmallEtale.localizedToposEquivalence` at the object
`AlgebraicGeometry.opensToBoundedEtale B S hS V` of the small étale site, the open subscheme `V`
regarded as étale over `S` — the composite of that functor with
`AlgebraicGeometry.SmallEtale.localizationEquivalence`, which is the identification the Zariski
gluing of Stacks 04I7 restricts along.

The sheaf it localizes at is `h_V^#` for `V` read in the small étale site. It is **not** stated
here to agree with `AlgebraicGeometry.openRepresentable'`, which spells the same idea as the
restriction to the small étale site of the presheaf `V` represents in the big étale slice, with
its sections raised by `CategoryTheory.uliftYoneda`; identifying the two is a separate
comparison and is not carried. -/
@[stacks 04IE "for an open subscheme: the topos of the small étale site of an open subscheme `V`
  of `S` is the topos of the localization of the small étale ringed topos of `S` at the sheaf
  represented by `V` regarded as étale over `S`.  This is the composite of
  `AlgebraicGeometry.opensToBoundedEtale` with the identification of the small étale site of an
  object with the slice over it.  The sheaf localized at is the one `V` represents in the small
  étale site; that it agrees with `AlgebraicGeometry.openRepresentable'` is
  `AlgebraicGeometry.SmallEtale.openRepresentableSheafIsoYoneda`, and the identification of the
  two RINGED topoi at that spelling is
  `AlgebraicGeometry.SmallEtale.openLocalizedRingedToposHom`", sga "4 VIII 6.2" "partial"]
noncomputable def openLocalizedToposEquivalence (V : S.Opens) :
    Sheaf (SmallEtale.topology B V.toScheme
        (Scheme.size_lt_of_isOpenImmersion V.ι hS)) (Type u) ≌
      (RingedTopos.localizedRingedTopos
        (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
        ((presheafToSheaf (SmallEtale.topology B S hS) (Type u)).obj
          (yoneda.obj ((opensToBoundedEtale B S hS).obj V)))).Topos :=
  localizedToposEquivalence B S hS ((opensToBoundedEtale B S hS).obj V)


/-- **The sheaf an open subscheme represents in the small étale site, in the two spellings the
two halves of Stacks 04IE use.**

`AlgebraicGeometry.openRepresentable'` is the restriction to the small étale site of the presheaf
`V` represents in the big étale slice over `S`, with its sections lifted by
`CategoryTheory.uliftYoneda`; `yoneda.obj ((opensToBoundedEtale B S hS).obj V)` is the presheaf
`V` represents in the small étale site itself.  They are isomorphic by
`AlgebraicGeometry.SmallEtale.openRepresentableIso`, which is full faithfulness of
`AlgebraicGeometry.SmallEtale.toOver`, followed by `CategoryTheory.uliftYonedaIsoYoneda`, which
removes the lift because here it is taken at the morphism universe of the site; sheafifying gives
the statement.

It exists because the two halves of input (1) of the Zariski gluing of Stacks 04I7 localize at
the two spellings: `AlgebraicGeometry.localizedOverOpen` and
`AlgebraicGeometry.inverseImageOpen` at the first,
`AlgebraicGeometry.SmallEtale.openLocalizedToposEquivalence` at the second. -/
def openRepresentableSheafIsoYoneda (V : S.Opens) :
    (presheafToSheaf (SmallEtale.topology B S hS) (Type u)).obj
        (openRepresentable'.{u, u} B S hS V) ≅
      (presheafToSheaf (SmallEtale.topology B S hS) (Type u)).obj
        (yoneda.obj ((opensToBoundedEtale B S hS).obj V)) :=
  (presheafToSheaf (SmallEtale.topology B S hS) (Type u)).mapIso
    (SmallEtale.openRepresentableIso.{u, u} B S hS V ≪≫
      uliftYonedaIsoYoneda.app ((opensToBoundedEtale B S hS).obj V))

/-- **Stacks 04IE for an open subscheme, at the `AlgebraicGeometry.openRepresentable'`
spelling of the sheaf it localizes at.**

This is `AlgebraicGeometry.SmallEtale.openLocalizedToposEquivalence` moved along
`AlgebraicGeometry.SmallEtale.openRepresentableSheafIsoYoneda` by
`AlgebraicGeometry.RingedTopos.localizedToposEquivalenceOfIso`, and it is the form in which
Stacks 04IE meets Stacks 04IF: the target of `AlgebraicGeometry.localizedOverOpen` and the
source `AlgebraicGeometry.inverseImageOpenLocalizedToposEquivalence` produces are both
localizations at the sheafification of `AlgebraicGeometry.openRepresentable'`.

Still the two **topoi** only.  The morphism of ringed topoi of Stacks 04IF therefore composes
with these as a morphism of topoi and not yet as one of ringed topoi; what is missing is the
comparison of the two structure sheaves, and this module's implementation notes record what that
needs. -/
@[stacks 04IE "for an open subscheme `V` of `S`, with the sheaf localized at spelled as the
  sheafification of `AlgebraicGeometry.openRepresentable'`: the topos of the small étale site of
  `V` is the topos of the localization of the small étale ringed topos of `S` at that sheaf.
  This is `AlgebraicGeometry.SmallEtale.openLocalizedToposEquivalence` transported along the
  comparison of the two spellings of the represented sheaf; the identification of the two RINGED
  topoi at this spelling, structure sheaves included, is
  `AlgebraicGeometry.SmallEtale.openLocalizedRingedToposHom`"]
noncomputable def openRepresentableLocalizedToposEquivalence (V : S.Opens) :
    Sheaf (SmallEtale.topology B V.toScheme
        (Scheme.size_lt_of_isOpenImmersion V.ι hS)) (Type u) ≌
      (RingedTopos.localizedRingedTopos
        (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
        ((presheafToSheaf (SmallEtale.topology B S hS) (Type u)).obj
          (openRepresentable'.{u, u} B S hS V))).Topos :=
  (openLocalizedToposEquivalence B S hS V).trans
    (RingedTopos.localizedToposEquivalenceOfIso _
      (openRepresentableSheafIsoYoneda B S hS V).symm)

/-! ### Stacks 04IE for an open subscheme, as a morphism of ringed topoi -/

/-- **The sheaf an open subscheme represents, in the representable and the sheafification
spellings.** `AlgebraicGeometry.SmallEtale.representableSheaf` at
`AlgebraicGeometry.opensToBoundedEtale` of `V` is isomorphic to the sheafification of
`AlgebraicGeometry.openRepresentable'`: the sheafification counit at a sheaf is an isomorphism,
and `AlgebraicGeometry.SmallEtale.openRepresentableSheafIsoYoneda` identifies the two presheaves
after sheafification.

It exists to feed `AlgebraicGeometry.RingedTopos.localizedRingedToposHomOfIso`, which moves a
localization between two spellings of its sheaf as a morphism of *ringed* topoi. -/
def openRepresentableSheafIso (V : S.Opens) :
    representableSheaf B S hS ((opensToBoundedEtale B S hS).obj V) ≅
      (presheafToSheaf (SmallEtale.topology B S hS) (Type u)).obj
        (openRepresentable'.{u, u} B S hS V) :=
  (asIso ((sheafificationAdjunction (SmallEtale.topology B S hS) (Type u)).counit.app
      (representableSheaf B S hS ((opensToBoundedEtale B S hS).obj V)))).symm ≪≫
    (openRepresentableSheafIsoYoneda B S hS V).symm

/-- **Stacks 04IE for an open subscheme, as a morphism of ringed topoi, at the
`AlgebraicGeometry.openRepresentable'` spelling.** The small étale ringed topos of an open
subscheme `V` of `S` is the localization of the small étale ringed topos of `S` at the sheaf
`V` represents — structure sheaves included, and at the spelling of that sheaf which Stacks
04IF's half of input (1) of the Zariski gluing of Stacks 04I7 localizes at.

It is `AlgebraicGeometry.SmallEtale.localizedRingedToposHom`, which is Stacks 04IE at the
representable spelling, followed by
`AlgebraicGeometry.RingedTopos.localizedRingedToposHomOfIso` along
`AlgebraicGeometry.SmallEtale.openRepresentableSheafIso`.  With it, the target of
`AlgebraicGeometry.localizedOverOpen` and the source
`AlgebraicGeometry.inverseImageOpenLocalizedToposEquivalence` produces are both identified with
small étale ringed topoi of opens, as morphisms of ringed topoi, and input (1) is closed.

**Universes.** `AlgebraicGeometry.RingedToposHom.comp` elaborates its own nine universe
parameters before its arguments, and the three belonging to the source default to zero if left
to be inferred; they are supplied positionally, in the order
`comp.{Xv, Xu, Xw, Yv, Yu, Yw, Zv, Zu, Zw}` that `pp.universes` reports, with the two
localizations' object universe written `max (u + 1) u`.  Annotating the argument, `let`-binding
it with its type written out, and `by exact` all come too late. -/
@[stacks 04IE "for an open subscheme `V` of `S`, as a morphism of RINGED topoi and at the
  `AlgebraicGeometry.openRepresentable'` spelling of the sheaf: the small étale ringed topos of
  `V` IS the localization of the small étale ringed topos of `S` at the sheaf `V` represents,
  structure sheaves included.  It is 04IE at the representable spelling
  (`AlgebraicGeometry.SmallEtale.localizedRingedToposHom`, whose identification of the topoi is a
  restriction along a functor of sites, which is what makes the structure sheaves comparable)
  followed by the transport of a localization along an isomorphism of sheaves
  (`AlgebraicGeometry.RingedTopos.localizedRingedToposHomOfIso`).  This is the spelling Stacks
  04IF's half of input (1) of the Zariski gluing of 04I7 localizes at, so with it that input is
  closed"]
def openLocalizedRingedToposHom (V : S.Opens) :
    RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B V.toScheme
        (Scheme.size_lt_of_isOpenImmersion V.ι hS)))
      (RingedTopos.localizedRingedTopos.{u, u + 1}
        (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS))
        ((presheafToSheaf (SmallEtale.topology B S hS) (Type u)).obj
          (openRepresentable'.{u, u} B S hS V))) :=
  RingedToposHom.comp.{u, u + 1, u, u, max (u + 1) u, u, u, max (u + 1) u, u}
    (RingedTopos.localizedRingedToposHomOfIso.{u, u + 1} _ (openRepresentableSheafIso B S hS V))
    (SmallEtale.localizedRingedToposHom B S hS ((opensToBoundedEtale B S hS).obj V))

end SmallEtale

end AlgebraicGeometry

end
