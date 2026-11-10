module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiToposMorphism
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.OpenMapFunctor

/-!
# Naturality of `u_{X/S}` in a change of divided power base

Let `X' ⊆ X` and `S' ⊆ S` be open subschemes with `X'` mapping into `S'`.  [Stacks, Tag 07KL]
asserts four things: that change of divided power base cuts out a fully faithful functor
`Cris(X'/S') ⥤ Cris(X/S)`, that this functor induces a morphism of crystalline topoi, that the
square
```
(X'/S')_cris  ⟶  (X/S)_cris
     |                 |
  u_{X'/S'}         u_{X/S}
     |                 |
     v                 v
 Sh(X'_Zar)    ⟶   Sh(X_Zar)
```
commutes, and that this square realizes a localization of morphisms of topoi in the sense of
[Stacks, Tag 04H1].  The first two are
`Crystalline.GlobalCrystallineSituation.smallChangeBaseFullyFaithful` and
`Crystalline.GlobalCrystallineSituation.smallChangeBaseMorphism`, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Functoriality.lean`.  This file proves the
third.

The content is the naturality of the forgetful functor `(U, T, δ) ↦ U` of [Stacks, Tag 07IH] in
the situation.  Change of base leaves the underlying divided power thickening untouched and only
composes the structure map `U ⟶ X'` with `X' ⟶ X`, so the open image of an object of
`Cris(X'/S')` inside `X` is the image under `X' ⟶ X` of its open image inside `X'`: the square
of *sites*
```
Cris(X'/S')  ⟶  Cris(X/S)
     |                |
  X'_Zar      ⟶    X_Zar
```
commutes on the nose, with bottom arrow the functor `V ↦ g(V)` of `IsOpenMap.functor` rather than
the preimage functor `Opens.map g`.  This is
`Crystalline.GlobalCrystallineSituation.smallChangeBase_comp_forgetToOpens`.

Three of the four functors in that square are cocontinuous and induce their morphisms of topoi
through `CategoryTheory.Functor.sheafPushforwardCocontinuous`, so the square of topoi follows by
the compositor and congruence of [Stacks, Tag 03L5].  The bottom one is the odd one out: the
morphism of small Zariski topoi `Sh(X'_Zar) ⟶ Sh(X_Zar)` of the library,
`StacksZariskiSite.opensMapMorphismOfTopoi`, is built from the *continuous* functor
`Opens.map g` in the other direction.  The two presentations agree, and that is [Stacks, Tag
00XQ]: `g(-)` is left adjoint to `g⁻¹(-)`, so the right Kan extension along `g(-)` is restriction
along `g⁻¹(-)` by [Stacks, Tag 00XX] (1).  This is
`StacksOpenMapSite.sheafPushforwardCocontinuousIsoOpensMap` below.

## Main definitions

* `StacksOpenMapSite.sheafPushforwardCocontinuousIsoOpensMap` — for an open continuous map
  `f : X ⟶ Y`, the sheaf pushforward along the cocontinuous image functor `V ↦ f(V)` is the sheaf
  pushforward along the continuous preimage functor `Opens.map f`, [Stacks, Tag 00XQ].
* `Crystalline.GlobalCrystallineSituation.smallChangeBaseZariskiSquare` — the square of topoi of
  [Stacks, Tag 07KL] commutes, as an invertible 2-morphism of topoi.

## Main results

* `Crystalline.GlobalCrystallineSituation.smallChangeBase_comp_forgetToOpens` — the square of
  sites commutes on the nose: forgetting the thickening and then taking images of opens along
  `X' ⟶ X` is change of divided power base followed by forgetting the thickening.

## Implementation notes

As everywhere in this tree, "the square commutes" is recorded as an isomorphism of the composite
*pushforwards*, an invertible 2-morphism of topoi in the sense of [Stacks, Tag 04IA], and not as
an equality of morphisms of topoi; compare
`Crystalline.GlobalCrystallineSituation.changeBaseStructureSquare` for the big site and
`Crystalline.GlobalCrystallineSituation.smallZariskiChangeBaseSquare` for the Zariski half.

Note the orientation of the variables: in `smallChangeBase S S' f g h` the situation `S` is the
*smaller* one `X'/S'` and `S'` is the ambient `X/S`, so `f : S.S ⟶ S'.S` is the inclusion
`S' ⟶ S` of divided power bases and `g : S.X ⟶ S'.X` the open immersion `X' ⟶ X`.

`StacksOpenMapSite.sheafPushforwardCocontinuousIsoOpensMap` is not tagged, the covering set of
[Stacks, Tag 00XQ] being already carried by
`StacksOpenMapSite.sheafPushforwardCocontinuousIsoTopPushforward` in
`StacksFrontier/CategoryTheory/Sites/Cocontinuous/OpenMapFunctor.lean`.  That declaration is stated
for sheaves of `Type u` on spaces in `TopCat.{u}` and against Mathlib's `TopCat.Sheaf.pushforward`;
the crystalline topoi are sheaves of `Type (u + 1)` on spaces in `TopCat.{u}` and the library's
small Zariski morphism is built from `Functor.sheafPushforwardContinuous`, so neither universe nor
target matches and the comparison is redone here for a general coefficient category.

The square proved here needs *less* than full faithfulness of the functor of
[Stacks, Tag 07KL] does: the only hypothesis used is that `X' ⟶ X` be an open immersion — in fact
only that its map of spaces be open, which is all that the bottom arrow and the site square see —
whereas `smallChangeBaseFullyFaithful` also needs `S' ⟶ S` to be an open immersion.

## What is and is not proved

Clause (c) of [Stacks, Tag 07KL], commutativity of the square, is proved, unconditionally in the
divided power base.  This supersedes the note in the module docstring of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Functoriality.lean` that the compatibility
of `u_{X/S}` with a change of divided power base "is not established".

Clause (d), that the square realizes a localization of morphisms of topoi as in
[Stacks, Tag 04H1], is **also proved**, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OpenSubobjectSlice.lean` and
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OpenSubobjectLocalization.lean`; the four
things it needs are listed below, and all four are proved.  The localization construction itself
is available — it is `MorphismOfTopoi.over` in
`StacksFrontier/CategoryTheory/Sites/SliceTopos/OverPushforward.lean`, with the two faces of its
square `MorphismOfTopoi.inverseImageCompToOverIso` and
`MorphismOfTopoi.toOverCompPushforwardIso` — and so is the slice presentation of a localized
topos, [Stacks, Tag 0791], whose equivalence `Sh(C/F) ≌ Sh(C)/F` and whose adjunction
`j_! ⊣ j^{-1}` are `CategoryTheory.Stacks.Topos.Localized.sheafEquivalence` and
`CategoryTheory.Stacks.Topos.Localized.shriekAdjunction` in
`StacksFrontier/CategoryTheory/Sites/Topos/LocalizationOfTopoi.lean`.  Writing `G` for the sheaf on
`X_Zar` represented by the open `X'` and `F = u_{X/S}^{-1} G`, the statement needs four things.

1. The sheaf `G` and the computation of `F`.  **Proved**, in
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OpenSubobject.lean`:
   `Crystalline.GlobalCrystallineSituation.opensReprSheaf` is `G`, and
   `Crystalline.GlobalCrystallineSituation.zariskiInverseImageOpensReprIso` identifies `F` with
   the restriction `(U, T, δ) ↦ G(U)` of `G` along the forgetful functor, the sheafification in
   `CategoryTheory.Functor.sheafPullbackCocontinuous` being trivial on it; the sections are
   `Crystalline.GlobalCrystallineSituation.nonempty_zariskiInverseImage_opensRepr_iff`.  This is
   not an instance of [Stacks, Tag 04D3], which is for a *continuous* functor.  What replaces the
   continuity of `forgetToOpens` — unavailable, for want of pullbacks in `Cris(X/S)` — is that
   `G` has subsingleton values, so that by
   `CategoryTheory.Precoverage.isSheaf_toGrothendieck_iff` only the pullbacks of the generating
   Zariski covering families have to be examined, and those are refined on ambient schemes.
   `Crystalline.GlobalCrystallineSituation.nonempty_zariskiInverseImage_opensRepr_iff_essImage`
   then identifies the objects of `Cris(X/S)` carrying a section of `F` with the essential image
   of change of divided power base, i.e. the site of elements of `F` with the full subcategory
   that `Cris(X'/S')` cuts out.
2. `Sh(X'_Zar) ≌ Sh(X_Zar)/G`, identifying the bottom arrow with the localization morphism `j_G`.
3. `(X'/S')_cris ≌ (X/S)_cris/F`, identifying the top arrow with `j_F`.

   These two are *the same statement twice*, and the obstruction to both is the same universe
   gap.  On each side the comparison functor is fully faithful with essential image the support
   of a subterminal sheaf: `IsOpenMap.functor` of `g` below, change of divided power base above,
   `G` below and `F` above.  But [Stacks, Tag 0791]
   (`CategoryTheory.Stacks.Topos.Localized.sheafEquivalence`) and its representable special case
   [Stacks, Tag 00Y1] (`CategoryTheory.OverShriek.sheafEquivalence`) are stated for sheaves of
   `Type v` with `v` the universe of the *morphisms* of the site — `u` for `Opens X` and for
   `Cris(X/S)`, whose objects are `Type (u + 1)` but whose homs are `Type u` — whereas both topoi
   of this square take values in `Type (u + 1)`.  For 0791 this is not only the statement:
   `CostructuredArrow yoneda F` does not typecheck for a `Type (u + 1)`-valued `F` at all
   (`CostructuredArrow uliftYoneda.{u + 1} F` does, and Mathlib's
   `CategoryTheory.CategoryOfElements.costructuredArrowULiftYonedaEquivalence` identifies it with
   the site of elements), and the body of 0791 rests on Mathlib's `OverPresheafAux` and
   `overEquivPresheafCostructuredArrow`, which exist only at `Type v`.  Nor can the gap be closed
   by transport: `uliftFunctor : Type u ⥤ Type (u + 1)` is fully faithful but essentially
   surjective only under `UnivLE.{u + 1, u}`, by `CategoryTheory.UnivLE_iff_essSurj`.

   What replaces 0791 here is that `G` — and hence `F` — is *subterminal*: its values are
   subsingletons.  The fibre `{t ∈ P(U) | φ(t) = s}` of a map `φ : P ⟶ F` is then all of `P(U)`,
   so the fibre functor of 0791 is plain restriction, `OverPresheafAux` is not needed, and the
   whole argument becomes universe-free.  **Both (2) and (3) are proved** on that
   replacement, `CategoryTheory.Stacks.Topos.Subterminal.sliceEquivalence` in
   `StacksFrontier/CategoryTheory/Sites/SliceTopos/SubterminalSliceSheaf.lean`: for a fully
   faithful continuous `j : D ⥤ C` whose essential image is the support of a subterminal sheaf
   `F` and whose covering sieves are exactly those whose image covers, `Sh(D) ≌ Sh(C)/F`.  The
   two instances are
   `Crystalline.GlobalCrystallineSituation.opensSliceEquivalence` and
   `Crystalline.GlobalCrystallineSituation.smallChangeBaseSliceEquivalence` in
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OpenSubobjectSlice.lean`, where
   `Crystalline.GlobalCrystallineSituation.zariskiInverseImageOpenSubobjectSheafIso` also
   identifies the sheaf used there with `u_{X/S}^{-1}G` in the sheafified spelling.

   Note that the bottom comparison is `IsOpenMap.functor` of `g`, not `Over.forget` of the open
   `g(X')`: that is the functor for which the square of sites already commutes on the nose, by
   `Crystalline.GlobalCrystallineSituation.smallChangeBase_comp_forgetToOpens`.  Its site-level
   inputs are in `StacksFrontier/CategoryTheory/Sites/OpenMapFunctorSubsite.lean`; those for change
   of divided power base are `smallChangeBase_coverPreserving` in
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ChangeBaseCoverPreserving.lean`, which
   with `smallChangeBase_isCocontinuous` gives the topology correspondence, and the four
   hypotheses assembled in
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OpenSubobjectSite.lean`.

   What (2) and (3) do not themselves record is the identification of the two horizontal arrows
   with the localization morphisms `j_G` and `j_F`, i.e. the adjunction `j_! ⊣ j^{-1}` that
   `CategoryTheory.Stacks.Topos.Localized.shriekAdjunction` records for 0791.  For the
   subterminal equivalence that is `sliceEquivalence.functor ⋙ Over.forget ⊣ sliceRestriction`,
   and it is `CategoryTheory.Stacks.Topos.Subterminal.shriekAdjunction` in
   `StacksFrontier/CategoryTheory/Sites/SliceTopos/SubterminalSliceShriek.lean`; the two instances
   are `Crystalline.GlobalCrystallineSituation.opensShriekAdjunction` and
   `Crystalline.GlobalCrystallineSituation.smallChangeBaseShriekAdjunction`, whose right
   adjoints are the inverse images of the two horizontal morphisms of topoi of the square
   itself.
4. That the resulting square *is* the square of 04H1.  **Proved**, as
   `Crystalline.GlobalCrystallineSituation.smallChangeBaseLocalizationSquare` in
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OpenSubobjectLocalization.lean`.
   `MorphismOfTopoi.over` of `u_{X/S}` at `G` has source `Over (u_{X/S}^{-1} G)` on the nose, so
   with `smallChangeBaseSliceEquivalence'` — the equivalence of (3) read at that object — the
   statement is an isomorphism
   `e_cris ⋙ (u_{X/S}.over G).pushforward ≅ u_{X'/S'}.pushforward ⋙ e_Zar` between the two
   composites, in the invertible-2-morphism idiom this tree uses everywhere.  It is proved by
   uniqueness of adjoints: both composites are right adjoints, and after cancelling the common
   `Over.forget G` their left adjoints are the two sides of clause (c) read on inverse images.
   `CategoryTheory.SliceTopos.underlyingIso_hom_app_comp_hom` ([Stacks, Tag 04IU]) in
   `StacksFrontier/CategoryTheory/Sites/SliceTopos/LocalizationAndMorphismsOfTopoi.lean` does not
   serve: it is stated for a *continuous* functor under `[HasFiniteLimits C]` and
   `[PreservesFiniteLimits u]`, hypotheses `Cris(X/S)` does not satisfy.

The *category* half of (3) is proved, and it is a statement-level constraint on the tag.  The site
of elements of `F` is the full subcategory of `Cris(X/S)` on the objects whose structure map lands
in `X'`, so (3) asks for change of divided power base to be *essentially surjective* onto that
subcategory, not merely fully faithful.  That is
`Crystalline.GlobalCrystallineSituation.smallChangeBase_essImage_iff` in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Functoriality.lean`, and it carries a
hypothesis the rest of this file does not: at the bare generality of `smallChangeBase` clause (d)
is false, because an object `(U, T, δ)` of `Cris(X/S)` with `U ⟶ X` landing in `X'` has `T ⟶ S`
landing in `S'` — the immersion `U ↪ T` being surjective on points — but the resulting
factorization `T ⟶ S'` is a morphism of divided power schemes only when the divided power
structure of `S'` is induced from that of `S`.  The hypothesis expressing that is
`Crystalline.DividedPowerScheme.IsInducedOpen` in
`StacksFrontier/AlgebraicGeometry/Crystalline/DividedPowerGluing.lean`, an open immersion whose
source ideal is induced from the target's, whose `inducedOpenLift` supplies the factorization.
`Crystalline.GlobalCrystallineSituation.nonempty_zariskiInverseImage_opensRepr_iff_essImage` keeps
that hypothesis, and so must anything proving (3).

## References

* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07IL](https://stacks.math.columbia.edu/tag/07IL)
* [Stacks Project, Tag 07IH](https://stacks.math.columbia.edu/tag/07IH)
* [Stacks Project, Tag 00XQ](https://stacks.math.columbia.edu/tag/00XQ)
* [Stacks Project, Tag 00XX](https://stacks.math.columbia.edu/tag/00XX)
* [Stacks Project, Tag 03L5](https://stacks.math.columbia.edu/tag/03L5)
* [Stacks Project, Tag 04H1](https://stacks.math.columbia.edu/tag/04H1)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
* [Stacks Project, Tag 04D3](https://stacks.math.columbia.edu/tag/04D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe w w' u

namespace StacksOpenMapSite

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f) (A : Type w) [Category.{w'} A]

/-- **The two presentations of the morphism of small Zariski topoi attached to an open continuous
map agree**, [Stacks, Tag 00XQ].  The sheaf pushforward along the cocontinuous image functor
`v : V ↦ f(V)` of `IsOpenMap.functor` is the sheaf pushforward along the continuous preimage
functor `u = Opens.map f`, that is, the topological `f_*`.

The image functor is left adjoint to the preimage functor, `IsOpenMap.adjunction`, so the right
Kan extension `{}_s v` along `v` is plain restriction `u^p` along `u`; this is [Stacks, Tag 00XX]
(1), available as `CategoryTheory.Functor.sheafPushforwardCocontinuousIsoRestriction`.  The two
sheaf functors are then compared through the fully faithful inclusion of sheaves into presheaves.

This is the form of `StacksOpenMapSite.sheafPushforwardCocontinuousIsoTopPushforward` needed for
sheaves whose coefficients do not lie in the universe of the spaces, and it lands in
`CategoryTheory.Functor.sheafPushforwardContinuous` rather than in `TopCat.Sheaf.pushforward`. -/
@[sga "4 III 2.5" "special case", sga "4 III 2.7" "Φ_* ≅ (i^{-1})_s"]
def sheafPushforwardCocontinuousIsoOpensMap
    [∀ P : (Opens X)ᵒᵖ ⥤ A, (IsOpenMap.functor hf).op.HasPointwiseRightKanExtension P] :
    haveI := isCocontinuous_isOpenMapFunctor hf
    (IsOpenMap.functor hf).sheafPushforwardCocontinuous A (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology Y) ≅
      (Opens.map f).sheafPushforwardContinuous A (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X) :=
  haveI := isCocontinuous_isOpenMapFunctor hf
  Functor.fullyFaithfulCancelRight (sheafToPresheaf (Opens.grothendieckTopology Y) A)
    ((Functor.sheafPushforwardCocontinuousIsoRestriction A (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology Y) hf.adjunction).trans
      ((Opens.map f).sheafPushforwardContinuousCompSheafToPresheafIso A
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).symm)

end StacksOpenMapSite

namespace Crystalline.GlobalCrystallineSituation

variable {S S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}
  [IsOpenImmersion g]

/-- **The square of sites underlying [Stacks, Tag 07KL] commutes on the nose.**  Forgetting the
divided power thickening of an object of `Cris(X'/S')` and then taking the image of the resulting
open of `X'` under `X' ⟶ X` is the same as changing the divided power base first and forgetting
afterwards.

Both routes send `(U, T, δ)` to the open image of `U ⟶ X' ⟶ X`: change of base leaves the
thickening untouched and replaces the structure map `U ⟶ X'` by its composite with `g`, and the
image of the range of a map is the range of its composite with that map.  The morphism components
need no checking, the opens of a space forming a partial order. -/
theorem smallChangeBase_comp_forgetToOpens (hg : IsOpenMap g.base) :
    forgetToOpens S ⋙ IsOpenMap.functor hg = smallChangeBase S S' f g h ⋙ forgetToOpens S' := by
  refine CategoryTheory.Functor.ext (fun A ↦ TopologicalSpace.Opens.ext (Set.ext fun x ↦ ?_))
    fun A B k ↦ Subsingleton.elim _ _
  have key : ∀ y : A.obj.thickening.source,
      ((changeBase S S' f g h).obj A.obj).toX.base y = g.base (A.obj.toX.base y) := fun y ↦ by
    rw [changeBase_obj_toX]
    exact Scheme.Hom.comp_apply _ _ y
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, key z⟩
  · rintro ⟨z, rfl⟩
    exact ⟨A.obj.toX.base z, ⟨z, rfl⟩, (key z).symm⟩

/-- **Stacks Project, Tag 07KL, clause (c).**  The square formed by the morphism of crystalline
topoi `(X'/S')_cris ⟶ (X/S)_cris` of change of divided power base, the comparisons `u_{X'/S'}` and
`u_{X/S}` of [Stacks, Tag 07IL] with the small Zariski topoi, and the morphism of small Zariski
topoi `Sh(X'_Zar) ⟶ Sh(X_Zar)` along `X' ⟶ X`, commutes: the two composites agree as morphisms of
topoi, recorded as an invertible 2-morphism between their direct images.

The square of sites commutes on the nose by
`Crystalline.GlobalCrystallineSituation.smallChangeBase_comp_forgetToOpens`, with the image functor
`V ↦ g(V)` along the bottom; the three cocontinuous functors contribute the compositor and
congruence of [Stacks, Tag 03L5], and the identification of the bottom arrow with the library's
morphism of small Zariski topoi is [Stacks, Tag 00XQ], in the form
`StacksOpenMapSite.sheafPushforwardCocontinuousIsoOpensMap`.

No hypothesis on the morphism `f` of divided power bases is needed, and of `g` only that it be an
open immersion — indeed only that its map of spaces be open. -/
@[stacks 07KL "clause (c): the square formed with u_{X'/S'} and u_{X/S} commutes, as an invertible
  2-morphism of topoi.  Clause (d), that this square realizes a localization of morphisms of
  topoi as in Stacks 04H1, is covered elsewhere: the two topos-level identifications by
  opensSliceEquivalence and smallChangeBaseSliceEquivalence in SmallSite/OpenSubobjectSlice.lean,
  and in SmallSite/OpenSubobjectLocalization.lean the identification of the two horizontal
  arrows with the localization morphisms j_G and j_F (opensShriekAdjunction,
  smallChangeBaseShriekAdjunction) and the commutativity of the resulting square
  (smallChangeBaseLocalizationSquare)"]
def smallChangeBaseZariskiSquare (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] :
    ((StacksZariskiSite.opensMapMorphismOfTopoi g.base).comp
        (zariskiToposMorphism S)).pushforward ≅
      ((zariskiToposMorphism S').comp (smallChangeBaseMorphism S S' f g h)).pushforward :=
  haveI hg : IsOpenMap g.base := g.isOpenEmbedding.isOpenMap
  haveI := StacksOpenMapSite.isCocontinuous_isOpenMapFunctor hg
  haveI : (forgetToOpens S ⋙ IsOpenMap.functor hg).IsCocontinuous (smallTopology S)
      (Opens.grothendieckTopology S'.X.carrier) :=
    CategoryTheory.isCocontinuous_comp _ _ _ (Opens.grothendieckTopology S.X.carrier)
  haveI : (smallChangeBase S S' f g h ⋙ forgetToOpens S').IsCocontinuous (smallTopology S)
      (Opens.grothendieckTopology S'.X.carrier) :=
    CategoryTheory.isCocontinuous_comp _ _ _ (smallTopology S')
  Functor.isoWhiskerLeft
      ((forgetToOpens S).sheafPushforwardCocontinuous (Type (u + 1)) (smallTopology S)
        (Opens.grothendieckTopology S.X.carrier))
      (StacksOpenMapSite.sheafPushforwardCocontinuousIsoOpensMap hg (Type (u + 1))).symm ≪≫
    (Functor.sheafPushforwardCocontinuousComp (Type (u + 1)) (smallTopology S)
      (Opens.grothendieckTopology S.X.carrier) (Opens.grothendieckTopology S'.X.carrier)
      (forgetToOpens S) (IsOpenMap.functor hg)).symm ≪≫
    Functor.sheafPushforwardCocontinuousCongr (Type (u + 1)) (smallTopology S)
      (Opens.grothendieckTopology S'.X.carrier) (forgetToOpens S ⋙ IsOpenMap.functor hg)
      (smallChangeBase S S' f g h ⋙ forgetToOpens S')
      (smallChangeBase_comp_forgetToOpens hg) ≪≫
    Functor.sheafPushforwardCocontinuousComp (Type (u + 1)) (smallTopology S) (smallTopology S')
      (Opens.grothendieckTopology S'.X.carrier) (smallChangeBase S S' f g h) (forgetToOpens S')

end Crystalline.GlobalCrystallineSituation

end
