module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChangeBaseZariski
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenSubobjectSlice
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.OverPushforward
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.SubterminalSliceShriek

/-!
# The square of [Stacks, Tag 07KL] is the localization square of [Stacks, Tag 04H1]

Let `X' ⊆ X` and `S' ⊆ S` be open subschemes with `X'` mapping into `S'`, let `G = h_{X'}` be the
sheaf on the small Zariski site of `X` represented by the open image of `X'`, and let
`F = u_{X/S}^{-1}G`.  Clause (d) of [Stacks, Tag 07KL] asserts that the commutative square
```
(X'/S')_cris  ⟶  (X/S)_cris
     |                 |
  u_{X'/S'}         u_{X/S}
     |                 |
     v                 v
 Sh(X'_Zar)    ⟶   Sh(X_Zar)
```
of `Crystalline.GlobalCrystallineSituation.smallChangeBaseZariskiSquare` is the square obtained
from `u_{X/S}` by the localization of [Stacks, Tag 04H1].  This file completes that clause.

`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OpenSubobjectSlice.lean` identifies the two
left-hand topoi with the slices: `opensSliceEquivalence` makes `Sh(X'_Zar)` the slice
`Sh(X_Zar)/G` and `smallChangeBaseSliceEquivalence` makes `(X'/S')_cris` the slice
`(X/S)_cris/F`.  What is added here is the two things that turn those identifications into the
assertion of clause (d).

*The horizontal arrows are the localization morphisms.*  The localization morphism `j_G` of
[Stacks, Tag 04H1] is the one whose `j_{G!}` is `Over.forget G` and whose `j_G^{-1}` is
restriction; so the content is an adjunction `e.functor ⋙ Over.forget ⊣ (-)^{-1}` on each side,
which is the last assertion of [Stacks, Tag 0791].  For the subterminal slice equivalence that
adjunction is `CategoryTheory.Stacks.Topos.Subterminal.shriekAdjunction`, and the two instances are
`opensShriekAdjunction` and `smallChangeBaseShriekAdjunction` below; the right adjoints are the
inverse images of the two horizontal morphisms of topoi of the square itself, not some
reconstruction of them.

*The square is the square of 04H1.*  `MorphismOfTopoi.over` of `u_{X/S}` at `G` has source
`Over (u_{X/S}^{-1}G)` on the nose, so `smallChangeBaseSliceEquivalence'` is the crystalline
equivalence read at that object, and `smallChangeBaseLocalizationSquare` is an isomorphism
between the two composites `(X'/S')_cris ⥤ Sh(X_Zar)/G`, in the invertible-2-morphism idiom this
tree uses everywhere.  It is proved by uniqueness of adjoints: both composites are right
adjoints, and their left adjoints agree because, after cancelling the common `Over.forget G`,
what is left is clause (c) read on inverse images.

Reading clause (c) on inverse images is `localizationSquareInverseImage`, and it needs the two
horizontal inverse images in their restriction form: the inverse image of change of divided power
base is restriction along `smallChangeBase` because that functor is continuous as well as
cocontinuous ([Stacks, Tag 00XR] (1)), and the inverse image of the morphism of small Zariski
topoi is restriction along `IsOpenMap.functor` of `g` because the two presentations of that
morphism agree ([Stacks, Tag 00XQ]).  Those are
`smallChangeBaseInverseImageIso` and `opensMapInverseImageIso`.

Note that `CategoryTheory.SliceTopos.underlyingIso_hom_app_comp_hom`, the library's
[Stacks, Tag 04IU] comparison of a localization square with the square of a morphism of topoi,
does not serve here: it is stated for a continuous functor under `[HasFiniteLimits C]` and
`[PreservesFiniteLimits u]`, hypotheses `Cris(X/S)` does not satisfy.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.smallChangeBaseSliceEquivalence'` — `(X'/S')_cris` is
  `(X/S)_cris/u_{X/S}^{-1}G`, with the sheaf spelled as the inverse image, which is what
  `MorphismOfTopoi.over` produces.
* `Crystalline.GlobalCrystallineSituation.opensShriekAdjunction` and
  `Crystalline.GlobalCrystallineSituation.smallChangeBaseShriekAdjunction` — the two horizontal
  arrows of the square are the localization morphisms `j_G` and `j_F`.
* `Crystalline.GlobalCrystallineSituation.smallChangeBaseLocalizationSquare` — **clause (d)**:
  the square is the one 04H1 produces.
* `Crystalline.GlobalCrystallineSituation.openSubspace` — the crystalline situation of an open
  `V` of `X` over the *same* divided power base, and
  `...openSubspaceSliceEquivalence`, `...openSubspaceShriekAdjunction`,
  `...openSubspaceLocalizationSquare` — clause (d) for it.  Change of base out of it is change
  of base along the identity of `S`, for which the `IsInducedOpen` hypothesis is automatic, so
  this is clause (d) in the form "`Cris(V/S)` is the open subobject `V` of the final sheaf on
  `Cris(X/S)`" that the remark [Stacks, Tag 07ML] takes for granted.

## Main results

* `Crystalline.GlobalCrystallineSituation.localizationSquareInverseImage` — clause (c) read on
  inverse images, in the slice form.

## References

* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 04H1](https://stacks.math.columbia.edu/tag/04H1)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
* [Stacks Project, Tag 00XQ](https://stacks.math.columbia.edu/tag/00XQ)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}
  [IsOpenImmersion g]

/-- **The inverse image of change of divided power base is restriction**, [Stacks, Tag 00XR] (1):
change of base is continuous as well as cocontinuous, so the sheafification in
`CategoryTheory.Functor.sheafPullbackCocontinuous` is unnecessary. -/
def smallChangeBaseInverseImageIso :
    (smallChangeBaseMorphism S S' f g h).inverseImage ≅
      (smallChangeBase S S' f g h).sheafPushforwardContinuous (Type (u + 1))
        (smallTopology S) (smallTopology S') :=
  (smallChangeBase S S' f g h).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type (u + 1)) (smallTopology S) (smallTopology S')

/-- **The inverse image of the morphism of small Zariski topoi along `g` is restriction along the
direct image of opens.**  Its pushforward is restriction along `Opens.map g`, which by
[Stacks, Tag 00XQ] is the sheaf pushforward along the cocontinuous `IsOpenMap.functor` of `g`;
the left adjoint of the latter is restriction along that functor, and left adjoints are unique. -/
def opensMapInverseImageIso :
    haveI := g.isOpenEmbedding.functor_isContinuous
    (StacksZariskiSite.opensMapMorphismOfTopoi g.base).inverseImage ≅
      (IsOpenMap.functor g.isOpenEmbedding.isOpenMap).sheafPushforwardContinuous (Type (u + 1))
        (Opens.grothendieckTopology S.X.carrier) (Opens.grothendieckTopology S'.X.carrier) :=
  haveI hgemb : Topology.IsOpenEmbedding g.base := g.isOpenEmbedding
  haveI hg : IsOpenMap g.base := hgemb.isOpenMap
  haveI := StacksOpenMapSite.isCocontinuous_isOpenMapFunctor hg
  haveI := hgemb.functor_isContinuous
  Adjunction.leftAdjointUniq
    ((StacksZariskiSite.opensMapMorphismOfTopoi g.base).adj.ofNatIsoRight
      (StacksOpenMapSite.sheafPushforwardCocontinuousIsoOpensMap hg (Type (u + 1))).symm)
    ((IsOpenMap.functor hg).sheafAdjunctionCocontinuous (Type (u + 1))
      (Opens.grothendieckTopology S.X.carrier) (Opens.grothendieckTopology S'.X.carrier))

/-- **[Stacks, Tag 07KL], clause (d): `(X'/S')_cris` is the slice of `(X/S)_cris` at
`u_{X/S}^{-1}h_{X'}`**, with the sheaf spelled as that inverse image rather than as the
restriction `(U, T, δ) ↦ h_{X'}(U)`.

This is `smallChangeBaseSliceEquivalence` transported along
`zariskiInverseImageOpenSubobjectSheafIso`.  The spelling matters: the source of
`MorphismOfTopoi.over` of `u_{X/S}` at `h_{X'}` is `Over (u_{X/S}^{-1}h_{X'})` on the nose, so
with this equivalence the square of clause (d) needs no bridging isomorphism. -/
@[stacks 07KL "clause (d): (X'/S')_cris is the slice of (X/S)_cris at u_{X/S}^{-1}h_{X'}, read \
  at the inverse image itself, which is the source of MorphismOfTopoi.over"]
def smallChangeBaseSliceEquivalence' [IsOpenImmersion f.hom]
    (hf : DividedPowerScheme.IsInducedOpen f) :
    smallTopos S ≌
      Over ((zariskiToposMorphism S').inverseImage.obj (opensReprSheaf g.opensRange)) :=
  (smallChangeBaseSliceEquivalence (h := h) hf).trans
    (Over.mapIso (zariskiInverseImageOpenSubobjectSheafIso (S := S) (g := g)).symm)

/-- **[Stacks, Tag 07KL], clause (d): the bottom arrow of the square is the localization morphism
`j_G`.**  The functor `Sh(X'_Zar) ⥤ Sh(X_Zar)` obtained from `opensSliceEquivalence` by forgetting
the structure map to `h_{X'}` is `j_{G!}`, left adjoint to the inverse image of the morphism of
small Zariski topoi along `g`, which is therefore `j_G^{-1}`.

This is the last assertion of [Stacks, Tag 0791] for the subterminal sheaf `h_{X'}`, composed
with `opensMapInverseImageIso`. -/
@[stacks 07KL "clause (d): the bottom arrow of the square is the localization morphism j_G, i.e. \
  the slice equivalence followed by Over.forget is left adjoint to its inverse image"]
def opensShriekAdjunction :
    (opensSliceEquivalence S S' g).functor ⋙
        Over.forget (opensReprSheaf (S := S') g.opensRange) ⊣
      (StacksZariskiSite.opensMapMorphismOfTopoi g.base).inverseImage :=
  haveI hgemb : Topology.IsOpenEmbedding g.base := g.isOpenEmbedding
  haveI hg : IsOpenMap g.base := hgemb.isOpenMap
  haveI := StacksOpenMapSite.full_functor hgemb
  haveI := hgemb.functor_isContinuous
  (Stacks.Topos.Subterminal.shriekAdjunction (j := IsOpenMap.functor hg)
      (fun V hV ↦ (StacksOpenMapSite.essImage_functor_iff hg V).mpr
        ((nonempty_opensRepr_obj_iff (S := S') g.opensRange V).mp hV))
      (fun _ ↦ (nonempty_opensRepr_obj_iff (S := S') g.opensRange _).mpr
        (fun _ ⟨y, _, hy⟩ ↦ ⟨y, hy⟩))
      (isSheaf_opensRepr (S := S') g.opensRange)
      (StacksOpenMapSite.mem_grothendieckTopology_iff_functorPushforward_mem hgemb)).ofNatIsoRight
    (opensMapInverseImageIso (S := S) (g := g)).symm

/-- **[Stacks, Tag 07KL], clause (d): the top arrow of the square is the localization morphism
`j_F`.**  The functor `(X'/S')_cris ⥤ (X/S)_cris` obtained from
`smallChangeBaseSliceEquivalence'` by forgetting the structure map to `F = u_{X/S}^{-1}h_{X'}` is
`j_{F!}`, left adjoint to the inverse image of change of divided power base, which is therefore
`j_F^{-1}`.

As for the Zariski half, this is the last assertion of [Stacks, Tag 0791] for a subterminal
sheaf, composed with `smallChangeBaseInverseImageIso`.  Forgetting the structure map to
`u_{X/S}^{-1}h_{X'}` after the transport of `smallChangeBaseSliceEquivalence'` is forgetting the
structure map to the restriction before it, `CategoryTheory.Over.map` of an isomorphism composed
with `CategoryTheory.Over.forget` being `CategoryTheory.Over.forget`. -/
@[stacks 07KL "clause (d): the top arrow of the square is the localization morphism j_F, i.e. \
  the slice equivalence followed by Over.forget is left adjoint to its inverse image"]
def smallChangeBaseShriekAdjunction [IsOpenImmersion f.hom]
    (hf : DividedPowerScheme.IsInducedOpen f) :
    (smallChangeBaseSliceEquivalence' (h := h) hf).functor ⋙
        Over.forget ((zariskiToposMorphism S').inverseImage.obj (opensReprSheaf g.opensRange)) ⊣
      (smallChangeBaseMorphism S S' f g h).inverseImage :=
  (Stacks.Topos.Subterminal.shriekAdjunction (j := smallChangeBase S S' f g h)
      (fun B hB ↦ (nonempty_forgetToOpensOpCompOpensRepr_iff_essImage (h := h) hf B).mp hB)
      (nonempty_forgetToOpensOpCompOpensRepr_smallChangeBase (h := h))
      (isSheaf_forgetToOpensOpCompOpensRepr g.opensRange)
      (mem_smallTopology_iff_functorPushforward_mem (h := h))).ofNatIsoRight
    (smallChangeBaseInverseImageIso (h := h)).symm

/-- **Clause (c) of [Stacks, Tag 07KL], read on inverse images and in the slice form.**  The
inverse image of the localized morphism `MorphismOfTopoi.over` of `u_{X/S}` at `h_{X'}`, followed
by the crystalline slice equivalence, is the Zariski slice equivalence followed by the inverse
image of `u_{X'/S'}`.

Both composites begin with `Over.forget h_{X'}`: for the left one because
`CategoryTheory.Over.post` followed by `Over.forget` is `Over.forget` followed by the functor,
and for the right one because the slice equivalence's inverse is restriction after
`Over.forget`.  What remains after cancelling it is the commutative square of clause (c) read on
inverse images, obtained from `smallChangeBaseZariskiSquare` by uniqueness of left adjoints, with
the two horizontal inverse images put in restriction form by `opensMapInverseImageIso` and
`smallChangeBaseInverseImageIso`. -/
def localizationSquareInverseImage [IsOpenImmersion f.hom]
    (hf : DividedPowerScheme.IsInducedOpen f) :
    ((zariskiToposMorphism S').over (opensReprSheaf g.opensRange)).inverseImage ⋙
        (smallChangeBaseSliceEquivalence' (h := h) hf).inverse ≅
      (opensSliceEquivalence S S' g).inverse ⋙ (zariskiToposMorphism S).inverseImage :=
  haveI hgemb : Topology.IsOpenEmbedding g.base := g.isOpenEmbedding
  haveI hg : IsOpenMap g.base := hgemb.isOpenMap
  haveI := StacksOpenMapSite.isCocontinuous_isOpenMapFunctor hg
  haveI := hgemb.functor_isContinuous
  let core : (StacksZariskiSite.opensMapMorphismOfTopoi g.base).inverseImage ⋙
      (zariskiToposMorphism S).inverseImage ≅
        (zariskiToposMorphism S').inverseImage ⋙
          (smallChangeBaseMorphism S S' f g h).inverseImage :=
    Adjunction.leftAdjointUniq
      (((StacksZariskiSite.opensMapMorphismOfTopoi g.base).comp
        (zariskiToposMorphism S)).adj.ofNatIsoRight (smallChangeBaseZariskiSquare S S' f g h))
      (((zariskiToposMorphism S').comp (smallChangeBaseMorphism S S' f g h)).adj)
  Functor.isoWhiskerLeft (Over.forget (opensReprSheaf (S := S') g.opensRange))
    ((Functor.isoWhiskerLeft (zariskiToposMorphism S').inverseImage
          (smallChangeBaseInverseImageIso (h := h))).symm ≪≫ core.symm ≪≫
      Functor.isoWhiskerRight (opensMapInverseImageIso (S := S) (g := g))
        (zariskiToposMorphism S).inverseImage)

/-- **[Stacks, Tag 07KL], clause (d): the square of clause (c) is the localization square of
[Stacks, Tag 04H1].**  Under the two slice equivalences the morphism of topoi
`(X'/S')_cris ⟶ Sh(X'_Zar)` becomes `MorphismOfTopoi.over` of `u_{X/S}` at `h_{X'}`: the two
composites `(X'/S')_cris ⥤ Sh(X_Zar)/h_{X'}` are isomorphic, as an invertible 2-morphism between
their direct images.

Together with `opensShriekAdjunction` and `smallChangeBaseShriekAdjunction`, which identify the
two horizontal arrows with the localization morphisms `j_G` and `j_F`, and with the two slice
equivalences of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OpenSubobjectSlice.lean`, this is the whole
of clause (d).

The proof is uniqueness of right adjoints.  The left adjoint of the left-hand composite is
`(u_{X/S}')^{-1}` followed by the inverse of the crystalline slice equivalence, that of the
right-hand one is the inverse of the Zariski slice equivalence followed by `u_{X'/S'}^{-1}`, and
`localizationSquareInverseImage` identifies them. -/
@[stacks 07KL "clause (d), and with it the whole of clause (d): the square of clause (c) IS the \
  localization square of Stacks 04H1 at h_{X'}.  The two slice identifications are \
  opensSliceEquivalence and smallChangeBaseSliceEquivalence', the two horizontal arrows are the \
  localization morphisms by opensShriekAdjunction and smallChangeBaseShriekAdjunction, and this \
  is the commutativity of the resulting square"]
def smallChangeBaseLocalizationSquare [IsOpenImmersion f.hom]
    (hf : DividedPowerScheme.IsInducedOpen f) :
    (smallChangeBaseSliceEquivalence' (h := h) hf).functor ⋙
        ((zariskiToposMorphism S').over (opensReprSheaf g.opensRange)).pushforward ≅
      (zariskiToposMorphism S).pushforward ⋙ (opensSliceEquivalence S S' g).functor :=
  Adjunction.rightAdjointUniq
    ((((zariskiToposMorphism S').over (opensReprSheaf g.opensRange)).adj.comp
      (smallChangeBaseSliceEquivalence' (h := h) hf).symm.toAdjunction).ofNatIsoLeft
        (localizationSquareInverseImage (h := h) hf))
    ((opensSliceEquivalence S S' g).symm.toAdjunction.comp (zariskiToposMorphism S).adj)

section OpenSubspace

/-- The underlying morphism of schemes of an identity of divided power schemes is an identity,
hence an open immersion. -/
instance isOpenImmersion_id_hom (D : DividedPowerScheme.{u}) :
    IsOpenImmersion (DividedPowerScheme.Hom.hom (𝟙 D)) := by
  rw [DividedPowerScheme.Hom.id_hom]
  infer_instance

/-- **The crystalline situation of an open subscheme of `X` over the same divided power base.**
Everything is inherited: the base, the prime and its `ℤ_(p)`-structure are those of `S`, the
space is `V`, and the structure morphism is that of `S` restricted to `V`.  Local nilpotence of
`p` passes because the local rings of an open subscheme are those of the ambient scheme.

Unlike `Crystalline.GlobalCrystallineSituation.restrict`, which restricts the base as well, this
leaves the base untouched, so change of divided power base out of it is change of base along the
*identity* of `S`.  That is what makes clause (d) of [Stacks, Tag 07KL] available for it: the
hypothesis `Crystalline.DividedPowerScheme.IsInducedOpen` holds for an isomorphism.

It is `@[reducible]` so that `(openSubspace S V).X` and `(openSubspace S V).S` reduce at
`instances` transparency: the three statements below mention `V.ι` at the type
`(openSubspace S V).X ⟶ S.X`, and without that reduction `IsOpenImmersion V.ι` is not found. -/
@[reducible]
def openSubspace (S : GlobalCrystallineSituation.{u}) (V : S.X.Opens) :
    GlobalCrystallineSituation.{u} where
  p := S.p
  prime := S.prime
  S := S.S
  algebraAtPrime := S.algebraAtPrime
  X := V.toScheme
  toClosedFiber := V.ι ≫ S.toClosedFiber
  prime_locallyNilpotent x := by
    have hx := S.prime_locallyNilpotent (V.ι.base x)
    simpa using hx.map (V.ι.stalkMap x).hom

/-- **The compatibility datum of [Stacks, Tag 07IC] for an open of `X` over the same base**: the
structure morphism of `V/S` followed by the closed fibre of the identity of `S` is the structure
morphism of `S` restricted to `V`.  The closed fibre of an identity is an identity, the closed
fibre being a functor. -/
theorem openSubspace_changeBase_condition (S : GlobalCrystallineSituation.{u}) (V : S.X.Opens) :
    (openSubspace S V).toClosedFiber ≫ DividedPowerScheme.closedFiberMap (𝟙 S.S) =
      V.ι ≫ S.toClosedFiber :=
  (congrArg (fun k ↦ (openSubspace S V).toClosedFiber ≫ k)
      (DividedPowerScheme.closedFiberFunctor.map_id S.S)).trans
    (Category.comp_id (V.ι ≫ S.toClosedFiber))

variable (S : GlobalCrystallineSituation.{u}) (V : S.X.Opens)

/-- **[Stacks, Tag 07KL], clause (d) for an open subscheme of `X` over the same divided power
base: `Cris(V/S)` is the localization of `Cris(X/S)` at the open subobject `V` of the final
sheaf.**  This is `smallChangeBaseSliceEquivalence'` for the identity of `S` and the open
immersion `V ⟶ X`, the hypothesis
`Crystalline.DividedPowerScheme.IsInducedOpen` being satisfied by an isomorphism.

It is this instance of clause (d) that the remark [Stacks, Tag 07ML] takes for granted when it
says that `Cris(X'/S)`, `Cris(X''/S)` and `Cris(X'''/S)` "correspond to open subobjects of the
final sheaf on `Cris(X/S)`". -/
@[stacks 07KL "clause (d) for an open V of X over the SAME divided power base: Cris(V/S) is the \
  slice of Cris(X/S) at u_{X/S}^{-1}h_V, which is the form the remark 07ML uses"]
def openSubspaceSliceEquivalence :
    smallTopos (openSubspace S V) ≌
      Over ((zariskiToposMorphism S).inverseImage.obj (opensReprSheaf V.ι.opensRange)) :=
  smallChangeBaseSliceEquivalence' (h := openSubspace_changeBase_condition S V)
    (DividedPowerScheme.isInducedOpen_of_isIso (𝟙 S.S))

/-- **[Stacks, Tag 07KL], clause (d) for an open of `X` over the same base: the inclusion
`Cris(V/S) ⟶ Cris(X/S)` is the localization morphism `j_{h_V}`.** -/
@[stacks 07KL "clause (d) for an open V of X over the same base: the inclusion of Cris(V/S) is \
  the localization morphism at h_V"]
def openSubspaceShriekAdjunction :
    (openSubspaceSliceEquivalence S V).functor ⋙
        Over.forget ((zariskiToposMorphism S).inverseImage.obj (opensReprSheaf V.ι.opensRange)) ⊣
      (smallChangeBaseMorphism (openSubspace S V) S (𝟙 S.S) V.ι
        (openSubspace_changeBase_condition S V)).inverseImage :=
  smallChangeBaseShriekAdjunction (h := openSubspace_changeBase_condition S V)
    (DividedPowerScheme.isInducedOpen_of_isIso (𝟙 S.S))

/-- **[Stacks, Tag 07KL], clause (d) for an open of `X` over the same base: the square is the
localization square of [Stacks, Tag 04H1].** -/
@[stacks 07KL "clause (d) for an open V of X over the same base: the square formed with \
  u_{V/S} and u_{X/S} is the localization square of Stacks 04H1 at h_V"]
def openSubspaceLocalizationSquare :
    (openSubspaceSliceEquivalence S V).functor ⋙
        ((zariskiToposMorphism S).over (opensReprSheaf V.ι.opensRange)).pushforward ≅
      (zariskiToposMorphism (openSubspace S V)).pushforward ⋙
        (opensSliceEquivalence (openSubspace S V) S V.ι).functor :=
  smallChangeBaseLocalizationSquare (h := openSubspace_changeBase_condition S V)
    (DividedPowerScheme.isInducedOpen_of_isIso (𝟙 S.S))

end OpenSubspace

end Crystalline.GlobalCrystallineSituation

end
