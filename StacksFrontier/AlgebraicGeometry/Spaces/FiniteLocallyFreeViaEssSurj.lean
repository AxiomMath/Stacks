module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreePushforwardComparison

/-!
# Finite local freeness of a module on the small étale site, read on the Zariski site

Let `S` be a scheme contained in a big étale site `B` and let `𝒢` be a sheaf of `𝒪`-modules on
the small étale site of `S`.  Write `𝓕 = 𝒢|_{S_Zar}` for its restriction to the small Zariski
site of `S`, `AlgebraicGeometry.SmallEtale.restrictModule`.  This file transfers finite local
freeness *downwards*: if `𝒢` is finite locally free on the site then `𝓕` is a finite locally
free `𝒪_S`-module.

No quasi-coherence is assumed.  A finite locally free module on a site is of finite
presentation on the site, hence quasi-coherent on it, so the counit `𝓕^a ⟶ 𝒢` of the
associated-module adjunction is an isomorphism by
`AlgebraicGeometry.SmallEtale.isIso_counit`; that exhibits `𝒢` as the associated module of its
own Zariski restriction, which is the essential surjectivity of Stacks 03DX (2) at
`τ = étale`, and the reflection half of Stacks 05VG then descends the trivialisation.

The payoff is at the level of morphisms of schemes.  For an *affine* morphism `a` of the big
étale site, the direct image of `𝒪_X` along the morphism of ringed sites
`(X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` is the associated module of the Zariski direct image
`r_*𝒪_X`, by `AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso`.  So finite local
freeness of that direct image on the small étale site is exactly finite local freeness of the
morphism of schemes in the sense of Stacks 02KA, and therefore gives that the morphism is
finite.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.SmallEtale.isFiniteLocallyFree_restrictModule_of_isFiniteLocallyFreeOnSite`:
  **the Zariski restriction of a finite locally free module on the small étale site is finite
  locally free**, with no hypothesis on the module.
* `AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_iff_isFiniteLocallyFree_restrictModule`:
  for a module quasi-coherent on the site, finite local freeness on the small étale site is
  finite local freeness of its Zariski restriction.
* `AlgebraicGeometry.SmallEtale.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite_pushforward`:
  **an affine morphism of schemes whose small étale direct image of the structure sheaf is
  finite locally free on the site is finite locally free** in the sense of Stacks 02KA, and
* `AlgebraicGeometry.SmallEtale.isFinite_of_isFiniteLocallyFreeOnSite_pushforward`: **such a
  morphism is finite.**

## Implementation notes

Quasi-coherence of `𝒢` on the site is not an extra hypothesis of the first result: it is
obtained inline from `SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite`
followed by the instance `SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite`,
which is Stacks 03DL (2) ⇒ (7) ⇒ (6).  (The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent` announce that composite under
the name `SheafOfModules.isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite`; no declaration of
that name exists, and none is introduced here, the two steps being a `haveI` apiece.)  The
second hypothesis of `AlgebraicGeometry.SmallEtale.isIso_counit`, quasi-coherence of the Zariski
restriction, is the unconditional
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`.

The converse direction carries quasi-coherence on the site as a hypothesis and cannot avoid it:
without it the counit is not known to be invertible, and finite local freeness of `𝓕` bounds
only `𝓕^a`.

`AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso` is stated at a quasi-coherent
`𝒪_X`-module, so the unit module is fed to it and the identification of `(𝒪_X)^a` with the unit
module of the small étale site is `SheafOfModules.pullbackObjUnitToUnit`, invertible by
`AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit` because the inclusion of the small
Zariski site is final.  Quasi-coherence of `r_*𝒪_X`, needed to descend the trivialisation, is the
instance `Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`,
which is Stacks 02KG; this is where affineness of the morphism is used, and it is used nowhere
else.

No `@[stacks]` attribute is placed.  Stacks 05VG for the clause 03DL (2) at `τ = étale` is
registered on `AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_iff` and
its two halves, which are stated at an associated module `𝓕^a`; what is added here is the same
statements read at an arbitrary module on the site through its own restriction, and the
morphism-level consequence, which Stacks 02KA states for the Zariski site and does not restate
for the small étale one.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallEtale

/-! ### The Zariski restriction of a finite locally free module on the site -/

section Site

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The Zariski restriction of a finite locally free module on the small étale site of `S` is
a finite locally free `𝒪_S`-module.**

A finite locally free module on a site is of finite presentation on it, hence quasi-coherent on
it, so the counit of the associated-module adjunction at `𝒢` is an isomorphism and exhibits `𝒢`
as the associated module of its own Zariski restriction.  The reflection half of Stacks 05VG for
the clause 03DL (2) then descends the trivialisation to the Zariski site. -/
theorem isFiniteLocallyFree_restrictModule_of_isFiniteLocallyFreeOnSite
    (G : _root_.SheafOfModules.{u} (structureSheaf B S hS))
    (h : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite G) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((restrictModule B S hS).obj G) := by
  have := _root_.SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite h
  have hG : G.IsQuasicoherentOnSite := inferInstance
  have hq := isQuasicoherent_restrictModule B S hS G hG
  have := isIso_counit B S hS G hG hq
  exact isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite_associatedModule B S hS _
    (_root_.SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
      (asIso ((associatedModuleAdjunction B S hS).counit.app G)).symm h)

/-- **For a module quasi-coherent on the small étale site of `S`, finite local freeness on that
site is finite local freeness of its Zariski restriction.**

The forward direction is
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFree_restrictModule_of_isFiniteLocallyFreeOnSite`
and does not use the hypothesis; the backward direction is the forward half of Stacks 05VG for
the clause 03DL (2), transported along the counit, which is where quasi-coherence on the site is
needed. -/
theorem isFiniteLocallyFreeOnSite_iff_isFiniteLocallyFree_restrictModule
    (G : _root_.SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite) :
    _root_.SheafOfModules.IsFiniteLocallyFreeOnSite G ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((restrictModule B S hS).obj G) := by
  refine ⟨isFiniteLocallyFree_restrictModule_of_isFiniteLocallyFreeOnSite B S hS G, fun h => ?_⟩
  have hq := isQuasicoherent_restrictModule B S hS G hG
  have := isIso_counit B S hS G hG hq
  exact _root_.SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (asIso ((associatedModuleAdjunction B S hS).counit.app G))
    (isFiniteLocallyFreeOnSite_associatedModule B S hS _ h)

end Site

/-! ### Finiteness of an affine morphism of schemes -/

section Morphism

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- The direct image of `𝒪_X` along the morphism of ringed sites of `a` is the associated module
of the Zariski direct image `r_*𝒪_X`, for an affine morphism.

This is `AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso` at the structure sheaf of
`X`, whose associated module is the unit module of the small étale site of `X` by
`SheafOfModules.pullbackObjUnitToUnit`. -/
noncomputable def pushforwardUnitAssociatedModuleIso [IsAffineHom (schemeHom B a)] :
    (_root_.SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
        (_root_.SheafOfModules.unit (structureSheaf B X.obj X.property)) ≅
      (associatedModule B Y.obj Y.property).obj
        (Stacks.Morphisms.pushforwardStructureSheaf (schemeHom B a)) :=
  (_root_.SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).mapIso
      (asIso (_root_.SheafOfModules.pullbackObjUnitToUnit.{u}
        (structureMap B X.obj X.property))).symm ≪≫
    pushforwardAssociatedModuleIso B a
      (_root_.SheafOfModules.unit X.obj.ringCatSheaf) inferInstance

/-- **An affine morphism of schemes whose small étale direct image of the structure sheaf is
finite locally free on the site is finite locally free in the sense of Stacks 02KA.**

The direct image on the site is the associated module of the Zariski direct image `r_*𝒪_X`, by
`AlgebraicGeometry.SmallEtale.pushforwardUnitAssociatedModuleIso`, and `r_*𝒪_X` is
quasi-coherent because `a` is affine, so the reflection half of Stacks 05VG for the clause
03DL (2) makes `r_*𝒪_X` finite locally free.  Affineness of the morphism is the other conjunct
of Stacks 02KA. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite_pushforward
    [IsAffineHom (schemeHom B a)]
    (h : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite
      ((_root_.SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
        (_root_.SheafOfModules.unit (structureSheaf B X.obj X.property)))) :
    Stacks.Morphisms.IsFiniteLocallyFree (schemeHom B a) := by
  rw [Stacks.Morphisms.isFiniteLocallyFree_iff]
  refine ⟨inferInstance, isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite_associatedModule
    B Y.obj Y.property _ (_root_.SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
      (pushforwardUnitAssociatedModuleIso B a) h)⟩

/-- **An affine morphism of schemes whose small étale direct image of the structure sheaf is
finite locally free on the site is finite.**  It is finite locally free in the sense of
Stacks 02KA by
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite_pushforward`, and
a finite locally free morphism is finite. -/
theorem isFinite_of_isFiniteLocallyFreeOnSite_pushforward [IsAffineHom (schemeHom B a)]
    (h : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite
      ((_root_.SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
        (_root_.SheafOfModules.unit (structureSheaf B X.obj X.property)))) :
    _root_.AlgebraicGeometry.IsFinite (schemeHom B a) :=
  have := isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite_pushforward B a h
  Stacks.Morphisms.IsFiniteLocallyFree.isFinite (schemeHom B a)

end Morphism

end AlgebraicGeometry.SmallEtale

end
