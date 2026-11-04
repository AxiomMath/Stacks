module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackSquareComp
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleRestrictModulePullback

/-!
# The quasi-coherent module on the scheme underlying a representable algebraic space

Let `B` be a big fppf site containing a scheme `S` and let `U` be an object of the big fppf
category over `S`.  A quasi-coherent `𝒪`-module on the small étale site of the representable
algebraic space `yoneda.obj U` becomes a quasi-coherent module on the small étale site of the
scheme underlying `U` by `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, and
then a quasi-coherent `AlgebraicGeometry.Scheme.Modules` on that scheme by restriction to its
small Zariski site, the right adjoint of `𝓕 ↦ 𝓕^a` of Stacks 03DX (2).  This file builds that
passage and identifies it with pullback along the underlying morphism of schemes:

`r^*(F|_{T_Zar}) ≅ (φ^*F)|_{T'_Zar}`

for `g : T' ⟶ T` of the big fppf category and `φ` the morphism of representable algebraic spaces
it represents.  The two factors are
`AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso` for the restriction and
`AlgebraicGeometry.Space.representedModulePullbackIso` for the identification of the small étale
sites, so the comparison is a composite of named isomorphisms and no functor is inverted.

This is the object half of the transport that carries a descent datum of quasi-coherent modules
relative to a family of *representable* algebraic spaces to a quasi-coherent descent datum
relative to the underlying family of schemes, where the effectivity half of Stacks 023T
(`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`) can consume it.

## Main definitions

* `AlgebraicGeometry.Space.representedZariskiModule`: the module on the scheme underlying `U` of
  an `𝒪`-module on the small étale site of `yoneda.obj U`.
* `AlgebraicGeometry.Space.representedZariskiModulePullbackIso`: **the comparison
  `r^*(F|_{T_Zar}) ≅ (φ^*F)|_{T'_Zar}`.**

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_representedSmallEtaleInverse`: a quasi-coherent
  `𝒪`-module on the small étale site of `yoneda.obj U` is quasi-coherent on the small étale site
  of the scheme underlying `U`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap`: **the
  inverse image of Stacks 03LU of a quasi-coherent module along a morphism of representable
  algebraic spaces is quasi-coherent.**  The corresponding statement for an arbitrary morphism of
  algebraic spaces is not in the library; for a *representable* morphism it follows from the
  square of `AlgebraicGeometry.Space.representedModulePullbackIso` and
  `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback`.
* `AlgebraicGeometry.Space.representedModulePullbackIso_comp_inv`: **the pairwise coherence of
  the square of `AlgebraicGeometry.Space.representedModulePullbackIso`, solved for the inverse
  arrows** — the shape in which a transport along the square consumes it, the square entering a
  transport through its inverse on the side of the small étale sites of the schemes.
* `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_hom`: the comparison written out,
  so that a consumer rewrites rather than unfolds it.
* `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_comp`: **the comparisons
  `r^*(F|_{T_Zar}) ≅ (φ^*F)|_{T'_Zar}` compose**, through
  `AlgebraicGeometry.Scheme.Modules.pullbackComp` on the modules on the schemes and
  `AlgebraicGeometry.Space.representedModulePullbackCompIso` on the inverse images of
  Stacks 03LU.  Together with the comparison itself this is the whole transport of a descent
  datum of quasi-coherent modules along a family of representable algebraic spaces.

## Implementation notes

Composition in the category of `𝒪`-modules is a projection of the `SheafOfModules` instance, so
a step that unfolds it underneath a `≫` is unaffordable; the comparison is therefore accompanied
by `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_hom`, an equation whose two sides
are the same term, and every consumer rewrites with that rather than unfolding the definition.

`AlgebraicGeometry.Space.representedModulePullbackIso_comp_inv` is proved from the pairwise
coherence `AlgebraicGeometry.Space.representedModulePullbackIso_comp` read at one module, by
cancelling the two isomorphisms on the left against their inverses; the two isomorphisms are
reassociated into `CategoryTheory.Functor.mapIso` of the square's component by an ascribed
equation, for the same reason — `CategoryTheory.Iso.inv_hom_id_assoc` has to see one and the same
isomorphism on both sides of the cancellation, and it cannot be asked to unfold a pullback of
modules to find it.

**No associativity pentagon enters.**  The coherence used is the pairwise one, at two composable
morphisms; the inverse arrows are what a transport reads, and solving for them does not change
how many comparisons are contracted at once.

The composition law pastes
`AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_comp` with
`AlgebraicGeometry.Space.representedModulePullbackIso_comp_inv`, glued by
`AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_naturality`.  Each input is restated
as an ascribed hypothesis before it is used: the scheme underlying an object of the big fppf
category over `S` has two spellings — `(BigFppfOver.toScheme B S hS).obj T'` and
`B.inclusion.obj ((BigFppfOver.forget B S hS).obj T')` — and `CategoryTheory.Functor.comp` is not
reducible, so a lemma whose statement has been normalised to the second spelling does not match a
goal in the first.  Ascribing each input in the goal's spelling, and whiskering it with the
remaining morphism by hand rather than through `reassoc_of%` (which normalises the spelling
away), keeps every rewrite syntactic.

No `stacks` attribute is registered.  Stacks 03LU is tagged where
`AlgebraicGeometry.Space.modulePullback` is built, Stacks 03DX (2) where its clauses are proved,
and Stacks 03G9 where quasi-coherence on an algebraic space is defined; what is added here is
their composite, which is a step in the proof of Stacks 04W8 and not a clause of any of them.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A quasi-coherent `𝒪`-module on the small étale site of `yoneda.obj U` is quasi-coherent on
the small étale site of the scheme underlying `U`.**  The two correspond under
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, which preserves and reflects
quasi-coherence by `AlgebraicGeometry.Space.isQuasicoherentOnSite_representedSmallEtaleModule_iff`;
the counit of the equivalence carries the hypothesis across. -/
public theorem isQuasicoherentOnSite_representedSmallEtaleInverse (U : BigFppfOver B S hS)
    (F : SheafOfModules.{u} (representedStructureRingSheaf B S hS U))
    (hF : F.IsQuasicoherentOnSite) :
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj F).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U _).1
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((representedSmallEtaleModuleEquivalence B S hS U).counitIso.app F).symm hF)

/-- **The module on the scheme underlying `U` of an `𝒪`-module on the small étale site of the
representable algebraic space `yoneda.obj U`.**  Read the module on the small étale site of the
scheme underlying `U` through
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, then restrict it to the small
Zariski site of that scheme along the right adjoint of `𝓕 ↦ 𝓕^a`.

For a quasi-coherent module this is quasi-coherent, by
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule` together with
`AlgebraicGeometry.Space.isQuasicoherentOnSite_representedSmallEtaleInverse`. -/
public noncomputable abbrev representedZariskiModule (U : BigFppfOver B S hS)
    (F : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj F)

section Represented

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

include hg in
/-- **The inverse image of Stacks 03LU of a quasi-coherent module along a morphism of
representable algebraic spaces is quasi-coherent.**

Read through `AlgebraicGeometry.Space.representedModulePullbackIso` the inverse image is pullback
along the morphism of small étale ringed sites of the underlying morphism of schemes, and that
preserves quasi-coherence by
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback`. -/
public theorem isQuasicoherentOnSite_modulePullback_representedSpaceMap
    (F : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
    (hF : F.IsQuasicoherentOnSite) :
    ((modulePullback B S hS (representedSpaceMap B S hS g)).obj F).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app _)
    ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T' _).2
      (SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((representedModulePullbackIso B S hS g hg).app F).symm
        (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback
          (associatedBigEtaleSite B) g.left _
          (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T F hF))))

/-- **The module on the scheme underlying `U` commutes with inverse images.**  For `g : T' ⟶ T`
of the big fppf category over `S`, with `r` the underlying morphism of schemes and `φ` the
morphism of representable algebraic spaces represented by `g`, and for a quasi-coherent
`𝒪`-module `F` on the small étale site of `yoneda.obj T`,

`r^*(F|_{T_Zar}) ≅ (φ^*F)|_{T'_Zar}`.

It is `AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso` at the module `F` becomes on
the small étale site of the scheme underlying `T`, followed by the restriction of the square
`AlgebraicGeometry.Space.representedModulePullbackIso` of that site against the small étale site
of `yoneda.obj T`. -/
public noncomputable def representedZariskiModulePullbackIso
    (F : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
    (hF : F.IsQuasicoherentOnSite) :
    (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).obj
        (representedZariskiModule B S hS T F) ≅
      representedZariskiModule B S hS T'
        ((modulePullback B S hS (representedSpaceMap B S hS g)).obj F) :=
  _root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso (associatedBigEtaleSite B)
      g.left ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj F)
      (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T F hF) ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).mapIso
      ((representedModulePullbackIso B S hS g hg).app F).symm

/-- `AlgebraicGeometry.Space.representedZariskiModulePullbackIso` written out, so that a consumer
rewrites with this equation instead of unfolding the definition underneath a `≫`. -/
public theorem representedZariskiModulePullbackIso_hom
    (F : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
    (hF : F.IsQuasicoherentOnSite) :
    (representedZariskiModulePullbackIso B S hS g hg F hF).hom =
      (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso (associatedBigEtaleSite B)
        g.left ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj F)
        (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T F hF)).hom ≫
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
        ((representedModulePullbackIso B S hS g hg).app F).inv := rfl

end Represented

section Comp

variable {T'' T' T : BigFppfOver B S hS} (h : T'' ⟶ T') (g : T' ⟶ T)
  (hh : yoneda.relativelyRepresentable (yoneda.map h))
  (hg : yoneda.relativelyRepresentable (yoneda.map g))
  (hhg : yoneda.relativelyRepresentable (yoneda.map (h ≫ g)))

/-- **The pairwise coherence of the square of
`AlgebraicGeometry.Space.representedModulePullbackIso`, solved for the inverse arrows.**  For
`h : T'' ⟶ T'` and `g : T' ⟶ T` of the big fppf category over `S` and a module `F` on the small
étale site of `yoneda.obj T`, going back round the two squares and then contracting the two
inverse images of Stacks 03LU is contracting the two pullbacks along the morphisms of small étale
ringed sites and then going back round the square of `h ≫ g`.

This is `AlgebraicGeometry.Space.representedModulePullbackIso_comp` at `F`, with the two
isomorphisms on the left cancelled against their inverses. -/
public theorem representedModulePullbackIso_comp_inv
    (F : SheafOfModules.{u} (representedStructureRingSheaf B S hS T)) :
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS h)).map
          ((representedModulePullbackIso B S hS g hg).app F).inv ≫
        ((representedModulePullbackIso B S hS h hh).app
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj F)).inv ≫
          (representedSmallEtaleModuleEquivalence B S hS T'').inverse.map
            ((representedModulePullbackCompIso B S hS h g).hom.app F) =
      (representedSchemeModulePullbackCompIso B S hS h g).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj F) ≫
        ((representedModulePullbackIso B S hS (h ≫ g) hhg).app F).inv := by
  have key : ((representedModulePullbackIso B S hS h hh).app
          ((modulePullback B S hS (representedSpaceMap B S hS g)).obj F)).hom ≫
        (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS h)).map
          ((representedModulePullbackIso B S hS g hg).app F).hom ≫
        (representedSchemeModulePullbackCompIso B S hS h g).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj F) =
      (representedSmallEtaleModuleEquivalence B S hS T'').inverse.map
          ((representedModulePullbackCompIso B S hS h g).hom.app F) ≫
        ((representedModulePullbackIso B S hS (h ≫ g) hhg).app F).hom :=
    NatTrans.congr_app
      (congrArg Iso.hom (representedModulePullbackIso_comp B S hS h g hh hg hhg)) F
  rw [Iso.eq_comp_inv, Category.assoc, Category.assoc, ← key,
    show ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS h)).map
          ((representedModulePullbackIso B S hS g hg).app F).inv) =
        ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS h)).mapIso
          ((representedModulePullbackIso B S hS g hg).app F)).inv from rfl,
    show ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS h)).map
          ((representedModulePullbackIso B S hS g hg).app F).hom) =
        ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS h)).mapIso
          ((representedModulePullbackIso B S hS g hg).app F)).hom from rfl,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]

/-- Whiskering an equation `a ≫ b = c ≫ d` on the right by `k`, as a rewrite of `a ≫ b ≫ k`. -/
private theorem comp_assoc_of_eq {C : Type*} [Category C] {X Y Z V W : C} {a : X ⟶ Y}
    {b : Y ⟶ Z} {c : X ⟶ V} {d : V ⟶ Z} (h : a ≫ b = c ≫ d) (k : Z ⟶ W) :
    a ≫ b ≫ k = c ≫ d ≫ k := by
  rw [← Category.assoc, h, Category.assoc]

/-- **The comparison `r^*(F|_{T_Zar}) ≅ (φ^*F)|_{T'_Zar}` composes.**  For `h : T'' ⟶ T'` and
`g : T' ⟶ T` of the big fppf category over `S` and `F` quasi-coherent on the small étale site of
`yoneda.obj T`, the comparison below `g` pulled back along the morphism of schemes underlying
`h`, followed by the comparison below `h` and by the restriction of the contraction of the two
inverse images of Stacks 03LU, is the contraction of the two pullbacks of modules on the schemes
followed by the comparison below `h ≫ g`.

This is `AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_comp` pasted with
`AlgebraicGeometry.Space.representedModulePullbackIso_comp_inv`: the first contracts the
restrictions to the small Zariski sites, the second goes back round the two squares of the small
étale sites.  The two are glued by
`AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_naturality`, which carries the
comparison below `h` from the pullback of the module on the small étale site of the scheme to the
module the square of `g` produces on the small étale site of `yoneda.obj T'`.

**No associativity pentagon enters**, here or in either input: only two comparisons are ever
contracted at once. -/
public theorem representedZariskiModulePullbackIso_comp
    (F : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
    (hF : F.IsQuasicoherentOnSite) :
    (Scheme.Modules.pullback
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)).map
          (representedZariskiModulePullbackIso B S hS g hg F hF).hom ≫
        (representedZariskiModulePullbackIso B S hS h hh
          ((modulePullback B S hS (representedSpaceMap B S hS g)).obj F)
          (isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS g hg F hF)).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T'') T''.left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS T'').inverse.map
            ((representedModulePullbackCompIso B S hS h g).hom.app F)) =
      (Scheme.Modules.pullbackComp
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) g.left)).hom.app
          (representedZariskiModule B S hS T F) ≫
        (representedZariskiModulePullbackIso B S hS (h ≫ g) hhg F hF).hom := by
  have e1 : (representedZariskiModulePullbackIso B S hS h hh
        ((modulePullback B S hS (representedSpaceMap B S hS g)).obj F)
        (isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS g hg F hF)).hom =
      (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso (associatedBigEtaleSite B)
          h.left
          ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj F))
          (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T'
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj F)
            (isQuasicoherentOnSite_modulePullback_representedSpaceMap
              B S hS g hg F hF))).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T'') T''.left.property).map
          ((representedModulePullbackIso B S hS h hh).app
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj F)).inv :=
    representedZariskiModulePullbackIso_hom B S hS h hh _ _
  have nat : (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)).map
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
            ((representedModulePullbackIso B S hS g hg).app F).inv) ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso
            (associatedBigEtaleSite B) h.left
            ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj
              ((modulePullback B S hS (representedSpaceMap B S hS g)).obj F))
            (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T'
              ((modulePullback B S hS (representedSpaceMap B S hS g)).obj F)
              (isQuasicoherentOnSite_modulePullback_representedSpaceMap
                B S hS g hg F hF))).hom =
      (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso (associatedBigEtaleSite B)
          h.left
          ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).obj
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj F))
          (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback
            (associatedBigEtaleSite B) g.left
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj F)
            (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T F hF))).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T'') T''.left.property).map
          ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS h)).map
            ((representedModulePullbackIso B S hS g hg).app F).inv) :=
    _root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_naturality
      (associatedBigEtaleSite B) h.left _ _ _
  have cmp : (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)).map
          (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso
            (associatedBigEtaleSite B) g.left
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj F)
            (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T F hF)).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso
            (associatedBigEtaleSite B) h.left
            ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).obj
              ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj F))
            (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback
              (associatedBigEtaleSite B) g.left
              ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj F)
              (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T F hF))).hom ≫
          (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T'') T''.left.property).map
            ((representedSchemeModulePullbackCompIso B S hS h g).hom.app
              ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj F)) =
      (Scheme.Modules.pullbackComp
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) g.left)).hom.app
          (representedZariskiModule B S hS T F) ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso
            (associatedBigEtaleSite B) (h ≫ g).left
            ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj F)
            (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T F hF)).hom :=
    _root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_comp
      (associatedBigEtaleSite B) h.left g.left
      ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj F)
      (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T F hF)
  simp only [representedZariskiModulePullbackIso_hom, e1, Functor.map_comp, Category.assoc]
  rw [comp_assoc_of_eq nat]
  simp only [← Functor.map_comp]
  rw [representedModulePullbackIso_comp_inv B S hS h g hh hg hhg F]
  simp only [Functor.map_comp]
  simpa only [Category.assoc] using eq_whisker cmp _

end Comp

end AlgebraicGeometry.Space

end
