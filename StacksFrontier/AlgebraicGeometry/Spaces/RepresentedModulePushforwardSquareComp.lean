module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparisonComp
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleBaseChangeConjugate

/-!
# The pasting coherence of the square of direct images of a representable morphism

`AlgebraicGeometry.Space.representedModulePushforwardSquareIso` compares, for a morphism
`g : T' ⟶ T` of the big fppf category over `S`, the two routes round the square of small étale
ringed sites: the direct image along base change of schemes followed by the identification of the
small étale site of `yoneda.obj T` with the small étale site of the scheme underlying `T`, and
that identification for `T'` followed by the direct image of Stacks 03LU along the represented
morphism.  This file proves that those squares paste: for `h : T'' ⟶ T'` and `g : T' ⟶ T`,
pasting the square of `h` against the square of `g` and contracting the two direct images on each
side gives the square of `h ≫ g`.

The square is a composite of four factors.  Three of them are structural —
`SheafOfModules.pushforwardComp` and `SheafOfModules.pushforwardCongr₂`, over
`AlgebraicGeometry.Space.representedStructureMapRing_square` — and the fourth is the comparison
`AlgebraicGeometry.Space.modulePushforwardChartIso` of the direct image of Stacks 03LU with the
direct image along base change of charts.  So the proof is in two halves: the structural three
factors paste because base change of charts pastes
(`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso_comp`), and the fourth factor is
carried by `AlgebraicGeometry.Space.modulePushforwardChartIso_comp`; a diagram of whiskered
isomorphisms puts the two halves together.

## Main definitions

* `Stacks.ChartPushforwardSquare.squareIso` is the structural square of two morphisms of ringed
  sites whose composites agree up to an isomorphism of the index functors, and
  `AlgebraicGeometry.Space.representedModuleStructuralSquareIso` is the square of this file with
  the chart comparison removed.
* `AlgebraicGeometry.Space.representedModulePushforwardCompIso` and
  `AlgebraicGeometry.Space.representedSchemeModulePushforwardCompIso` contract the two direct
  images on the two sides of the square.

## Main results

* `Stacks.ChartPushforwardSquare.pastedSquare_eq`: **structural squares paste**, at an arbitrary
  site, given the identity of the comparison arrows at an object.
* `Stacks.ChartPushforwardSquare.pasteWithCorrection`: the two-categorical diagram that composes
  a pasting of structural squares with a pasting of corrections of their right-hand edges.
* `AlgebraicGeometry.Space.representedModuleStructuralSquareIso_comp`: the structural part of the
  square pastes.
* `AlgebraicGeometry.Space.representedModulePushforwardSquareIso_comp`: **the square of direct
  images of a representable morphism satisfies the pasting coherence.**

## Implementation notes

Every step that unfolds the sections of a direct image is taken at an arbitrary site.  The
reason: over an étale chart `V` of `yoneda.obj T` the sections of
`F' ⋙ Π_g` — the identification of the two small étale sites followed by the direct image along
base change of charts — are spelled both as sections of that composite over `V` and as sections
of the module over the base-changed chart, and reconciling those two spellings *at the
represented site* costs some six seconds for a single occurrence and exhausts the heartbeat
budget when it occurs twice in one declaration.  At an arbitrary site, with the two pushforwards
variables, the same reconciliation is `rfl`.  So
`Stacks.ChartPushforwardSquare.pastedSquare_eq` carries the whole sections computation, with
nineteen pieces of site data as variables, and its instantiation here matches only functors and
morphisms of sheaves of rings.  The same holds for
`Stacks.ChartPushforwardSquare.pasteWithCorrection`, which is a statement about isomorphisms in
functor categories and has no sections in it at all.

The composite of the morphisms of algebraic spaces represented by `h` and by `g` is only
provably the morphism represented by `h ≫ g`
(`AlgebraicGeometry.Space.representedSpaceMap_comp`), so the contraction of the two
base-change direct images and the composition law for the chart comparison are both needed at a
*factorisation* of the composite; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRepresentableBaseChangeComp.lean`.  The
contraction of the two direct images of Stacks 03LU therefore carries the `eqToIso` of that
equality, which is the only transport appearing in the statement of the coherence.

The local `implicit_reducible` attribute on `AlgebraicGeometry.Space.smallEtaleRingedSite`
collapses the two spellings of the category of `𝒪`-modules, as it does in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardChartComparisonComp.lean`; without it the
two direct images of the square cannot be composed.

No tag is registered.  Stacks 03LU is tagged where
`AlgebraicGeometry.Space.modulePushforwardCompIso` is proved; what is added here is that the
identification of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackBaseChange.lean` is functorial in
the morphism.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ChartPushforwardSquare

universe w v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

/-! ### The structural square of two morphisms of ringed sites -/

section Sites

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {C'' : Type u₃} [Category.{v₃} C''] {D : Type u₄} [Category.{v₄} D]
  {D' : Type u₅} [Category.{v₅} D'] {D'' : Type u₆} [Category.{v₆} D'']
  {JC : GrothendieckTopology C} {JC' : GrothendieckTopology C'}
  {JC'' : GrothendieckTopology C''} {JD : GrothendieckTopology D}
  {JD' : GrothendieckTopology D'} {JD'' : GrothendieckTopology D''}
  {bcg : C ⥤ C'} {bch : C' ⥤ C''} {bck : C ⥤ C''}
  {scg : D ⥤ D'} {sch : D' ⥤ D''} {sck : D ⥤ D''}
  {E : C ⥤ D} {E' : C' ⥤ D'} {E'' : C'' ⥤ D''}
  [bcg.IsContinuous JC JC'] [bch.IsContinuous JC' JC''] [bck.IsContinuous JC JC'']
  [scg.IsContinuous JD JD'] [sch.IsContinuous JD' JD''] [sck.IsContinuous JD JD'']
  [E.IsContinuous JC JD] [E'.IsContinuous JC' JD'] [E''.IsContinuous JC'' JD'']
  [(E ⋙ scg).IsContinuous JC JD'] [(bcg ⋙ E').IsContinuous JC JD']
  [(E' ⋙ sch).IsContinuous JC' JD''] [(bch ⋙ E'').IsContinuous JC' JD'']
  [(E ⋙ sck).IsContinuous JC JD''] [(bck ⋙ E'').IsContinuous JC JD'']
  [(scg ⋙ sch).IsContinuous JD JD''] [(bcg ⋙ bch).IsContinuous JC JC'']
  {RC : Sheaf JC RingCat.{w}} {RC' : Sheaf JC' RingCat.{w}} {RC'' : Sheaf JC'' RingCat.{w}}
  {RD : Sheaf JD RingCat.{w}} {RD' : Sheaf JD' RingCat.{w}} {RD'' : Sheaf JD'' RingCat.{w}}

section Square

variable (ε : RC ⟶ (E.sheafPushforwardContinuous RingCat.{w} JC JD).obj RD)
  (ρ : RD ⟶ (scg.sheafPushforwardContinuous RingCat.{w} JD JD').obj RD')
  (σ : RC ⟶ (bcg.sheafPushforwardContinuous RingCat.{w} JC JC').obj RC')
  (ε' : RC' ⟶ (E'.sheafPushforwardContinuous RingCat.{w} JC' JD').obj RD')
  (e : bcg ⋙ E' ≅ E ⋙ scg)
  (he : SheafOfModules.comparisonComp ε ρ ≫
    (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{w} JC JD').app RD' =
      SheafOfModules.comparisonComp σ ε')

/-- **The structural square of two morphisms of ringed sites.**  Let the two composite index
functors of a square of sites be identified by `e`, compatibly with the four structure maps.
Then the two composite direct images of sheaves of modules round the square are identified: each
is the direct image along one of the two composite morphisms of ringed sites, and those are
compared by `SheafOfModules.pushforwardCongr₂` along `e`.

Nothing here needs an adjointness instance, which is why the square is written out rather than
taken from `SheafOfModules.pullbackSquareIso`; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackBaseChange.lean`. -/
noncomputable abbrev squareIso :
    SheafOfModules.pushforward.{w} ρ ⋙ SheafOfModules.pushforward.{w} ε ≅
      SheafOfModules.pushforward.{w} ε' ⋙ SheafOfModules.pushforward.{w} σ :=
  SheafOfModules.pushforwardComp.{w} ε ρ ≪≫
    SheafOfModules.pushforwardCongr₂.{w} _ e he ≪≫
    (SheafOfModules.pushforwardComp.{w} σ ε').symm

/-- **The structural square on sections.**  Over an object `W` of the first site the square
reads a section as its restriction along the component of `e` at `W`: the two
`SheafOfModules.pushforwardComp` factors only reindex sections, and
`SheafOfModules.pushforwardCongr₂` restricts them along that component.

The point of the statement is that it is at an arbitrary site, with the module, the object and
the comparison morphism all variables; see the implementation notes. -/
theorem squareIso_hom_app_val_app
    (M : SheafOfModules.{w} RD') (W : C) (s : M.val.obj (op (scg.obj (E.obj W))))
    {c : E'.obj (bcg.obj W) ⟶ scg.obj (E.obj W)} (hc : e.hom.app W = c) :
    ((squareIso ε ρ σ ε' e he).hom.app M).val.app (op W) s = M.val.map c.op s := by
  subst hc
  rfl

end Square

/-! ### Pasting two structural squares -/

section Pasting

variable (ε : RC ⟶ (E.sheafPushforwardContinuous RingCat.{w} JC JD).obj RD)
  (ε' : RC' ⟶ (E'.sheafPushforwardContinuous RingCat.{w} JC' JD').obj RD')
  (ε'' : RC'' ⟶ (E''.sheafPushforwardContinuous RingCat.{w} JC'' JD'').obj RD'')
  (ρg : RD ⟶ (scg.sheafPushforwardContinuous RingCat.{w} JD JD').obj RD')
  (ρh : RD' ⟶ (sch.sheafPushforwardContinuous RingCat.{w} JD' JD'').obj RD'')
  (ρk : RD ⟶ (sck.sheafPushforwardContinuous RingCat.{w} JD JD'').obj RD'')
  (σg : RC ⟶ (bcg.sheafPushforwardContinuous RingCat.{w} JC JC').obj RC')
  (σh : RC' ⟶ (bch.sheafPushforwardContinuous RingCat.{w} JC' JC'').obj RC'')
  (σk : RC ⟶ (bck.sheafPushforwardContinuous RingCat.{w} JC JC'').obj RC'')
  (eg : bcg ⋙ E' ≅ E ⋙ scg) (eh : bch ⋙ E'' ≅ E' ⋙ sch) (ek : bck ⋙ E'' ≅ E ⋙ sck)
  (cc : bck ≅ bcg ⋙ bch) (scc : scg ⋙ sch ≅ sck)
  (heg : SheafOfModules.comparisonComp ε ρg ≫
    (Functor.sheafPushforwardContinuousNatTrans eg.hom RingCat.{w} JC JD').app RD' =
      SheafOfModules.comparisonComp σg ε')
  (heh : SheafOfModules.comparisonComp ε' ρh ≫
    (Functor.sheafPushforwardContinuousNatTrans eh.hom RingCat.{w} JC' JD'').app RD'' =
      SheafOfModules.comparisonComp σh ε'')
  (hek : SheafOfModules.comparisonComp ε ρk ≫
    (Functor.sheafPushforwardContinuousNatTrans ek.hom RingCat.{w} JC JD'').app RD'' =
      SheafOfModules.comparisonComp σk ε'')
  (hcc : SheafOfModules.comparisonComp σg σh ≫
    (Functor.sheafPushforwardContinuousNatTrans cc.hom RingCat.{w} JC JC'').app RC'' = σk)
  (hscc : ρk ≫
    (Functor.sheafPushforwardContinuousNatTrans scc.hom RingCat.{w} JD JD'').app RD'' =
      SheafOfModules.comparisonComp ρg ρh)

/-- **Structural squares paste.**  Pasting the square of the second morphism against the square
of the first and contracting the two direct images along the bottom edge is contracting the two
direct images along the top edge and then taking the square of the composite, provided the
comparison arrows satisfy the corresponding identity at every object of the first site.

Both sides are isomorphisms of direct images, so this is checked on sections, where every factor
is a restriction map and the identity that remains is `hchart`. -/
theorem pastedSquare_eq
    (hchart : ∀ W : C, E''.map (cc.hom.app W) ≫ eh.hom.app (bcg.obj W) ≫
        sch.map (eg.hom.app W) = ek.hom.app W ≫ scc.inv.app (E.obj W)) :
    Functor.isoWhiskerLeft (SheafOfModules.pushforward.{w} ρh)
          (squareIso ε ρg σg ε' eg heg) ≪≫
        Functor.isoWhiskerRight (squareIso ε' ρh σh ε'' eh heh)
          (SheafOfModules.pushforward.{w} σg) ≪≫
        Functor.isoWhiskerLeft (SheafOfModules.pushforward.{w} ε'')
          (SheafOfModules.pushforwardComp.{w} σg σh ≪≫
            SheafOfModules.pushforwardCongr₂.{w} _ cc hcc) =
      Functor.isoWhiskerRight
          (SheafOfModules.pushforwardComp.{w} ρg ρh ≪≫
            (SheafOfModules.pushforwardCongr₂.{w} ρk scc hscc).symm)
          (SheafOfModules.pushforward.{w} ε) ≪≫
        squareIso ε ρk σk ε'' ek hek := by
  refine Iso.ext (NatTrans.ext (funext fun M =>
    Stacks.ChartUnitTransport.hom_ext_val_app_apply_unop fun W x => ?_))
  show M.val.map (E''.map (cc.hom.app W)).op (M.val.map (eh.hom.app (bcg.obj W)).op
      (M.val.map (sch.map (eg.hom.app W)).op x)) =
    M.val.map (ek.hom.app W).op (M.val.map (scc.inv.app (E.obj W)).op x)
  refine Eq.trans (congrArg (fun z => M.val.map (E''.map (cc.hom.app W)).op z)
    (Stacks.SectionsComponents.val_map_map M (eh.hom.app (bcg.obj W))
      (sch.map (eg.hom.app W)) x)) ?_
  refine Eq.trans (Stacks.SectionsComponents.val_map_map M (E''.map (cc.hom.app W))
    (eh.hom.app (bcg.obj W) ≫ sch.map (eg.hom.app W)) x) ?_
  refine Eq.trans ?_ (Stacks.SectionsComponents.val_map_map M (ek.hom.app W)
    (scc.inv.app (E.obj W)) x).symm
  exact congrArg (fun z : E''.obj (bck.obj W) ⟶ (scg ⋙ sch).obj (E.obj W) =>
    M.val.map (Quiver.Hom.op z) x) (hchart W)

end Pasting

end Sites

/-! ### Correcting the right-hand edge of a pasting -/

section Correction

variable {MA : Type u₁} [Category.{v₁} MA] {MB : Type u₂} [Category.{v₂} MB]
  {MC : Type u₃} [Category.{v₃} MC] {NA : Type u₄} [Category.{v₄} NA]
  {NB : Type u₅} [Category.{v₅} NB] {NC : Type u₆} [Category.{v₆} NC]
  {Ph : MA ⥤ MB} {Pg : MB ⥤ MC} {Pk : MA ⥤ MC}
  {F : MC ⥤ NC} {F' : MB ⥤ NB} {F'' : MA ⥤ NA}
  {Qh Rh : NA ⥤ NB} {Qg Rg : NB ⥤ NC} {Qk Rk : NA ⥤ NC}
  (strg : Pg ⋙ F ≅ F' ⋙ Rg) (strh : Ph ⋙ F' ≅ F'' ⋙ Rh) (strk : Pk ⋙ F ≅ F'' ⋙ Rk)
  (cg : Qg ≅ Rg) (ch : Qh ≅ Rh) (ck : Qk ≅ Rk)
  (pc : Ph ⋙ Pg ≅ Pk) (rc : Rh ⋙ Rg ≅ Rk) (qc : Qh ⋙ Qg ≅ Qk)

/-- **A pasting of squares survives correcting their right-hand edges.**  Suppose three squares
paste, and that the right-hand edge of each is replaced by an isomorphic functor, compatibly
with the contractions of the composites.  Then the corrected squares paste.

This is the two-categorical half of the coherence of
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`: the corrections are the chart
comparisons of the direct image of Stacks 03LU, `hs` is the pasting of the structural squares
and `hc` is the pasting of the chart comparisons.  The proof is naturality of the correction on
the right-hand edge, followed by `hc` and `hs`. -/
theorem pasteWithCorrection
    (hs : Functor.isoWhiskerLeft Ph strg ≪≫ Functor.isoWhiskerRight strh Rg ≪≫
        Functor.isoWhiskerLeft F'' rc =
      Functor.isoWhiskerRight pc F ≪≫ strk)
    (hc : Functor.isoWhiskerRight ch Qg ≪≫ Functor.isoWhiskerLeft Rh cg ≪≫ rc =
      qc ≪≫ ck) :
    Functor.isoWhiskerLeft Ph (strg ≪≫ Functor.isoWhiskerLeft F' cg.symm) ≪≫
        Functor.isoWhiskerRight (strh ≪≫ Functor.isoWhiskerLeft F'' ch.symm) Qg ≪≫
        Functor.isoWhiskerLeft F'' qc =
      Functor.isoWhiskerRight pc F ≪≫ (strk ≪≫ Functor.isoWhiskerLeft F'' ck.symm) := by
  refine Iso.ext (NatTrans.ext (funext fun X => ?_))
  have hs' := NatTrans.congr_app (congrArg Iso.hom hs) X
  have hc' := NatTrans.congr_app (congrArg Iso.hom hc) (F''.obj X)
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    Category.assoc, Functor.map_comp] at hs' hc' ⊢
  have key : cg.inv.app (Rh.obj (F''.obj X)) ≫ Qg.map (ch.inv.app (F''.obj X)) ≫
      qc.hom.app (F''.obj X) = rc.hom.app (F''.obj X) ≫ ck.inv.app (F''.obj X) := by
    refine (Iso.eq_comp_inv (ck.app (F''.obj X))).mpr ?_
    simp only [Iso.app_hom, Category.assoc, ← hc']
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% cg.inv.naturality (strh.hom.app X), key, reassoc_of% hs']

end Correction

end Stacks.ChartPushforwardSquare

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart comparison at a factorisation of the composite -/

section Factored

variable {A C D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C) (k : D ⟶ C)
    (hk : h ≫ g = k)
    (hreph : yoneda.relativelyRepresentable h.hom)
    (hrepg : yoneda.relativelyRepresentable g.hom)
    (hrepk : yoneda.relativelyRepresentable k.hom)

/- The two spellings of the category of `𝒪`-modules are definitionally equal through
`AlgebraicGeometry.Space.smallEtaleRingedSite`; collapsing them is what lets the two direct
images be composed.  See the implementation notes. -/
attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- The contraction of the two base-change direct images at a chosen factorisation `h ≫ g = k`
of the composite.  This is
`AlgebraicGeometry.Space.smallBaseChangeChartPushforwardCompIso` with the comparison of the
charts and the compatibility of the structure maps taken at the factorisation. -/
noncomputable abbrev smallBaseChangeChartPushforwardFactoredCompIso :
    smallBaseChangeModulePushforward.{u, u} B S hS h hreph ⋙
        smallBaseChangeModulePushforward.{u, u} B S hS g hrepg ≅
      smallBaseChangeModulePushforward.{u, u} B S hS k hrepk :=
  SheafOfModules.pushforwardComp.{u} (smallBaseChangeSharp B S hS g hrepg)
      (smallBaseChangeSharp B S hS h hreph) ≪≫
    SheafOfModules.pushforwardCongr₂.{u} _
      (smallBaseChangeChartFactoredCompIso B S hS h g k hk hreph hrepg hrepk)
      (smallBaseChangeSharp_factoredComparisonComp B S hS h g k hk hreph hrepg hrepk)

/-- **The chart comparison of the direct image of modules is compatible with composition**, at a
chosen factorisation `h ≫ g = k` of the composite: this is
`AlgebraicGeometry.Space.modulePushforwardChartIso_comp` transported along the factorisation,
and the transport is carried by the contraction of the two direct images of Stacks 03LU. -/
theorem modulePushforwardChartIso_factoredComp :
    Functor.isoWhiskerRight (modulePushforwardChartIso B S hS h hreph)
          (modulePushforward B S hS g) ≪≫
        Functor.isoWhiskerLeft (smallBaseChangeModulePushforward.{u, u} B S hS h hreph)
          (modulePushforwardChartIso B S hS g hrepg) ≪≫
        smallBaseChangeChartPushforwardFactoredCompIso B S hS h g k hk hreph hrepg hrepk =
      (modulePushforwardCompIso B S hS h g ≪≫
          eqToIso (congrArg (modulePushforward B S hS) hk)) ≪≫
        modulePushforwardChartIso B S hS k hrepk := by
  subst hk
  exact (modulePushforwardChartIso_comp B S hS h g hreph hrepg hrepk).trans
    (congrArg (fun z => z ≪≫ modulePushforwardChartIso B S hS (h ≫ g) hrepk)
      (Iso.trans_refl _).symm)

end Factored

/-! ### The square of direct images and its structural part -/

section Represented

variable {T'' T' T : BigFppfOver B S hS} (h : T'' ⟶ T') (g : T' ⟶ T)
  (hh : yoneda.relativelyRepresentable (yoneda.map h))
  (hg : yoneda.relativelyRepresentable (yoneda.map g))
  (hhg : yoneda.relativelyRepresentable (yoneda.map (h ≫ g)))

/-- Base change of schemes along the morphism underlying `g` followed by base change along the
morphism underlying `h` is continuous.  `CategoryTheory.Functor.isContinuous_comp` is a lemma and
not an instance — the intermediate topology cannot be read off the goal — so the composite that
the pasting of the structural squares runs along has to be supplied by hand. -/
instance isContinuous_representedSchemeBaseChange_comp :
    (representedSchemeBaseChange B S hS g ⋙
        representedSchemeBaseChange B S hS h).IsContinuous
      (representedSchemeSmallEtaleTopology B S hS T)
      (representedSchemeSmallEtaleTopology B S hS T'') :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _
    (isContinuous_representedSchemeBaseChange B S hS g)
    (isContinuous_representedSchemeBaseChange B S hS h)

/-- Base change of étale scheme charts along the morphism represented by `g` followed by base
change along the morphism represented by `h` is continuous; as above, the composite has to be
supplied by hand. -/
instance isContinuous_representedSmallBaseChange_comp :
    (smallBaseChange B S hS (representedSpaceMap B S hS g) hg ⋙
        smallBaseChange B S hS (representedSpaceMap B S hS h) hh).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T))
      (SmallEtale.topology B S hS (yoneda.obj T'')) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _
    (isContinuous_representedSmallBaseChange B S hS g hg)
    (isContinuous_representedSmallBaseChange B S hS h hh)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **The square of direct images of a representable morphism with the chart comparison
removed.**  The three structural factors of
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`: the direct image along base
change of schemes read on the small étale site of `yoneda.obj T` is the direct image along base
change of charts read there, by
`AlgebraicGeometry.Space.representedStructureMapRing_square`. -/
noncomputable abbrev representedModuleStructuralSquareIso :
    SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g) ⋙
        SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T) ≅
      SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T') ⋙
        SheafOfModules.pushforward.{u}
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) :=
  Stacks.ChartPushforwardSquare.squareIso (representedEquivSharp B S hS T)
    (representedSchemeStructureMapRing B S hS g)
    (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
    (representedEquivSharp B S hS T')
    (representedSmallEtaleBaseChangeIso B S hS g hg)
    (representedStructureMapRing_square B S hS g hg)

/-- **The square of direct images is its structural part followed by the chart comparison.**
This is the definition of `AlgebraicGeometry.Space.representedModulePushforwardSquareIso`,
reassociated so that the three structural factors are grouped. -/
theorem representedModulePushforwardSquareIso_eq :
    representedModulePushforwardSquareIso B S hS g hg =
      representedModuleStructuralSquareIso B S hS g hg ≪≫
        Functor.isoWhiskerLeft ((representedSmallEtaleModuleEquivalence B S hS T').functor)
          (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).symm :=
  ((Iso.trans_assoc _ _ _).trans
    (congrArg (fun z => SheafOfModules.pushforwardComp.{u} (representedEquivSharp B S hS T)
        (representedSchemeStructureMapRing B S hS g) ≪≫ z)
      (Iso.trans_assoc _ _ _))).symm

/-- The contraction of the two direct images of Stacks 03LU along the represented morphisms, at
the morphism represented by the composite.  The transport is
`AlgebraicGeometry.Space.representedSpaceMap_comp`. -/
noncomputable abbrev representedModulePushforwardCompIso :
    modulePushforward B S hS (representedSpaceMap B S hS h) ⋙
        modulePushforward B S hS (representedSpaceMap B S hS g) ≅
      modulePushforward B S hS (representedSpaceMap B S hS (h ≫ g)) :=
  modulePushforwardCompIso B S hS (representedSpaceMap B S hS h)
      (representedSpaceMap B S hS g) ≪≫
    eqToIso (congrArg (modulePushforward B S hS) (representedSpaceMap_comp B S hS h g))

/-- The contraction of the two direct images along base change of schemes: Mathlib's contraction
of an iterated direct image, followed by the reindexing
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardCompIso` of the two successive base changes
with the base change along the composite. -/
noncomputable abbrev representedSchemeModulePushforwardCompIso :
    SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS h) ⋙
        SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g) ≅
      SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS (h ≫ g)) :=
  SheafOfModules.pushforwardComp.{u} (representedSchemeStructureMapRing B S hS g)
      (representedSchemeStructureMapRing B S hS h) ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.smallEtalePushforwardCompIso
      (associatedBigEtaleSite B) h.left g.left).symm

/-! ### The pasting coherence -/

/-- **The structural part of the square pastes.**  Pasting the structural square of `h` against
that of `g` and contracting the two base-change direct images is contracting the two direct
images along base change of schemes and then taking the structural square of `h ≫ g`.

This is `Stacks.ChartPushforwardSquare.pastedSquare_eq` at the represented site; the identity of
the comparison arrows it asks for is
`AlgebraicGeometry.Space.representedSmallEtaleBaseChange_comp_component`. -/
theorem representedModuleStructuralSquareIso_comp :
    Functor.isoWhiskerLeft
          (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS h))
          (representedModuleStructuralSquareIso B S hS g hg) ≪≫
        Functor.isoWhiskerRight (representedModuleStructuralSquareIso B S hS h hh)
          (smallBaseChangeModulePushforward.{u, u} B S hS
            (representedSpaceMap B S hS g) hg) ≪≫
        Functor.isoWhiskerLeft
          (SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T''))
          (smallBaseChangeChartPushforwardFactoredCompIso B S hS
            (representedSpaceMap B S hS h) (representedSpaceMap B S hS g)
            (representedSpaceMap B S hS (h ≫ g)) (representedSpaceMap_comp B S hS h g)
            hh hg hhg) =
      Functor.isoWhiskerRight (representedSchemeModulePushforwardCompIso B S hS h g)
          (SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T)) ≪≫
        representedModuleStructuralSquareIso B S hS (h ≫ g) hhg :=
  Stacks.ChartPushforwardSquare.pastedSquare_eq (representedEquivSharp B S hS T)
    (representedEquivSharp B S hS T') (representedEquivSharp B S hS T'')
    (representedSchemeStructureMapRing B S hS g) (representedSchemeStructureMapRing B S hS h)
    (representedSchemeStructureMapRing B S hS (h ≫ g))
    (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
    (smallBaseChangeSharp B S hS (representedSpaceMap B S hS h) hh)
    (smallBaseChangeSharp B S hS (representedSpaceMap B S hS (h ≫ g)) hhg)
    (representedSmallEtaleBaseChangeIso B S hS g hg)
    (representedSmallEtaleBaseChangeIso B S hS h hh)
    (representedSmallEtaleBaseChangeIso B S hS (h ≫ g) hhg)
    (smallBaseChangeChartFactoredCompIso B S hS (representedSpaceMap B S hS h)
      (representedSpaceMap B S hS g) (representedSpaceMap B S hS (h ≫ g))
      (representedSpaceMap_comp B S hS h g) hh hg hhg)
    (_root_.AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso (associatedBigEtaleSite B)
      T''.left T'.left T.left h.left g.left (h ≫ g).left rfl)
    (representedStructureMapRing_square B S hS g hg)
    (representedStructureMapRing_square B S hS h hh)
    (representedStructureMapRing_square B S hS (h ≫ g) hhg)
    (smallBaseChangeSharp_factoredComparisonComp B S hS (representedSpaceMap B S hS h)
      (representedSpaceMap B S hS g) (representedSpaceMap B S hS (h ≫ g))
      (representedSpaceMap_comp B S hS h g) hh hg hhg)
    (_root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing_comparisonComp
      (associatedBigEtaleSite B) h.left g.left)
    fun V => (Iso.eq_comp_inv (Iso.app
      (_root_.AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso (associatedBigEtaleSite B)
        T''.left T'.left T.left h.left g.left (h ≫ g).left rfl)
      ((representedSmallEtaleEquivalence B S hS T).functor.obj V))).mpr
        (((Category.assoc _ _ _).trans
          (congrArg (fun z => _ ≫ z) (Category.assoc _ _ _))).trans
          (representedSmallEtaleBaseChange_comp_component B S hS h g hh hg hhg V))

/-- **The square of direct images of a representable morphism satisfies the pasting
coherence.**  For `h : T'' ⟶ T'` and `g : T' ⟶ T` of the big fppf category over `S`, pasting the
square of `h` against the square of `g` and contracting the two direct images of Stacks 03LU is
contracting the two direct images along base change of schemes and then taking the square of
`h ≫ g`.

Each square is its structural part followed by the chart comparison of the direct image of
Stacks 03LU, so the coherence is
`AlgebraicGeometry.Space.representedModuleStructuralSquareIso_comp` for the structural parts and
`AlgebraicGeometry.Space.modulePushforwardChartIso_factoredComp` for the chart comparisons, put
together by `Stacks.ChartPushforwardSquare.pasteWithCorrection`. -/
theorem representedModulePushforwardSquareIso_comp :
    Functor.isoWhiskerLeft
          (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS h))
          (representedModulePushforwardSquareIso B S hS g hg) ≪≫
        Functor.isoWhiskerRight (representedModulePushforwardSquareIso B S hS h hh)
          (modulePushforward B S hS (representedSpaceMap B S hS g)) ≪≫
        Functor.isoWhiskerLeft
          ((representedSmallEtaleModuleEquivalence B S hS T'').functor)
          (representedModulePushforwardCompIso B S hS h g) =
      Functor.isoWhiskerRight (representedSchemeModulePushforwardCompIso B S hS h g)
          ((representedSmallEtaleModuleEquivalence B S hS T).functor) ≪≫
        representedModulePushforwardSquareIso B S hS (h ≫ g) hhg := by
  rw [representedModulePushforwardSquareIso_eq B S hS g hg,
    representedModulePushforwardSquareIso_eq B S hS h hh,
    representedModulePushforwardSquareIso_eq B S hS (h ≫ g) hhg]
  exact Stacks.ChartPushforwardSquare.pasteWithCorrection
    (representedModuleStructuralSquareIso B S hS g hg)
    (representedModuleStructuralSquareIso B S hS h hh)
    (representedModuleStructuralSquareIso B S hS (h ≫ g) hhg)
    (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg)
    (modulePushforwardChartIso B S hS (representedSpaceMap B S hS h) hh)
    (modulePushforwardChartIso B S hS (representedSpaceMap B S hS (h ≫ g)) hhg)
    (representedSchemeModulePushforwardCompIso B S hS h g)
    _
    (representedModulePushforwardCompIso B S hS h g)
    (representedModuleStructuralSquareIso_comp B S hS h g hh hg hhg)
    (modulePushforwardChartIso_factoredComp B S hS _ _ _
      (representedSpaceMap_comp B S hS h g) hh hg hhg)

end Represented

end AlgebraicGeometry.Space

end
