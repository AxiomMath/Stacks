module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackBigSitesMixed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.QuasiCoherentPullback
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSectionsSheafTauBigSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The associated module commutes with pullback along `f_sites : (Sch/X)_τ ⟶ Y_étale`

Topologies, Section 03FE lists twenty-seven morphisms of sites, and Remark 070R makes each of
them a morphism of ringed sites.  Four of the twenty-seven go from a big site of `X` to the
small étale site of `Y`:

`(Sch/X)_fppf ⟶ Y_étale`, `(Sch/X)_syntomic ⟶ Y_étale`,
`(Sch/X)_smooth ⟶ Y_étale`, `(Sch/X)_étale ⟶ Y_étale`,

entries (16) to (19) of the list.  **This file proves Stacks 03FH (2) for those four.**  There
is no `(Sch/X)_Zar ⟶ Y_étale` on the list, and none is proved here: the big Zariski topology
does not refine the étale one, so the identity functor `(Sch/X)_Zar → (Sch/X)_étale` is not a
morphism of sites and the composite does not exist.

## What `f_sites` is here

Section 03FE builds these four by composing the two factorizations it already has,

`(Sch/X)_τ --id_{τ,étale}--> X_étale --ε_f--> Y_étale`,

and 03FH's proof of clause (2) is "(1) and the fact that pullbacks are compatible with
compositions of morphisms of ringed sites, Modules on Sites, Lemma 03D8".  So `f_sites^*` is
`AlgebraicGeometry.BigFppfOver.smallEtaleMixedPullback`: the pullback along
`ε_f : X_étale ⟶ Y_étale`, which is `SheafOfModules.pullback` of
`AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing`, followed by the pullback along
`id_{τ,étale} : (Sch/X)_τ ⟶ X_étale`, which is
`AlgebraicGeometry.BigFppfOver.smallEtaleToBaseModulePullback`.  Both factors are pullbacks
along a single morphism of ringed sites, built where they belong; the ringed-site morphism
itself is `AlgebraicGeometry.BigFppfSite.bigToSmallEtaleRingedSiteHom`, which carries
`@[stacks 070R "entries (16)-(19)"]`.

## The hypothesis

The one hypothesis is that the inclusion of the small étale site of `X` is continuous into the
`τ`-localized topology of the big category over `X`.  That is exactly the assertion that
`id_{τ,étale}` is a morphism of sites, which is Section 03FE's own condition for entries (16)
to (19) to be on its list, and it is what distinguishes those four `τ` from `τ = Zariski`.  It
is an instance at each of the four: at `τ = étale` and `τ = fppf` it is already
`AlgebraicGeometry.BigFppfOver.isContinuous_smallEtaleInclusion_etale` and
`.isContinuous_smallEtaleInclusion_fppf`, and this file adds the two in between from
`AlgebraicGeometry.BigFppfOver.isContinuous_smallEtaleToFppf_of_etaleTopology_le` and the
inequalities of
`StacksFrontier/AlgebraicGeometry/Topologies/Fppf/ChosenCoveringsComparison.lean`.

Those four are stated for a scheme with a containment hypothesis, which is not the spelling the
clause below is stated at, and instance search does not bridge the two (see the implementation
note); so each is restated for an object of the big étale category carried by `B`, as
`AlgebraicGeometry.BigFppfOver.isContinuous_smallEtaleInclusion_obj_etale` and its three
siblings.  With those the four entries are instances of the clause with nothing left to
supply: `associatedModuleSmallEtaleMixedPullbackIso B a .etale` and its values at `.smooth`,
`.syntomic` and `.fppf` elaborate with no argument beyond `B` and `a`.

Nothing is assumed of the module, and nothing of `X ⟶ Y` beyond its being a morphism of the
chosen big étale category — the parameterization
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` already uses, that being the
carrier of the clause for `ε_f`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.smallEtaleMixedPullback`: `f_sites^*` for
  `f_sites : ((Sch/X)_τ, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)`.
* `AlgebraicGeometry.BigFppfOver.associatedModuleSmallEtaleMixedPullbackIso` and
  `AlgebraicGeometry.BigFppfOver.associatedModuleSmallEtaleMixedObjPullbackIso`:
  **Stacks 03FH (2)** for that `f_sites`, as functors and at one module.
* `AlgebraicGeometry.BigFppfOver.baseSmallEtaleIsoSectionsSmooth` and
  `AlgebraicGeometry.BigFppfOver.baseSmallEtaleIsoSectionsSyntomic`: **Stacks 070S part (3)** at
  the two topologies of its range for which the continuity hypothesis only becomes available
  here, completing `τ ∈ {étale, smooth, syntomic, fppf}`.  They carry no `stacks` attribute, a
  statement at a single `τ` being narrower than the clause; the tag sits on
  `AlgebraicGeometry.BigFppfOver.baseSmallEtalePullbackIsoSectionsSheafification`, whose
  statement is the source's.

## Main results

* `AlgebraicGeometry.BigFppfOver.isContinuous_smallEtaleInclusion_smooth` and
  `.isContinuous_smallEtaleInclusion_syntomic`: the two missing instances of the hypothesis.
* `AlgebraicGeometry.BigFppfOver.isContinuous_smallEtaleInclusion_obj_etale`,
  `.isContinuous_smallEtaleInclusion_obj_smooth`,
  `.isContinuous_smallEtaleInclusion_obj_syntomic` and
  `.isContinuous_smallEtaleInclusion_obj_fppf`: the four, restated for an object of the big
  étale category carried by `B`, which is the spelling instance search needs to discharge the
  hypothesis of the clause.

## Implementation notes

The proof is the source's, in the shape
`AlgebraicGeometry.BigFppfOver.associatedModuleBaseMixedPullbackIso` uses for the mixed big
pairs: whisker the factorization of the associated-module functor through the small étale site,
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSmallEtalePullback`, against the clause
for `ε_f`, `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`, and reassociate.
Neither input is new; what was missing was the composite, and the two continuity instances that
make it exist at `τ = smooth` and `τ = syntomic`.

The schemes are taken as objects `X Y : B.toBigEtaleSite.Scheme` and the morphism as
`a : X ⟶ Y` rather than as schemes with containment hypotheses and a morphism of schemes.  The
two are interchangeable — `B.toBigEtaleSite.Contains` is `B.Contains` by `rfl`, the object is
`CategoryTheory.ObjectProperty.homMk` of the morphism, and
`AlgebraicGeometry.SmallEtale.schemeHom` recovers it — but the spellings `X.obj` and
`X.property` are the ones the small étale base-change continuity instance
`AlgebraicGeometry.smallEtaleBaseChange_isContinuous` is stated at, and instance search does
not unfold `AlgebraicGeometry.BigEtaleSite.obj` to match the other form.

The same non-unfolding is why the four continuity instances have to be restated here.
`X.property` has type `B.toBigEtaleSite.Contains X.obj`, and the four are stated over a
`hS : B.Contains S`; the two types are the same by `rfl`, so each of the four *applies* when it
is written out, but reaching that `rfl` needs more transparency than instance search allows, and
without the restatements the hypothesis of the clause is found by no search and every use has to
supply it by hand.

## What this file does not claim

Of the twenty-seven entries of Section 03FE, five go from a big site to the small *Zariski*
site, `(Sch/X)_τ ⟶ Y_{Zar}`, and one is the mixed small pair `X_étale ⟶ Y_{Zar}`.  No statement
here is about those; they are entries (20) to (24) and (26), and
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModulePullbackToSmallZariski.lean` proves the
clause for them.

## References

* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### `id_{τ,étale}` is a morphism of sites at each of the four `τ` -/

/-- The inclusion of the small étale site of `S` is continuous into the smooth member of the
five localized topologies, the big smooth topology refining the big étale one.  This is the
assertion that `id_{smooth, étale} : (Sch/S)_smooth ⟶ S_étale` is a morphism of sites. -/
public instance isContinuous_smallEtaleInclusion_smooth :
    (smallEtaleToFppf B S hS).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite S hS) (baseOverTopology B S hS .smooth) :=
  isContinuous_smallEtaleToFppf_of_etaleTopology_le B S hS .smooth
    B.etaleTopology_le_smoothTopology

/-- The inclusion of the small étale site of `S` is continuous into the syntomic member of the
five localized topologies.  This is the assertion that
`id_{syntomic, étale} : (Sch/S)_syntomic ⟶ S_étale` is a morphism of sites. -/
public instance isContinuous_smallEtaleInclusion_syntomic :
    (smallEtaleToFppf B S hS).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite S hS) (baseOverTopology B S hS .syntomic) :=
  isContinuous_smallEtaleToFppf_of_etaleTopology_le B S hS .syntomic
    (B.etaleTopology_le_smoothTopology.trans B.smoothTopology_le_syntomicTopology)

/-! ### The same four instances, at the spelling the clause below is stated at

The four instances above are stated for a scheme `S` with a containment `hS : B.Contains S`.
The clause below is stated for an object `X` of the big étale category carried by `B`, where the
containment enters as `X.property`, of type `B.toBigEtaleSite.Contains X.obj`.  The two types
agree by `rfl` — so each of the four instances above *applies*, written out by hand — but not at
the transparency instance search works at, so search does not find them there and the
hypothesis of the clause would be left for every consumer to supply.  These four restate them at
that spelling, in the same way and for the same reason as
`AlgebraicGeometry.BigFppfOver.essentiallySmall_smallEtaleOfBigFppf` and
`AlgebraicGeometry.BigFppfOver.isContinuous_opensToSmallEtaleOfBigFppf` restate theirs.  With
them the clause below is an unconditional statement at each of the four `τ`. -/

/-- `id_{étale, étale}` is a morphism of sites, for an object of the big étale category carried
by `B`. -/
@[sga "4 VII 4.0" "partial"]
public instance isContinuous_smallEtaleInclusion_obj_etale (X : B.toBigEtaleSite.Scheme) :
    (smallEtaleToFppf B X.obj X.property).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite X.obj X.property)
      (baseOverTopology B X.obj X.property .etale) :=
  isContinuous_smallEtaleInclusion_etale B X.obj X.property

/-- `id_{smooth, étale}` is a morphism of sites, for an object of the big étale category carried
by `B`. -/
public instance isContinuous_smallEtaleInclusion_obj_smooth (X : B.toBigEtaleSite.Scheme) :
    (smallEtaleToFppf B X.obj X.property).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite X.obj X.property)
      (baseOverTopology B X.obj X.property .smooth) :=
  isContinuous_smallEtaleInclusion_smooth B X.obj X.property

/-- `id_{syntomic, étale}` is a morphism of sites, for an object of the big étale category
carried by `B`. -/
public instance isContinuous_smallEtaleInclusion_obj_syntomic (X : B.toBigEtaleSite.Scheme) :
    (smallEtaleToFppf B X.obj X.property).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite X.obj X.property)
      (baseOverTopology B X.obj X.property .syntomic) :=
  isContinuous_smallEtaleInclusion_syntomic B X.obj X.property

/-- `id_{fppf, étale}` is a morphism of sites, for an object of the big étale category carried
by `B`. -/
public instance isContinuous_smallEtaleInclusion_obj_fppf (X : B.toBigEtaleSite.Scheme) :
    (smallEtaleToFppf B X.obj X.property).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite X.obj X.property)
      (baseOverTopology B X.obj X.property .fppf) :=
  isContinuous_smallEtaleInclusion_fppf B X.obj X.property

/-! ### Stacks 070S part (3) at the two remaining topologies

`AlgebraicGeometry.BigFppfOver.baseSmallEtalePullbackIsoSectionsSheafification` states
Stacks 070S part (3) over the source's own range of `τ`, namely those refining the étale
topology, and `AlgebraicGeometry.BigFppfOver.baseSmallEtaleIsoSectionsEtale` and
`.baseSmallEtaleIsoSectionsFppf` are its instances at the two ends of that range.  The two in
between are only available once the continuity of the inclusion of the small étale site is, so
they are here rather than there: with the instances above, part (3) at `τ = smooth` and
`τ = syntomic` carries no hypothesis either, and the four entries of the clause's range are
each unconditional. -/

variable (𝓖 : SheafOfModules.{u} (SmallEtale.structureSheaf B.toBigEtaleSite S hS))

/-- **Stacks 070S part (3) at `τ = smooth`**: the instance of
`AlgebraicGeometry.BigFppfOver.baseSmallEtalePullbackIsoSectionsSheafification` at the smooth
member of the clause's range, where the hypothesis on `τ` is
`AlgebraicGeometry.BigFppfSite.etaleTopology_le_smoothTopology` and the continuity of the
inclusion of the small étale site is
`AlgebraicGeometry.BigFppfOver.isContinuous_smallEtaleInclusion_smooth`. -/
public noncomputable def baseSmallEtaleIsoSectionsSmooth :
    (smallEtaleToBaseModulePullback B S hS .smooth).obj 𝓖 ≅
      (PresheafOfModules.sheafification.{u}
          (𝟙 (FibredSite.baseRingStructureSheaf B S hS .smooth).obj)).obj
        (smallEtaleSectionsPresheafOfModules B S hS .smooth 𝓖) :=
  baseSmallEtalePullbackIsoSectionsSheafification B S hS .smooth 𝓖
    B.etaleTopology_le_smoothTopology

/-- **Stacks 070S part (3) at `τ = syntomic`**: the instance of
`AlgebraicGeometry.BigFppfOver.baseSmallEtalePullbackIsoSectionsSheafification` at the syntomic
member of the clause's range, where the hypothesis on `τ` is
`AlgebraicGeometry.BigFppfSite.etaleTopology_le_smoothTopology` composed with
`.smoothTopology_le_syntomicTopology` and the continuity of the inclusion of the small étale
site is `AlgebraicGeometry.BigFppfOver.isContinuous_smallEtaleInclusion_syntomic`. -/
public noncomputable def baseSmallEtaleIsoSectionsSyntomic :
    (smallEtaleToBaseModulePullback B S hS .syntomic).obj 𝓖 ≅
      (PresheafOfModules.sheafification.{u}
          (𝟙 (FibredSite.baseRingStructureSheaf B S hS .syntomic).obj)).obj
        (smallEtaleSectionsPresheafOfModules B S hS .syntomic 𝓖) :=
  baseSmallEtalePullbackIsoSectionsSheafification B S hS .syntomic 𝓖
    (B.etaleTopology_le_smoothTopology.trans B.smoothTopology_le_syntomicTopology)

/-! ### `f_sites^*` for `f_sites : (Sch/X)_τ ⟶ Y_étale` -/

section Mixed

variable {X Y : B.toBigEtaleSite.Scheme} (a : X ⟶ Y) (τ : SiteKind)
  [(smallEtaleToFppf B X.obj X.property).IsContinuous
    (SmallEtale.topology B.toBigEtaleSite X.obj X.property)
    (baseOverTopology B X.obj X.property τ)]

/-- **`f_sites^*` for `f_sites : ((Sch/X)_τ, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)`.**  Topologies,
Section 03FE builds that morphism of sites as the composite

`(Sch/X)_τ --id_{τ,étale}--> X_étale --ε_f--> Y_étale`,

so its pullback of sheaves of modules is the composite of their pullbacks in the opposite
order, by Modules on Sites, Lemma 03D8: first `ε_f^*`, the pullback along
`AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing`, then
`AlgebraicGeometry.BigFppfOver.smallEtaleToBaseModulePullback`, the pullback along
`id_{τ,étale}`.  The ringed-site morphism itself is
`AlgebraicGeometry.BigFppfSite.bigToSmallEtaleRingedSiteHom`. -/
public abbrev smallEtaleMixedPullback :=
  SheafOfModules.pullback.{u} (SmallEtale.smallEtaleStructureMapRing B.toBigEtaleSite a) ⋙
    smallEtaleToBaseModulePullback B X.obj X.property τ

/-- **Stacks 03FH, part (2), for the morphisms of ringed sites
`f_sites : ((Sch/X)_τ, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` of Remark 070R** — entries (16) to (19) of the
list of Topologies, Section 03FE, at `τ ∈ {étale, smooth, syntomic, fppf}`.  The associated
module of a pullback is the pullback of the associated module,

`(f^*𝓕)^a ≅ f_sites^*(𝓕^a)`,

naturally in the `𝒪_Y`-module `𝓕`, with `𝓕^a` the associated module on the small étale site of
`Y` and `(f^*𝓕)^a` the associated module on the big `τ`-site of `X`.

The hypothesis is that the inclusion of the small étale site of `X` is continuous into the
`τ`-localized topology, which is Section 03FE's own condition for these entries to be on its
list — `id_{τ,étale}` being a morphism of sites — and is an instance at each of the four `τ`,
found by search at this spelling as
`AlgebraicGeometry.BigFppfOver.isContinuous_smallEtaleInclusion_obj_etale`,
`.isContinuous_smallEtaleInclusion_obj_smooth`, `.isContinuous_smallEtaleInclusion_obj_syntomic`
and `.isContinuous_smallEtaleInclusion_obj_fppf`.  So this is an unconditional statement at each
of the four.  It fails for `τ = Zariski`, which is why the list has four such entries and not
five.  Nothing is assumed of `𝓕`.

The proof is the source's: `f_sites` is `ε_f ∘ id_{τ,étale}`, so `f_sites^*` is
`id_{τ,étale}^* ∘ ε_f^*` by Lemma 03D8, and then

`(f^*𝓕)^a_{(Sch/X)_τ} ≅ id_{τ,étale}^*((f^*𝓕)^a_{X_étale})
  ≅ id_{τ,étale}^*(ε_f^*(𝓕^a_{Y_étale}))`,

the first step being the factorization
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSmallEtalePullback` of the
associated-module functor of `(Sch/X)_τ` through the small étale site, and the second the
clause for `ε_f`, `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`.

The clause for the single morphism of ringed sites registered for Remark 070R, on the big sites
carried by the chosen big fppf site, is
`AlgebraicGeometry.BigFppfSite.associatedModuleBigToSmallEtaleRingedSiteHomPullbackIso`; this
declaration states it for the pullback written out above and carries no `stacks` attribute. -/
public def associatedModuleSmallEtaleMixedPullbackIso :
    Scheme.Modules.pullback (SmallEtale.schemeHom B.toBigEtaleSite a) ⋙
        baseAssociatedModule B X.obj X.property τ ≅
      SmallEtale.associatedModule B.toBigEtaleSite Y.obj Y.property ⋙
        smallEtaleMixedPullback B a τ :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback (SmallEtale.schemeHom B.toBigEtaleSite a))
      (baseAssociatedModuleIsoSmallEtalePullback B X.obj X.property τ).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (SmallEtale.associatedModuleBaseChangeIso B.toBigEtaleSite a)
      (smallEtaleToBaseModulePullback B X.obj X.property τ) ≪≫
    Functor.associator _ _ _

/-- **Stacks 03FH, part (2), at one module**, for the morphisms of ringed sites
`f_sites : ((Sch/X)_τ, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` of Remark 070R — entries (16) to (19) of the
Section 03FE list: `(f^*𝓕)^a ≅ f_sites^*(𝓕^a)`, read off from
`AlgebraicGeometry.BigFppfOver.associatedModuleSmallEtaleMixedPullbackIso`.

The clause for the single morphism of ringed sites registered for Remark 070R, on the big sites
carried by the chosen big fppf site, is
`AlgebraicGeometry.BigFppfSite.associatedModuleBigToSmallEtaleRingedSiteHomPullbackIso`; this
declaration states it for the pullback written out above and carries no `stacks` attribute. -/
public def associatedModuleSmallEtaleMixedObjPullbackIso (𝓕 : Y.obj.Modules) :
    (baseAssociatedModule B X.obj X.property τ).obj
        ((Scheme.Modules.pullback (SmallEtale.schemeHom B.toBigEtaleSite a)).obj 𝓕) ≅
      (smallEtaleMixedPullback B a τ).obj
        ((SmallEtale.associatedModule B.toBigEtaleSite Y.obj Y.property).obj 𝓕) :=
  (associatedModuleSmallEtaleMixedPullbackIso B a τ).app 𝓕

end Mixed

end AlgebraicGeometry.BigFppfOver

end
