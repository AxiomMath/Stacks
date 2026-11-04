module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseAssociatedModuleTensor
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.RingedChangeOfTopologiesList
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteHomGeneralPullbackComp
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.TopologicalComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The associated module commutes with pullback along the `f_sites` landing in `Y_Zar`

Topologies, Section 03FE lists twenty-seven morphisms of sites and Remark 070R makes each of
them a morphism of ringed sites.  Six of the twenty-seven land in the **small Zariski site** of
`Y`: the five

`(Sch/X)_fppf ⟶ Y_Zar`, `(Sch/X)_syntomic ⟶ Y_Zar`, `(Sch/X)_smooth ⟶ Y_Zar`,
`(Sch/X)_étale ⟶ Y_Zar`, `(Sch/X)_Zar ⟶ Y_Zar`,

which are entries (20) to (24) of the list, and the mixed small pair `X_étale ⟶ Y_Zar`, which is
entry (26).  **This file proves Stacks 03FH (2) for those six.**

## What clause (2) says at these entries

Clause (2) of Remark 03FH reads `(f^*𝓕)^a = f_sites^*(𝓕^a)` for an `𝒪_Y`-module `𝓕`.  The
*target* of each of these six `f_sites` is the ringed site `(Y_Zar, 𝒪_Y)` itself, and clause (1)
of the same remark identifies `𝓕 ↦ 𝓕^a` there with the pullback under
`id_{small, Zar, Zar} : (Y_Zar, 𝒪) ⟶ (Y_Zar, 𝒪_Y)`, which is the identity reading.  So `𝓕^a` is
`𝓕` and the clause reads

`(f^*𝓕)^a ≅ f_sites^*𝓕`,

with `(f^*𝓕)^a` the associated module of the *source* site — the big `τ`-site of `X` for entries
(20) to (24), the small étale site of `X` for entry (26).

## `f_sites^*` is the pullback along the single morphism

Section 03FE obtains these six by composing the generators it has already constructed; for
entries (20) to (24) its two factorizations are

`(Sch/X)_τ --id_{τ,Zar}--> X_Zar --f_small,Zar--> Y_Zar` and
`(Sch/X)_τ --f_big--> (Sch/Y)_Zar --π_Y--> Y_Zar`,

which have the same underlying continuous functor, and for entry (26) it is
`X_étale --f_small--> Y_étale --id_{small,étale,Zar}--> Y_Zar`.

In each of the six statements below `f_sites^*` is
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesGeneral` of the **single** morphism of
ringed sites, that is `SheafOfModules.pullback` of its own structure map, characterised as the
left adjoint of the pushforward along its own continuous functor.  It is *not* the composite of
the two factors' pullbacks, and for entries (20) to (24) that distinction is the whole content:
in this development `id_{τ,Zar}^*` **is** `AlgebraicGeometry.BigFppfOver.baseAssociatedModule`
and `f_small,Zar^*` **is** `AlgebraicGeometry.Scheme.Modules.pullback f`, each by `rfl`, so over
the composite the two sides of the clause are the same functor and the statement would assert
nothing.  Over the single morphism it is Modules on Sites, Lemma 03D8 —
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesGeneralCompIso` — which is exactly the
proof Remark 03FH gives for clause (2): "this follows from (1) and the fact that pullbacks are
compatible with compositions of morphisms of ringed sites".

## The hypotheses

There are none beyond the ambient data.  Section 03FE's own condition for entries (20) to (24)
to be on its list is that `τ` be a stronger topology than the Zariski one, and that holds for
every one of the five, so the statement is uniform in `τ : SiteKind`; for entry (26) the étale
topology is likewise always finer than the Zariski one.  Nothing is assumed of `𝓕` — no
quasi-coherence — and nothing of `f` beyond `X` lying in the chosen big site.  For entries (20)
to (24) even `Y` is unconstrained: the target site is the site of opens of the space of `Y` with
`𝒪_Y`, which does not refer to the chosen big site at all.

## Which presentation of `Y_Zar`

Entry (26) is stated at its registered morphism,
`AlgebraicGeometry.smallEtaleToSmallZariskiRingedSiteHom`, whose target already is
`AlgebraicGeometry.Scheme.zariskiRingedSite`, the opens presentation.

Entries (20) to (24) are stated at
`AlgebraicGeometry.BigFppfOver.bigToSmallZariskiOpensRingedSiteHom`, the same composite of the
same two generators built in the opens presentation of both small Zariski sites.  The registered
`AlgebraicGeometry.BigFppfSite.bigToSmallZariskiRingedSiteHom` takes the other presentation on
both sides: its target is `AlgebraicGeometry.smallZariskiRingedSite`, the small Zariski site
presented by the Zariski-local schemes over `Y`, and its source is
`AlgebraicGeometry.BigFppfSite.carriedOverRingedSite`, whose topology is
`AlgebraicGeometry.BigFppfOver.baseOverTopology` for `τ = fppf` on the nose and for the other
four only up to the equalities
`AlgebraicGeometry.BigFppfSite.bigZariskiOver_topology_toBigZariskiSite` and its three siblings.
Clause (2) is a statement about `𝒪_Y`-modules, and `AlgebraicGeometry.Scheme.Modules.pullback`,
`AlgebraicGeometry.BigFppfOver.baseAssociatedModule` and the twenty-one entries already proved
are all stated over the opens presentation, which is why it is the one used here.  The two
presentations of the small Zariski site are compared by Topologies, Lemma 020X, which Stacks
03FG records, and the comparison of their categories of modules is
`AlgebraicGeometry.SmallZariski.associatedModule`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.zariskiRingedSiteHom`: `f_small,Zar` of Remark 070R part (2) in
  the opens presentation, `(X_Zar, 𝒪_X) ⟶ (Y_Zar, 𝒪_Y)`.
* `AlgebraicGeometry.BigFppfOver.bigToSmallZariskiOpensRingedSiteHom`: entries (20) to (24) of
  the Section 03FE list as one morphism of ringed sites `((Sch/X)_τ, 𝒪_X) ⟶ (Y_Zar, 𝒪_Y)`.
* `AlgebraicGeometry.BigFppfOver.associatedModuleBigToSmallZariskiPullbackIso` and
  `.associatedModuleBigToSmallZariskiObjPullbackIso`: **Stacks 03FH (2) for entries (20) to
  (24)**, as functors and at one module.
* `AlgebraicGeometry.SmallEtale.associatedModuleSmallEtaleToSmallZariskiPullbackIso` and
  `.associatedModuleSmallEtaleToSmallZariskiObjPullbackIso`: **Stacks 03FH (2) for entry (26)**,
  as functors and at one module.

## Implementation notes

`AlgebraicGeometry.Scheme.Hom.zariskiRingedSiteHom` is the inverse image of opens together with
`f^♯ : 𝒪_Y ⟶ f_*𝒪_X`.  That the inverse image of opens defines a morphism of sites is
`StacksZariskiSite.isMorphismOfSites_opensMap`, Stacks 00X2, read at the universe of the
structure rings through
`CategoryTheory.Functor.IsMorphismOfSites.toIsMorphismOfSites` — the two sites are genuinely
small there, so the chosen sheaf pullback is itself the left exact left adjoint the unrestricted
condition asks for.  Its structure map is the term
`AlgebraicGeometry.Scheme.Hom.zariskiSharp` of
`StacksFrontier/Cotangent/SchemeCotangentComplex.lean`, written out rather than imported so that
this file does not depend on the cotangent-complex development.

The pullback of modules along it is `AlgebraicGeometry.Scheme.Modules.pullback f` by `rfl`: the
structure map read on sheaves of not necessarily commutative rings is
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`, and both functors are
`SheafOfModules.pullback` of it.  This is the identification
`AlgebraicGeometry.SmallZariski.schemeModulesPullback_eq` already records in the other
presentation.

The two clauses then reduce to inputs that are already available: for entries (20) to (24) to
nothing at all beyond Lemma 03D8, both factors of the composite being the two functors the
clause compares, and for entry (26) to Lemma 03D8 together with the clause for `f_small` on the
small étale sites, `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`, which is entry
(25).

## What this file does not claim

Nothing here is a statement about the other twenty-one entries of the Section 03FE list.  Those
are `AlgebraicGeometry.BigFppfOver.associatedModuleBasePullbackIso` and
`.associatedModuleBaseMixedPullbackIso` for the fifteen big-to-big entries,
`.associatedModuleSmallEtaleMixedPullbackIso` for entries (16) to (19),
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` for entry (25) and
`AlgebraicGeometry.SmallZariski.lcAssociatedModulePullbackIso` for entry (27).

## References

* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
* [Stacks Project, Tag 03FG](https://stacks.math.columbia.edu/tag/03FG)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 00X2](https://stacks.math.columbia.edu/tag/00X2)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### `f_small,Zar` in the opens presentation -/

/-- **`f_small,Zar` of Remark 070R part (2), in the opens presentation of the small Zariski
sites.**  A morphism of schemes `f : X ⟶ Y` as a morphism of ringed sites

```
  (f_small, f_small^♯) : (X_Zar, 𝒪_X) ⟶ (Y_Zar, 𝒪_Y),
```

the underlying morphism of sites being the inverse image of opens `V ↦ f^{-1}(V)` and the
structure map `f^♯ : 𝒪_Y ⟶ f_*𝒪_X` the one of the morphism of schemes.

No `stacks` attribute is attached: 070R part (2) for the small Zariski sites, which is entry
(27) of the Topologies, Section 03FE list, is registered on
`AlgebraicGeometry.smallZariskiRingedSiteHom`, over the presentation of the small Zariski site
by the Zariski-local schemes over the base.  This is the same morphism of ringed sites in the
presentation by the opens of the space, which is where the `𝒪_Y`-modules of Remark 03FH live. -/
public def Scheme.Hom.zariskiRingedSiteHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RingedSite.HomGeneral X.zariskiRingedSite Y.zariskiRingedSite where
  u := Opens.map f.base
  isMorphismOfSites := (StacksZariskiSite.isMorphismOfSites_opensMap f.base).toIsMorphismOfSites
  fsharp := ObjectProperty.homMk f.c

/-- The functor of sites underlying `f.zariskiRingedSiteHom` is the inverse image of opens
`Opens.map f.base`. -/
@[simp]
public theorem Scheme.Hom.zariskiRingedSiteHom_u {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.zariskiRingedSiteHom.u = Opens.map f.base := rfl

/-- **`f_small,Zar^* = f^*`.**  The pullback of sheaves of modules along the morphism of ringed
sites of the small Zariski sites in the opens presentation is pullback of `𝒪_Y`-modules along
the morphism of schemes.  It holds by `rfl`: the structure map of
`AlgebraicGeometry.Scheme.Hom.zariskiRingedSiteHom`, read on sheaves of not necessarily
commutative rings, is `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`, and both functors are
`SheafOfModules.pullback` of it. -/
public theorem Scheme.Hom.pullbackModulesGeneral_zariskiRingedSiteHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.zariskiRingedSiteHom.pullbackModulesGeneral = Scheme.Modules.pullback f := rfl

/-! ### Entries (20)–(24): `(Sch/X)_τ ⟶ Y_Zar` -/

namespace BigFppfOver

variable (B : BigFppfSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (f : X ⟶ Y)
  (τ : SiteKind)

/-- **Entries (20) to (24) of the Topologies, Section 03FE list as one morphism of ringed
sites**, in the opens presentation of the small Zariski site of `Y`:

```
  f_sites : ((Sch/X)_τ, 𝒪_X) ⟶ (Y_Zar, 𝒪_Y)
```

at each of `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.  It is Section 03FE's second
factorization of these entries, the composite

`(Sch/X)_τ --id_{τ,Zar}--> X_Zar --f_small,Zar--> Y_Zar`,

of the comparison `id_{τ,Zar}` of Stacks 070U — `AlgebraicGeometry.BigFppfOver`
`.baseToZariskiRingedSiteHom`, the morphism Remark 03FH part (1) is about — with
`AlgebraicGeometry.Scheme.Hom.zariskiRingedSiteHom`, and the composition of morphisms of ringed
sites is Stacks 03AD part (3).  Its underlying continuous functor is `V ↦ f^{-1}(V)/X`, which is
the functor `Y'/Y ↦ X ×_Y Y'/X` of Remark 070R read at an open of `Y`.

No `stacks` attribute is attached: 070R for these five entries is registered on
`AlgebraicGeometry.BigFppfSite.bigToSmallZariskiRingedSiteHom`, which is the same composite in
the other presentation of the two small Zariski sites; see the module's implementation notes. -/
public def bigToSmallZariskiOpensRingedSiteHom :
    RingedSite.HomGeneral (baseRingedSite B X hX τ) Y.zariskiRingedSite :=
  (baseToZariskiRingedSiteHom B X hX τ).comp f.zariskiRingedSiteHom

/-- **Stacks 03FH, part (2), for the morphisms of ringed sites
`f_sites : ((Sch/X)_τ, 𝒪_X) ⟶ (Y_Zar, 𝒪_Y)` of Remark 070R** — entries (20) to (24) of the list
of Topologies, Section 03FE, at each of `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.  The
associated module of a pullback is the pullback of the associated module,

`(f^*𝓕)^a ≅ f_sites^*𝓕`,

naturally in the `𝒪_Y`-module `𝓕`, with `(f^*𝓕)^a` the associated module on the big `τ`-site of
`X`.  The target of `f_sites` is the ringed site `(Y_Zar, 𝒪_Y)` itself, so the `𝓕^a` of the
source's formulation is `𝓕`: on the target, clause (1) of the same remark is the identity
reading `id_{small, Zar, Zar}`.

There is no hypothesis.  Section 03FE's own condition for these entries to be on its list is
that `τ` be a stronger topology than the Zariski one, which holds at every one of the five, so
the statement is uniform in `τ`.  Nothing is assumed of `𝓕`, and nothing of `f` beyond `X` lying
in the chosen big fppf site.

`f_sites^*` here is the pullback of sheaves of modules along the single morphism of ringed sites
`AlgebraicGeometry.BigFppfOver.bigToSmallZariskiOpensRingedSiteHom`, that is
`SheafOfModules.pullback` of its own structure map; the two functors on the left are the
pullbacks along its two factors, and the isomorphism is Modules on Sites, Lemma 03D8 for that
composite, `AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesGeneralCompIso`.  That is the
proof Remark 03FH gives: clause (1) for each factor, and compatibility of pullbacks with
composition.  Both factors are pullbacks along a single morphism of ringed sites already:
`id_{τ,Zar}^*` is `AlgebraicGeometry.BigFppfOver.baseAssociatedModule` and `f_small,Zar^*` is
`AlgebraicGeometry.Scheme.Modules.pullback f`, by
`AlgebraicGeometry.BigFppfOver.pullbackToposGeneral_baseToZariskiRingedToposHom` and
`AlgebraicGeometry.Scheme.Hom.pullbackModulesGeneral_zariskiRingedSiteHom`.

The clause for the single morphism of ringed sites registered for Remark 070R, on the big sites
carried by the chosen big fppf site, is
`AlgebraicGeometry.BigFppfSite.associatedModuleBigToSmallZariskiRingedSiteHomPullbackIso`; this
declaration states it for the pullback written out above and carries no `stacks` attribute. -/
public def associatedModuleBigToSmallZariskiPullbackIso :
    Scheme.Modules.pullback f ⋙ baseAssociatedModule B X hX τ ≅
      (bigToSmallZariskiOpensRingedSiteHom B hX f τ).pullbackModulesGeneral :=
  ((baseToZariskiRingedSiteHom B X hX τ).pullbackModulesGeneralCompIso
    f.zariskiRingedSiteHom).symm

/-- **Stacks 03FH, part (2), at one module**, for the morphisms of ringed sites
`f_sites : ((Sch/X)_τ, 𝒪_X) ⟶ (Y_Zar, 𝒪_Y)` of Remark 070R — entries (20) to (24) of the
Section 03FE list: `(f^*𝓕)^a ≅ f_sites^*𝓕`, read off from
`AlgebraicGeometry.BigFppfOver.associatedModuleBigToSmallZariskiPullbackIso`.

The clause for the single morphism of ringed sites registered for Remark 070R, on the big sites
carried by the chosen big fppf site, is
`AlgebraicGeometry.BigFppfSite.associatedModuleBigToSmallZariskiRingedSiteHomPullbackIso`; this
declaration states it for the pullback written out above and carries no `stacks` attribute. -/
public def associatedModuleBigToSmallZariskiObjPullbackIso (𝓕 : Y.Modules) :
    (baseAssociatedModule B X hX τ).obj ((Scheme.Modules.pullback f).obj 𝓕) ≅
      (bigToSmallZariskiOpensRingedSiteHom B hX f τ).pullbackModulesGeneral.obj 𝓕 :=
  (associatedModuleBigToSmallZariskiPullbackIso B hX f τ).app 𝓕

end BigFppfOver

/-! ### Entry (26): `X_étale ⟶ Y_Zar` -/

namespace SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **Stacks 03FH, part (2), for the morphism of ringed sites
`f_sites : (X_étale, 𝒪_X) ⟶ (Y_Zar, 𝒪_Y)` of Remark 070R** — entry (26) of the list of
Topologies, Section 03FE, the one mixed pair of small sites.  The associated module of a pullback
is the pullback of the associated module,

`(f^*𝓕)^a ≅ f_sites^*𝓕`,

naturally in the `𝒪_Y`-module `𝓕`, with `(f^*𝓕)^a` the associated module on the small étale site
of `X`.  As for entries (20) to (24) the target of `f_sites` is `(Y_Zar, 𝒪_Y)` itself, so the
`𝓕^a` of the source's formulation is `𝓕`.

There is no hypothesis: the étale topology is finer than the Zariski one, which is Section 03FE's
condition for this entry to be on its list.  Nothing is assumed of `𝓕`, and nothing of the
morphism beyond `X` and `Y` lying in the chosen big étale site.

`f_sites` is the registered
`AlgebraicGeometry.smallEtaleToSmallZariskiRingedSiteHom`, Section 03FE's factorization

`X_étale --f_small--> Y_étale --id_{small,étale,Zar}--> Y_Zar`,

and `f_sites^*` is the pullback of sheaves of modules along that single morphism of ringed sites.
The proof is the source's: Lemma 03D8 splits it as `f_small^*` followed by
`id_{small,étale,Zar}^*`, the second of which is the associated-module functor of the small étale
site by `AlgebraicGeometry.SmallEtale.pullbackToposGeneral_toZariskiRingedToposHom`, and the
clause for `f_small` on the small étale sites — entry (25) —
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`, finishes. -/
@[stacks 03FH "part (2), for the morphism of ringed sites f_sites : (X_étale, 𝒪_X) → \
(Y_Zar, 𝒪_Y) of Stacks 070R — entry (26) of the Stacks 03FE list: (f^*𝓕)^a ≅ f_sites^*𝓕, \
naturally in 𝓕, the 𝓕^a of the target being 𝓕 because the target is (Y_Zar, 𝒪_Y) itself"]
public def associatedModuleSmallEtaleToSmallZariskiPullbackIso :
    Scheme.Modules.pullback (SmallEtale.schemeHom B a) ⋙
        SmallEtale.associatedModule B X.obj X.property ≅
      (smallEtaleToSmallZariskiRingedSiteHom B a).pullbackModulesGeneral :=
  SmallEtale.associatedModuleBaseChangeIso B a ≪≫
    ((smallEtaleRingedSiteHom B a).pullbackModulesGeneralCompIso
      (SmallEtale.toZariskiRingedSiteHom B Y.obj Y.property)).symm

/-- **Stacks 03FH, part (2), at one module**, for the morphism of ringed sites
`f_sites : (X_étale, 𝒪_X) ⟶ (Y_Zar, 𝒪_Y)` of Remark 070R — entry (26) of the Section 03FE list:
`(f^*𝓕)^a ≅ f_sites^*𝓕`, read off from
`AlgebraicGeometry.SmallEtale.associatedModuleSmallEtaleToSmallZariskiPullbackIso`. -/
@[stacks 03FH "part (2) at one module, for the morphism of ringed sites f_sites : \
(X_étale, 𝒪_X) → (Y_Zar, 𝒪_Y) of Stacks 070R — entry (26) of the Stacks 03FE list"]
public def associatedModuleSmallEtaleToSmallZariskiObjPullbackIso (𝓕 : Y.obj.Modules) :
    (SmallEtale.associatedModule B X.obj X.property).obj
        ((Scheme.Modules.pullback (SmallEtale.schemeHom B a)).obj 𝓕) ≅
      (smallEtaleToSmallZariskiRingedSiteHom B a).pullbackModulesGeneral.obj 𝓕 :=
  (associatedModuleSmallEtaleToSmallZariskiPullbackIso B a).app 𝓕

end SmallEtale

end AlgebraicGeometry

end
