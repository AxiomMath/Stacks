module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackToSmallZariski
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackBigToSmallEtale
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiPushforwardSquare
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRingedSiteHomGeneral
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesZariskiExists
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.BaseTopologyComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EnoughPoints
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteHomGeneralPullbackCongr
public import StacksCore.Tactic.StacksAttribute

/-!
# The associated module commutes with pullback along the change-of-topologies morphisms

Let `f : T ⟶ S` be a morphism of schemes of a chosen big fppf site.  Topologies, Section 03FE
lists the morphisms of sites `f_sites` attached to `f`, and Descent, Remark 070R makes each of
them a morphism of ringed sites.  Remark 03FH (2) states that for every one of them

`(f^*𝓕)^a ≅ f_sites^*(𝓕^a)`

for an `𝒪_S`-module `𝓕`, where `𝓕 ↦ 𝓕^a` is the associated module on the target of `f_sites`
and `(f^*𝓕)^a` the associated module on its source.  The source's proof: by Remark 03FH (1)
`𝓕 ↦ 𝓕^a` is the pullback along `id_{τ, Zar} : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` (respectively
along `id_{small, τ, Zar}` on a small site), and pullbacks are compatible with composition of
morphisms of ringed sites, Modules on Sites, Lemma 03D8.

This file proves the clause for the big-site entries (1)–(24) of the Section 03FE list, each
**for the single morphism of ringed sites registered for Remark 070R**:

* entries (1), (6), (10), (13), (15), `(Sch/T)_τ ⟶ (Sch/S)_τ`, for
  `AlgebraicGeometry.BigFppfSite.bigBaseChangeRingedSiteHom`;
* entries (1)–(15), `(Sch/T)_τ ⟶ (Sch/S)_{τ'}` for `τ` finer than `τ'`, for
  `AlgebraicGeometry.BigFppfSite.bigRingedSiteHom`;
* entries (16)–(19), `(Sch/T)_τ ⟶ S_étale`, for
  `AlgebraicGeometry.BigFppfSite.bigToSmallEtaleRingedSiteHom`;
* entries (20)–(24), `(Sch/T)_τ ⟶ S_Zar`, for
  `AlgebraicGeometry.BigFppfSite.bigToSmallZariskiRingedSiteHom`.

Of the three small-site entries, (26) is
`AlgebraicGeometry.SmallEtale.associatedModuleSmallEtaleToSmallZariskiPullbackIso`, already at
its registered morphism, and (25) and (27) are
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` and
`AlgebraicGeometry.SmallZariski.lcAssociatedModulePullbackIso`, whose pullbacks are those along
the registered morphisms by `AlgebraicGeometry.pullbackModulesGeneral_smallEtaleRingedSiteHom`
and `AlgebraicGeometry.pullbackModulesGeneral_smallZariskiRingedSiteHom`.

In every statement `f_sites^*` is `AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesGeneral`
of that one morphism — the left adjoint of the pushforward along its own continuous functor and
its own structure map — and not a composite of pullbacks along factors.

## The associated module on the sites of the list

The registered morphisms go between the localized big sites carried by the chosen big fppf
site, `AlgebraicGeometry.BigFppfSite.carriedOverRingedSite`, and the small étale and small
Zariski ringed sites.  On the latter the associated module is
`AlgebraicGeometry.SmallEtale.associatedModule` and
`AlgebraicGeometry.SmallZariski.associatedModule`, each the pullback along `id_{small, τ, Zar}`
by definition (`AlgebraicGeometry.SmallEtale.pullbackToposGeneral_toZariskiRingedToposHom`,
`AlgebraicGeometry.SmallZariski.pullbackToposGeneral_toOpensRingedSiteHom`).  On
`carriedOverRingedSite S hS τ` it is, as Remark 03FH (1) describes it, the pullback along

`AlgebraicGeometry.BigFppfSite.carriedOverToZariskiRingedSiteHom : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`,

the inclusion of the opens of `S` with the identification `𝒪_S(U) ≅ Γ(U, 𝒪_U)`: the same
functor and the same structure map as `AlgebraicGeometry.BigFppfOver.baseToZariskiRingedSiteHom`,
whose pullback is `AlgebraicGeometry.BigFppfOver.baseAssociatedModule`.  At `τ = fppf` the two
sites are the same term and the two associated-module functors agree by `rfl`
(`AlgebraicGeometry.BigFppfSite.pullbackModulesGeneral_carriedOverToZariskiRingedSiteHom_fppf`).

## Main definitions

* `AlgebraicGeometry.BigFppfSite.carriedOverToZariskiRingedSiteHom`: `id_{τ, Zar}` on the big
  `τ`-site carried by a big fppf site.
* `AlgebraicGeometry.BigFppfSite.associatedModuleBigBaseChangeRingedSiteHomPullbackIso`,
  `.associatedModuleBigRingedSiteHomPullbackIso`,
  `.associatedModuleBigToSmallEtaleRingedSiteHomPullbackIso`,
  `.associatedModuleBigToSmallZariskiRingedSiteHomPullbackIso`: **Stacks 03FH (2)** for
  entries (1)–(24) of the Section 03FE list, at their registered morphisms.

## Main results

* `AlgebraicGeometry.BigFppfSite.carriedOverTopology_eq_baseOverTopology`: the topology of the
  carried localized big `τ`-site is the localized topology `baseOverTopology` of the same `τ`.
* `AlgebraicGeometry.Scheme.Opens.topIso_inv_comp_appTop_eq`: for an open immersion `ι : W ⟶ S`
  factoring through an open `V` by `l`, the identification `𝒪_S(V) ≅ Γ(V, 𝒪_V)` followed by
  `l^♯` is restriction to the image of `ι` followed by `Γ(S, ι(W)) ≅ Γ(W, 𝒪_W)`.
* `AlgebraicGeometry.pullbackModulesGeneral_smallEtaleRingedSiteHom` and
  `AlgebraicGeometry.pullbackModulesGeneral_smallZariskiRingedSiteHom`: the pullbacks along the
  registered morphisms of entries (25) and (27).

## Implementation notes

Each proof follows the source.  For entries (1), (6), (10), (13), (15): by Lemma 03D8, `(f^*𝓕)^a`
is the pullback along the composite `(Sch/T)_τ ⟶ T_Zar ⟶ S_Zar` of `id_{τ, Zar}` and `f_small`, and
`f_big^*(𝓕^a)` the pullback along the composite `(Sch/T)_τ ⟶ (Sch/S)_τ ⟶ S_Zar` of `f_big` and
`id_{τ, Zar}`.  These two composite morphisms of ringed sites are not equal, but their functors are
isomorphic, `V ↦ f⁻¹(V)` against `V ↦ T ×_S V`
(`AlgebraicGeometry.BigFppfOver.opensBaseChangeIso`), compatibly with the structure maps
(`AlgebraicGeometry.BigFppfOver.comparisonComp_baseOpensBaseChangeIso`, which is a statement about
sections and so holds verbatim on the carried site); that is the content of the remark of Section
03FE that a composite of two morphisms of its list is the morphism attached to the composite, and
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesGeneralIsoOfIso` turns it into an
isomorphism of pullbacks.

The registered morphism of entries (1)–(15) is `id_{τ, τ'} ∘ f_big`, with `f_big` at the
topology `τ` of the source, so Lemma 03D8 reduces it to the same-topology clause at `τ` and to
`id_{τ, Zar} = id_{τ', Zar} ∘ id_{τ, τ'}`, which holds with the identity comparison.  Entries
(16)–(24) are `π_S ∘ f_sites` with `π_S` the projection to the small site, and reduce in the
same way to entries (1)–(15) and to `id_{τ, Zar} = id_{small, τ, Zar} ∘ π_S` on the big étale,
respectively Zariski, site of `S`.  On the étale side the two functors agree on the nose; on the
Zariski side the small Zariski site is presented by the open immersions into `S`, the object
over an open `V` is chosen through the inverse of the equivalence of Stacks 020X, and the
comparison with `V` itself is
`AlgebraicGeometry.BigFppfSite.opensToSmallZariskiInclusionIso`.

The localized topologies `carriedOverTopology` are equal to `baseOverTopology`, but for
`τ ≠ fppf` not definitionally, so the module categories of the carried sites are not those over
which `AlgebraicGeometry.BigFppfOver.baseAssociatedModule` and the composite pullbacks
`AlgebraicGeometry.BigFppfOver.baseMixedPullback` and
`AlgebraicGeometry.BigFppfOver.smallEtaleMixedPullback` are stated.  The clause is therefore
proved here directly on the carried sites; the sheaf-theoretic instances it needs there are
transported along `carriedOverTopology_eq_baseOverTopology`.

## References

* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Let `ι : W ⟶ S` be an open immersion whose image lies in the open `V`, and `l : W ⟶ V` the
factorization of `ι` through `V`.  Then the identification `𝒪_S(V) ≅ Γ(V, 𝒪_V)` followed by
`l^♯` is restriction from `V` to the image of `ι` followed by the identification
`Γ(S, ι(W)) ≅ Γ(W, 𝒪_W)`: both are `ι^♯` on sections over `V`. -/
public theorem Scheme.Opens.topIso_inv_comp_appTop_eq {S W : Scheme.{u}} (ι : W ⟶ S)
    [IsOpenImmersion ι] (V : S.Opens) (h : ι.opensRange ≤ V) (l : W ⟶ V.toScheme)
    (hl : l ≫ V.ι = ι) :
    V.topIso.inv ≫ l.appTop =
      S.presheaf.map (homOfLE h).op ≫ (IsOpenImmersion.ΓIsoTop ι).inv := by
  have hf : l.appTop = l.appLE ⊤ ⊤ (by simp) := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  have ht : V.topIso.inv = V.ι.appLE V ⊤ V.ι_preimage_self.ge := by
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
    congr 1
  rw [openImmersion_ΓIsoTop_inv, Scheme.Hom.map_appLE, ht, hf]
  refine (Scheme.Hom.appLE_comp_appLE l V.ι V ⊤ ⊤ _ _).trans ?_
  subst hl
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.BigFppfSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The topology of the localization at `S` of the big `τ`-site carried by `B` is the
localization at `S` of the `τ`-topology of `B`'s category, `baseOverTopology`.  At `τ = fppf` the
two are the same term; for the other four they are equal by the comparisons of
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/EnoughPoints.lean`. -/
public theorem carriedOverTopology_eq_baseOverTopology (τ : CoveringTopology) :
    B.carriedOverTopology S hS τ = BigFppfOver.baseOverTopology B S hS τ.toSiteKind := by
  cases τ
  · rfl
  · exact B.bigSyntomicOver_topology_toBigSyntomicSite S hS
  · exact B.bigSmoothOver_topology_toBigSmoothSite S hS
  · exact B.bigEtaleOver_topology_toBigEtaleSite S hS
  · exact B.bigZariskiOver_topology_toBigZariskiSite S hS

/-- Abelian presheaves on the carried localized big `τ`-site have a sheafification. -/
public instance hasWeakSheafify_carriedOverRingedSite (τ : CoveringTopology) :
    HasWeakSheafify (B.carriedOverRingedSite S hS τ).J AddCommGrpCat.{u} := by
  change HasWeakSheafify (B.carriedOverTopology S hS τ) AddCommGrpCat.{u}
  rw [carriedOverTopology_eq_baseOverTopology]
  infer_instance

/-- The weak equivalences of abelian presheaves on the carried localized big `τ`-site are the
locally bijective maps. -/
public instance wEqualsLocallyBijective_carriedOverRingedSite (τ : CoveringTopology) :
    (B.carriedOverRingedSite S hS τ).J.WEqualsLocallyBijective AddCommGrpCat.{u} := by
  change (B.carriedOverTopology S hS τ).WEqualsLocallyBijective AddCommGrpCat.{u}
  rw [carriedOverTopology_eq_baseOverTopology]
  infer_instance

/-- The carried localized big `τ`-site is essentially small at the universe of its structure
rings. -/
public instance essentiallySmall_carriedOverRingedSite (τ : CoveringTopology) :
    EssentiallySmall.{u} (B.carriedOverRingedSite S hS τ).C :=
  inferInstanceAs (EssentiallySmall.{u} (Over (B.obj hS)))

/-- `AlgebraicGeometry.essentiallySmall_smallZariski` at the spelling of the small Zariski
ringed site of the big Zariski site carried by `B`, with the containment taken in `B`; instance
search does not identify the two containment predicates. -/
public instance essentiallySmall_smallZariskiRingedSite_toBigZariskiSite :
    EssentiallySmall.{u} (smallZariskiRingedSite B.toBigZariskiSite S hS).C :=
  essentiallySmall_smallZariski B.toBigZariskiSite (S := ⟨S, hS⟩)

/-- The inclusion of the small Zariski site of `S` into the carried localized big `τ`-site
defines a morphism of sites at the universe of the structure rings:
`AlgebraicGeometry.BigFppfOver.opensToBig_isMorphismOfSites` along
`carriedOverTopology_eq_baseOverTopology`. -/
public theorem isMorphismOfSites_opensToBig (τ : CoveringTopology) :
    IsMorphismOfSites.{u} (BigFppfOver.opensToBig B S hS) (Opens.grothendieckTopology S)
      (B.carriedOverTopology S hS τ) := by
  rw [carriedOverTopology_eq_baseOverTopology]
  exact BigFppfOver.opensToBig_isMorphismOfSites B S hS _

/-- **`id_{τ, Zar} : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` on the carried localized big `τ`-site**, the
morphism of ringed sites of Remark 03FH (1): the inclusion of the opens of `S` together with the
identification of `𝒪_S(U)` with the global functions of the open subscheme `U`.  Its pullback
of modules is the associated-module functor `𝓕 ↦ 𝓕^a` of this site.

It has the functor and the structure map of
`AlgebraicGeometry.BigFppfOver.baseToZariskiRingedSiteHom`; only the topology of the source is
spelled as the carried one. -/
public def carriedOverToZariskiRingedSiteHom (τ : CoveringTopology) :
    RingedSite.HomGeneral (B.carriedOverRingedSite S hS τ) S.zariskiRingedSite where
  u := BigFppfOver.opensToBig B S hS
  isMorphismOfSites := B.isMorphismOfSites_opensToBig S hS τ
  fsharp := ObjectProperty.homMk (BigFppfOver.baseCommStructureMap B S hS τ.toSiteKind).hom

/-- The underlying functor of `carriedOverToZariskiRingedSiteHom` is the inclusion of the opens
of `S` into the localized big site, `AlgebraicGeometry.BigFppfOver.opensToBig`. -/
@[simp]
public theorem carriedOverToZariskiRingedSiteHom_u (τ : CoveringTopology) :
    (B.carriedOverToZariskiRingedSiteHom S hS τ).u = BigFppfOver.opensToBig B S hS := rfl

/-- At `τ = fppf` the associated module of the carried site is
`AlgebraicGeometry.BigFppfOver.baseAssociatedModule`, on the nose. -/
public theorem pullbackModulesGeneral_carriedOverToZariskiRingedSiteHom_fppf :
    (B.carriedOverToZariskiRingedSiteHom S hS .fppf).pullbackModulesGeneral =
      BigFppfOver.baseAssociatedModule B S hS .fppf := rfl

/-- An open `U` of `S` as an object of the small Zariski site of the big Zariski site carried by
`B`: the open immersion `U ⟶ S`. -/
public def opensSmallZariskiObj (U : S.Opens) : SmallZariski B.toBigZariskiSite S hS :=
  ⟨BigFppfOver.opensObj B S hS U, (inferInstance : IsOpenImmersion U.ι)⟩

/-- The object of the small Zariski site chosen over an open `U` by the inverse of the
equivalence of Stacks 020X is isomorphic to `U ⟶ S` itself, both having open image `U`. -/
public def opensToSmallZariskiObjIso (U : S.Opens) :
    (SmallZariski.opensToSmallZariski B.toBigZariskiSite S hS).obj U ≅
      opensSmallZariskiObj B S hS U :=
  (smallZariskiSiteEquiv B.toBigZariskiSite S hS).fullyFaithfulFunctor.preimageIso
    (eqToIso ((smallZariskiToOpens_opensToSmallZariski_obj B.toBigZariskiSite S hS U).trans
      (Scheme.Opens.opensRange_ι U).symm))

/-- The inclusion of the opens of `S` into the small Zariski site followed by the inclusion of
the small site into the big one is the inclusion of the opens of `S` into the big site, up to
the isomorphisms `opensToSmallZariskiObjIso`.  Naturality is automatic, a morphism into an open
of `S` being unique. -/
public def opensToSmallZariskiInclusionIso :
    SmallZariski.opensToSmallZariski B.toBigZariskiSite S hS ⋙
        SmallZariski.inclusion B.toBigZariskiSite S hS ≅ BigFppfOver.opensToBig B S hS :=
  NatIso.ofComponents
    (fun U => (SmallZariski.inclusion B.toBigZariskiSite S hS).mapIso
      (opensToSmallZariskiObjIso B S hS U))
    (fun {_ V} _ => (BigFppfOver.subsingleton_hom_opensObj B S hS _ V).elim _ _)

/-- **`id_{τ, Zar} = id_{small, Zar, Zar} ∘ π_S` on modules, for the big Zariski site**: the
associated module of the small Zariski site followed by `π_S^*` is the associated module of the
carried big Zariski site.  Lemma 03D8, and the comparison `opensToSmallZariskiInclusionIso` of
the two functors from the opens of `S`, which carries the one structure map to the other. -/
public def smallZariskiPiRingedSiteHomPullbackIso :
    SmallZariski.associatedModule B.toBigZariskiSite S hS ⋙
        RingedSite.HomGeneral.pullbackModulesGeneral (X := B.carriedOverRingedSite S hS .zariski)
          (smallZariskiPiRingedSiteHom B.toBigZariskiSite (S := ⟨S, hS⟩)) ≅
      (B.carriedOverToZariskiRingedSiteHom S hS .zariski).pullbackModulesGeneral :=
  (RingedSite.HomGeneral.pullbackModulesGeneralCompIso
      (X := B.carriedOverRingedSite S hS .zariski)
      (smallZariskiPiRingedSiteHom B.toBigZariskiSite (S := ⟨S, hS⟩))
      (SmallZariski.toOpensRingedSiteHom B.toBigZariskiSite S hS)).symm ≪≫
    RingedSite.HomGeneral.pullbackModulesGeneralIsoOfIso
      (RingedSite.HomGeneral.comp (X := B.carriedOverRingedSite S hS .zariski)
        (smallZariskiPiRingedSiteHom B.toBigZariskiSite (S := ⟨S, hS⟩))
        (SmallZariski.toOpensRingedSiteHom B.toBigZariskiSite S hS))
      (B.carriedOverToZariskiRingedSiteHom S hS .zariski)
      (opensToSmallZariskiInclusionIso B S hS) (by
        ext U : 3
        have hl := (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map
          (Over.w ((opensToSmallZariskiInclusionIso B S hS).hom.app U.unop)))
        have : IsOpenImmersion (smallZariskiOpenImmersion B.toBigZariskiSite S hS
            ((SmallZariski.opensToSmallZariski B.toBigZariskiSite S hS).obj U.unop)) :=
          ((SmallZariski.opensToSmallZariski B.toBigZariskiSite S hS).obj U.unop).property
        refine (Scheme.Opens.topIso_inv_comp_appTop_eq _ U.unop
          (smallZariskiToOpens_opensToSmallZariski_obj B.toBigZariskiSite S hS U.unop).le
          (B.inclusion.map ((opensToSmallZariskiInclusionIso B S hS).hom.app U.unop).left)
          hl).trans ?_
        rfl)

variable {S} {T : Scheme.{u}} {hS} {hT : B.Contains T}

/-- **Stacks 03FH, part (2), for the morphism of ringed sites
`f_big : ((Sch/T)_τ, 𝒪_T) ⟶ ((Sch/S)_τ, 𝒪_S)` of Remark 070R** — entries (1), (6), (10), (13),
(15) of the Topologies, Section 03FE list — at its registered form
`AlgebraicGeometry.BigFppfSite.bigBaseChangeRingedSiteHom`, for each of the five topologies:

`(f^*𝓕)^a ≅ f_big^*(𝓕^a)`,

naturally in the `𝒪_S`-module `𝓕`, where `f_big^*` is the pullback along that single morphism
and `(-)^a` is the pullback along `id_{τ, Zar}`
(`AlgebraicGeometry.BigFppfSite.carriedOverToZariskiRingedSiteHom`), as in clause (1).  Nothing
is assumed of `𝓕`.

The proof is the source's: by Lemma 03D8 both sides are pullbacks along a composite morphism
`(Sch/T)_τ ⟶ S_Zar`, namely `f_small ∘ id_{τ, Zar}` and `id_{τ, Zar} ∘ f_big`, and these have
isomorphic functors, `V ↦ f⁻¹(V)` and `V ↦ T ×_S V`, compatibly with the structure maps. -/
@[stacks 03FH "part (2), for the morphism of ringed sites f_big : ((Sch/T)_τ, 𝒪_T) → \
((Sch/S)_τ, 𝒪_S) of Stacks 070R (entries (1), (6), (10), (13), (15) of Stacks 03FE), at the \
registered morphism bigBaseChangeRingedSiteHom, for each of the five topologies: \
(f^*𝓕)^a ≅ f_big^*(𝓕^a), naturally in 𝓕"]
public def associatedModuleBigBaseChangeRingedSiteHomPullbackIso (τ : CoveringTopology)
    (f : B.obj hT ⟶ B.obj hS) :
    Scheme.Modules.pullback f.hom ⋙
        (B.carriedOverToZariskiRingedSiteHom T hT τ).pullbackModulesGeneral ≅
      (B.carriedOverToZariskiRingedSiteHom S hS τ).pullbackModulesGeneral ⋙
        (B.bigBaseChangeRingedSiteHom τ f).pullbackModulesGeneral :=
  ((B.carriedOverToZariskiRingedSiteHom T hT τ).pullbackModulesGeneralCompIso
      f.hom.zariskiRingedSiteHom).symm ≪≫
    RingedSite.HomGeneral.pullbackModulesGeneralIsoOfIso
      ((B.carriedOverToZariskiRingedSiteHom T hT τ).comp f.hom.zariskiRingedSiteHom)
      ((B.bigBaseChangeRingedSiteHom τ f).comp (B.carriedOverToZariskiRingedSiteHom S hS τ))
      (BigFppfOver.opensBaseChangeIso B hT hS f.hom) (by
        ext U : 3
        exact (forget₂ CommRingCat RingCat).map_injective <| congrArg (fun φ => φ.hom.app U)
          (BigFppfOver.comparisonComp_baseOpensBaseChangeIso B hT hS f.hom τ.toSiteKind)) ≪≫
    (B.bigBaseChangeRingedSiteHom τ f).pullbackModulesGeneralCompIso
      (B.carriedOverToZariskiRingedSiteHom S hS τ)

variable (S hS) in
/-- **`id_{τ, Zar} = id_{τ', Zar} ∘ id_{τ, τ'}` on modules**: for `τ` finer than `τ'`, the
associated module of the carried big `τ'`-site followed by `id_{τ, τ'}^*` is the associated
module of the carried big `τ`-site.  Lemma 03D8, the two functors being equal and the
structure map of `id_{τ, τ'}` the identity. -/
public def idRingedSiteHomPullbackIso {τ τ' : CoveringTopology} (h : τ.IsFiner τ') :
    (B.carriedOverToZariskiRingedSiteHom S hS τ').pullbackModulesGeneral ⋙
        (B.idRingedSiteHom S hS h).pullbackModulesGeneral ≅
      (B.carriedOverToZariskiRingedSiteHom S hS τ).pullbackModulesGeneral :=
  ((B.idRingedSiteHom S hS h).pullbackModulesGeneralCompIso
      (B.carriedOverToZariskiRingedSiteHom S hS τ')).symm ≪≫
    RingedSite.HomGeneral.pullbackModulesGeneralIsoOfIso
      ((B.idRingedSiteHom S hS h).comp (B.carriedOverToZariskiRingedSiteHom S hS τ'))
      (B.carriedOverToZariskiRingedSiteHom S hS τ)
      (Functor.rightUnitor _) (by
        ext U : 3
        simp [RingedSite.HomGeneral.comp_fsharp, idRingedSiteHom_fsharp,
          Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousNatTrans]
        rfl)

variable (S hS) in
/-- **`id_{τ, Zar} = id_{small, étale, Zar} ∘ π_S` on modules, for the big étale site**: the
associated module of the small étale site followed by `π_S^*` is the associated module of the
carried big étale site.  Lemma 03D8, the two composite functors from the opens of `S` being
equal. -/
public def smallEtalePiRingedSiteHomPullbackIso :
    SmallEtale.associatedModule B.toBigEtaleSite S hS ⋙
        RingedSite.HomGeneral.pullbackModulesGeneral (X := B.carriedOverRingedSite S hS .etale)
          (smallEtalePiRingedSiteHom B.toBigEtaleSite (S := ⟨S, hS⟩)) ≅
      (B.carriedOverToZariskiRingedSiteHom S hS .etale).pullbackModulesGeneral :=
  (RingedSite.HomGeneral.pullbackModulesGeneralCompIso (X := B.carriedOverRingedSite S hS .etale)
      (smallEtalePiRingedSiteHom B.toBigEtaleSite (S := ⟨S, hS⟩))
      (SmallEtale.toZariskiRingedSiteHom B.toBigEtaleSite S hS)).symm ≪≫
    RingedSite.HomGeneral.pullbackModulesGeneralIsoOfIso
      (RingedSite.HomGeneral.comp (X := B.carriedOverRingedSite S hS .etale)
        (smallEtalePiRingedSiteHom B.toBigEtaleSite (S := ⟨S, hS⟩))
        (SmallEtale.toZariskiRingedSiteHom B.toBigEtaleSite S hS))
      (B.carriedOverToZariskiRingedSiteHom S hS .etale)
      (Iso.refl _) (by
        ext U : 3
        simp [Functor.sheafPushforwardContinuousNatTrans]
        rfl)

/-- **Stacks 03FH, part (2), for the morphisms of ringed sites
`f_sites : ((Sch/T)_τ, 𝒪_T) ⟶ ((Sch/S)_{τ'}, 𝒪_S)` of Remark 070R** — entries (1)–(15) of the
Topologies, Section 03FE list, one for each pair with `τ` finer than `τ'` — at their registered
form `AlgebraicGeometry.BigFppfSite.bigRingedSiteHom`:

`(f^*𝓕)^a ≅ f_sites^*(𝓕^a)`,

naturally in the `𝒪_S`-module `𝓕`, where `f_sites^*` is the pullback along that single morphism
and `(-)^a` is the pullback along `id_{τ, Zar}`, as in clause (1).  The hypothesis is Section
03FE's own condition for the entry to be on its list; nothing is assumed of `𝓕`.

The registered morphism is `id_{τ, τ'} ∘ f_big`, so by Lemma 03D8 its pullback is
`id_{τ, τ'}^*` followed by `f_big^*`, and
`AlgebraicGeometry.BigFppfSite.associatedModuleBigBaseChangeRingedSiteHomPullbackIso` together
with `AlgebraicGeometry.BigFppfSite.idRingedSiteHomPullbackIso` finishes. -/
@[stacks 03FH "part (2), for the morphisms of ringed sites f_sites : ((Sch/T)_τ, 𝒪_T) → \
((Sch/S)_τ', 𝒪_S) of Stacks 070R, entries (1)-(15) of the Stacks 03FE list (τ finer than τ'), \
at the registered morphism bigRingedSiteHom: (f^*𝓕)^a ≅ f_sites^*(𝓕^a), naturally in 𝓕"]
public def associatedModuleBigRingedSiteHomPullbackIso {τ τ' : CoveringTopology} (h : τ.IsFiner τ')
    (f : B.obj hT ⟶ B.obj hS) :
    Scheme.Modules.pullback f.hom ⋙
        (B.carriedOverToZariskiRingedSiteHom T hT τ).pullbackModulesGeneral ≅
      (B.carriedOverToZariskiRingedSiteHom S hS τ').pullbackModulesGeneral ⋙
        (B.bigRingedSiteHom h f).pullbackModulesGeneral :=
  B.associatedModuleBigBaseChangeRingedSiteHomPullbackIso τ f ≪≫
    Functor.isoWhiskerRight (B.idRingedSiteHomPullbackIso S hS h).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((B.bigBaseChangeRingedSiteHom τ f).pullbackModulesGeneralCompIso
        (B.idRingedSiteHom S hS h)).symm

/-- **Stacks 03FH, part (2), for the morphisms of ringed sites
`f_sites : ((Sch/T)_τ, 𝒪_T) ⟶ (S_étale, 𝒪_S)` of Remark 070R** — entries (16)–(19) of the
Topologies, Section 03FE list, `τ ∈ {étale, smooth, syntomic, fppf}` — at their registered form
`AlgebraicGeometry.BigFppfSite.bigToSmallEtaleRingedSiteHom`:

`(f^*𝓕)^a ≅ f_sites^*(𝓕^a)`,

naturally in the `𝒪_S`-module `𝓕`, with `𝓕^a` the associated module of the small étale site of
`S` and `(f^*𝓕)^a` that of the big `τ`-site of `T`.  The hypothesis, `τ` finer than the étale
topology, is Section 03FE's condition for the entry to be on its list.

The registered morphism is `π_S ∘ f_sites` with `f_sites : (Sch/T)_τ ⟶ (Sch/S)_étale`; Lemma 03D8
reduces the clause to that for `f_sites`,
`AlgebraicGeometry.BigFppfSite.associatedModuleBigRingedSiteHomPullbackIso`, and to
`AlgebraicGeometry.BigFppfSite.smallEtalePiRingedSiteHomPullbackIso`. -/
@[stacks 03FH "part (2), for the morphisms of ringed sites f_sites : ((Sch/T)_τ, 𝒪_T) → \
(S_étale, 𝒪_S) of Stacks 070R, entries (16)-(19) of the Stacks 03FE list, at the registered \
morphism bigToSmallEtaleRingedSiteHom: (f^*𝓕)^a ≅ f_sites^*(𝓕^a), naturally in 𝓕"]
public def associatedModuleBigToSmallEtaleRingedSiteHomPullbackIso {τ : CoveringTopology}
    (h : τ.IsFiner .etale) (f : B.obj hT ⟶ B.obj hS) :
    Scheme.Modules.pullback f.hom ⋙
        (B.carriedOverToZariskiRingedSiteHom T hT τ).pullbackModulesGeneral ≅
      SmallEtale.associatedModule B.toBigEtaleSite S hS ⋙
        (B.bigToSmallEtaleRingedSiteHom h f).pullbackModulesGeneral :=
  B.associatedModuleBigRingedSiteHomPullbackIso h f ≪≫
    Functor.isoWhiskerRight (B.smallEtalePiRingedSiteHomPullbackIso S hS).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((B.bigRingedSiteHom h f).pullbackModulesGeneralCompIso
        (smallEtalePiRingedSiteHom B.toBigEtaleSite (S := ⟨S, hS⟩))).symm

/-- **Stacks 03FH, part (2), for the morphisms of ringed sites
`f_sites : ((Sch/T)_τ, 𝒪_T) ⟶ (S_Zar, 𝒪_S)` of Remark 070R** — entries (20)–(24) of the
Topologies, Section 03FE list, one for each of the five topologies — at their registered form
`AlgebraicGeometry.BigFppfSite.bigToSmallZariskiRingedSiteHom`:

`(f^*𝓕)^a ≅ f_sites^*(𝓕^a)`,

naturally in the `𝒪_S`-module `𝓕`, with `𝓕^a` the associated module of the small Zariski site
of `S` and `(f^*𝓕)^a` that of the big `τ`-site of `T`.  The hypothesis holds at every `τ`
(`AlgebraicGeometry.BigFppfSite.isFiner_zariski`).

The registered morphism is `π_S ∘ f_sites` with `f_sites : (Sch/T)_τ ⟶ (Sch/S)_Zar`; Lemma 03D8
reduces the clause to that for `f_sites`,
`AlgebraicGeometry.BigFppfSite.associatedModuleBigRingedSiteHomPullbackIso`, and to
`AlgebraicGeometry.BigFppfSite.smallZariskiPiRingedSiteHomPullbackIso`. -/
@[stacks 03FH "part (2), for the morphisms of ringed sites f_sites : ((Sch/T)_τ, 𝒪_T) → \
(S_Zar, 𝒪_S) of Stacks 070R, entries (20)-(24) of the Stacks 03FE list, at the registered \
morphism bigToSmallZariskiRingedSiteHom: (f^*𝓕)^a ≅ f_sites^*(𝓕^a), naturally in 𝓕"]
public def associatedModuleBigToSmallZariskiRingedSiteHomPullbackIso {τ : CoveringTopology}
    (h : τ.IsFiner .zariski) (f : B.obj hT ⟶ B.obj hS) :
    Scheme.Modules.pullback f.hom ⋙
        (B.carriedOverToZariskiRingedSiteHom T hT τ).pullbackModulesGeneral ≅
      SmallZariski.associatedModule B.toBigZariskiSite S hS ⋙
        (B.bigToSmallZariskiRingedSiteHom h f).pullbackModulesGeneral :=
  B.associatedModuleBigRingedSiteHomPullbackIso h f ≪≫
    Functor.isoWhiskerRight (B.smallZariskiPiRingedSiteHomPullbackIso S hS).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((B.bigRingedSiteHom h f).pullbackModulesGeneralCompIso
        (smallZariskiPiRingedSiteHom B.toBigZariskiSite (S := ⟨S, hS⟩))).symm

end AlgebraicGeometry.BigFppfSite

/-! ### Entries (25) and (27): the small sites

The clause for `f_small` on the small étale and small Zariski sites is
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` and
`AlgebraicGeometry.SmallZariski.lcAssociatedModulePullbackIso`, stated with
`SheafOfModules.pullback` of the structure map of `f_small`.  That is the pullback along the
registered morphisms of ringed sites `AlgebraicGeometry.smallEtaleRingedSiteHom` and
`AlgebraicGeometry.smallZariskiRingedSiteHom` on the nose. -/

namespace AlgebraicGeometry

/-- The pullback of modules along the morphism of ringed small étale sites of Remark 070R (2) is
`SheafOfModules.pullback` of its structure map
`AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing`. -/
public theorem pullbackModulesGeneral_smallEtaleRingedSiteHom (B : BigEtaleSite.{u})
    {X Y : B.Scheme} (a : X ⟶ Y) :
    (smallEtaleRingedSiteHom B a).pullbackModulesGeneral =
      SheafOfModules.pullback.{u} (SmallEtale.smallEtaleStructureMapRing B a) := rfl

/-- The pullback of modules along the morphism of ringed small Zariski sites of Remark 070R (2)
is `SheafOfModules.pullback` of its structure map
`AlgebraicGeometry.SmallZariski.lcStructureMapRing`. -/
public theorem pullbackModulesGeneral_smallZariskiRingedSiteHom (B : BigZariskiSite.{u})
    {S T : B.Schemes} (f : T ⟶ S) :
    (smallZariskiRingedSiteHom B f).pullbackModulesGeneral =
      SheafOfModules.pullback.{u} (SmallZariski.lcStructureMapRing B f) := rfl

end AlgebraicGeometry

end
