module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectFunctoriality
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologyEtaleClauseOne
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologySmallSiteComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.SmallEtaleToBaseUnit

/-!
# Clause (2) of [Stacks, Tag 0756] at `τ = étale`

Let `B` be a big fppf site, `S` a scheme below its cutoff and `𝒢` a sheaf of `𝒪`-modules on
`(Sch/S)_fppf`.  Clause (2) of [Stacks, Tag 0756] at `τ = étale` says that for every object `T`
of `(Sch/S)_fppf` flat and locally of finite presentation over `S`, with scheme `X` and
structure morphism `f : X ⟶ S`, the canonical map

```
ε_f^*(𝒢|_{S_étale}) ⟶ 𝒢|_{X_étale}
```

is an isomorphism, `ε_f` being the morphism of ringed sites `(X_étale, 𝒪_X) ⟶ (S_étale, 𝒪_S)` of
[Stacks, Tag 070R] (2).  This file writes that map down and derives from it clause (2) at
`τ = Zariski`, which is what the Zariski half of the tag
(`AlgebraicGeometry.BigFppfOver.flatSmallSiteCohomologyAddEquiv`) consumes.

## The square of ringed sites

The left-hand side of the clause is `ε_f^*` applied to the restriction of `𝒢`; the comparison
module of the source's proof is `ℱ = a_S^*(𝒢|_{S_étale})` and the clause's left-hand side has to
be identified with `ℱ|_{X_étale}`.  The identification rests on the commuting square of
morphisms of ringed sites

```
  (Sch/X)_fppf --- a_X ---> X_étale
       |                      |
     f_big                   ε_f
       |                      |
       v                      v
  (Sch/S)_fppf --- a_S ---> S_étale
```

whose site functors are `AlgebraicGeometry.BigFppfOver.smallEtaleToFppf` and
`CategoryTheory.Over.pullback` one way and `AlgebraicGeometry.smallEtaleBaseChange` and
`AlgebraicGeometry.BigFppfOver.smallEtaleToFppf` the other.  The two composite site functors are
*equal*, both sending an étale `W / S` to the fibre product `X ×_S W` read over `X`: that is
`AlgebraicGeometry.smallEtaleBaseChange_comp_inclusion` after unfolding the ascriptions.  So the
geometric half of the square is the identity and only the comparison of structure sheaves has to
be checked, which is `AlgebraicGeometry.BigFppfOver.comparisonComp_smallEtaleToBaseObjSquare`:
both routes pull a function back along the projection `X ×_S W ⟶ W`.

`AlgebraicGeometry.BigFppfOver.smallEtaleToBaseObjRestrictNatIso` is the resulting comparison of
inverse images, the étale counterpart of
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.objSmallEtalePullback`,
  `AlgebraicGeometry.BigFppfOver.objSmallEtalePushforward` and
  `AlgebraicGeometry.BigFppfOver.objSmallEtaleAdjunction`: `ε_f^* ⊣ ε_{f,*}`, the inverse and
  direct image of sheaves of modules along `ε_f`.
* `AlgebraicGeometry.BigFppfOver.smallEtaleToBaseObjRestrictNatIso`: **restriction to the big
  fppf site of `X` commutes with the small étale inverse image**,
  `(a_S^*𝓗)|_{(Sch/X)_fppf} ≅ a_X^*(ε_f^*𝓗)`, naturally in `𝓗` and with no hypothesis.
* `AlgebraicGeometry.BigFppfOver.etaleComparisonRestrictIso`: **the two sides of clause (2) are
  comparable**, `ε_f^*(𝒢|_{S_étale}) ≅ ℱ|_{X_étale}` under clause (1) at `τ = étale`.
* `AlgebraicGeometry.BigFppfOver.etaleClause2Map`: **the canonical map of clause (2) at
  `τ = étale`**, the base-change map of the square of ringed sites; that it is the adjoint
  transpose of the restriction map `𝒢|_{S_étale} ⟶ ε_{f,*}(𝒢|_{X_étale})` is
  `AlgebraicGeometry.BigFppfOver.etaleClause2Map_eq_homEquiv_symm`.

## Main results

* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_objSmallEtalePullback`: `ε_f^*` preserves
  quasi-coherence on the small étale site.  This is [Stacks, Tag 03LC] (1) at `τ = étale`
  together with [Stacks, Tag 01BG].
* `AlgebraicGeometry.BigFppfOver.zariskiComparisonMap_eq_etaleComparisonMap`: **the comparison
  map at `τ = Zar` is an isomorphism followed by the comparison map at `τ = étale`**, under
  clause (1) at `τ = étale`.  The isomorphism is the counit of the associated-module adjunction
  of `S_étale`, which clause (1) makes invertible, carried along `a_S^*`.
* `AlgebraicGeometry.BigFppfOver.isIso_zariskiClause2Map_of_isIso_etaleClause2Map`: **clause (2)
  at `τ = étale` implies clause (2) at `τ = Zar`**, over clause (1) at `τ = étale`.
* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_objSmallEtaleRestrict`: **clause (1) at
  `τ = étale` passes from `S` to `X`**, over clause (2) at `τ = étale` at the object.

## Implementation notes

No `stacks` attribute is placed here.  Clause (2) is a *hypothesis* of [Stacks, Tag 0756], not
one of its assertions, and the covering set of the tag is its conclusion.

## References

* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-! ### The square of ringed sites -/

/-- **The structure morphism of `T`, read as a morphism of the schemes of the big étale site
carried by `B`.**  The two categories of schemes are the same, but only in this spelling are the
objects `AlgebraicGeometry.BigEtaleSite.obj` of the big étale site, so that the base-change
constructions of `StacksDraft.AlgebraicGeometry.Descent.AssociatedModule.\
SmallEtaleMorphismBaseChange` — which are indexed by two such objects — present their small
étale sites as the sites of `S` and of the scheme of `T`, and instance search can see them. -/
public abbrev objEtaleHom :
    B.toBigEtaleSite.obj (objScheme B S hS T) (contains_objScheme B S hS T) ⟶
      B.toBigEtaleSite.obj S hS :=
  T.hom

/-- The inclusion of the small étale site of `S` into the big fppf site of `S` is continuous for
`AlgebraicGeometry.BigFppfOver.topology`.  This is
`AlgebraicGeometry.BigFppfOver.isContinuous_smallEtaleInclusion_fppf`, whose target topology is
written as the fppf member of the five localized topologies; the two are the same topology, and
only this spelling matches the one `AlgebraicGeometry.BigFppfOver.objBaseChangeSharp` carries. -/
public instance isContinuous_smallEtaleToFppf_topology :
    (smallEtaleToFppf B S hS).IsContinuous (SmallEtale.topology B.toBigEtaleSite S hS)
      (topology B S hS) :=
  isContinuous_smallEtaleInclusion_fppf B S hS

/-- Base change along the structure morphism of `T` between the two small étale sites is
continuous, restated with the two topologies written as
`AlgebraicGeometry.SmallEtale.topology` of the scheme of `T` and of `S`; in that form instance
search does not find [Stacks, Tag 021I], whose statement is indexed by two objects of the big
étale site. -/
public instance isContinuous_smallEtaleBaseChange_objHom :
    (smallEtaleBaseChange B.toBigEtaleSite (objEtaleHom B S hS T)).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite S hS)
      (SmallEtale.topology B.toBigEtaleSite (objScheme B S hS T)
        (contains_objScheme B S hS T)) :=
  smallEtaleBaseChange_isContinuous B.toBigEtaleSite T.hom

/-- Base change along the structure morphism of `T` on the big fppf sites is continuous, restated
at `AlgebraicGeometry.BigFppfOver.topology`; in that form instance search does not find
`AlgebraicGeometry.BigFppfOver.isContinuous_objBaseChange`. -/
public instance isContinuous_objBaseChange' :
    (Over.pullback T.hom).IsContinuous (topology B S hS)
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  isContinuous_objBaseChange B S hS T

/-- The same continuity with the source topology written as the fppf member of the five
localized topologies, which is the spelling
`AlgebraicGeometry.BigFppfOver.smallEtaleToBaseStructureMap` carries. -/
public instance isContinuous_objBaseChange_fppf :
    (Over.pullback T.hom).IsContinuous (baseOverTopology B S hS .fppf)
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  isContinuous_objBaseChange B S hS T

/-- The two routes round the square of sites are the same functor: both send an object `W / S`
of the small étale site of `S` to the fibre product `X ×_S W`, read as an object of the big fppf
site of `X`.  This is `AlgebraicGeometry.smallEtaleBaseChange_comp_inclusion`. -/
public theorem smallEtaleToFppf_comp_objBaseChange_eq :
    smallEtaleToFppf B S hS ⋙ Over.pullback T.hom =
      smallEtaleBaseChange B.toBigEtaleSite (objEtaleHom B S hS T) ⋙
        smallEtaleToFppf B (objScheme B S hS T) (contains_objScheme B S hS T) :=
  rfl

/-- The route `S_étale ⟶ (Sch/S)_fppf ⟶ (Sch/X)_fppf` round the square is continuous. -/
public instance isContinuous_smallEtaleToFppf_comp_objBaseChange :
    (smallEtaleToFppf B S hS ⋙ Over.pullback T.hom).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite S hS)
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  Functor.isContinuous_comp (smallEtaleToFppf B S hS) (Over.pullback T.hom)
    (SmallEtale.topology B.toBigEtaleSite S hS) (topology B S hS)
    (topology B (objScheme B S hS T) (contains_objScheme B S hS T))

/-- The route `S_étale ⟶ X_étale ⟶ (Sch/X)_fppf` round the square is continuous. -/
public instance isContinuous_smallEtaleBaseChange_comp_smallEtaleToFppf :
    (smallEtaleBaseChange B.toBigEtaleSite (objEtaleHom B S hS T) ⋙
        smallEtaleToFppf B (objScheme B S hS T) (contains_objScheme B S hS T)).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite S hS)
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  Functor.isContinuous_comp (smallEtaleBaseChange B.toBigEtaleSite (objEtaleHom B S hS T))
    (smallEtaleToFppf B (objScheme B S hS T) (contains_objScheme B S hS T))
    (SmallEtale.topology B.toBigEtaleSite S hS)
    (SmallEtale.topology B.toBigEtaleSite (objScheme B S hS T) (contains_objScheme B S hS T))
    (topology B (objScheme B S hS T) (contains_objScheme B S hS T))

/-- The same continuity with the target topology written as the fppf member of the five
localized topologies, which is the spelling
`AlgebraicGeometry.BigFppfOver.smallEtaleToBaseStructureMap` carries; the two are the same
topology. -/
public instance isContinuous_smallEtaleToFppf_comp_objBaseChange_fppf :
    (smallEtaleToFppf B S hS ⋙ Over.pullback T.hom).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite S hS)
      (baseOverTopology B (objScheme B S hS T) (contains_objScheme B S hS T) .fppf) :=
  isContinuous_smallEtaleToFppf_comp_objBaseChange B S hS T

/-- The same continuity for the other route, with the target topology written as the fppf member
of the five localized topologies. -/
public instance isContinuous_smallEtaleBaseChange_comp_smallEtaleToFppf_fppf :
    (smallEtaleBaseChange B.toBigEtaleSite (objEtaleHom B S hS T) ⋙
        smallEtaleToFppf B (objScheme B S hS T) (contains_objScheme B S hS T)).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite S hS)
      (baseOverTopology B (objScheme B S hS T) (contains_objScheme B S hS T) .fppf) :=
  isContinuous_smallEtaleBaseChange_comp_smallEtaleToFppf B S hS T

/-- **The ring half of the square.**  The two composite comparisons of structure sheaves round
the square agree: over an object `W / S` of the small étale site both pull a global function on
`W` back along the base-change projection `X ×_S W ⟶ W`.  The two comparisons attached to `a_S`
and `a_X` are identities, the structure sheaf of a small étale site being the restriction of the
structure sheaf of the big site, so only the two remaining ones have to be compared, and they
are the same restriction map. -/
public theorem comparisonComp_smallEtaleToBaseObjSquare :
    SheafOfModules.comparisonComp
        (SmallEtale.smallEtaleStructureMapRing B.toBigEtaleSite (objEtaleHom B S hS T))
        (smallEtaleToBaseStructureMap B (objScheme B S hS T)
          (contains_objScheme B S hS T) .fppf) =
      SheafOfModules.comparisonComp (smallEtaleToBaseStructureMap B S hS .fppf)
        (objBaseChangeSharp B S hS T) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun W => ?_)
  rfl

/-! ### The inverse image along `ε_f` -/

/-- **`ε_f^*`**: the inverse image of sheaves of modules along the morphism of ringed sites
`ε_f : (X_étale, 𝒪_X) ⟶ (S_étale, 𝒪_S)` of [Stacks, Tag 070R] (2) attached to the structure
morphism `f : X ⟶ S` of `T`. -/
public abbrev objSmallEtalePullback :
    SheafOfModules.{u} (SmallEtale.structureSheaf B.toBigEtaleSite S hS) ⥤
      SheafOfModules.{u} (SmallEtale.structureSheaf B.toBigEtaleSite (objScheme B S hS T)
        (contains_objScheme B S hS T)) :=
  SheafOfModules.pullback.{u}
    (SmallEtale.smallEtaleStructureMapRing B.toBigEtaleSite (objEtaleHom B S hS T))

/-- **`ε_{f,*}`**: the direct image of sheaves of modules along the morphism of ringed sites
`ε_f : (X_étale, 𝒪_X) ⟶ (S_étale, 𝒪_S)` attached to the structure morphism `f : X ⟶ S` of `T`,
which on sections over an étale `W ⟶ S` is the sections over `X ×_S W`. -/
public abbrev objSmallEtalePushforward :
    SheafOfModules.{u} (SmallEtale.structureSheaf B.toBigEtaleSite (objScheme B S hS T)
        (contains_objScheme B S hS T)) ⥤
      SheafOfModules.{u} (SmallEtale.structureSheaf B.toBigEtaleSite S hS) :=
  SheafOfModules.pushforward.{u}
    (SmallEtale.smallEtaleStructureMapRing B.toBigEtaleSite (objEtaleHom B S hS T))

/-- **`ε_f^* ⊣ ε_{f,*}`**, with both functors read on the small étale sites of `S` and of the
scheme of `T`. -/
public abbrev objSmallEtaleAdjunction :
    objSmallEtalePullback B S hS T ⊣ objSmallEtalePushforward B S hS T :=
  SheafOfModules.pullbackPushforwardAdjunction.{u}
    (SmallEtale.smallEtaleStructureMapRing B.toBigEtaleSite (objEtaleHom B S hS T))

/-- **Restriction to the big fppf site of `X` commutes with the small étale inverse image.**
For `T` an object of `(Sch/S)_fppf` with scheme `X` and structure morphism `f : X ⟶ S`, and `𝓗`
a sheaf of `𝒪`-modules on the small étale site of `S`,

```
(a_S^*𝓗)|_{(Sch/X)_fppf}  ≅  a_X^*(ε_f^*𝓗),
```

naturally in `𝓗` and with no hypothesis.  This is the étale counterpart of
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`.

The proof is the mate argument of `SheafOfModules.pullbackSquareIso`, carried out here rather
than cited because the geometric half of the square is an *equality* of functors
(`AlgebraicGeometry.BigFppfOver.smallEtaleToFppf_comp_objBaseChange_eq`) and not merely an
isomorphism: the two composite comparisons of structure sheaves then live in the same type and
`SheafOfModules.pushforwardCongr` replaces the transport along a natural isomorphism.  Both
sides are composites of two inverse images, so each is left adjoint to the corresponding
composite of direct images, and those two composites agree by
`SheafOfModules.pushforwardComp` and
`AlgebraicGeometry.BigFppfOver.comparisonComp_smallEtaleToBaseObjSquare`.  Restriction to the big
fppf site of `X` is the inverse image along the vertical morphism `f_big` by
`AlgebraicGeometry.BigFppfOver.objInverseImageIso`. -/
public def smallEtaleToBaseObjRestrictNatIso :
    smallEtaleToBaseModulePullback B S hS .fppf ⋙ objRestrict B S hS T ≅
      objSmallEtalePullback B S hS T ⋙
        smallEtaleToBaseModulePullback B (objScheme B S hS T)
          (contains_objScheme B S hS T) .fppf :=
  Functor.isoWhiskerLeft (smallEtaleToBaseModulePullback B S hS .fppf)
      (objInverseImageIso B S hS T).symm ≪≫
    Adjunction.leftAdjointUniq
      ((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleToBaseStructureMap B S hS .fppf)).comp
        (SheafOfModules.pullbackPushforwardAdjunction.{u} (objBaseChangeSharp B S hS T)))
      (((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (SmallEtale.smallEtaleStructureMapRing B.toBigEtaleSite
              (objEtaleHom B S hS T))).comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleToBaseStructureMap B (objScheme B S hS T)
              (contains_objScheme B S hS T) .fppf))).ofNatIsoRight
        (SheafOfModules.pushforwardComp.{u}
              (SmallEtale.smallEtaleStructureMapRing B.toBigEtaleSite (objEtaleHom B S hS T))
              (smallEtaleToBaseStructureMap B (objScheme B S hS T)
                (contains_objScheme B S hS T) .fppf) ≪≫
            SheafOfModules.pushforwardCongr.{u}
              (comparisonComp_smallEtaleToBaseObjSquare B S hS T) ≪≫
          (SheafOfModules.pushforwardComp.{u} (smallEtaleToBaseStructureMap B S hS .fppf)
            (objBaseChangeSharp B S hS T)).symm))

/-! ### `ε_f^*` preserves quasi-coherence on the site -/

/-- **`ε_f^*` preserves quasi-coherence on the small étale site.**  If `𝓗` is quasi-coherent on
the small étale site of `S` then `ε_f^*𝓗` is quasi-coherent on the small étale site of `X`.

Three inputs.  `𝓗` is the associated module of its own restriction to `S_Zar` — the
counit is invertible by `AlgebraicGeometry.SmallEtale.isIso_counit`, whose second hypothesis is
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`.  `ε_f^*` carries an associated
module to the associated module of the pullback, which is [Stacks, Tag 03LC] (1) at `τ = étale`,
`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso`.  And the pullback of a
quasi-coherent module is quasi-coherent by [Stacks, Tag 01BG]. -/
public theorem isQuasicoherentOnSite_objSmallEtalePullback
    (H : SheafOfModules.{u} (SmallEtale.structureSheaf B.toBigEtaleSite S hS))
    (hH : H.IsQuasicoherentOnSite) :
    ((objSmallEtalePullback B S hS T).obj H).IsQuasicoherentOnSite := by
  have hM : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((SmallEtale.restrictModule B.toBigEtaleSite S hS).obj H) :=
    SmallEtale.isQuasicoherent_restrictModule B.toBigEtaleSite S hS H hH
  have hc : IsIso ((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).counit.app H) :=
    SmallEtale.isIso_counit B.toBigEtaleSite S hS H hH hM
  have hpb : SheafOfModules.IsQuasicoherent
      (R := (objScheme B S hS T).ringCatSheaf)
      ((Scheme.Modules.pullback
          (SmallEtale.schemeHom B.toBigEtaleSite (objEtaleHom B S hS T))).obj
        ((SmallEtale.restrictModule B.toBigEtaleSite S hS).obj H)) :=
    Stacks.Modules.isQuasicoherent_pullback
      (SmallEtale.schemeHom B.toBigEtaleSite (objEtaleHom B S hS T)) _ hM
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((SmallEtale.associatedModuleObjBaseChangeIso B.toBigEtaleSite (objEtaleHom B S hS T)
        ((SmallEtale.restrictModule B.toBigEtaleSite S hS).obj H)).trans
      ((objSmallEtalePullback B S hS T).mapIso (@asIso _ _ _ _ _ hc))) ?_
  exact SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent
    B.toBigEtaleSite (objScheme B S hS T) (contains_objScheme B S hS T) _ hpb

/-! ### The comparison map at `τ = Zar` factors through the one at `τ = étale` -/

section Factor

variable (G : SheafOfModules.{u} (structureSheaf B S hS))

/-- The associated-module adjunction of the big fppf site of `S` read through the small étale
site: the associated-module functor of `S_étale` followed by `a_S^*`, against restriction to
`S_Zar`.  Its left adjoint is compared with the associated-module functor of the big fppf site by
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSmallEtalePullback`, which is exactly the
uniqueness isomorphism of left adjoints between the two. -/
public def smallEtaleFactoredAdjunction :
    SmallEtale.associatedModule B.toBigEtaleSite S hS ⋙
        smallEtaleToBaseModulePullback B S hS .fppf ⊣ baseRestrictModule B S hS .fppf :=
  ((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).comp
      (smallEtaleToBaseModuleAdjunction B S hS .fppf)).ofNatIsoRight
    (smallEtaleToBasePushforwardCompIso B S hS .fppf)

/-- The comparison of the two left adjoints carries the counit of the factored adjunction to the
comparison map at `τ = Zar`.  This is `CategoryTheory.Adjunction.leftAdjointUniq_hom_app_counit`
at the uniqueness isomorphism that
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSmallEtalePullback` is. -/
public theorem baseAssociatedModuleIsoSmallEtalePullback_hom_app_comp_zariskiComparisonMap :
    (baseAssociatedModuleIsoSmallEtalePullback B S hS .fppf).hom.app
          ((baseRestrictModule B S hS .fppf).obj G) ≫ zariskiComparisonMap B S hS G =
      (smallEtaleFactoredAdjunction B S hS).counit.app G :=
  Adjunction.leftAdjointUniq_hom_app_counit (smallEtaleFactoredAdjunction B S hS)
    (baseAssociatedModuleAdjunction B S hS .fppf) G

/-- The counit of the factored adjunction at `𝒢` is `a_S^*` applied to the counit of the
associated-module adjunction of `S_étale`, followed by the comparison map at `τ = étale`, after
the transport along `AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforwardCompIso`.  The
first factor is the counit of `CategoryTheory.Adjunction.ofNatIsoRight`, which is `a_S^*` of that
transport and is an isomorphism; the remaining equality is
`CategoryTheory.Adjunction.comp_counit_app`. -/
public theorem smallEtaleFactoredAdjunction_counit_app :
    (smallEtaleFactoredAdjunction B S hS).counit.app G =
      (smallEtaleToBaseModulePullback B S hS .fppf).map
            ((SmallEtale.associatedModule B.toBigEtaleSite S hS).map
              ((smallEtaleToBasePushforwardCompIso B S hS .fppf).inv.app G)) ≫
        ((smallEtaleToBaseModulePullback B S hS .fppf).map
              ((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).counit.app
                ((smallEtaleToBasePushforward B S hS .fppf).obj G)) ≫
          etaleComparisonMap B S hS G) :=
  congrArg (fun k => (smallEtaleToBaseModulePullback B S hS .fppf).map
            ((SmallEtale.associatedModule B.toBigEtaleSite S hS).map
              ((smallEtaleToBasePushforwardCompIso B S hS .fppf).inv.app G)) ≫ k)
    (Adjunction.comp_counit_app (SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS)
      (smallEtaleToBaseModuleAdjunction B S hS .fppf) G)

/-- **The comparison map at `τ = Zar`, preceded by the comparison of the two left adjoints, is
the comparison map at `τ = étale` preceded by two canonical maps**, unconditionally.

Writing `L₁ ⊣ R₁` for the associated-module adjunction of the big fppf site of `S`, `L₂ ⊣ R₂`
for that of the small étale site and `L₃ ⊣ R₃` for `a_S^* ⊣ a_{S,*}`, the comparison map at
`τ = Zar` is the counit of `L₁ ⊣ R₁` at `𝒢` and the one at `τ = étale` is the counit of
`L₃ ⊣ R₃` at `𝒢`.  The composite adjunction `L₂ ⋙ L₃ ⊣ R₃ ⋙ R₂` has right adjoint `R₁` after
the transport `AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforwardCompIso`, so its counit
at `𝒢` agrees with the counit of `L₁ ⊣ R₁` up to the comparison of left adjoints
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSmallEtalePullback`; and that counit
factors as `L₃` of the counit of `L₂ ⊣ R₂` at `𝒢|_{S_étale}`, followed by the counit of
`L₃ ⊣ R₃`.

Of the two maps preceding the étale comparison map the first is always an isomorphism, and
clause (1) of [Stacks, Tag 0756] at `τ = étale` makes the second one an isomorphism too, by
`AlgebraicGeometry.SmallEtale.isIso_counit`. -/
public theorem baseAssociatedModuleIsoSmallEtalePullback_hom_app_comp_zariskiComparisonMap_eq :
    (baseAssociatedModuleIsoSmallEtalePullback B S hS .fppf).hom.app
          ((baseRestrictModule B S hS .fppf).obj G) ≫ zariskiComparisonMap B S hS G =
      (smallEtaleToBaseModulePullback B S hS .fppf).map
            ((SmallEtale.associatedModule B.toBigEtaleSite S hS).map
              ((smallEtaleToBasePushforwardCompIso B S hS .fppf).inv.app G)) ≫
        ((smallEtaleToBaseModulePullback B S hS .fppf).map
              ((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).counit.app
                ((smallEtaleToBasePushforward B S hS .fppf).obj G)) ≫
          etaleComparisonMap B S hS G) :=
  (baseAssociatedModuleIsoSmallEtalePullback_hom_app_comp_zariskiComparisonMap B S hS G).trans
    (smallEtaleFactoredAdjunction_counit_app B S hS G)

/-- **Clause (2) at `τ = étale` implies clause (2) at `τ = Zar`**, over clause (1) at
`τ = étale`.  Any functor out of the sheaves of `𝒪`-modules on `(Sch/S)_fppf` that carries the
comparison map at `τ = étale` to an isomorphism carries the one at `τ = Zar` to an isomorphism.

By `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSmallEtalePullback_hom_app_comp_\
zariskiComparisonMap_eq` the two comparison maps agree after `Φ` up to three isomorphisms: the
comparison of the two left adjoints, the transport of the factorization of the direct images,
and `a_S^*` of the counit of the associated-module adjunction of `S_étale` at `𝒢|_{S_étale}`,
which clause (1) at `τ = étale` makes invertible by
`AlgebraicGeometry.SmallEtale.isIso_counit`. -/
public theorem isIso_map_zariskiComparisonMap_of_isIso_map_etaleComparisonMap
    {D : Type*} [Category D] (Φ : SheafOfModules.{u} (structureSheaf B S hS) ⥤ D)
    (h : ((smallEtaleToBasePushforward B S hS .fppf).obj G).IsQuasicoherentOnSite)
    (hφ : IsIso (Φ.map (etaleComparisonMap B S hS G))) :
    IsIso (Φ.map (zariskiComparisonMap B S hS G)) := by
  have hc : IsIso ((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).counit.app
      ((smallEtaleToBasePushforward B S hS .fppf).obj G)) :=
    SmallEtale.isIso_counit B.toBigEtaleSite S hS _ h
      (SmallEtale.isQuasicoherent_restrictModule B.toBigEtaleSite S hS _ h)
  have := hc
  have := hφ
  have key := (Φ.map_comp _ _).symm.trans ((congrArg Φ.map
    (baseAssociatedModuleIsoSmallEtalePullback_hom_app_comp_zariskiComparisonMap_eq B S hS G)).trans
      ((Φ.map_comp _ _).trans (congrArg (_ ≫ ·) (Φ.map_comp _ _))))
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _
    (Φ.mapIso ((baseAssociatedModuleIsoSmallEtalePullback B S hS .fppf).app
      ((baseRestrictModule B S hS .fppf).obj G))).isIso_hom
    (@IsIso.comp_isIso _ _ _ _ _ _ _
      (Φ.mapIso ((smallEtaleToBaseModulePullback B S hS .fppf).mapIso
        ((SmallEtale.associatedModule B.toBigEtaleSite S hS).mapIso
          ((smallEtaleToBasePushforwardCompIso B S hS .fppf).app G).symm))).isIso_hom
      (@IsIso.comp_isIso _ _ _ _ _ _ _
        (Φ.mapIso ((smallEtaleToBaseModulePullback B S hS .fppf).mapIso
          (@asIso _ _ _ _ _ hc))).isIso_hom hφ)) key

end Factor

/-! ### The two sides of clause (2) are comparable -/

section Clause

variable (G : SheafOfModules.{u} (structureSheaf B S hS))

/-- **`𝒢|_{X_étale}` for `X` the scheme of an object `T` of the big fppf site**: restrict `𝒢` to
the big fppf site of `X` and then along `a_X`.  This is the right-hand side of clause (2) of
[Stacks, Tag 0756] at `τ = étale`. -/
public abbrev objSmallEtaleRestrict :
    SheafOfModules.{u} (SmallEtale.structureSheaf B.toBigEtaleSite (objScheme B S hS T)
      (contains_objScheme B S hS T)) :=
  (smallEtaleToBasePushforward B (objScheme B S hS T) (contains_objScheme B S hS T) .fppf).obj
    ((objRestrict B S hS T).obj G)

/-- **The restriction of `ℱ = a_S^*(𝒢|_{S_étale})` to the small étale site of the scheme `X` of
an object `T` is `ε_f^*(𝒢|_{S_étale})`**, whenever `𝒢|_{S_étale}` is quasi-coherent on the small
étale site — that is, under clause (1) of [Stacks, Tag 0756] at `τ = étale`.

Two steps.  `ε_f^*(𝒢|_{S_étale})` is quasi-coherent on the small étale site of `X` by
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_objSmallEtalePullback`, so the unit of
`a_X^* ⊣ a_{X,*}` is an isomorphism at it by
`AlgebraicGeometry.BigFppfOver.isIso_smallEtaleToBaseUnit_app`, identifying it with
`a_{X,*}a_X^*(ε_f^*(𝒢|_{S_étale}))`.  And `a_X^*(ε_f^*(𝒢|_{S_étale}))` is `ℱ` restricted to the
big fppf site of `X` by
`AlgebraicGeometry.BigFppfOver.smallEtaleToBaseObjRestrictNatIso`.

This is the étale counterpart of
`AlgebraicGeometry.BigFppfOver.zariskiComparisonRestrictIso`, and it is where clause (1) at
`τ = étale` does its work: it makes the two sides of clause (2) comparable. -/
public def etaleComparisonRestrictIso
    (h : ((smallEtaleToBasePushforward B S hS .fppf).obj G).IsQuasicoherentOnSite) :
    (objSmallEtalePullback B S hS T).obj
        ((smallEtaleToBasePushforward B S hS .fppf).obj G) ≅
      objSmallEtaleRestrict B S hS T (etaleComparisonModule B S hS G) :=
  letI hqc := isQuasicoherentOnSite_objSmallEtalePullback B S hS T _ h
  letI : IsIso ((smallEtaleToBaseModuleAdjunction B (objScheme B S hS T)
      (contains_objScheme B S hS T) .fppf).unit.app
      ((objSmallEtalePullback B S hS T).obj
        ((smallEtaleToBasePushforward B S hS .fppf).obj G))) :=
    isIso_smallEtaleToBaseUnit_app B (objScheme B S hS T) (contains_objScheme B S hS T) _ hqc
  asIso ((smallEtaleToBaseModuleAdjunction B (objScheme B S hS T)
      (contains_objScheme B S hS T) .fppf).unit.app
      ((objSmallEtalePullback B S hS T).obj
        ((smallEtaleToBasePushforward B S hS .fppf).obj G))) ≪≫
    (smallEtaleToBasePushforward B (objScheme B S hS T)
        (contains_objScheme B S hS T) .fppf).mapIso
      ((smallEtaleToBaseObjRestrictNatIso B S hS T).app
        ((smallEtaleToBasePushforward B S hS .fppf).obj G)).symm

/-- **The canonical map `ε_f^*(𝒢|_{S_étale}) ⟶ 𝒢|_{X_étale}` of clause (2) of
[Stacks, Tag 0756] at `τ = étale`**, for `f : X ⟶ S` the structure morphism of an object `T` of
`(Sch/S)_fppf`.

It is the base-change map of the square of ringed sites formed by `f_big`, `a_S`, `a_X` and `ε_f`:
the unit of `a_X^* ⊣ a_{X,*}` at `ε_f^*(𝒢|_{S_étale})`, the comparison of inverse images
`a_X^*(ε_f^*(-)) ≅ (a_S^*(-))|_{(Sch/X)_fppf}` of
`AlgebraicGeometry.BigFppfOver.smallEtaleToBaseObjRestrictNatIso`, and the restriction of the
counit `φ : a_S^*(𝒢|_{S_étale}) ⟶ 𝒢`.
`AlgebraicGeometry.BigFppfOver.etaleClause2Map_eq_homEquiv_symm` identifies it with the adjoint
transpose of `𝒢|_{S_étale} ⟶ ε_{f,*}(𝒢|_{X_étale})`, restriction along the base change
`X ×_S W ⟶ W` followed by the identification of the two composite direct images, which is the
source's description.  No hypothesis on `𝒢` is needed to define it. -/
public def etaleClause2Map :
    (objSmallEtalePullback B S hS T).obj
        ((smallEtaleToBasePushforward B S hS .fppf).obj G) ⟶
      objSmallEtaleRestrict B S hS T G :=
  ((smallEtaleToBaseModuleAdjunction B (objScheme B S hS T)
        (contains_objScheme B S hS T) .fppf).unit.app
      ((objSmallEtalePullback B S hS T).obj
        ((smallEtaleToBasePushforward B S hS .fppf).obj G)) ≫
    (smallEtaleToBasePushforward B (objScheme B S hS T)
        (contains_objScheme B S hS T) .fppf).map
      ((smallEtaleToBaseObjRestrictNatIso B S hS T).inv.app
        ((smallEtaleToBasePushforward B S hS .fppf).obj G))) ≫
    (smallEtaleToBasePushforward B (objScheme B S hS T)
        (contains_objScheme B S hS T) .fppf).map
      ((objRestrict B S hS T).map (etaleComparisonMap B S hS G))

/-- **Under clause (1) at `τ = étale` the canonical map of clause (2) is an isomorphism followed
by the restriction of `φ`**: its first two factors are
`AlgebraicGeometry.BigFppfOver.etaleComparisonRestrictIso`, the identification
`ε_f^*(𝒢|_{S_étale}) ≅ ℱ|_{X_étale}` for `ℱ = a_S^*(𝒢|_{S_étale})`. -/
public theorem etaleClause2Map_eq
    (h : ((smallEtaleToBasePushforward B S hS .fppf).obj G).IsQuasicoherentOnSite) :
    etaleClause2Map B S hS T G =
      (etaleComparisonRestrictIso B S hS T G h).hom ≫
        (smallEtaleToBasePushforward B (objScheme B S hS T)
            (contains_objScheme B S hS T) .fppf).map
          ((objRestrict B S hS T).map (etaleComparisonMap B S hS G)) :=
  rfl

/-- **Clause (1) of [Stacks, Tag 0756] at `τ = étale` passes from `S` to `X`.**  If
`𝒢|_{S_étale}` is quasi-coherent on the small étale site and the canonical map of clause (2) at
`τ = étale` is an isomorphism at `T`, then `𝒢|_{X_étale}` is quasi-coherent on the small étale
site of the scheme `X` of `T`: it is then isomorphic to `ε_f^*(𝒢|_{S_étale})`, which is
quasi-coherent on the site by
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_objSmallEtalePullback`. -/
public theorem isQuasicoherentOnSite_objSmallEtaleRestrict
    (h : ((smallEtaleToBasePushforward B S hS .fppf).obj G).IsQuasicoherentOnSite)
    (h2 : IsIso (etaleClause2Map B S hS T G)) :
    (objSmallEtaleRestrict B S hS T G).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (@asIso _ _ _ _ _ h2)
    (isQuasicoherentOnSite_objSmallEtalePullback B S hS T _ h)

/-- **Clause (2) at `τ = étale` gives the restriction of `φ_étale` to `X_étale` an inverse.**
The first factor of `AlgebraicGeometry.BigFppfOver.etaleClause2Map` is an isomorphism already. -/
public theorem isIso_objSmallEtaleRestrict_map_etaleComparisonMap
    (h : ((smallEtaleToBasePushforward B S hS .fppf).obj G).IsQuasicoherentOnSite)
    (h2 : IsIso (etaleClause2Map B S hS T G)) :
    IsIso ((smallEtaleToBasePushforward B (objScheme B S hS T)
        (contains_objScheme B S hS T) .fppf).map
      ((objRestrict B S hS T).map (etaleComparisonMap B S hS G))) :=
  @IsIso.of_isIso_comp_left _ _ _ _ _ (etaleComparisonRestrictIso B S hS T G h).hom
    ((smallEtaleToBasePushforward B (objScheme B S hS T)
        (contains_objScheme B S hS T) .fppf).map
      ((objRestrict B S hS T).map (etaleComparisonMap B S hS G))) inferInstance h2

/-- **Clause (2) at `τ = étale` gives the restriction of `φ_étale` to `X_Zar` an inverse.**
Restriction to `X_Zar` factors as restriction to `X_étale` followed by restriction from
`X_étale` to `X_Zar`, by
`AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforwardCompIso`, and the naturality square of
that isomorphism carries the previous statement across. -/
public theorem isIso_objZariskiRestrict_map_etaleComparisonMap
    (h : ((smallEtaleToBasePushforward B S hS .fppf).obj G).IsQuasicoherentOnSite)
    (h2 : IsIso (etaleClause2Map B S hS T G)) :
    IsIso ((restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)).map
      ((objRestrict B S hS T).map (etaleComparisonMap B S hS G))) := by
  have h3 := isIso_objSmallEtaleRestrict_map_etaleComparisonMap B S hS T G h h2
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _
    ((smallEtaleToBasePushforwardCompIso B (objScheme B S hS T)
      (contains_objScheme B S hS T) .fppf).app
        ((objRestrict B S hS T).obj (etaleComparisonModule B S hS G))).isIso_hom
    (@IsIso.comp_isIso _ _ _ _ _ _ _
      ((SmallEtale.restrictModule B.toBigEtaleSite (objScheme B S hS T)
        (contains_objScheme B S hS T)).mapIso (@asIso _ _ _ _ _ h3)).isIso_hom
      ((smallEtaleToBasePushforwardCompIso B (objScheme B S hS T)
        (contains_objScheme B S hS T) .fppf).app ((objRestrict B S hS T).obj G)).isIso_hom)
    ((smallEtaleToBasePushforwardCompIso B (objScheme B S hS T)
      (contains_objScheme B S hS T) .fppf).hom.naturality
        ((objRestrict B S hS T).map (etaleComparisonMap B S hS G))).symm

/-- **Clause (2) of [Stacks, Tag 0756] at `τ = étale` implies clause (2) at `τ = Zar`**, at each
object separately.  Over clause (1) at `τ = étale`, which gives clause (1) at `τ = Zar` by
`AlgebraicGeometry.BigFppfOver.isQuasicoherent_restrictModule_of_isQuasicoherentOnSite`, the
invertibility of `AlgebraicGeometry.BigFppfOver.etaleClause2Map` at `T` implies that of
`AlgebraicGeometry.BigFppfOver.zariskiClause2Map` at `T`.

The first factor of the Zariski map is an isomorphism by construction, and its second factor is
the restriction to `X_Zar` of `φ_Zar`, which differs from that of `φ_étale` by a map clause (1)
at `τ = étale` makes invertible. -/
public theorem isIso_zariskiClause2Map_of_isIso_etaleClause2Map
    (h : ((smallEtaleToBasePushforward B S hS .fppf).obj G).IsQuasicoherentOnSite)
    (h2 : IsIso (etaleClause2Map B S hS T G)) :
    IsIso (zariskiClause2Map B S hS T G) := by
  have hz : IsIso ((restrictModule B (objScheme B S hS T)
      (contains_objScheme B S hS T)).map
      ((objRestrict B S hS T).map (zariskiComparisonMap B S hS G))) :=
    isIso_map_zariskiComparisonMap_of_isIso_map_etaleComparisonMap B S hS G
      (objRestrict B S hS T ⋙
        restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)) h
      (isIso_objZariskiRestrict_map_etaleComparisonMap B S hS T G h h2)
  rw [zariskiClause2Map_eq B S hS T G
    (isQuasicoherent_restrictModule_of_isQuasicoherentOnSite B S hS G h)]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (zariskiComparisonRestrictIso B S hS T G
      (isQuasicoherent_restrictModule_of_isQuasicoherentOnSite B S hS G h)).isIso_hom hz

end Clause

end AlgebraicGeometry.BigFppfOver

end
