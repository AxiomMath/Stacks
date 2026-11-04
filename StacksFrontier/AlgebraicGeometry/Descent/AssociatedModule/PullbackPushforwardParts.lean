module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackBigSites
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePushforwardCartesian
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiPushforwardSquare
public import StacksFrontier.AlgebraicGeometry.RelativeMayerVietoris.Qcoh

/-!
# Stacks 03LC parts (1) and (3), each stated whole

[Stacks, Tag 03LC] has three parts about the equivalences `𝓖 ↦ 𝓖^a` of Proposition 03DX, which
live on the big sites `(Sch/S)_τ` for `τ ∈ {Zariski, étale, smooth, syntomic, fppf}` (03DX (1))
and on the small sites `S_τ` for `τ ∈ {Zariski, étale}` (03DX (2)):

1. they are compatible with pullback, `f^*(𝓖^a) = (f^*𝓖)^a`;
2. the big-site ones are not compatible with pushforward in general;
3. for `f` quasi-compact and quasi-separated and `τ ∈ {Zariski, étale}`, `f_*` and `f_{small, *}`
   preserve quasi-coherent sheaves and `f_{small, *}(𝓕^a) = (f_*𝓕)^a`.

The pieces of parts (1) and (3) are proved site by site and conjunct by conjunct in the modules
imported here.  This file states each of the two parts as one proposition, at every site and
every topology the part speaks of, so that one declaration carries each part:

* `AlgebraicGeometry.associatedModule_pullback_compatible`: **Stacks 03LC part (1)**, for the
  big sites at all five `τ` and for the small étale and small Zariski sites.
* `AlgebraicGeometry.associatedModule_pushforward_compatible_of_qcqs`: **Stacks 03LC part (3)**,
  its three conjuncts at `τ = étale` and at `τ = Zariski`.

Part (2) is `Stacks.Examples.QcohPushforward.exists_isEmpty_iso_bigPushforward_associatedModule`
(`StacksFrontier/Examples/QuasiCoherentPushforward/BigSitePushforward.lean`).

## Implementation notes

Both statements are stronger than the source's where the proofs allow it: the compatibility with
pullback holds for arbitrary modules, not only quasi-coherent ones, and naturally in the module;
the Zariski square of part (3) needs no hypothesis on `f`.  Each isomorphism is asserted as
`Nonempty` of the natural isomorphism the cited declaration constructs.

## References

* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 03LC part (1).**  The equivalences of Proposition 03DX are compatible
with pullback: for every morphism of schemes `f` and every module `𝓖` on the target,
`f_sites^*(𝓖^a) ≅ (f^*𝓖)^a`, naturally in `𝓖`, where `f_sites` is the induced morphism of ringed
sites of Stacks 070R —

* on the big sites, `f_big : ((Sch/X)_τ, 𝒪) ⟶ ((Sch/Y)_τ, 𝒪)` at each of
  `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`
  (`AlgebraicGeometry.BigFppfOver.associatedModuleBasePullbackIso`);
* on the small étale sites, `f_small : X_étale ⟶ Y_étale`
  (`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`);
* on the small Zariski sites, `f_small : T_Zar ⟶ S_Zar`
  (`AlgebraicGeometry.SmallZariski.lcAssociatedModulePullbackIso`).

The source states it for quasi-coherent `𝓖`; it holds for every module. -/
@[stacks 03LC "(1)"]
theorem associatedModule_pullback_compatible :
    (∀ (B : BigFppfSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (hY : B.Contains Y)
        (f : X ⟶ Y) (τ : SiteKind),
      Nonempty (Scheme.Modules.pullback f ⋙ BigFppfOver.baseAssociatedModule B X hX τ ≅
        BigFppfOver.baseAssociatedModule B Y hY τ ⋙
          SheafOfModules.pullback.{u} (BigFppfOver.baseStructureComparison B hX hY f τ))) ∧
    (∀ (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y),
      Nonempty (Scheme.Modules.pullback (SmallEtale.schemeHom B a) ⋙
          SmallEtale.associatedModule B X.obj X.property ≅
        SmallEtale.associatedModule B Y.obj Y.property ⋙
          SheafOfModules.pullback.{u} (SmallEtale.smallEtaleStructureMapRing B a))) ∧
    (∀ (B : BigZariskiSite.{u}) {S T : B.Schemes} (f : T ⟶ S),
      Nonempty (Scheme.Modules.pullback (SmallZariski.lcSchemeHom B f) ⋙
          SmallZariski.associatedModule B T.1 T.property ≅
        SmallZariski.associatedModule B S.1 S.property ⋙
          SheafOfModules.pullback.{u} (SmallZariski.lcStructureMapRing B f))) :=
  ⟨fun B _ _ hX hY f τ => ⟨BigFppfOver.associatedModuleBasePullbackIso B hX hY f τ⟩,
    fun B _ _ a => ⟨SmallEtale.associatedModuleBaseChangeIso B a⟩,
    fun B _ _ f => ⟨SmallZariski.lcAssociatedModulePullbackIso B f⟩⟩

/-- **Stacks Project, Tag 03LC part (3).**  Let `f` be quasi-compact and quasi-separated and
`τ ∈ {Zariski, étale}`.  Then `f_*` preserves quasi-coherent modules (Stacks 01LC,
`AlgebraicGeometry.pushforward_isQuasicoherent`), `f_{small, *}` preserves quasi-coherent
`𝒪`-modules on the small `τ`-sites, and the square of the two associated-module functors commutes,
`f_{small, *}(𝓕^a) ≅ (f_*𝓕)^a` for every quasi-coherent `𝓕`.

At `τ = étale` the last two conjuncts are
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_smallPushforward` and
`AlgebraicGeometry.SmallEtale.associatedModuleSmallPushforwardIsoOfQcqs`; at `τ = Zariski` they
are `AlgebraicGeometry.SmallZariski.lcIsQuasicoherentOnSite_smallPushforward` and
`AlgebraicGeometry.SmallZariski.lcAssociatedModuleSmallPushforwardIso`. -/
@[stacks 03LC "(3)"]
theorem associatedModule_pushforward_compatible_of_qcqs :
    (∀ (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)
        [QuasiCompact (SmallEtale.schemeHom B a)] [QuasiSeparated (SmallEtale.schemeHom B a)],
      (∀ 𝓕 : X.obj.Modules, 𝓕.IsQuasicoherent →
        ((Scheme.Modules.pushforward (SmallEtale.schemeHom B a)).obj 𝓕).IsQuasicoherent) ∧
      (∀ 𝓖 : SheafOfModules.{u} (SmallEtale.structureSheaf B X.obj X.property),
        𝓖.IsQuasicoherentOnSite → ((SmallEtale.smallPushforward B a).obj 𝓖).IsQuasicoherentOnSite) ∧
      (∀ 𝓕 : X.obj.Modules, 𝓕.IsQuasicoherent →
        Nonempty ((SmallEtale.associatedModule B Y.obj Y.property).obj
            ((Scheme.Modules.pushforward (SmallEtale.schemeHom B a)).obj 𝓕) ≅
          (SmallEtale.smallPushforward B a).obj
            ((SmallEtale.associatedModule B X.obj X.property).obj 𝓕)))) ∧
    (∀ (B : BigZariskiSite.{u}) {S T : B.Schemes} (f : T ⟶ S)
        [QuasiCompact (SmallZariski.lcSchemeHom B f)]
        [QuasiSeparated (SmallZariski.lcSchemeHom B f)],
      (∀ 𝓕 : (T.1).Modules, 𝓕.IsQuasicoherent →
        ((Scheme.Modules.pushforward (SmallZariski.lcSchemeHom B f)).obj 𝓕).IsQuasicoherent) ∧
      (∀ 𝓖 : SheafOfModules.{u} (SmallZariski.structureSheaf B T.1 T.property),
        𝓖.IsQuasicoherentOnSite →
          ((SheafOfModules.pushforward.{u} (SmallZariski.lcStructureMapRing B f)).obj
            𝓖).IsQuasicoherentOnSite) ∧
      (∀ 𝓕 : (T.1).Modules, 𝓕.IsQuasicoherent →
        Nonempty ((SmallZariski.associatedModule B S.1 S.property).obj
            ((Scheme.Modules.pushforward (SmallZariski.lcSchemeHom B f)).obj 𝓕) ≅
          (SheafOfModules.pushforward.{u} (SmallZariski.lcStructureMapRing B f)).obj
            ((SmallZariski.associatedModule B T.1 T.property).obj 𝓕)))) :=
  ⟨fun B _ _ a _ _ =>
      ⟨fun 𝓕 _ => pushforward_isQuasicoherent _ 𝓕,
        fun 𝓖 h𝓖 => SmallEtale.isQuasicoherentOnSite_smallPushforward B a 𝓖 h𝓖,
        fun 𝓕 _ => ⟨SmallEtale.associatedModuleSmallPushforwardIsoOfQcqs B a 𝓕⟩⟩,
    fun B _ _ f _ _ =>
      ⟨fun 𝓕 _ => pushforward_isQuasicoherent _ 𝓕,
        fun 𝓖 h𝓖 => SmallZariski.lcIsQuasicoherentOnSite_smallPushforward B f 𝓖 h𝓖,
        fun 𝓕 _ => ⟨SmallZariski.lcAssociatedModuleSmallPushforwardIso B f 𝓕⟩⟩⟩

end AlgebraicGeometry

end
