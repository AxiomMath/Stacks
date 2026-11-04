module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.QuasiCoherentPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The unit of `a_S^* ⊣ a_{S,*}` at a module quasi-coherent on the small étale site

Let `B` be a big fppf site, `S` a scheme below its cutoff, and write

* `a_S : ((Sch/S)_fppf, 𝒪) ⟶ (S_étale, 𝒪)` for the morphism of ringed sites given by the
  inclusion of the small étale site of [Stacks, Tag 021B],
* `a_S^* = AlgebraicGeometry.BigFppfOver.smallEtaleToBaseModulePullback` at `.fppf` and
  `a_{S,*} = AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforward` at `.fppf` for the
  inverse and direct images of sheaves of modules along it, adjoint by
  `AlgebraicGeometry.BigFppfOver.smallEtaleToBaseModuleAdjunction`.

This file proves that the **unit `𝓗 ⟶ a_{S,*}a_S^*𝓗` of that adjunction is an isomorphism at
every `𝓗` quasi-coherent on the small étale site**, with no hypothesis beyond that.

Three functors and three adjunctions meet here.  Writing `L₁ ⊣ R₁` for the associated-module
adjunction of the big fppf site over `S` (`𝓕 ↦ 𝓕^a` against restriction to `S_Zar`), `L₂ ⊣ R₂`
for that of the small étale site, and `L₃ ⊣ R₃` for `a_S^* ⊣ a_{S,*}`, the development already
has both comparisons of the composites,

* `R₃ ⋙ R₂ ≅ R₁` — `AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforwardCompIso`, and
* `L₂ ⋙ L₃ ≅ L₁` — `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSmallEtalePullback`,

the second being exactly the comparison of left adjoints that the first produces.  The unit of
the composite adjunction `L₂ ⋙ L₃ ⊣ R₃ ⋙ R₂` at a quasi-coherent `𝒪_S`-module `𝓕` is therefore
the unit of `L₁ ⊣ R₁` at `𝓕` up to isomorphism, hence invertible by Stacks 0GN7
(`AlgebraicGeometry.BigFppfOver.isIso_baseUnit_app`); and that composite unit factors as the
unit of `L₂ ⊣ R₂` at `𝓕`, invertible by the small étale half of Stacks 0GN7
(`AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`), followed by `R₂` applied to the unit of
`L₃ ⊣ R₃` at `𝓕^a`.  So `R₂` applied to the latter is invertible.

`R₂` is restriction from `S_étale` to `S_Zar`, which does not reflect isomorphisms in general;
it does between modules quasi-coherent on `S_étale`, because the counit
`(R₂𝓗)^a ⟶ 𝓗` is invertible there — `AlgebraicGeometry.SmallEtale.isIso_counit`, whose second
hypothesis is discharged by `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`.  Both
ends of the unit are such modules: its source `𝓕^a` by [Stacks, Tag 03DV] (2) at `τ = étale`,
and its target `a_{S,*}a_S^*(𝓕^a)` because `a_S^*(𝓕^a) ≅ 𝓕^a` on the big fppf site and
`a_{S,*}` carries that back to `𝓕^a` — the content of
`AlgebraicGeometry.BigFppfOver.pushforward_smallEtaleAssociatedSheaf`, which is [Stacks, Tag
0DEW] clause (6).  Finally every quasi-coherent `𝓗` on `S_étale` is such an `𝓕^a`, by the
essential surjectivity of [Stacks, Tag 03DX] (2) at `τ = étale`
(`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`), and the unit is
natural, so the general case follows from that one.

## Main results

* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_smallEtaleToBasePushforward_\
  baseAssociatedSheaf`: `a_{S,*}(𝓕^a)` is quasi-coherent on the small étale site, for `𝓕` a
  quasi-coherent `𝒪_S`-module.
* `AlgebraicGeometry.BigFppfOver.isIso_smallEtaleToBaseUnit_app_associatedModule`: the unit of
  `a_S^* ⊣ a_{S,*}` is an isomorphism at `𝓕^a`.
* `AlgebraicGeometry.BigFppfOver.isIso_smallEtaleToBaseUnit_app`: **the unit of
  `a_S^* ⊣ a_{S,*}` is an isomorphism at every module quasi-coherent on the small étale site.**

## Implementation notes

No `stacks` attribute is placed.  The statement is a step of the proof of [Stacks, Tag 0DEW]
rather than one of its clauses: the clauses the tag lists about `a_S` are the sheaf condition,
the two identifications of inverse images, and the identification of the direct image, all of
which are carried elsewhere in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/FppfEtaleComparison/`.

The comparison of left adjoints is spelled out as `CategoryTheory.Adjunction.leftAdjointUniq`
of the transported composite adjunction rather than reused from
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSmallEtalePullback`, which is that very
term: `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` is stated about the former and
unfolding the latter to meet it buys nothing.

## References

* [Stacks Project, Tag 0DEW](https://stacks.math.columbia.edu/tag/0DEW)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`a_{S,*}(𝓕^a)` is quasi-coherent on the small étale site of `S`**, for `𝓕` a quasi-coherent
`𝒪_S`-module.  The direct image along `a_S` of the associated module of the big fppf site *is*
the associated module of the small étale site, by [Stacks, Tag 0DEW] clause (6)
(`AlgebraicGeometry.BigFppfOver.pushforward_smallEtaleAssociatedSheaf` together with
`AlgebraicGeometry.BigFppfOver.smallEtaleAssociatedModuleIsoSheaf`), and that is quasi-coherent
on the site by [Stacks, Tag 03DV] (2) at `τ = étale`. -/
public theorem isQuasicoherentOnSite_smallEtaleToBasePushforward_baseAssociatedSheaf
    (F : S.Modules) [F.IsQuasicoherent] :
    ((smallEtaleToBasePushforward B S hS .fppf).obj
        (baseAssociatedSheaf B S hS F .fppf)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((smallEtaleAssociatedModuleIsoSheaf B S hS F).trans
      (eqToIso (pushforward_smallEtaleAssociatedSheaf B S hS F).symm))
    (SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B.toBigEtaleSite S hS F
      inferInstance)

section Unit

variable (F : S.Modules) [F.IsQuasicoherent]

/-- `a_S^*(𝓕^a) ≅ 𝓕^a` on the big fppf site: the inverse image along `a_S` of the associated
module of the small étale site is the associated module of the big fppf site, which is
[Stacks, Tag 0DEW] clause (3) read at `𝓕^a` in its module spelling. -/
public def smallEtaleToBasePullbackAssociatedModuleIso :
    (smallEtaleToBaseModulePullback B S hS .fppf).obj
        ((SmallEtale.associatedModule B.toBigEtaleSite S hS).obj F) ≅
      baseAssociatedSheaf B S hS F .fppf :=
  (smallEtaleToBaseModulePullback B S hS .fppf).mapIso
      (smallEtaleAssociatedModuleIsoSheaf B S hS F) ≪≫
    baseAssociatedSheafIsoSmallEtalePullback B S hS .fppf F

/-- `a_{S,*}a_S^*(𝓕^a) ≅ 𝓕^a`: the two ends of the unit of `a_S^* ⊣ a_{S,*}` at `𝓕^a` are
isomorphic. -/
public def smallEtaleToBaseUnitTargetIso :
    (smallEtaleToBasePushforward B S hS .fppf).obj
        ((smallEtaleToBaseModulePullback B S hS .fppf).obj
          ((SmallEtale.associatedModule B.toBigEtaleSite S hS).obj F)) ≅
      (SmallEtale.associatedModule B.toBigEtaleSite S hS).obj F :=
  (smallEtaleToBasePushforward B S hS .fppf).mapIso
      (smallEtaleToBasePullbackAssociatedModuleIso B S hS F) ≪≫
    eqToIso (pushforward_smallEtaleAssociatedSheaf B S hS F) ≪≫
    (smallEtaleAssociatedModuleIsoSheaf B S hS F).symm

/-- The counit of the associated-module adjunction of the small étale site is invertible at a
module quasi-coherent on that site. -/
private theorem isIso_associatedModule_counit_app
    (G : SheafOfModules.{u} (SmallEtale.structureSheaf B.toBigEtaleSite S hS))
    (hG : G.IsQuasicoherentOnSite) :
    IsIso ((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).counit.app G) :=
  SmallEtale.isIso_counit B.toBigEtaleSite S hS G hG
    (SmallEtale.isQuasicoherent_restrictModule B.toBigEtaleSite S hS G hG)

/-- **`R₂` applied to the unit of `a_S^* ⊣ a_{S,*}` at `𝓕^a` is an isomorphism.**  The unit of
the composite adjunction `(𝓕 ↦ 𝓕^a on S_étale) ⋙ a_S^* ⊣ a_{S,*} ⋙ (restriction to S_Zar)`
at `𝓕` is, after the transport along
`AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforwardCompIso`, the unit of the
associated-module adjunction of the big fppf site at `𝓕`, which Stacks 0GN7 makes invertible;
and that composite unit is the unit of the small étale associated-module adjunction at `𝓕`,
invertible by the small étale half of Stacks 0GN7, followed by the map in question. -/
public theorem isIso_restrictModule_map_smallEtaleToBaseUnit_app_associatedModule :
    IsIso ((SmallEtale.restrictModule B.toBigEtaleSite S hS).map
      ((smallEtaleToBaseModuleAdjunction B S hS .fppf).unit.app
        ((SmallEtale.associatedModule B.toBigEtaleSite S hS).obj F))) := by
  have h₁ : IsIso ((baseAssociatedModuleAdjunction B S hS .fppf).unit.app F) :=
    isIso_baseUnit_app B S hS .fppf F
  have h₂ : IsIso ((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).unit.app F) :=
    SmallEtale.unitIsoOnQuasicoherent B.toBigEtaleSite S hS ⟨F, inferInstance⟩
  -- the transported composite adjunction and its comparison of left adjoints
  have hX : IsIso (((((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).comp
      (smallEtaleToBaseModuleAdjunction B S hS .fppf)).ofNatIsoRight
        (smallEtaleToBasePushforwardCompIso B S hS .fppf)).unit.app F)) :=
    IsIso.of_isIso_fac_right (Adjunction.unit_leftAdjointUniq_hom_app
      ((((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).comp
        (smallEtaleToBaseModuleAdjunction B S hS .fppf)).ofNatIsoRight
          (smallEtaleToBasePushforwardCompIso B S hS .fppf)))
      (baseAssociatedModuleAdjunction B S hS .fppf) F)
  have hu : ((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).comp
        (smallEtaleToBaseModuleAdjunction B S hS .fppf)).unit.app F ≫
      (smallEtaleToBasePushforwardCompIso B S hS .fppf).hom.app _ =
      ((((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).comp
        (smallEtaleToBaseModuleAdjunction B S hS .fppf)).ofNatIsoRight
          (smallEtaleToBasePushforwardCompIso B S hS .fppf)).unit.app F) := by
    rfl
  have hC : IsIso ((((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).comp
      (smallEtaleToBaseModuleAdjunction B S hS .fppf)).unit.app F)) :=
    IsIso.of_isIso_fac_right hu
  exact IsIso.of_isIso_fac_left (Adjunction.comp_unit_app
    (SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS)
    (smallEtaleToBaseModuleAdjunction B S hS .fppf) F).symm

/-- **The unit of `a_S^* ⊣ a_{S,*}` is an isomorphism at `𝓕^a`**, for `𝓕` a quasi-coherent
`𝒪_S`-module.  Its image under restriction to the small Zariski site is an isomorphism, and
restriction reflects isomorphisms between modules quasi-coherent on the small étale site: the
counit `(R₂𝓗)^a ⟶ 𝓗` is invertible at such a module, and the naturality square of the counit
exhibits the map as a composite of three isomorphisms. -/
public theorem isIso_smallEtaleToBaseUnit_app_associatedModule :
    IsIso ((smallEtaleToBaseModuleAdjunction B S hS .fppf).unit.app
      ((SmallEtale.associatedModule B.toBigEtaleSite S hS).obj F)) := by
  have hsrc : ((SmallEtale.associatedModule B.toBigEtaleSite S hS).obj F
      ).IsQuasicoherentOnSite :=
    SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B.toBigEtaleSite S hS F
      inferInstance
  have htgt : ((smallEtaleToBasePushforward B S hS .fppf).obj
      ((smallEtaleToBaseModulePullback B S hS .fppf).obj
        ((SmallEtale.associatedModule B.toBigEtaleSite S hS).obj F))).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      (smallEtaleToBaseUnitTargetIso B S hS F).symm hsrc
  have hR := isIso_restrictModule_map_smallEtaleToBaseUnit_app_associatedModule B S hS F
  have hcs := isIso_associatedModule_counit_app B S hS _ hsrc
  have hct := isIso_associatedModule_counit_app B S hS _ htgt
  have hnat : (SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).counit.app
          ((SmallEtale.associatedModule B.toBigEtaleSite S hS).obj F) ≫
        (smallEtaleToBaseModuleAdjunction B S hS .fppf).unit.app
          ((SmallEtale.associatedModule B.toBigEtaleSite S hS).obj F) =
      (SmallEtale.associatedModule B.toBigEtaleSite S hS).map
          ((SmallEtale.restrictModule B.toBigEtaleSite S hS).map
            ((smallEtaleToBaseModuleAdjunction B S hS .fppf).unit.app
              ((SmallEtale.associatedModule B.toBigEtaleSite S hS).obj F))) ≫
        (SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).counit.app
          ((smallEtaleToBasePushforward B S hS .fppf).obj
            ((smallEtaleToBaseModulePullback B S hS .fppf).obj
              ((SmallEtale.associatedModule B.toBigEtaleSite S hS).obj F))) :=
    ((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).counit.naturality
      ((smallEtaleToBaseModuleAdjunction B S hS .fppf).unit.app
        ((SmallEtale.associatedModule B.toBigEtaleSite S hS).obj F))).symm
  exact IsIso.of_isIso_fac_left hnat

end Unit

/-- **The unit of `a_S^* ⊣ a_{S,*}` is an isomorphism at every module quasi-coherent on the small
étale site of `S`**, with no further hypothesis: `𝓗 ⟶ a_{S,*}a_S^*𝓗` is invertible.

Equivalently, the inverse image `a_S^*` along `a_S : ((Sch/S)_fppf, 𝒪) ⟶ (S_étale, 𝒪)` is fully
faithful on the modules quasi-coherent on `S_étale`.

Every such `𝓗` is the associated module `𝓕^a` of a quasi-coherent `𝒪_S`-module, namely of its
own restriction to the small Zariski site, by the essential surjectivity of [Stacks, Tag 03DX]
(2) at `τ = étale` — `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`,
which needs no hypothesis — and the unit is an isomorphism there by
`AlgebraicGeometry.BigFppfOver.isIso_smallEtaleToBaseUnit_app_associatedModule`.  The unit being
natural, its invertibility transports along that isomorphism. -/
public theorem isIso_smallEtaleToBaseUnit_app
    (G : SheafOfModules.{u} (SmallEtale.structureSheaf B.toBigEtaleSite S hS))
    (hG : G.IsQuasicoherentOnSite) :
    IsIso ((smallEtaleToBaseModuleAdjunction B S hS .fppf).unit.app G) := by
  have hc := isIso_associatedModule_counit_app B S hS G hG
  have := SmallEtale.isQuasicoherent_restrictModule B.toBigEtaleSite S hS G hG
  have h0 := isIso_smallEtaleToBaseUnit_app_associatedModule B S hS
    ((SmallEtale.restrictModule B.toBigEtaleSite S hS).obj G)
  have hnat : (SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).counit.app G ≫
        (smallEtaleToBaseModuleAdjunction B S hS .fppf).unit.app G =
      (smallEtaleToBaseModuleAdjunction B S hS .fppf).unit.app
          ((SmallEtale.associatedModule B.toBigEtaleSite S hS).obj
            ((SmallEtale.restrictModule B.toBigEtaleSite S hS).obj G)) ≫
        (smallEtaleToBasePushforward B S hS .fppf).map
          ((smallEtaleToBaseModulePullback B S hS .fppf).map
            ((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).counit.app G)) :=
    (smallEtaleToBaseModuleAdjunction B S hS .fppf).unit.naturality
      ((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).counit.app G)
  exact IsIso.of_isIso_fac_left hnat

end AlgebraicGeometry.BigFppfOver

end
