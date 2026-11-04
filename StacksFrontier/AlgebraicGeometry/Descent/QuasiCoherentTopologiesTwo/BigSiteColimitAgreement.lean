module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreementRestrFun
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsFppfSite

/-!
# Stacks 0GNE (1) at the big sites of a scheme: the colimits agree

Descent, Lemma 0GNE (1) says that `QCoh((Sch/S)_fppf, 𝒪)` has colimits, and that they agree
with the colimits of the same diagram computed in the three ambient categories
`Mod((Sch/S)_Zar, 𝒪)`, `Mod((Sch/S)_étale, 𝒪)` and `Mod((Sch/S)_fppf, 𝒪)`.  The clause is not
`τ`-quantified: the category whose colimits are taken is the fppf one in all three cases, and
what varies is the category the colimit is compared in.

Two of the three halves were already in the library as implications over the
essential-surjectivity hypothesis
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`
(`AlgebraicGeometry.BigFppfOver.hasColimitsOfSize_quasicoherentOnSite'` and
`…preservesColimitsOfSize_quasicoherentOnSite_ι'`), and that hypothesis is now a theorem,
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`.  They are
restated here with it discharged.

The third half — the agreement with the coarser big sites — reduces to
the agreement for a diagram of **associated** modules
(`AlgebraicGeometry.BigFppfOver.isColimitMapCoconeRestrictTopologyAssociatedModuleQcoh`), the
source's own reduction of an arbitrary diagram to one of associated modules being the essential
surjectivity of `𝓕 ↦ 𝓕^a`.  With Stacks 03DX (1) for `τ = fppf` proved as an equivalence
(`AlgebraicGeometry.BigFppfOver.associatedModuleEquivalence_fppf`) that reduction is available,
and the clause is proved here for an **arbitrary** diagram of quasi-coherent modules on
`(Sch/S)_fppf`.

## Main results

* `AlgebraicGeometry.BigFppfOver.hasColimitsOfSize_quasicoherentOnSite_fppf`: **Stacks 0GNE (1),
  the existence half**, with no hypothesis.
* `AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_quasicoherentOnSite_ι_fppf`: **Stacks
  0GNE (1), the agreement with `Mod((Sch/S)_fppf, 𝒪)`**, with no hypothesis.
* `AlgebraicGeometry.BigFppfOver`
  `.preservesColimitsOfShape_quasicoherentOnSite_ι_comp_restrictTopology`
  and `…preservesColimitsOfSize_quasicoherentOnSite_ι_comp_restrictTopology`: **Stacks 0GNE (1),
  the agreement with `Mod((Sch/S)_τ, 𝒪)`** at every one of the five topologies, and so in
  particular with `Mod((Sch/S)_Zar, 𝒪)` and `Mod((Sch/S)_étale, 𝒪)` — for an arbitrary diagram.
* `AlgebraicGeometry.BigFppfOver.isColimitMapCoconeRestrictTopologyQuasicoherentOnSite`: the same
  read on cocones — a colimit cocone of a diagram of quasi-coherent modules on `(Sch/S)_fppf`,
  read in `Mod((Sch/S)_τ, 𝒪)`, is a colimit cocone there.

## Implementation notes

The reduction of an arbitrary diagram to a diagram of associated modules is performed on the
functor rather than on the diagram.  Write `ι_τ` for the composite
"include into `Mod((Sch/S)_fppf, 𝒪)`, then read for `τ`" and `e` for the equivalence
`QCoh(𝒪_S) ≌ QCoh((Sch/S)_fppf, 𝒪)` of Stacks 03DX (1).  Then

* `e.functor ⋙ ι_τ` is `𝓕 ↦ 𝓕^a` followed by the reading for `τ`, which by
  `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleQcohIso` — the key to Stacks
  0GNE, as an isomorphism of **functors** — is the associated-module functor of `(Sch/S)_τ`, and
  that preserves colimits, being a left adjoint composed with the inclusion of the
  quasi-coherent modules of `S`;
* `e.inverse ⋙ e.functor ⋙ ι_τ ≅ ι_τ` by `CategoryTheory.Equivalence.invFunIdAssoc`, and
  `e.inverse` preserves colimits because it is an equivalence.

So `ι_τ` preserves colimits, which is the clause for every diagram at once; stating it this way
rather than diagram by diagram is what makes the reduction a composition of functors instead of
a transport of a cocone along an isomorphism of diagrams.

`e.functor ⋙ ι_τ = associatedModuleQcoh ⋙ restrictTopology τ` holds by `rfl`: the functor of
the equivalence is `AlgebraicGeometry.BigFppfOver.associatedModuleQcoh` corestricted to the
quasi-coherent modules of the site, and `CategoryTheory.ObjectProperty.liftCompιIso` — the
identity isomorphism — undoes the corestriction.

The shapes are `K : Type u` with `Category.{u} K`, `u` being the universe of the morphisms of
the site; this is the convention of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentTransfer`, whose
implementation notes explain why a bare `HasColimits` would say something else.  The two
colimit-existence hypotheses that
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_baseAssociatedModuleQcoh` carries —
colimits of shape `K` in `ModuleCat.{u} R` and in the `𝒪_S`-modules of the small Zariski site —
are found by instance search at those shapes, so nothing below has a hypothesis.

## Coverage limits

* The three ambient categories of the source's clause are `Mod((Sch/S)_Zar, 𝒪)`,
  `Mod((Sch/S)_étale, 𝒪)` and `Mod((Sch/S)_fppf, 𝒪)`, and all three are covered: the `τ`-results
  below are stated for an arbitrary `AlgebraicGeometry.SiteKind`.
* The category whose colimits are taken is `QCoh((Sch/S)_fppf, 𝒪)` throughout, which is what the
  source's clause asks.  The analogous statement for `QCoh((Sch/S)_τ, 𝒪)` at `τ ≠ fppf` is not
  made and is not part of this clause; it would need the essential surjectivity of `𝓕 ↦ 𝓕^a`
  at that `τ`, which is
  `AlgebraicGeometry.BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule τ`
  (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/QuasiCoherentSmallEtaleBigSite.lean:113`) and
  is proved at no `τ ≠ fppf`.
* Stacks 06WN (1) is the same pair of assertions for the associated `τ`-site of a category
  fibred in groupoids.  Nothing below advances it: the reduction used here is the equivalence of
  Stacks 03DX (1) over a *scheme*.

## References

* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GNE (1), the existence half**, with no hypothesis: the category of quasi-coherent
`𝒪`-modules on the big fppf site of `S` has all colimits indexed at the size of the site.

`AlgebraicGeometry.BigFppfOver.hasColimitsOfSize_quasicoherentOnSite'` with its
essential-surjectivity hypothesis discharged by
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`. -/
@[stacks 0GNE "part (1), existence: QCoh((Sch/S)_fppf, O) has colimits indexed at the size of \
the site"]
public theorem hasColimitsOfSize_quasicoherentOnSite_fppf :
    HasColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  hasColimitsOfSize_quasicoherentOnSite' B S hS
    (quasicoherentIsEssImageAssociatedModule' B S hS)

/-- **Stacks 0GNE (1), the agreement with `Mod((Sch/S)_fppf, 𝒪)`**, with no hypothesis: a colimit
of quasi-coherent `𝒪`-modules on `(Sch/S)_fppf` is the colimit of the same diagram taken in all
`𝒪`-modules on `(Sch/S)_fppf`.

`AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_quasicoherentOnSite_ι'` with its
essential-surjectivity hypothesis discharged. -/
@[stacks 0GNE "part (1), agreement: the colimits of QCoh((Sch/S)_fppf, O) are the colimits \
taken in Mod((Sch/S)_fppf, O)"]
public theorem preservesColimitsOfSize_quasicoherentOnSite_ι_fppf :
    PreservesColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).ι :=
  preservesColimitsOfSize_quasicoherentOnSite_ι' B S hS
    (quasicoherentIsEssImageAssociatedModule' B S hS)

section Agreement

variable (τ : SiteKind)

/-- **Stacks 0GNE (1), the agreement with `Mod((Sch/S)_τ, 𝒪)`, of shape `K`.**  A colimit of
quasi-coherent `𝒪`-modules on `(Sch/S)_fppf` is the colimit of the same diagram taken in the
`𝒪`-modules of the coarser big site `(Sch/S)_τ`, for an **arbitrary** diagram.

This is the half of the source's clause (1) that compares with `Mod((Sch/S)_Zar, 𝒪)` and
`Mod((Sch/S)_étale, 𝒪)`.
`AlgebraicGeometry.BigFppfOver.isColimitMapCoconeRestrictTopologyAssociatedModuleQcoh` had it
for a diagram of associated modules; the reduction of an arbitrary diagram to that case is the
equivalence of Stacks 03DX (1) for `τ = fppf`,
`AlgebraicGeometry.BigFppfOver.associatedModuleEquivalence_fppf`, performed here on the functor
rather than on the diagram — see the implementation notes. -/
public theorem preservesColimitsOfShape_quasicoherentOnSite_ι_comp_restrictTopology
    (K : Type u) [Category.{u} K] :
    PreservesColimitsOfShape K
      ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (structureSheaf B S hS)).ι ⋙
        restrictTopology B S hS τ) := by
  set e := associatedModuleEquivalence_fppf B S hS
  -- `e.functor ⋙ ι` is `𝓕 ↦ 𝓕^a` on the nose, and that followed by the reading for `τ` is the
  -- associated-module functor of `(Sch/S)_τ`, which preserves colimits.
  have h1 : PreservesColimitsOfShape K
      (e.functor ⋙ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).ι ⋙ restrictTopology B S hS τ) :=
    have := preservesColimitsOfShape_baseAssociatedModuleQcoh B S hS τ K
    preservesColimitsOfShape_of_natIso (restrictTopologyAssociatedModuleQcohIso B S hS τ)
  -- precomposing with `e.inverse`, which preserves colimits, returns `ι ⋙ restrictTopology τ`.
  have h2 : PreservesColimitsOfShape K
      (e.inverse ⋙ e.functor ⋙ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).ι ⋙ restrictTopology B S hS τ) :=
    have := h1
    inferInstance
  have := h2
  exact preservesColimitsOfShape_of_natIso (Equivalence.invFunIdAssoc e _)

/-- **Stacks 0GNE (1), the agreement with `Mod((Sch/S)_τ, 𝒪)`**, over every shape indexed at the
size of the site: the colimits of `QCoh((Sch/S)_fppf, 𝒪)` are the colimits taken in
`Mod((Sch/S)_τ, 𝒪)`, at every one of the five topologies and for an arbitrary diagram.

Together with `AlgebraicGeometry.BigFppfOver.hasColimitsOfSize_quasicoherentOnSite_fppf` and
`…preservesColimitsOfSize_quasicoherentOnSite_ι_fppf` this is the source's clause (1): the
colimits exist and agree with those computed in `Mod((Sch/S)_Zar, 𝒪)`,
`Mod((Sch/S)_étale, 𝒪)` and `Mod((Sch/S)_fppf, 𝒪)`. -/
@[stacks 0GNE "part (1), agreement: the colimits of QCoh((Sch/S)_fppf, O) are the colimits \
taken in Mod((Sch/S)_tau, O), for every one of the five topologies and for an arbitrary diagram"]
public theorem preservesColimitsOfSize_quasicoherentOnSite_ι_comp_restrictTopology :
    PreservesColimitsOfSize.{u, u}
      ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (structureSheaf B S hS)).ι ⋙
        restrictTopology B S hS τ) where
  preservesColimitsOfShape {K} _ :=
    preservesColimitsOfShape_quasicoherentOnSite_ι_comp_restrictTopology B S hS τ K

/-- **Stacks 0GNE (1), the agreement with `Mod((Sch/S)_τ, 𝒪)`, read on cocones.**  Take a
diagram of quasi-coherent `𝒪`-modules on `(Sch/S)_fppf` and a colimit cocone for it in
`QCoh((Sch/S)_fppf, 𝒪)`.  Its image in `Mod((Sch/S)_τ, 𝒪)` is a colimit cocone there — so the
colimit taken on the big fppf site and the colimit taken on `(Sch/S)_τ` are the same object with
the same cocone, not merely isomorphic objects.

`AlgebraicGeometry.BigFppfOver.isColimitMapCoconeRestrictTopologyAssociatedModuleQcoh` is the
same statement for a diagram of associated modules; the diagram here is arbitrary. -/
public noncomputable def isColimitMapCoconeRestrictTopologyQuasicoherentOnSite
    (K : Type u) [Category.{u} K]
    {D : K ⥤ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).FullSubcategory}
    {c : Cocone D} (hc : IsColimit c) :
    IsColimit ((restrictTopology B S hS τ).mapCocone
      ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).ι.mapCocone c)) :=
  have := preservesColimitsOfShape_quasicoherentOnSite_ι_comp_restrictTopology B S hS τ K
  isColimitOfPreserves ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (structureSheaf B S hS)).ι ⋙ restrictTopology B S hS τ) hc

end Agreement

end BigFppfOver

end AlgebraicGeometry

end
