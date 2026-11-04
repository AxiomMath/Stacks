module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineLimitEtaleCohomology
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeAlgebraSystemCohomologySupplement
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.BiggerSiteGlobalCohomologySupplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomologySupplement

/-!
# Stacks 03Q6 with its cohomology identified with the library's etale cohomology

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/BaseChangeAlgebraSystemCohomology.lean`
proves Stacks 03Q6 for an affine `X`, with the cohomology taken as the right derived functors of
`sheafSections` on the universe-raised small *affine* etale sites that Stacks 09YP is stated on.
This file replaces those groups by the library's mainstream etale cohomology functor
`Stacks.EtaleCohomology.etaleCohomologyFunctor`, at both ends of the colimit:

`H^p_etale(Y, 𝒢') = colim_i H^p_etale(Y_i, F_i')`.

## Main results

* `bcCoconeVertexIsoEtaleCohomology` — the vertex of the cohomology cocone of Stacks 03Q6 is the
  etale cohomology group `H^p_etale(Y, 𝒢')` of the limit `Y = Spec B ×_{Spec A} X`.
* `etaleCohomologyColimit_baseChange_systemLimit_colimitSheaf_etale_isColimit` — **Stacks 03Q6
  for an affine `X`, at the canonical limit, with the colimit sheaf constructed and the vertex of
  the colimit the library's etale cohomology of `Y`.**
* `bcDiagramObjIsoEtaleCohomology` — every group of the cohomology diagram of Stacks 03Q6 is the
  etale cohomology group `H^p_etale(Y_j, F_j')` of a level.

## Implementation notes

Everything here is an instantiation at the system of base changes `baseChange T X Z` of the two
general identifications of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/AffineLimitEtaleCohomology.lean`, which
are in turn the cohomological form of Stacks 04HR
(`affineEtaleCohomologyFunctorIso`, needing no affineness of its scheme) composed with the
passage across the universe raise of the site that Stacks 09YP computes on
(`raisedAffineEtaleCohomologyFunctorIso`) and across the small models of the levels of Stacks 0EYL
(`Stacks.EtaleCohomology.AffineLimitCohomology.levelCohomologyFunctorIso`).

The abelian sheaf `𝒢` on the small etale site of `Y` that the conclusion is about is
`raisedToSmallEtale`, the sheaf the colimit sheaf `bcColimitSheaf` comes from across those two
equivalences; the sheaf on the small etale site of `Y_j` is
`Stacks.EtaleCohomology.AffineLimitCohomology.levelToSmallEtale` of `F_j`.

What is still not covered, and what the clause strings of the tags say: `X` is affine, where the
source allows any quasi-compact quasi-separated `X ⟶ Spec(A)`; the system `F` of abelian sheaves
on the levels is given rather than being the system of inverse images of one sheaf on `X`; and
the *transition maps* of the cohomology diagram are not identified with the transition maps of
`Stacks.EtaleCohomology.etaleCohomologyFunctor` — only the groups themselves are, object by
object.

That last identification is the naturality of the comparison in the index, and two earlier
descriptions of it in this file were wrong. It is *not* entangled with the system `F` being a
system of inverse images: the naturality square
`Stacks.EtaleCohomology.TransitionBaseChange.edge_levelEtaleSquare` is proved for an arbitrary
pair of abelian sheaves on two stages together with a transition map between them, with no
inverse-image hypothesis anywhere. And the naturality is no longer unproved: the transition maps
of the cohomology diagram are the Leray edge morphisms of the direct image along the transition
functor (`Stacks.WeakSites.ColimitSiteCohomology.CohomologyCocone.diagram_map_eq_edge_app`), the
square relating those to the transition maps of the derived sections of the small etale sites of
the levels commutes (`...TransitionBaseChange.edge_levelEtaleSquare`), and the vertical
comparisons of that square are isomorphisms
(`...TransitionBaseChange.isIso_edge_levelEtaleRestrict`).

The *renaming* of the groups of that square as `etaleCohomologyFunctor` is done, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LevelEtaleSquareEtaleCohomology.lean`:
`...TransitionBaseChange.sectionsRightDerivedIsoEtaleCohomology` is
`Stacks.Cohomology.GlobalSections.rightDerivedSectionsIsoFunctorH` read on the small etale site of
the stage, `...TransitionBaseChange.levelEtaleCohomologyIso` is the resulting object-by-object
comparison as an isomorphism, and `...TransitionBaseChange.levelEtaleCohomologyIso_naturality` is
the square with both ends renamed — the index-naturality in the `etaleCohomologyFunctor`
spelling. It needs the image of the object the sections are taken over to be terminal in the small
etale site of the stage, which `...TransitionBaseChange.isTerminal_levelEtale_obj` supplies for an
affine stage and which is false for a non-affine one.

What is genuinely left is a *bridge* between the two comparisons: the one in the square is the
edge morphism, built from injective resolutions, while the one in
`bcDiagramObjIsoEtaleCohomology` is `levelCohomologyFunctorIsoEtaleCohomology`, built from
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence` and so from `Ext` and the
comparison of constant sheaves. Half of that bridge is proved —
`Stacks.Cohomology.RightDerivedEdge.edge_app_eq_compRightDerivedNatIso_inv_app`, the edge morphism
of an exact injective-preserving functor is the inverse of
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, the engine of
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp`. The other half is not: the `Ext`-side
comparison actually used goes through `extFunctorObjIsoCompOfIsoOfAcyclic`, whose engine is
`ModuleSheafCohomology.extComparisonIso` — delta-functor universality, Stacks 010T and 010U, with
no pinning lemma in this library — and through the degree-split `extFunctorObjIsoRightDerived` and
`rightDerivedΓIsoFunctorH`, whose branches this library does not claim to be compatible.

## References

* [Stacks 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)
* [Stacks 04HR](https://stacks.math.columbia.edu/tag/04HR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe u

namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.AffineLimitCohomology
open Stacks.WeakSites.ColimitSiteCohomology

attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion hasSheafify_smallAffineEtale hasSheafify_smallEtale
  locallySmall_smallAffineEtale locallySmall_smallEtale enoughInjectives_smallAffineEtale
  enoughInjectives_smallEtale hasExt_smallAffineEtale hasExt_smallEtale
  restrictToAffineEtale_isEquivalence CategoryTheory.AsSmall.isDenseSubsite_up
  hasSheafify_raisedAffineEtale locallySmall_raisedAffineEtale
  enoughInjectives_raisedAffineEtale hasExt_raisedAffineEtale

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
  [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
  (B : AlgebraicGeometry.BigEtaleSite.{u})
  (hD : ∀ i, B.Contains ((baseChange T X Z).obj i))
  (hY : B.Contains (systemLimitCone T X Z).pt)
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{u, u, u + 1, u + 1}
    (bcSys T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY))

/-- **The vertex of the cohomology cocone of Stacks 03Q6 is the etale cohomology of `Y`.** For
every degree `p`, the right derived functors of sections over the object of the site of
`Y = (lim_i Z_i) ×_T X` that Stacks 09YQ takes its cohomology over, applied to the colimit sheaf,
are the etale cohomology group `H^p_etale(Y, 𝒢')` where `𝒢'` is the abelian sheaf on the small
etale site of `Y` that `𝒢` comes from. -/
def bcCoconeVertexIsoEtaleCohomology
    (𝒢 : Sheaf (bcPrecoverage T X Z (systemLimitCone T X Z)
      (isLimitSystemLimitCone T X Z) B hD hY).toGrothendieck Ab.{u + 1})
    (i : (bcSys T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY).I)
    (p : ℕ) :
    ((((sheafSections (bcPrecoverage T X Z (systemLimitCone T X Z)
              (isLimitSystemLimitCone T X Z) B hD hY).toGrothendieck Ab.{u + 1}).obj
          (op ((bcToLimitSmall T X Z (systemLimitCone T X Z)
              (isLimitSystemLimitCone T X Z) B hD hY i).obj
            (bcLevelTerminal T X Z (systemLimitCone T X Z)
              (isLimitSystemLimitCone T X Z) B hD hY i)))).rightDerived p).obj 𝒢) ≅
      (Stacks.EtaleCohomology.etaleCohomologyFunctor B ⟨(systemLimitCone T X Z).pt, hY⟩ p).obj
        ((raisedToSmallEtale B (systemLimitCone T X Z).pt hY).obj 𝒢) :=
  coconeVertexIsoEtaleCohomology.{u, u} (baseChange T X Z) (systemLimitCone T X Z) B hD hY
    (isLimitSystemLimitCone T X Z) 𝒢 i p

/-- **Stacks 03Q6 for an affine `X`, at the canonical limit, with the colimit sheaf constructed
and the cohomology at the limit the library's etale cohomology.** Let `I` be a nonempty directed
preorder, let `T = Spec A` be affine, let `Z_i = Spec B_i` be a diagram of affine schemes over
`T`, let `X` be an affine scheme over `T`, and let `F` be a system of abelian sheaves on the small
affine etale sites of the levels `Y_i = Z_i ×_T X`. Then, for every degree `p`,

`H^p_etale(Y, 𝒢') = colim_i H^p(Y_i, F_i)`,

where `Y = (lim_i Z_i) ×_T X = Spec B ×_{Spec A} X` with `B = colim_i B_i`, the sheaf `𝒢'` on the
small etale site of `Y` is the one the constructed colimit sheaf `colim_i f_i^{-1} F_i` comes
from, and the right hand side is a filtered colimit: the canonical cohomology cocone, with its
vertex transported along `bcCoconeVertexIsoEtaleCohomology`, is a colimit cocone.

This is `etaleCohomologyColimit_baseChange_systemLimit_colimitSheaf_isColimit` with its vertex
replaced by the etale cohomology group it is isomorphic to. The groups of the *diagram* are
likewise etale cohomology groups of the levels, by `bcDiagramObjIsoEtaleCohomology`.

This is a partial form of [Stacks, Tag 03Q6]; the registered statement is
`Stacks.EtaleCohomology.ColimitBaseChange.isIso_colimitDesc_algebraCohomologyCocone`. -/
def etaleCohomologyColimit_baseChange_systemLimit_colimitSheaf_etale_isColimit
    (i : (bcSys T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY).I) (p : ℕ)
    (E : CohomologyCocone.{u, u, u + 1, u + 1}
      (bcSys T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY)
      (bcToLimitSmall T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY)
      (bcToLimitSmall_transition T X Z (systemLimitCone T X Z)
        (isLimitSystemLimitCone T X Z) B hD hY)
      (bcPrecoverage T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY) F
      (bcColimitSheaf T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY F)
      (bcColimitSheafLegs T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY F)
      i
      (bcLevelTerminal T X Z (systemLimitCone T X Z)
        (isLimitSystemLimitCone T X Z) B hD hY i) p :=
      bcCohomologyCocone T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY
        F i p) :
    IsColimit (E.cocone.extend (bcCoconeVertexIsoEtaleCohomology T X Z B hD hY
      (bcColimitSheaf T X Z (systemLimitCone T X Z)
        (isLimitSystemLimitCone T X Z) B hD hY F) i p).hom) :=
  IsColimit.ofIsoColimit
    (etaleCohomologyColimit_baseChange_systemLimit_colimitSheaf_isColimit T X Z B hD hY F i p E)
    (Cocone.ext (bcCoconeVertexIsoEtaleCohomology T X Z B hD hY
      (bcColimitSheaf T X Z (systemLimitCone T X Z)
        (isLimitSystemLimitCone T X Z) B hD hY F) i p) fun _ => rfl)

/-- **Every group of the cohomology diagram of Stacks 03Q6 is an etale cohomology group of a
level.** The value of the diagram at an arrow `A : j ⟶ i` is `H^p_etale(Y_j, F_j')`, where `F_j'`
is the abelian sheaf on the small etale site of `Y_j` that `F_j` comes from.

This is a partial form of [Stacks, Tag 03Q6]; the registered statement is
`Stacks.EtaleCohomology.ColimitBaseChange.isIso_colimitDesc_algebraCohomologyCocone`. -/
def bcDiagramObjIsoEtaleCohomology
    (i : (bcSys T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY).I) (p : ℕ)
    (E : CohomologyCocone.{u, u, u + 1, u + 1}
      (bcSys T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY)
      (bcToLimitSmall T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY)
      (bcToLimitSmall_transition T X Z (systemLimitCone T X Z)
        (isLimitSystemLimitCone T X Z) B hD hY)
      (bcPrecoverage T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY) F
      (bcColimitSheaf T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY F)
      (bcColimitSheafLegs T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY F)
      i
      (bcLevelTerminal T X Z (systemLimitCone T X Z)
        (isLimitSystemLimitCone T X Z) B hD hY i) p :=
      bcCohomologyCocone T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY
        F i p)
    (A : Over i) :
    E.diagram.obj (op A) ≅
      (Stacks.EtaleCohomology.etaleCohomologyFunctor B
          ⟨levelScheme (baseChange T X Z) (systemLimitCone T X Z) B hD hY
              (isLimitSystemLimitCone T X Z) A.left,
            hD (levelIndex (baseChange T X Z) (systemLimitCone T X Z) B hD hY
              (isLimitSystemLimitCone T X Z) A.left)⟩ p).obj
        ((levelToSmallEtale (baseChange T X Z) (systemLimitCone T X Z) B hD hY
          (isLimitSystemLimitCone T X Z) A.left).obj (F.obj A.left)) :=
  diagramObjIsoEtaleCohomology.{u, u} (baseChange T X Z) (systemLimitCone T X Z) B hD hY
    (isLimitSystemLimitCone T X Z) F
    (bcColimitSheaf T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY F)
    (bcColimitSheafLegs T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY F)
    i p E A

end Stacks.EtaleCohomology.BaseChangeAlgebraSystem

end
