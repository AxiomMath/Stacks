module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyAtlasULift
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteGlobalCohomologyAtlas
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.ModuleCohomologyAbelianComparisonGlobal

/-!
# Global cohomology of sheaves of modules on the lisse-étale and the flat-fppf site

The module clauses of parts (1)(a) and (2)(a) of Stacks 0GR0 — "the same holds for sheaves of
modules" — for the global comparison: for an algebraic stack `𝒳` and a sheaf `ℱ` of
`𝒪_𝒳`-modules on `𝒳_étale` (respectively `𝒳_fppf`),

`H^p(𝒳_étale, ℱ) = H^p(𝒳_{lisse,étale}, g^*ℱ)` and `H^p(𝒳_fppf, ℱ) = H^p(𝒳_{flat,fppf}, g^*ℱ)`,

where `H^p` of a sheaf of modules is `Ext^p` out of the structure sheaf and `g^*` is restriction
of sheaves of modules, the structure sheaf of the subsite being the restriction of `𝒪_𝒳`
(Stacks 0788 (f)).

## The proof

The cohomology of a sheaf of modules is the cohomology of its underlying abelian sheaf, on any
site: that is Stacks 03FD, `Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIso`, which
needs no terminal object. Restriction of sheaves of modules forgets to restriction of abelian
sheaves on the nose. So the module comparison is the abelian one, parts (1)(a) and (2)(a), read
through Stacks 03FD on both sites.

The rings of `𝒪_𝒳` and the sections of its modules are taken in any universe `max (u + 1) t`
containing the site, as for the module clauses over an object
(`AlgebraicGeometry.Stack.LisseEtale.sliceModuleCohomologyIso`). The underlying abelian sheaves
then live in that universe, so the abelian comparison used is Stacks 07AK at those coefficients,
`AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlasOfLe`, with the hypotheses of
`AlgebraicGeometry.Stack.LisseEtale.globalCohomologyIso` and
`AlgebraicGeometry.Stack.FlatFppf.globalCohomologyIso`.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.globalModuleCohomologyIso`: **Stacks 0GR0** (1)(a) for
  sheaves of modules.
* `AlgebraicGeometry.Stack.FlatFppf.globalModuleCohomologyIso`: **Stacks 0GR0** (2)(a) for
  sheaves of modules.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 0GR0](https://stacks.math.columbia.edu/tag/0GR0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.BiggerSiteModules Stacks.Cohomology.ModuleAbelianComparison

namespace AlgebraicGeometry.Stack

universe u w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The lisse-étale site -/

namespace LisseEtale

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The structure sheaf `𝒪_𝒳` of Stacks 06TV on the étale site of `𝒳`, with its rings in the
universe `max (u + 1) t`, which contains the site. -/
noncomputable abbrev etaleStructureRing :
    Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) RingCat.{max (u + 1) t} :=
  ringStructureSheaf.{u, u + 1, u, t} B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (etaleTopology_le_topology B)

attribute [local instance] isContinuousInclusion

/-- **Stacks 0GR0, part (1)(a), for sheaves of modules.** For an algebraic stack `𝒳`, every degree
`q` and every sheaf `ℱ` of `𝒪_𝒳`-modules on the étale site of `𝒳`,

`H^q(𝒳_{lisse,étale}, g^*ℱ) ≅ H^q(𝒳_étale, ℱ)`,

naturally in `ℱ`, where `g^*` is restriction of sheaves of modules to the lisse-étale site of
Stacks 0787, over the restriction of `𝒪_𝒳`, and `H^q` of a sheaf of modules is `Ext^q` out of the
structure sheaf.

It is the abelian comparison, Stacks 07AK at the coefficients of the modules
(`AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlasOfLe`, with the hypotheses of
`AlgebraicGeometry.Stack.LisseEtale.globalCohomologyIso`), read through Stacks 03FD,
`Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIso`, on both sites. -/
@[stacks 0GR0 "part (1)(a), sheaves of modules"]
def globalModuleCohomologyIso (q : ℕ) :
    subsiteModuleRestriction.{u, u + 1, u, t} B S hS 𝒳.val.val.p (etaleTopology B)
          (smoothObject.{u, w} B S hS 𝒳) (etaleStructureRing.{u, w, t} B S hS 𝒳) ⋙
        moduleFunctorH.{t, u, u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
          (subsiteRing.{u, u + 1, u, t} B S hS 𝒳.val.val.p (etaleTopology B)
            (smoothObject.{u, w} B S hS 𝒳) (etaleStructureRing.{u, w, t} B S hS 𝒳)) q ≅
      moduleFunctorH.{t, u, u + 1} (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (etaleStructureRing.{u, w, t} B S hS 𝒳) q :=
  Functor.isoWhiskerLeft _ (moduleFunctorHIso.{t} _ _ q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Iso.refl (SheafOfModules.toSheaf _ ⋙
        (smoothObject.{u, w} B S hS 𝒳).ι.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) t}
          (inclusionTopology.{u, w} B S hS 𝒳)
          (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)))) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (subsiteCohomologyIsoOfAtlasOfLe.{u, w, t}
      (isClosedUnderSitePullback.{u, w} B S hS 𝒳) (exists_atlas.{u, w} B S hS 𝒳) q) ≪≫
    (moduleFunctorHIso.{t} _ _ q).symm

end LisseEtale

/-! ### The flat-fppf site -/

namespace FlatFppf

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The structure sheaf `𝒪_𝒳` of Stacks 06TV on the fppf site of `𝒳`, with its rings in the
universe `max (u + 1) t`, which contains the site. -/
noncomputable abbrev fppfStructureRing :
    Sheaf (fppfTopology B S hS 𝒳) RingCat.{max (u + 1) t} :=
  ringStructureSheaf.{u, u + 1, u, t} B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    B.topology le_rfl

attribute [local instance] isContinuous_inclusion'

/-- **Stacks 0GR0, part (2)(a), for sheaves of modules.** For an algebraic stack `𝒳`, every degree
`q` and every sheaf `ℱ` of `𝒪_𝒳`-modules on the fppf site of `𝒳`,

`H^q(𝒳_{flat,fppf}, g^*ℱ) ≅ H^q(𝒳_fppf, ℱ)`,

naturally in `ℱ`, where `g^*` is restriction of sheaves of modules to the flat-fppf site of
Stacks 0787, over the restriction of `𝒪_𝒳`, and `H^q` of a sheaf of modules is `Ext^q` out of the
structure sheaf.

It is the abelian comparison, Stacks 07AK at the coefficients of the modules
(`AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlasOfLe`, with the hypotheses of
`AlgebraicGeometry.Stack.FlatFppf.globalCohomologyIso`), read through Stacks 03FD,
`Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIso`, on both sites. -/
@[stacks 0GR0 "part (2)(a), sheaves of modules"]
def globalModuleCohomologyIso (q : ℕ) :
    subsiteModuleRestriction.{u, u + 1, u, t} B S hS 𝒳.val.val.p B.topology
          (objectProperty B S hS 𝒳) (fppfStructureRing.{u, w, t} B S hS 𝒳) ⋙
        moduleFunctorH.{t, u, u + 1} (inclusionTopology B S hS 𝒳)
          (subsiteRing.{u, u + 1, u, t} B S hS 𝒳.val.val.p B.topology
            (objectProperty B S hS 𝒳) (fppfStructureRing.{u, w, t} B S hS 𝒳)) q ≅
      moduleFunctorH.{t, u, u + 1} (fppfTopology B S hS 𝒳)
        (fppfStructureRing.{u, w, t} B S hS 𝒳) q :=
  Functor.isoWhiskerLeft _ (moduleFunctorHIso.{t} _ _ q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Iso.refl (SheafOfModules.toSheaf _ ⋙
        (objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) t}
          (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳))) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (subsiteCohomologyIsoOfAtlasOfLe.{u, w, t}
      (isClosedUnderSitePullback B S hS 𝒳) (exists_atlas.{u, w} B S hS 𝒳) q) ≪≫
    (moduleFunctorHIso.{t} _ _ q).symm

end FlatFppf

end AlgebraicGeometry.Stack

end
