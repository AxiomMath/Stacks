module

public import StacksFrontier.AlgebraicGeometry.Stacks.DerivedGlobalSectionsOnSmoothAndFlatSites
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedModuleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedModuleSectionsAlongARestriction
import StacksCore.Tactic.StacksAttribute

/-!
# Derived sections of modules on the lisse-étale and on the flat-fppf site

Let `𝒳` be an algebraic stack and let `g` be either of the comparison morphisms of ringed topoi
of Stacks 0788,

`g : (Sh(𝒳_{lisse,étale}), 𝒪_{𝒳_{lisse,étale}}) ⟶ (Sh(𝒳_{étale}), 𝒪_𝒳)` or
`g : (Sh(𝒳_{flat,fppf}), 𝒪_{𝒳_{flat,fppf}}) ⟶ (Sh(𝒳_{fppf}), 𝒪_𝒳)`,

where the structure sheaf of the small site is the restriction `g⁻¹𝒪_𝒳`, so that `g^* = g⁻¹` on
sheaves of modules. The statement of **Stacks 0H10** closes with: "In both cases, the same holds
for modules, since we have `g⁻¹ = g^*` and there is no difference in computing cohomology by
Cohomology on Sites, Lemma 0D6J." This file proves those module statements, for all four parts:
for `K` in the unbounded derived category of sheaves of `𝒪_𝒳`-modules,

* (1)(a) `RΓ(𝒳_{étale}, K) = RΓ(𝒳_{lisse,étale}, g^*K)`,
* (1)(b) `RΓ(x, K) = RΓ(𝒳_{lisse,étale}/x, g^*K)` for `x` an object of `𝒳_{lisse,étale}`,
* (2)(a) `RΓ(𝒳_{fppf}, K) = RΓ(𝒳_{flat,fppf}, g^*K)`,
* (2)(b) `RΓ(x, K) = RΓ(𝒳_{flat,fppf}/x, g^*K)` for `x` an object of `𝒳_{flat,fppf}`,

where each `RΓ` is the unbounded right derived functor, computed on complexes of modules, of the
corresponding sections functor (global sections, resp. sections over `x`). The proof is the
source's: by Stacks 0D6J each side is the derived functor of abelian sheaves applied to the
underlying complex, forgetting the module structure commutes with `g^* = g⁻¹`, and the abelian
statements are
`StacksFrontier/AlgebraicGeometry/Stacks/DerivedGlobalSectionsOnSmoothAndFlatSites.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/DerivedSectionsOverSmoothAndFlatObjects.lean`. The general
step is
`Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedModuleSectionsRestrictionIsoOfAbelian`.

## Universes

The structure sheaves have sections in `Type u` and the sheaves of modules have sections in
`Type (u + 1)`: the sites have objects in `Type (u + 1)` and morphisms in `Type u`, and the module
universe has to dominate both for `Mod(𝒪)` to be Grothendieck abelian, which is what makes the
unbounded derived functors exist. This is the convention of
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteDerivedModuleBaseChange.lean`, whose structure
sheaves `ambientRingStructureSheaf` are used here.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.derivedModuleGlobalSectionsRestrictionIso`: (1)(a).
* `AlgebraicGeometry.Stack.LisseEtale.derivedModuleSectionsRestrictionIso`: (1)(b).
* `AlgebraicGeometry.Stack.FlatFppf.derivedModuleGlobalSectionsRestrictionIso`: (2)(a).
* `AlgebraicGeometry.Stack.FlatFppf.derivedModuleSectionsRestrictionIso`: (2)(b).

## References

* [Stacks Project, Tag 0H10](https://stacks.math.columbia.edu/tag/0H10)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedLowerShriek.BigSite

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` and its Grothendieck
counterpart leave a stuck universe constraint against modules in the pinned universe `u + 1`;
the instances used here are Mathlib's, from sheafification in that universe. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

namespace FlatFppf

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'
  Stacks.Cohomology.GlobalSections.additive_Γ

/-- Sheafification of abelian presheaves with sections in `Type (u + 1)` on the flat-fppf site. -/
theorem hasSheafify_inclusionTopology_succ :
    HasSheafify (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- On the flat-fppf site, sheafification of abelian presheaves with sections in `Type (u + 1)`
inverts exactly the locally bijective morphisms. -/
theorem wEqualsLocallyBijective_inclusionTopology_succ :
    (inclusionTopology B S hS 𝒳).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _

/-- Sheafification of abelian presheaves with sections in `Type (u + 1)` on the fppf site. -/
theorem hasSheafify_fppfTopology_succ :
    HasSheafify (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- On the fppf site, sheafification of abelian presheaves with sections in `Type (u + 1)`
inverts exactly the locally bijective morphisms. -/
theorem wEqualsLocallyBijective_fppfTopology_succ :
    (fppfTopology B S hS 𝒳).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _

attribute [local instance] hasSheafify_inclusionTopology_succ
  wEqualsLocallyBijective_inclusionTopology_succ hasSheafify_fppfTopology_succ
  wEqualsLocallyBijective_fppfTopology_succ

/-- **Stacks 0H10, part (2)(a), for sheaves of modules.** For every `K` in the unbounded derived
category of sheaves of `𝒪_𝒳`-modules on `𝒳_{fppf}`,
`RΓ(𝒳_{flat,fppf}, g^*K) = RΓ(𝒳_{fppf}, K)`, naturally in `K`, both sides computed on complexes
of modules; `𝒪_{𝒳_{flat,fppf}} = g⁻¹𝒪_𝒳` and `g^* = g⁻¹`. -/
@[stacks 0H10 "part (2)(a) for sheaves of modules (the closing sentence of the statement), with \
NO hypothesis: derived global sections on the flat-fppf site of g^*K, computed on complexes of \
modules, are those of K on the fppf site"]
def derivedModuleGlobalSectionsRestrictionIso :
    haveI := hasPointwiseRightKanExtension_inclusion_ab.{u, w, u + 1} B S hS 𝒳
    (Stacks.Cohomology.DerivedLowerShriek.BigSite.moduleInverseImage (inclusionTopology B S hS 𝒳)
        (fppfTopology B S hS 𝒳)
        (objectProperty B S hS 𝒳).ι (ambientRingStructureSheaf B S hS 𝒳)).mapDerivedCategory ⋙
        derivedModuleOf (restrictedRing (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳)
          (objectProperty B S hS 𝒳).ι (ambientRingStructureSheaf B S hS 𝒳))
          (Sheaf.Γ (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) ≅
      derivedModuleOf (ambientRingStructureSheaf B S hS 𝒳)
        (Sheaf.Γ (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) :=
  haveI := hasPointwiseRightKanExtension_inclusion_ab.{u, w, u + 1} B S hS 𝒳
  derivedModuleSectionsRestrictionIsoOfAbelian _ _ _ _ _ _
    (constantIntegerSheaf.{u + 1} (inclusionTopology B S hS 𝒳))
    (Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation.{u + 1}
      (inclusionTopology B S hS 𝒳)).symm
    (isTorsionFree_constantIntegerSheaf (inclusionTopology B S hS 𝒳))
    (constantIntegerSheaf.{u + 1} (fppfTopology B S hS 𝒳))
    (Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation.{u + 1}
      (fppfTopology B S hS 𝒳)).symm
    (isTorsionFree_constantIntegerSheaf (fppfTopology B S hS 𝒳))
    (derivedGlobalSectionsRestrictionIso B S hS 𝒳)

/-- **Stacks 0H10, part (2)(b), for sheaves of modules.** For every object `x` of the flat-fppf
site and every `K` in the unbounded derived category of sheaves of `𝒪_𝒳`-modules on
`𝒳_{fppf}`, `RΓ(x, g^*K) = RΓ(x, K)`, naturally in `K`, both sides computed on complexes of
modules, cohomology over `x` being the derived functor of sections over `x`. -/
@[stacks 0H10 "part (2)(b) for sheaves of modules (the closing sentence of the statement), with \
NO hypothesis; cohomology over an object is the derived functor of sections over it"]
def derivedModuleSectionsRestrictionIso
    (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)) :
    haveI := hasPointwiseRightKanExtension_inclusion_ab.{u, w, u + 1} B S hS 𝒳
    (Stacks.Cohomology.DerivedLowerShriek.BigSite.moduleInverseImage (inclusionTopology B S hS 𝒳)
        (fppfTopology B S hS 𝒳)
        (objectProperty B S hS 𝒳).ι (ambientRingStructureSheaf B S hS 𝒳)).mapDerivedCategory ⋙
        derivedModuleOf (restrictedRing (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳)
          (objectProperty B S hS 𝒳).ι (ambientRingStructureSheaf B S hS 𝒳))
          (abelianSections.{u + 1} (inclusionTopology B S hS 𝒳) x) ≅
      derivedModuleOf (ambientRingStructureSheaf B S hS 𝒳)
        (abelianSections.{u + 1} (fppfTopology B S hS 𝒳) ((objectProperty B S hS 𝒳).ι.obj x)) :=
  haveI := hasPointwiseRightKanExtension_inclusion_ab.{u, w, u + 1} B S hS 𝒳
  derivedModuleSectionsRestrictionIsoOfAbelian _ _ _ _ _ _
    (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{u + 1}
      (inclusionTopology B S hS 𝒳) x)
    (abelianSectionsCorepresentation.{u + 1} (inclusionTopology B S hS 𝒳) x)
    (isTorsionFree_extensionByZeroUnitAb (inclusionTopology B S hS 𝒳) x)
    (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{u + 1} (fppfTopology B S hS 𝒳)
      ((objectProperty B S hS 𝒳).ι.obj x))
    (abelianSectionsCorepresentation.{u + 1} (fppfTopology B S hS 𝒳)
      ((objectProperty B S hS 𝒳).ι.obj x))
    (isTorsionFree_extensionByZeroUnitAb (fppfTopology B S hS 𝒳)
      ((objectProperty B S hS 𝒳).ι.obj x))
    (derivedSectionsRestrictionIsoOfFlatObject B S hS 𝒳 x)

end FlatFppf

namespace LisseEtale

/-- Sheafification of abelian presheaves with sections in `Type (u + 1)` on the lisse-étale
site. -/
theorem hasSheafify_inclusionTopology_succ :
    HasSheafify (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- On the lisse-étale site, sheafification of abelian presheaves with sections in
`Type (u + 1)` inverts exactly the locally bijective morphisms. -/
theorem wEqualsLocallyBijective_inclusionTopology_succ :
    (inclusionTopology.{u, w} B S hS 𝒳).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _

/-- Sheafification of abelian presheaves with sections in `Type (u + 1)` on the étale site. -/
theorem hasSheafify_etaleTopology_succ :
    HasSheafify (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- On the étale site, sheafification of abelian presheaves with sections in `Type (u + 1)`
inverts exactly the locally bijective morphisms. -/
theorem wEqualsLocallyBijective_etaleTopology_succ :
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _

attribute [local instance] hasSheafify_inclusionTopology_succ
  wEqualsLocallyBijective_inclusionTopology_succ hasSheafify_etaleTopology_succ
  wEqualsLocallyBijective_etaleTopology_succ

/-- Global sections of abelian sheaves on the lisse-étale site are additive, being a right
adjoint. -/
theorem additive_globalSections_inclusionTopology :
    (Sheaf.Γ (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u + 1}).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{0, u, u + 1} _

/-- Global sections of abelian sheaves on the étale site are additive, being a right
adjoint. -/
theorem additive_globalSections_etaleTopology :
    (Sheaf.Γ (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      AddCommGrpCat.{u + 1}).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{0, u, u + 1} _

attribute [local instance] additive_globalSections_inclusionTopology
  additive_globalSections_etaleTopology

/-- **Stacks 0H10, part (1)(a), for sheaves of modules.** For every `K` in the unbounded derived
category of sheaves of `𝒪_𝒳`-modules on `𝒳_{étale}`,
`RΓ(𝒳_{lisse,étale}, g^*K) = RΓ(𝒳_{étale}, K)`, naturally in `K`, both sides computed on
complexes of modules; `𝒪_{𝒳_{lisse,étale}} = g⁻¹𝒪_𝒳` and `g^* = g⁻¹`. -/
@[stacks 0H10 "part (1)(a) for sheaves of modules (the closing sentence of the statement), with \
NO hypothesis: derived global sections on the lisse-étale site of g^*K, computed on complexes of \
modules, are those of K on the étale site"]
def derivedModuleGlobalSectionsRestrictionIso :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    (Stacks.Cohomology.DerivedLowerShriek.BigSite.moduleInverseImage
        (inclusionTopology.{u, w} B S hS 𝒳)
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (smoothObject.{u, w} B S hS 𝒳).ι (ambientRingStructureSheaf B S hS 𝒳)).mapDerivedCategory ⋙
        derivedModuleOf (restrictedRing (inclusionTopology.{u, w} B S hS 𝒳)
          (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
          (smoothObject.{u, w} B S hS 𝒳).ι (ambientRingStructureSheaf B S hS 𝒳))
          (Sheaf.Γ (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u + 1}) ≅
      derivedModuleOf (ambientRingStructureSheaf B S hS 𝒳)
        (Sheaf.Γ (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
          AddCommGrpCat.{u + 1}) :=
  haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  derivedModuleSectionsRestrictionIsoOfAbelian _ _ _ _ _ _
    (constantIntegerSheaf.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳))
    (Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation.{u + 1}
      (inclusionTopology.{u, w} B S hS 𝒳)).symm
    (isTorsionFree_constantIntegerSheaf (inclusionTopology.{u, w} B S hS 𝒳))
    (constantIntegerSheaf.{u + 1} (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)))
    (Stacks.Cohomology.GlobalSections.globalSectionsCorepresentation.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).symm
    (isTorsionFree_constantIntegerSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)))
    (derivedGlobalSectionsRestrictionIso B S hS 𝒳)

/-- **Stacks 0H10, part (1)(b), for sheaves of modules.** For every object `x` of the
lisse-étale site and every `K` in the unbounded derived category of sheaves of `𝒪_𝒳`-modules on
`𝒳_{étale}`, `RΓ(x, g^*K) = RΓ(x, K)`, naturally in `K`, both sides computed on complexes of
modules, cohomology over `x` being the derived functor of sections over `x`. -/
@[stacks 0H10 "part (1)(b) for sheaves of modules (the closing sentence of the statement), with \
NO hypothesis; cohomology over an object is the derived functor of sections over it"]
def derivedModuleSectionsRestrictionIso (x : LisseEtale.{u, w} B S hS 𝒳) :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    (Stacks.Cohomology.DerivedLowerShriek.BigSite.moduleInverseImage
        (inclusionTopology.{u, w} B S hS 𝒳)
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (smoothObject.{u, w} B S hS 𝒳).ι (ambientRingStructureSheaf B S hS 𝒳)).mapDerivedCategory ⋙
        derivedModuleOf (restrictedRing (inclusionTopology.{u, w} B S hS 𝒳)
          (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
          (smoothObject.{u, w} B S hS 𝒳).ι (ambientRingStructureSheaf B S hS 𝒳))
          (abelianSections.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳) x) ≅
      derivedModuleOf (ambientRingStructureSheaf B S hS 𝒳)
        (abelianSections.{u + 1} (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
          ((smoothObject.{u, w} B S hS 𝒳).ι.obj x)) :=
  haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  derivedModuleSectionsRestrictionIsoOfAbelian _ _ _ _ _ _
    (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{u + 1}
      (inclusionTopology.{u, w} B S hS 𝒳) x)
    (abelianSectionsCorepresentation.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳) x)
    (isTorsionFree_extensionByZeroUnitAb (inclusionTopology.{u, w} B S hS 𝒳) x)
    (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      ((smoothObject.{u, w} B S hS 𝒳).ι.obj x))
    (abelianSectionsCorepresentation.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      ((smoothObject.{u, w} B S hS 𝒳).ι.obj x))
    (isTorsionFree_extensionByZeroUnitAb
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      ((smoothObject.{u, w} B S hS 𝒳).ι.obj x))
    (derivedSectionsRestrictionIso B S hS 𝒳 x)

end LisseEtale

end AlgebraicGeometry.Stack

end
