module

public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleDerivedModuleLowerShriekULift
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleModuleDerivedBaseChange

/-!
# Stacks 07AV, second identity, on cohomology sheaves at the universe of the rings

Let `f : 𝒳 ⟶ 𝒴` be a smooth 1-morphism of algebraic stacks and `f'` its restriction to the
lisse-étale sites. The second identity of Stacks 07AV, `L(g')_! ∘ (f')^{-1} = f^{-1} ∘ Lg_!`, is
proved for sheaves of modules at the module universe `u + 1` of the étale sites
(`AlgebraicGeometry.Stack.LisseEtale.moduleDerivedLowerShriekBaseChangeIso`). This file derives
its consequence at the module universe `u` of the rings, for the derived lower shriek
`AlgebraicGeometry.Stack.LisseEtale.derivedModuleLowerShriek` of Stacks 07AS (2) at that universe:
for a sheaf of modules `H` on the lisse-étale site of `𝒴`,

`f^{-1} H^p(Lg_! H) ≅ H^p(L(g')_! (f')^{-1} H)`.

The universe lift `Λ` of the sections is fully faithful and commutes with `f^{-1}`, `(f')^{-1}` on
the nose and with the two derived lower shrieks on cohomology sheaves
(`AlgebraicGeometry.Stack.LisseEtale.nonempty_uliftHomologyDerivedModuleLowerShriekIso`), so the
identity at `u + 1` descends.

## Main definitions

* `AlgebraicGeometry.Stack.LisseEtale.lisseEtaleModuleRing`: the structure sheaf of the lisse-étale
  site, on its inherited topology.
* `AlgebraicGeometry.Stack.LisseEtale.lisseEtaleModuleInverseImage`: `(f')^{-1}` at the universe
  of the rings.

## Main results

* `nonempty_modulePullback_homology_derivedModuleLowerShriek_iso`:
  `f^{-1} H^p(Lg_! H) ≅ H^p(L(g')_! (f')^{-1} H)`.

## References

* [Stacks Project, Tag 07AV](https://stacks.math.columbia.edu/tag/07AV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedLowerShriek

namespace AlgebraicGeometry.Stack.LisseEtale

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'
  isContinuous_inclusion_topology' isCocontinuous_inclusion_topology'
  Stacks.hasSheafCompose_forget₂_commRingCat Stacks.essentiallySmall_over
  preservesCoveringPullbacks_inclusion preservesCoveringPullbacks_inclusion_topology
  GrothendieckTopology.hasSheafify_addCommGrpCat
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure sheaf of the lisse-étale site of `𝒳`, on its inherited topology: the ring of
07BA's derived lower shriek at the universe of the rings. -/
abbrev lisseEtaleModuleRing (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    Sheaf (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      RingCat.{u} :=
  inverseImageRing (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS 𝒳))
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
    (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
        (etaleTopology_le_topology B)).O)

variable {B S hS} {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsSmooth B S hS f)

/-- **Stacks 06TW on the lisse-étale sites, at their inherited topologies**: the structure sheaf of
the lisse-étale site of `𝒳` is the restriction along `f'` of that of `𝒴`, by the identification
`AlgebraicGeometry.Stack.LisseEtale.subsiteRingStructureSheaf_inverseImageRing` of the underlying
presheaves of rings (which do not depend on the topology). -/
def lisseEtaleModuleRingInverseImageHom :
    haveI := isContinuous_subsiteFunctor.{u, w} B S hS f hf
    lisseEtaleModuleRing B S hS 𝒳 ⟶
      ((primedSiteFunctor B S hS f hf).sheafPushforwardContinuous RingCat.{u}
        (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴)).obj
        (lisseEtaleModuleRing B S hS 𝒴) :=
  ObjectProperty.homMk (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm).hom

/-- The comparison `lisseEtaleModuleRingInverseImageHom f hf` of structure sheaves is an
isomorphism. -/
instance isIso_lisseEtaleModuleRingInverseImageHom :
    IsIso (lisseEtaleModuleRingInverseImageHom f hf) := by
  haveI := isContinuous_subsiteFunctor.{u, w} B S hS f hf
  have : IsIso ((sheafToPresheaf _ _).map (lisseEtaleModuleRingInverseImageHom f hf)) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map
      (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm)))
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- `(f')^{-1}` on sheaves of modules on the lisse-étale sites, at the universe of the rings:
restriction along `f'`, read over the structure sheaf of the lisse-étale site of `𝒳` through
`AlgebraicGeometry.Stack.LisseEtale.lisseEtaleModuleRingInverseImageHom`. -/
abbrev lisseEtaleModuleInverseImage :
    SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒴) ⥤
      SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒳) :=
  haveI := isContinuous_subsiteFunctor.{u, w} B S hS f hf
  SheafOfModules.pushforward.{u} (F := primedSiteFunctor B S hS f hf)
    (lisseEtaleModuleRingInverseImageHom f hf)

/-- `(f')^{-1}` commutes with raising the universe of the sections, on the nose. -/
def moduleSubsiteInverseImageULiftIso (M : SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒴)) :
    (moduleSubsiteInverseImage B S hS f hf).obj ((moduleULift B S hS 𝒴).obj M) ≅
      (moduleULift B S hS 𝒳).obj ((lisseEtaleModuleInverseImage f hf).obj M) :=
  Iso.refl _

/-- `f^{-1}` commutes with raising the universe of the sections, on the nose. -/
def modulePullbackULiftIso (M : SheafOfModules.{u}
      (SmallModel.targetRing (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)) :
    (ULiftComparison.targetULift _ _).obj
        ((AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p
          𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
          f.hom.hom.w (etaleTopology B) (etaleTopology_le_topology B)).obj M) ≅
      (AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS 𝒳.val.val.p
          𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
          f.hom.hom.w (etaleTopology B) (etaleTopology_le_topology B)).obj
        ((ULiftComparison.targetULift _ _).obj M) :=
  Iso.refl _


/-- **Stacks 07AV, second identity, on cohomology sheaves at the universe of the rings.** For a
smooth 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, a sheaf of modules `H` with sections in
`Type u` on the lisse-étale site of `𝒴` and every `p`,
`f^{-1} H^p(Lg_! H) ≅ H^p(L(g')_! (f')^{-1} H)`, for 07BA's derived lower shrieks of Stacks
07AS (2) at the universe of the rings, at the standard models of the derived categories. -/
theorem nonempty_modulePullback_homology_derivedModuleLowerShriek_iso
    (H : SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒴)) (p : ℤ) :
    letI := abelianEtaleModules B S hS 𝒳
    letI := abelianLisseEtaleModules B S hS 𝒳
    letI := abelianEtaleModules B S hS 𝒴
    letI := abelianLisseEtaleModules B S hS 𝒴
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (inverseImageRing
      (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))
    letI := HasDerivedCategory.standard (SheafOfModules.{u}
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (inverseImageRing
      (subsiteTopology B S hS 𝒴.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒴))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒴).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))
    letI := HasDerivedCategory.standard (SheafOfModules.{u}
      (SmallModel.targetRing (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))
    Nonempty ((AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u, u + 1, u} B S hS
        𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        f.hom.hom.toFunctor f.hom.hom.w (etaleTopology B) (etaleTopology_le_topology B)).obj
          ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
              (SmallModel.targetRing (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
                (associatedRingedTopos B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
                  (etaleTopology B) (etaleTopology_le_topology B)).O)) p).obj
            ((derivedModuleLowerShriek B S hS 𝒴).obj ((DerivedCategory.singleFunctor _ 0).obj H))) ≅
      (DerivedCategory.homologyFunctor (SheafOfModules.{u}
              (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
                (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
                  (etaleTopology B) (etaleTopology_le_topology B)).O)) p).obj
        ((derivedModuleLowerShriek B S hS 𝒳).obj ((DerivedCategory.singleFunctor _ 0).obj
          ((lisseEtaleModuleInverseImage f hf).obj H)))) := by
  let := abelianEtaleModules B S hS 𝒳
  let := abelianLisseEtaleModules B S hS 𝒳
  let := abelianEtaleModules B S hS 𝒴
  let := abelianLisseEtaleModules B S hS 𝒴
  let := HasDerivedCategory.standard (SheafOfModules.{u} (inverseImageRing
      (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (inverseImageRing
      (subsiteTopology B S hS 𝒴.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒴))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒴).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
      (SmallModel.targetRing (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴))
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴))
  obtain ⟨e𝒴⟩ := nonempty_uliftHomologyDerivedModuleLowerShriekIso B S hS 𝒴 H p
  obtain ⟨e𝒳⟩ := nonempty_uliftHomologyDerivedModuleLowerShriekIso B S hS 𝒳
    ((lisseEtaleModuleInverseImage f hf).obj H) p
  let F₁ := AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    f.hom.hom.toFunctor f.hom.hom.w (etaleTopology B) (etaleTopology_le_topology B)
  have : PreservesFiniteLimits F₁ :=
    preservesFiniteLimits_modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    f.hom.hom.toFunctor f.hom.hom.w (etaleTopology B) (etaleTopology_le_topology B)
  have : PreservesFiniteColimits F₁ :=
    preservesFiniteColimits_modulePullback.{u, u + 1, u, u, u + 1, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    f.hom.hom.toFunctor f.hom.hom.w (etaleTopology B) (etaleTopology_le_topology B)
  have : F₁.Additive := ⟨fun {_ _ _ _} => rfl⟩
  obtain ⟨eB⟩ := F₁.nonempty_homology_mapDerivedCategory_obj_iso
    ((derivedModuleLowerShriekSucc B S hS 𝒴).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((moduleULift B S hS 𝒴).obj H))) p
  let e07 := (moduleDerivedLowerShriekBaseChangeIso B S hS f hf).app
    ((DerivedCategory.singleFunctor _ 0).obj ((moduleULift B S hS 𝒴).obj H))
  have := isContinuous_subsiteFunctor_topology.{u, w} B S hS f hf
  have := isCocontinuous_subsiteFunctor_topology.{u, w} B S hS f hf
  have hex := SheafOfModules.exactFunctor_pushforward_of_isCocontinuous.{u + 1, u, u + 1, u, u,
    u + 1} (primedSiteFunctor B S hS f hf)
    (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm)
  have : PreservesFiniteLimits (moduleSubsiteInverseImage B S hS f hf) := hex.1
  have : PreservesFiniteColimits (moduleSubsiteInverseImage B S hS f hf) := hex.2
  let eS := ((moduleSubsiteInverseImage B S hS f hf).mapDerivedCategorySingleFunctor 0).app
    ((moduleULift B S hS 𝒴).obj H)
  refine ⟨(ULiftComparison.targetULift _ _).preimageIso ?_⟩
  exact modulePullbackULiftIso f _ ≪≫ F₁.mapIso e𝒴 ≪≫ eB.symm ≪≫
    (DerivedCategory.homologyFunctor _ p).mapIso e07 ≪≫
    (DerivedCategory.homologyFunctor _ p).mapIso
      ((derivedModuleLowerShriekSucc B S hS 𝒳).mapIso
        (eS ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso
          (moduleSubsiteInverseImageULiftIso f hf H))) ≪≫
    e𝒳.symm

end AlgebraicGeometry.Stack.LisseEtale

end
