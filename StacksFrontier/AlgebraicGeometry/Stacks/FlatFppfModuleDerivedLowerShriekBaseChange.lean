module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ULiftDerivedLowerShriekComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedModuleLowerShriekLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfModuleDerivedBaseChange

/-!
# Stacks 07AV, second identity, on cohomology sheaves at the universe of the rings: flat-fppf sites

Let `f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic stacks and `f'` its restriction to the
flat-fppf sites. The second identity of Stacks 07AV, `L(g')_! ∘ (f')^{-1} = f^{-1} ∘ Lg_!`, is
proved for sheaves of modules at the module universe `u + 1` of the fppf sites
(`AlgebraicGeometry.Stack.FlatFppf.moduleDerivedLowerShriekBaseChangeIso`). This file derives its
consequence at the module universe `u` of the rings, for the derived lower shriek
`AlgebraicGeometry.Stack.FlatFppf.derivedModuleLowerShriek` of Stacks 07AS (4) at that universe:
for a sheaf of modules `H` on the flat-fppf site of `𝒴`,

`f^{-1} H^p(Lg_! H) ≅ H^p(L(g')_! (f')^{-1} H)`.

The universe lift `Λ` of the sections is fully faithful, commutes with `f^{-1}`, `(f')^{-1}` on
the nose and with the two derived lower shrieks on cohomology sheaves
(`ULiftComparison.nonempty_homologyDerivedLowerShriekULiftIso` in the namespace
`Stacks.Cohomology.DerivedLowerShriek`).

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.moduleULift`: `Λ : Mod_u(𝒪_{𝒳_{flat,fppf}}) ⥤
  Mod_{u+1}(𝒪_{𝒳_{flat,fppf}})`.
* `AlgebraicGeometry.Stack.FlatFppf.flatFppfModuleInverseImage`: `(f')^{-1}` at the universe of
  the rings.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.nonempty_uliftHomologyDerivedModuleLowerShriekIso`:
  `Λ H^p(Lg_! H) ≅ H^p(Lg_!(Λ H))`.
* `AlgebraicGeometry.Stack.FlatFppf.nonempty_modulePullback_homology_derivedModuleLowerShriek_iso`:
  `f^{-1} H^p(Lg_! H) ≅ H^p(L(g')_! (f')^{-1} H)`.

## References

* [Stacks Project, Tag 07AV](https://stacks.math.columbia.edu/tag/07AV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedLowerShriek

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  isContinuous_inclusion_topology isCocontinuous_inclusion_topology Stacks.essentiallySmall_over
  preservesCoveringPullbacks_inclusion_topology
  GrothendieckTopology.hasSheafify_addCommGrpCat
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section ULift

variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- The raising `Λ` of the universe of the sections of sheaves of modules on the flat-fppf site,
from the universe `u` of 07BA's `Lg_!` to the universe `u + 1` of Stacks 07AV. -/
abbrev moduleULift :
    flatFppfModules B S hS 𝒳 ⥤ SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳) :=
  ULiftComparison.sourceULift (topology B S hS 𝒳) (fppfTopology B S hS 𝒳)
    (objectProperty B S hS 𝒳).ι
    (SmallModel.targetRing (fppfTopology B S hS 𝒳) (ambientStructureSheaf B S hS 𝒳))

/-- **`Λ H^p(Lg_! H) ≅ H^p(Lg_!(Λ H))` for the flat-fppf site.** For a sheaf of modules `H` on the
flat-fppf site of `𝒳` with sections in `Type u` and every `p`, the universe lift of the `p`-th
cohomology sheaf of 07BA's `Lg_!(H)` (Stacks 07AS (4), module universe `u`) is the `p`-th
cohomology sheaf of `Lg_!(Λ H)` at the module universe `u + 1` of Stacks 07AV, at the standard
models of the derived categories. -/
theorem nonempty_uliftHomologyDerivedModuleLowerShriekIso (H : flatFppfModules B S hS 𝒳) (p : ℤ) :
    letI := (SheafOfModules.instAbelian _ : Abelian (fppfModules B S hS 𝒳))
    letI := abelianFlatFppfModulesSpelling B S hS 𝒳
    letI := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    Nonempty ((ULiftComparison.targetULift _ _).obj
        ((DerivedCategory.homologyFunctor (fppfModules B S hS 𝒳) p).obj
          ((derivedModuleLowerShriek B S hS 𝒳).obj ((DerivedCategory.singleFunctor _ 0).obj H))) ≅
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) p).obj
        ((derivedModuleLowerShriekSucc B S hS 𝒳).obj
          ((DerivedCategory.singleFunctor _ 0).obj ((moduleULift B S hS 𝒳).obj H)))) := by
  have := hasSheafify_addCommGrpCat B S hS 𝒳
  have := wEqualsLocallyBijective_addCommGrpCat B S hS 𝒳
  have : HasSheafify (fppfTopology B S hS 𝒳) AddCommGrpCat.{u} :=
    hasSheafify_associatedTopology_ab.{u, w, u} B S hS 𝒳
  have := wEqualsLocallyBijective_fppfTopology_addCommGrpCat B S hS 𝒳
  have : EssentiallySmall.{u + 1} 𝒳.val.val.obj :=
    essentiallySmall_obj_coefficient.{u, w, u + 1} B S hS 𝒳
  have : EssentiallySmall.{u + 1} (FlatFppf B S hS 𝒳) :=
    essentiallySmall_flatFppf.{u, w, u + 1} B S hS 𝒳
  have : HasSheafify (topology B S hS 𝒳) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have : (topology B S hS 𝒳).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  have : HasSheafify (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have : (fppfTopology B S hS 𝒳).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  let := (SheafOfModules.instAbelian _ : Abelian (fppfModules B S hS 𝒳))
  let := abelianFlatFppfModulesSpelling B S hS 𝒳
  let := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
  let := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  let := HasDerivedCategory.standard (SheafOfModules.{u} (inverseImageRing
      (topology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι
      (Stacks.SheafOfModules.Tensor.ringSheaf (ambientStructureSheaf B S hS 𝒳))))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ambientStructureSheaf B S hS 𝒳)))
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1} (inverseImageRing
      (topology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι
      (Stacks.SheafOfModules.Tensor.ringSheaf (ambientStructureSheaf B S hS 𝒳))))
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ambientStructureSheaf B S hS 𝒳)))
  exact ULiftComparison.nonempty_homologyDerivedLowerShriekULiftIso
    (topology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι
    (ambientStructureSheaf B S hS 𝒳) H p

end ULift


section BaseChange

variable {B S hS} {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsFlat B S hS f)

/-- `(f')^{-1}` on sheaves of modules on the flat-fppf sites, at the universe of the rings:
restriction along `f'`, read over the structure sheaf of the flat-fppf site of `𝒳` through
`AlgebraicGeometry.Stack.FlatFppf.subsiteRingStructureSheaf_inverseImageRing` (Stacks 06TW). -/
abbrev flatFppfModuleInverseImage : flatFppfModules B S hS 𝒴 ⥤ flatFppfModules B S hS 𝒳 :=
  haveI := isContinuous_subsiteFunctor_topology B S hS f hf
  SheafOfModules.pushforward.{u} (F := primedSiteFunctor B S hS f hf)
    (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm)

/-- `(f')^{-1}` commutes with raising the universe of the sections, on the nose. -/
def moduleSubsiteInverseImageULiftIso (M : flatFppfModules B S hS 𝒴) :
    (moduleSubsiteInverseImage B S hS f hf).obj ((moduleULift B S hS 𝒴).obj M) ≅
      (moduleULift B S hS 𝒳).obj ((flatFppfModuleInverseImage f hf).obj M) :=
  Iso.refl _

/-- `f^{-1}` commutes with raising the universe of the sections, on the nose. -/
def modulePullbackULiftIso (M : fppfModules B S hS 𝒴) :
    (ULiftComparison.targetULift (fppfTopology B S hS 𝒳)
        (SmallModel.targetRing (fppfTopology B S hS 𝒳) (ambientStructureSheaf B S hS 𝒳))).obj
        ((AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p
          𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
          f.hom.hom.w B.topology le_rfl).obj M) ≅
      (AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS 𝒳.val.val.p
          𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
          f.hom.hom.w B.topology le_rfl).obj
        ((ULiftComparison.targetULift (fppfTopology B S hS 𝒴)
          (SmallModel.targetRing (fppfTopology B S hS 𝒴)
            (ambientStructureSheaf B S hS 𝒴))).obj M) :=
  Iso.refl _

/-- **Stacks 07AV, second identity, on cohomology sheaves at the universe of the rings, for the
flat-fppf sites.** For a flat 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, a sheaf of modules `H`
with sections in `Type u` on the flat-fppf site of `𝒴` and every `p`,
`f^{-1} H^p(Lg_! H) ≅ H^p(L(g')_! (f')^{-1} H)`, for 07BA's derived lower shrieks of Stacks
07AS (4) at the universe of the rings, at the standard models of the derived categories. -/
theorem nonempty_modulePullback_homology_derivedModuleLowerShriek_iso
    (H : flatFppfModules B S hS 𝒴) (p : ℤ) :
    letI := (SheafOfModules.instAbelian _ : Abelian (fppfModules B S hS 𝒳))
    letI := abelianFlatFppfModulesSpelling B S hS 𝒳
    letI := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    letI := (SheafOfModules.instAbelian _ : Abelian (fppfModules B S hS 𝒴))
    letI := abelianFlatFppfModulesSpelling B S hS 𝒴
    letI := HasDerivedCategory.standard (flatFppfModules B S hS 𝒴)
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒴)
    Nonempty ((AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u, u + 1, u} B S hS
        𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        f.hom.hom.toFunctor f.hom.hom.w B.topology le_rfl).obj
          ((DerivedCategory.homologyFunctor (fppfModules B S hS 𝒴) p).obj
            ((derivedModuleLowerShriek B S hS 𝒴).obj ((DerivedCategory.singleFunctor _ 0).obj H))) ≅
      (DerivedCategory.homologyFunctor (fppfModules B S hS 𝒳) p).obj
        ((derivedModuleLowerShriek B S hS 𝒳).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((flatFppfModuleInverseImage f hf).obj H)))) := by
  let := (SheafOfModules.instAbelian _ : Abelian (fppfModules B S hS 𝒳))
  let := abelianFlatFppfModulesSpelling B S hS 𝒳
  let := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
  let := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  let := (SheafOfModules.instAbelian _ : Abelian (fppfModules B S hS 𝒴))
  let := abelianFlatFppfModulesSpelling B S hS 𝒴
  let := HasDerivedCategory.standard (flatFppfModules B S hS 𝒴)
  let := HasDerivedCategory.standard (fppfModules B S hS 𝒴)
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴))
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴))
  obtain ⟨e𝒴⟩ := nonempty_uliftHomologyDerivedModuleLowerShriekIso B S hS 𝒴 H p
  obtain ⟨e𝒳⟩ := nonempty_uliftHomologyDerivedModuleLowerShriekIso B S hS 𝒳
    ((flatFppfModuleInverseImage f hf).obj H) p
  let F₁ := AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    f.hom.hom.toFunctor f.hom.hom.w B.topology le_rfl
  have : PreservesFiniteLimits F₁ :=
    preservesFiniteLimits_modulePullback.{u, u + 1, u, u + 1, u + 1, u}
    B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    f.hom.hom.toFunctor f.hom.hom.w B.topology le_rfl
  have : PreservesFiniteColimits F₁ :=
    preservesFiniteColimits_modulePullback.{u, u + 1, u, u, u + 1, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    f.hom.hom.toFunctor f.hom.hom.w B.topology le_rfl
  have : F₁.Additive := ⟨fun {_ _ _ _} => rfl⟩
  obtain ⟨eB⟩ := F₁.nonempty_homology_mapDerivedCategory_obj_iso
    ((derivedModuleLowerShriekSucc B S hS 𝒴).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((moduleULift B S hS 𝒴).obj H))) p
  let e07 := (moduleDerivedLowerShriekBaseChangeIso B S hS f hf).app
    ((DerivedCategory.singleFunctor _ 0).obj ((moduleULift B S hS 𝒴).obj H))
  have := isContinuous_subsiteFunctor_topology B S hS f hf
  have := isCocontinuous_subsiteFunctor_topology B S hS f hf
  have hex :=
    SheafOfModules.exactFunctor_pushforward_of_isCocontinuous.{u + 1, u, u + 1, u, u, u + 1}
    (primedSiteFunctor B S hS f hf)
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

end BaseChange

end AlgebraicGeometry.Stack.FlatFppf

end
