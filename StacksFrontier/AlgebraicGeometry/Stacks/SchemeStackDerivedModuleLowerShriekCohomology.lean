module

public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackFlatSubsiteQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.ExtensionByZeroUnitAtTerminal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.BiggerSiteModuleCohomology
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalTypesComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.Coherence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackLisseSubsiteQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleDerivedModuleLowerShriek

/-!
# The cohomology of `Lg_!` of a globally presented module over an affine scheme

Let `U` be an affine scheme over `S` and let `g` be the morphism of ringed topoi of
**Stacks 0788** (2) from the flat-fppf site of the algebraic stack `(Sch/U)_{fppf}` to its fppf
site. For a sheaf of modules `H` on the flat-fppf site with a global presentation (Stacks 03DE),
every cohomology sheaf `H^p(Lg_! H)` lies in any weak Serre subcategory of `Mod(𝒪)` containing
the free modules: this is the affine step of **Stacks 07B3** (2). The same holds for the
lisse-étale site, which is the affine step of **Stacks 07B3** (1).

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.isSumOfExtensionByZeroUnits_of_isFree`: on a site with a
  terminal object, a free module is a direct sum of extensions by zero of structure sheaves of
  slices.
* `Stacks.Cohomology.DerivedLowerShriek.isFree_lowerShriekModules_obj`: lower shriek along a final
  functor of sites carries free modules to free modules.
* `AlgebraicGeometry.Stack.FlatFppf.prop_homology_derivedModuleLowerShriek_of_quasiIso_isFree`:
  for an algebraic stack whose flat-fppf site has a terminal object mapping to a terminal object,
  the cohomology of `Lg_! H` lies in a weak Serre class containing the free modules as soon as
  `H` has a free resolution.
* `AlgebraicGeometry.Stack.FlatFppf.prop_homology_derivedModuleLowerShriek_schemeStack`: the
  affine step of Stacks 07B3 (2).
* `AlgebraicGeometry.Stack.LisseEtale.prop_homology_derivedModuleLowerShriek_of_quasiIso_isFree`:
  the same statement for the lisse-étale site.
* `AlgebraicGeometry.Stack.LisseEtale.prop_homology_derivedModuleLowerShriek_schemeStack`: the
  affine step of Stacks 07B3 (1).

## References

* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedLowerShriek

universe w v₁ u₁ v₂ u₂

section Terminal

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : C, (SheafOfModules.pushforward.{w} (F := Over.forget U)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).IsRightAdjoint]

/-- **On a site with a terminal object `T`, a free module is a direct sum of copies of
`j_{T!} O_T`**. -/
theorem isSumOfExtensionByZeroUnits_of_isFree {T : C} (hT : IsTerminal T)
    {M : SheafOfModules.{w} R} (hM : M.IsFree) : IsSumOfExtensionByZeroUnits R M := by
  obtain ⟨I, ι, ⟨hc⟩⟩ := hM
  exact ⟨I, fun _ => T, ⟨Sigma.mapIso (fun _ =>
    Stacks.Sites.ExtensionByZero.extensionByZeroUnitIsoUnitOfTerminal J R T hT) ≪≫
      (colimit.isColimit _).coconePointUniqueUpToIso hc⟩⟩

end Terminal

section Free

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] (O : Sheaf K RingCat.{w})
  [(SheafOfModules.pushforward.{w} (idRingMap J K f O)).IsRightAdjoint]
  [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Lower shriek along a final functor of sites carries free modules to free modules.** -/
theorem isFree_lowerShriekModules_obj [f.Final] {M : SheafOfModules.{w} (inverseImageRing J K f O)}
    (hM : M.IsFree) : ((lowerShriekModules J K f O).obj M).IsFree := by
  obtain ⟨I, ι, ⟨hc⟩⟩ := hM
  exact Stacks.Sheaves.QcohTypeComparison.isFree_of_iso
    ((lowerShriekModules J K f O).mapIso
      (hc.coconePointUniqueUpToIso (colimit.isColimit _)) ≪≫
        SheafOfModules.pullbackObjFreeIso (idRingMap J K f O) I)
    (Stacks.Sheaves.QcohTypeComparison.isFree_free I)

end Free

end Stacks.Cohomology.DerivedLowerShriek

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

open Stacks.Cohomology.DerivedLowerShriek

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat isContinuous_inclusion_topology
  isCocontinuous_inclusion_topology hasSheafify_addCommGrpCat
  wEqualsLocallyBijective_addCommGrpCat hasSheafify_fppf_addCommGrpCat
  wEqualsLocallyBijective_fppf_addCommGrpCat hasSheafify_associatedTopology_ab
  wEqualsLocallyBijective_fppfTopology_addCommGrpCat Stacks.essentiallySmall_over

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If `F → H[0]` is a quasi-isomorphism from a bounded above complex of free modules along which
`Lg_!` is computed degreewise, then every `H^p(Lg_! H)` lies in a weak Serre class containing the
free modules. -/
private theorem prop_homology_totalLeftDerivedLowerShriek_of_quasiIso_isFree
    {C : Type (w + 1)} [Category.{w} C] {D : Type (w + 1)} [Category.{w} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D)
    [f.IsContinuous J K] (O : Sheaf K RingCat.{w}) [f.Final]
    [(SheafOfModules.pushforward.{w} (idRingMap J K f O)).IsRightAdjoint]
    [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasDerivedCategory (SheafOfModules.{w} (inverseImageRing J K f O))]
    [HasDerivedCategory (SheafOfModules.{w} O)]
    [(lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (sourceQuasiIso J K f O)]
    (P : ObjectProperty (SheafOfModules.{w} O)) [P.IsWeakSerreClass]
    (hP : ∀ M : SheafOfModules.{w} O, M.IsFree → P M)
    {H : SheafOfModules.{w} (inverseImageRing J K f O)}
    (F : CochainComplex (SheafOfModules.{w} (inverseImageRing J K f O)) ℤ)
    (hfree : ∀ n, (F.X n).IsFree) (π : F ⟶ (CochainComplex.singleFunctor _ 0).obj H)
    (hπ : QuasiIso π)
    [IsIso ((totalLeftDerivedLowerShriekCounit J K f O).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F))] (p : ℤ) :
    P ((DerivedCategory.homologyFunctor _ p).obj
      ((totalLeftDerivedLowerShriek J K f O).obj ((DerivedCategory.singleFunctor _ 0).obj H))) := by
  let G := ((lowerShriekModules J K f O).mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  have hG : P (G.homology p) := P.prop_homology G p
    (fun n => hP _ (isFree_lowerShriekModules_obj J K f O (hfree n)))
  have : IsIso (DerivedCategory.Q.map π) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := π)).2 hπ
  let e₁ : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F) ≅
      (DerivedCategory.singleFunctor _ 0).obj H :=
    (DerivedCategory.quotientCompQhIso _).app F ≪≫ asIso (DerivedCategory.Q.map π) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app H).symm
  let e₂ : (totalLeftDerivedLowerShriek J K f O).obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F)) ≅
      DerivedCategory.Q.obj G :=
    asIso ((totalLeftDerivedLowerShriekCounit J K f O).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F)) ≪≫
      (DerivedCategory.quotientCompQhIso _).app G
  exact P.prop_of_iso (((DerivedCategory.homologyFunctor _ p).mapIso
    ((totalLeftDerivedLowerShriek J K f O).mapIso e₁.symm ≪≫ e₂) ≪≫
      (DerivedCategory.homologyFunctorFactors _ p).app G).symm) hG


section Derived

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

attribute [local instance] abelianFppfModules abelianFlatFppfModules
  AlgebraicGeometry.Stack.abelianFppfModules abelianFlatFppfModulesSpelling

/-- **The cohomology of `Lg_!` of a module with a free resolution, over a flat-fppf site with a
terminal object.** Let `T` be a terminal object of the flat-fppf site of `𝒳` whose image in `𝒳`
is terminal, let `P` be a weak Serre class of `Mod(𝒪_𝒳)` containing the free modules, and let
`F → H[0]` be a quasi-isomorphism from a bounded above complex of free modules. Then every
`H^p(Lg_! H)` lies in `P`. -/
theorem prop_homology_derivedModuleLowerShriek_of_quasiIso_isFree
    {T : FlatFppf B S hS 𝒳} (hT : IsTerminal T)
    (hT' : IsTerminal ((objectProperty B S hS 𝒳).ι.obj T))
    (P : ObjectProperty (fppfModules B S hS 𝒳)) [P.IsWeakSerreClass]
    (hP : ∀ F : fppfModules B S hS 𝒳, F.IsFree → P F)
    (H : SheafOfModules.{u} (inverseImageRing (topology B S hS 𝒳) (fppfTopology B S hS 𝒳)
      (objectProperty B S hS 𝒳).ι
      (SmallModel.targetRing (fppfTopology B S hS 𝒳) (ambientStructureSheaf B S hS 𝒳))))
    (F : CochainComplex (SheafOfModules.{u} (inverseImageRing (topology B S hS 𝒳)
      (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι
      (SmallModel.targetRing (fppfTopology B S hS 𝒳) (ambientStructureSheaf B S hS 𝒳)))) ℤ)
    (hF : F.IsStrictlyLE 0) (hfree : ∀ n, (F.X n).IsFree)
    (π : F ⟶ (CochainComplex.singleFunctor _ 0).obj H) (hπ : QuasiIso π) (p : ℤ) :
    letI := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    P ((DerivedCategory.homologyFunctor _ p).obj
      ((derivedModuleLowerShriek B S hS 𝒳).obj ((DerivedCategory.singleFunctor _ 0).obj H))) := by
  let := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
  let := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  let := HasDerivedCategory.standard (SheafOfModules.{u} (inverseImageRing (topology B S hS 𝒳)
    (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι
    (SmallModel.targetRing (fppfTopology B S hS 𝒳) (ambientStructureSheaf B S hS 𝒳))))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (SmallModel.targetRing (fppfTopology B S hS 𝒳) (ambientStructureSheaf B S hS 𝒳)))
  have := Functor.final_of_isTerminal_obj _ hT hT'
  have hiso := isIso_derivedModuleLowerShriekComparison_app B S hS 𝒳 F
    (fun n => isSumOfExtensionByZeroUnits_of_isFree.{u} _ hT (hfree n))
  have : ObjectProperty.IsWeakSerreClass (C := SheafOfModules.{u} (SmallModel.targetRing
    (fppfTopology B S hS 𝒳) (ambientStructureSheaf B S hS 𝒳))) P := ‹_›
  exact prop_homology_totalLeftDerivedLowerShriek_of_quasiIso_isFree _
    (fppfTopology B S hS 𝒳) _
    (SmallModel.targetRing (fppfTopology B S hS 𝒳) (ambientStructureSheaf B S hS 𝒳))
    P hP F hfree π hπ p

/-- **The affine step of Stacks 07B3 (2).** Let `U` be an affine scheme and `H` a sheaf of modules
with a global presentation on the flat-fppf site of `(Sch/U)_{fppf}`. Then for every `p` the
sheaf `H^p(Lg_! H)` lies in every weak Serre class `P` of `Mod(𝒪)` containing the free
modules. -/
theorem prop_homology_derivedModuleLowerShriek_schemeStack (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (P : ObjectProperty (fppfModules B S hS (schemeStack.{u, w} B S hS U)))
    [@ObjectProperty.IsWeakSerreClass _ _ (AlgebraicGeometry.Stack.abelianFppfModules B S hS _) P]
    (hP : ∀ F : fppfModules B S hS (schemeStack.{u, w} B S hS U), F.IsFree → P F)
    (H : flatFppfModules B S hS (schemeStack.{u, w} B S hS U))
    (hH : H.IsPresentedByGlobalSections) (p : ℤ) :
    letI := AlgebraicGeometry.Stack.abelianFppfModules B S hS (schemeStack.{u, w} B S hS U)
    letI := abelianFlatFppfModulesSpelling B S hS (schemeStack.{u, w} B S hS U)
    letI := HasDerivedCategory.standard (flatFppfModules B S hS (schemeStack.{u, w} B S hS U))
    letI := HasDerivedCategory.standard (fppfModules B S hS (schemeStack.{u, w} B S hS U))
    P ((DerivedCategory.homologyFunctor _ p).obj
      ((derivedModuleLowerShriek B S hS (schemeStack.{u, w} B S hS U)).obj
        ((DerivedCategory.singleFunctor _ 0).obj H))) := by
  obtain ⟨F, π, hF, hπ, hfree⟩ := exists_quasiIso_isFree_schemeStack.{u, w} B S hS U hU H hH
  exact prop_homology_derivedModuleLowerShriek_of_quasiIso_isFree B S hS _
    (isTerminalFlatObjectSchemeStackId.{u, w} B S hS U) Over.mkIdTerminal P hP H F hF hfree π hπ p

end Derived

end AlgebraicGeometry.Stack.FlatFppf

namespace AlgebraicGeometry.Stack.LisseEtale

universe u w

open Stacks.Cohomology.DerivedLowerShriek

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'
  Stacks.hasSheafCompose_forget₂_commRingCat Stacks.essentiallySmall_over
  preservesCoveringPullbacks_inclusion

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Derived

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

attribute [local instance] abelianEtaleModules abelianLisseEtaleModules

/-- **The cohomology of `Lg_!` of a module with a free resolution, over a lisse-étale site with a
terminal object.** Let `T` be a terminal object of the lisse-étale site of `𝒳` whose image in
`𝒳` is terminal, let `P` be a weak Serre class of `Mod(𝒳_étale, 𝒪_𝒳)` containing the free
modules, and let `F → H[0]` be a quasi-isomorphism from a bounded above complex of free modules.
Then every `H^p(Lg_! H)` lies in `P`. -/
theorem prop_homology_derivedModuleLowerShriek_of_quasiIso_isFree
    {T : (smoothObject.{u, w} B S hS 𝒳).FullSubcategory} (hT : IsTerminal T)
    (hT' : IsTerminal ((smoothObject.{u, w} B S hS 𝒳).ι.obj T))
    (P : ObjectProperty (SheafOfModules.{u}
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))) [P.IsWeakSerreClass]
    (hP : ∀ F, SheafOfModules.IsFree F → P F)
    (H : SheafOfModules.{u} (inverseImageRing (subsiteTopology B S hS 𝒳.val.val.p
      (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))
    (F : CochainComplex (SheafOfModules.{u} (inverseImageRing (subsiteTopology B S hS
      𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))) ℤ)
    (hF : F.IsStrictlyLE 0) (hfree : ∀ n, (F.X n).IsFree)
    (π : F ⟶ (CochainComplex.singleFunctor _ 0).obj H) (hπ : QuasiIso π) (p : ℤ) :
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
    P ((DerivedCategory.homologyFunctor _ p).obj
      ((derivedModuleLowerShriek B S hS 𝒳).obj ((DerivedCategory.singleFunctor _ 0).obj H))) := by
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
  have := Functor.final_of_isTerminal_obj _ hT hT'
  have hiso := isIso_derivedModuleLowerShriekComparison_app B S hS 𝒳 F
    (fun n => isSumOfExtensionByZeroUnits_of_isFree.{u} _ hT (hfree n))
  exact FlatFppf.prop_homology_totalLeftDerivedLowerShriek_of_quasiIso_isFree _
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) _
    (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
        (etaleTopology_le_topology B)).O) P hP F hfree π hπ p

/-- The inclusion of the lisse-étale site of the stack of a scheme is continuous. -/
local instance isContinuous_inclusion_schemeStack (U : BigFppfOver B S hS) :
    (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)).ι.IsContinuous
      (subsiteTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B)
        (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)))
      (associatedTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B)) :=
  isContinuous_inclusion'.{u, w} B S hS _

/-- **The affine step of Stacks 07B3 (1).** Let `U` be an affine scheme and `H` a sheaf of
modules with a global presentation on the lisse-étale site of `(Sch/U)_{fppf}`. Then for every
`p` the sheaf `H^p(Lg_! H)` lies in every weak Serre class `P` of `Mod((Sch/U)_étale, 𝒪)`
containing the free modules. -/
theorem prop_homology_derivedModuleLowerShriek_schemeStack (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (P : ObjectProperty (SheafOfModules.{u}
      (SmallModel.targetRing (associatedTopology B S hS
        (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS (schemeStack.{u, w} B S hS U).val.val.p
          (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))
    [@ObjectProperty.IsWeakSerreClass _ _ (abelianEtaleModules B S hS _) P]
    (hP : ∀ F, SheafOfModules.IsFree F → P F)
    (H : SheafOfModules.{u} (inverseImageRing (subsiteTopology B S hS
      (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)))
      (associatedTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)).ι
      (SmallModel.targetRing (associatedTopology B S hS
        (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS (schemeStack.{u, w} B S hS U).val.val.p
          (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)))
    (hH : H.IsPresentedByGlobalSections) (p : ℤ) :
    letI := abelianEtaleModules B S hS (schemeStack.{u, w} B S hS U)
    letI := abelianLisseEtaleModules B S hS (schemeStack.{u, w} B S hS U)
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (inverseImageRing
        (subsiteTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p
          (etaleTopology B) (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)))
        (associatedTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B))
        (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)).ι
        (SmallModel.targetRing (associatedTopology B S hS
            (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B))
          (associatedRingedTopos B S hS (schemeStack.{u, w} B S hS U).val.val.p
            (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids (etaleTopology B)
            (etaleTopology_le_topology B)).O)))
    letI := HasDerivedCategory.standard (SheafOfModules.{u}
        (SmallModel.targetRing (associatedTopology B S hS
            (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B))
          (associatedRingedTopos B S hS (schemeStack.{u, w} B S hS U).val.val.p
            (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids (etaleTopology B)
            (etaleTopology_le_topology B)).O))
    P ((DerivedCategory.homologyFunctor _ p).obj
      ((derivedModuleLowerShriek B S hS (schemeStack.{u, w} B S hS U)).obj
        ((DerivedCategory.singleFunctor _ 0).obj H))) := by
  obtain ⟨F, π, hF, hπ, hfree⟩ := exists_quasiIso_isFree_schemeStack.{u, w} B S hS U hU H hH
  exact prop_homology_derivedModuleLowerShriek_of_quasiIso_isFree B S hS _
    (isTerminalSmoothObjectSchemeStackId.{u, w} B S hS U) Over.mkIdTerminal P hP H F hF hfree π
    hπ p

end Derived

end AlgebraicGeometry.Stack.LisseEtale

end
