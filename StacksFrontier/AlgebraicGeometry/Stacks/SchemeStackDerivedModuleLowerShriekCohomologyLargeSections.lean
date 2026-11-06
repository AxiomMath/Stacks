module

public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackDerivedModuleLowerShriekCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedModuleLowerShriekLargeSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport

/-!
# The cohomology of `Lg_!` of a module with a free resolution, at module universe `u + 1`

The universe-`u + 1` twin of
`StacksFrontier/AlgebraicGeometry/Stacks/SchemeStackDerivedModuleLowerShriekCohomology.lean`, the
affine step of the proof of **Stacks 07B3** (2) for the modules of Stacks 07AV, 07BC and 07BE,
whose sections lie in `Type (u + 1)`, one universe above the structure sheaf.

The derived lower shriek at that universe
(`AlgebraicGeometry.Stack.FlatFppf.derivedModuleLowerShriekSucc`) is formed over the structure
sheaf raised to `Type (u + 1)`, through the ring transport
`Stacks.Cohomology.DerivedLowerShriek.ULift.sourceModulesEquivalence`. Free modules,
presentations and free resolutions are single-universe notions, so they are taken over the raised
rings: a module over an affine scheme which, read over the raised rings, has a presentation by
global sections has a resolution whose terms become free over the raised rings (the source's
`O ⊗_A F_• ⟶ H`); `Lg_!` is computed termwise on it, and termwise `g_!` carries such a term to a
module which, read back over the original rings, is a direct sum of copies of the universe lift of
the structure sheaf. So every `H^p(Lg_! H)` lies in any weak Serre class containing those direct
sums.

## Main results

In the namespace `Stacks.Cohomology.DerivedLowerShriek.ULift`:

* `targetModulesEquivalenceInverseUnitIso`, `sourceModulesEquivalenceFunctorUnitIso`: the ring
  transport and the universe lift of the structure sheaf.
* `exists_isColimit_cofan_uliftForPresentation_unit_of_isFree`: the read-back of a free module
  over the raised rings is a direct sum of copies of the universe lift of the structure sheaf.

In the namespace `AlgebraicGeometry.Stack.FlatFppf`:

* `prop_homology_derivedModuleLowerShriekSucc_of_quasiIso`: the cohomology of `Lg_! H` over a
  flat-fppf site with a terminal object.
* `exists_quasiIso_isFree_schemeStack_succ`: the free resolution over an affine scheme.

## References

* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

-- the abelian structure of the library on sheaves of modules whose sections contain the site
-- would be met first by instance search here, with a universe constraint it cannot solve
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace Stacks.Cohomology.DerivedLowerShriek.ULift

universe w r v₁ u₁ v₂ u₂

variable {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D) (O : Sheaf K CommRingCat.{r})
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max r w} RingCat.{max r w})]

/-- **The structure sheaf over the raised rings, read back over the original rings, is the
universe lift of the structure sheaf**: the identity on sections `ULift O(V)`. -/
def targetModulesEquivalenceInverseUnitIso :
    (targetModulesEquivalence.{w} K O).inverse.obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (liftedStructureSheaf.{w} K O))) ≅
      SheafOfModules.uliftForPresentation.{u₂, v₂, r, r, w}
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    { hom := PresheafOfModules.homMk (𝟙 ((SheafOfModules.forget _).obj
          ((targetModulesEquivalence.{w} K O).inverse.obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
              (liftedStructureSheaf.{w} K O))))).presheaf)
        (fun X r m => ULift.ext_iff.2 <| congrArg (· * m.down)
          (((targetRingTransport.{w} K O).iso_symm_iso X r).trans
            (ConcreteCategory.congr_hom
              ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.map_id X) r)))
      inv := PresheafOfModules.homMk (𝟙 ((SheafOfModules.forget _).obj
          (SheafOfModules.uliftForPresentation.{u₂, v₂, r, r, w}
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)))).presheaf)
        (fun X r m => by
          apply ULift.ext
          change @HMul.hMul (O.obj.obj X) (O.obj.obj X) (O.obj.obj X) _ r m.down =
            @HMul.hMul (O.obj.obj X) (O.obj.obj X) (O.obj.obj X) _ _ m.down
          congr 1
          exact (((targetRingTransport.{w} K O).iso_symm_iso X r).trans
            (ConcreteCategory.congr_hom
              ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.map_id X) r)).symm)
      hom_inv_id := by ext X x; rfl
      inv_hom_id := by ext X x; rfl }

omit [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max r w} RingCat.{max r w})] in
/-- **The read-back of a free module over the raised rings is a direct sum of copies of the
universe lift of the structure sheaf.** -/
theorem exists_isColimit_cofan_uliftForPresentation_unit_of_isFree
    {X : SheafOfModules.{max r w} (Stacks.SheafOfModules.Tensor.ringSheaf
      (liftedStructureSheaf.{w} K O))} (hX : X.IsFree) :
    ∃ (I : Type (max r w))
      (ι : I → (SheafOfModules.uliftForPresentation.{u₂, v₂, r, r, w}
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⟶
          (targetModulesEquivalence.{w} K O).inverse.obj X)),
      Nonempty (IsColimit (Cofan.mk _ ι)) := by
  obtain ⟨I, ι, ⟨hc⟩⟩ := hX
  let G := (targetModulesEquivalence.{w} K O).inverse
  have : PreservesColimitsOfSize.{max r w, max r w} G :=
    (targetModulesEquivalence.{w} K O).symm.toAdjunction.leftAdjoint_preservesColimits
  exact ⟨I, _, ⟨Stacks.SheafOfModules.GlobalPresentationTransport.isColimitCofanPrecompose
    (targetModulesEquivalenceInverseUnitIso.{w} K O).symm _
    ((Cofan.isColimitMapCoconeEquiv G _ (Cofan.mk X ι)).toFun (isColimitOfPreserves G hc))⟩⟩

section Source

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (f : C ⥤ D)
  [f.IsContinuous J K] [f.IsCocontinuous J K]

/-- **The universe lift of the structure sheaf of the source, read over the raised rings, is the
structure sheaf over the raised rings**: the identity on sections `ULift O(f V)`. -/
def sourceModulesEquivalenceFunctorUnitIso :
    (sourceModulesEquivalence.{w} J K f O).functor.obj
        (SheafOfModules.uliftForPresentation.{u₁, v₁, r, r, w}
          (SheafOfModules.unit
            (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)))) ≅
      SheafOfModules.unit (inverseImageRing J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O))) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    { hom := PresheafOfModules.homMk (𝟙 ((SheafOfModules.forget _).obj
          ((sourceModulesEquivalence.{w} J K f O).functor.obj
            (SheafOfModules.uliftForPresentation.{u₁, v₁, r, r, w}
              (SheafOfModules.unit (inverseImageRing J K f
                (Stacks.SheafOfModules.Tensor.ringSheaf O)))))).presheaf)
        (fun _ _ _ => rfl)
      inv := PresheafOfModules.homMk (𝟙 ((SheafOfModules.forget _).obj
          (SheafOfModules.unit (inverseImageRing J K f
            (Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf.{w} K O))))).presheaf)
        (fun _ _ _ => rfl)
      hom_inv_id := by ext X; rfl
      inv_hom_id := by ext X; rfl }

end Source

end Stacks.Cohomology.DerivedLowerShriek.ULift

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w t t'

open Stacks.Cohomology.DerivedLowerShriek

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology
  Stacks.hasSheafCompose_forget₂_commRingCat preservesCoveringPullbacks_inclusion_topology
  essentiallySmall_obj_largeSections essentiallySmall_flatFppf_largeSections
  hasSheafify_topology_largeSections wEqualsLocallyBijective_topology_largeSections
  hasSheafify_fppfTopology_largeSections wEqualsLocallyBijective_fppfTopology_largeSections
  hasPointwiseRightKanExtension_inclusion_ringCat_largeSections
  hasPointwiseRightKanExtension_inclusion_addCommGrpCat_largeSections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

variable [HasDerivedCategory.{t} (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))]
  [HasDerivedCategory.{t'} (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))]

/-- **The cohomology of `Lg_!` at module universe `u + 1` of a module with a free resolution, over
a flat-fppf site with a terminal object.** Let `T` be a terminal object of the flat-fppf site of
`𝒳` whose image in `𝒳` is terminal, let `P` be a weak Serre class of modules with sections in
`Type (u + 1)` containing the direct sums of copies of the structure sheaf (lifted to that
universe), and let `F → H[0]` be a quasi-isomorphism from a complex bounded above by `0` whose
terms become free over the raised structure sheaf. Then every `H^p(Lg_! H)` lies in `P`. -/
theorem prop_homology_derivedModuleLowerShriekSucc_of_quasiIso
    {T : FlatFppf B S hS 𝒳} (hT : IsTerminal T)
    (hT' : IsTerminal ((objectProperty B S hS 𝒳).ι.obj T))
    (P : ObjectProperty (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    [P.IsWeakSerreClass]
    (hP : ∀ (I : Type (u + 1)) (F : SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
      (ι : I → (SheafOfModules.uliftForPresentation.{_, _, u, u, u + 1}
        (SheafOfModules.unit (ambientRingStructureSheaf B S hS 𝒳)) ⟶ F)),
      Nonempty (IsColimit (Cofan.mk F ι)) → P F)
    (H : SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
    (F : CochainComplex (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) ℤ)
    (hF : F.IsStrictlyLE 0)
    (hfree : ∀ n, ((ULift.sourceModulesEquivalence.{u + 1} (topology B S hS 𝒳)
      (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι
      (ambientStructureSheaf B S hS 𝒳)).functor.obj (F.X n)).IsFree)
    (π : F ⟶ (CochainComplex.singleFunctor _ 0).obj H) (hπ : QuasiIso π) (p : ℤ) :
    P ((DerivedCategory.homologyFunctor _ p).obj
      ((derivedModuleLowerShriekSucc B S hS 𝒳).obj
        ((DerivedCategory.singleFunctor _ 0).obj H))) := by
  have := Functor.final_of_isTerminal_obj _ hT hT'
  let G := ((Stacks.SheafOfModules.lowerShriek.{u + 1} (topology B S hS 𝒳)
    (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι
    (ambientRingStructureSheaf B S hS 𝒳)).mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  have hG : P (G.homology p) := P.prop_homology G p (fun n => by
    have hfree' := isFree_lowerShriekModules_obj (topology B S hS 𝒳) (fppfTopology B S hS 𝒳)
      (objectProperty B S hS 𝒳).ι
      (Stacks.SheafOfModules.Tensor.ringSheaf (ULift.liftedStructureSheaf.{u + 1}
        (fppfTopology B S hS 𝒳) (ambientStructureSheaf B S hS 𝒳))) (hfree n)
    obtain ⟨I, ι, hc⟩ := ULift.exists_isColimit_cofan_uliftForPresentation_unit_of_isFree.{u + 1}
      (fppfTopology B S hS 𝒳) (ambientStructureSheaf B S hS 𝒳) hfree'
    exact P.prop_of_iso ((ULift.lowerShriekCompIso.{u + 1} (topology B S hS 𝒳)
      (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι
      (ambientStructureSheaf B S hS 𝒳)).app (F.X n)) (hP I _ ι hc))
  let e₁ : DerivedCategory.Q.obj F ≅ (DerivedCategory.singleFunctor _ 0).obj H :=
    asIso (DerivedCategory.Q.map π) ≪≫ ((DerivedCategory.singleFunctorIsoCompQ _ 0).app H).symm
  let e₃ : (DerivedCategory.homologyFunctor _ p).obj
      ((derivedModuleLowerShriekSucc B S hS 𝒳).obj ((DerivedCategory.singleFunctor _ 0).obj H)) ≅
      G.homology p :=
    (DerivedCategory.homologyFunctor _ p).mapIso
      ((derivedModuleLowerShriekSucc B S hS 𝒳).mapIso e₁.symm ≪≫
        derivedModuleLowerShriekSuccObjQIso B S hS 𝒳 F hF
          (fun n => isSumOfExtensionByZeroUnits_of_isFree.{u + 1} _ hT (hfree n))) ≪≫
      (DerivedCategory.homologyFunctorFactors _ p).app G
  exact P.prop_of_iso e₃.symm hG

/-- The ring transport of `Stacks.Cohomology.DerivedLowerShriek.ULift` for the flat-fppf site of
an algebraic stack: modules with sections in `Type (u + 1)` over the structure sheaf are modules
over the structure sheaf raised to `Type (u + 1)`. -/
abbrev sourceModulesEquivalenceSucc :=
  ULift.sourceModulesEquivalence.{u + 1} (topology B S hS 𝒳) (fppfTopology B S hS 𝒳)
    (objectProperty B S hS 𝒳).ι (ambientStructureSheaf B S hS 𝒳)

/-- **A globally presented module over an affine scheme has a free resolution at module universe
`u + 1`.** For `U` affine and `H` a module on the flat-fppf site of `(Sch/U)_{fppf}` with sections
in `Type (u + 1)` which, read over the raised structure sheaf, has a global presentation, there
are a complex `F` bounded above by `0` whose terms are free over the raised structure sheaf, and a
quasi-isomorphism `F ⟶ H[0]`: the free resolution `O ⊗_A F_• ⟶ H` of the source, formed over the
raised structure sheaf
(`Stacks.TerminalFreeResolution.exists_quasiIso_isFree_of_isPresentedByGlobalSections`)
and read back. -/
theorem exists_quasiIso_isFree_schemeStack_succ (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (H : SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS (schemeStack.{u, w} B S hS U)))
    (hH : ((sourceModulesEquivalenceSucc B S hS (schemeStack.{u, w} B S hS U)).functor.obj
      H).IsPresentedByGlobalSections) :
    ∃ (F : CochainComplex (SheafOfModules.{u + 1}
        (subsiteRingStructureSheaf B S hS (schemeStack.{u, w} B S hS U))) ℤ)
      (π : F ⟶ (CochainComplex.singleFunctor _ 0).obj H),
      F.IsStrictlyLE 0 ∧ QuasiIso π ∧
        ∀ n, ((sourceModulesEquivalenceSucc B S hS (schemeStack.{u, w} B S hS U)).functor.obj
          (F.X n)).IsFree := by
  have := isContinuous_inclusion_topology B S hS (schemeStack.{u, w} B S hS U)
  have := isCocontinuous_inclusion_topology B S hS (schemeStack.{u, w} B S hS U)
  have := hasSheafify_topology_largeSections B S hS (schemeStack.{u, w} B S hS U)
  have := wEqualsLocallyBijective_topology_largeSections B S hS (schemeStack.{u, w} B S hS U)
  have := hasSheafify_fppfTopology_largeSections B S hS (schemeStack.{u, w} B S hS U)
  have := wEqualsLocallyBijective_fppfTopology_largeSections B S hS
    (schemeStack.{u, w} B S hS U)
  let e := sourceModulesEquivalenceSucc B S hS (schemeStack.{u, w} B S hS U)
  obtain ⟨F₁, π₁, hF₁, hπ₁, hfree₁⟩ : ∃ (F : CochainComplex (SheafOfModules.{u + 1}
      (inverseImageRing (topology B S hS (schemeStack.{u, w} B S hS U))
        (fppfTopology B S hS (schemeStack.{u, w} B S hS U))
        (objectProperty B S hS (schemeStack.{u, w} B S hS U)).ι
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (ULift.liftedStructureSheaf.{u + 1} (fppfTopology B S hS (schemeStack.{u, w} B S hS U))
            (ambientStructureSheaf B S hS (schemeStack.{u, w} B S hS U)))))) ℤ)
      (π : F ⟶ (CochainComplex.singleFunctor _ 0).obj (e.functor.obj H)),
      F.IsStrictlyLE 0 ∧ QuasiIso π ∧ ∀ n, (F.X n).IsFree :=
    Stacks.TerminalFreeResolution.exists_quasiIso_isFree_of_isPresentedByGlobalSections
      (ULift.liftedStructureSheaf.{u + 1} (topology B S hS (schemeStack.{u, w} B S hS U))
        (structureSheaf B S hS (schemeStack.{u, w} B S hS U)))
      (isTerminalFlatObjectSchemeStackId.{u, w} B S hS U)
      (fun Z => IsAffine ((BigFppfOver.toScheme B S hS).obj Z.obj.left))
      (generate_isAffine_mem_topology_schemeStack B S hS U)
      (fun Z hZ => RingHom.Flat.comp (RingHom.Flat.comp
        (RingHom.Flat.of_bijective ULift.ringEquiv.bijective)
        (flat_structureSheaf_map_schemeStack B S hS U hU Z hZ))
        (RingHom.Flat.of_bijective ULift.ringEquiv.symm.bijective))
      (isQuasiCompactObject_schemeStack_id B S hS U (by have := hU; infer_instance))
      (e.functor.obj H) hH
  refine ⟨(e.inverse.mapHomologicalComplex _).obj F₁,
    (e.inverse.mapHomologicalComplex _).map π₁ ≫
      (HomologicalComplex.singleMapHomologicalComplex e.inverse (ComplexShape.up ℤ) 0).hom.app _ ≫
      (CochainComplex.singleFunctor _ 0).map (e.unitIso.inv.app H),
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff F₁ e.inverse 0).2 hF₁, ?_,
    fun n => Stacks.Sheaves.QcohTypeComparison.isFree_of_iso (e.counitIso.app (F₁.X n))
      (hfree₁ n)⟩
  have h₁ : QuasiIso ((e.inverse.mapHomologicalComplex _).map π₁) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology π₁ e.inverse
  have h₂ : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex e.inverse
      (ComplexShape.up ℤ) 0).hom.app (e.functor.obj H)) := inferInstance
  have : IsIso (e.unitIso.inv.app H) := (e.unitIso.app H).isIso_inv
  have := Functor.map_isIso (CochainComplex.singleFunctor _ 0) (e.unitIso.inv.app H)
  have h₃ : QuasiIso ((CochainComplex.singleFunctor _ 0).map (e.unitIso.inv.app H)) :=
    quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := h₁) (hφ' := quasiIso_comp _ _ (hφ := h₂) (hφ' := h₃))

end AlgebraicGeometry.Stack.FlatFppf
