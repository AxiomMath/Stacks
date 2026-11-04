module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ULiftLowerShriekComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.EssentiallySmallModuleDerivedLowerShriek
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedAboveResolution

/-!
# The derived lower shriek of modules commutes with raising the universe of the sections

Let `f : C ⥤ D` be a continuous and cocontinuous functor of essentially small sites whose
morphisms lie in the universe `r` of a sheaf of commutative rings `O_D`, with the covering-pullback
condition of Stacks 00WV, and `O_C = g^{-1} O_D`. The derived lower shriek
`Lg_! : D(O_C) ⥤ D(O_D)` exists for modules with sections in `Type r`
(`Stacks.Cohomology.DerivedLowerShriek.totalLeftDerivedLowerShriek`) and for modules with
sections in `Type (max u₁ r)` (`Stacks.Cohomology.DerivedLowerShriek.ULift.derivedLowerShriek`).
For a sheaf of `O_C`-modules `H` with sections in `Type r` and every `p`, this file identifies

`Λ H^p(Lg_! H) ≅ H^p(Lg_! (Λ H))`,

`Λ` being the universe lift of the sections. Both sides are computed on a resolution `P → H` by
direct sums of the `j_{U!} O_U` (Stacks 0794), and `g_!(Λ P) ≅ Λ(g_! P)` termwise by
`Stacks.Cohomology.DerivedLowerShriek.ULiftComparison.isIso_lowerShriekULiftComparison_app`.

## Main results

* `ULiftComparison.exists_quasiIso_isSumOfExtensionByZeroUnits`: every sheaf of modules on an
  essentially small site has a resolution, bounded above by `0`, by direct sums of the
  `j_{U!} O_U`.
* `Stacks.Cohomology.DerivedLowerShriek.ULiftComparison.homologyDerivedLowerShriekULiftIso`:
  `Λ H^p(Lg_! H) ≅ H^p(Lg_! (Λ H))`.

## References

* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

universe r u₁ t₁ t₂ t₃ t₄

namespace Stacks.Cohomology.DerivedLowerShriek.ULiftComparison

-- the abelian structure of the library on sheaves of modules whose sections contain the site
-- would be met first by instance search here, with a universe constraint it cannot solve
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

section Resolution

variable {C : Type u₁} [Category.{r} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ U : C, (SheafOfModules.pushforward.{r} (F := Over.forget U)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).IsRightAdjoint] [EssentiallySmall.{r} C]

/-- The direct sums of the `j_{U!} O_U` are closed under isomorphisms. -/
lemma isSumOfExtensionByZeroUnits_of_isIso {M N : SheafOfModules.{r} R} (e : M ⟶ N) [IsIso e]
    (hM : IsSumOfExtensionByZeroUnits R M) : IsSumOfExtensionByZeroUnits R N := by
  obtain ⟨ι, U, ⟨φ⟩⟩ := hM
  exact ⟨ι, U, ⟨φ ≪≫ asIso e⟩⟩

/-- **Every sheaf of modules on an essentially small site has a resolution, bounded above by `0`,
by direct sums of the `j_{U!} O_U`.** -/
theorem exists_quasiIso_isSumOfExtensionByZeroUnits (M : SheafOfModules.{r} R) :
    ∃ (P : CochainComplex (SheafOfModules.{r} R) ℤ) (_ : P.IsStrictlyLE 0)
      (π : P ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) (_ : QuasiIso π),
        ∀ n, IsSumOfExtensionByZeroUnits R (P.X n) := by
  have hzero : IsSumOfExtensionByZeroUnits R (0 : SheafOfModules.{r} R) := by
    obtain ⟨Z, hZ, hZP⟩ := (IsSumOfExtensionByZeroUnits R).exists_prop_of_containsZero
    exact isSumOfExtensionByZeroUnits_of_isIso R (hZ.isoZero.hom) hZP
  obtain ⟨P, hP, π, hπ, hPG⟩ :=
    Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis
      (⊤ : ObjectProperty (SheafOfModules.{r} R)) (IsSumOfExtensionByZeroUnits R)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)
      (fun V W g _ _ => by
        obtain ⟨N, hN, p, hp⟩ := exists_epi_isSumOfExtensionByZeroUnits_of_essentiallySmall R V
        exact ⟨N, p, hN, trivial, epi_comp p g⟩)
      hzero (fun _ _ hC hE => isSumOfExtensionByZeroUnits_biprod R hC hE)
      (fun _ _ e _ hV => isSumOfExtensionByZeroUnits_of_isIso R e hV) 0 (fun _ => trivial)
  exact ⟨P, hP, π, hπ, hPG⟩

end Resolution

section ChangeOfTopology

universe v w

variable {C : Type*} [Category C] {D : Type*} [Category D] {J₁ J₂ : GrothendieckTopology C}
  (K : GrothendieckTopology D) (f : C ⥤ D) [f.IsContinuous J₁ K] [f.IsContinuous J₂ K]
  (O : Sheaf K RingCat.{w})

/-- Sheaves of `g^{-1} O_D`-modules for two equal topologies on `C`: the identity on underlying
presheaves of modules. -/
def changeTopology (h : J₁ = J₂) :
    SheafOfModules.{v} (inverseImageRing J₁ K f O) ⥤ SheafOfModules.{v} (inverseImageRing J₂ K f O)
    where
  obj M := ⟨M.val, by subst h; exact M.isSheaf⟩
  map φ := ⟨φ.val⟩

end ChangeOfTopology

section Comparison

variable {C : Type u₁} [Category.{r} C] {D : Type u₁} [Category.{r} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D)
  [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K CommRingCat.{r})
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max r u₁} RingCat.{max r u₁})]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  [EssentiallySmall.{max r u₁} C] [EssentiallySmall.{max r u₁} D]
  [Stacks.Sites.PreservesCoveringPullbacks J f]
  [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  [HasWeakSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify K AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{max r u₁}] [J.WEqualsLocallyBijective AddCommGrpCat.{max r u₁}]
  [HasSheafify J AddCommGrpCat.{max r u₁}]
  [HasWeakSheafify K AddCommGrpCat.{max r u₁}] [K.WEqualsLocallyBijective AddCommGrpCat.{max r u₁}]
  [HasSheafify K AddCommGrpCat.{max r u₁}]
  [(SheafOfModules.pushforward.{r} (F := f)
    (idRingMap J K f (Stacks.SheafOfModules.Tensor.ringSheaf O))).IsRightAdjoint]
  [∀ U : C, (SheafOfModules.pushforward.{r} (F := Over.forget U)
    (𝟙 ((inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)).over U) :
      (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)).over U ⟶
        (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)).over U)).IsRightAdjoint]
  [∀ U : C, (SheafOfModules.pushforward.{max r u₁} (F := Over.forget U)
    (𝟙 ((inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (ULift.liftedStructureSheaf.{u₁} K O))).over U) :
      (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (ULift.liftedStructureSheaf.{u₁} K O))).over U ⟶
        (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf
          (ULift.liftedStructureSheaf.{u₁} K O))).over U)).IsRightAdjoint]
  [HasDerivedCategory.{t₁} (SheafOfModules.{r}
    (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)))]
  [HasDerivedCategory.{t₂} (SheafOfModules.{r} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{t₃} (SheafOfModules.{max r u₁}
    (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)))]
  [HasDerivedCategory.{t₄} (SheafOfModules.{max r u₁} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [(lowerShriekOnHomotopy J K f (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (sourceQuasiIso J K f (Stacks.SheafOfModules.Tensor.ringSheaf O))]

/-- A functor of abelian categories preserving finite limits and colimits of size `r` is additive,
preserves finite colimits and preserves homology. -/
private theorem additive_and_preservesHomology_of_preservesColimitsOfSize.{r'}
    {A : Type*} [Category A] [Abelian A] {B : Type*} [Category B] [Abelian B] (F : A ⥤ B)
    [PreservesFiniteLimits F] [PreservesColimitsOfSize.{r', r'} F] :
    F.Additive ∧ PreservesFiniteColimits F ∧ F.PreservesHomology := by
  have : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink _
  have : PreservesFiniteColimits F := ⟨fun _ _ _ => inferInstance⟩
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have := Functor.additive_of_preservesBinaryBiproducts F
  exact ⟨inferInstance, inferInstance, Functor.preservesHomologyOfExact F⟩

/-- **The derived lower shriek of modules commutes with raising the universe of the sections,
on cohomology sheaves.** For a sheaf of `O_C`-modules `H` with sections in the universe of the
rings and every `p`, `Λ H^p(Lg_! H) ≅ H^p(Lg_! (Λ H))`, `Λ` raising the universe of the sections
to one containing the sites, the two derived lower shrieks being those of Stacks 07AS at the two
universes, for any models of the derived categories. -/
theorem nonempty_homologyDerivedLowerShriekULiftIso
    (H : SheafOfModules.{r} (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (p : ℤ) :
    Nonempty ((targetULift K (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj
        ((DerivedCategory.homologyFunctor _ p).obj
          ((totalLeftDerivedLowerShriek J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj
            ((DerivedCategory.singleFunctor _ 0).obj H))) ≅
      (DerivedCategory.homologyFunctor _ p).obj ((ULift.derivedLowerShriek.{u₁} J K f O).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((sourceULift J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj H)))) := by
  obtain ⟨P, hP0, π, hπ, hPsum⟩ := exists_quasiIso_isSumOfExtensionByZeroUnits _ H
  let Λc := sourceULift J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)
  let Λd := targetULift K (Stacks.SheafOfModules.Tensor.ringSheaf O)
  have hFP := SmallModel.lowerShriekModules_acyclic_of_essentiallySmall J K f O
  -- the universe of the rings
  have := isIso_totalLeftDerivedLowerShriekCounit_app J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf O) hFP P hP0 hPsum
  have : IsIso (DerivedCategory.Q.map π) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := π)).2 hπ
  let L₁ := ((lowerShriekModules J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf O)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  let i₁ : (totalLeftDerivedLowerShriek J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj
      ((DerivedCategory.singleFunctor _ 0).obj H) ≅ DerivedCategory.Q.obj L₁ :=
    (totalLeftDerivedLowerShriek J K f (Stacks.SheafOfModules.Tensor.ringSheaf O)).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app H ≪≫
          (asIso (DerivedCategory.Q.map π)).symm ≪≫
          ((DerivedCategory.quotientCompQhIso _).app P).symm) ≪≫
      asIso ((totalLeftDerivedLowerShriekCounit J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≪≫
      (DerivedCategory.quotientCompQhIso _).app L₁
  -- the raised universe
  have : PreservesFiniteLimits Λc :=
    SheafOfModules.preservesFiniteLimits_uliftForPresentationFunctor _
  have : PreservesColimitsOfSize.{r, r} Λc :=
    SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor' _
  have : PreservesFiniteLimits Λd :=
    SheafOfModules.preservesFiniteLimits_uliftForPresentationFunctor _
  have : PreservesColimitsOfSize.{r, r} Λd :=
    SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor' _
  obtain ⟨_, _, _⟩ := additive_and_preservesHomology_of_preservesColimitsOfSize.{r} Λc
  obtain ⟨_, _, _⟩ := additive_and_preservesHomology_of_preservesColimitsOfSize.{r} Λd
  let P' := (Λc.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hP'0 : CochainComplex.IsStrictlyLE P' 0 :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff P Λc 0).2 hP0
  have hP'sum := fun n => isSumOfExtensionByZeroUnits_sourceModulesEquivalence_sourceULift
    J K f O (hPsum n)
  let i₂ := ULift.derivedLowerShriekObjQIso.{u₁} J K f O P' hP'0 hP'sum
  have : IsIso (DerivedCategory.Q.map ((Λc.mapHomologicalComplex (ComplexShape.up ℤ)).map π)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (φ := (Λc.mapHomologicalComplex (ComplexShape.up ℤ)).map π)).2
        (HomologicalComplex.quasiIso_map_of_preservesHomology π Λc)
  let i₃ : (DerivedCategory.singleFunctor _ 0).obj (Λc.obj H) ≅ DerivedCategory.Q.obj P' :=
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app (Λc.obj H) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex Λc (ComplexShape.up ℤ) 0).app H).symm ≪≫
      (asIso (DerivedCategory.Q.map ((Λc.mapHomologicalComplex (ComplexShape.up ℤ)).map π))).symm
  -- the comparison of the two complexes computing the lower shrieks
  let L₂ := ((Stacks.SheafOfModules.lowerShriek.{max u₁ r} J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf O)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P'
  have hα := fun n => isIso_lowerShriekULiftComparison_app J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf O) (hPsum n)
  let i₄ : L₂ ≅ (Λd.mapHomologicalComplex (ComplexShape.up ℤ)).obj L₁ :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n => asIso ((lowerShriekULiftComparison J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).app (P.X n)))
      (fun i j _ => ((lowerShriekULiftComparison J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).natTrans.naturality (P.d i j)).symm)
  exact ⟨Λd.mapIso ((DerivedCategory.homologyFunctor _ p).mapIso i₁ ≪≫
      (DerivedCategory.homologyFunctorFactors _ p).app L₁) ≪≫
    ((L₁.sc p).mapHomologyIso Λd).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) p).mapIso i₄.symm ≪≫
    ((DerivedCategory.homologyFunctorFactors _ p).app L₂).symm ≪≫
    (DerivedCategory.homologyFunctor _ p).mapIso
      (i₂.symm ≪≫ (ULift.derivedLowerShriek.{u₁} J K f O).mapIso i₃.symm)⟩

end Comparison


section ComparisonOfTopologies

variable {C : Type u₁} [Category.{r} C] {D : Type u₁} [Category.{r} D]
  (J₁ J₂ : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D) (h : J₁ = J₂)
  [f.IsContinuous J₁ K] [f.IsCocontinuous J₁ K] [f.IsContinuous J₂ K] [f.IsCocontinuous J₂ K]
  (O : Sheaf K CommRingCat.{r})
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max r u₁} RingCat.{max r u₁})]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  [EssentiallySmall.{max r u₁} C] [EssentiallySmall.{max r u₁} D]
  [Stacks.Sites.PreservesCoveringPullbacks J₁ f] [Stacks.Sites.PreservesCoveringPullbacks J₂ f]
  [HasWeakSheafify J₁ AddCommGrpCat.{r}] [J₁.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J₁ AddCommGrpCat.{r}]
  [HasWeakSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify K AddCommGrpCat.{r}]
  [HasWeakSheafify J₁ AddCommGrpCat.{max r u₁}]
  [J₁.WEqualsLocallyBijective AddCommGrpCat.{max r u₁}] [HasSheafify J₁ AddCommGrpCat.{max r u₁}]
  [HasWeakSheafify J₂ AddCommGrpCat.{max r u₁}]
  [J₂.WEqualsLocallyBijective AddCommGrpCat.{max r u₁}] [HasSheafify J₂ AddCommGrpCat.{max r u₁}]
  [HasWeakSheafify K AddCommGrpCat.{max r u₁}] [K.WEqualsLocallyBijective AddCommGrpCat.{max r u₁}]
  [HasSheafify K AddCommGrpCat.{max r u₁}]
  [(SheafOfModules.pushforward.{r} (F := f)
    (idRingMap J₁ K f (Stacks.SheafOfModules.Tensor.ringSheaf O))).IsRightAdjoint]
  [∀ U : C, (SheafOfModules.pushforward.{r} (F := Over.forget U)
    (𝟙 ((inverseImageRing J₁ K f (Stacks.SheafOfModules.Tensor.ringSheaf O)).over U) :
      (inverseImageRing J₁ K f (Stacks.SheafOfModules.Tensor.ringSheaf O)).over U ⟶
        (inverseImageRing J₁ K f
          (Stacks.SheafOfModules.Tensor.ringSheaf O)).over U)).IsRightAdjoint]
  [∀ U : C, (SheafOfModules.pushforward.{max r u₁} (F := Over.forget U)
    (𝟙 ((inverseImageRing J₁ K f (Stacks.SheafOfModules.Tensor.ringSheaf
      (ULift.liftedStructureSheaf.{u₁} K O))).over U) :
      (inverseImageRing J₁ K f (Stacks.SheafOfModules.Tensor.ringSheaf
        (ULift.liftedStructureSheaf.{u₁} K O))).over U ⟶
        (inverseImageRing J₁ K f (Stacks.SheafOfModules.Tensor.ringSheaf
          (ULift.liftedStructureSheaf.{u₁} K O))).over U)).IsRightAdjoint]
  [HasDerivedCategory.{t₁} (SheafOfModules.{r}
    (inverseImageRing J₁ K f (Stacks.SheafOfModules.Tensor.ringSheaf O)))]
  [HasDerivedCategory.{t₂} (SheafOfModules.{r} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{t₃} (SheafOfModules.{max r u₁}
    (inverseImageRing J₂ K f (Stacks.SheafOfModules.Tensor.ringSheaf O)))]
  [HasDerivedCategory.{t₄} (SheafOfModules.{max r u₁} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [(lowerShriekOnHomotopy J₁ K f (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (sourceQuasiIso J₁ K f (Stacks.SheafOfModules.Tensor.ringSheaf O))]

/-- `nonempty_homologyDerivedLowerShriekULiftIso` for two equal topologies on the source site, one
at each universe of the sections. -/
theorem nonempty_homologyDerivedLowerShriekULiftIso_of_eq
    (H : SheafOfModules.{r} (inverseImageRing J₁ K f (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (p : ℤ) :
    Nonempty ((targetULift K (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj
        ((DerivedCategory.homologyFunctor _ p).obj
          ((totalLeftDerivedLowerShriek J₁ K f (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj
            ((DerivedCategory.singleFunctor _ 0).obj H))) ≅
      (DerivedCategory.homologyFunctor _ p).obj ((ULift.derivedLowerShriek.{u₁} J₂ K f O).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((changeTopology K f
          (Stacks.SheafOfModules.Tensor.ringSheaf O) h).obj
            ((sourceULift J₁ K f (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj H))))) := by
  subst h
  exact nonempty_homologyDerivedLowerShriekULiftIso J₁ K f O H p

end ComparisonOfTopologies


section ExactFunctor

universe v₁ v₂ w₁ w₂

/-- **The cohomology sheaves of the image of a complex under an exact functor**: for an exact
functor `F` of abelian categories, `H^p(F X) ≅ F(H^p X)` on the derived categories, `F` acting
degreewise. -/
theorem _root_.CategoryTheory.Functor.nonempty_homology_mapDerivedCategory_obj_iso
    {A : Type w₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A]
    {B : Type w₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory A) (p : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor B p).obj (F.mapDerivedCategory.obj X) ≅
      F.obj ((DerivedCategory.homologyFunctor A p).obj X)) := by
  let K := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  exact ⟨(DerivedCategory.homologyFunctor B p).mapIso (F.mapDerivedCategory.mapIso e.symm) ≪≫
    (DerivedCategory.homologyFunctor B p).mapIso (F.mapDerivedCategoryFactors.app K) ≪≫
    (DerivedCategory.homologyFunctorFactors B p).app ((F.mapHomologicalComplex _).obj K) ≪≫
    (K.sc p).mapHomologyIso F ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors A p).app K).symm ≪≫
    F.mapIso ((DerivedCategory.homologyFunctor A p).mapIso e)⟩

end ExactFunctor

end Stacks.Cohomology.DerivedLowerShriek.ULiftComparison

end
