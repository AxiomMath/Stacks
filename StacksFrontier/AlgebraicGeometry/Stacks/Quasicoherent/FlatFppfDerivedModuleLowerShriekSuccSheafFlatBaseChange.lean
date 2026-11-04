module

public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackDerivedModuleLowerShriekCohomologyLargeSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePresentationRestrictionRaisedRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderIso
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfModuleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfAffineChartFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectStackMapSlicePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfCoherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFlatLocalLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfWeakSerreLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfColimitsLargeSections
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# Stacks 07B3 (2) at module universe `u + 1`

Let `𝒳` be an algebraic stack and `M` a quasi-coherent module on its flat-fppf site with sections
in `Type (u + 1)`, one universe above the structure sheaf. This file proves **Stacks 07B3** (2) at
that universe: every `H^p(Lg_! M)` lies in the faithful `LQCoh^fbc(𝒪_𝒳)`, for the derived lower
shriek `AlgebraicGeometry.Stack.FlatFppf.derivedModuleLowerShriekSucc` of Stacks 07AS (4) at that
universe; equivalently, `Lg_!(M[0]) ∈ D_{LQCoh^fbc}`.

## Main results

* `derivedCategoryB_derivedModuleLowerShriekSucc_singleFunctor`: for a quasi-coherent `M` with
  sections in `Type (u + 1)`, `Lg_!(M[0])` lies in `D_{LQCoh^fbc}(𝒪_𝒳)`.

## Implementation notes

The universe-`u` statement is
`locallyQuasicoherentSheafFlatBaseChange_homology_derivedModuleLowerShriek`. Moving `Lg_!` between
universes along the universe lift of the sections does not reach a module at `u + 1`, so the
argument is carried out directly at `u + 1`:

* Stacks 07AQ (2) at `u + 1` reduces to the flat, locally finitely presented affine charts
  `y : (Sch/U) → 𝒳` mapping to objects over which `M` is globally presented
  (`sheafFlatBaseChangeModuleRule_of_affine_presented`);
* Stacks 07AV at `u + 1` turns `y^{-1} H^p(Lg_! M)` into `H^p(L(g')_! (f')^{-1} M)`, and
  `(f')^{-1} M` has a presentation by global sections over the raised rings
  (`isPresentedByGlobalSections_sourceModulesEquivalenceSucc_moduleSubsiteInverseImage`);
* over the affine `U` a free resolution computes `L(g')_!`, the faithful `LQCoh^fbc` at `u + 1` is
  a weak Serre class (Stacks 0771 (2)) and contains the free modules
  (`sheafFlatBaseChangeModuleRule_fppfModulePullback_homology_derivedModuleLowerShriekSucc`).

The derived categories are the standard models, named by `letI` in the statements, at which
Stacks 07AV at `u + 1` (`moduleDerivedLowerShriekBaseChangeIso`) is stated.

## References

* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
* [Stacks Project, Tag 07AV](https://stacks.math.columbia.edu/tag/07AV)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedLowerShriek

universe u w

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology
  Stacks.hasSheafCompose_forget₂_commRingCat preservesCoveringPullbacks_inclusion_topology
  essentiallySmall_obj_largeSections essentiallySmall_flatFppf_largeSections
  hasSheafify_topology_largeSections wEqualsLocallyBijective_topology_largeSections
  hasSheafify_fppfTopology_largeSections wEqualsLocallyBijective_fppfTopology_largeSections
  hasPointwiseRightKanExtension_inclusion_ringCat_largeSections
  hasPointwiseRightKanExtension_inclusion_addCommGrpCat_largeSections

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **A presentation over an object, restricted to a flat affine chart mapping to it, is a
presentation by global sections over the raised rings**, at module universe `u + 1`. For a
module `M` on the flat-fppf site of `𝒳` with sections in `Type (u + 1)` and a global presentation
over `V`, and a flat object `y` with an arrow `y ⟶ V`, the restriction `(f')^{-1} M` of `M` to the
flat-fppf site of `(Sch/U)`, `U` the scheme under `y`, read over the structure sheaf raised to
`Type (u + 1)`, has a presentation by global sections. -/
theorem isPresentedByGlobalSections_sourceModulesEquivalenceSucc_moduleSubsiteInverseImage
    (M : SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) (y V : FlatFppf B S hS 𝒳)
    (g : y ⟶ V) (hV : (M.over V).HasGlobalPresentation) :
    ((sourceModulesEquivalenceSucc B S hS
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))).functor.obj
        ((moduleSubsiteInverseImage B S hS (objectStackMap B S hS 𝒳 y.obj) y.property).obj
          M)).IsPresentedByGlobalSections := by
  have := isContinuous_subsiteFunctor_topology B S hS (objectStackMap B S hS 𝒳 y.obj) y.property
  have := isCocontinuous_subsiteFunctor_topology B S hS (objectStackMap B S hS 𝒳 y.obj)
    y.property
  have := isContinuous_inclusion_topology B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  exact Stacks.SheafOfModules.isPresentedByGlobalSections_map_pushforward_of_isTerminal.{u, 0,
      u + 1, u}
    (𝒪 := (structureSheaf B S hS 𝒳).val) (subsiteRingStructureSheaf B S hS 𝒳).cond
    ((hasSheafCompose_forget_ringCat (topology B S hS 𝒳)).isSheaf _
      (subsiteRingStructureSheaf B S hS 𝒳).cond)
    (topology B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)))
    (𝒪' := (structureSheaf B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))).val)
    (subsiteRingStructureSheaf B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))).cond
    (isTerminalFlatObjectSchemeStackId.{u, w} B S hS _)
    (primedSiteFunctor B S hS (objectStackMap B S hS 𝒳 y.obj) y.property) V
    (primedSiteFunctorTerminalHom B S hS 𝒳 y ≫ g)
    (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS (objectStackMap B S hS 𝒳 y.obj)
      y.property).symm)
    (eqToIso (subsiteRingStructureSheaf_inverseImageRing B S hS (objectStackMap B S hS 𝒳 y.obj)
      y.property).symm).isIso_hom
    (sourceModulesEquivalenceSucc B S hS
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))).functor
    (Adjunction.leftAdjoint_preservesColimits (sourceModulesEquivalenceSucc B S hS
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))).toAdjunction)
    ⟨fun _ _ => rfl⟩
    (ULift.sourceModulesEquivalenceFunctorUnitIso.{u + 1}
      (fppfTopology B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)))
      (ambientStructureSheaf B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)))
      (topology B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)))
      (objectProperty B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))).ι)
    M hV

/-- **The universe lift of the structure sheaf lies in the faithful `LQCoh^fbc`** at module
universe `u + 1`: it is an étale sheaf, and it is cartesian over every arrow, its base change maps
being those of the structure presheaf with raised sections
(`Stacks.PresheafOfModules.isIso_restrictionBaseChange_largeUnit`). -/
theorem sheafFlatBaseChangeModulesSucc_uliftForPresentation_unit :
    sheafFlatBaseChangeModulesSucc B E h S hS 𝒳
      (SheafOfModules.uliftForPresentation.{_, _, u, u, u + 1}
        (SheafOfModules.unit (ambientRingStructureSheaf B S hS 𝒳))) :=
  isLocallyQuasicoherentWithSheafFlatBaseChangeUnivLE_of_isCartesianOnFlatAffineArrows.{u, u + 1,
    u, u} B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids _
    ((SheafOfModules.uliftForPresentation.{_, _, u, u, u + 1}
      (SheafOfModules.unit (ambientRingStructureSheaf B S hS 𝒳))).isSheaf.of_le
        (BigFppfOver.associatedTopology_le_fppf B S hS _ .etale))
    fun _ _ φ _ _ _ => (ConcreteCategory.isIso_iff_bijective _).1
      (Stacks.PresheafOfModules.isIso_restrictionBaseChange_largeUnit.{_, _, u, u + 1}
        (Stack.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).obj φ.op)

/-- **Free modules at module universe `u + 1` lie in the faithful `LQCoh^fbc`**: a direct sum,
indexed by a type in `Type (u + 1)`, of copies of the universe lift of the structure sheaf. The
universe lift of the structure sheaf lies in it, and it is closed under direct sums
(Stacks 0771 (5) at that universe). -/
theorem sheafFlatBaseChangeModulesSucc_of_isColimit_cofan_uliftForPresentation_unit
    {I : Type (u + 1)} {F : SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)}
    (ι : I → (SheafOfModules.uliftForPresentation.{_, _, u, u, u + 1}
      (SheafOfModules.unit (ambientRingStructureSheaf B S hS 𝒳)) ⟶ F))
    (hc : Nonempty (IsColimit (Cofan.mk F ι))) :
    sheafFlatBaseChangeModulesSucc B E h S hS 𝒳 F := by
  have :=
    isClosedUnderColimitsOfShape_discrete_isLocallyQuasicoherentWithSheafFlatBaseChange_fppf_succ
      B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids I
  exact ObjectProperty.prop_of_isColimit
    (fun F : SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳) =>
      IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u + 1} B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val) hc.some
    fun _ => sheafFlatBaseChangeModulesSucc_uliftForPresentation_unit B E h S hS 𝒳

/-- **Stacks 07B3 (2) at module universe `u + 1` on a flat affine chart.** For a module `M` on the
flat-fppf site of `𝒳` with sections in `Type (u + 1)`, a flat object `y` over an affine scheme `U`
with an arrow to an object over which `M` has a global presentation, and every `p`, the inverse
image of `H^p(Lg_! M)` along `y : (Sch/U) → 𝒳` lies in `LQCoh^fbc`: by Stacks 07AV it is
`H^p(L(g')_! (f')^{-1} M)`, `(f')^{-1} M` is globally presented, and over an affine scheme a free
resolution computes `L(g')_!`. -/
theorem sheafFlatBaseChangeModuleRule_fppfModulePullback_homology_derivedModuleLowerShriekSucc
    (M : SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) (p : ℤ)
    (y V : FlatFppf B S hS 𝒳) (g : y ⟶ V)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y.obj)))
    (hV : (M.over V).HasGlobalPresentation) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    AlgebraicStacks.sheafFlatBaseChangeModuleRule B S hS E h
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
      ((AlgebraicStacks.fppfModulePullback B S hS (objectStackMap B S hS 𝒳 y.obj)).obj
        ((DerivedCategory.homologyFunctor _ p).obj ((derivedModuleLowerShriekSucc B S hS 𝒳).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)))) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
  have := isContinuous_inclusion_topology B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  have := isCocontinuous_inclusion_topology B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  have := hasSheafify_topology_largeSections B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  have := wEqualsLocallyBijective_topology_largeSections B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  have := hasSheafify_fppfTopology_largeSections B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  have := wEqualsLocallyBijective_fppfTopology_largeSections B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  have := essentiallySmall_obj_largeSections B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  have := essentiallySmall_flatFppf_largeSections B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  have := preservesCoveringPullbacks_inclusion_topology B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1}
    (subsiteRingStructureSheaf B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))))
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1}
    (ambientRingStructureSheaf B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))))
  obtain ⟨F, π, hF, hπ, hfr⟩ :=
    exists_quasiIso_isFree_schemeStack_succ B S hS (𝒳.val.val.p.obj y.obj) hU
      ((moduleSubsiteInverseImage B S hS (objectStackMap B S hS 𝒳 y.obj) y.property).obj M)
      (isPresentedByGlobalSections_sourceModulesEquivalenceSucc_moduleSubsiteInverseImage
        B S hS 𝒳 M y V g hV)
  have : (sheafFlatBaseChangeModulesSucc B E h S hS
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))).IsWeakSerreClass :=
    isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppfModulesSucc B E h S hS
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  have hG := prop_homology_derivedModuleLowerShriekSucc_of_quasiIso B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
    (isTerminalFlatObjectSchemeStackId.{u, w} B S hS (𝒳.val.val.p.obj y.obj)) Over.mkIdTerminal
    (sheafFlatBaseChangeModulesSucc B E h S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)))
    (fun _ _ ι hc => sheafFlatBaseChangeModulesSucc_of_isColimit_cofan_uliftForPresentation_unit
      B E h S hS _ ι hc) _ F hF hfr π hπ p
  have := preservesFiniteLimits_modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)).val.val.p 𝒳.val.val.p
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids
    (objectStackMap B S hS 𝒳 y.obj).hom.hom.toFunctor
    (objectStackMap B S hS 𝒳 y.obj).hom.hom.w B.topology le_rfl
  have := preservesFiniteColimits_modulePullback.{u, u + 1, u, u, u + 1, u} B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)).val.val.p 𝒳.val.val.p
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids
    (objectStackMap B S hS 𝒳 y.obj).hom.hom.toFunctor
    (objectStackMap B S hS 𝒳 y.obj).hom.hom.w B.topology le_rfl
  have : (AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)).val.val.p 𝒳.val.val.p
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)).val.isFiberedInGroupoids
      𝒳.val.isFiberedInGroupoids
      (objectStackMap B S hS 𝒳 y.obj).hom.hom.toFunctor
      (objectStackMap B S hS 𝒳 y.obj).hom.hom.w B.topology le_rfl).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  have := isContinuous_subsiteFunctor_topology B S hS (objectStackMap B S hS 𝒳 y.obj) y.property
  have := isCocontinuous_subsiteFunctor_topology B S hS (objectStackMap B S hS 𝒳 y.obj) y.property
  have hex := _root_.SheafOfModules.exactFunctor_pushforward_of_isCocontinuous.{u + 1, u, u + 1,
    u, u, u + 1} (primedSiteFunctor B S hS (objectStackMap B S hS 𝒳 y.obj) y.property)
    (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS (objectStackMap B S hS 𝒳 y.obj)
      y.property).symm)
  have : PreservesFiniteLimits
      (moduleSubsiteInverseImage B S hS (objectStackMap B S hS 𝒳 y.obj) y.property) := hex.1
  have : PreservesFiniteColimits
      (moduleSubsiteInverseImage B S hS (objectStackMap B S hS 𝒳 y.obj) y.property) := hex.2
  let e₀ := (moduleDerivedLowerShriekBaseChangeIso B S hS (objectStackMap B S hS 𝒳 y.obj)
    y.property).app ((DerivedCategory.singleFunctor _ 0).obj M)
  let e₁ := ((AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)).val.val.p 𝒳.val.val.p
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)).val.isFiberedInGroupoids
      𝒳.val.isFiberedInGroupoids
      (objectStackMap B S hS 𝒳 y.obj).hom.hom.toFunctor
      (objectStackMap B S hS 𝒳 y.obj).hom.hom.w B.topology le_rfl).mapDerivedCategoryHomologyIso
        p).app
    ((derivedModuleLowerShriekSucc B S hS 𝒳).obj ((DerivedCategory.singleFunctor _ 0).obj M))
  let e₂ := ((moduleSubsiteInverseImage B S hS (objectStackMap B S hS 𝒳 y.obj)
    y.property).mapDerivedCategorySingleFunctor 0).app M
  exact ObjectProperty.prop_of_iso _ (e₁.symm ≪≫ (DerivedCategory.homologyFunctor _ p).mapIso
    (e₀ ≪≫ (derivedModuleLowerShriekSucc B S hS
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))).mapIso e₂)).symm hG

/-- **Stacks 07B3 (2) at module universe `u + 1`, the reduction to affine charts.** Let `H` be a
quasi-coherent module on the flat-fppf site of `𝒳` with sections in `Type (u + 1)`, and `F` a
module on `𝒳_fppf` with sections in `Type (u + 1)`. If the pullback of `F` along `y : (Sch/U) → 𝒳`
lies in `LQCoh^fbc` for every flat object `y` over an affine scheme `U` admitting an arrow to an
object over which `H` has a global presentation, then `F` lies in `LQCoh^fbc(𝒪_𝒳)`: Stacks 07AQ (2)
at that universe
(`AlgebraicGeometry.Stack.AlgebraicStacks.sheafFlatBaseChangeModuleRule_of_flatLfp_cover_of_atlas`)
for the flat, locally finitely presented, jointly surjective affine family of Stacks 03DL (6). -/
theorem sheafFlatBaseChangeModuleRule_of_affine_presented
    {R : Sheaf (topology B S hS 𝒳) RingCat.{u}} (H : SheafOfModules.{u + 1} R)
    (hH : H.IsQuasicoherentOnSite) (F : AlgebraicStacks.fppfModules B S hS 𝒳)
    (hF : ∀ (y V : FlatFppf B S hS 𝒳) (_ : y ⟶ V),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y.obj)) →
      (H.over V).HasGlobalPresentation →
      AlgebraicStacks.sheafFlatBaseChangeModuleRule B S hS E h
        (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
        ((AlgebraicStacks.fppfModulePullback B S hS (objectStackMap B S hS 𝒳 y.obj)).obj F)) :
    AlgebraicStacks.sheafFlatBaseChangeModuleRule B S hS E h 𝒳 F := by
  obtain ⟨x₀, hsm, hsurj⟩ := exists_smooth_surjective_objectMorphism _ _ _ 𝒳
  have hx₀ : flatObject B S hS 𝒳.val x₀ := flatObject_of_smoothObject B S hS 𝒳 hsm
  let J := {d : (y : FlatFppf B S hS 𝒳) × (V : FlatFppf B S hS 𝒳) × (y ⟶ V) × (y.obj ⟶ x₀) //
    IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj d.1.obj)) ∧
      (H.over d.2.1).HasGlobalPresentation ∧
      Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map d.2.2.2)) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map d.2.2.2))}
  refine AlgebraicStacks.sheafFlatBaseChangeModuleRule_of_flatLfp_cover_of_atlas
    B E h S hS 𝒳 x₀ hsm hsurj (J := J) (fun j => j.1.1.obj) (fun j => j.1.2.2.2)
    (fun j => j.2.2.2.1) (fun j => j.2.2.2.2) (fun t => ?_) F
    (fun j => hF j.1.1 j.1.2.1 j.1.2.2.1 j.2.1 j.2.2.1)
  obtain ⟨y, V, a, g, haff, hpres, hflat, hlfp, s, hs⟩ :=
    exists_flat_lfp_affine_presented B S hS 𝒳 H hH x₀ hx₀ t
  exact ⟨⟨⟨y, V, a, g⟩, haff, hpres, hflat, hlfp⟩, s, hs⟩

/-- **Stacks 07B3 (2) at module universe `u + 1`**. Let `M` be a quasi-coherent module
(Stacks 03DL) on the flat-fppf site of an algebraic stack `𝒳`, with sections in `Type (u + 1)`.
Then `Lg_!(M[0])`, for the derived lower shriek of Stacks 07AS (4) at that universe, lies in
`D_{LQCoh^fbc}(𝒪_𝒳)`: every `H^p(Lg_! M)` is locally quasi-coherent with the flat base change
property of Stacks 0762, read with the pullback of sheaves. The derived categories are the
standard models. -/
theorem derivedCategoryB_derivedModuleLowerShriekSucc_singleFunctor :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    ∀ M : SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳),
      M.IsQuasicoherentOnSite → DerivedCategoryB.derivedCategoryB
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
        ((derivedModuleLowerShriekSucc B S hS 𝒳).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) := fun M hM p =>
  sheafFlatBaseChangeModuleRule_of_affine_presented B E h S hS 𝒳 M hM _ fun y V g hU hV =>
    sheafFlatBaseChangeModuleRule_fppfModulePullback_homology_derivedModuleLowerShriekSucc
      B E h S hS 𝒳 M p y V g hU hV

end AlgebraicGeometry.Stack.FlatFppf
