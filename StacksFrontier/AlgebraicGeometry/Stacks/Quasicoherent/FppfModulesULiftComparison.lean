module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleRuleCriterion
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPrecompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# Higher direct images and cohomology of modules on algebraic stacks across the universe lift

Let `𝒳` be an algebraic stack over `S`. Sheaves of `𝒪_𝒳`-modules on the fppf site are taken in
this library at the module universe `u` of the schemes (`AlgebraicGeometry.Stack.fppfModules`),
where the inverse image, the quasi-coherent theory and the direct image
`AlgebraicGeometry.Stack.fppfModulesPushforward` live, and also at the universe `u + 1` of the
objects of the site (`AlgebraicGeometry.Stack.AlgebraicStacks.fppfModules`), where the direct
image of **Stacks 06WE** is first constructed. The universe lift
`AlgebraicGeometry.Stack.fppfModulesULift` from the first to the second is fully faithful and
exact. This file proves that it also preserves injective objects, and deduces that it carries the
higher direct images and the cohomology at `u` to those at `u + 1`.

## Main results

* `AlgebraicGeometry.Stack.preservesInjectiveObjects_fppfModulesULift`: the universe lift
  preserves injective objects.
* `AlgebraicGeometry.Stack.fppfModulesHigherDirectImageULiftIso`: the lift of `Rⁱf_*ℱ`, taken
  at `u`, is `Rⁱf_*` at `u + 1` of the lift of `ℱ`.
* `AlgebraicGeometry.Stack.fppfModuleCohomologyULiftIso`: the cohomology
  `H^i(𝒳, ℱ) = Ext^i(𝒪_𝒳, ℱ)` at `u` is `Ext^i` out of the lifted structure sheaf at `u + 1` of
  the lift of `ℱ`.
* `AlgebraicGeometry.Stack.isZero_fppfModuleCohomology_iff`: hence the cohomology at `u` of `ℱ`
  vanishes exactly when that at `u + 1` of its lift does, for `Ext`-groups in any universe.

## Implementation notes

Preservation of injective objects is Baer's criterion
(`Stacks.SheafOfModules.injective_moduleULift_obj`): the site of an algebraic stack is essentially
`u`-small (`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`), so every section of a
sheaf of modules at `u + 1` lies in a subsheaf coming from `u`. Given it, both comparisons are
formal: an exact functor commutes with right derived functors on the left
(`CategoryTheory.Functor.rightDerivedCompIso`), an exact functor preserving injective objects on
the right (`CategoryTheory.Functor.rightDerivedCompIsoOfPreservesInjectiveObjects`), and
`Ext`-functors out of objects corepresenting the same functor along an exact functor sending
injectives to acyclic objects agree (`ModuleSheafCohomology.extComparisonIso`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u w t

namespace AlgebraicGeometry.Stack

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  AlgebraicStacks.hasSheafify_fppfAssociatedTopology
  AlgebraicStacks.wEqualsLocallyBijective_fppfAssociatedTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The universe lift preserves injective objects -/

/-- **The universe lift of modules on an algebraic stack preserves injective objects**: an
injective `𝒪_𝒳`-module at the module universe `u` is still injective at `u + 1`. This is
`Stacks.SheafOfModules.preservesInjectiveObjects_moduleULift`, whose inputs are that the site of
`𝒳` is essentially `u`-small and that modules at `u + 1` form a Grothendieck abelian category. -/
theorem preservesInjectiveObjects_fppfModulesULift (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (fppfModulesULift B S hS 𝒳).PreservesInjectiveObjects := by
  have := isGrothendieckAbelian_fppfModules B S hS 𝒳
  have : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u, 0} _
  exact Stacks.SheafOfModules.preservesInjectiveObjects_moduleULift.{u + 1, u}

/-- The universe lift of modules on an algebraic stack is additive. -/
instance additive_fppfModulesULift (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (fppfModulesULift B S hS 𝒳).Additive :=
  inferInstanceAs (Stacks.SheafOfModules.moduleULift.{u + 1, u} _).Additive

/-- Modules on an algebraic stack at the module universe `u + 1` have `Ext`-groups in `u + 1`:
they form a Grothendieck abelian category. -/
theorem hasExt_fppfModules_succ (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasExt.{u + 1} (SheafOfModules.{u + 1}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)) :=
  have : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u, 0} _
  inferInstance

attribute [local instance] hasExt_fppfModules_succ

variable {B S hS}

/-- The universe lift of modules on an algebraic stack is exact, hence preserves homology. -/
theorem preservesHomology_fppfModulesULift (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (fppfModulesULift B S hS 𝒳).PreservesHomology :=
  have : PreservesFiniteLimits (fppfModulesULift B S hS 𝒳) :=
    Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
  have : PreservesFiniteColimits (fppfModulesULift B S hS 𝒳) :=
    Stacks.SheafOfModules.preservesFiniteColimits_moduleULift.{u + 1, u} _
  inferInstance

/-! ### Higher direct images -/

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **The higher direct images commute with the universe lift.** For a `1`-morphism `f : 𝒳 ⟶ 𝒴`
of algebraic stacks and a sheaf of `𝒪_𝒳`-modules `ℱ` at the module universe `u`, the lift of
`Rⁿf_*ℱ` is `Rⁿf_*` at `u + 1` of the lift of `ℱ`.

The lift is exact, so it commutes with the right derived functors of `f_*` on the left; the lift
of `f_*` at `u` is `f_*` at `u + 1` of the lift
(`AlgebraicGeometry.Stack.fppfModulesPushforwardULiftIso`); and the lift preserves injective
objects (`AlgebraicGeometry.Stack.preservesInjectiveObjects_fppfModulesULift`), so it carries an
injective resolution to one. -/
def fppfModulesHigherDirectImageULiftIso (n : ℕ) (F : fppfModules B S hS 𝒳) :
    (fppfModulesULift B S hS 𝒴).obj ((fppfModulesHigherDirectImage B S hS f n).obj F) ≅
      (AlgebraicStacks.fppfHigherDirectImage B S hS f n).obj
        ((fppfModulesULift B S hS 𝒳).obj F) :=
  letI := enoughInjectives_fppfModules B S hS 𝒳
  letI : EnoughInjectives (AlgebraicStacks.fppfModules B S hS 𝒳) :=
    enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl
  haveI := preservesInjectiveObjects_fppfModulesULift B S hS 𝒳
  haveI := preservesHomology_fppfModulesULift 𝒳
  haveI := preservesHomology_fppfModulesULift 𝒴
  ((Functor.rightDerivedCompIso (fppfModulesPushforward B S hS f)
      (fppfModulesULift B S hS 𝒴) n).app F).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso (fppfModulesPushforwardULiftIso B S hS f) n).app F ≪≫
    Functor.rightDerivedCompIsoOfPreservesInjectiveObjects (fppfModulesULift B S hS 𝒳)
      (fppfModulesPushforwardSucc B S hS f) F n

/-! ### Cohomology -/

variable (𝒳) in
/-- The lifted structure sheaf `𝒪_𝒳` at the module universe `u + 1`: the universe lift of the
structure sheaf at `u`, which is `Stacks.SheafOfModules.uliftUnit`. -/
abbrev fppfModulesULiftUnit : SheafOfModules.{u + 1}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf) :=
  Stacks.SheafOfModules.uliftUnit.{u + 1} _

variable (𝒳) in
/-- **Morphisms out of the structure sheaf are morphisms out of its lift**, the universe lift
being fully faithful: as functors of the module, `Hom(𝒪_𝒳, -)` at `u` is `Hom(𝒪_𝒳, -)` at `u + 1`
after the lift. -/
def fppfModulesULiftCoyonedaIso :
    preadditiveCoyoneda.obj (op (SheafOfModules.unit (FibredSite.ringStructureSheafCore B S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf))) ≅
      Stacks.SheafOfModules.moduleULift.{u + 1, u} _ ⋙
        preadditiveCoyoneda.obj (op (fppfModulesULiftUnit 𝒳)) :=
  NatIso.ofComponents (fun M =>
      (AddEquiv.mk (fppfModulesULiftFullyFaithful B S hS 𝒳).homEquiv
        (fun _ _ => (fppfModulesULift B S hS 𝒳).map_add)).toAddCommGrpIso)
    (fun {M N} g => by
      ext a
      exact (fppfModulesULift B S hS 𝒳).map_comp a g)

variable (𝒳) in
/-- **The cohomology of a module at `u` is the cohomology of its lift at `u + 1`.** For every
degree `i`, `H^i(𝒳, ℱ) = Ext^i(𝒪_𝒳, ℱ)` computed among the modules at `u` is `Ext^i` out of the
lifted structure sheaf, computed among the modules at `u + 1`, of the lift of `ℱ`, naturally in
`ℱ`: the lift is exact, `Hom(𝒪_𝒳, -)` is corepresented on both sides compatibly
(`AlgebraicGeometry.Stack.fppfModulesULiftCoyonedaIso`), and the lift of an injective module is
injective (`AlgebraicGeometry.Stack.preservesInjectiveObjects_fppfModulesULift`), hence has no
higher `Ext`. -/
def fppfModuleCohomologyULiftIso [HasExt.{u + 1} (fppfModules B S hS 𝒳)] (i : ℕ) :
    FlatFppf.fppfModuleCohomology.{u, w, u + 1} B S hS 𝒳 i ≅
      Stacks.SheafOfModules.moduleULift.{u + 1, u} _ ⋙
        extFunctorObj.{u + 1} (fppfModulesULiftUnit 𝒳) i :=
  letI := enoughInjectives_fppfModules B S hS 𝒳
  haveI := preservesInjectiveObjects_fppfModulesULift B S hS 𝒳
  haveI : PreservesFiniteLimits (Stacks.SheafOfModules.moduleULift.{u + 1, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)) :=
    Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
  haveI : PreservesFiniteColimits (Stacks.SheafOfModules.moduleULift.{u + 1, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)) :=
    Stacks.SheafOfModules.preservesFiniteColimits_moduleULift.{u + 1, u} _
  ModuleSheafCohomology.extComparisonIso (Stacks.SheafOfModules.moduleULift.{u + 1, u} _)
    (fppfModulesULiftUnit 𝒳)
    (SheafOfModules.unit _)
    (fun I _ n e =>
      haveI : Injective ((Stacks.SheafOfModules.moduleULift.{u + 1, u}
          (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
            .fppf)).obj I) :=
        (preservesInjectiveObjects_fppfModulesULift B S hS 𝒳).injective_obj ‹_›
      Ext.eq_zero_of_injective e)
    (fppfModulesULiftCoyonedaIso 𝒳) i

/-! ### Every topology -/

section SiteKind

variable (τ : SiteKind)

/-- Abelian presheaves on the `τ`-site of an algebraic stack can be sheafified at the universe
`u + 1` of its objects. -/
theorem hasSheafify_associatedTopology_succ (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, u + 1}

/-- The sheafification equivalences of abelian presheaves at `u + 1` on the `τ`-site of an
algebraic stack are the locally bijective maps. -/
theorem wEqualsLocallyBijective_associatedTopology_succ (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, u + 1}

/-- **The universe lift of modules on the `τ`-site of an algebraic stack preserves injective
objects**: an injective sheaf of `𝒪_𝒳`-modules on `𝒳_τ` at the module universe `u` is still
injective at `u + 1`. This is `Stacks.SheafOfModules.preservesInjectiveObjects_moduleULift`,
whose inputs are that the site of `𝒳` is essentially `u`-small and that modules at `u + 1` form a
Grothendieck abelian category. -/
theorem preservesInjectiveObjects_stackModuleULift (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (stackModuleULift B S hS τ 𝒳).PreservesInjectiveObjects := by
  let := hasSheafify_associatedTopology_siteKind B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ
  let := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒳.val.val.p τ
  let := hasSheafify_associatedTopology_succ τ 𝒳
  let := wEqualsLocallyBijective_associatedTopology_succ τ 𝒳
  have := isGrothendieckAbelian_moduleRingSheaf B S hS 𝒳 τ
  have : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u, 0} _
  exact Stacks.SheafOfModules.preservesInjectiveObjects_moduleULift.{u + 1, u}

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (k : 𝒳 ⟶ 𝒴)

attribute [local instance] hasSheafify_associatedTopology_succ
  wEqualsLocallyBijective_associatedTopology_succ

/-- **The higher direct images on the `τ`-sites commute with the universe lift**, naturally: for
a `1`-morphism `k : 𝒳 ⟶ 𝒴` of algebraic stacks and every `q`,

`Rᵠk_* ⋙ lift ≅ lift ⋙ Rᵠk_*`,

the left-hand `Rᵠk_*` at the module universe `u`
(`AlgebraicGeometry.Stack.stackModuleHigherDirectImage`) and the right-hand one the higher direct
image `AlgebraicGeometry.Stack.moduleSheafHigherDirectImage` at `u + 1` for the topology `τ`.

The lift is exact, so it commutes with the right derived functors of `k_*` on the left
(`CategoryTheory.Functor.rightDerivedCompIso`); the lift of `k_*` at `u` is `k_*` at `u + 1` of the
lift (`AlgebraicGeometry.Stack.stackModuleDirectImageULiftIso`,
`AlgebraicGeometry.Stack.AlgebraicStacks.moduleDirectImageRightDerivedIso`); and the lift
preserves injective objects (`AlgebraicGeometry.Stack.preservesInjectiveObjects_stackModuleULift`),
so it carries injective resolutions to injective resolutions
(`CategoryTheory.Functor.rightDerivedCompNatIsoOfPreservesInjectiveObjects`). -/
def stackModuleHigherDirectImageULiftIso (q : ℕ) :
    stackModuleHigherDirectImage B S hS k τ q ⋙ stackModuleULift B S hS τ 𝒴 ≅
      stackModuleULift B S hS τ 𝒳 ⋙
        moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
          𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor k.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p k.hom) (B.baseTopology τ)
          (B.baseTopology_le_topology τ) q :=
  letI := hasSheafify_associatedTopology_siteKind B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ
  letI := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒳.val.val.p τ
  letI := hasSheafify_associatedTopology_siteKind B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ
  letI := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒴.val.val.p τ
  letI := enoughInjectives_moduleRingSheaf B S hS 𝒳 τ
  letI : EnoughInjectives (SheafOfModules.{u + 1}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)) :=
    enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (B.baseTopology τ) (B.baseTopology_le_topology τ)
  haveI := preservesInjectiveObjects_stackModuleULift τ 𝒳
  haveI : PreservesFiniteLimits (stackModuleULift B S hS τ 𝒳) :=
    Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
  haveI : PreservesFiniteColimits (stackModuleULift B S hS τ 𝒳) :=
    Stacks.SheafOfModules.preservesFiniteColimits_moduleULift.{u + 1, u} _
  haveI : PreservesFiniteLimits (stackModuleULift B S hS τ 𝒴) :=
    Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
  haveI : PreservesFiniteColimits (stackModuleULift B S hS τ 𝒴) :=
    Stacks.SheafOfModules.preservesFiniteColimits_moduleULift.{u + 1, u} _
  haveI : (stackModuleDirectImageSucc B S hS k τ).Additive :=
    Stacks.RelativeCech.moduleDirectImage_additive.{u, u + 1, u + 1, u, u, u} B S hS
      𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor k.hom) (CatFiberedInGroupoids.homFunctor_comp_p k.hom) τ
  (Functor.rightDerivedCompIso (stackModuleDirectImage B S hS k τ)
      (stackModuleULift B S hS τ 𝒴) q).symm ≪≫
    Functor.rightDerivedIsoOfNatIso (stackModuleDirectImageULiftIso B S hS k τ) q ≪≫
    Functor.rightDerivedCompNatIsoOfPreservesInjectiveObjects (stackModuleULift B S hS τ 𝒳)
      (stackModuleDirectImageSucc B S hS k τ) q ≪≫
    Functor.isoWhiskerLeft (stackModuleULift B S hS τ 𝒳)
      (AlgebraicStacks.moduleDirectImageRightDerivedIso B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor k.hom) (CatFiberedInGroupoids.homFunctor_comp_p k.hom)
        τ q)

/-- **The comparison of higher direct images across the universe lift, in the form the criteria of
Stacks 076Z and Stacks 0770 consume**
(`AlgebraicGeometry.Stack.StackModuleRule.HigherDirectImageULiftComparison`): for every
`1`-morphism `k` of algebraic stacks and every `q`, the lift followed by `Rᵠk_*` at `u + 1` is
`Rᵠk_*` at `u` followed by the lift. This is
`AlgebraicGeometry.Stack.stackModuleHigherDirectImageULiftIso`, for every topology `τ`. -/
theorem higherDirectImageULiftComparison :
    StackModuleRule.HigherDirectImageULiftComparison.{u, w} B S hS τ :=
  fun k q => ⟨(stackModuleHigherDirectImageULiftIso τ k q).symm⟩

/-- Modules on the `τ`-site of an algebraic stack at the module universe `u + 1` have
`Ext`-groups in `u + 1`: they form a Grothendieck abelian category. -/
theorem hasExt_stackModules_succ (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasExt.{u + 1} (SheafOfModules.{u + 1}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)) :=
  have : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u, 0} _
  inferInstance

attribute [local instance] hasExt_stackModules_succ

variable (𝒳) in
/-- **The cohomology of a module on the `τ`-site at `u` is the cohomology of its lift at
`u + 1`.** For every degree `i`, `H^i(𝒳_τ, ℱ) = Ext^i(𝒪_𝒳, ℱ)` computed among the modules at `u`
is `Ext^i` out of the lifted structure sheaf `Stacks.SheafOfModules.uliftUnit`, computed among
the modules at `u + 1`, of the lift of `ℱ`, naturally in `ℱ`: the lift is exact, fully faithful,
and preserves injective objects
(`AlgebraicGeometry.Stack.preservesInjectiveObjects_stackModuleULift`).

This is `AlgebraicGeometry.Stack.fppfModuleCohomologyULiftIso` for every topology `τ`. -/
def stackModuleCohomologyULiftIso
    [HasExt.{u + 1} (SheafOfModules.{u}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ))]
    (i : ℕ) :
    extFunctorObj.{u + 1} (SheafOfModules.unit
        (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)) i ≅
      stackModuleULift B S hS τ 𝒳 ⋙ extFunctorObj.{u + 1} (Stacks.SheafOfModules.uliftUnit.{u + 1}
        (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)) i :=
  letI := enoughInjectives_moduleRingSheaf B S hS 𝒳 τ
  haveI := preservesInjectiveObjects_stackModuleULift τ 𝒳
  haveI : PreservesFiniteLimits (stackModuleULift B S hS τ 𝒳) :=
    Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
  haveI : PreservesFiniteColimits (stackModuleULift B S hS τ 𝒳) :=
    Stacks.SheafOfModules.preservesFiniteColimits_moduleULift.{u + 1, u} _
  haveI : (stackModuleULift B S hS τ 𝒳).Additive :=
    inferInstanceAs (Stacks.SheafOfModules.moduleULift.{u + 1, u} _).Additive
  ModuleSheafCohomology.extComparisonIso (stackModuleULift B S hS τ 𝒳)
    (Stacks.SheafOfModules.uliftUnit.{u + 1} _) (SheafOfModules.unit _)
    (fun I _ n e =>
      haveI : Injective ((stackModuleULift B S hS τ 𝒳).obj I) :=
        (preservesInjectiveObjects_stackModuleULift τ 𝒳).injective_obj ‹_›
      Ext.eq_zero_of_injective e)
    (NatIso.ofComponents (fun M =>
        (AddEquiv.mk (stackModuleULiftFullyFaithful B S hS τ 𝒳).homEquiv
          (fun _ _ => (stackModuleULift B S hS τ 𝒳).map_add)).toAddCommGrpIso)
      (fun {M N} g => by
        ext a
        exact (stackModuleULift B S hS τ 𝒳).map_comp a g)) i

/-- If `Ext^i(X, Y)` vanishes in one universe, it vanishes in any other. -/
private theorem isZero_extFunctorObj_of_isZero_chgUniv.{a, b, v, w'} {C : Type w'}
    [Category.{v} C] [Abelian C] [HasExt.{a} C] [HasExt.{b} C] (X Y : C) (i : ℕ)
    (h : IsZero ((extFunctorObj.{a} X i).obj Y)) : IsZero ((extFunctorObj.{b} X i).obj Y) :=
  have : Subsingleton (Ext.{a} X Y i) := AddCommGrpCat.subsingleton_of_isZero h
  have : Subsingleton (Ext.{b} X Y i) := Ext.chgUniv.{a, b}.subsingleton
  @AddCommGrpCat.isZero_of_subsingleton _ this

/-- **`Ext` out of the structure sheaf on the `τ`-site at `u` vanishes exactly when `Ext` out of
the lifted structure sheaf at `u + 1` of the lift does**, for `Ext`-groups at `u` in any universe
`t`: `AlgebraicGeometry.Stack.stackModuleCohomologyULiftIso` moved along
`CategoryTheory.Abelian.Ext.chgUniv`. -/
theorem isZero_ext_unit_iff_isZero_ext_uliftUnit (𝒳 : AlgebraicStacks.{u, w} B S hS)
    [HasExt.{t} (SheafOfModules.{u}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ))]
    (N : SheafOfModules.{u}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ))
    (i : ℕ) :
    IsZero ((extFunctorObj.{t} (SheafOfModules.unit _) i).obj N) ↔
      IsZero ((extFunctorObj.{u + 1} (Stacks.SheafOfModules.uliftUnit.{u + 1}
        (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ))
          i).obj ((stackModuleULift B S hS τ 𝒳).obj N)) := by
  let := enoughInjectives_moduleRingSheaf B S hS 𝒳 τ
  have : HasExt.{u + 1} (SheafOfModules.{u}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)) :=
    @hasExt_of_enoughInjectives.{u + 1} _ _ _ (locallySmall_self _) ‹_›
  exact Iff.trans ⟨isZero_extFunctorObj_of_isZero_chgUniv _ _ i,
    isZero_extFunctorObj_of_isZero_chgUniv _ _ i⟩
    ((stackModuleCohomologyULiftIso τ 𝒳 i).app N).isZero_iff

end SiteKind

end AlgebraicGeometry.Stack

end
