module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClassifyingStackHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence.ModuleCech
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.SmoothCoveringSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Equalizers

/-!
# The relative Čech resolution along the atlas of a classifying stack

Let `G` be a smooth group algebraic space over the final algebraic space of the big fppf site of a
scheme `S`, let `BG = [S/G]` be its classifying stack and `π : S ⟶ BG` its atlas
(`AlgebraicGeometry.Stack.classifyingAtlas`). This file specialises the relative Čech complex of
sheaves of modules (`Stacks.RelativeCech.cechModuleComplexFunctor`) to `π`, at module universe
`u + 1`, and records the two facts about it that hold because `π` is representable by algebraic
spaces, surjective, flat and locally of finite presentation: its augmentation is a
quasi-isomorphism, and its terms at an injective module are injective.

## Main definitions

* `AlgebraicGeometry.Stack.classifyingCechComplex`: the relative Čech complex of `π`, as a
  functor of the module.
* `AlgebraicGeometry.Stack.classifyingCechAugmentation`: its augmentation.

## Main results

* `AlgebraicGeometry.Stack.quasiIso_classifyingCechAugmentation_app`.
* `AlgebraicGeometry.Stack.injective_classifyingCechComplex_obj_X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  (G : Space.GroupAlgebraicSpace C S hS (Space.terminalSpace C S hS).obj
    (Space.terminalSpace C S hS).property)
  (hG : Space.IsSmooth C S hS G.obj.X.hom)

/-- The source of the atlas of a classifying stack: the base `S`, as an algebraic stack. -/
abbrev classifyingAtlasSource : AlgebraicStacks.{u, w} C S hS :=
  algebraicSpaceStack.{u, w} C S hS (Space.terminalSpace C S hS).obj
    (Space.terminalSpace C S hS).property

/-- The underlying functor of the atlas `π : S ⟶ BG`. -/
abbrev classifyingAtlasFunctor :
    (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.val.obj ⥤
      (classifyingAlgebraicStack.{u, w} G hG).val.val.obj :=
  CatFiberedInGroupoids.homFunctor (classifyingAtlas.{u, w} G hG).hom

/-- The atlas is a `1`-morphism of categories fibred in groupoids. -/
theorem isFibredOneMorphism_classifyingAtlasFunctor :
    (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.val.p.IsFibredOneMorphism
      (classifyingAlgebraicStack.{u, w} G hG).val.val.p
      (classifyingAtlasFunctor.{u, w} G hG) :=
  Functor.isFibredOneMorphism_of_isFiberedInGroupoids
    (classifyingAlgebraicStack.{u, w} G hG).val.isFiberedInGroupoids
    (classifyingAtlas.{u, w} G hG).hom.hom.w

/-- The atlas is faithful, being representable by algebraic spaces. -/
instance faithful_classifyingAtlasFunctor :
    (classifyingAtlasFunctor.{u, w} G hG).Faithful :=
  AlgebraicStacks.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces C S hS _
    (classifyingAtlas_fppf.{u, w} G hG).1

/-- **The image of the atlas covers `BG`** for the fppf topology, by single morphisms. -/
theorem classifyingAtlas_cover (x : (classifyingAlgebraicStack.{u, w} G hG).val.val.obj) :
    ∃ R : Presieve x,
      Sieve.generate R ∈ BigFppfOver.associatedTopology C S hS
        (classifyingAlgebraicStack.{u, w} G hG).val.val.p .fppf x ∧
      ∀ ⦃y⦄ (k : y ⟶ x), R k → ∃ z, Nonempty (y ≅ (classifyingAtlasFunctor.{u, w} G hG).obj z) := by
  obtain ⟨-, hsurj, hflat, hlfp⟩ := classifyingAtlas_fppf.{u, w} G hG
  obtain ⟨z, α, hα⟩ := AlgebraicStacks.exists_fppfLocalLift_singleton C S hS
    (classifyingAtlas.{u, w} G hG) hsurj hflat hlfp x
  refine ⟨Presieve.singleton α, hα, ?_⟩
  rintro y k ⟨⟩
  exact ⟨z, ⟨Iso.refl _⟩⟩

/-- **The relative Čech complex along the atlas of `BG`**, as a functor of the fppf module, at
module universe `u + 1`. -/
abbrev classifyingCechComplex :
    fppfModulesUnivLE.{u, w, u + 1} C S hS (classifyingAlgebraicStack.{u, w} G hG) ⥤
      CochainComplex
        (fppfModulesUnivLE.{u, w, u + 1} C S hS (classifyingAlgebraicStack.{u, w} G hG)) ℕ :=
  Stacks.RelativeCech.cechModuleComplexFunctor.{u, u + 1, u + 1, u, u, u} C S hS
    (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.val.p
    (classifyingAlgebraicStack.{u, w} G hG).val.val.p (classifyingAtlasFunctor.{u, w} G hG) .fppf
    (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.isFiberedInGroupoids
    (classifyingAlgebraicStack.{u, w} G hG).val.isFiberedInGroupoids
    (isFibredOneMorphism_classifyingAtlasFunctor.{u, w} G hG)

/-- The relative Čech complex along the atlas of `BG` is an additive functor. -/
instance additive_classifyingCechComplex : (classifyingCechComplex.{u, w} G hG).Additive :=
  Stacks.RelativeCech.cechModuleComplexFunctor_additive.{u, u + 1, u + 1, u, u, u} C S hS _ _ _
    .fppf _ _ (isFibredOneMorphism_classifyingAtlasFunctor.{u, w} G hG)

/-- The augmentation of a module into its relative Čech complex along the atlas of `BG`. -/
abbrev classifyingCechAugmentation :
    CochainComplex.single₀
        (fppfModulesUnivLE.{u, w, u + 1} C S hS (classifyingAlgebraicStack.{u, w} G hG)) ⟶
      classifyingCechComplex.{u, w} G hG :=
  Stacks.RelativeCech.cechModuleAugmentationNatTrans.{u, u + 1, u + 1, u, u, u} C S hS
    (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.val.p
    (classifyingAlgebraicStack.{u, w} G hG).val.val.p (classifyingAtlasFunctor.{u, w} G hG) .fppf
    (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.isFiberedInGroupoids
    (classifyingAlgebraicStack.{u, w} G hG).val.isFiberedInGroupoids
    (isFibredOneMorphism_classifyingAtlasFunctor.{u, w} G hG)

/-- **The relative Čech complex along the atlas of `BG` is a resolution** (Stacks 06XE): its
augmentation is a quasi-isomorphism at every module. -/
theorem quasiIso_classifyingCechAugmentation_app
    (𝓕 : fppfModulesUnivLE.{u, w, u + 1} C S hS (classifyingAlgebraicStack.{u, w} G hG)) :
    QuasiIso ((classifyingCechAugmentation.{u, w} G hG).app 𝓕) :=
  Stacks.RelativeCech.quasiIso_cechModuleAugmentationNatTrans_app.{u, u + 1, u + 1, u, u, u}
    C S hS
    (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.val.p
    (classifyingAlgebraicStack.{u, w} G hG).val.val.p (classifyingAtlasFunctor.{u, w} G hG) .fppf
    (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.isFiberedInGroupoids
    (classifyingAlgebraicStack.{u, w} G hG).val.isFiberedInGroupoids
    (isFibredOneMorphism_classifyingAtlasFunctor.{u, w} G hG)
    (classifyingAtlas_cover.{u, w} G hG) 𝓕

/-- The terms of the relative Čech complex along the atlas of `BG` of an injective module are
injective. -/
theorem injective_classifyingCechComplex_obj_X
    (𝓘 : fppfModulesUnivLE.{u, w, u + 1} C S hS (classifyingAlgebraicStack.{u, w} G hG))
    [Injective 𝓘] (n : ℕ) :
    Injective (((classifyingCechComplex.{u, w} G hG).obj 𝓘).X n) :=
  haveI : HasEqualizers (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.val.obj :=
    AlgebraicStacks.hasEqualizers (B := C) (S := S) (hS := hS) _
  haveI : Injective (show SheafOfModules.{u + 1} (Stacks.RelativeCech.moduleRingSheaf C S hS
      (classifyingAlgebraicStack.{u, w} G hG).val.val.p
      (classifyingAlgebraicStack.{u, w} G hG).val.isFiberedInGroupoids .fppf) from 𝓘) :=
    ‹Injective 𝓘›
  Stacks.RelativeCech.injective_cechModuleTerm.{u, u + 1, u + 1, u, u, u}
    C S hS
    (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.val.p
    (classifyingAlgebraicStack.{u, w} G hG).val.val.p (classifyingAtlasFunctor.{u, w} G hG) .fppf
    (classifyingAtlasSource.{u, w} (C := C) (S := S) (hS := hS)).val.isFiberedInGroupoids
    (classifyingAlgebraicStack.{u, w} G hG).val.isFiberedInGroupoids
    (isFibredOneMorphism_classifyingAtlasFunctor.{u, w} G hG)
    (fun _ => PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE.{u + 1} _)
    𝓘 n

end AlgebraicGeometry.Stack

end
