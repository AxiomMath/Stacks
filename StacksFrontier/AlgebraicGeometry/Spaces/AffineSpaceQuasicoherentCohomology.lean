module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceModuleCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicRepresentableComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardInjectiveAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsAndPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.LerayCollapse

/-!
# Cohomology of quasi-coherent modules on an affine algebraic space, and along affine morphisms

Let `S` be a scheme contained in a big fppf site `B`. Cohomology of an `𝒪_X`-module on an
algebraic space `X` over `S` is the right derived functor of global sections on the small étale
ringed site of `X`, at the module universe of the structure rings.

* `H^p(W, 𝓙) = 0` for `p > 0`, for a quasi-coherent `𝒪_W`-module `𝓙` on an affine algebraic
  space `W`: the representing affine scheme, read as an étale chart, is a final object of the
  small étale site, so global sections are the sections over it, whose higher derived functors
  vanish on quasi-coherent modules
  (`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`).
* For a morphism `g : W ⟶ X`, the derived functors of `Γ(X, g_* −)` and of `Γ(W, −)` vanish at
  the same modules: `Γ(X, g_* −)` is `Γ(W, −)` with scalars restricted
  (`Stacks.Cohomology.SiteModules.globalSectionsPushforwardIso`, for the morphism of small étale
  ringed topoi of Stacks 03G8 and its inverse image).
* Hence, for an affine morphism `g : W ⟶ X` from an affine algebraic space and a quasi-coherent
  `𝓙` on `W`, `H^p(X, g_*𝓙) = 0` for `p > 0`: the collapse of Stacks 0D2U
  (`AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHomOfIsQuasicoherent`) identifies it
  with the `p`-th derived functor of `Γ(X, g_* −)` at `𝓙`.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_globalSections_of_isAffineSpace`
* `AlgebraicGeometry.Space.isZero_rightDerived_comp_modulePushforward_iff`
* `AlgebraicGeometry.Space.isZero_rightDerived_globalSections_modulePushforward_of_isAffineHom`
* `AlgebraicGeometry.Space.isAffineSpace_of_isAffineHom_of_algebraicSpaces` — an algebraic space
  affine over an affine algebraic space is affine, which supplies the affineness of `W` in the
  third item above whenever `X` is affine.

## References

* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Global sections over a final chart -/

section FinalChart

variable {X : AlgebraicSpaces B S hS} {c : SmallEtale B S hS X.1} (hc : IsTerminal c)

/-- Global sections of an `𝒪_X`-module, read in abelian groups, are its sections over a final
chart, lifted to the universe of the global sections. -/
def globalSectionsForgetIsoEvaluation :
    globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) ⋙
      forget₂ _ AddCommGrpCat.{u + 1} ≅
    SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
        (op c) ⋙ forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op c))) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  NatIso.ofComponents
    (fun M => AddEquiv.toAddCommGrpIso
      { (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M hc).trans
          Equiv.ulift.symm with
        map_add' := fun _ _ => rfl })
    (fun _ => rfl)

include hc in
/-- **On an algebraic space with a final étale chart `c` whose scheme is affine, the higher
cohomology of a quasi-coherent `𝒪_X`-module vanishes.**  Global sections are the sections over
`c` (`AlgebraicGeometry.Space.globalSectionsForgetIsoEvaluation`), whose higher derived functors
vanish on quasi-coherent modules over an affine chart. -/
theorem isZero_rightDerived_globalSections_of_isTerminal (hca : IsAffineChart B S hS X.1 c)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (p : ℕ) (hp : 0 < p) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O))).rightDerived p).obj M) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have h := isZero_rightDerived_evaluation_of_isAffineChart B S hS X.1 X.2 M hM c hca p hp
  have hu : (AddCommGrpCat.uliftFunctor.{u + 1, u}).PreservesHomology := inferInstance
  have hfu : (forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op c))) AddCommGrpCat.{u} ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u}).PreservesHomology := inferInstance
  have e₁ := (Functor.rightDerivedCompIso (globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
    (forget₂ (ModuleCat.{u + 1} (RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj))
      AddCommGrpCat.{u + 1}) p).app M
  have e₂ := (Functor.rightDerivedIsoOfNatIso
    (globalSectionsForgetIsoEvaluation B S hS hc) p).app M
  have e₃ := (Functor.rightDerivedCompIso (SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
      (op c)) (forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op c))) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}) p).app M
  have hz : IsZero ((forget₂ (ModuleCat.{u + 1} (RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj))
      AddCommGrpCat.{u + 1}).obj
      (((globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O))).rightDerived p).obj M)) :=
    ((Functor.map_isZero (forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op c))) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}) h).of_iso e₃).of_iso (e₁.symm ≪≫ e₂)
  rw [AddCommGrpCat.isZero_iff_subsingleton] at hz
  exact ModuleCat.isZero_iff_subsingleton.2 hz

end FinalChart

/-! ### Global sections along a direct image -/

variable {B S hS}

/-- Restricting scalars after an additive functor does not change where its right derived
functors vanish: restriction of scalars is exact and does not change the underlying group. -/
theorem isZero_rightDerived_comp_restrictScalars_iff {A : Type*} [Category* A] [Abelian A]
    [HasInjectiveResolutions A] {R R' : Type*} [Ring R] [Ring R'] (F : A ⥤ ModuleCat.{v} R)
    (hF : F.Additive) (φ : R' →+* R) (p : ℕ) (M : A) :
    IsZero (((F ⋙ ModuleCat.restrictScalars.{v} φ).rightDerived p).obj M) ↔
      IsZero ((F.rightDerived p).obj M) := by
  have := hF
  have : (ModuleCat.restrictScalars.{v} φ).PreservesHomology :=
    ((Functor.exact_tfae (ModuleCat.restrictScalars.{v} φ)).out 2 3).mp fun T hT ↦ by
      rwa [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
  rw [((Functor.rightDerivedCompIso F (ModuleCat.restrictScalars.{v} φ) p).app M).isZero_iff,
    ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  rfl

/-- **Global sections are unchanged by a direct image, at the level of derived functors.**  For
a morphism `g : W ⟶ X` of algebraic spaces and an `𝒪_W`-module `𝓜`, the `p`-th derived functor
of `Γ(X, g_* −)` vanishes at `𝓜` exactly when `H^p(W, 𝓜)` does.

`Γ(X, g_* −)` is `Γ(W, −)` followed by restriction of scalars along `Γ(X, 𝒪_X) ⟶ Γ(W, 𝒪_W)`
(`Stacks.Cohomology.SiteModules.globalSectionsPushforwardIso`, transported along
`AlgebraicGeometry.Space.modulePushforwardIso`), and restriction of scalars is exact and does
not change the underlying group. -/
theorem isZero_rightDerived_comp_modulePushforward_iff {W X : AlgebraicSpaces B S hS}
    (g : W ⟶ X) (M : Modules.{u, u} B S hS W.1 W.2) (p : ℕ) :
    have := hasInjectiveResolutions_modules B S hS W.1 W.2
    (IsZero (((modulePushforward B S hS g ⋙ globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O))).rightDerived p).obj M) ↔
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS W.1 W.2).O))).rightDerived p).obj M)) := by
  have := hasInjectiveResolutions_modules B S hS W.1 W.2
  have e := Functor.isoWhiskerRight (modulePushforwardIso B S hS g).symm
      (globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) ≪≫
    globalSectionsPushforwardIso (smallEtaleRingedToposModulesHom B S hS g)
  have := Functor.additive_of_iso e
  have e' := (Functor.rightDerivedIsoOfNatIso e p).app M
  exact e'.isZero_iff.trans (isZero_rightDerived_comp_restrictScalars_iff _
    (globalSectionsFunctor_additive _) _ p M)

/-- **The higher cohomology of the direct image of a quasi-coherent module along an affine
morphism from an affine algebraic space vanishes.**  Let `g : W ⟶ X` be an affine morphism of
algebraic spaces over `S` with `W` affine, and `𝓙` a quasi-coherent `𝒪_W`-module.  Then
`H^p(X, g_*𝓙) = 0` for `p > 0`.

The collapse of Stacks 0D2U identifies `H^p(X, g_*𝓙)` with the `p`-th derived functor of
`Γ(X, g_* −)` at `𝓙`, which vanishes with `H^p(W, 𝓙)` by
`AlgebraicGeometry.Space.isZero_rightDerived_comp_modulePushforward_iff`; and the latter is zero
because `W` is affine. -/
theorem isZero_rightDerived_globalSections_modulePushforward_of_isAffineHom
    {W X : AlgebraicSpaces B S hS} (g : W ⟶ X) (hg : IsAffineHom B S hS g.hom)
    (hW : IsAffineSpace B S hS W.1) (J : Modules.{u, u} B S hS W.1 W.2)
    (hJ : J.IsQuasicoherentOnSite) (p : ℕ) (hp : 0 < p) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O))).rightDerived p).obj
        ((modulePushforward B S hS g).obj J)) := by
  have := hasInjectiveResolutions_modules B S hS W.1 W.2
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  exact ((isZero_rightDerived_comp_modulePushforward_iff g J p).2
    (isZero_rightDerived_globalSections_of_isAffineSpace B S hS W hW J hJ p hp)).of_iso
      (cohomologyCollapseIsoOfIsAffineHomOfIsQuasicoherent B S hS g hg J hJ p).symm

/-- **An algebraic space affine over an affine algebraic space is affine.** -/
theorem isAffineSpace_of_isAffineHom_of_algebraicSpaces {W X : AlgebraicSpaces B S hS}
    (g : W ⟶ X) (hg : IsAffineHom B S hS g.hom) (hX : IsAffineSpace B S hS X.1) :
    IsAffineSpace B S hS W.1 := by
  obtain ⟨T, hT, ⟨i⟩⟩ := hX
  obtain ⟨V, p, q, hpb⟩ := hg ⟨T, hT⟩ i.inv
  have : IsIso p := hpb.isIso_fst_of_isIso
  exact ⟨(BigAffineFppf.inclusion B S hS).obj V, V.2, ⟨(asIso p).symm⟩⟩

end AlgebraicGeometry.Space

end
