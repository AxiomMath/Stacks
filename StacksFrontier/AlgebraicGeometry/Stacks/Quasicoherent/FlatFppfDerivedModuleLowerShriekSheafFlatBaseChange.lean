module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfAffineChartFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfDerivedModuleLowerShriekAffineChart
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFlatLocal
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07B3 (2): `H^p(Lg_! H)` lies in `LQCoh^fbc` for `H` quasi-coherent on the flat-fppf site

Let `𝒳` be an algebraic stack and `H` a quasi-coherent module on the flat-fppf site of `𝒳`. For
every `p`, the cohomology sheaf `H^p(Lg_! H)` of the derived lower shriek of Stacks 07AS (4) is a
locally quasi-coherent module with the flat base change property on `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.locallyQuasicoherentSheafFlatBaseChange_of_affine_presented`:
  a sheaf of modules on `𝒳_fppf` lies in `LQCoh^fbc` if its pullbacks to flat affine objects
  mapping to objects over which `H` is globally presented do.
* `FlatFppf.locallyQuasicoherentSheafFlatBaseChange_homology_derivedModuleLowerShriek` (in the
  namespace `AlgebraicGeometry.Stack`): **Stacks 07B3 (2)**, for `H` quasi-coherent on the
  flat-fppf site every `H^p(Lg_! H)` is locally quasi-coherent with the flat base change property.

## References

* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
* [Stacks Project, Tag 07AV](https://stacks.math.columbia.edu/tag/07AV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedLowerShriek

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology
  Stacks.hasSheafCompose_forget₂_commRingCat Stacks.essentiallySmall_over

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- Let `H` be a quasi-coherent module on the
flat-fppf site of `𝒳` and `F` a sheaf of modules on `𝒳_fppf`. If the pullback of `F` along
`y : (Sch/U) → 𝒳` lies in `LQCoh^fbc` for every flat object `y` over an affine scheme `U`
admitting an arrow to an object over which `H` has a global presentation, then `F` lies in
`LQCoh^fbc(𝒪_𝒳)`. -/
theorem locallyQuasicoherentSheafFlatBaseChange_of_affine_presented
    {R : Sheaf (topology B S hS 𝒳) RingCat.{u}} (H : SheafOfModules.{u} R)
    (hH : H.IsQuasicoherentOnSite) (F : fppfModules B S hS 𝒳)
    (hF : ∀ (y V : FlatFppf B S hS 𝒳) (_ : y ⟶ V),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y.obj)) →
      (H.over V).HasGlobalPresentation →
      IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, _, _, u} B E h S hS
        (CatFiberedInGroupoids.homFunctor (objectStackMap B S hS 𝒳 y.obj).hom ⋙ 𝒳.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS (objectStackMap B S hS 𝒳 y.obj).hom)
        ((stackModulePresheafPullback.{u, w, u} B S hS (objectStackMap B S hS 𝒳 y.obj)).obj
          F.val)) :
    lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳 F := by
  obtain ⟨x₀, hsm, hsurj⟩ := exists_smooth_surjective_objectMorphism _ _ _ 𝒳
  have hx₀ : flatObject B S hS 𝒳.val x₀ := flatObject_of_smoothObject B S hS 𝒳 hsm
  let J := {d : (y : FlatFppf B S hS 𝒳) × (V : FlatFppf B S hS 𝒳) × (y ⟶ V) × (y.obj ⟶ x₀) //
    IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj d.1.obj)) ∧
      (H.over d.2.1).HasGlobalPresentation ∧
      Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map d.2.2.2)) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map d.2.2.2))}
  refine locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_flatLfp_cover_of_atlas
    B E h S hS 𝒳 x₀ hsm hsurj (J := J) (fun j => j.1.1.obj) (fun j => j.1.2.2.2)
    (fun j => j.2.2.2.1) (fun j => j.2.2.2.2) (fun t => ?_) F
    (fun j => hF j.1.1 j.1.2.1 j.1.2.2.1 j.2.1 j.2.2.1)
  obtain ⟨y, V, a, g, haff, hpres, hflat, hlfp, s, hs⟩ :=
    exists_flat_lfp_affine_presented B S hS 𝒳 H hH x₀ hx₀ t
  exact ⟨⟨⟨y, V, a, g⟩, haff, hpres, hflat, hlfp⟩, s, hs⟩

/-- Let `H` be a quasi-coherent module on the flat-fppf site of an algebraic
stack `𝒳`. For every `p`, the cohomology sheaf `H^p(Lg_! H)` of the derived lower shriek of
Stacks 07AS (4) is a locally quasi-coherent module with the flat base change property on `𝒳`, the
flat base change property of Stacks 0762 being read with the pullback of sheaves. -/
@[stacks 07B3 "part (2): for a quasi-coherent module `H` (Stacks 03DL) on the flat-fppf site of \
an arbitrary algebraic stack and every `p`, `H^p(Lg_! H)` is a locally quasi-coherent module with \
the flat base change property, the class `LQCoh^fbc` of Stacks 0762 read with the pullback of \
sheaves, for the actual derived lower shriek `Lg_!` of Stacks 07AS (4) at the universe of the \
rings, with no hypothesis"]
theorem locallyQuasicoherentSheafFlatBaseChange_homology_derivedModuleLowerShriek
    (H : flatFppfModules B S hS 𝒳) (hH : H.IsQuasicoherentOnSite) (p : ℤ) :
    letI := (SheafOfModules.instAbelian _ : Abelian (fppfModules B S hS 𝒳))
    letI := abelianFlatFppfModulesSpelling B S hS 𝒳
    letI := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳
      ((DerivedCategory.homologyFunctor _ p).obj
        ((derivedModuleLowerShriek B S hS 𝒳).obj ((DerivedCategory.singleFunctor _ 0).obj H))) :=
  locallyQuasicoherentSheafFlatBaseChange_of_affine_presented B E h S hS 𝒳 H hH _
    (fun y V g hU hV =>
      isLocallyQuasicoherentWithSheafFlatBaseChange_stackModulePresheafPullback_homology_derivedModuleLowerShriek
        B E h S hS 𝒳 H p y V g hU hV)

end AlgebraicGeometry.Stack.FlatFppf

end
