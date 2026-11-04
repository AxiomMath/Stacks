module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfModuleDerivedLowerShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleAffineChartReduction
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectStackMapSlicePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SchemeStackLowerShriekSheafFlatBaseChange

/-!
# Stacks 07B3 (2) on a flat affine chart

Let `H` be a module on the flat-fppf site of an algebraic stack `𝒳`, and let `y` be a flat object
over an affine scheme `U` with an arrow to an object over which `H` has a global presentation.
This file proves that the pullback of every `H^p(Lg_! H)` along `y : (Sch/U) → 𝒳` lies in
`LQCoh^fbc`: by Stacks 07AV it is `H^p(L(g')_! (f')^{-1} H)`
(`AlgebraicGeometry.Stack.FlatFppf.nonempty_modulePullback_homology_derivedModuleLowerShriek_iso`),
`(f')^{-1} H` has a global presentation, and over an affine scheme the statement is
`AlgebraicGeometry.Stack.FlatFppf.locallyQuasicoherentSheafFlatBaseChange_homology_schemeStack`.
This is the chart step of the proof of Stacks 07B3 (2), before Stacks 07AQ (2).

## Main results

* `isLocallyQuasicoherentWithSheafFlatBaseChange_modulePullback_iff_of_topology`: the class
  `LQCoh^fbc` of an inverse image of sheaves of modules, for any topology, read on the inverse
  image of presheaves of modules.
* The chart step, in the namespace `AlgebraicGeometry.Stack.FlatFppf`: the pullback of every
  `H^p(Lg_! H)` along `y : (Sch/U) → 𝒳` lies in `LQCoh^fbc`.

## References

* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
* [Stacks Project, Tag 07AV](https://stacks.math.columbia.edu/tag/07AV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedLowerShriek

universe u v w v' w'

namespace AlgebraicGeometry.Stack

section Transport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- **The class `LQCoh^fbc` of an inverse image does not depend on the topology nor on which of
two equal structure functors carries it.** For `f` with `f ⋙ q = p`, the inverse image of
Stacks 06WE of sheaves of modules for the topology `τ` lies in `LQCoh^fbc` exactly when the
inverse image of presheaves of modules of Stacks 06WD, the form in which Stacks 07AQ is stated,
does. -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_modulePullback_iff_of_topology
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) (hfq : (f ⋙ q).IsFiberedInGroupoids)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS q hq τ hτ)) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, u} B E h S hS p hp
      ((modulePullback.{u, v, w, u, v', w'} B S hS p q hp hq f hf τ hτ).obj M).val ↔
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, u} B E h S hS (f ⋙ q) hfq
      ((modulePresheafPullback.{u, v, w, v', w', u} B S hS q hq f hfq).obj M.val) := by
  subst hf
  rfl

end Transport

namespace FlatFppf

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology
  Stacks.hasSheafCompose_forget₂_commRingCat Stacks.essentiallySmall_over

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 07B3 (2) on a flat affine chart.** For a module `H` on the flat-fppf site of `𝒳`, a
flat object `y` over an affine scheme with an arrow to an object over which `H` has a global
presentation, and every `p`, the pullback of `H^p(Lg_! H)` along `y : (Sch/U) → 𝒳` lies in
`LQCoh^fbc`. -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_stackModulePresheafPullback_homology_derivedModuleLowerShriek
    (H : flatFppfModules B S hS 𝒳) (p : ℤ) (y V : FlatFppf B S hS 𝒳) (g : y ⟶ V)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y.obj)))
    (hV : (H.over V).HasGlobalPresentation) :
    letI := (SheafOfModules.instAbelian _ : Abelian (fppfModules B S hS 𝒳))
    letI := abelianFlatFppfModulesSpelling B S hS 𝒳
    letI := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, _, _, u} B E h S hS
      (CatFiberedInGroupoids.homFunctor (objectStackMap B S hS 𝒳 y.obj).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (objectStackMap B S hS 𝒳 y.obj).hom)
      ((stackModulePresheafPullback.{u, w, u} B S hS (objectStackMap B S hS 𝒳 y.obj)).obj
        ((DerivedCategory.homologyFunctor _ p).obj
          ((derivedModuleLowerShriek B S hS 𝒳).obj
            ((DerivedCategory.singleFunctor _ 0).obj H))).val) := by
  let := (SheafOfModules.instAbelian _ : Abelian (fppfModules B S hS 𝒳))
  let := abelianFlatFppfModulesSpelling B S hS 𝒳
  let := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
  let := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  let f := objectStackMap B S hS 𝒳 y.obj
  let U := 𝒳.val.val.p.obj y.obj
  let 𝒵 := schemeStack.{u, w} B S hS U
  have hpres : ((flatFppfModuleInverseImage f y.property).obj H).IsPresentedByGlobalSections := by
    have := isContinuous_subsiteFunctor_topology B S hS f y.property
    have := isCocontinuous_subsiteFunctor_topology B S hS f y.property
    have := hasSheafify_addCommGrpCat B S hS 𝒵
    have := wEqualsLocallyBijective_addCommGrpCat B S hS 𝒵
    have : EssentiallySmall.{u} (Over V) :=
      Stacks.Sites.ExtensionByZero.OfEssentiallySmall.essentiallySmall_over V
    have : HasSheafify ((topology B S hS 𝒳).over V) AddCommGrpCat.{u} :=
      hasSheafifyEssentiallySmallSite.{u, u, u + 1, u + 1, u} _ _
    have : ((topology B S hS 𝒳).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _
    exact Stacks.SheafOfModules.isPresentedByGlobalSections_pushforward_of_isTerminal _
      (isTerminalFlatObjectSchemeStackId.{u, w} B S hS U)
      (primedSiteFunctor B S hS f y.property) V
      (primedSiteFunctorTerminalHom B S hS 𝒳 y ≫ g)
      (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f y.property).symm) hV
  have hG := locallyQuasicoherentSheafFlatBaseChange_homology_schemeStack.{u, w} B E h S hS U hU
    ((flatFppfModuleInverseImage f y.property).obj H) hpres p
  obtain ⟨e⟩ := nonempty_modulePullback_homology_derivedModuleLowerShriek_iso f y.property H p
  let := hasSheafify_associatedTopology_algebraicStack B S hS 𝒵 .fppf
  let := wEqualsLocallyBijective_associatedTopology_algebraicStack B S hS 𝒵 .fppf
  have := ObjectProperty.isWeakSerreClass_of_abelian _
    ((SheafOfModules.instAbelian _ : Abelian (fppfModules B S hS 𝒵))) _
    (isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppfModules B E h S hS 𝒵)
  have hF := ObjectProperty.prop_of_iso
    (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒵) e.symm hG
  exact (isLocallyQuasicoherentWithSheafFlatBaseChange_modulePullback_iff_of_topology B S hS E h
    𝒵.val.val.p 𝒳.val.val.p 𝒵.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
    B.topology le_rfl f.hom.hom.toFunctor f.hom.hom.w _ _).1 hF

end FlatFppf

end AlgebraicGeometry.Stack

end
