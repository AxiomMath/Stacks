module

public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleModuleDerivedLowerShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleAffineChartReduction
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectStackMapSlicePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SchemeStackLowerShriekSheafFlatBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07B3 (1): `H^p(Lg_! H)` lies in `LQCoh^fbc` for `H` quasi-coherent on the lisse-étale site

Let `𝒳` be an algebraic stack and `H` a quasi-coherent module on the lisse-étale site of `𝒳`. For
every `p`, the cohomology sheaf `H^p(Lg_! H)` of the derived lower shriek `Lg_!` is a locally
quasi-coherent module with the flat base change property on `𝒳`.

## Main results

* `isLocallyQuasicoherentWithSheafFlatBaseChange_homology_derivedModuleLowerShriek` (in the
  namespace `AlgebraicGeometry.Stack.LisseEtale`): **Stacks 07B3 (1)**, for `H` quasi-coherent on
  the lisse-étale site every `H^p(Lg_! H)` lies in `LQCoh^fbc`.

## References

* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
* [Stacks Project, Tag 07AV](https://stacks.math.columbia.edu/tag/07AV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedLowerShriek

namespace AlgebraicGeometry.Stack.LisseEtale

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'
  Stacks.hasSheafCompose_forget₂_commRingCat Stacks.essentiallySmall_over

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- Let `H` be a quasi-coherent module on the lisse-étale site of an algebraic stack `𝒳`. For
every `p`, the cohomology sheaf `H^p(Lg_! H)` of the derived lower shriek `Lg_!` is a locally
quasi-coherent module with the flat base change property on `𝒳`, the flat base change property
being read with the pullback of sheaves. -/
@[stacks 07B3 "part (1): for a quasi-coherent module `H` (Stacks 03DL) on the lisse-étale site of \
an arbitrary algebraic stack and every `p`, `H^p(Lg_! H)` is a locally quasi-coherent module with \
the flat base change property, the class `LQCoh^fbc` of Stacks 0762 read with the pullback of \
sheaves, for the actual derived lower shriek `Lg_!` of Stacks 07AS (2) at the universe of the \
rings, with no hypothesis"]
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_homology_derivedModuleLowerShriek
    (H : SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒳)) (hH : H.IsQuasicoherentOnSite)
    (p : ℤ) :
    letI := abelianEtaleModules B S hS 𝒳
    letI := abelianLisseEtaleModules B S hS 𝒳
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (lisseEtaleModuleRing B S hS 𝒳))
    letI := HasDerivedCategory.standard (SheafOfModules.{u}
      (SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O))
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      ((DerivedCategory.homologyFunctor _ p).obj
        ((derivedModuleLowerShriek B S hS 𝒳).obj
          ((DerivedCategory.singleFunctor _ 0).obj H))).val := by
  refine isLocallyQuasicoherentWithSheafFlatBaseChange_of_affine_presented B S hS E h 𝒳 H hH _
    (fun y V g hU hV => ?_)
  let f := objectStackMap B S hS 𝒳 y.obj
  let U := 𝒳.val.val.p.obj y.obj
  let 𝒵 := schemeStack.{u, w} B S hS U
  have hpres : ((lisseEtaleModuleInverseImage f y.property).obj H).IsPresentedByGlobalSections := by
    have := isContinuous_subsiteFunctor.{u, w} B S hS f y.property
    have := isCocontinuous_subsiteFunctor.{u, w} B S hS f y.property
    have := hasSheafify_inclusionTopology B S hS 𝒵
    have := wEqualsLocallyBijective_inclusionTopology B S hS 𝒵
    have : EssentiallySmall.{u} (Over V) :=
      Stacks.Sites.ExtensionByZero.OfEssentiallySmall.essentiallySmall_over V
    have : HasSheafify ((inclusionTopology.{u, w} B S hS 𝒳).over V) AddCommGrpCat.{u} :=
      hasSheafifyEssentiallySmallSite.{u, u, u + 1, u + 1, u} _ _
    have : ((inclusionTopology.{u, w} B S hS 𝒳).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
      GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _
    have := isIso_lisseEtaleModuleRingInverseImageHom f y.property
    exact Stacks.SheafOfModules.isPresentedByGlobalSections_pushforward_of_isTerminal _
      (isTerminalSmoothObjectSchemeStackId.{u, w} B S hS U)
      (primedSiteFunctor.{u, w} B S hS f y.property) V
      (primedSiteFunctorTerminalHom B S hS 𝒳 y ≫ g)
      (lisseEtaleModuleRingInverseImageHom f y.property) hV
  have hG := locallyQuasicoherentSheafFlatBaseChange_homology_schemeStack.{u, w} B E h S hS U hU
    ((lisseEtaleModuleInverseImage f y.property).obj H) hpres p
  obtain ⟨e⟩ := nonempty_modulePullback_homology_derivedModuleLowerShriek_iso f y.property H p
  have := hasSheafify_etaleAssociatedTopology B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids
  have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS 𝒵.val.val.p
    𝒵.val.isFiberedInGroupoids
  have : @ObjectProperty.IsWeakSerreClass (SheafOfModules.{u}
      (SmallModel.targetRing (associatedTopology B S hS 𝒵.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O)) _
      (abelianEtaleModules B S hS 𝒵)
      (fun F => IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u} B E h S hS
        𝒵.val.val.p 𝒵.val.isFiberedInGroupoids F.val) :=
    ObjectProperty.isWeakSerreClass_of_abelian _ _ _
      (isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChange B E h S hS
        𝒵.val.val.p 𝒵.val.isFiberedInGroupoids)
  have hF := ObjectProperty.prop_of_iso
    (fun F : SheafOfModules.{u}
      (SmallModel.targetRing (associatedTopology B S hS 𝒵.val.val.p (etaleTopology B))
        (associatedRingedTopos B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids (etaleTopology B)
          (etaleTopology_le_topology B)).O) =>
      IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, u + 1, u, u} B E h S hS
        𝒵.val.val.p 𝒵.val.isFiberedInGroupoids F.val) e.symm hG
  exact (isLocallyQuasicoherentWithSheafFlatBaseChange_modulePullback_iff B S hS E h
    𝒵.val.val.p 𝒳.val.val.p 𝒵.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
    f.hom.hom.toFunctor f.hom.hom.w _ _).1 hF

end AlgebraicGeometry.Stack.LisseEtale

end
