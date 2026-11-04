module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeRingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteSmallEtale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology
public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# Cohomology on the slices of the locally-finite-type étale site

Let `S` be a scheme and `C` the site of schemes locally of finite type over `S` with the étale
topology (in its single-universe model `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.Lifted`).
For an object `V` of `C` and an object `U = (V' ⟶ V)` of the slice `C/V`, the iterated slice
`(C/V)/U` contains the small étale site of the scheme underlying `V'`: a scheme étale over `V'`
is locally of finite type over `S`. Restriction along that inclusion does not change global
cohomology: for every abelian sheaf `G` on `(C/V)/U`,

`H^p((C/V)/U, G) ≅ H^p(V'_ét, G|_{V'_ét})`.

This is the comparison of the big and the small étale site (Stacks 03YU, 0757, 0758) for the
subcategory `C` of the big étale site.

## Main definitions

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.sliceSmallEtaleFunctor`: the inclusion of
  `V'_ét` in `(C/V)/U`.

## Main results

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.subsingleton_sheafH_of_sliceSmallEtale`:
  vanishing of `H^p(V'_ét, G|_{V'_ét})` gives vanishing of `H^p((C/V)/U, G)`.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 0757](https://stacks.math.columbia.edu/tag/0757)
* [Stacks Project, Tag 0758](https://stacks.math.columbia.edu/tag/0758)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

variable {S : Scheme.{u}} {V : Lifted S} (U : Over V)

/-- The object of the (unlifted) site underlying the source of `U`. -/
abbrev memberObj : LocallyFiniteTypeEtale S := (liftedEquiv S).inverse.obj U.left

/-- The localized topology on the iterated slice `(C/V)/U`. -/
abbrev sliceTopology : GrothendieckTopology (Over U) := ((liftedTopology S).over V).over U

/-- The slice `C/V'` of the site, read in the lifted model as the slice over the source `V'`
of `U`. -/
def liftSliceFunctor : Over (memberObj U) ⥤ Over U.left :=
  (Over.postEquiv (X := memberObj U) (liftedEquiv S)).functor

/-- The functor `liftSliceFunctor U` is an equivalence of categories. -/
instance : (liftSliceFunctor U).IsEquivalence :=
  inferInstanceAs (Over.postEquiv (X := memberObj U) (liftedEquiv S)).functor.IsEquivalence

/-- The functor `liftSliceFunctor U` is continuous for the localized étale topologies. -/
instance : (liftSliceFunctor U).IsContinuous
    ((topology S).over (memberObj U)) ((liftedTopology S).over U.left) :=
  Functor.isContinuous_overPost _ _ _ _

/-- The functor `liftSliceFunctor U` is cocontinuous for the localized étale topologies. -/
instance : (liftSliceFunctor U).IsCocontinuous
    ((topology S).over (memberObj U)) ((liftedTopology S).over U.left) :=
  inferInstanceAs ((Over.post (X := memberObj U) (liftedEquiv S).functor).IsCocontinuous
    ((topology S).over (memberObj U)) ((liftedTopology S).over _))

/-- **The small étale site of the scheme underlying `U` inside the iterated slice `(C/V)/U`.** -/
def sliceSmallEtaleFunctor : (memberObj U).obj.left.Etale ⥤ Over U :=
  smallEtaleFunctor (memberObj U) ⋙ liftSliceFunctor U ⋙ U.iteratedSliceEquiv.inverse

/-- The functor `sliceSmallEtaleFunctor U` is continuous from the small étale topology to the
localized topology on `(C/V)/U`. -/
instance sliceSmallEtaleFunctor_isContinuous :
    (sliceSmallEtaleFunctor U).IsContinuous (memberObj U).obj.left.smallEtaleTopology
      (sliceTopology U) :=
  have : (liftSliceFunctor U ⋙ U.iteratedSliceEquiv.inverse).IsContinuous
      ((topology S).over (memberObj U)) (sliceTopology U) :=
    Functor.isContinuous_comp _ _ _ ((liftedTopology S).over U.left) _
  Functor.isContinuous_comp _ _ _ ((topology S).over (memberObj U)) _

/-- The functor `sliceSmallEtaleFunctor U` is cocontinuous from the small étale topology to the
localized topology on `(C/V)/U`. -/
instance sliceSmallEtaleFunctor_isCocontinuous :
    (sliceSmallEtaleFunctor U).IsCocontinuous (memberObj U).obj.left.smallEtaleTopology
      (sliceTopology U) :=
  have : (liftSliceFunctor U ⋙ U.iteratedSliceEquiv.inverse).IsCocontinuous
      ((topology S).over (memberObj U)) (sliceTopology U) :=
    isCocontinuous_comp _ _ _ ((liftedTopology S).over U.left)
  isCocontinuous_comp _ _ _ ((topology S).over (memberObj U))

/-- The functor `sliceSmallEtaleFunctor U` preserves pullbacks. -/
instance : PreservesLimitsOfShape WalkingCospan (sliceSmallEtaleFunctor U) := by
  dsimp only [sliceSmallEtaleFunctor]
  infer_instance

/-- The functor `sliceSmallEtaleFunctor U` preserves equalizers. -/
instance : PreservesLimitsOfShape WalkingParallelPair (sliceSmallEtaleFunctor U) := by
  dsimp only [sliceSmallEtaleFunctor]
  infer_instance

/-- The image of the terminal object of the small étale site is terminal in `(C/V)/U`. -/
def isTerminalSliceSmallEtaleFunctorObj :
    IsTerminal ((sliceSmallEtaleFunctor U).obj (smallEtaleTerminal (memberObj U))) :=
  (((isTerminalSmallEtaleFunctorObj (memberObj U)).isTerminalObj
    (liftSliceFunctor U)).isTerminalObj U.iteratedSliceEquiv.inverse :)

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- Abelian presheaves on `(C/V)/U` admit sheafification for the localized topology. -/
instance : HasSheafify (sliceTopology U) AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u + 1, u + 1}

/-- **Global cohomology on the iterated slice `(C/V)/U` vanishes when that of the restriction to
the small étale site of the scheme underlying `U` does.** -/
theorem subsingleton_sheafH_of_sliceSmallEtale
    (G : Sheaf (sliceTopology U) AddCommGrpCat.{u + 1}) (p : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1} (((sliceSmallEtaleFunctor U).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (memberObj U).obj.left.smallEtaleTopology
        (sliceTopology U)).obj G) p)) :
    Subsingleton (Sheaf.H.{u + 1} G p) := by
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf (memberObj U).obj.left.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.Cohomology.SiteConstantSheaf.isGrothendieckAbelian_smallEtaleAbelianSheaf _
  have : ∀ P : ((memberObj U).obj.left.Etale)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (sliceSmallEtaleFunctor U).op.HasPointwiseRightKanExtension P := fun _ ↦ inferInstance
  have : PreservesFiniteColimits ((sliceSmallEtaleFunctor U).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (memberObj U).obj.left.smallEtaleTopology (sliceTopology U)) :=
    Stacks.Cohomology.BiggerSite.preservesFiniteColimits_sheafPushforwardContinuous
      (memberObj U).obj.left.smallEtaleTopology (sliceTopology U) _ _
  have : ((sliceSmallEtaleFunctor U).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (memberObj U).obj.left.smallEtaleTopology
        (sliceTopology U)).PreservesInjectiveObjects :=
    Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous.{u + 1}
      (memberObj U).obj.left.smallEtaleTopology (sliceTopology U) _
  exact (Stacks.Cohomology.BiggerSite.sheafHAddEquiv.{u + 1}
    (memberObj U).obj.left.smallEtaleTopology (sliceTopology U) (sliceSmallEtaleFunctor U)
    (Stacks.Cohomology.SiteConstantSheaf.smallEtaleTerminalObjIsTerminal _)
    (isTerminalSliceSmallEtaleFunctorObj U) rfl G p).toEquiv.subsingleton

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

end
