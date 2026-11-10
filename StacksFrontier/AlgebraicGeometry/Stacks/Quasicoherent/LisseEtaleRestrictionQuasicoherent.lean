module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleDerivedModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteLocalFactorizations

/-!
# The restriction of `LQCoh^fbc` to the lisse-étale site is quasi-coherent (Stacks 07B1 (1)(b))

Let `𝒳` be an algebraic stack and `F` a module on its étale site lying in `LQCoh^fbc(𝒪_𝒳)`, with
the flat base change property of **Stacks 0762** read with the pullback of sheaves.  This file
proves **Stacks 07B1** (1)(b): the restriction `g^{-1}F` of `F` to the lisse-étale site is a
quasi-coherent module on that ringed site.  The argument is the one of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatFppfRestrictionQuasicoherent.lean` for
the flat-fppf site, read for the étale topology: smooth objects are flat, so the comparison map of
Stacks 06WC is invertible along every arrow of the lisse-étale site, and the localization at a
smooth object `y` is the restriction of the associated module `𝓕^a` on the big étale site of the
scheme below `y`, which is quasi-coherent (Stacks 03DV).

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.isQuasicoherentOnSite_moduleRestriction`: **Stacks 07B1**
  (1)(b).

## References

* [Stacks Project, Tag 07B1](https://stacks.math.columbia.edu/tag/07B1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedLowerShriek

universe u w

namespace AlgebraicGeometry.Stack.LisseEtale

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The structure sheaf of the étale site of an algebraic stack, as a sheaf of rings. -/
abbrev lisseAmbientRing :
    Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) RingCat.{u} :=
  SmallModel.targetRing (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (associatedRingedTopos B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
      (etaleTopology_le_topology B)).O

/-- Restriction of sheaves of modules from the étale site of an algebraic stack to its
lisse-étale site, over the restricted structure sheaf: `g^{-1}` of Stacks 0788 (1). -/
abbrev lisseRestriction :=
  restrictionModules.{u}
    (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
    (lisseAmbientRing B S hS 𝒳)

/-- The functor from the lisse-étale site of an algebraic stack to the big site of schemes
sending a smooth object to the scheme below it. -/
abbrev baseFunctor : LisseEtale.{u, w} B S hS 𝒳 ⥤ B.Schemes :=
  (smoothObject.{u, w} B S hS 𝒳).ι ⋙ 𝒳.val.val.p ⋙ Over.forget (B.obj hS)

/-- The functor to schemes is continuous for the lisse-étale and the étale topologies. -/
instance isContinuous_baseFunctor :
    (baseFunctor B S hS 𝒳).IsContinuous (inclusionTopology.{u, w} B S hS 𝒳) (etaleTopology B) := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have := Stacks.Sites.FibredCategory.isContinuous_inheritedTopology_of_isFibered
    𝒳.val.val.p ((etaleTopology B).over (B.obj hS))
  have : (𝒳.val.val.p ⋙ Over.forget (B.obj hS)).IsContinuous
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (etaleTopology B) :=
    Functor.isContinuous_comp _ _ _ ((etaleTopology B).over (B.obj hS)) _
  exact Functor.isContinuous_comp _ _ _
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) _

/-- The functor to schemes is cocontinuous for the lisse-étale and the étale topologies. -/
instance isCocontinuous_baseFunctor :
    (baseFunctor B S hS 𝒳).IsCocontinuous (inclusionTopology.{u, w} B S hS 𝒳)
      (etaleTopology B) := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have := Stacks.Sites.FibredCategory.isCocontinuous_inheritedTopology_of_isFibered
    𝒳.val.val.p ((etaleTopology B).over (B.obj hS))
  have : (𝒳.val.val.p ⋙ Over.forget (B.obj hS)).IsCocontinuous
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (etaleTopology B) :=
    isCocontinuous_comp _ _ _ ((etaleTopology B).over (B.obj hS))
  exact isCocontinuous_comp _ _ _ (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))

section Slice

variable (y : LisseEtale.{u, w} B S hS 𝒳)

/-- The slice functor is continuous for the étale topologies. -/
instance isContinuous_sliceFunctor :
    (subcategorySliceFunctor (smoothObject.{u, w} B S hS 𝒳) y).IsContinuous
      ((inclusionTopology.{u, w} B S hS 𝒳).over y)
      (BigFppfOver.baseOverTopology B (𝒳.val.val.p.obj y.obj).left.1
        (𝒳.val.val.p.obj y.obj).left.2 .etale) :=
  Functor.isContinuous_overPost (inclusionTopology.{u, w} B S hS 𝒳) (etaleTopology B)
    (baseFunctor B S hS 𝒳) y

/-- The slice functor is cocontinuous for the étale topologies. -/
instance isCocontinuous_sliceFunctor :
    (subcategorySliceFunctor (smoothObject.{u, w} B S hS 𝒳) y).IsCocontinuous
      ((inclusionTopology.{u, w} B S hS 𝒳).over y)
      (BigFppfOver.baseOverTopology B (𝒳.val.val.p.obj y.obj).left.1
        (𝒳.val.val.p.obj y.obj).left.2 .etale) :=
  inferInstanceAs ((Over.post (X := y) (baseFunctor B S hS 𝒳)).IsCocontinuous
    ((inclusionTopology.{u, w} B S hS 𝒳).over y)
    ((etaleTopology B).over ((baseFunctor B S hS 𝒳).obj y)))

/-- The localizations of the slice functor are continuous. -/
instance isContinuous_overPost_sliceFunctor (X : Over y) :
    (Over.post (X := X) (subcategorySliceFunctor (smoothObject.{u, w} B S hS 𝒳) y)).IsContinuous
      (((inclusionTopology.{u, w} B S hS 𝒳).over y).over X)
      ((BigFppfOver.baseOverTopology B (𝒳.val.val.p.obj y.obj).left.1
        (𝒳.val.val.p.obj y.obj).left.2 .etale).over
          ((subcategorySliceFunctor (smoothObject.{u, w} B S hS 𝒳) y).obj X)) :=
  Functor.isContinuous_overPost _ _ (subcategorySliceFunctor (smoothObject.{u, w} B S hS 𝒳) y) X

/-- The structure sheaf of the lisse-étale site, localized at `y`, is the restriction of the
structure sheaf of the big étale site of the scheme below `y` along the slice functor. -/
theorem ringSheaf_over_obj_eq :
    ((inverseImageRing (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B)
        (smoothObject.{u, w} B S hS 𝒳)) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (smoothObject.{u, w} B S hS 𝒳).ι (lisseAmbientRing B S hS 𝒳)).over y).obj =
      (subcategorySliceFunctor (smoothObject.{u, w} B S hS 𝒳) y).op ⋙
        (FibredSite.baseRingStructureSheaf B
          (𝒳.val.val.p.obj y.obj).left.1 (𝒳.val.val.p.obj y.obj).left.2 .etale).obj :=
  rfl

/-- **The restriction along the slice functor of the associated module of a quasi-coherent
module on the scheme below `y` is quasi-coherent**, for the étale topologies. -/
theorem isQuasicoherentOnSite_sliceRestriction (𝓕 : (𝒳.val.val.p.obj y.obj).left.1.Modules)
    [𝓕.IsQuasicoherent] :
    ((SheafOfModules.restrictAlongContinuous
      (J := (inclusionTopology.{u, w} B S hS 𝒳).over y)
      (subcategorySliceFunctor (smoothObject.{u, w} B S hS 𝒳) y)
      (FibredSite.baseRingStructureSheaf B
        (𝒳.val.val.p.obj y.obj).left.1 (𝒳.val.val.p.obj y.obj).left.2 .etale)).obj
      (BigFppfOver.sectionsSheafOfModules B (𝒳.val.val.p.obj y.obj).left.1
        (𝒳.val.val.p.obj y.obj).left.2 .etale 𝓕)).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restriction
    (subcategorySliceFunctor (smoothObject.{u, w} B S hS 𝒳) y) _ _
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      (BigFppfOver.baseAssociatedModuleIsoSectionsSheaf B _ _ .etale 𝓕)
      (BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent B _ _ .etale 𝓕
        inferInstance))

end Slice

section SliceIso

variable {B E h S hS 𝒳} (F : SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))
  (hF : locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳 F)
  (y : LisseEtale.{u, w} B S hS 𝒳)
  (d : QuasicoherentBelow B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val y.obj)

include hF in
/-- **Stacks 07B1 (1)(b), localized at a smooth object.** -/
theorem isQuasicoherentOnSite_over_moduleRestriction :
    (((lisseRestriction B S hS 𝒳).obj F).over y).IsQuasicoherentOnSite := by
  obtain ⟨d⟩ := nonempty_quasicoherentBelow B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    F.val hF.1 y.obj
  have := d.isQuasicoherent
  have := isQuasicoherentOnSite_sliceRestriction B S hS 𝒳 y d.val
  exact SheafOfModules.isQuasicoherentOnSite_of_restrictionIso
    (subcategorySliceFunctor (smoothObject.{u, w} B S hS 𝒳) y)
    (FibredSite.baseRingStructureSheaf B (𝒳.val.val.p.obj y.obj).left.1
      (𝒳.val.val.p.obj y.obj).left.2 .etale) _ (ringSheaf_over_obj_eq B S hS 𝒳 y)
    (BigFppfOver.sectionsSheafOfModules B (𝒳.val.val.p.obj y.obj).left.1
      (𝒳.val.val.p.obj y.obj).left.2 .etale d.val) _
    ((SheafOfModules.pushforwardPushforwardValIso (Over.forget y)
      (smoothObject.{u, w} B S hS 𝒳).ι F) ≪≫
      subcategorySliceModuleIso (smoothObject.{u, w} B S hS 𝒳)
        (fun _ hx => flatObject_of_smoothObject B S hS 𝒳 hx) F.val hF y d)

end SliceIso

section Restriction

variable {B E h S hS 𝒳} (F : SheafOfModules.{u} (lisseAmbientRing B S hS 𝒳))
  (hF : locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳 F)

include hF in
/-- **Stacks 07B1** (1)(b).  Let `𝒳` be an algebraic stack and `F` a module on its étale site in
`LQCoh^fbc(𝒪_𝒳)` — locally quasi-coherent with the flat base change property of Stacks 0762,
read with the pullback of sheaves.  Then the restriction `g^{-1}F` of `F` to the lisse-étale site
is a quasi-coherent module on that ringed site. -/
theorem isQuasicoherentOnSite_moduleRestriction :
    ((lisseRestriction B S hS 𝒳).obj F).IsQuasicoherentOnSite :=
  (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite _).2
    ⟨LisseEtale.{u, w} B S hS 𝒳, fun y => y, fun Y =>
      (inclusionTopology.{u, w} B S hS 𝒳).superset_covering
      (fun Z _ _ => ⟨Z, ⟨𝟙 Z⟩⟩) ((inclusionTopology.{u, w} B S hS 𝒳).top_mem Y),
      fun y => isQuasicoherentOnSite_over_moduleRestriction F hF y⟩

end Restriction

end AlgebraicGeometry.Stack.LisseEtale

