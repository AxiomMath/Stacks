module

public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealSheafKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ChartModel
public import
  StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparisonPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparisonConverse
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModuleAdjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DistinguishedTriangles
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherenceAlongAnEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedPerfectPseudoCoherentTransport

/-!
# Pseudo-coherence across `ε : X_étale ⟶ X_Zar` for a representable algebraic space

Let `T` be an object of the big fppf site over `S`, with underlying scheme `X_0`, and let
`ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X_0})` be the comparison morphism for the algebraic space
`X = yoneda.obj T`. An object `E` of `D(𝒪_{X_0})` is `m`-pseudo-coherent exactly when
`Lε^* E` is `m`-pseudo-coherent on the small étale site of `X`.

The small étale site of `X` is the small étale site of `X_0` (Stacks 04M0), along which
`m`-pseudo-coherence is transported in both directions, and `Lε^*` is the associated-module
functor of the small étale site of `X_0` followed by that transport; on the scheme `X_0` the
statement is Stacks 08HE.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentFrom_representedZariskiDerivedPullback_iff`
* `AlgebraicGeometry.Space.isPseudoCoherent_representedZariskiDerivedPullback_iff`

## References

* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (T : BigFppfOver B S hS)

/-- The equivalence of small étale sites of Stacks 04M0 is continuous, at the spelling of the two
ringed sites. -/
instance isContinuous_representedSmallEtaleEquivalence_functor_ringedSite :
    (representedSmallEtaleEquivalence B S hS T).functor.IsContinuous
      (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).J
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T) T.left.property).J :=
  isContinuous_representedSmallEtaleEquivalence_functor B S hS T

/-- The inverse of the equivalence of small étale sites of Stacks 04M0 is continuous, at the
spelling of the two ringed sites. -/
instance isContinuous_representedSmallEtaleEquivalence_inverse_smallEtaleRingedSite :
    (representedSmallEtaleEquivalence B S hS T).inverse.IsContinuous
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T) T.left.property).J
      (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).J :=
  isContinuous_representedSmallEtaleEquivalence_inverse B S hS T

/-- The transport of modules along the equivalence of small étale sites of Stacks 04M0, as the
equivalence of module categories it is. -/
abbrev representedPushforwardEquivalence :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T) T.left.property).O) ≌
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O) :=
  RingedSite.pushforwardEquivalenceOfIsIso
    (X := smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (Y := _root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T) T.left.property)
    (hfun := isContinuous_representedSmallEtaleEquivalence_functor B S hS T)
    (hinv := isContinuous_representedSmallEtaleEquivalence_inverse B S hS T)
    (representedSmallEtaleEquivalence B S hS T) (representedStructureMap B S hS T)
    (hρ := isIso_representedStructureMap _ _ _ T)

/-- The transport of modules along the equivalence of small étale sites is additive. -/
instance additive_representedPushforwardEquivalence_functor :
    (representedPushforwardEquivalence T).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **`Lε^*` is the associated-module functor of the small étale site of `X_0` followed by the
transport along Stacks 04M0**, on objects of the derived category. -/
def representedZariskiDerivedPullbackObjIso
    (E : DerivedCategory (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules) :
    (representedZariskiDerivedPullback B S hS T).obj E ≅
      (representedModulePushforward B S hS T).mapDerivedCategory.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
          T.left.property).mapDerivedCategory.obj E) :=
  haveI := Functor.preservesZeroMorphisms_of_iso
    (representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction B S hS T)
  (representedZariskiDerivedPullbackIso B S hS T).app E ≪≫
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact
      B S hS T).mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact
      B S hS T).mapDerivedCategoryFactors.app
      (DerivedCategory.Q.objPreimage E) ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex
          (representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
            B S hS T)
        (ComplexShape.up ℤ)).app (DerivedCategory.Q.objPreimage E)) ≪≫
    ((representedModulePushforward B S hS T).mapDerivedCategoryFactors.app
      (((_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
          T.left.property).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (DerivedCategory.Q.objPreimage E))).symm ≪≫
    (representedModulePushforward B S hS T).mapDerivedCategory.mapIso
      (((_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
          T.left.property).mapDerivedCategoryFactors.app
          (DerivedCategory.Q.objPreimage E)).symm ≪≫
        (_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
          T.left.property).mapDerivedCategory.mapIso
          (DerivedCategory.Q.objObjPreimageIso E))

/-- **`m`-pseudo-coherence across `ε` for a representable algebraic space.** An object `E` of
`D(𝒪_{X_0})` is `m`-pseudo-coherent exactly when `Lε^* E` is `m`-pseudo-coherent on the small
étale site of `yoneda.obj T`. -/
theorem isPseudoCoherentFrom_representedZariskiDerivedPullback_iff
    (E : DerivedCategory (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules)
    (m : ℤ) :
    (smallEtaleRingedSite B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).IsPseudoCoherentFrom
        ((representedZariskiDerivedPullback B S hS T).obj E) m ↔
      RingedSpace.IsPseudoCoherentFrom
        (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).toRingedSpace) E m := by
  have h₁ : (smallEtaleRingedSite B S hS (yoneda.obj T)
        (isAlgebraicSpace_yoneda B S hS T)).IsPseudoCoherentFrom
          ((representedZariskiDerivedPullback B S hS T).obj E) m ↔
      (smallEtaleRingedSite B S hS (yoneda.obj T)
        (isAlgebraicSpace_yoneda B S hS T)).IsPseudoCoherentFrom
          ((representedModulePushforward B S hS T).mapDerivedCategory.obj
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
              (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
              T.left.property).mapDerivedCategory.obj E)) m :=
    ⟨fun h => RingedSite.isPseudoCoherentFrom_of_iso _ m h
        (representedZariskiDerivedPullbackObjIso T E).symm,
      fun h => RingedSite.isPseudoCoherentFrom_of_iso _ m h
        (representedZariskiDerivedPullbackObjIso T E)⟩
  have h₂ := RingedSite.isPseudoCoherentFrom_mapDerivedCategory_pushforwardEquivalenceOfIsIso_iff
    (X := smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (Y := _root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T) T.left.property)
    (hfun := isContinuous_representedSmallEtaleEquivalence_functor B S hS T)
    (hinv := isContinuous_representedSmallEtaleEquivalence_inverse B S hS T)
    (representedSmallEtaleEquivalence B S hS T) (representedStructureMap B S hS T)
    (hρ := isIso_representedStructureMap _ _ _ T)
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
      T.left.property).mapDerivedCategory.obj E) m
  have h₃ := _root_.AlgebraicGeometry.SmallEtale.pseudoCoherentIffAssociatedModule
    (associatedBigEtaleSite B) (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
    T.left.property E m
  have h₄ := RingedSpace.PseudoCoherence.isPseudoCoherentFrom_ringedSite_iff
    (representedSchemeRepresentedZariskiRingedToposHom B S hS T).toRingedSpace E m
  exact h₁.trans (h₂.trans (h₃.symm.trans h₄))

/-- **Pseudo-coherence across `ε` for a representable algebraic space.** An object `E` of
`D(𝒪_{X_0})` is pseudo-coherent exactly when `Lε^* E` is pseudo-coherent on the small étale site
of `yoneda.obj T`. -/
theorem isPseudoCoherent_representedZariskiDerivedPullback_iff
    (E : DerivedCategory (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules) :
    (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).IsPseudoCoherent
        ((representedZariskiDerivedPullback B S hS T).obj E) ↔
      RingedSpace.IsPseudoCoherent
        (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).toRingedSpace) E := by
  refine (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).trans
    (Iff.trans ?_ (RingedSpace.isPseudoCoherent_iff_forall E).symm)
  exact forall_congr' fun m => isPseudoCoherentFrom_representedZariskiDerivedPullback_iff T E m

end AlgebraicGeometry.Space

end
