module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectQuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointCoproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongADenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms

/-!
# Perfect objects on the model of the spaces-étale site

Let `X` be an algebraic space.  The sheaves of modules on the `Type u`-presented model
`AlgebraicGeometry.Space.spacesEtaleModelRingedTopos X` of the ringed spaces-étale site are the
`𝒪_X`-modules on the small étale site, by `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv`.
This file shows that the induced equivalence of derived categories preserves perfect objects
(Stacks 08G5) in both directions.

The equivalence is the composite of three: the Comparison Lemma along the dense subsite of the
small étale model in the spaces-étale model, restriction of scalars along the identification of
the two structure sheaves, and the inverse of the Comparison Lemma along the small étale model of
the small étale site.  Each preserves perfect objects by
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongADenseSubsite`.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelRingedSite`: the ringed site of the spaces-étale model.
* `AlgebraicGeometry.Space.spacesEtaleModelModulesEquivMapDerivedIso`,
  `AlgebraicGeometry.Space.spacesEtaleModelModulesEquivInverseMapDerivedIso`: the derived functors
  of the equivalence and of its inverse as composites of the derived functors of their factors,
  each factor written between the module categories of the ringed sites involved.

## Main results

* `AlgebraicGeometry.Space.isPerfect_spacesEtaleModelModulesEquiv_functor`: a perfect object of
  the model is carried to a perfect object of `D(𝒪_X)`.
* `AlgebraicGeometry.Space.isPerfect_spacesEtaleModelModulesEquiv_inverse`: a perfect object of
  `D(𝒪_X)` is carried to a perfect object of the model.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.DenseSubsiteModules

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The ringed site of the model of the spaces-étale site of `X`: the ringed site underlying
`AlgebraicGeometry.Space.spacesEtaleModelRingedTopos`, with its fields spelled out. -/
abbrev spacesEtaleModelRingedSite : RingedSite.{u, u, u} where
  C := SmallModel.{u} (SpacesEtale B S hS X)
  J := smallModelTopology B S hS X
  O := spacesEtaleModelStructureSheaf B S hS X

/-- The small étale ringed site of `X`, `AlgebraicGeometry.Space.smallEtaleRingedSite`, written as
a structure literal so that instance search sees its fields. -/
abbrev smallEtaleRingedSiteLiteral : RingedSite.{u + 1, u, u} where
  C := SmallEtale B S hS X.1
  J := SmallEtale.topology B S hS X.1
  O := structureSheaf B S hS X.1 X.2

attribute [local instance] Stacks.Sites.overPost_isDenseSubsite

/-- The first factor of `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv`: the Comparison
Lemma along the dense subsite of the small étale model in the spaces-étale model. -/
abbrev spacesEtaleModelModulesEquiv₁ :=
  (moduleRestrictionEquivalence.{u} (smallEtaleModelTopology B S hS X.1)
      (smallModelTopology B S hS X) (spacesEtaleModelComparison B S hS X)
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelStructureSheaf B S hS X)))

/-- The second factor of `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv`: restriction of
scalars along the identification of the two structure sheaves on the small étale model. -/
abbrev spacesEtaleModelModulesEquiv₂ :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (spacesEtaleModelRingRestrictionIso B S hS X))

section Exactness

variable {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ]

/-- The functor of an equivalence of abelian categories is additive and preserves finite limits
and finite colimits; packaged so that the three instances are available at once. -/
theorem exact_functor_of_equivalence (e : 𝒜 ≌ ℬ) :
    e.functor.Additive ∧ PreservesFiniteLimits e.functor ∧ PreservesFiniteColimits e.functor :=
  ⟨Functor.additive_of_preserves_binary_products _,
    @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _ _ _ _ _
      e.symm.toAdjunction.rightAdjoint_preservesLimits,
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
      e.toAdjunction.leftAdjoint_preservesColimits⟩

end Exactness

/-- Restriction to the dense subsite of the small étale model, into the sheaves of modules of the
induced ringed site. -/
abbrev spacesEtaleModelRestriction₁ :=
  (spacesEtaleModelRingedSite B S hS X).denseSubsiteModuleRestriction
    (smallEtaleModelTopology B S hS X.1) (spacesEtaleModelComparison B S hS X)

/-- Restriction of scalars along the identification of the two structure sheaves on the small étale
model, between the sheaves of modules of the two ringed sites. -/
abbrev spacesEtaleModelRestriction₂ :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((spacesEtaleModelRingedSite B S hS X).denseSubsiteRestriction
        (smallEtaleModelTopology B S hS X.1) (spacesEtaleModelComparison B S hS X)).O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((smallEtaleRingedSiteLiteral B S hS X).denseSubsiteRestriction
          (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X).inverse).O) :=
  SheafOfModules.restrictScalars.{u} (spacesEtaleModelRingRestrictionIso B S hS X).inv

/-- The inverse of the Comparison Lemma along the small étale model. -/
abbrev spacesEtaleModelRestriction₃ :=
  ((smallEtaleRingedSiteLiteral B S hS X).denseSubsiteModulesEquiv
    (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X).inverse).inverse

/-- The inverse of the Comparison Lemma along the small étale model is additive. -/
instance additive_spacesEtaleModelRestriction₃ : (spacesEtaleModelRestriction₃ B S hS X).Additive :=
  RingedSite.additive_denseSubsiteModulesEquiv_inverse _ _ _

/-- Restriction to the dense subsite of the small étale model is additive. -/
instance additive_spacesEtaleModelRestriction₁ : (spacesEtaleModelRestriction₁ B S hS X).Additive :=
  RingedSite.additive_denseSubsiteModuleRestriction _ _ _

/-- Restriction of scalars along the identification of the two structure sheaves is an
equivalence. -/
instance isEquivalence_spacesEtaleModelRestriction₂ :
    (spacesEtaleModelRestriction₂ B S hS X).IsEquivalence :=
  @RingedSite.isEquivalence_restrictScalars_of_isIso _ _ _ _ _ _ (Iso.isIso_inv _)

/-- Restriction to the dense subsite of the small étale model is an equivalence. -/
instance isEquivalence_spacesEtaleModelRestriction₁ :
    (spacesEtaleModelRestriction₁ B S hS X).IsEquivalence :=
  RingedSite.isEquivalence_denseSubsiteModuleRestriction _ _ _

/-- Restriction of scalars along the identification of the two structure sheaves is additive. -/
instance additive_spacesEtaleModelRestriction₂ : (spacesEtaleModelRestriction₂ B S hS X).Additive :=
  inferInstanceAs
    (SheafOfModules.restrictScalars.{u} (spacesEtaleModelRingRestrictionIso B S hS X).inv).Additive

/-- The derived functor of `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` is the composite
of the derived functors of its three factors. -/
def spacesEtaleModelModulesEquivMapDerivedIso
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedSite B S hS X).O))) :
    (spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj K ≅
      (spacesEtaleModelRestriction₃ B S hS X).mapDerivedCategory.obj
        ((spacesEtaleModelRestriction₂ B S hS X).mapDerivedCategory.obj
          ((spacesEtaleModelRestriction₁ B S hS X).mapDerivedCategory.obj K)) :=
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv₁ B S hS X)).1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv₁ B S hS X)).2.1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv₁ B S hS X)).2.2
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv₂ B S hS X)).1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv₂ B S hS X)).2.1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv₂ B S hS X)).2.2
  haveI := (exact_functor_of_equivalence (smallEtaleModelModulesEquiv B S hS X).symm).1
  haveI := (exact_functor_of_equivalence (smallEtaleModelModulesEquiv B S hS X).symm).2.1
  haveI := (exact_functor_of_equivalence (smallEtaleModelModulesEquiv B S hS X).symm).2.2
  ((Stacks.DerivedFunctor.mapDerivedCategoryCompIso (spacesEtaleModelModulesEquiv₁ B S hS X).functor
    ((spacesEtaleModelModulesEquiv₂ B S hS X).functor ⋙
      (smallEtaleModelModulesEquiv B S hS X).symm.functor)).app K).symm ≪≫
  ((Stacks.DerivedFunctor.mapDerivedCategoryCompIso (spacesEtaleModelModulesEquiv₂ B S hS X).functor
      (smallEtaleModelModulesEquiv B S hS X).symm.functor).app _).symm ≪≫ Iso.refl _

/-- **The equivalence of the modules on the spaces-étale model with the `𝒪_X`-modules carries
perfect objects to perfect objects.** -/
theorem isPerfect_spacesEtaleModelModulesEquiv_functor
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedSite B S hS X).O)))
    (hK : (spacesEtaleModelRingedSite B S hS X).IsPerfect K) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect
      ((spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj K) := by
  have h₁ := (spacesEtaleModelRingedSite B S hS X).isPerfect_mapDerivedCategory_moduleRestriction
    (smallEtaleModelTopology B S hS X.1) (spacesEtaleModelComparison B S hS X) K hK
  have h₂ := RingedSite.isPerfect_mapDerivedCategory_restrictScalars_of_iso
    ((spacesEtaleModelRingedSite B S hS X).denseSubsiteRestriction
      (smallEtaleModelTopology B S hS X.1) (spacesEtaleModelComparison B S hS X))
    (smallEtaleModelStructureSheaf B S hS X) (spacesEtaleModelRingRestrictionIso B S hS X).symm _ h₁
  have h₃ := (smallEtaleRingedSiteLiteral B S hS X)
    |>.isPerfect_mapDerivedCategory_moduleRestrictionEquivalence_inverse
    (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X).inverse _ h₂
  obtain ⟨L, hL, ⟨i⟩⟩ := h₃
  exact ⟨L, hL, ⟨i ≪≫ (spacesEtaleModelModulesEquivMapDerivedIso B S hS X K).symm⟩⟩

/-- Restriction to the dense subsite given by the small étale model of the small étale site. -/
abbrev smallEtaleModelRestriction₃ :=
  (smallEtaleRingedSiteLiteral B S hS X).denseSubsiteModuleRestriction
    (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X).inverse

/-- Restriction of scalars along the inverse identification of the two structure sheaves on the
small étale model. -/
abbrev smallEtaleModelRestriction₂ :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((smallEtaleRingedSiteLiteral B S hS X).denseSubsiteRestriction
        (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X).inverse).O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((spacesEtaleModelRingedSite B S hS X).denseSubsiteRestriction
          (smallEtaleModelTopology B S hS X.1) (spacesEtaleModelComparison B S hS X)).O) :=
  SheafOfModules.restrictScalars.{u} (spacesEtaleModelRingRestrictionIso B S hS X).hom

/-- The inverse of the Comparison Lemma along the dense subsite of the small étale model in the
spaces-étale model. -/
abbrev smallEtaleModelRestriction₁ :=
  ((spacesEtaleModelRingedSite B S hS X).denseSubsiteModulesEquiv
    (smallEtaleModelTopology B S hS X.1) (spacesEtaleModelComparison B S hS X)).inverse

/-- The inverse of the Comparison Lemma along the dense subsite of the small étale model in the
spaces-étale model is additive. -/
instance additive_smallEtaleModelRestriction₁ : (smallEtaleModelRestriction₁ B S hS X).Additive :=
  RingedSite.additive_denseSubsiteModulesEquiv_inverse _ _ _

/-- Restriction to the small étale model of the small étale site is additive. -/
instance additive_smallEtaleModelRestriction₃ : (smallEtaleModelRestriction₃ B S hS X).Additive :=
  RingedSite.additive_denseSubsiteModuleRestriction _ _ _

/-- Restriction to the small étale model of the small étale site is an equivalence. -/
instance isEquivalence_smallEtaleModelRestriction₃ :
    (smallEtaleModelRestriction₃ B S hS X).IsEquivalence :=
  RingedSite.isEquivalence_denseSubsiteModuleRestriction _ _ _

/-- Restriction of scalars along the inverse identification of the two structure sheaves is an
equivalence. -/
instance isEquivalence_smallEtaleModelRestriction₂ :
    (smallEtaleModelRestriction₂ B S hS X).IsEquivalence :=
  @RingedSite.isEquivalence_restrictScalars_of_isIso _ _ _ _ _ _ (Iso.isIso_hom _)

/-- Restriction of scalars along the inverse identification of the two structure sheaves is
additive. -/
instance additive_smallEtaleModelRestriction₂ : (smallEtaleModelRestriction₂ B S hS X).Additive :=
  inferInstanceAs
    (SheafOfModules.restrictScalars.{u} (spacesEtaleModelRingRestrictionIso B S hS X).hom).Additive

/-- The derived functor of the inverse of `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` is
the composite of the derived functors of its three factors. -/
def spacesEtaleModelModulesEquivInverseMapDerivedIso
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    (spacesEtaleModelModulesEquiv B S hS X).inverse.mapDerivedCategory.obj K ≅
      (smallEtaleModelRestriction₁ B S hS X).mapDerivedCategory.obj
        ((smallEtaleModelRestriction₂ B S hS X).mapDerivedCategory.obj
          ((smallEtaleModelRestriction₃ B S hS X).mapDerivedCategory.obj K)) :=
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv₁ B S hS X).symm).1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv₁ B S hS X).symm).2.1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv₁ B S hS X).symm).2.2
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv₂ B S hS X).symm).1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv₂ B S hS X).symm).2.1
  haveI := (exact_functor_of_equivalence (spacesEtaleModelModulesEquiv₂ B S hS X).symm).2.2
  haveI := (exact_functor_of_equivalence (smallEtaleModelModulesEquiv B S hS X)).1
  haveI := (exact_functor_of_equivalence (smallEtaleModelModulesEquiv B S hS X)).2.1
  haveI := (exact_functor_of_equivalence (smallEtaleModelModulesEquiv B S hS X)).2.2
  ((Stacks.DerivedFunctor.mapDerivedCategoryCompIso
    ((smallEtaleModelModulesEquiv B S hS X).functor ⋙
      (spacesEtaleModelModulesEquiv₂ B S hS X).symm.functor)
    (spacesEtaleModelModulesEquiv₁ B S hS X).symm.functor).app K).symm ≪≫
  (spacesEtaleModelModulesEquiv₁ B S hS X).symm.functor.mapDerivedCategory.mapIso
    ((Stacks.DerivedFunctor.mapDerivedCategoryCompIso (smallEtaleModelModulesEquiv B S hS X).functor
      (spacesEtaleModelModulesEquiv₂ B S hS X).symm.functor).app K).symm ≪≫ Iso.refl _

/-- **The equivalence of the `𝒪_X`-modules with the modules on the spaces-étale model carries
perfect objects to perfect objects.** -/
theorem isPerfect_spacesEtaleModelModulesEquiv_inverse
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect K) :
    (spacesEtaleModelRingedSite B S hS X).IsPerfect
      ((spacesEtaleModelModulesEquiv B S hS X).inverse.mapDerivedCategory.obj K) := by
  have h₃ := (smallEtaleRingedSiteLiteral B S hS X).isPerfect_mapDerivedCategory_moduleRestriction
    (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X).inverse K hK
  have h₂ := RingedSite.isPerfect_mapDerivedCategory_restrictScalars_of_iso
    ((smallEtaleRingedSiteLiteral B S hS X).denseSubsiteRestriction
      (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X).inverse)
    ((spacesEtaleModelComparison B S hS X).sheafPushforwardContinuous CommRingCat.{u}
      (smallEtaleModelTopology B S hS X.1) (smallModelTopology B S hS X)
      |>.obj (spacesEtaleModelStructureSheaf B S hS X))
    (spacesEtaleModelRingRestrictionIso B S hS X) _ h₃
  have h₁ := (spacesEtaleModelRingedSite B S hS X)
    |>.isPerfect_mapDerivedCategory_moduleRestrictionEquivalence_inverse
    (smallEtaleModelTopology B S hS X.1) (spacesEtaleModelComparison B S hS X) _ h₂
  obtain ⟨L, hL, ⟨i⟩⟩ := h₁
  exact ⟨L, hL, ⟨i ≪≫ (spacesEtaleModelModulesEquivInverseMapDerivedIso B S hS X K).symm⟩⟩

end AlgebraicGeometry.Space

end
