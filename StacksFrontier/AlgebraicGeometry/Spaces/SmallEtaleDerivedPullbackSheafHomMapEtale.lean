module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleKFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBaseChangeAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHomSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomLeftAdjoint
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# The map of Stacks 08JF along an étale morphism

Let `a : X' ⟶ X` be an étale morphism of algebraic spaces. Extension by zero
`a_! : Mod(𝒪_{X'}) ⥤ Mod(𝒪_X)` is exact (Stacks 03DJ), so the adjunction `a_! ⊣ a^*` descends
to an adjunction `a_! ⊣ La^*` on unbounded derived categories. Through it, Yoneda's lemma
reduces the invertibility of the map of Stacks 08JF,
`La^*R𝓗om(M, K) ⟶ R𝓗om(La^*M, La^*K)`, to that of the canonical projection map
`a_!(Z ⊗^L La^*M) ⟶ a_!Z ⊗^L M`, the transpose of
`Z ⊗^L La^*M ⟶ La^*a_!Z ⊗^L La^*M ≅ La^*(a_!Z ⊗^L M)` (unit, then Stacks 07A4).

## Main definitions

* `smallEtaleDerivedLowerShriekAdjunction`: the adjunction `a_! ⊣ La^*` on derived categories.
* `smallEtaleDerivedLowerShriekProjectionMap`: the canonical projection map
  `a_!(Z ⊗^L La^*M) ⟶ a_!Z ⊗^L M`.

## Main results

* `isIso_smallEtaleDerivedPullbackSheafHomMap_of_isIso_projectionMap`: the map of Stacks 08JF at
  `M` is invertible when the projection maps at `M` are.
* `isIso_smallEtaleDerivedLowerShriekProjectionMap`: the derived projection maps are invertible
  when the module-level ones (`etaleModuleLowerShriekProjectionMap`) are.
* `isIso_smallEtaleDerivedPullbackSheafHomMap_of_isIso_etaleModuleLowerShriekProjectionMap`:
  hence the map of Stacks 08JF is invertible as soon as the module-level projection maps are.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/- The standard model of the derived category: the derived functors this file uses (derived
pullback, pushforward, tensor product and internal Hom on ringed sites and topoi) are stated
on it, so the statements here must be too. -/
attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' : AlgebraicSpaces B S hS}

/-- Extension by zero along an étale morphism, on unbounded derived categories, written between
the derived categories that the derived pullback is stated over. -/
abbrev smallEtaleDerivedLowerShriek (a : X' ⟶ X) (ha : IsEtale B S hS a.hom) :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  (etaleModuleLowerShriek B S hS a ha).mapDerivedCategory

/-- **Extension by zero is left adjoint to the derived pullback along an étale morphism**:
`a_! ⊣ La^*` on unbounded derived categories, from `a_! ⊣ a^*` and `La^* ≅ (a^*)_D`. -/
def smallEtaleDerivedLowerShriekAdjunction (a : X' ⟶ X) (ha : IsEtale B S hS a.hom) :
    smallEtaleDerivedLowerShriek a ha ⊣ smallEtaleDerivedModulePullback B S hS a :=
  (etaleModuleLowerShriekAdjunction B S hS a ha).mapDerivedCategory.ofNatIsoRight
    (smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).symm

/-- **The canonical projection map** `a_!(Z ⊗^L La^*M) ⟶ a_!Z ⊗^L M` along an étale morphism:
the transpose under `a_! ⊣ La^*` of the unit tensored with `La^*M`, followed by the inverse of
the isomorphism of Stacks 07A4. -/
abbrev smallEtaleDerivedLowerShriekProjectionMap (a : X' ⟶ X) (ha : IsEtale B S hS a.hom)
    (Z : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedLowerShriek a ha).obj
        (((smallEtaleDerivedTensor B S hS X').obj Z).obj
          ((smallEtaleDerivedModulePullback B S hS a).obj M)) ⟶
      ((smallEtaleDerivedTensor B S hS X).obj ((smallEtaleDerivedLowerShriek a ha).obj Z)).obj M :=
  PullbackInternalHom.leftAdjointProjectionMap (smallEtaleDerivedLowerShriekAdjunction a ha)
    (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedTensor B S hS X')
    (smallEtaleDerivedPullbackTensorIso a) Z M

/-- **The map of Stacks 08JF along an étale morphism is invertible when the projection maps
are.** If `a_!(Z ⊗^L La^*M) ⟶ a_!Z ⊗^L M` is invertible for every `Z`, then
`La^*R𝓗om(M, K) ⟶ R𝓗om(La^*M, La^*K)` is invertible for every `K`: Yoneda's lemma through
`a_! ⊣ La^*` and Stacks 08J8 on `X` and `X'`. -/
theorem isIso_smallEtaleDerivedPullbackSheafHomMap_of_isIso_projectionMap
    (a : X' ⟶ X) (ha : IsEtale B S hS a.hom)
    (M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hp : ∀ Z, IsIso (smallEtaleDerivedLowerShriekProjectionMap a ha Z M)) :
    IsIso (smallEtaleDerivedPullbackSheafHomMap a M K) := by
  rw [smallEtaleDerivedPullbackSheafHomMap_eq]
  exact PullbackInternalHom.isIso_pullbackHomMap_of_isIso_leftAdjointProjectionMap
    (smallEtaleDerivedLowerShriekAdjunction a ha) _ _ _ _ _ _ _ M K hp

/-- **The module-level projection map** `a_!(A ⊗ a^*M) ⟶ a_!A ⊗ M` of extension by zero along an
étale morphism: the transpose under `a_! ⊣ a^*` of the unit tensored with `a^*M`, followed by the
inverse of the comparison of Stacks 03EL transported to étale restriction. -/
abbrev etaleModuleLowerShriekProjectionMap (a : X' ⟶ X) (ha : IsEtale B S hS a.hom)
    (A : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :
    (etaleModuleLowerShriek B S hS a ha).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedTopos B S hS X').O).obj A).obj
          ((etaleModulePullback.{u, u} B S hS a ha).obj M)) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedTopos B S hS X).O).obj
        ((etaleModuleLowerShriek B S hS a ha).obj A)).obj M :=
  PullbackInternalHom.leftAdjointProjectionMap (etaleModuleLowerShriekAdjunction B S hS a ha)
    (Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedTopos B S hS X).O)
    (Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedTopos B S hS X').O)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorIsoOfIso
      (smallEtaleRingedToposHom B S hS a)
      (pullbackModulesIsoModulePullback B S hS a ≪≫
        modulePullbackIsoEtaleModulePullback B S hS a ha))
    A M

/-- **The derived projection maps along an étale morphism are invertible when the module-level
ones are**: `a_!(Z ⊗^L La^*M) ⟶ a_!Z ⊗^L M` is an isomorphism for all `Z` and `M` as soon as
`a_!(A ⊗ a^*M) ⟶ a_!A ⊗ M` is for all modules `A` and `M`. -/
theorem isIso_smallEtaleDerivedLowerShriekProjectionMap (a : X' ⟶ X) (ha : IsEtale B S hS a.hom)
    (hπ : ∀ A M, IsIso (etaleModuleLowerShriekProjectionMap a ha A M))
    (Z : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    IsIso (smallEtaleDerivedLowerShriekProjectionMap a ha Z M) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.isIso_leftAdjointProjectionMap_mapDerivedCategory
    (hGa := etaleModulePullback_additive B S hS a ha)
    (hGl := preservesFiniteLimits_etaleModulePullback B S hS a ha)
    (hGc := preservesFiniteColimits_etaleModulePullback B S hS a ha)
    (hEa := etaleModuleLowerShriek_additive B S hS a ha)
    (hEl := inferInstanceAs (PreservesFiniteLimits (etaleModuleLowerShriek B S hS a ha)))
    (hEc := inferInstanceAs (PreservesFiniteColimits (etaleModuleLowerShriek B S hS a ha)))
    (smallEtaleRingedToposHom B S hS a)
    (pullbackModulesIsoModulePullback B S hS a ≪≫ modulePullbackIsoEtaleModulePullback B S hS a ha)
    (smallEtaleDerivedTensorProduct B S hS X') (smallEtaleDerivedTensorProduct B S hS X)
    (etaleModuleLowerShriekAdjunction B S hS a ha) hπ Z M

/-- **The map of Stacks 08JF along an étale morphism is invertible when the module-level
projection maps are.** -/
theorem isIso_smallEtaleDerivedPullbackSheafHomMap_of_isIso_etaleModuleLowerShriekProjectionMap
    (a : X' ⟶ X) (ha : IsEtale B S hS a.hom)
    (hπ : ∀ A M, IsIso (etaleModuleLowerShriekProjectionMap a ha A M))
    (M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    IsIso (smallEtaleDerivedPullbackSheafHomMap a M K) :=
  isIso_smallEtaleDerivedPullbackSheafHomMap_of_isIso_projectionMap a ha M K
    (fun Z => isIso_smallEtaleDerivedLowerShriekProjectionMap a ha hπ Z M)

end AlgebraicGeometry.Space

end
