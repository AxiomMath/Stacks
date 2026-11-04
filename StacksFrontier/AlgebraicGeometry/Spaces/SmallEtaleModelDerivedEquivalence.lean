module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleEquiUniverseModel
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteEquivalenceTensorAnyUniverse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnEquivalence
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorOfToposHom

/-!
# The derived category of an algebraic space and its equi-universe model

Let `X` be an algebraic space. `AlgebraicGeometry.Space.modulesEquivModelModules` identifies the
`𝒪_X`-modules with the sheaves of modules on the equi-universe model
`AlgebraicGeometry.Space.smallEtaleModelRingedSite` of the small étale ringed site of `X`. This
file passes that equivalence to derived categories and shows that it carries the derived tensor
product of `X` to the derived tensor product of the model.

The equivalence of module categories is the pullback of modules along the morphism of ringed
topoi from the model to the small étale site presented by the inverse of the model equivalence
(`Stacks.SheafOfModules.reindexRingedSiteHomAnyUniverse`): both are left adjoint to the same
pushforward.
That pullback is exact, so its derived functor of Stacks 06YY is the induced functor on derived
categories, and Stacks 07A4 for this morphism of ringed topoi is the comparison of the two
derived tensor products.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleModelDerivedEquivalence`: `D(𝒪_X) ≌ D(𝒪_model)`.
* `AlgebraicGeometry.Space.smallEtaleModelRingedSiteHom`: the morphism of ringed sites from the
  model to the small étale site.
* `AlgebraicGeometry.Space.smallEtaleModelDerivedPullbackIso`: its derived pullback is the
  derived equivalence.
* `AlgebraicGeometry.Space.smallEtaleModelDerivedTensorIso`: the derived equivalence carries
  `K ⊗^L L` to the derived tensor product of the images, naturally in `(K, L)`.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (X : AlgebraicSpaces B S hS)

/-- `AlgebraicGeometry.Space.modulesEquivModelModules` with its source written over the structure
sheaf of the small étale ringed topos, the spelling at which `D(𝒪_X)` is stated. -/
abbrev smallEtaleModelModulesEquivalence :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) ≌
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O) :=
  modulesEquivModelModules B S hS X.1 X.2

/-- The functor of `smallEtaleModelModulesEquivalence` is additive. -/
instance smallEtaleModelModulesEquivalence_functor_additive :
    (smallEtaleModelModulesEquivalence B S hS X).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The derived category of an algebraic space is the derived category of its equi-universe
model**, through the exact equivalence of module categories
`AlgebraicGeometry.Space.modulesEquivModelModules`. -/
def smallEtaleModelDerivedEquivalence :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ≌
      DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O)) :=
  Stacks.DerivedQCoh.Equivalence.mapDerivedCategory (smallEtaleModelModulesEquivalence B S hS X)

/-- The morphism of ringed sites from the equi-universe model to the small étale ringed site of
`X`: the inverse of the model equivalence, which is a morphism of sites as a dense subsite
inclusion, with the counit as structure map. -/
def smallEtaleModelRingedSiteHom :
    RingedSite.HomGeneral (smallEtaleModelRingedSite B S hS X.1 X.2)
      (smallEtaleRingedSite B S hS X.1 X.2) :=
  letI : ∀ x, HasInitial (StructuredArrow x (smallEtaleModelEquivalence B S hS X.1).inverse.op) :=
    isRightAdjoint_iff_hasInitial_structuredArrow.1 inferInstance
  letI : ∀ x, HasLimitsOfShape
      (StructuredArrow x (smallEtaleModelEquivalence B S hS X.1).inverse.op) (Type u) :=
    fun _ => ⟨fun _ => inferInstance⟩
  letI : IsMorphismOfSites.{u} (smallEtaleModelEquivalence B S hS X.1).inverse
      (SmallEtale.topology B S hS X.1) (smallEtaleModelTopology B S hS X.1) :=
    IsMorphismOfSites.ofIsDenseSubsite _
  Stacks.SheafOfModules.reindexRingedSiteHomAnyUniverse (smallEtaleModelTopology B S hS X.1)
    (smallEtaleModelEquivalence B S hS X.1) (structureSheaf B S hS X.1 X.2)

/-- The morphism of ringed topoi underlying `smallEtaleModelRingedSiteHom`. -/
abbrev smallEtaleModelRingedToposHom :
    RingedToposHom (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos
      (smallEtaleRingedTopos B S hS X) :=
  (smallEtaleModelRingedSiteHom B S hS X).toRingedToposHom

/-- The pushforward of modules along `smallEtaleModelRingedToposHom` is the inverse of the module
equivalence. -/
def smallEtaleModelPushforwardIso :
    (smallEtaleModelRingedToposHom B S hS X).pushforwardModules ≅
      ((modulesEquivModelModules B S hS X.1 X.2).inverse :
        SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O) ⥤
          SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  (smallEtaleModelRingedSiteHom B S hS X).pushforwardToposIsoGeneral ≪≫ Iso.refl _

/-- The pullback of modules along `smallEtaleModelRingedToposHom` is the functor of the module
equivalence: both are left adjoint to its inverse. -/
def smallEtaleModelPullbackIso :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
        (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleModelRingedToposHom B S hS X).toModulesHom ≅
      (smallEtaleModelModulesEquivalence B S hS X).functor :=
  Adjunction.leftAdjointUniq
    ((RingedToposHom.pullbackAdjPushforwardModules
      (smallEtaleModelRingedToposHom B S hS X)).ofNatIsoRight
        (smallEtaleModelPushforwardIso B S hS X))
    (smallEtaleModelModulesEquivalence B S hS X).toAdjunction

open Stacks.Cohomology.DerivedPullbackOfToposHom in
/-- The derived pullback along `smallEtaleModelRingedToposHom` exists (Stacks 06YY). -/
instance hasLeftDerivedFunctor_smallEtaleModelPullbackOnHomotopy :
    (pullbackOnHomotopy (smallEtaleModelRingedToposHom B S hS X)).HasLeftDerivedFunctor
    (quasiIsoTarget (Y := smallEtaleRingedTopos B S hS X)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
    (Y := smallEtaleRingedTopos B S hS X) (smallEtaleModelRingedToposHom B S hS X)

open Stacks.Cohomology.DerivedPullbackOfToposHom in
/-- The derived pullback along `smallEtaleModelRingedToposHom` is the derived equivalence: the
pullback of modules is exact, so its left derived functor is the induced functor. -/
def smallEtaleModelDerivedPullbackIso :
    derivedPullback (X := (smallEtaleModelRingedSite B S hS X.1 X.2).toRingedTopos)
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleModelRingedToposHom B S hS X) ≅
      (smallEtaleModelDerivedEquivalence B S hS X).functor :=
  haveI := RingedToposHom.pullbackModules_additive (smallEtaleModelRingedToposHom B S hS X)
  Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso _ _ _
    (derivedPullbackComparison (smallEtaleModelRingedToposHom B S hS X))
    (smallEtaleModelPullbackIso B S hS X)

/-- The total tensor complexes of sheaves of modules on the small étale model site exist, at the
universes of the model site. -/
theorem hasMapBifunctor_sheafTensor_smallEtaleModel
    (K₁ K₂ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O)) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (smallEtaleModelRingedSite B S hS X.1 X.2).O) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u, u, u, u, u} _ K₁ K₂

attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

open Stacks.Cohomology.DerivedPullbackOfToposHom in
/-- **The derived equivalence with the model carries the derived tensor product of `X` to that of
the model**, `E(K ⊗^L L) ≅ E K ⊗^L E L` naturally in `(K, L)`. This is Stacks 07A4 for
`smallEtaleModelRingedToposHom`, read through `smallEtaleModelDerivedPullbackIso`. -/
def smallEtaleModelDerivedTensorIso :
    Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X) ⋙
        (smallEtaleModelDerivedEquivalence B S hS X).functor ≅
      (smallEtaleModelDerivedEquivalence B S hS X).functor.prod
          (smallEtaleModelDerivedEquivalence B S hS X).functor ⋙
        Functor.uncurry.obj (Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2)) :=
  Functor.isoWhiskerLeft _ (smallEtaleModelDerivedPullbackIso B S hS X).symm ≪≫
    derivedPullbackTensorIso (smallEtaleModelRingedToposHom B S hS X)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct _)
      (smallEtaleDerivedTensorProduct B S hS X) ≪≫
    Functor.isoWhiskerRight (NatIso.prod (smallEtaleModelDerivedPullbackIso B S hS X)
      (smallEtaleModelDerivedPullbackIso B S hS X)) _


/-- **The derived equivalence with the model carries perfect objects to perfect objects.** -/
theorem isPerfect_smallEtaleModelDerivedEquivalence_functor_obj
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    RingedSite.IsPerfect (smallEtaleModelRingedSite B S hS X.1 X.2)
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj E) :=
  RingedSite.isPerfect_mapDerivedCategory_pushforwardEquivalenceOfIsIso
    (X := smallEtaleModelRingedSite B S hS X.1 X.2) (Y := smallEtaleRingedSite B S hS X.1 X.2)
    (smallEtaleModelEquivalence B S hS X.1)
    (hfun := smallEtaleModelRingedSite_functor_isContinuous B S hS X.1 X.2)
    (hinv := smallEtaleModelRingedSite_inverse_isContinuous B S hS X.1 X.2)
    (𝟙 _) (hρ := IsIso.id _) E hE

/-- The counit of the model equivalence, read on the structure sheaf, is invertible. -/
instance isIso_reindexBackSharp_smallEtaleModel :
    IsIso (Stacks.SheafOfModules.reindexBackSharp (J' := smallEtaleModelTopology B S hS X.1)
      (smallEtaleModelEquivalence B S hS X.1) (ringedToposStructureRingSheaf B S hS X)) := by
  have : IsIso ((sheafToPresheaf _ _).map (Stacks.SheafOfModules.reindexBackSharp
      (J' := smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquivalence B S hS X.1)
      (ringedToposStructureRingSheaf B S hS X))) :=
    inferInstanceAs (IsIso (Functor.whiskerRight
      (NatTrans.op (smallEtaleModelEquivalence B S hS X.1).counit) _))
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- **The inverse of the derived equivalence with the model carries perfect objects to perfect
objects.** -/
theorem isPerfect_smallEtaleModelDerivedEquivalence_inverse_obj
    (N : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O)))
    (hN : RingedSite.IsPerfect (smallEtaleModelRingedSite B S hS X.1 X.2) N) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2)
      ((smallEtaleModelDerivedEquivalence B S hS X).inverse.obj N) :=
  RingedSite.isPerfect_mapDerivedCategory_pushforwardEquivalenceOfIsIso
    (X := smallEtaleRingedSite B S hS X.1 X.2) (Y := smallEtaleModelRingedSite B S hS X.1 X.2)
    (smallEtaleModelEquivalence B S hS X.1).symm
    (hfun := smallEtaleModelRingedSite_inverse_isContinuous B S hS X.1 X.2)
    (hinv := smallEtaleModelRingedSite_functor_isContinuous B S hS X.1 X.2)
    (Stacks.SheafOfModules.reindexBackSharp (J' := smallEtaleModelTopology B S hS X.1)
      (smallEtaleModelEquivalence B S hS X.1) (ringedToposStructureRingSheaf B S hS X))
    (hρ := isIso_reindexBackSharp_smallEtaleModel B S hS X) N hN

end AlgebraicGeometry.Space

end
