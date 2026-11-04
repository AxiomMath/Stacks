module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# Derived pullback and derived pushforward along an isomorphism of algebraic spaces

Let `ι : X ≅ Y` be an isomorphism of algebraic spaces.  Then `Lι^* : D(𝒪_Y) ⥤ D(𝒪_X)` is an
equivalence of categories, with quasi-inverse `L(ι⁻¹)^*`, by the composition and unit laws of
derived pullback (Stacks 0D6D); consequently `Rι_* ∘ Lι^* ≅ id`, and for any `q : Y ⟶ Z` the
derived direct image along `ι ≫ q` of `Lι^*K` is the derived direct image of `K` along `q`.
On a single module, `Lι^*(M[0]) ≅ (ι^*M)[0]`, an isomorphism being étale.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackEquivalenceOfIso`: `Lι^*` as an
  equivalence of derived categories.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackPushforwardIsoOfIso`: `Lι^* ⋙ Rι_* ≅ 𝟭`.
* `AlgebraicGeometry.Space.derivedModulePushforwardCompPullbackIsoOfIso`:
  `R(ι ≫ q)_*(Lι^*K) ≅ Rq_*K`, for the total right derived functors of the direct images.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackSingleIsoOfIso`:
  `Lι^*(M[0]) ≅ (ι^*M)[0]`.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackSingleInvIsoOfIso`:
  `Lι^*((ι⁻¹)^*M[0]) ≅ M[0]`.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y Z : AlgebraicSpaces B S hS}

/-- **Derived pullback along an isomorphism of algebraic spaces is an equivalence**, with
quasi-inverse the derived pullback along the inverse isomorphism. -/
def smallEtaleDerivedModulePullbackEquivalenceOfIso (ι : X ≅ Y) :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ≌
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  CategoryTheory.Equivalence.mk (smallEtaleDerivedModulePullback B S hS ι.hom)
    (smallEtaleDerivedModulePullback B S hS ι.inv)
    ((smallEtaleDerivedModulePullbackIdIso B S hS Y).symm ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS ι.inv_hom_id.symm ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS ι.inv ι.hom).symm)
    (smallEtaleDerivedModulePullbackCompIso B S hS ι.hom ι.inv ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS ι.hom_inv_id ≪≫
      smallEtaleDerivedModulePullbackIdIso B S hS X)

/-- **For an isomorphism `ι` of algebraic spaces, `Rι_* ∘ Lι^* ≅ id`**: the right adjoint of the
equivalence `Lι^*` is its quasi-inverse `L(ι⁻¹)^*`. -/
def smallEtaleDerivedPullbackPushforwardIsoOfIso (ι : X ≅ Y) :
    smallEtaleDerivedModulePullback B S hS ι.hom ⋙ smallEtaleDerivedModulePushforward B S hS ι.hom ≅
      𝟭 _ :=
  Functor.isoWhiskerLeft _
      ((smallEtaleDerivedAdjunction B S hS ι.hom).rightAdjointUniq
        (smallEtaleDerivedModulePullbackEquivalenceOfIso ι).toAdjunction) ≪≫
    (smallEtaleDerivedModulePullbackEquivalenceOfIso ι).unitIso.symm

/-- **Derived direct image along `ι ≫ q` of a pullback along an isomorphism `ι`**:
`R(ι ≫ q)_*(Lι^*K) ≅ Rq_*K`, for the total right derived functors of the direct images of
modules. -/
def derivedModulePushforwardCompPullbackIsoOfIso (ι : X ≅ Y) (q : Y ⟶ Z)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS (ι.hom ≫ q)) :
        DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
          DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)).obj
        ((smallEtaleDerivedModulePullback B S hS ι.hom).obj K) ≅
      (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS q) :
        DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
          DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)).obj K :=
  (derivedModulePushforwardCompIso B S hS ι.hom q).app _ ≪≫
    (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS q)).mapIso
      (((smallEtaleDerivedModulePushforwardIso B S hS ι.hom).app _).symm ≪≫
        (smallEtaleDerivedPullbackPushforwardIsoOfIso ι).app K)

/-- **Derived pullback of a single module along an isomorphism is the pullback in degree zero**:
`Lι^*(M[0]) ≅ (ι^*M)[0]`, an isomorphism being étale. -/
def smallEtaleDerivedModulePullbackSingleIsoOfIso (ι : X ≅ Y)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    (smallEtaleDerivedModulePullback B S hS ι.hom).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((modulePullback B S hS ι.hom).obj M) :=
  (smallEtaleDerivedModulePullback B S hS ι.hom).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M) ≪≫
    smallEtaleDerivedModulePullbackObjQIsoOfIsEtale ι.hom (isEtale_of_isIso B S hS ι.hom.hom) _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (modulePullback B S hS ι.hom)
        (ComplexShape.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm

/-- **`Lι^*` undoes the inverse image along `ι⁻¹` on a single module**:
`Lι^*(((ι⁻¹)^*M)[0]) ≅ M[0]`. -/
def smallEtaleDerivedModulePullbackSingleInvIsoOfIso (ι : X ≅ Y)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :
    (smallEtaleDerivedModulePullback B S hS ι.hom).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((modulePullback B S hS ι.inv).obj M)) ≅
      (DerivedCategory.singleFunctor _ 0).obj M :=
  smallEtaleDerivedModulePullbackSingleIsoOfIso ι _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((modulePullbackCompIso B S hS ι.hom ι.inv).app M ≪≫
        (eqToIso (congrArg (modulePullback B S hS) ι.hom_inv_id)).app M ≪≫
        (modulePullbackIdIso B S hS X).app M)

end AlgebraicGeometry.Space

end
