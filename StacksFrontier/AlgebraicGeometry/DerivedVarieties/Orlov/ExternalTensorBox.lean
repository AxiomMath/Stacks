module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.SingleKernel
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.BoxTransform
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ExternalTensorProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor

/-!
# The external tensor product of modules is the derived external product

Let `X` and `Y` be schemes over `S` with flat projections `X ×_S Y ⟶ X` and `X ×_S Y ⟶ Y`, let
`ℰ` be an `𝒪_X`-module and `𝒢` a finite locally free `𝒪_Y`-module. Then the derived external
product of `ℰ[0]` and `𝒢[0]` is the external tensor product placed in degree zero:

`L pr_1^*ℰ[0] ⊗^𝐋 L pr_2^*𝒢[0] ≅ (pr_1^*ℰ ⊗ pr_2^*𝒢)[0] = (ℰ ⊠ 𝒢)[0]`.

The derived pullbacks are the termwise ones because the projections are flat, and the derived
tensor product with the flat module `pr_2^*𝒢` placed in degree zero is the termwise one because
`pr_2^*𝒢[0]` is K-flat. This identifies the terms `ℰᵢ ⊠ 𝒢ᵢ` of the resolution of the diagonal of
[Stacks, Section 0G07] with the objects `AlgebraicGeometry.derivedBox` that the computation of
the integral transform (`AlgebraicGeometry.boxTransformMap`) is stated for.

## Main definitions

* `AlgebraicGeometry.dpullSingleIsoOfIsFlat`: `L p^*(ℱ[0]) ≅ (p^*ℱ)[0]` for flat `p`.
* `AlgebraicGeometry.dtenSingleIsoOfIsFlat`: `A[0] ⊗^𝐋 L[0] ≅ (A ⊗ L)[0]` for flat `L`.
* `AlgebraicGeometry.derivedBoxSingleIso`: `ℰ[0] ⊠^𝐋 𝒢[0] ≅ (ℰ ⊠ 𝒢)[0]`.

## References

* [Stacks Project, Section 0G07](https://stacks.math.columbia.edu/tag/0G07)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DerivedTensor.RingedSite RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- **The derived pullback along a flat morphism of a module in degree zero is the pullback in
degree zero**: `L p^*(ℱ[0]) ≅ (p^*ℱ)[0]`, naturally in `ℱ`. -/
def dpullSingleIsoOfIsFlat {V W : Scheme.{u}} (p : V ⟶ W)
    (hp : AlgebraicGeometry.IsFlat p.toLRSHom.toShHom) :
    DerivedCategory.singleFunctor W.Modules 0 ⋙ dpull p ≅
      Scheme.Modules.pullback p ⋙ DerivedCategory.singleFunctor V.Modules 0 :=
  Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQh _ 0) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.singleFunctor _ 0)
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackComparisonIsoOfIsFlat _ hp) ≪≫
    Stacks.DerivedFunctor.mapSingleQhIso (modulePullback p.toLRSHom.toShHom) 0

/-- **The twist of a complex by a flat module is computed termwise**: `Q(P) ⊗^𝐋 L[0] ≅ Q(P ⊗ L)`
for a flat `L`, since `L[0]` is K-flat ([Stacks, Tag 06YQ]). This is `Stacks.Chow.derivedTwistQIso`
with the invertibility of `L` weakened to flatness, which is all its proof uses. -/
def derivedTwistQIsoOfIsFlat {W : Scheme.{u}} (P : CochainComplex W.Modules ℤ) (L : W.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := W.sheaf) L) :
    Stacks.Chow.derivedTwist (DerivedCategory.Q.obj P) L ≅
      DerivedCategory.Q.obj (Stacks.Chow.twistComplex P L) :=
  (canonicalDerivedTensorProduct W.sheaf).comparisonRight P (Stacks.Chow.singleZero L)
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat W.sheaf L hL 0) ≪≫
    DerivedCategory.Q.mapIso (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor W.toRingedSpace.sheaf) P L)

/-- **The derived tensor product with a flat module in degree zero is the tensor product in
degree zero**: `A[0] ⊗^𝐋 L[0] ≅ (A ⊗ L)[0]` for a flat `L`. -/
def dtenSingleIsoOfIsFlat {W : Scheme.{u}} (A L : W.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := W.sheaf) L) :
    ((derivedTensorProductFunctor W.sheaf).obj
        ((DerivedCategory.singleFunctor W.Modules 0).obj A)).obj
        ((DerivedCategory.singleFunctor W.Modules 0).obj L) ≅
      (DerivedCategory.singleFunctor W.Modules 0).obj ((Stacks.Chow.twistFunctor L).obj A) :=
  ((derivedTensorProductFunctor W.sheaf).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ W.Modules 0).app A)).app _ ≪≫
    ((derivedTensorProductFunctor W.sheaf).obj _).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ W.Modules 0).app L) ≪≫
    derivedTwistQIsoOfIsFlat _ L hL ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
        (Stacks.Chow.twistFunctor L) (ComplexShape.up ℤ) 0).app A) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ W.Modules 0).app _).symm

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The derived external product of two modules in degree zero is their external tensor
product in degree zero**, when the two projections are flat and the second module is finite
locally free. -/
def derivedBoxSingleIso (hfst : AlgebraicGeometry.IsFlat (pullback.fst f g).toLRSHom.toShHom)
    (hsnd : AlgebraicGeometry.IsFlat (pullback.snd f g).toLRSHom.toShHom)
    (E : X.Modules) (G : Y.Modules)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G) :
    derivedBox f g ((DerivedCategory.singleFunctor X.Modules 0).obj E)
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G) ≅
      (DerivedCategory.singleFunctor (pullback f g).Modules 0).obj
        (externalTensorProduct f g E G) :=
  ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).mapIso
      ((dpullSingleIsoOfIsFlat (pullback.fst f g) hfst).app E)).app _ ≪≫
    ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj _).mapIso
      ((dpullSingleIsoOfIsFlat (pullback.snd f g) hsnd).app G) ≪≫
    dtenSingleIsoOfIsFlat _ _ (AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree _
      (Stacks.Chow.isFiniteLocallyFree_pullback (pullback.snd f g) G hG))

end AlgebraicGeometry

end
