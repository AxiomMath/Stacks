module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PullbackPushforwardTensor
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensorDegrees

/-!
# Derived pullback and derived tensor product of single modules

Let `f : X ⟶ S` be a morphism of schemes along which inverse image of modules is exact (that
is, `f` is flat), let `H` be an `𝒪_S`-module and let `L` be a flat `𝒪_X`-module. Then

`Lf^*(H[0]) ⊗ᴸ_{𝒪_X} L[n] ≅ (f^*H ⊗_{𝒪_X} L)[n]`

in `D(𝒪_X)` (for `f` flat the exactness hypothesis is
`AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat f`). A flat module placed in a
single degree is K-flat ([Stacks, Tag 06YQ]), so the derived tensor product with it is computed by
the total tensor complex ([Stacks, Tag 06YU]).

## Main results

* `Stacks.Duality.derivedTensorSingleSingleIsoOfFlat`: `M[0] ⊗ᴸ L[n] ≅ (M ⊗ L)[n]` for `L` flat.
* `Stacks.Duality.derivedPullbackSingleTensorSingleIso`:
  `Lf^*(H[0]) ⊗ᴸ L[n] ≅ (f^*H ⊗ L)[n]` for `f^*` exact and `L` flat.
* `Stacks.Duality.quasiCoherentDerivedPullbackTensorSingleIso`: the same read on the objects of
  `D_QCoh`, with the bifunctor `Stacks.Duality.quasiCoherentDerivedTensor` and the functor
  `Stacks.Duality.quasiCoherentDerivedPullback'`.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-- **The total tensor complex of two single complexes is a single complex**:
`Tot(M[0] ⊗_O L[n]) ≅ (M ⊗_O L)[n]` on a ringed site. -/
def tensorComplexSingleSingleIso {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) {_ : HasWeakSheafify J AddCommGrpCat.{u}}
    {_ : J.WEqualsLocallyBijective AddCommGrpCat.{u}}
    {_ : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).Additive}
    {_ : ∀ X, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj X).Additive}
    {_ : ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R))
        (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ)}
    (M L : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R)) (n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj L) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M).obj L) :=
  HomologicalComplex.mapBifunctorSingleSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) M L 0 n ≪≫
    eqToIso (by rw [zero_add])

/-- **A module in degree zero tensored with a flat module in degree `n`**:
`M[0] ⊗ᴸ_{𝒪_X} L[n] ≅ (M ⊗_{𝒪_X} L)[n]` for a flat `𝒪_X`-module `L`. -/
def derivedTensorSingleSingleIsoOfFlat {X : Scheme.{u}} (M L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.toRingedSpace.sheaf) L)
    (n : ℤ) :
    ((derivedTensor X).obj ((DerivedCategory.singleFunctor X.Modules 0).obj M)).obj
        ((DerivedCategory.singleFunctor X.Modules n).obj L) ≅
      (DerivedCategory.singleFunctor X.Modules n).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
          M).obj L) :=
  ((derivedTensor X).mapIso ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app M)).app _ ≪≫
    ((derivedTensor X).obj _).mapIso ((DerivedCategory.singleFunctorIsoCompQ X.Modules n).app L) ≪≫
    (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).comparisonRight _ _
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat _ L hL n) ≪≫
    DerivedCategory.Q.mapIso (tensorComplexSingleSingleIso _ M L n) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules n).app _).symm

/-- **The derived pullback of a module in degree zero, tensored with a flat module in degree
`n`**: `Lf^*(H[0]) ⊗ᴸ_{𝒪_X} L[n] ≅ (f^*H ⊗_{𝒪_X} L)[n]` for a morphism `f : X ⟶ S` along which
inverse image is exact and a flat `𝒪_X`-module `L`. -/
def derivedPullbackSingleTensorSingleIso {X S : Scheme.{u}} (f : X ⟶ S)
    [PreservesFiniteLimits (Scheme.Modules.pullback f)] (H : S.Modules) (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.toRingedSpace.sheaf) L)
    (n : ℤ) :
    ((derivedTensor X).obj ((derivedPullback f).obj
        ((DerivedCategory.singleFunctor S.Modules 0).obj H))).obj
        ((DerivedCategory.singleFunctor X.Modules n).obj L) ≅
      (DerivedCategory.singleFunctor X.Modules n).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
          ((Scheme.Modules.pullback f).obj H)).obj L) :=
  ((derivedTensor X).mapIso
      (Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPullbackSingleIsoOfExact f H)).app
      _ ≪≫
    derivedTensorSingleSingleIsoOfFlat _ L hL n

/-- **`Lf^*(H[0]) ⊗ᴸ L[n] ≅ (f^*H ⊗ L)[n]` on `D_QCoh`**: `derivedPullbackSingleTensorSingleIso`
read on the underlying objects of `Stacks.Duality.quasiCoherentDerivedTensor` and
`Stacks.Duality.quasiCoherentDerivedPullback'`, for any objects `K` and `E` of the
quasi-coherent derived categories whose underlying objects are `H[0]` and `L[n]`. -/
def quasiCoherentDerivedPullbackTensorSingleIso {X S : Scheme.{u}} (f : X ⟶ S)
    [PreservesFiniteLimits (Scheme.Modules.pullback f)] (H : S.Modules) (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.toRingedSpace.sheaf) L)
    (n : ℤ) (K : quasiCoherentDerivedCategory S)
    (hK : K.obj = (DerivedCategory.singleFunctor S.Modules 0).obj H)
    (E : quasiCoherentDerivedCategory X)
    (hE : E.obj = (DerivedCategory.singleFunctor X.Modules n).obj L) :
    (((quasiCoherentDerivedTensor X).obj ((quasiCoherentDerivedPullback' f).obj K)).obj E).obj ≅
      (DerivedCategory.singleFunctor X.Modules n).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
          ((Scheme.Modules.pullback f).obj H)).obj L) :=
  eqToIso rfl ≪≫
    ((derivedTensor X).mapIso ((derivedPullback f).mapIso (eqToIso hK))).app E.obj ≪≫
    ((derivedTensor X).obj _).mapIso (eqToIso hE) ≪≫
    derivedPullbackSingleTensorSingleIso f H L hL n

end Stacks.Duality

end
