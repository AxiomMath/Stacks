module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPresentation
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineLeray

/-!
# The projection formula of the affine base change, with the tensor factors in the other order

`BaseChangeAffineProjectionFormula.lean` proves the projection formula that conclusion (c) of
[Stacks, Tag 0EX3] needs,

> `((f')^* h_* 𝒪_{Y''}) ⊗_{𝒪_{X'}} F' ≅ h'_* (h')^* F'`,

with the pulled-back structure sheaf on the **left** of the tensor product, because that is the
order `Stacks.AlgebraicGeometry.ProjectionFormula.pushforwardUnitTensorIso` is stated at.
Conclusion (b) runs in the other order: the geometric factor of the Eilenberg-Watts endofunctor
is `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorFactor`, which is `F' ⊗ -`, so what (b)
computes is `H^d(X', F' ⊗ (f')^* M~)` with the coefficient on the **left**. Two isomorphic
objects spelled in opposite orders are not a spelling, so the two halves of the source's
computation cannot meet until the orders are crossed.

This file crosses them, by the symmetry `Stacks.SheafOfModules.tensorSheafCommIso` of the
sheafified tensor product, and reads the Leray composite of `BaseChangeAffineLeray.lean` in the
crossed order.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `tensorSheafSchemeCommIso`: the symmetry `A ⊗_{𝒪_X} B ≅ B ⊗_{𝒪_X} A` of the tensor product of
  modules on a scheme, at the uncurried `Stacks.SheafOfModules.Tensor.sheafTensor` spelling the
  projection formula is stated in.
* `pushforwardPullbackTensorIsoRight`: **the projection formula with the coefficient on the
  left**, `F' ⊗_{𝒪_{X'}} ((f')^* h_* 𝒪_{Y''}) ≅ h'_* (h')^* F'`.
* `cohomologyPullbackIsoTensorCohomologyRight`: **the right-hand end of the computation in
  [Stacks, Tag 0EX3] (c), in the order conclusion (b) is stated in**,
  `H^n(X'', (h')^* F') ≅ H^n(X', F' ⊗_{𝒪_{X'}} ((f')^* h_* 𝒪_{Y''}))`.

## Implementation notes

*The symmetry is available at the spelling in hand, and no bridge is needed.*
`Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)` is the
tensor bifunctor at the Grothendieck topology of the opens of `X` and the structure sheaf of
`X`, and `Stacks.SheafOfModules.tensorSheafRight_obj` says that the second variable of
`Stacks.SheafOfModules.tensorSheafCommIso` is that bifunctor with its arguments swapped. So the
symmetry applies with no retyping; the only care needed is that the two factors are named in the
order the bifunctor receives them.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The symmetry of the tensor product of modules on a scheme**, `A ⊗ B ≅ B ⊗ A`, at the
uncurried `Stacks.SheafOfModules.Tensor.sheafTensor` spelling in which the projection formula of
this directory is stated. This is `Stacks.SheafOfModules.tensorSheafCommIso`, whose two variables
are that bifunctor with its arguments in the two orders. -/
def tensorSheafSchemeCommIso (X : Scheme.{u}) (A B : X.Modules) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj (A, B) ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj (B, A) :=
  Stacks.SheafOfModules.tensorSheafCommIso
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (Osharp := X.toRingedSpace.sheaf) A B

variable {X' Y' X'' Y'' : Scheme.{u}} (f' : X' ⟶ Y') (h' : X'' ⟶ X') (f'' : X'' ⟶ Y'')
  (h : Y'' ⟶ Y')

/-- **The projection formula of the affine base change, with the coefficient on the left.** For a
cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
with `h` affine and `F'` a quasi-coherent `𝒪_{X'}`-module,

`F' ⊗_{𝒪_{X'}} ((f')^* h_* 𝒪_{Y''}) ≅ h'_* (h')^* F'`.

This is `pushforwardPullbackTensorIso` with the two tensor factors exchanged, which is the order
the geometric factor of conclusion (b) of [Stacks, Tag 0EX3] puts them in. -/
def pushforwardPullbackTensorIsoRight (hsq : IsPullback h' f'' f' h) [IsAffineHom h]
    (F' : X'.Modules) (hF' : F'.IsQuasicoherent) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).obj
        (F', (Scheme.Modules.pullback f').obj
          ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y''))) ≅
      (Scheme.Modules.pushforward h').obj ((Scheme.Modules.pullback h').obj F') :=
  tensorSheafSchemeCommIso X' F'
      ((Scheme.Modules.pullback f').obj
        ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y''))) ≪≫
    pushforwardPullbackTensorIso f' h' f'' h hsq F' hF'

/-- **The right-hand end of the computation in [Stacks, Tag 0EX3] (c), in the order conclusion
(b) is stated in.** For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
with `h` affine and `F'` a quasi-coherent `𝒪_{X'}`-module,

`H^n(X'', (h')^* F') ≅ H^n(X', F' ⊗_{𝒪_{X'}} ((f')^* h_* 𝒪_{Y''}))`

as `Γ(X', ⊤)`-modules, with no hypothesis on `Y'`, on `Y''` or on `f'` and in every degree. This
is `cohomologyPullbackIsoTensorCohomology` with the tensor factors in the order the geometric
factor of conclusion (b) puts them in. -/
def cohomologyPullbackIsoTensorCohomologyRight (hsq : IsPullback h' f'' f' h) [IsAffineHom h]
    (F' : X'.Modules) (hF' : F'.IsQuasicoherent) (n : ℕ) :
    (ModuleCat.restrictScalars h'.appTop.hom).obj
        (((moduleGlobalSections X'').rightDerived n).obj
          ((Scheme.Modules.pullback h').obj F')) ≅
      ((moduleGlobalSections X').rightDerived n).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).obj
          (F', (Scheme.Modules.pullback f').obj
            ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')))) :=
  haveI : IsAffineHom h' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
  cohomologyPullbackIsoPushforward h' F' hF' n ≪≫
    ((moduleGlobalSections X').rightDerived n).mapIso
      (pushforwardPullbackTensorIsoRight f' h' f'' h hsq F' hF').symm

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
