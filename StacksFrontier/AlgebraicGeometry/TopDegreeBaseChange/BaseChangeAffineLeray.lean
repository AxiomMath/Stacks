module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineProjectionFormula

/-!
# Cohomology of a pullback along an affine base change

Let
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
be a cartesian square of schemes with `h` affine, and let `F'` be a quasi-coherent
`𝒪_{X'}`-module. We construct isomorphisms of `Γ(X', ⊤)`-modules
`H^n(X'', (h')^* F') ≅ H^n(X', h'_* (h')^* F')` and
`H^n(X'', (h')^* F') ≅ H^n(X', ((f')^* h_* 𝒪_{Y''}) ⊗_{𝒪_{X'}} F')`, where `H^n(X'', −)` is read
through restriction of scalars along `(h')^♯ : Γ(X', ⊤) ⟶ Γ(X'', ⊤)`.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.cohomologyPullbackIsoPushforward`: for `h'`
  affine, `H^n(X'', (h')^* F') ≅ H^n(X', h'_* (h')^* F')`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.cohomologyPullbackIsoTensorCohomology`:
  `H^n(X'', (h')^* F') ≅ H^n(X', ((f')^* h_* 𝒪_{Y''}) ⊗_{𝒪_{X'}} F')`.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X' Y' X'' Y'' : Scheme.{u}} (f' : X' ⟶ Y') (h' : X'' ⟶ X') (f'' : X'' ⟶ Y'')
  (h : Y'' ⟶ Y')

/-- For `h' : X'' ⟶ X'` affine and `F'` a quasi-coherent `𝒪_{X'}`-module, the isomorphism

`H^n(X'', (h')^* F') ≅ H^n(X', h'_* (h')^* F')`

of `Γ(X', ⊤)`-modules, the left-hand side being read through restriction of scalars along
`(h')^♯`, given by [Stacks, Tag 089W] at `(h')^* F'`. -/
def cohomologyPullbackIsoPushforward [IsAffineHom h'] (F' : X'.Modules)
    (hF' : F'.IsQuasicoherent) (n : ℕ) :
    (ModuleCat.restrictScalars h'.appTop.hom).obj
        (((moduleGlobalSections X'').rightDerived n).obj
          ((Scheme.Modules.pullback h').obj F')) ≅
      ((moduleGlobalSections X').rightDerived n).obj
        ((Scheme.Modules.pushforward h').obj ((Scheme.Modules.pullback h').obj F')) :=
  haveI : F'.IsQuasicoherent := hF'
  haveI : ((Scheme.Modules.pullback h').obj F').IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback h' F'
  Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward h'
    ((Scheme.Modules.pullback h').obj F') n

/-- For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
with `h` affine and `F'` a quasi-coherent `𝒪_{X'}`-module,

`H^n(X'', (h')^* F') ≅ H^n(X', ((f')^* h_* 𝒪_{Y''}) ⊗_{𝒪_{X'}} F')`

as `Γ(X', ⊤)`-modules: the isomorphism `cohomologyPullbackIsoPushforward` along the affine `h'`
followed by the projection formula `pushforwardPullbackTensorIso`. -/
def cohomologyPullbackIsoTensorCohomology (hsq : IsPullback h' f'' f' h) [IsAffineHom h]
    (F' : X'.Modules) (hF' : F'.IsQuasicoherent) (n : ℕ) :
    (ModuleCat.restrictScalars h'.appTop.hom).obj
        (((moduleGlobalSections X'').rightDerived n).obj
          ((Scheme.Modules.pullback h').obj F')) ≅
      ((moduleGlobalSections X').rightDerived n).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).obj
          ((Scheme.Modules.pullback f').obj
            ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')), F')) :=
  haveI : IsAffineHom h' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
  cohomologyPullbackIsoPushforward h' F' hF' n ≪≫
    ((moduleGlobalSections X').rightDerived n).mapIso
      (pushforwardPullbackTensorIso f' h' f'' h hsq F' hF').symm

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
