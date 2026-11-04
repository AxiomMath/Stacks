module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaStructureSheafTensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projection formula for the affine base change of a morphism

Let
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
be a cartesian square of schemes with `h` affine, and let `F'` be a quasi-coherent
`𝒪_{X'}`-module. We construct an isomorphism
`((f')^* h_* 𝒪_{Y''}) ⊗_{𝒪_{X'}} F' ≅ h'_* (h')^* F'` of `𝒪_{X'}`-modules, as the composite of
affine base change for direct images ([Stacks, Tag 02KG]) at `𝒪_{Y''}` with the projection
formula ([Stacks, Tag 0FZE]) at the structure sheaf of `X''`.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.pullbackPushforwardUnitIso`: the structure-sheaf
  base change `(f')^* h_* 𝒪_{Y''} ≅ h'_* 𝒪_{X''}` of a cartesian square whose right-hand
  morphism `h` is affine.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.pushforwardPullbackTensorIso`: the projection
  formula `((f')^* h_* 𝒪_{Y''}) ⊗_{𝒪_{X'}} F' ≅ h'_* (h')^* F'`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable {X' Y' X'' Y'' : Scheme.{u}} (f' : X' ⟶ Y') (h' : X'' ⟶ X') (f'' : X'' ⟶ Y'')
  (h : Y'' ⟶ Y')

/-- For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
with `h` affine,

`(f')^* h_* 𝒪_{Y''} ≅ h'_* 𝒪_{X''}`.

This is the base-change morphism of [Stacks, Tag 02KG] at `𝒪_{Y''}`, followed by the
identification `(f'')^* 𝒪_{Y''} ≅ 𝒪_{X''}` of
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`. -/
@[ega "I 10.14.6" "special case",
  ega "II 1.5.5" "partial",
  ega "III 1.4.15" "q = 0, F = O_X, u affine",
  sga "1 X 1.5" "partial",
  sga "3 VIB 11.1",
  sga "6 0 2.9" "partial"]
def pullbackPushforwardUnitIso (hsq : IsPullback h' f'' f' h) [IsAffineHom h] :
    (Scheme.Modules.pullback f').obj
        ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')) ≅
      (Scheme.Modules.pushforward h').obj (Scheme.unitModule X'') :=
  haveI : IsIso ((AffinePushforward.baseChangeNatTrans hsq.flip.w).app
      (Scheme.unitModule Y'')) :=
    AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hsq.flip (Scheme.unitModule Y'')
  asIso ((AffinePushforward.baseChangeNatTrans hsq.flip.w).app (Scheme.unitModule Y'')) ≪≫
    (Scheme.Modules.pushforward h').mapIso (Scheme.Modules.pullbackUnitIso f'')

/-- For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
with `h` affine and `F'` a quasi-coherent `𝒪_{X'}`-module,

`((f')^* h_* 𝒪_{Y''}) ⊗_{𝒪_{X'}} F' ≅ h'_* (h')^* F'`,

given by `pullbackPushforwardUnitIso` on the left tensor factor followed by the projection
formula `Stacks.AlgebraicGeometry.ProjectionFormula.pushforwardUnitTensorIso` along the affine
`h'`. -/
def pushforwardPullbackTensorIso (hsq : IsPullback h' f'' f' h) [IsAffineHom h]
    (F' : X'.Modules) (hF' : F'.IsQuasicoherent) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).obj
        ((Scheme.Modules.pullback f').obj
          ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')), F') ≅
      (Scheme.Modules.pushforward h').obj ((Scheme.Modules.pullback h').obj F') :=
  haveI : IsAffineHom h' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).mapIso
      ((pullbackPushforwardUnitIso f' h' f'' h hsq).prod (Iso.refl F')) ≪≫
    ProjectionFormula.pushforwardUnitTensorIso h' F' hF'

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
