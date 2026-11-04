module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineTildePushforwardUnit
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineOpenSquare
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineTensorOrder

/-!
# The right-hand end of [Stacks, Tag 0EX3] (c) over a compatible pair of affine opens

For a cartesian square of schemes
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
a quasi-coherent `𝒪_{X'}`-module `F'`, an affine open `V` of `Y'` and an affine open `W` of `Y''`
lying over `V`, this file identifies the cohomology of the pullback of `F'` over `f''⁻¹(W)` with
the cohomology over `f'⁻¹(V)` of `F'` tensored with the pullback of the direct image of `𝒪_W`,
with no hypothesis on `h` or on either base.

## Main definitions

* `cohomologyPullbackIsoTensorCohomologyAffineOpens`: **the right-hand end of the computation in
  [Stacks, Tag 0EX3] (c) over a compatible pair of affine opens**,

  > `H^n(f''⁻¹(W), (h' ∣)^* (F'|)) ≅
  >    H^n(f'⁻¹(V), (F'|) ⊗ ((f' ∣_ V)^* (h ∣_ V^W)_* 𝒪_W))`.

* `cohomologyPullbackIsoTensorTildeAffineOpens`: **the same, with the direct image of the
  structure sheaf replaced by the module it is associated to**, the geometric factor of
  conclusion (b) evaluated at the functions on `W`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The right-hand end of the computation in [Stacks, Tag 0EX3] (c) over a compatible pair of
affine opens.** For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'`, an affine open `W` of `Y''` with `W ≤ h⁻¹(V)` and a quasi-coherent
`𝒪_{X'}`-module `F'`,

`H^n(f''⁻¹(W), (h' ∣)^* (F'|)) ≅ H^n(f'⁻¹(V), (F'|) ⊗ ((f' ∣_ V)^* (h ∣_ V^W)_* 𝒪_W))`

as `Γ(f'⁻¹(V), ⊤)`-modules, in every degree and with **no hypothesis on `Y'`, `Y''`, `f'` or
`h`**. -/
def cohomologyPullbackIsoTensorCohomologyAffineOpens
    {X' Y' X'' Y'' : Scheme.{u}} {f' : X' ⟶ Y'} {h' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}
    {h : Y'' ⟶ Y'} (hsq : IsPullback h' f'' f' h)
    {V : Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)]
    (hWV : W ≤ h ⁻¹ᵁ V) (hle : f'' ⁻¹ᵁ W ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V))
    (F' : X'.Modules) (hF' : F'.IsQuasicoherent) (n : ℕ) :
    (ModuleCat.restrictScalars
          (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle).appTop.hom).obj
        (((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerived n).obj
          ((Scheme.Modules.pullback (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
            ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F'))) ≅
      ((moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)).rightDerived n).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
              (f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).obj
          ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F',
            (Scheme.Modules.pullback (f' ∣_ V)).obj
              ((Scheme.Modules.pushforward (h.resLE V W hWV)).obj
                (Scheme.unitModule (W : Scheme))))) :=
  haveI := hF'
  cohomologyPullbackIsoTensorCohomologyRight (f' ∣_ V)
    (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle) (f'' ∣_ W) (h.resLE V W hWV)
    (isPullback_resLE_of_isPullback hsq hWV)
    ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')
    (Scheme.Modules.isQuasicoherent_restrictFunctor (f' ⁻¹ᵁ V).ι F') n

/-- **The right-hand end of [Stacks, Tag 0EX3] (c) over a pair of affine opens, with the
structure-sheaf direct image replaced by the module it is associated to.** The tensor factor
`(h ∣_ V^W)_* 𝒪_W` of `cohomologyPullbackIsoTensorCohomologyAffineOpens` is replaced by the module
associated to its global sections:

`H^n(f''⁻¹(W), (h' ∣)^* (F'|)) ≅ H^n(f'⁻¹(V), (F'|) ⊗ (f' ∣_ V)^* (Γ((h ∣_ V^W)_* 𝒪_W, ⊤))~)`.

The right-hand side is the geometric factor `M ↦ F ⊗ (f')^* M~` of conclusion (b) evaluated at
the functions on `W`, read over the functions on `V`. -/
def cohomologyPullbackIsoTensorTildeAffineOpens
    {X' Y' X'' Y'' : Scheme.{u}} {f' : X' ⟶ Y'} {h' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}
    {h : Y'' ⟶ Y'} (hsq : IsPullback h' f'' f' h)
    {V : Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)]
    (hWV : W ≤ h ⁻¹ᵁ V) (hle : f'' ⁻¹ᵁ W ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V))
    (F' : X'.Modules) (hF' : F'.IsQuasicoherent) (n : ℕ) :
    (ModuleCat.restrictScalars
          (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle).appTop.hom).obj
        (((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerived n).obj
          ((Scheme.Modules.pullback (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
            ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F'))) ≅
      ((moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)).rightDerived n).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
              (f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).obj
          ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F',
            (Scheme.Modules.pullback (f' ∣_ V)).obj
              ((Stacks.Coherent.affineTilde (V : Scheme)).obj
                ((SheafOfModules.evaluation (V : Scheme).ringCatSheaf (op ⊤)).obj
                  ((Scheme.Modules.pushforward (h.resLE V W hWV)).obj
                    (Scheme.unitModule (W : Scheme))))))) :=
  cohomologyPullbackIsoTensorCohomologyAffineOpens hsq hWV hle F' hF' n ≪≫
    ((moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)).rightDerived n).mapIso
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
            (f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).mapIso
        ((Iso.refl ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')).prod
          ((Scheme.Modules.pullback (f' ∣_ V)).mapIso
            (pushforwardUnitIsoAffineTilde (h.resLE V W hWV)).symm)))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
