module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.DegreewiseComparison
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.SourcePasting
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.SourcePastingDerived

/-!
# The pasting law along the fibre for the derived comparison of flat base change

Let

```
Z' --k'--> Z
|i'        |i
v          v
X' --g'--> X
|f'        |f
v          v
S' --g---> S
```

be two commutative squares of schemes stacked along the fibre and let `G` be an `𝒪_{S'}`-module
flat over `S` whose inverse image `(f')^*G` is flat over `X`.  `SourcePasting.lean` proves the
pasting law for the *underived* comparison of [Stacks, Tag 0GN5]; this file transports it to the
bounded below derived categories, in the form the Mayer--Vietoris dévissage consumes: for a
bounded below complex `N` of injective `𝒪_Z`-modules whose image the comparisons of the outer
rectangle and of the upper square invert, the comparison of the lower square is invertible at the
image of the direct image `i_* N`.

The generic statement is `Stacks.Cohomology.BaseChange.isIso_derived_app_pasteSource`.  What this
file supplies is its three comparison isomorphisms at the concrete functors: the comparison of
the direct images along the two composite vertical morphisms, which are
`pushforwardSourceComp`, and the comparison

`Ψ' = (k')^*(-) ⊗ (i')^*(f')^*G ≅ (k')^*(-) ⊗ (i' ≫ f')^*G`

of the coefficient functor upstairs with the one the rectangle carries, which is the comparison
of the inverse images of `G` along `i' ≫ f'` tensored into the second factor.  The pointwise
pasting identity those three have to satisfy is exactly
`Stacks.AlgebraicGeometry.ModuleBaseChange.underivedComparison_pasteSource`.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleBaseChange.totalCoefficientsSourceCompIso`: the comparison of
  the coefficient functor upstairs with the one the rectangle carries.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_derivedComparison_app_pushforward`: **the
  derived comparison of the lower square is invertible at the image of `i_* N`.**

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S S' X X' Z Z' : Scheme.{u}}

/-- **The coefficient functor upstairs, read with the inverse image of `G` along the composite.**
The coefficient functor `Ψ' : M ↦ (k')^*M ⊗ (i')^*(f')^*G` attached to the upper square and the
module `(f')^*G` agrees with the coefficient functor `M ↦ (k')^*M ⊗ (i' ≫ f')^*G` the outer
rectangle carries, through the comparison of the inverse images of `G` along `i' ≫ f'`. -/
def totalCoefficientsSourceCompIso (k' : Z' ⟶ Z) (i' : Z' ⟶ X') (f' : X' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    totalCoefficients k' i' ((modulePullback f'.toLRSHom.toShHom).obj G) ≅
      totalCoefficients k' (i' ≫ f') G :=
  Functor.isoWhiskerLeft (modulePullback k'.toLRSHom.toShHom)
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z'.toRingedSpace.sheaf).flip.mapIso
      ((pullbackSourceComp i' f').app G))

/-- The component of `totalCoefficientsSourceCompIso` at `M`: the comparison of the inverse
images of `G` along `i' ≫ f'`, tensored into the second factor of `(k')^*M ⊗ -`. -/
theorem totalCoefficientsSourceCompIso_hom_app (k' : Z' ⟶ Z) (i' : Z' ⟶ X') (f' : X' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (M : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) :
    (totalCoefficientsSourceCompIso k' i' f' G).hom.app M =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z'.toRingedSpace.sheaf).obj
        ((modulePullback k'.toLRSHom.toShHom).obj M)).map ((pullbackSourceComp i' f').hom.app G)) :=
  rfl

/-! ### The pasting law on bounded below derived categories -/

variable {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  {i : Z ⟶ X} {k' : Z' ⟶ Z} {i' : Z' ⟶ X'}

/-- **The derived comparison of [Stacks, Tag 0GN5] for the lower square is invertible at the
image of a direct image.**  For two commutative squares of schemes stacked along the fibre, a
bounded below complex `N` of injective `𝒪_Z`-modules, and the comparisons of the outer rectangle
and of the upper square invertible at the image of `N` in `D⁺(Z)`, the comparison of the lower
square is invertible at the image of `i_* N` in `D⁺(X)`.

Neither square is required to be cartesian; what is used is that the direct images along `i` and
along `i'` preserve injective objects. -/
theorem isIso_derivedComparison_app_pushforward (w : g' ≫ f = f' ≫ g) (wi : k' ≫ i = i' ≫ g')
    (w2 : k' ≫ (i ≫ f) = (i' ≫ f') ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (hGup : AlgebraicGeometry.IsFlatOver g'.toLRSHom.toShHom
      ((modulePullback f'.toLRSHom.toShHom).obj G))
    [(modulePushforward i.toLRSHom.toShHom).PreservesInjectiveObjects]
    [(modulePushforward i'.toLRSHom.toShHom).PreservesInjectiveObjects]
    (N : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (hN : ∀ n : ℤ, Injective (N.obj.as.X n))
    (hrect : IsIso ((derivedComparison G w2 hG).app (DerivedCategory.Plus.Qh.obj N)))
    (hup : IsIso ((derivedComparison ((modulePullback f'.toLRSHom.toShHom).obj G) wi hGup).app
      (DerivedCategory.Plus.Qh.obj N))) :
    IsIso ((derivedComparison G w hG).app (DerivedCategory.Plus.Qh.obj
      ((modulePushforward i.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj N))) :=
  Stacks.Cohomology.BaseChange.isIso_derived_app_pasteSource
    (modulePushforward i.toLRSHom.toShHom) (modulePushforward f.toLRSHom.toShHom)
    (modulePushforward i'.toLRSHom.toShHom) (modulePushforward f'.toLRSHom.toShHom)
    (baseCoefficients g G) (totalCoefficients g' f' G)
    (totalCoefficients k' i' ((modulePullback f'.toLRSHom.toShHom).obj G))
    (modulePushforward (i ≫ f).toLRSHom.toShHom)
    (modulePushforward (i' ≫ f').toLRSHom.toShHom) (totalCoefficients k' (i' ≫ f') G)
    (underivedComparison wi ((modulePullback f'.toLRSHom.toShHom).obj G))
    (underivedComparison w G) (underivedComparison w2 G)
    (pushforwardSourceComp i f) (pushforwardSourceComp i' f')
    (totalCoefficientsSourceCompIso k' i' f' G)
    (baseCoefficientsDerivedIso g G hG)
    (baseCoefficientsDerivedIso g' ((modulePullback f'.toLRSHom.toShHom).obj G) hGup)
    rfl (underivedComparison_pasteSource w wi w2 G) N hN hrect hup

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
