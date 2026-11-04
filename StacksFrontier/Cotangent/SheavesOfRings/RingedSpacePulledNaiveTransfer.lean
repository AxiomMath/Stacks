module

public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceInverseImageNaiveExt
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionPresentationClass
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt

/-!
# The transfer `Ext¹_{f⁻¹𝒪_Y}(NL_{X_A/S}, 𝒢) = Ext¹_{𝒪_X}(Lf^*NL_{Y/S}, 𝒢)`, in the spellings of
the deformation theory of ringed spaces

Let `f : X ⟶ Y` and `t : Y ⟶ S` be morphisms of ringed spaces, let `X_A = (X, f⁻¹𝒪_Y)` be the
inverse-image ringed space with projection `π : X_A ⟶ Y`, and let `ι : X ⟶ X_A` be the
factorization of `f` (`AlgebraicGeometry.RingedSpace.inverseImageSourceInclusion`).  This file
states `AlgebraicGeometry.RingedSpace.relativeNaiveCotangentExtEquivDerivedPullback` in degree
`1` with its two sides spelled as
`AlgebraicGeometry.RingedSpaceThickening.PresentedSquareZeroExtension.relativeObj` /
`...shiftedSingleObj` on `X_A` (the `Ext¹` group in which the classes of square-zero extensions
of `f⁻¹𝒪_Y`-algebras live, Tag 0GQ0) and
`AlgebraicGeometry.RingedSpaceThickening.extOnePulledNaiveCotangent` (the group
`Ext¹_{𝒪_X}(Lf^*NL_{Y/S}, 𝒢)` of Tags 08U8 and 0E3V).

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.pulledNaiveCotangentTransfer`: the identification.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.pulledNaiveCotangentTransfer_naturality`: it is natural
  in the coefficient module `𝒢`.
-/

@[expose] public noncomputable section

open CategoryTheory RingedSpaceModuleAdjunction AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

attribute [local instance] HasDerivedCategory.standard

variable {X Y S : RingedSpace.{u, u}} (f : X ⟶ Y) (t : Y ⟶ S)

/-- **`Ext¹_{f⁻¹𝒪_Y}(NL_{X_A/S}, ι_*𝒢) = Ext¹_{𝒪_X}(Lf^*NL_{Y/S}, 𝒢)`**, where
`X_A = (X, f⁻¹𝒪_Y)`, `NL_{X_A/S}` is the naive cotangent complex of `π ≫ t`, and `ι_*𝒢` is the
`𝒪_X`-module `𝒢` read over `f⁻¹𝒪_Y` along `f♯`.  No hypothesis: `π` is flat, `ι_*` is exact,
and `Lf^* = Lι^* ∘ π^*` with `Lι^* ⊣ Rι_* = ι_*`. -/
def pulledNaiveCotangentTransfer (G : SheafOfModules.{u} (structureSheafRing X)) :
    (PresentedSquareZeroExtension.relativeObj (inverseImageProjection Y f.hom.base ≫ t) ⟶
        PresentedSquareZeroExtension.shiftedSingleObj
          ((modulePushforward (inverseImageSourceInclusion f)).obj G)) ≃+
      extOnePulledNaiveCotangent f t G :=
  relativeNaiveCotangentExtEquivDerivedPullback f t G 1

/-- The transfer is precomposition with `π^*NL_{Y/S} ≅ NL_{X_A/S}`, transposition along
`Lι^* ⊣ Rι_*` and `Lf^* = Lι^* ∘ π^*`: it is
`AlgebraicGeometry.RingedSpace.relativeNaiveCotangentExtEquivDerivedPullback` in degree `1`. -/
theorem pulledNaiveCotangentTransfer_apply (G : SheafOfModules.{u} (structureSheafRing X))
    (x : PresentedSquareZeroExtension.relativeObj (inverseImageProjection Y f.hom.base ≫ t) ⟶
        PresentedSquareZeroExtension.shiftedSingleObj
          ((modulePushforward (inverseImageSourceInclusion f)).obj G)) :
    pulledNaiveCotangentTransfer f t G x =
      relativeNaiveCotangentExtEquivDerivedPullback f t G 1 x :=
  rfl

/-- **Naturality of the transfer in the coefficient module**: for `g : 𝒢 ⟶ 𝒢'`, postcomposing
with `(ι_*g)[0]⟦1⟧` before the transfer is postcomposing with `g[0]⟦1⟧` after it. -/
theorem pulledNaiveCotangentTransfer_naturality
    {G G' : SheafOfModules.{u} (structureSheafRing X)} (g : G ⟶ G')
    (x : PresentedSquareZeroExtension.relativeObj (inverseImageProjection Y f.hom.base ≫ t) ⟶
        PresentedSquareZeroExtension.shiftedSingleObj
          ((modulePushforward (inverseImageSourceInclusion f)).obj G)) :
    pulledNaiveCotangentTransfer f t G'
        (x ≫ ((DerivedCategory.singleFunctor _ 0).map
          ((modulePushforward (inverseImageSourceInclusion f)).map g))⟦(1 : ℤ)⟧') =
      pulledNaiveCotangentTransfer f t G x ≫
        ((DerivedCategory.singleFunctor _ 0).map g)⟦(1 : ℤ)⟧' :=
  relativeNaiveCotangentExtEquivDerivedPullback_naturality f t g 1 x

end AlgebraicGeometry.RingedSpaceThickening

end
