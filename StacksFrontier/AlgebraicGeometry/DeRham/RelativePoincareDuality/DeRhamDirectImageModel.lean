module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.RelativeCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.RelativeHodgePairing
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardSingle

/-!
# The derived direct image of the relative de Rham complex in `D(𝒪_S)`

Let `f : X ⟶ S` be a morphism of schemes. The relative de Rham complex `Ω^•_{X/S}` is a complex of
`f⁻¹𝒪_S`-modules, so its derived direct image `Rf_*Ω^•_{X/S}` is taken along the morphism of ringed
spaces `(X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)` whose ring map `𝒪_S ⟶ f_*f⁻¹𝒪_S` is the unit of `f⁻¹ ⊣ f_*`. That
morphism is the second factor of `f` itself: `f` is the composite

`(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)`

of the identity of `X` with the structure map `f⁻¹𝒪_S ⟶ 𝒪_X` and that morphism. This is the setting
of [Stacks, Tag 0G8K]: the relative cup product of `Rf_*Ω^•_{X/S}` (Tag 0FU6) and the relative cup
products of the `Rf_*Ω^p_{X/S}` of [Stacks, Tag 0G8I] live in the same `D(𝒪_S)`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamDirectImage`: `Rf_*Ω^•_{X/S}` in `D(𝒪_S)`, along
  `Stacks.DeRhamDirectImage.inverseImageBaseProjection f : (X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)`.
* `AlgebraicGeometry.Scheme.Hom.deRhamDirectImageCup`: its relative cup product
  `Rf_*Ω^• ⊗^L Rf_*Ω^• ⟶ Rf_*Ω^•` (Tag 0FU6).
* `AlgebraicGeometry.Scheme.Hom.formsDirectImageIso`: `Rf_*(Ω^p[0])` along `f` is the derived
  direct image along `(X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)` of `Ω^p` read as an `f⁻¹𝒪_S`-module.
* `AlgebraicGeometry.Scheme.Hom.deRhamDerivedMulShift`: the shifted multiplication
  `Ω^• ⊗^L Ω^•[m] ⟶ Ω^•[m]`.
* `AlgebraicGeometry.Scheme.Hom.deRhamPoincarePairing`: the pairing `(ξ, ξ') ↦ t(ξ ∪ ξ')` on
  `Rf_*Ω^• ⊗^L Rf_*(Ω^•[m])`.
* `AlgebraicGeometry.RelativeDualitySituation.IsDeRhamPoincareTrace`: the property of `t` in
  [Stacks, Tag 0G8K].

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
* [Stacks Project, Tag 0FU6](https://stacks.math.columbia.edu/tag/0FU6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Stacks.StandardDerivedModel
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **`Rf_*Ω^•_{X/S}` in `D(𝒪_S)`**: the derived direct image of the relative de Rham complex along
`(X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)`. -/
abbrev deRhamDirectImage :=
  (derivedPushforward (Stacks.DeRhamDirectImage.inverseImageBaseProjection f)).obj
    (Scheme.deRhamDerived f)

/-- **The relative cup product `Rf_*Ω^•_{X/S} ⊗^L Rf_*Ω^•_{X/S} ⟶ Rf_*Ω^•_{X/S}`** in `D(𝒪_S)` of
[Stacks, Tag 0FU6], for the morphism `(X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)`. -/
def deRhamDirectImageCup :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj f.deRhamDirectImage).obj
        f.deRhamDirectImage ⟶ f.deRhamDirectImage :=
  SheafOfModules.deRhamRelativeCupProduct _ _
    (Stacks.DeRhamDirectImage.inverseImageBaseProjection f)

/-- The direct image along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` is right exact. -/
instance preservesFiniteColimits_modulePushforward_toInverseImageBase :
    PreservesFiniteColimits (RingedSpaceModuleAdjunction.modulePushforward
      (Stacks.DeRhamDirectImage.toInverseImageBase f)) :=
  Stacks.DeRhamDirectImage.preservesFiniteColimits_pushforward_toInverseImageBase f

/-- **`Rf_*Ω^p_{X/S}` read along `(X, f⁻¹𝒪_S)`**: the derived direct image of the `𝒪_X`-module
`Ω^p_{X/S}` placed in degree zero is the derived direct image along `(X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)` of its
restriction of scalars to `f⁻¹𝒪_S`, also placed in degree zero. -/
def formsDirectImageIso (p : ℤ) :
    (derivedPushforward f.toLRSHom.toShHom).obj (f.formsInDegreeZero p) ≅
      (derivedPushforward (Stacks.DeRhamDirectImage.inverseImageBaseProjection f)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((RingedSpaceModuleAdjunction.modulePushforward
            (Stacks.DeRhamDirectImage.toInverseImageBase f)).obj
              (relativeDifferentialForms f p))) :=
  eqToIso (congrArg (fun g => (derivedPushforward g).obj (f.formsInDegreeZero p))
      (Stacks.DeRhamDirectImage.toInverseImageBase_comp f).symm) ≪≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
      (Stacks.DeRhamDirectImage.toInverseImageBase f)
      (Stacks.DeRhamDirectImage.inverseImageBaseProjection f)).symm.app _ ≪≫
    (derivedPushforward (Stacks.DeRhamDirectImage.inverseImageBaseProjection f)).mapIso
      ((derivedPushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm ≪≫
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardSingleIso
          (Stacks.DeRhamDirectImage.toInverseImageBase f)).app _).symm)

/-- **The shifted multiplication `Ω^• ⊗^L Ω^•[m] ⟶ Ω^•[m]`** in `D(X, f⁻¹𝒪_S)`: the commutation of
the derived tensor product with the shift in its second variable followed by the shift of the
derived wedge multiplication of the de Rham complex. -/
def deRhamDerivedMulShift (m : ℤ) :
    ((derivedTensorProductFunctor (Stacks.DeRhamDirectImage.inverseImageBase f).sheaf).obj
        (Scheme.deRhamDerived f)).obj ((Scheme.deRhamDerived f)⟦m⟧) ⟶
      (Scheme.deRhamDerived f)⟦m⟧ :=
  letI := (canonicalDerivedTensorProduct (Stacks.DeRhamDirectImage.inverseImageBase f).sheaf
    ).commShift_right (Scheme.deRhamDerived f)
  (((derivedTensorProductFunctor (Stacks.DeRhamDirectImage.inverseImageBase f).sheaf).obj
      (Scheme.deRhamDerived f)).commShiftIso m).hom.app (Scheme.deRhamDerived f) ≫
    (SheafOfModules.deRhamDerivedMul _ _)⟦m⟧'

/-- **The pairing `(ξ, ξ') ↦ t(ξ ∪ ξ')` of [Stacks, Tag 0G8K]** on
`Rf_*Ω^•_{X/S} ⊗^L Rf_*(Ω^•_{X/S}[m]) ⟶ 𝒪_S`, for `t : Rf_*(Ω^•_{X/S}[m]) ⟶ 𝒪_S`: the relative cup
product of [Stacks, Tag 0B68] along `(X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)`, followed by `Rf_*` of the shifted
multiplication `Ω^• ⊗^L Ω^•[m] ⟶ Ω^•[m]` and by `t`. The shift is taken inside `Rf_*`, as for the
trace of [Stacks, Tag 0G8I]. -/
def deRhamPoincarePairing (m : ℤ)
    (t : (derivedPushforward (Stacks.DeRhamDirectImage.inverseImageBaseProjection f)).obj
        ((Scheme.deRhamDerived f)⟦m⟧) ⟶ (Stacks.Duality.derivedStructureSheafInDegree S 0).obj) :
    ((derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite S.sheaf).O).obj
        f.deRhamDirectImage).obj
        ((derivedPushforward (Stacks.DeRhamDirectImage.inverseImageBaseProjection f)).obj
          ((Scheme.deRhamDerived f)⟦m⟧)) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj :=
  Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct
      (Stacks.DeRhamDirectImage.inverseImageBaseProjection f) (Scheme.deRhamDerived f)
      ((Scheme.deRhamDerived f)⟦m⟧) ≫
    (derivedPushforward (Stacks.DeRhamDirectImage.inverseImageBaseProjection f)).map
      (f.deRhamDerivedMulShift m) ≫ t

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- **The property of `t : Rf_*(Ω^•_{X/S}[2n]) ⟶ 𝒪_S` in [Stacks, Tag 0G8K]**: the pairing
`Rf_*Ω^•_{X/S} ⊗^L Rf_*(Ω^•_{X/S}[2n]) ⟶ 𝒪_S`, `(ξ, ξ') ↦ t(ξ ∪ ξ')`, is a perfect pairing of
perfect complexes on `S`. A map `R^{2n}f_*Ω^•_{X/S} ⟶ 𝒪_S` is the same as such a `t`, since
`Rf_*(Ω^•_{X/S}[2n])` has no cohomology in positive degrees. -/
def IsDeRhamPoincareTrace
    (t : (derivedPushforward (Stacks.DeRhamDirectImage.inverseImageBaseProjection D.f)).obj
        ((Scheme.deRhamDerived D.f)⟦(2 * D.n : ℤ)⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj) : Prop :=
  IsPerfectDerivedPairing
    (Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction
      (Stacks.SheafOfModules.ringedSite D.S.sheaf))
    (D.f.deRhamPoincarePairing (2 * D.n) t)

end AlgebraicGeometry.RelativeDualitySituation
