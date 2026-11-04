module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamDirectImageModel
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.PushedPairingShiftTarget
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# The pairings of [Stacks, Tag 0G8K] as pushed-forward pairings

Let `f : X ⟶ S` be a morphism of schemes and `F : (X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)` the morphism of ringed
spaces along which the de Rham complex is pushed forward. The relative cup product of
[Stacks, Tag 0B68] along `F` is natural in both variables and `Rf_*` is exact, so the relative cup
product, `Rf_*` and the derived tensor products form push data for pairings
(`CategoryTheory.Functor.PairingPushData`); shifting the second variable and the target by `m`
inside `Rf_*` gives the push data `AlgebraicGeometry.Scheme.Hom.deRhamPushData f m`. The pairing
`(ξ, ξ') ↦ t(ξ ∪ ξ')` of [Stacks, Tag 0G8K] is the push of the multiplication of `Ω^•_{X/S}` along
it, and every pairing of the induction in the proof of that tag is such a push, of a pairing
`K ⊗^L L ⟶ Ω^•_{X/S}` upstairs.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamPushDataBase`
* `AlgebraicGeometry.Scheme.Hom.deRhamPushData`

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamPoincarePairing_eq_pushedPairing`

## Implementation notes

The derived categories are taken at the standard model (`Stacks.StandardDerivedModel`), where the
relative cup product is stated. The shifts of `Rf_*` are those of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift`, and those of the
derived tensor products the field `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift₂`
of the canonical derived tensor product.

The derived tensor products live on `Stacks.DerivedTensor.RingedSite.DerivedModules`, the derived
category of modules over `Stacks.SheafOfModules.Tensor.ringSheaf` of the structure sheaf, while
`Rf_*` is stated on the derived category of modules over `structureSheafRing`. The two are
definitionally equal but not at instance transparency, so the shift datum and the exactness of
`Rf_*` are seated on `Rf_*` read as a functor between the `DerivedModules` (a `β`-redex of the
identity carries that reading of the type), and every shift in a statement is the shift of
`DerivedModules`.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward
  derivedPushforwardCommShift derivedPushforward_isTriangulated)
open Stacks.DerivedTensor.RingedSite (DerivedModules derivedTensorProductFunctor
  canonicalDerivedTensorProduct)
open Stacks.DeRhamDirectImage (inverseImageBase inverseImageBaseProjection)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The push data of the relative cup product along `(X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)`**: `Rf_*` in both
variables, the relative cup product of [Stacks, Tag 0B68] and its naturality. -/
def deRhamPushDataBase :
    Functor.PairingPushData (derivedTensorProductFunctor (inverseImageBase f).sheaf)
      (derivedTensorProductFunctor S.toRingedSpace.sheaf)
      (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection f)) :=
  letI : ((fun F : DerivedModules.{u + 1, u} (inverseImageBase f).sheaf ⥤
      DerivedModules.{u + 1, u} S.toRingedSpace.sheaf => F)
        (derivedPushforward (inverseImageBaseProjection f))).CommShift ℤ :=
    derivedPushforwardCommShift (inverseImageBaseProjection f)
  haveI : ((fun F : DerivedModules.{u + 1, u} (inverseImageBase f).sheaf ⥤
      DerivedModules.{u + 1, u} S.toRingedSpace.sheaf => F)
        (derivedPushforward (inverseImageBaseProjection f))).IsTriangulated :=
    derivedPushforward_isTriangulated (inverseImageBaseProjection f)
  letI : ∀ Z, ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj Z).CommShift ℤ :=
    fun Z => (canonicalDerivedTensorProduct S.toRingedSpace.sheaf).commShift_right Z
  haveI : ∀ Z, ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj Z).IsTriangulated :=
    fun Z => (canonicalDerivedTensorProduct S.toRingedSpace.sheaf).exact_right Z
  Functor.PairingPushData.ofIsTriangulated
    (derivedPushforward (inverseImageBaseProjection f))
    (derivedPushforward (inverseImageBaseProjection f))
    (Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct (inverseImageBaseProjection f))
    (fun e L => Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_natural_left _ e L)
    (fun K _ _ e =>
      Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_natural_right _ K e)

/-- **The push data of the pairings of [Stacks, Tag 0G8K]**: the relative cup product along
`(X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)` with the second variable and the target shifted by `m` inside `Rf_*`. -/
def deRhamPushData (m : ℤ) :
    Functor.PairingPushData (derivedTensorProductFunctor (inverseImageBase f).sheaf)
      (derivedTensorProductFunctor S.toRingedSpace.sheaf)
      (shiftFunctor (DerivedModules.{u + 1, u} (inverseImageBase f).sheaf) m ⋙
        derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection f)) :=
  letI := (canonicalDerivedTensorProduct (inverseImageBase f).sheaf
    ).commShift₂
  letI : ∀ Z, ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj Z).CommShift ℤ :=
    fun Z => (canonicalDerivedTensorProduct S.toRingedSpace.sheaf).commShift_right Z
  haveI : ∀ Z, ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj Z).IsTriangulated :=
    fun Z => (canonicalDerivedTensorProduct S.toRingedSpace.sheaf).exact_right Z
  (deRhamPushDataBase f).shiftTarget m

/-- **The pairing `(ξ, ξ') ↦ t(ξ ∪ ξ')` of [Stacks, Tag 0G8K] is pushed forward**: it is the push
of the multiplication `Ω^• ⊗^L Ω^• ⟶ Ω^•` of the de Rham complex along `deRhamPushData f m`. -/
theorem deRhamPoincarePairing_eq_pushedPairing (m : ℤ)
    (t : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection f)).obj
        ((shiftFunctor (DerivedModules.{u + 1, u} (inverseImageBase f).sheaf) m).obj
          (Scheme.deRhamDerived f)) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj) :
    f.deRhamPoincarePairing m t =
      (f.deRhamPushData m).pushedPairing t (SheafOfModules.deRhamDerivedMul _ _) := by
  let := (canonicalDerivedTensorProduct (inverseImageBase f).sheaf
    ).commShift₂
  let : ∀ Z, ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj Z).CommShift ℤ :=
    fun Z => (canonicalDerivedTensorProduct S.toRingedSpace.sheaf).commShift_right Z
  have : ∀ Z, ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj Z).IsTriangulated :=
    fun Z => (canonicalDerivedTensorProduct S.toRingedSpace.sheaf).exact_right Z
  refine Eq.trans ?_ (Functor.PairingPushData.pushedPairing_shiftTarget (deRhamPushDataBase f) m t
    (SheafOfModules.deRhamDerivedMul _ _)).symm
  rfl

end AlgebraicGeometry.Scheme.Hom
