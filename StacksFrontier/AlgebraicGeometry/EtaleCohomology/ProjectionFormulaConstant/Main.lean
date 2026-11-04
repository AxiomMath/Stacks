module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProjectionFormulaConstant.Devissage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Coproducts
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProjectionFormulaConstant.DirectSums
import StacksCore.Tactic.StacksAttribute

/-!
# Pulling a constant complex out of derived global sections (Stacks 0F12)

Let `X` be a quasi-compact and quasi-separated scheme with `cd(X) < ∞`, let `Λ` be a torsion
ring, and let `E ∈ D(X_étale, Λ)` and `K ∈ D(Λ)`. [Stacks, Tag 0F12] asserts

`RΓ(X, E ⊗^L_Λ K̲) = RΓ(X, E) ⊗^L_Λ K`

through the canonical map from right to left of Cohomology on Sites, Section 0943. That map is
the one of Equation 21.50.0.1 ([Stacks, Tag 0B56]) for the morphism of ringed topoi
`π : (X_étale, Λ̲) ⟶ (pt, Λ)`: `Rπ_*` is `RΓ(X, -)` and `Lπ^*K` is the constant complex `K̲`.
This file proves that it is an isomorphism.

## Main results

* `Stacks.EtaleCohomology.ProjectionFormulaConstant.isIso_projectionFormulaMap_toPoint`:
  **[Stacks, Tag 0F12]**.

## The proof

Write `T(K)` for invertibility of the map at `K`; More on Algebra, Remark 15.60.11
([Stacks, Tag 09PB]) reduces `T` for all `K` to three properties, checked here through
`Stacks.EtaleCohomology.ProjectionFormulaConstant.isIso_app_of_coproducts_of_unitShifts`:

1. both sides commute with direct sums: the derived tensor products do in the second variable
   ([Stacks, Tag 06YU]), `Lπ^*` does as a left adjoint, and `Rπ_*` does by [Stacks, Tag 0F11],
   which is where `cd(X) < ∞`, the qcqs hypothesis and the torsion of `Λ` are used
   (`preservesColimitsOfShape_derivedPushforward_toPoint`);
2. both sides are exact functors of `K` (Derived Categories, Lemma 13.4.3, [Stacks, Tag 014A]);
3. `T(Λ[k])` holds for every `k`: tensoring with a shift of the structure sheaf is an
   equivalence on both sides, so the abstract projection formula applies
   (`Stacks.Cohomology.ProjectionFormulaOfToposHom.isIso_projectionFormulaMap_unitShift`).

`K` lives in `D(pt, Λ)`, which is `D(Λ)` through the explicit equivalence
`Stacks.EtaleCohomology.EtaleCoefficients.pointDerivedEquivalence`; the dévissage is run in `D(Λ)`
and transported along it.

## Conventions

`D(X_étale, Λ)` is the derived category of sheaves of modules over the constant sheaf of rings
`Λ̲` on the small model of the small étale site, the shared ringed topos
`Stacks.EtaleCohomology.EtaleCoefficients.ringedTopos Λ X`, and `⊗^L` is its derived tensor
product `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, which is
`Stacks.EtaleCohomology.EtaleCoefficients.tensor`. `cd(X)` is
`AlgebraicGeometry.Scheme.etaleCohomologicalDimension` of [Stacks, Tag 0F0Q], on Mathlib's small
étale site. A torsion ring is a ring whose additive group is torsion, `IsAddTorsion Λ`.
The ring `Λ` lies in the universe `u + 1` of the étale sheaves of `X : Scheme.{u}`, a ring of a
smaller universe entering through `ULift`.

## References

* [Stacks Project, Tag 0F12](https://stacks.math.columbia.edu/tag/0F12)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
* [Stacks Project, Tag 0F11](https://stacks.math.columbia.edu/tag/0F11)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.ProjectionFormulaOfToposHom
open Stacks.PointRingedSite (ev pt)
open Stacks.EtaleCohomology.EtaleCoefficients

universe u

namespace Stacks.EtaleCohomology.ProjectionFormulaConstant

-- `Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap` is stated on the standard
-- model of the derived categories.
attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The target `K ↦ Rπ_*(E ⊗^L Lπ^*K)` of the projection formula map commutes with direct
sums. -/
theorem preservesColimitsOfShape_projectionFormulaTarget [CompactSpace X] [QuasiSeparatedSpace X]
    (hcd : Scheme.etaleCohomologicalDimension X < ⊤) (hΛ : IsAddTorsion Λ)
    (E : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O))) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      (derivedPullback (X := ringedTopos Λ X) (Y := pointRingedTopos Λ) (toPoint Λ X) ⋙
        (derivedTensorProductFunctor (ringedTopos Λ X).O).obj E ⋙
          derivedPushforward (X := ringedTopos Λ X) (Y := pointRingedTopos Λ)
            (toPoint Λ X)) := by
  have : PreservesColimitsOfShape (Discrete I)
      (derivedPullback (X := ringedTopos Λ X) (Y := pointRingedTopos Λ) (toPoint Λ X)) := by
    have := (derivedAdjunction (toPoint Λ X)).leftAdjoint_preservesColimits
    infer_instance
  have : PreservesColimitsOfShape (Discrete I)
      ((derivedTensorProductFunctor (ringedTopos Λ X).O).obj E) :=
    preservesColimitsOfShape_discrete_derivedTensorProductFunctor _ I E
  have := preservesColimitsOfShape_derivedPushforward_toPoint Λ X hcd hΛ I
  infer_instance


/-! ### The exactness data of the two sides -/

/-- The derived pullback to the étale site commutes with the shift. -/
@[instance_reducible]
def pullbackCommShift :
    (derivedPullback (X := ringedTopos Λ X) (Y := pointRingedTopos Λ)
      (toPoint Λ X)).CommShift ℤ :=
  derivedPullback_commShift (toPoint Λ X)

attribute [local instance] pullbackCommShift

/-- The derived direct image to the point commutes with the shift, as the right adjoint of the
derived pullback. -/
@[instance_reducible]
def pushforwardCommShift :
    (derivedPushforward (X := ringedTopos Λ X) (Y := pointRingedTopos Λ)
      (toPoint Λ X)).CommShift ℤ :=
  (derivedAdjunction (toPoint Λ X)).rightAdjointCommShift ℤ

attribute [local instance] pushforwardCommShift

/-- The derived adjunction to the point is compatible with the shift. -/
theorem adjunctionCommShift : (derivedAdjunction (toPoint Λ X)).CommShift ℤ :=
  (derivedAdjunction (toPoint Λ X)).commShift_of_leftAdjoint ℤ

attribute [local instance] adjunctionCommShift

/-- The derived pullback from the point is exact. -/
theorem pullback_isTriangulated :
    (derivedPullback (X := ringedTopos Λ X) (Y := pointRingedTopos Λ)
      (toPoint Λ X)).IsTriangulated :=
  derivedPullback_isTriangulated (toPoint Λ X)

attribute [local instance] pullback_isTriangulated

/-- The derived direct image to the point is exact. -/
theorem pushforward_isTriangulated :
    (derivedPushforward (X := ringedTopos Λ X) (Y := pointRingedTopos Λ)
      (toPoint Λ X)).IsTriangulated :=
  (derivedAdjunction (toPoint Λ X)).isTriangulated_rightAdjoint

attribute [local instance] pushforward_isTriangulated

/-- Tensoring with a fixed object on the étale side commutes with the shift. -/
@[instance_reducible]
def etaleTensorCommShift (E : DerivedCategory (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O))) :
    ((derivedTensorProductFunctor (ringedTopos Λ X).O).obj E).CommShift ℤ :=
  (canonicalDerivedTensorProduct (ringedTopos Λ X).O).commShift_right E

/-- Tensoring with a fixed object on the étale side is exact. -/
theorem etaleTensor_isTriangulated (E : DerivedCategory (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O))) :
    letI := etaleTensorCommShift Λ X E
    ((derivedTensorProductFunctor (ringedTopos Λ X).O).obj E).IsTriangulated :=
  (canonicalDerivedTensorProduct (ringedTopos Λ X).O).exact_right E

/-- Tensoring with a fixed object on the point commutes with the shift. -/
@[instance_reducible]
def pointTensorCommShift (A : DerivedCategory (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedTopos Λ).O))) :
    ((derivedTensorProductFunctor (pointRingedTopos Λ).O).obj A).CommShift ℤ :=
  (canonicalDerivedTensorProduct (pointRingedTopos Λ).O).commShift_right A

/-- Tensoring with a fixed object on the point is exact. -/
theorem pointTensor_isTriangulated (A : DerivedCategory (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedTopos Λ).O))) :
    letI := pointTensorCommShift Λ A
    ((derivedTensorProductFunctor (pointRingedTopos Λ).O).obj A).IsTriangulated :=
  (canonicalDerivedTensorProduct (pointRingedTopos Λ).O).exact_right A

attribute [local instance] etaleTensorCommShift etaleTensor_isTriangulated pointTensorCommShift
  pointTensor_isTriangulated

/-- The projection formula map is invertible at every shift of the image of the ring. -/
theorem isIso_projectionFormulaMap_pointDerived_single
    (E : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O))) (n : ℤ) :
    IsIso ((projectionFormulaNatTrans (toPoint Λ X) E).app (((pointDerived Λ).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of (pointScalars Λ) (Shrink.{u + 1} (pointScalars Λ)))))⟦n⟧)) :=
  ((projectionFormulaNatTrans (toPoint Λ X) E).isIso_app_iff_of_iso
    ((shiftFunctor _ n).mapIso (pointDerivedSingleIso Λ))).2
    (isIso_projectionFormulaMap_unitShift (toPoint Λ X) E n)

/-- Let `X` be a quasi-compact and quasi-separated scheme with `cd(X) < ∞` and let `Λ` be a
torsion ring. For `E ∈ D(X_étale, Λ)` and `K ∈ D(pt, Λ) = D(Λ)`, the
canonical map of Cohomology on Sites, Section 0943, for the structure morphism
`π : (X_étale, Λ̲) ⟶ (pt, Λ)`,

`RΓ(X, E) ⊗^L_Λ K = Rπ_*E ⊗^L_Λ K ⟶ Rπ_*(E ⊗^L_Λ Lπ^*K) = RΓ(X, E ⊗^L_Λ K̲)`,

is an isomorphism. -/
@[stacks 0F12 "the canonical map of Section 0943 for the structure morphism of `(X_étale, Λ̲)` to
the point ringed by `Λ`, on the shared ringed topos `EtaleCoefficients.ringedTopos`; `D(pt, Λ)`
is `D(Λ)` through `EtaleCoefficients.pointDerivedEquivalence`"]
theorem isIso_projectionFormulaMap_toPoint [CompactSpace X] [QuasiSeparatedSpace X]
    (hcd : Scheme.etaleCohomologicalDimension X < ⊤) (hΛ : IsAddTorsion Λ)
    (E : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O)))
    (K : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedTopos Λ).O))) :
    IsIso (projectionFormulaMap (toPoint Λ X) E K) := by
  have := preservesColimitsOfShape_projectionFormulaTarget Λ X hcd hΛ E
  have : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      ((derivedTensorProductFunctor (pointRingedTopos Λ).O).obj
        ((derivedPushforward (X := ringedTopos Λ X) (Y := pointRingedTopos Λ)
          (toPoint Λ X)).obj E)) :=
    fun I => preservesColimitsOfShape_discrete_derivedTensorProductFunctor
      (pointRingedTopos Λ).O I _
  have : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) (pointDerived Λ) :=
    fun I => inferInstance
  exact isIso_app_of_coproducts_of_unitShifts (R := pointScalars Λ) _ _
    (projectionFormulaNatTrans (toPoint Λ X) E) (pointDerived Λ)
    (isIso_projectionFormulaMap_pointDerived_single Λ X E) K

/-- [Stacks, Tag 0F12] with `K` taken in `D(Λ)`: the canonical map is invertible at the complex
of sheaves of modules on the point attached to any `K ∈ D(Λ)`. -/
theorem isIso_projectionFormulaMap_toPoint_pointDerived [CompactSpace X] [QuasiSeparatedSpace X]
    (hcd : Scheme.etaleCohomologicalDimension X < ⊤) (hΛ : IsAddTorsion Λ)
    (E : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O)))
    (K : DerivedCategory (ModuleCat.{u + 1} Λ)) :
    IsIso (projectionFormulaMap (toPoint Λ X) E ((pointDerived Λ).obj K)) :=
  isIso_projectionFormulaMap_toPoint Λ X hcd hΛ E _

end Stacks.EtaleCohomology.ProjectionFormulaConstant
