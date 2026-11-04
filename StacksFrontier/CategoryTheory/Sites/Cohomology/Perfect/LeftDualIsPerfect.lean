module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualIsTheDerivedDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualPseudoCoherenceStep
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualLocalTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessCriterionGeneralIff
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomProducts
import StacksCore.Tactic.StacksAttribute

/-!
# An object of `D(O)` with a left dual is perfect

Let `(C, O)` be a ringed site and let `M` be an object of `D(O)` which has a left dual `N` in the
symmetric monoidal category `D(O)` of Stacks 0FPT. Then `M` is perfect, and `N` is the dual
object `RSheafHom(M, O)` of Example 0FPU. This is Stacks 0FPV.

The second assertion is `AlgebraicGeometry.RingedSite.isIso_derivedDualToLeftDual`. The first is
proved here, following the source. Restricting the pairing to the members of a covering, `M` is
locally bounded above (`AlgebraicGeometry.RingedSite.exists_presieve_isLE`), and perfectness is
local (`AlgebraicGeometry.RingedSite.isPerfect_of_locally_general`), so one may assume `M`
concentrated in degrees `≤ b`. Then `M` locally has finite Tor dimension
(`AlgebraicGeometry.RingedSite.locallyHasFiniteTorDimension_of_exactPairing_of_isLE`) and is
pseudo-coherent (`AlgebraicGeometry.RingedSite.isPseudoCoherent_of_exactPairing_of_isLE`), and the
criterion of Stacks 08G8 concludes.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_of_exactPairing_of_isLE`: a bounded above object of
  `D(O)` with a left dual is perfect.
* `AlgebraicGeometry.RingedSite.isPerfect_of_exactPairing`: an object of `D(O)` with a left dual
  is perfect.
* `AlgebraicGeometry.RingedSite.isPerfect_and_isIso_derivedDualToLeftDual`: **Stacks 0FPV**, both
  assertions.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules.DerivedMonoidal
open Stacks.SheafOfModules.DerivedTensorProduct
open Stacks.DerivedTensor.ExtensionByZero (restriction)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance] HasDerivedCategory.standard

/-- The tensor bifunctor of a ringed site is additive in its first variable. -/
local instance perfTensorAdditive (Y : RingedSite.{u, u, u}) [HasSheafify Y.J AddCommGrpCat.{u}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive _

/-- The tensor bifunctor of a ringed site is additive in its second variable. -/
local instance perfTensorObjAdditive (Y : RingedSite.{u, u, u})
    [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive _ A

/-- Total complexes of the tensor bifunctor of a ringed site exist. -/
local instance perfHasMapBifunctor (Y : RingedSite.{u, u, u})
    [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ) :=
  hasMapBifunctor_sheafTensor Y K L

section Bounded

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] pcStepSliceHasSheafify pcStepSliceWEq pcStepIterHasSheafify pcStepIterWEq

/-- Sheafification on an iterated slice. -/
local instance perfIterHasSheafify (U : X.C) (V : Over U) :
    HasSheafify ((X.J.over U).over V) AddCommGrpCat.{u} :=
  Stacks.SheafOfModules.iteratedSliceHasSheafify AddCommGrpCat.{u} V

/-- Local bijectivity of the weak equivalences on an iterated slice. -/
local instance perfIterWEq (U : X.C) (V : Over U) :
    ((X.J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  Stacks.SheafOfModules.iteratedSliceWEqualsLocallyBijective AddCommGrpCat.{u} V

/-- Sheafification on a threefold slice. -/
local instance perfTripleHasSheafify (U : X.C) (V : (X.over U).C) (W : Over V) :
    HasSheafify (((X.over U).J.over V).over W) AddCommGrpCat.{u} :=
  Stacks.SheafOfModules.iteratedSliceHasSheafify AddCommGrpCat.{u} (J := (X.over U).J) W

/-- Local bijectivity of the weak equivalences on a threefold slice. -/
local instance perfTripleWEq (U : X.C) (V : (X.over U).C) (W : Over V) :
    (((X.over U).J.over V).over W).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  Stacks.SheafOfModules.iteratedSliceWEqualsLocallyBijective AddCommGrpCat.{u}
    (J := (X.over U).J) W

/-- **A bounded above object of `D(O)` with a left dual is perfect.** It is pseudo-coherent,
by `isPseudoCoherent_of_exactPairing_of_isLE`, and locally has finite Tor dimension, by
`locallyHasFiniteTorDimension_of_exactPairing_of_isLE`, so it is perfect by Stacks 08G8. -/
theorem isPerfect_of_exactPairing_of_isLE
    (M N : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O)
    (pair : letI := derivedMonoidal X.O; ExactPairing M N) (b : ℤ) (hb : M.IsLE b) :
    X.IsPerfect M :=
  isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension_general
    (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over U)) M
    (isPseudoCoherent_of_exactPairing_of_isLE X M N pair b hb)
    (locallyHasFiniteTorDimension_of_exactPairing_of_isLE X M N pair b hb _)

/-- **An object of `D(O)` with a left dual is perfect**, the first assertion of Stacks 0FPV.
Along a covering of each object of `C` the restriction of `M` is bounded above, by
`exists_presieve_isLE`, and keeps a left dual, by `exactPairingRestrict`; so it is perfect by
`isPerfect_of_exactPairing_of_isLE`, and perfectness is local. -/
theorem isPerfect_of_exactPairing
    (M N : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O)
    (pair : letI := derivedMonoidal X.O; ExactPairing M N) :
    X.IsPerfect M := by
  refine isPerfect_of_locally_general X M fun U => ?_
  obtain ⟨S, hS, hdata⟩ := exists_presieve_isLE X U M N pair
  refine ⟨S, hS, fun {W} h hh => ?_⟩
  obtain ⟨b, hb⟩ := hdata h hh
  exact isPerfect_of_exactPairing_of_isLE (X.over W) _ _ (exactPairingRestrict X W M N pair) b hb

/-- **Stacks 0FPV.** Let `(C, O)` be a ringed site and let `M` be an object of `D(O)` with a left
dual `N` in the symmetric monoidal category `D(O)` of Stacks 0FPT. Then `M` is perfect, and the
left dual is the object `M^∨ = RSheafHom(M, O)` of Example 0FPU: the morphism `M^∨ ⟶ N` which the
pairing matches with the evaluation of Example 0FPU is an isomorphism, and it carries the
evaluation `ε` of the pairing to the evaluation `ε'` of Example 0FPU.

The first assertion is `isPerfect_of_exactPairing`, the second `isIso_derivedDualToLeftDual`
together with `whiskerRight_derivedDualToLeftDual`. -/
@[stacks 0FPV "both assertions: `M` is perfect, and the left dual `N` is the object \
`RSheafHom(M, O)` of Example 0FPU, by the morphism `derivedDualToLeftDual` which the pairing \
matches with the evaluation of Example 0FPU and which carries the evaluation of the pairing to \
that of Example 0FPU. The monoidal structure on `D(O)` is the one of \
Tag 0FPT, `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal`, a left dual is Mathlib's \
`CategoryTheory.ExactPairing` (Definition 0FFP), and perfect is \
`AlgebraicGeometry.RingedSite.IsPerfect` (Definition 08G5)"]
theorem isPerfect_and_isIso_derivedDualToLeftDual
    (M N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (pair : letI := derivedMonoidal X.O; ExactPairing M N) :
    X.IsPerfect M ∧
      (letI := derivedMonoidal X.O; letI := pair;
        IsIso (derivedDualToLeftDual M N) ∧
          derivedDualToLeftDual M N ▷ M ≫ ε_ M N = derivedDualEvaluationMonoidal M) :=
  ⟨isPerfect_of_exactPairing X M N pair,
    let := derivedMonoidal X.O; let := pair;
    ⟨isIso_derivedDualToLeftDual M N, whiskerRight_derivedDualToLeftDual M N⟩⟩

end Bounded

end AlgebraicGeometry.RingedSite

end
