module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductAdjunctFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointUnitalComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat

/-!
# The left adjoint of derived global sections on `A[-i]`, and tensoring with it

Let `(X, 𝒪_X)` be a ringed space, `A = Γ(X, 𝒪_X)` and `L ⊣ RΓ(X, -)` the adjunction of the
canonical one-point comparison of Section 0FKU. A class in `Hⁱ(X, K)` is a morphism
`L(A[-i]) ⟶ K` (`Stacks.Cohomology.DerivedGlobalCupProduct.classAdjunct`). This file identifies
the source: `L(A[-i]) ≅ 𝒪_X[-i]`, and deduces that tensoring with `L(A[-i])` is, up to a natural
isomorphism, the shift by `-i`; in particular it is fully faithful.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.pullbackBaseShiftIso`: `L(A[-i]) ≅ 𝒪_X[-i]`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.tensorSingleUnitIso`: `𝒪_X[-i] ⊗^𝐋 - ≅ (-)[-i]`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.tensorPullbackBaseShiftIso`:
  `L(A[-i]) ⊗^𝐋 - ≅ (-)[-i]`.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.bijective_map_tensorPullbackBaseShift`: tensoring
  with `L(A[-i])` is bijective on morphisms.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedSectionsLeftAdjoint
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-- Restricting the scalars of the free module of rank one along a ring isomorphism gives the
free module of rank one. -/
def restrictScalarsSelfIso {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S) ≅ ModuleCat.of R R :=
  letI : Module R S := Module.compHom S e.toRingHom
  LinearEquiv.toModuleIso (X₁ := S) (X₂ := R)
    { toFun := fun s ↦ e.symm s
      invFun := fun r ↦ e r
      map_add' := fun a b ↦ map_add _ a b
      map_smul' := fun r s ↦ by
        change e.symm (e r * s) = r * e.symm s
        rw [map_mul, RingEquiv.symm_apply_apply]
      left_inv := fun s ↦ e.apply_symm_apply s
      right_inv := fun r ↦ e.symm_apply_apply r }

/-- `π^♯ : Γ({*}, 𝒪) ≅ A` read on `A` itself: restricting the scalars of `A` along `π^♯` gives the
free module of rank one over `Γ({*}, 𝒪)`. -/
def basePointRestrictBaseIso :
    (basePointRestrict X).functor.obj (ModuleCat.of (baseRing X) (baseRing X)) ≅
      ModuleCat.of ↥((structureSheafRing (basePoint X)).obj.obj (op ⊤))
        ↥((structureSheafRing (basePoint X)).obj.obj (op ⊤)) :=
  restrictScalarsSelfIso (basePointRingEquiv X)

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **`L(A[-i]) ≅ 𝒪_X[-i]`.** -/
def pullbackBaseShiftIso (i : ℤ) :
    (onePointComparisonCanonical X).pullback.obj (baseShift X i) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) i).obj
        (SheafOfModules.unit (structureSheafRing X)) :=
  (derivedPullback (toBasePoint X)).mapIso
      ((basePointExtension X).mapIso
          (((basePointRestrict X).functor.mapDerivedCategorySingleFunctor i).app
              (ModuleCat.of (baseRing X) (baseRing X)) ≪≫
            (DerivedCategory.singleFunctor _ i).mapIso (basePointRestrictBaseIso X)) ≪≫
        ((Stacks.Cohomology.DerivedSectionsOnAPoint.onePointSectionsEquivalence
          ↥(baseRing X)).functor.mapDerivedCategorySingleFunctor i).app _ ≪≫
        (DerivedCategory.singleFunctor _ i).mapIso
          (Stacks.Cohomology.DerivedSectionsOnAPoint.onePointUnitSheafIso ↥(baseRing X)) ≪≫
        (((DerivedCategory.singleFunctors _).shiftIso (-i) i 0 (by omega)).app _).symm) ≪≫
    ((derivedPullback (toBasePoint X)).commShiftIso (-i)).app _ ≪≫
    (shiftFunctor _ (-i)).mapIso
      (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso (toBasePoint X)) ≪≫
    ((DerivedCategory.singleFunctors _).shiftIso (-i) i 0 (by omega)).app _

/-! ### Tensoring with `𝒪_X[-i]` is the shift by `-i` -/

/-- **Tensoring on the left with `V⟦m⟧` is tensoring with `V` followed by the shift by `m`**,
naturally in the second factor: the commutation of the derived tensor product with shifts in its
first variable, which is natural in the second variable. -/
def tensorShiftLeftIso (V : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (m : ℤ) :
    (derivedTensorProductFunctor X.sheaf).obj (V⟦m⟧) ≅
      (derivedTensorProductFunctor X.sheaf).obj V ⋙ shiftFunctor _ m :=
  letI := (canonicalDerivedTensorProduct X.sheaf).commShift₂
  NatIso.ofComponents
    (fun Y ↦ (((derivedTensorProductFunctor X.sheaf).flip.obj Y).commShiftIso m).app V)
    (fun g ↦ (NatTrans.shift_app_comm ((derivedTensorProductFunctor X.sheaf).flip.map g)
      m V).symm)

/-- **Tensoring with `𝒪_X[-i]` is the shift by `-i`.** -/
def tensorSingleUnitIso (i : ℤ) :
    (derivedTensorProductFunctor X.sheaf).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) i).obj
          (SheafOfModules.unit (structureSheafRing X))) ≅
      shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (-i) :=
  (derivedTensorProductFunctor X.sheaf).mapIso
      (((DerivedCategory.singleFunctors _).shiftIso (-i) i 0 (by omega)).app _).symm ≪≫
    tensorShiftLeftIso X _ (-i) ≪≫
    Functor.isoWhiskerRight
      (@MonoidalCategory.leftUnitorNatIso _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)) _ ≪≫
    Functor.leftUnitor _

/-- **Tensoring with `L(A[-i])` is the shift by `-i`**, up to a natural isomorphism. -/
def tensorPullbackBaseShiftIso (i : ℤ) :
    (derivedTensorProductFunctor X.sheaf).obj
        ((onePointComparisonCanonical X).pullback.obj (baseShift X i)) ≅
      shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (-i) :=
  (derivedTensorProductFunctor X.sheaf).mapIso (pullbackBaseShiftIso X i) ≪≫
    tensorSingleUnitIso X i

/-- **Tensoring with `L(A[-i])` is bijective on morphisms.** -/
theorem bijective_map_tensorPullbackBaseShift (i : ℤ)
    (Y Y' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    Function.Bijective (fun g : Y ⟶ Y' => ((derivedTensorProductFunctor X.sheaf).obj
      ((onePointComparisonCanonical X).pullback.obj (baseShift X i))).map g) :=
  ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor _ (-i))).ofIso
    (tensorPullbackBaseShiftIso X i).symm).map_bijective Y Y'

end Stacks.Cohomology.DerivedGlobalCupProduct

end
