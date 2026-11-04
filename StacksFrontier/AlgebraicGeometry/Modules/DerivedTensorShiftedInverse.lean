module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison

/-!
# Cancelling a shifted module against its tensor inverse in `D(𝒪_X)`

Let `X` be a scheme and let `L, L'` be `𝒪_X`-modules with `L'` finite locally free and
`L ⊗_{𝒪_X} L' ≅ 𝒪_X`. If an object `ω` of `D(𝒪_X)` satisfies `ω ⊗ᴸ L[-n] ≅ 𝒪_X`, then
`ω ≅ L'[n]`: the object `L[-n]` is invertible in the monoidal category `D(𝒪_X)`, with inverse
`L'[n]`.

## Main results

* `Stacks.Duality.derivedTensorSingleShiftIso`: `L[-n] ⊗ᴸ L'[n] ≅ 𝒪_X`.
* `Stacks.Duality.derivedTensorSingleSingleIso`: `L[-m] ⊗ᴸ L'[-n] ≅ (L ⊗ L')[-(m + n)]`.
* `Stacks.Duality.isoSingleFunctorOfDerivedTensorIso`: the cancellation
  `ω ⊗ᴸ L[-n] ≅ 𝒪_X ⟹ ω ≅ L'[n]`.

## Implementation notes

The shift `M[-n]` of a module is `DerivedCategory.singleFunctor _ n` applied to `M`. The
monoidal structure on `D(𝒪_X)` is `AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal`,
whose tensor product is `Stacks.Duality.derivedTensor X` and whose unit is the structure sheaf
in degree zero.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace Stacks.Duality

variable {X : Scheme.{u}}

/-- The derived tensor product on `X`, as a
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`. -/
abbrev derivedTensorProduct :
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf :=
  Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    (C := TopologicalSpace.Opens X) (J := Opens.grothendieckTopology X) X.toRingedSpace.sheaf

/-- `L[-n] ⊗ᴸ L'[n] ≅ 𝒪_X` when `L ⊗ L' ≅ 𝒪_X` and `L'` is finite locally free. -/
def derivedTensorSingleShiftIso (L L' : X.Modules)
    (hL' : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) L')
    (e : Scheme.Modules.tensorObjRingedSpace X L L' ≅ SheafOfModules.unit X.ringCatSheaf)
    (n : ℤ) :
    ((derivedTensor X).obj ((DerivedCategory.singleFunctor X.Modules n).obj L)).obj
        ((DerivedCategory.singleFunctor X.Modules (-n)).obj L') ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) :=
  let T := derivedTensorProduct (X := X)
  let A := (DerivedCategory.singleFunctor X.Modules 0).obj L
  let B := (DerivedCategory.singleFunctor X.Modules 0).obj L'
  ((derivedTensor X).mapIso
      (((DerivedCategory.singleFunctors X.Modules).shiftIso (-n) n 0 (by lia)).app L).symm).app
      _ ≪≫
    ((derivedTensor X).obj _).mapIso
      (((DerivedCategory.singleFunctors X.Modules).shiftIso n (-n) 0 (by lia)).app L').symm ≪≫
    ((Functor.commShiftIso (self := T.commShift_left _)
      (T.tensor.flip.obj ((shiftFunctor _ n).obj B)) (-n)).app A) ≪≫
    (shiftFunctor _ (-n)).mapIso
      ((Functor.commShiftIso (self := T.commShift_right A) (T.tensor.obj A) n).app B) ≪≫
    (shiftFunctorCompIsoId (DerivedCategory X.Modules) n (-n) (add_neg_cancel n)).app _ ≪≫
    (nonempty_derivedTensorSingleIso X T L L' hL').some ≪≫
    (DerivedCategory.singleFunctor X.Modules 0).mapIso e

/-- `L[-m] ⊗ᴸ L'[-n] ≅ (L ⊗ L')[-(m + n)]` when `L'` is finite locally free. -/
def derivedTensorSingleSingleIso (L L' : X.Modules)
    (hL' : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) L')
    (m n : ℤ) :
    ((derivedTensor X).obj ((DerivedCategory.singleFunctor X.Modules m).obj L)).obj
        ((DerivedCategory.singleFunctor X.Modules n).obj L') ≅
      (DerivedCategory.singleFunctor X.Modules (m + n)).obj
        (Scheme.Modules.tensorObjRingedSpace X L L') :=
  let T := derivedTensorProduct (X := X)
  let A := (DerivedCategory.singleFunctor X.Modules 0).obj L
  let B := (DerivedCategory.singleFunctor X.Modules 0).obj L'
  ((derivedTensor X).mapIso
      (((DerivedCategory.singleFunctors X.Modules).shiftIso (-m) m 0 (by lia)).app L).symm).app
      _ ≪≫
    ((derivedTensor X).obj _).mapIso
      (((DerivedCategory.singleFunctors X.Modules).shiftIso (-n) n 0 (by lia)).app L').symm ≪≫
    ((Functor.commShiftIso (self := T.commShift_left _)
      (T.tensor.flip.obj ((shiftFunctor _ (-n)).obj B)) (-m)).app A) ≪≫
    (shiftFunctor _ (-m)).mapIso
      ((Functor.commShiftIso (self := T.commShift_right A) (T.tensor.obj A) (-n)).app B) ≪≫
    ((shiftFunctorAdd' (DerivedCategory X.Modules) (-n) (-m) (-(m + n)) (by lia)).app _).symm ≪≫
    (shiftFunctor _ (-(m + n))).mapIso (nonempty_derivedTensorSingleIso X T L L' hL').some ≪≫
    ((DerivedCategory.singleFunctors X.Modules).shiftIso (-(m + n)) (m + n) 0 (by lia)).app _

/-- **Cancellation of a shifted invertible module.** If `ω ⊗ᴸ L[-n] ≅ 𝒪_X` in `D(𝒪_X)`, where
`L ⊗ L' ≅ 𝒪_X` with `L'` finite locally free, then `ω ≅ L'[n]`. -/
def isoSingleFunctorOfDerivedTensorIso (ω : DerivedCategory X.Modules) (L L' : X.Modules)
    (hL' : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) L')
    (e : Scheme.Modules.tensorObjRingedSpace X L L' ≅ SheafOfModules.unit X.ringCatSheaf)
    (n : ℤ)
    (h : ((derivedTensor X).obj ω).obj ((DerivedCategory.singleFunctor X.Modules n).obj L) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) :
    ω ≅ (DerivedCategory.singleFunctor X.Modules (-n)).obj L' :=
  letI := Scheme.Modules.canonicalDerivedMonoidal X
  let A := (DerivedCategory.singleFunctor X.Modules n).obj L
  let B := (DerivedCategory.singleFunctor X.Modules (-n)).obj L'
  have e' : A ⊗ B ≅ 𝟙_ (DerivedCategory X.Modules) := derivedTensorSingleShiftIso L L' hL' e n
  have h' : ω ⊗ A ≅ 𝟙_ (DerivedCategory X.Modules) := h
  (ρ_ ω).symm ≪≫ whiskerLeftIso ω e'.symm ≪≫ (α_ ω A B).symm ≪≫ whiskerRightIso h' B ≪≫ λ_ B

end Stacks.Duality
