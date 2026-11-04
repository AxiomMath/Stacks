module

public import StacksFrontier.AlgebraicGeometry.Assembly.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.FundamentalClassDeterminantDual
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedTensorShiftedInverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank

/-!
# The determinant of the normal sheaf of the diagonal of a smooth morphism

Let `f : X ⟶ S` be smooth of relative dimension `d`, with diagonal `Δ : X ⟶ X ×_S X`. The conormal
sheaf `𝒞_Δ` is `Ω_{X/S}` ([Stacks, Tag 08S2]), so it is finite locally free of rank `d`, and the
determinant pairing identifies `∧^d 𝒩_Δ ⊗ ∧^d 𝒞_Δ` with `𝒪_X`, where `𝒩_Δ = 𝒞_Δ^∨` is the
normal sheaf. Consequently an object `ω` of `D(𝒪_X)` with `ω ⊗ᴸ ∧^d 𝒩_Δ[-d] ≅ 𝒪_X` is
`∧^d Ω_{X/S}[d]`.

## Main results

* `Stacks.Duality.isFiniteLocallyFreeOfRank_conormalSheaf_diagonal` — `𝒞_Δ` has rank `d`.
* `Stacks.Duality.exteriorPowerNormalTensorConormalDiagonalIso` —
  `∧^d 𝒩_Δ ⊗ ∧^d 𝒞_Δ ≅ 𝒪_X`.
* `Stacks.Duality.isoSingleFunctorExteriorPowerOfDerivedTensorIso` — the cancellation
  `ω ⊗ᴸ ∧^d 𝒩_Δ[-d] ≅ 𝒪_X ⟹ ω ≅ ∧^d Ω_{X/S}[d]`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The conormal sheaf of the diagonal of a morphism smooth of relative dimension `d` is finite
locally free of rank `d`. -/
theorem isFiniteLocallyFreeOfRank_conormalSheaf_diagonal :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := X.ringCatSheaf) (Stacks.Conormal.conormalSheaf (pullback.diagonal f)) d :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal f)
    (Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials f d)

/-- **The determinant pairing of the diagonal**, `∧^d 𝒩_Δ ⊗ ∧^d 𝒞_Δ ≅ 𝒪_X`, for `f` smooth of
relative dimension `d`, where `𝒩_Δ` is the normal sheaf and `𝒞_Δ` the conormal sheaf of the
diagonal. -/
def exteriorPowerNormalTensorConormalDiagonalIso :
    Scheme.Modules.tensorObjRingedSpace X
        (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf (pullback.diagonal f)) d)
        (Scheme.Modules.exteriorPower (Stacks.Conormal.conormalSheaf (pullback.diagonal f)) d) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf)
      (Stacks.Conormal.conormalSheaf (pullback.diagonal f)) d :=
    isFiniteLocallyFreeOfRank_conormalSheaf_diagonal f d
  @asIso _ _ _ _ (detDualPairing (X := X) (Osharp := X.sheaf)
    (_root_.SheafOfModules.algebras _ (Stacks.Duality.dualMod (X := X) (Osharp := X.sheaf)
      (Stacks.Conormal.conormalSheaf (pullback.diagonal f))))
    (_root_.SheafOfModules.algebras _ (Stacks.Conormal.conormalSheaf (pullback.diagonal f))) d)
    (isIso_detDualPairing _ _ d)

/-- For `f` smooth of relative dimension `d`, an object `ω` of `D(𝒪_X)` with
`ω ⊗ᴸ ∧^d 𝒩_Δ[-d] ≅ 𝒪_X` is `∧^d Ω_{X/S}[d]`. -/
def isoSingleFunctorExteriorPowerOfDerivedTensorIso (ω : DerivedCategory X.Modules)
    (h : ((derivedTensor X).obj ω).obj ((DerivedCategory.singleFunctor X.Modules d).obj
        (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf (pullback.diagonal f)) d)) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) :
    ω ≅ (DerivedCategory.singleFunctor X.Modules (-d)).obj
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) d) :=
  haveI := isFiniteLocallyFreeOfRank_conormalSheaf_diagonal f d
  have hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.exteriorPower (Stacks.Conormal.conormalSheaf (pullback.diagonal f)) d) 1 := by
    simpa only [Nat.choose_self] using
      Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower _ d d
  have hfree : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Scheme.Modules.exteriorPower (Stacks.Conormal.conormalSheaf (pullback.diagonal f)) d) :=
    ⟨(AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
      (hM := hrank)).exists_isFiniteLocallyFreeData⟩
  isoSingleFunctorOfDerivedTensorIso ω _ _ hfree
      (exteriorPowerNormalTensorConormalDiagonalIso f d) d h ≪≫
    (DerivedCategory.singleFunctor X.Modules (-d)).mapIso
      ((Scheme.Modules.exteriorPowerFunctor X d).mapIso
        (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal f).symm)

end Stacks.Duality
