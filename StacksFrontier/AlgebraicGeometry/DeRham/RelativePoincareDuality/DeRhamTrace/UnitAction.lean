module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.ProperSmoothBottomDifferential

/-!
# Multiplication by a global function on the relative de Rham complex

A global function `g ∈ Γ(X, 𝒪_X)` of a proper smooth `f : X ⟶ S` is closed (`dg = 0`, from
[Stacks, Tag 0G8H]), so by the Leibniz rule multiplication by `g` is a map of complexes
`Ω^•_{X/S} ⟶ Ω^•_{X/S}`. This is the action by which the trace of [Stacks, Tag 0G8K] is
unique up to a unit of `H^0(X, 𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.RelativeDualitySituation.deRhamComplexSMul`: multiplication by a global
  function as an endomorphism of `Ω^•_{X/S}`, and its images `deRhamDerivedSMul`,
  `deRhamDirectImageTopSMul` and `deRhamTopCohomologySMul` in the derived category, after
  `Rf_*(-[2n])` and on `R^{2n}f_*Ω^•_{X/S}`.

## Main results

* `AlgebraicGeometry.SheafOfModules.deRhamComplex_d_smul_of_closed`: for any de Rham
  differential, multiplication by a closed local function `a` (one with `d(a · 1) = 0`) commutes
  with `d` on local forms.
* `AlgebraicGeometry.RelativeDualitySituation.formsSMul_comm`: multiplication by a global function
  of a proper smooth `X/S` commutes with the relative de Rham differential.

## Implementation notes

`deRhamComplex_d_smul_of_closed` names the form `dω` by a separate variable `η` of the exterior
power, because `a · dω` only typechecks there: the arrow of the de Rham complex lands in the
exterior power with scalars restricted to `A`, which carries no `𝒪_X`-action.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
* [Stacks Project, Tag 0G8H](https://stacks.math.columbia.edu/tag/0G8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (DerivedModules derivedTensorProductFunctor
  canonicalDerivedTensorProduct)
open Stacks.DeRhamDirectImage (inverseImageBase inverseImageBaseProjection)

universe u

namespace AlgebraicGeometry.SheafOfModules

open TopologicalSpace

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **Multiplication by a closed function commutes with the de Rham differential.** If a local
section `a` of `𝒪_X` over `U` is closed, that is `d(a · 1) = 0`, then `d(a · ω) = a · dω` for every
local differential form `ω` over `U`: by the Leibniz rule
`d(ω ∧ a · 1) = dω ∧ a · 1 ± ω ∧ d(a · 1)`. -/
theorem deRhamComplex_d_smul_of_closed (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (a : X.sheaf.obj.obj U)
    (ha : ((deRhamComplex B D).d 0 1).val.app U (a • B.exterior.one.eval U) = 0)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower (p + 1)).val.obj U)
    (hη : ((deRhamComplex B D).d p (p + 1)).val.app U ω = η) :
    ((deRhamComplex B D).d p (p + 1)).val.app U (a • ω) = a • η := by
  have ha' : ((deRhamComplex B D).d 0 (0 + 1)).val.app U (a • B.exterior.one.eval U) = 0 := ha
  have hprod : ∀ (q : ℕ) (η : (B.exteriorPower q).val.obj U),
      formProduct B q 0 U η (a • B.exterior.one.eval U) = a • η :=
    fun q η => ((B.exterior.mul (q : ℤ) ((0 : ℕ) : ℤ)).map_smul_right U a η _).trans
      (congrArg (fun z => a • z) (eq_of_heq (B.exterior.mul_one (q : ℤ) U η)))
  have hL := d_formProduct B D p 0 U ω (a • B.exterior.one.eval U)
  rw [ha', hη, hprod (p + 1) η, hprod p ω] at hL
  simp only at hL
  refine hL.trans ?_
  refine (congrArg₂ (· + ·) rfl ((congrArg _ ?_).trans (smul_zero _))).trans (add_zero _)
  exact (congrArg (fun z => ((deRhamComplex B D).XIsoOfEq
    (show p + (0 + 1) = p + 0 + 1 by omega)).hom.val.app U z)
      (map_zero ((B.exterior.mul (p : ℤ) ((0 + 1 : ℕ) : ℤ)).app U ω))).trans (map_zero _)

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- (C0) multiplication by a global function commutes with the de Rham differential: global
functions are closed ([Stacks, Tag 0G8H]) and the Leibniz rule. -/
theorem formsSMul_comm (g : Γ(D.X, ⊤)) (p : ℕ) :
    D.formsSMul g p ≫ D.deRhamCx.d p (p + 1) = D.deRhamCx.d p (p + 1) ≫ D.formsSMul g (p + 1) := by
  let B := Scheme.Hom.deRhamAlgebras D.f
  let Dd := SheafOfModules.deRhamDifferential B
  let a : ∀ U : (D.X.Opens)ᵒᵖ, D.X.toRingedSpace.sheaf.obj.obj U := fun U =>
    Stacks.Cohomology.InvertibleDerived.globalRes (X := D.X.toRingedSpace) g U.unop
  have hclosed : ∀ U : (D.X.Opens)ᵒᵖ,
      ((SheafOfModules.deRhamComplex B Dd).d 0 1).val.app U
        (a U • B.exterior.one.eval U) = 0 := by
    intro U
    have htop := deRhamComplex_d_zero_app_preimage_eq_zero D.f ⊤ B Dd
    rw [Scheme.Hom.preimage_top] at htop
    let i : (Opposite.op (⊤ : D.X.Opens)) ⟶ U := (homOfLE le_top).op
    have hx : (B.exteriorPower 0).val.map i
        (a (Opposite.op ⊤) • B.exterior.one.eval (Opposite.op ⊤)) =
          a U • B.exterior.one.eval U := by
      refine ((B.exteriorPower 0).val.map_smul i _ _).trans ?_
      have h2 : (B.exteriorPower 0).val.map i (B.exterior.one.eval (Opposite.op ⊤)) =
          B.exterior.one.eval U := B.exterior.one.property i
      rw [h2]
      exact congrArg (fun z => z • B.exterior.one.eval U)
        (Stacks.Cohomology.InvertibleDerived.map_globalRes (X := D.X.toRingedSpace) g i)
    have hnat := PresheafOfModules.naturality_apply
      ((SheafOfModules.deRhamComplex B Dd).d 0 1).val i
      (a (Opposite.op ⊤) • B.exterior.one.eval (Opposite.op ⊤))
    rw [htop] at hnat
    rw [← hx]
    exact hnat.trans (map_zero _)
  ext U ω
  exact SheafOfModules.deRhamComplex_d_smul_of_closed B Dd p U (a U) (hclosed U) ω _ rfl

/-- Multiplication by a global function on `Ω^•_{X/S}`. -/
def deRhamComplexSMul (g : Γ(D.X, ⊤)) : D.deRhamCx ⟶ D.deRhamCx where
  f p := D.formsSMul g p
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact D.formsSMul_comm g i

/-- Multiplication by `g` on `Ω^•_{X/S}` in the derived category. -/
def deRhamDerivedSMul (g : Γ(D.X, ⊤)) : Scheme.deRhamDerived D.f ⟶ Scheme.deRhamDerived D.f :=
  DerivedCategory.Q.map (HomologicalComplex.extendMap (D.deRhamComplexSMul g)
    ComplexShape.embeddingUpNat)

/-- Multiplication by `g` on `Rf_*(Ω^•[2n])`. -/
def deRhamDirectImageTopSMul (g : Γ(D.X, ⊤)) : D.deRhamDirectImageTop ⟶ D.deRhamDirectImageTop :=
  (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).map
    ((shiftFunctor (DerivedModules.{u + 1, u} (inverseImageBase D.f).sheaf) (2 * D.n : ℤ)).map
      (D.deRhamDerivedSMul g))

/-- Multiplication by `g` on `R^{2n}f_*Ω^•`. -/
def deRhamTopCohomologySMul (g : Γ(D.X, ⊤)) : D.deRhamTopCohomology ⟶ D.deRhamTopCohomology :=
  (DerivedCategory.homologyFunctor D.S.Modules (2 * D.n : ℤ)).map
    ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).map
      (D.deRhamDerivedSMul g))

end AlgebraicGeometry.RelativeDualitySituation

end
