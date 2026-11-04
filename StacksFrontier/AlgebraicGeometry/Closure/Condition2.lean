module

public import StacksFrontier.AlgebraicGeometry.Closure.FibreRing
public import StacksFrontier.AlgebraicGeometry.SmoothAtClosedFibre.Basic
public import StacksFrontier.AlgebraicGeometry.SmoothAtRingCriterion.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Condition (2) of Tag 01V9 implies condition (1)

Condition (2) of Stacks Tag 01V9 is flatness of the induced map of local rings
`𝒪_{S,f x} → 𝒪_{X,x}` together with smoothness, at the point determined by `x`, of the
scheme-theoretic fibre of `f` through `x` over `κ(f x)`.  This file proves that it implies
condition (1), smoothness of `f` at `x`, for `f` locally of finite presentation.

## Main results

* `Stacks.Tag01V9Closure.formallySmooth_residueField_tensor_stalk`: if the fibre of `f` through
  `x` is smooth at `x`, then `κ(f x) ⊗_{𝒪_{S,f x}} 𝒪_{X,x}` is formally smooth over `κ(f x)`.
* `Stacks.Tag01V9Closure.condition2_imp_condition1`: condition (2) implies condition (1).

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 00TF](https://stacks.math.columbia.edu/tag/00TF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct IsLocalRing
open Stacks.SmoothAtJacobian

universe u

namespace Stacks.Tag01V9Closure

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- If the fibre of `f` through `x`, as a scheme over `κ(f x)`, is smooth at `x`, then
`κ(f x) ⊗_{𝒪_{S,f x}} 𝒪_{X,x}` is a formally smooth `κ(f x)`-algebra. -/
public theorem formallySmooth_residueField_tensor_stalk [LocallyOfFinitePresentation f]
    (h : InfinitesimalLifting.SmoothAt (f.fiberToSpecResidueField (f x)) (f.asFiber x)) :
    letI : Algebra ↥(S.presheaf.stalk (f x)) ↥(X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    Algebra.FormallySmooth (ResidueField ↥(S.presheaf.stalk (f x)))
      (ResidueField ↥(S.presheaf.stalk (f x)) ⊗[↥(S.presheaf.stalk (f x))]
        ↥(X.presheaf.stalk x)) := by
  let _ : Algebra ↥(S.presheaf.stalk (f x)) ↥(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have hkey : ∀ r : ↥(S.presheaf.stalk (f x)),
      (Stacks.SmoothAtClosedFibre.kappaToFibreStalk f x).hom ((S.residue (f x)).hom r)
        = ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
            ((X.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber x).symm)).hom
              ((f.stalkMap x).hom r)) := fun r => by
    simpa using congrArg (fun t : S.presheaf.stalk (f x) ⟶
        (f.fiber (f x)).presheaf.stalk (f.asFiber x) => t.hom r)
      (Stacks.SmoothAtClosedFibre.residue_kappaToFibreStalk f x)
  exact formallySmooth_residueField_tensor_of_quotient
    (Stacks.SmoothAtClosedFibre.kappaToFibreStalk f x).hom
    (quotientStalkEquivFiberStalk f x)
    (fun r => (quotientStalkEquivFiberStalk_mk f x _).trans (hkey r).symm)
    (Stacks.SmoothAtClosedFibre.formallySmooth_kappaToFibreStalk f x h)

/-- For a morphism locally of finite presentation, if the induced map of local rings at `x` is
flat and the scheme-theoretic fibre through `x` is smooth at `x` over the residue field of `f x`,
then `f` is smooth at `x`. -/
@[sga "3 XV 1.1" "partial"]
public theorem condition2_imp_condition1 [LocallyOfFinitePresentation f]
    (h : Condition2 f x) : Condition1 f x := by
  obtain ⟨hflat, hfib⟩ := h
  obtain ⟨V, hV, hfxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := f x) (U := ⊤) (by simp)
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ V) hfxV
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have _ : Algebra.FinitePresentation Γ(S, V) Γ(X, U) := f.finitePresentation_appLE hV hU hUV
  have _ : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.LiesOver
      (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU).1).symm⟩
  let _ : Algebra Γ(X, U) ↥(X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (U := U) ⟨x, hxU⟩
  have _ : IsLocalization.AtPrime ↥(X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  let _ : Algebra Γ(S, V) ↥(S.presheaf.stalk (f x)) :=
    S.presheaf.algebra_section_stalk (U := V) ⟨f x, hUV hxU⟩
  have _ : IsLocalization.AtPrime ↥(S.presheaf.stalk (f x))
      (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal := hV.isLocalization_stalk ⟨f x, hUV hxU⟩
  let _ : Algebra ↥(S.presheaf.stalk (f x)) ↥(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let _ : Algebra Γ(S, V) ↥(X.presheaf.stalk x) :=
    (f.appLE V U hUV ≫ X.presheaf.germ U x hxU).hom.toAlgebra
  have _ : IsScalarTower Γ(S, V) Γ(X, U) ↥(X.presheaf.stalk x) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra]
    exact CommRingCat.hom_comp _ _
  have _ : IsScalarTower Γ(S, V) ↥(S.presheaf.stalk (f x)) ↥(X.presheaf.stalk x) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom
      (Stacks.RelativeDifferentialStalkMap.appLE_germ_eq_germ_stalkMap f x U V hxU hUV)
  have _ : Module.Flat ↥(S.presheaf.stalk (f x)) ↥(X.presheaf.stalk x) := hflat
  have _ : IsLocalHom (algebraMap ↥(S.presheaf.stalk (f x)) ↥(X.presheaf.stalk x)) :=
    (inferInstance : IsLocalHom (f.stalkMap x).hom)
  have _ : Algebra.FormallySmooth (ResidueField ↥(S.presheaf.stalk (f x)))
      (ResidueField ↥(S.presheaf.stalk (f x)) ⊗[↥(S.presheaf.stalk (f x))]
        ↥(X.presheaf.stalk x)) := formallySmooth_residueField_tensor_stalk f x hfib
  exact (condition1_iff_mem_smoothLocus f x).mpr <| Scheme.Hom.mem_smoothLocus.mpr <|
    formallySmooth_of_formallySmooth_residueField_tensor
      (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
      ↥(S.presheaf.stalk (f x)) ↥(X.presheaf.stalk x)

end Stacks.Tag01V9Closure

end
