module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.StandardSmooth
public import StacksFrontier.AlgebraicGeometry.NumericalCriterion.Ring
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import Mathlib.RingTheory.Etale.Kaehler

/-!
# The relative cotangent space of Tag 01V9, computed on an affine chart

Condition (4) of Stacks Tag 01V9 bounds the dimension of
`Stacks.SmoothAtJacobian.relativeCotangentSpace f x`, the residue-field fibre at `x` of the stalk
of the sheaf of relative differentials.  Tag 00TT bounds the dimension of
`κ(𝔮) ⊗_A Ω_{A/R}`, for `A = Γ(X, U)` and `R = Γ(S, V)` the sections over affine charts and `𝔮`
the prime of `x` in `A`.  **This file proves those two dimensions equal.**

## Main results

* `Stacks.Tag01V9NumericalCriterion.finrank_relativeCotangentSpace_eq_chart`: the `κ(x)`-dimension
  of condition (4)'s relative cotangent space is the `κ(𝔮)`-dimension of
  `κ(𝔮) ⊗_{Γ(X,U)} Ω[Γ(X,U)⁄Γ(S,V)]`.

## Implementation notes

The identification is a chain of existing equivalences, all `𝒪_{X,x}`-linear before the base change
to `κ(x)`:

1. `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`, which is Tag 01V0
   at a point: the stalk of the sheaf of relative differentials is `Ω[𝒪_{X,x}⁄𝒪_{S,f x}]`;
2. `omega_localization_base` (Tag 00RT) at the multiplicative set defining `𝒪_{S,f x}`, which
   replaces the base `𝒪_{S,f x}` by `Γ(S, V)`, of which it is a localization;
3. `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`, which recognises `Ω[𝒪_{X,x}⁄Γ(S, V)]`
   as the base change of `Ω[Γ(X, U)⁄Γ(S, V)]` along the formally étale map `Γ(X, U) → 𝒪_{X,x}`;
4. `TensorProduct.AlgebraTensorModule.cancelBaseChange`, which collapses the two base changes
   `κ(x) ⊗_{𝒪_{X,x}} (𝒪_{X,x} ⊗_{Γ(X,U)} -)` into one.

The dimension is then read over `κ(𝔮)` rather than over `κ(x)` by
`Stacks.Tag01V9NumericalCriterion.finrank_tensor_residueField_eq`, the two fields being related by
`IsLocalRing.ResidueField.mapAlgEquiv` of `IsLocalization.algEquiv`: `𝒪_{X,x}` is a model of
`Localization.AtPrime 𝔮`, so its residue field is a model of `κ(𝔮)`.

Everything sits in a single declaration, with the eight algebra structures and four scalar towers
named by `let` inside the proof.  None of them is found by instance search — the stalk of a
presheaf of modules and `AlgebraicGeometry.Scheme.Modules` are definitions — and naming them in
the statement instead, by one `abbrev` apiece, does not work: the type of such an `abbrev` is
itself a `let`-expression, and the structures it introduces are then not visible to the next one
in the chain.  `Γ(S, V)` acts on `𝒪_{X,x}` through `𝒪_{S,f x}`, for which the tower is
`IsScalarTower.of_algebraMap_eq (fun _ => rfl)`; the tower through `Γ(X, U)` is the one that needs
`AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply`.

## References

* [Stacks Project, Tag 00RT](https://stacks.math.columbia.edu/tag/00RT)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.SmoothAtJacobian Stacks.RelativeDifferentialStalkMap
open scoped TensorProduct

universe u

namespace Stacks.Tag01V9NumericalCriterion

/-- **The dimension of the relative cotangent space of Tag 01V9, read on an affine chart.**  For
affine opens `U ∋ x` of the source and `V` of the target with `U ≤ f⁻¹ V`, the `κ(x)`-dimension of
condition (4)'s `Stacks.SmoothAtJacobian.relativeCotangentSpace f x` is the `κ(𝔮)`-dimension of
`κ(𝔮) ⊗_{Γ(X,U)} Ω[Γ(X,U)⁄Γ(S,V)]`, which is the module Tag 00TT bounds. -/
public theorem finrank_relativeCotangentSpace_eq_chart {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (U : X.affineOpens) (V : S.affineOpens) (hxU : x ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    Module.finrank ↥(X.residueField x) (relativeCotangentSpace f x) =
      Module.finrank (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.ResidueField
        ((U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.ResidueField ⊗[Γ(X, U.1)]
          Ω[Γ(X, U.1)⁄Γ(S, V.1)]) := by
  classical
  let _ : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  let _ : Algebra Γ(X, U.1) ↥(X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (U := U.1) ⟨x, hxU⟩
  let _ : Algebra Γ(S, V.1) ↥(S.presheaf.stalk (f x)) :=
    S.presheaf.algebra_section_stalk (U := V.1) ⟨f x, hUV hxU⟩
  let _ : Algebra ↥(S.presheaf.stalk (f x)) ↥(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let _ : Algebra Γ(S, V.1) ↥(X.presheaf.stalk x) :=
    (f.appLE V.1 U.1 hUV ≫ X.presheaf.germ U.1 x hxU).hom.toAlgebra
  let _ : Algebra ↥(X.presheaf.stalk x) ↥(X.residueField x) := (X.residue x).hom.toAlgebra
  let _ : Algebra Γ(X, U.1) ↥(X.residueField x) :=
    ((X.residue x).hom.comp (X.presheaf.germ U.1 x hxU).hom).toAlgebra
  let _ : Module ↥(X.presheaf.stalk x) (relativeDifferentialStalk f x) :=
    relativeDifferentialStalkModule f x
  have _ : IsScalarTower Γ(X, U.1) ↥(X.presheaf.stalk x) ↥(X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower Γ(S, V.1) Γ(X, U.1) ↥(X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (CommRingCat.hom_comp _ _)
  have _ : IsScalarTower Γ(S, V.1) ↥(S.presheaf.stalk (f x)) ↥(X.presheaf.stalk x) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom (appLE_germ_eq_germ_stalkMap f x U.1 V.1 hxU hUV)
  have _ : IsLocalization.AtPrime ↥(S.presheaf.stalk (f x))
      (V.2.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal := V.2.isLocalization_stalk ⟨f x, hUV hxU⟩
  have _ : IsLocalization.AtPrime ↥(X.presheaf.stalk x)
      (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal := U.2.isLocalization_stalk ⟨x, hxU⟩
  have _ : Algebra.FormallyEtale Γ(X, U.1) ↥(X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  -- The residue field of `Γ(X, U)` at the prime of `x` is a model of `κ(x)`.
  let eRes : (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.ResidueField ≃ₐ[Γ(X, U.1)]
      ↥(X.residueField x) :=
    IsLocalRing.ResidueField.mapAlgEquiv
      (IsLocalization.algEquiv (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
        (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal) ↥(X.presheaf.stalk x))
  let _ : Algebra (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.ResidueField ↥(X.residueField x) :=
    eRes.toRingHom.toAlgebra
  have _ : IsScalarTower Γ(X, U.1) (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.ResidueField
      ↥(X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun a => (eRes.commutes a).symm
  -- Step 1: the stalk of the relative differentials is `Ω[𝒪_{X,x}⁄𝒪_{S,f x}]`.
  let e₁ : relativeDifferentialStalk f x ≃ₗ[↥(X.presheaf.stalk x)]
      Ω[↥(X.presheaf.stalk x)⁄↥(S.presheaf.stalk (f x))] :=
    relativeDifferentialsStalkKaehlerEquiv f x
  -- Step 2: the base `𝒪_{S,f x}` may be replaced by `Γ(S, V)`.
  let e₂ : Ω[↥(X.presheaf.stalk x)⁄Γ(S, V.1)] ≃ₗ[↥(X.presheaf.stalk x)]
      Ω[↥(X.presheaf.stalk x)⁄↥(S.presheaf.stalk (f x))] :=
    LinearEquiv.ofBijective _ (omega_localization_base Γ(S, V.1) ↥(X.presheaf.stalk x)
      (V.2.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal.primeCompl ↥(S.presheaf.stalk (f x)))
  -- Step 3: `Ω[𝒪_{X,x}⁄Γ(S,V)]` is the base change of `Ω[Γ(X,U)⁄Γ(S,V)]`.
  let e₃ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale Γ(S, V.1) Γ(X, U.1)
    ↥(X.presheaf.stalk x)
  -- Step 4: base change to `κ(x)`, cancel, and change the field the rank is read over.
  let e : ↥(X.residueField x) ⊗[↥(X.presheaf.stalk x)] relativeDifferentialStalk f x
      ≃ₗ[↥(X.residueField x)] ↥(X.residueField x) ⊗[Γ(X, U.1)] Ω[Γ(X, U.1)⁄Γ(S, V.1)] :=
    ((e₁.trans e₂.symm |>.trans e₃.symm).baseChange ↥(X.presheaf.stalk x)
        ↥(X.residueField x) _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(X, U.1) ↥(X.presheaf.stalk x)
        ↥(X.residueField x) ↥(X.residueField x) Ω[Γ(X, U.1)⁄Γ(S, V.1)])
  exact e.finrank_eq.trans (finrank_tensor_residueField_eq Γ(X, U.1)
    (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.ResidueField ↥(X.residueField x)
    Ω[Γ(X, U.1)⁄Γ(S, V.1)]).symm

end Stacks.Tag01V9NumericalCriterion

end
