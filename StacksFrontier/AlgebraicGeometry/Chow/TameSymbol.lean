module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Fraction
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The tame symbol at a codimension-one point of a scheme

Let `X` be an integral scheme and `ξ ∈ X` a point. Write `Z_ξ` for the integral closed subscheme
`Stacks.Chow.integralComponentAt ξ`, the reduced induced structure on the closure of `ξ`, and
`B = 𝒪_{X, ξ}`. Then

* the fraction field of `B` is the function field of `X`, hence Stacks' ring `R(X)` of rational
  functions (Stacks 01RV);
* the residue field of `B` is `κ(ξ)`, which is the function field of `Z_ξ`, hence `R(Z_ξ)`.

So a tame symbol `∂_B : Q(B)^* × Q(B)^* → κ(𝔪_B)^*` on the one-dimensional Noetherian local
domain `B` — the data of `Stacks.Chow.TameSymbol`, which Stacks 0EAH constructs — becomes a map

`∂_ξ : R(X)^* × R(X)^* → R(Z_ξ)^*`.

This is the form in which the tame symbol enters the key formula Stacks 0AYC: the field
`Stacks.Chow.KeyFormulaData.tameSymbol` of the statement of that formula takes values in
`(Stacks.Chow.rationalFunctions Z_i)ˣ`, and `Stacks.Chow.tameSymbolAt` is what instantiates it,
applied to `f_i` and `g_i` in `R(X)^*`.

The identification `R(Z_ξ) ≅ κ(ξ)` is `Stacks.Chow.rationalFunctionsIntegralComponentEquiv`: the
rational functions of the integral scheme `Z_ξ` are the residue field at its generic point
(Stacks 01RV), the generic point of `Z_ξ` is `ξ` (`Stacks.Chow.genericPointOf_integralComponentAt`)
and a closed immersion identifies residue fields at corresponding points
(`Stacks.Chow.residueFieldEquivOfIsClosedImmersion`).

## Main definitions

* `Stacks.Chow.residueFieldEquivOfIsClosedImmersion` — a closed immersion identifies the residue
  field of the target at the image of a point with the residue field of the source at that point.
* `Stacks.Chow.rationalFunctionsIntegralComponentEquiv` — `R(Z_ξ) ≅ κ(ξ)`.
* `Stacks.Chow.tameSymbolAt` — the tame symbol at `ξ`, as a map
  `R(X)^* × R(X)^* → R(Z_ξ)^*`.

## Main results

* `Stacks.Chow.tameSymbolAt_mul_right`, `Stacks.Chow.tameSymbolAt_skew`,
  `Stacks.Chow.tameSymbolAt_steinberg` — the three properties Stacks 0EAI, 0EAJ and 0EAK of the
  tame symbol, in the form they take on `R(X)^*`.

## References

* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- A closed immersion identifies the residue field of the target at the image of a point with
the residue field of the source at that point: it is injective on stalks' residue fields because
residue fields are fields, and surjective because the map on stalks is. -/
def residueFieldEquivOfIsClosedImmersion {W X : Scheme.{u}} (i : W ⟶ X) [IsClosedImmersion i]
    (y : W) : X.residueField (i.base y) ≃+* W.residueField y :=
  RingEquiv.ofBijective (i.residueFieldMap y).hom
    ⟨(i.residueFieldMap y).hom.injective, fun z ↦ by
      obtain ⟨a, rfl⟩ := W.residue_surjective y z
      obtain ⟨b, rfl⟩ := i.stalkMap_surjective y a
      exact ⟨X.residue (i.base y) b,
        ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i y) b⟩⟩

/-- **The rational functions of `Z_ξ` are the residue field of `X` at `ξ`.** The integral closed
subscheme `Z_ξ = Stacks.Chow.integralComponentAt ξ` has generic point `ξ`, so Stacks 01RV
identifies `R(Z_ξ)` with the residue field of `Z_ξ` at its generic point, and the closed
immersion `Z_ξ → X` identifies that with `κ(ξ)`. -/
def rationalFunctionsIntegralComponentEquiv {X : Scheme.{u}} (x : X) :
    rationalFunctions (integralComponentAt x).subscheme ≃+*
      IsLocalRing.ResidueField (X.presheaf.stalk x) := by
  letI := isIntegral_integralComponentAt x
  have hpt : (integralComponentAt x).subschemeι.base
      (genericPoint (integralComponentAt x).subscheme) = x :=
    genericPointOf_integralComponentAt x
  exact ((rationalFunctionsEquivResidueField (integralComponentAt x).subscheme).1.trans
    (residueFieldEquivOfIsClosedImmersion (integralComponentAt x).subschemeι
      (genericPoint (integralComponentAt x).subscheme)).symm).trans
    (X.residueFieldCongr hpt).commRingCatIsoToRingEquiv

/-- The units of `R(X)`, transported to the units of the function field of `X` (the fraction
field of each local ring `𝒪_{X, ξ}`). -/
def rationalFunctionsUnitsEquivFunctionField (X : Scheme.{u}) [IsIntegral X] :
    (rationalFunctions X)ˣ ≃* X.functionFieldˣ :=
  Units.mapEquiv (rationalFunctionsEquivFunctionField X).1.toMulEquiv

section

variable {X : Scheme.{u}} [IsIntegral X] (x : X)

/-- The units of `R(Z_ξ)`, transported to the units of the residue field of `𝒪_{X, ξ}`. -/
def rationalFunctionsUnitsIntegralComponentEquiv :
    (rationalFunctions (integralComponentAt x).subscheme)ˣ ≃*
      (IsLocalRing.ResidueField (X.presheaf.stalk x))ˣ :=
  Units.mapEquiv (rationalFunctionsIntegralComponentEquiv x).toMulEquiv

variable (symb : TameSymbol (X.presheaf.stalk x) X.functionField)

/-- **The tame symbol at a point of an integral scheme.** Stacks 0EAH gives a tame symbol
`∂_B : Q(B)^* × Q(B)^* → κ(𝔪_B)^*` for `B = 𝒪_{X, ξ}` a one-dimensional Noetherian local domain.
Reading `Q(B)` as `R(X)` and `κ(𝔪_B)` as `R(Z_ξ)` turns it into a map
`R(X)^* × R(X)^* → R(Z_ξ)^*`, which is the shape in which the key formula Stacks 0AYC uses it:
it is exactly what `Stacks.Chow.KeyFormulaData.tameSymbol` expects. -/
def tameSymbolAt (f g : (rationalFunctions X)ˣ) :
    (rationalFunctions (integralComponentAt x).subscheme)ˣ :=
  (rationalFunctionsUnitsIntegralComponentEquiv x).symm
    (symb (rationalFunctionsUnitsEquivFunctionField X f)
      (rationalFunctionsUnitsEquivFunctionField X g))

/-- **Stacks 0EAI at a point.** `∂_ξ(f, g h) = ∂_ξ(f, g) ∂_ξ(f, h)`. -/
theorem tameSymbolAt_mul_right (f g h : (rationalFunctions X)ˣ) :
    tameSymbolAt x symb f (g * h) = tameSymbolAt x symb f g * tameSymbolAt x symb f h := by
  simp only [tameSymbolAt, map_mul, symb.map_mul_right]

/-- **Stacks 0EAJ at a point.** `∂_ξ(f, g) ∂_ξ(g, f) = 1`. -/
theorem tameSymbolAt_skew (f g : (rationalFunctions X)ˣ) :
    tameSymbolAt x symb f g * tameSymbolAt x symb g f = 1 := by
  simp only [tameSymbolAt, ← map_mul, symb.skew, map_one]

/-- **Stacks 0EAK at a point.** `∂_ξ(f, 1 - f) = 1`, for `f` and `1 - f` both invertible
rational functions. -/
theorem tameSymbolAt_steinberg (f g : (rationalFunctions X)ˣ)
    (hfg : (f : rationalFunctions X) + (g : rationalFunctions X) = 1) :
    tameSymbolAt x symb f g = 1 := by
  have hval : ((rationalFunctionsUnitsEquivFunctionField X f : X.functionFieldˣ) :
      X.functionField) +
      ((rationalFunctionsUnitsEquivFunctionField X g : X.functionFieldˣ) :
        X.functionField) = 1 := by
    have h := congrArg (rationalFunctionsEquivFunctionField X).1 hfg
    rwa [map_add, map_one] at h
  rw [tameSymbolAt, symb.steinberg _ _ hval, map_one]

end

end Stacks.Chow

end
