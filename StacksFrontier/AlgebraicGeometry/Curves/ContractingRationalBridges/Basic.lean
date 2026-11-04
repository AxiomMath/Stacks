module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.RationalTail
public import StacksCore.Tactic.StacksAttribute

/-!
# Rational bridges of nodal curves

Let `X` be a proper one-dimensional at-worst-nodal scheme over a field `k`, with
`H⁰(X, 𝒪_X) = k`. An integral irreducible component `C` is a rational bridge if the
scheme-theoretic closure of its complement is nonempty, its scheme-theoretic intersection with
that closure has degree two over `H⁰(C, 𝒪_C)`, and `C` has genus zero.

## Main definitions

* `AlgebraicGeometry.IsRationalBridge` is the rational-bridge condition.

## Main results

* `AlgebraicGeometry.isRationalBridge_iff` characterizes rational bridges.

## Implementation notes

The closed component is represented by an ideal sheaf. The complementary closure and
intersection are the constructions used for rational tails. The intersection maps to `C` by
inclusion of ideal sheaves, so its degree over the global functions of `C` is their module
finrank. As `X` is proper over `k` and `C` is integral, these global functions form a field, and
the genus of `C` is taken over this field via `C.subscheme.toSpecΓ`, not over `k`. The dimension,
nodality and global-sections conditions on `X` are not part of the definition.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An integral irreducible component is a rational bridge if the closure of its complement is
nonempty, the intersection has degree two over its global functions, and its genus is zero. -/
@[stacks 0E3M "rational_bridge"]
def IsRationalBridge (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (C : X.IdealSheafData) : Prop :=
  ∃ hIntegral : IsIntegral C.subscheme,
    letI : IsIntegral C.subscheme := hIntegral
    letI : Field Γ(C.subscheme, ⊤) :=
      (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
    (C.support : Set X) ∈ irreducibleComponents X ∧ Nonempty (complementaryCurve C) ∧
      (let I := intersectionWithComplementaryCurveIdeal C
        let i : I.subscheme ⟶ C.subscheme :=
          Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ I)
        letI : Algebra Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) := i.appTop.hom.toAlgebra
        Module.finrank Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) = 2) ∧
      genus C.subscheme.toSpecΓ = 0

/-- The defining conditions for a rational bridge. -/
@[simp] theorem isRationalBridge_iff (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] (C : X.IdealSheafData) :
    IsRationalBridge k X C ↔
      ∃ hIntegral : IsIntegral C.subscheme,
        letI : IsIntegral C.subscheme := hIntegral
        letI : Field Γ(C.subscheme, ⊤) :=
          (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
        (C.support : Set X) ∈ irreducibleComponents X ∧ Nonempty (complementaryCurve C) ∧
          (let I := intersectionWithComplementaryCurveIdeal C
            let i : I.subscheme ⟶ C.subscheme :=
              Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ I)
            letI : Algebra Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) := i.appTop.hom.toAlgebra
            Module.finrank Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) = 2) ∧
          genus C.subscheme.toSpecΓ = 0 := Iff.rfl

namespace IsRationalBridge

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] {C : X.IdealSheafData}

/-- A rational bridge is integral. -/
theorem isIntegral (hC : IsRationalBridge k X C) : IsIntegral C.subscheme := hC.1

/-- A rational bridge is an irreducible component. -/
theorem support_mem_irreducibleComponents (hC : IsRationalBridge k X C) :
    (C.support : Set X) ∈ irreducibleComponents X := hC.2.1

/-- The closure of the complement of a rational bridge is nonempty. -/
theorem complementaryCurve_nonempty (hC : IsRationalBridge k X C) :
    Nonempty (complementaryCurve C) := hC.2.2.1

/-- The intersection of a rational bridge with the complementary curve has degree two over the
global functions on the bridge. -/
theorem intersection_finrank_eq_two (hC : IsRationalBridge k X C) :
    let I := intersectionWithComplementaryCurveIdeal C
    let i : I.subscheme ⟶ C.subscheme := Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ I)
    letI : Algebra Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) := i.appTop.hom.toAlgebra
    Module.finrank Γ(C.subscheme, ⊤) Γ(I.subscheme, ⊤) = 2 := hC.2.2.2.1

/-- A rational bridge has genus zero. -/
theorem genus_eq_zero (hC : IsRationalBridge k X C) :
    letI : IsIntegral C.subscheme := hC.isIntegral
    letI : Field Γ(C.subscheme, ⊤) :=
      (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
    genus C.subscheme.toSpecΓ = 0 := hC.2.2.2.2

end IsRationalBridge

end AlgebraicGeometry
