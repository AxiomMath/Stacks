module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Rational tails

Let `X` be a scheme over a field `k`. An integral irreducible component `C` of `X`, given as a
closed subscheme by an ideal sheaf, is a rational tail when the scheme-theoretic closure of its
complement is nonempty, meets `C` in one reduced point, the global functions on `C` map
isomorphically to the residue field at that point, and `C` has genus zero.

## Main definitions

* `AlgebraicGeometry.complementaryCurve` is the scheme-theoretic closure of the complement of
  a closed subscheme.
* `AlgebraicGeometry.intersectionWithComplementaryCurveIdeal` is the ideal sheaf cutting out
  its scheme-theoretic intersection with that closure.
* `AlgebraicGeometry.IsRationalTail` is the rational-tail condition on an integral irreducible
  component.
* `AlgebraicGeometry.IsRationalTail.attachingPoint` is the point at which a rational tail meets
  the closure of its complement.

## Main results

* `AlgebraicGeometry.isRationalTail_iff` unfolds the rational-tail condition.

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The ideal sheaf cutting out the scheme-theoretic closure of the complement of the closed
subscheme cut out by `C`. -/
abbrev complementaryCurveIdeal {X : Scheme.{u}} (C : X.IdealSheafData) : X.IdealSheafData :=
  (Scheme.Opens.ι C.support.compl).ker

/-- The scheme-theoretic closure of the complement of the closed subscheme cut out by `C`. -/
abbrev complementaryCurve {X : Scheme.{u}} (C : X.IdealSheafData) : Scheme.{u} :=
  (Scheme.Opens.ι C.support.compl).image

/-- The canonical closed immersion of the scheme-theoretic closure of the complement into the
ambient scheme. -/
abbrev complementaryCurveι {X : Scheme.{u}} (C : X.IdealSheafData) :
    complementaryCurve C ⟶ X := (Scheme.Opens.ι C.support.compl).imageι

/-- The ideal sheaf cutting out the scheme-theoretic intersection of `C` with the
scheme-theoretic closure of its complement. -/
abbrev intersectionWithComplementaryCurveIdeal {X : Scheme.{u}} (C : X.IdealSheafData) :
    X.IdealSheafData := C ⊔ complementaryCurveIdeal C

/-- The scheme-theoretic intersection of `C` with the closure of its complement. -/
abbrev intersectionWithComplementaryCurve {X : Scheme.{u}} (C : X.IdealSheafData) :
    Scheme.{u} := (intersectionWithComplementaryCurveIdeal C).subscheme

/-- An integral irreducible component `C` of a scheme over `k` is a rational tail when the
closure of its complement is nonempty, its intersection with `C` is one reduced point, the
global functions on `C` map isomorphically to the residue field of that point, and `C` has
genus zero. -/
@[stacks 0E3H "rational_tail"]
def IsRationalTail (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (C : X.IdealSheafData) : Prop :=
  IsIntegral C.subscheme ∧ (C.support : Set X) ∈ irreducibleComponents X ∧
    Nonempty (complementaryCurve C) ∧
    ∃ (x : C.subscheme) (hx : IsClosed ({C.subschemeι x} : Set X)),
      intersectionWithComplementaryCurveIdeal C =
          Scheme.IdealSheafData.vanishingIdeal ⟨{C.subschemeι x}, hx⟩ ∧
        IsIso (C.subscheme.Γevaluation x) ∧
        genus (C.subschemeι ≫ (X ↘ Spec (.of k))) = 0

/-- The defining conditions for a rational tail. -/
@[simp] theorem isRationalTail_iff (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] (C : X.IdealSheafData) :
    IsRationalTail k X C ↔
      IsIntegral C.subscheme ∧ (C.support : Set X) ∈ irreducibleComponents X ∧
        Nonempty (complementaryCurve C) ∧
        ∃ (x : C.subscheme) (hx : IsClosed ({C.subschemeι x} : Set X)),
          intersectionWithComplementaryCurveIdeal C =
              Scheme.IdealSheafData.vanishingIdeal ⟨{C.subschemeι x}, hx⟩ ∧
            IsIso (C.subscheme.Γevaluation x) ∧
            genus (C.subschemeι ≫ (X ↘ Spec (.of k))) = 0 := Iff.rfl

namespace IsRationalTail

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {C : X.IdealSheafData}

/-- A rational tail is integral. -/
theorem isIntegral (hC : IsRationalTail k X C) : IsIntegral C.subscheme := hC.1

/-- The support of a rational tail is an irreducible component of the ambient scheme. -/
theorem support_mem_irreducibleComponents (hC : IsRationalTail k X C) :
    (C.support : Set X) ∈ irreducibleComponents X := hC.2.1

/-- The scheme-theoretic closure of the complement of a rational tail is nonempty. -/
theorem complementaryCurve_nonempty (hC : IsRationalTail k X C) :
    Nonempty (complementaryCurve C) := hC.2.2.1

/-- The point at which a rational tail meets the scheme-theoretic closure of its
complement. -/
noncomputable def attachingPoint (hC : IsRationalTail k X C) : C.subscheme :=
  hC.2.2.2.choose

/-- The attaching point of a rational tail is closed in the ambient scheme. -/
theorem attachingPoint_isClosed (hC : IsRationalTail k X C) :
    IsClosed ({C.subschemeι hC.attachingPoint} : Set X) := hC.2.2.2.choose_spec.choose

/-- The intersection of a rational tail with the closure of its complement is the reduced
closed subscheme supported at the attaching point. -/
theorem intersectionWithComplementaryCurveIdeal_eq (hC : IsRationalTail k X C) :
    intersectionWithComplementaryCurveIdeal C =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨{C.subschemeι hC.attachingPoint}, hC.attachingPoint_isClosed⟩ :=
  hC.2.2.2.choose_spec.choose_spec.1

/-- Global functions on a rational tail map isomorphically to the residue field of its
attaching point. -/
theorem isIso_Γevaluation_attachingPoint (hC : IsRationalTail k X C) :
    IsIso (C.subscheme.Γevaluation hC.attachingPoint) :=
  hC.2.2.2.choose_spec.choose_spec.2.1

/-- A rational tail has genus zero. -/
theorem genus_eq_zero (hC : IsRationalTail k X C) :
    genus (C.subschemeι ≫ (X ↘ Spec (.of k))) = 0 :=
  hC.2.2.2.choose_spec.choose_spec.2.2

end IsRationalTail

end AlgebraicGeometry
