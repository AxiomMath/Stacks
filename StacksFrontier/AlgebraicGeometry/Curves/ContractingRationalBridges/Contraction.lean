module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Basic

/-!
# Contractions of rational bridges

Let `C` be a rational bridge of a curve `X`, let `X'` be the scheme-theoretic closure of its
complement, and let `k'` be the ring of global functions on `C`, a field. Contracting `C`
replaces it by the single point `Spec k'`: the target of the contraction is the pushout of `X'`
and `Spec k'` along their common intersection with `C`, and the contraction is the morphism from
`X` whose two restrictions are the canonical maps into that pushout.

## Main definitions

* `AlgebraicGeometry.IsContractionOfRationalBridge` is the predicate for a morphism contracting
  a rational bridge.
* `AlgebraicGeometry.IsIteratedContractionOfRationalBridges` records a finite chain
  `X = X₀ → X₁ → ⋯ → Xₙ` of contractions of rational bridges of curves over `k` through its
  composite.

## Main results

* `AlgebraicGeometry.isContractionOfRationalBridge_iff` characterizes contractions by the
  pushout square and the two restrictions.
* `AlgebraicGeometry.IsContractionOfRationalBridge.schemeTheoreticUnion` extracts the assertion
  that the ambient scheme is the scheme-theoretic union of the bridge and the closure of its
  complement.
* `AlgebraicGeometry.IsIteratedContractionOfRationalBridges.comp`: chains compose.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0E3Q](https://stacks.math.columbia.edu/tag/0E3Q)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism contracting a rational bridge. The ambient scheme is the scheme-theoretic union
of the bridge and the closure of its complement, and the morphism exhibits its target as the
pushout of that closure and the spectrum of the global functions on the bridge along their
common intersection with the bridge. -/
def IsContractionOfRationalBridge {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] {C : X.IdealSheafData}
    (_hC : IsRationalBridge k X C) {Y : Scheme.{u}} (c : X ⟶ Y) : Prop :=
  (C ⊓ complementaryCurveIdeal C = ⊥) ∧
    ∃ (a : complementaryCurve C ⟶ Y) (b : Spec Γ(C.subscheme, ⊤) ⟶ Y),
      IsPushout
          (Scheme.IdealSheafData.inclusion (I := complementaryCurveIdeal C)
            (J := intersectionWithComplementaryCurveIdeal C) le_sup_right)
          (Scheme.IdealSheafData.inclusion (I := C)
            (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫
            C.subscheme.toSpecΓ) a b ∧
        complementaryCurveι C ≫ c = a ∧
        C.subschemeι ≫ c = C.subscheme.toSpecΓ ≫ b

/-- The scheme-theoretic union condition, the pushout square and the two restrictions
characterize a contraction of a rational bridge. -/
@[simp] theorem isContractionOfRationalBridge_iff {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] {C : X.IdealSheafData}
    (hC : IsRationalBridge k X C) {Y : Scheme.{u}} (c : X ⟶ Y) :
    IsContractionOfRationalBridge hC c ↔
      (C ⊓ complementaryCurveIdeal C = ⊥) ∧
        ∃ (a : complementaryCurve C ⟶ Y) (b : Spec Γ(C.subscheme, ⊤) ⟶ Y),
          IsPushout
              (Scheme.IdealSheafData.inclusion (I := complementaryCurveIdeal C)
                (J := intersectionWithComplementaryCurveIdeal C) le_sup_right)
              (Scheme.IdealSheafData.inclusion (I := C)
                (J := intersectionWithComplementaryCurveIdeal C) le_sup_left ≫
                C.subscheme.toSpecΓ) a b ∧
            complementaryCurveι C ≫ c = a ∧
            C.subschemeι ≫ c = C.subscheme.toSpecΓ ≫ b := Iff.rfl

namespace IsContractionOfRationalBridge

/-- The bridge and the closure of its complement have scheme-theoretic union the whole ambient
scheme whenever a contraction exists. -/
theorem schemeTheoreticUnion {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] {C : X.IdealSheafData}
    {hC : IsRationalBridge k X C} {Y : Scheme.{u}} {c : X ⟶ Y}
    (hc : IsContractionOfRationalBridge hC c) :
    C ⊓ complementaryCurveIdeal C = ⊥ := hc.1

end IsContractionOfRationalBridge

/-- **A chain of contractions of rational bridges** `X = X₀ → X₁ → ⋯ → Xₙ = Y` of curves over `k`
(Tag 0E3M), recorded through its composite `c` together with the structure morphisms `fX` and
`fY`. Each step contracts a rational bridge by a morphism compatible with the structure
morphisms; since rational bridges are defined on proper curves, the bridge and contraction
conditions are asserted for the curve being contracted whenever it is proper. -/
inductive IsIteratedContractionOfRationalBridges (k : Type u) [Field k] :
    {X Y : Scheme.{u}} → (fX : X ⟶ Spec (.of k)) → (fY : Y ⟶ Spec (.of k)) → (c : X ⟶ Y) → Prop
  | identity (X : Scheme.{u}) (fX : X ⟶ Spec (.of k)) :
      IsIteratedContractionOfRationalBridges k fX fX (𝟙 X)
  | step {X Y Z : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
      {fZ : Z ⟶ Spec (.of k)} {c : X ⟶ Y} {d : Y ⟶ Z} (C : X.IdealSheafData)
      (hC : ∀ hp : IsProper fX,
        letI : X.Over (Spec (.of k)) := ⟨fX⟩
        haveI : IsProper (X ↘ Spec (.of k)) := hp
        ∃ hC : IsRationalBridge k X C, IsContractionOfRationalBridge hC c)
      (hbase : c ≫ fY = fX) (hd : IsIteratedContractionOfRationalBridges k fY fZ d) :
      IsIteratedContractionOfRationalBridges k fX fZ (c ≫ d)

namespace IsIteratedContractionOfRationalBridges

variable {k : Type u} [Field k]

/-- The composite of a chain of contractions of rational bridges is compatible with the
structure morphisms. -/
theorem comp_structureMorphism {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)}
    {fY : Y ⟶ Spec (.of k)} {c : X ⟶ Y} (h : IsIteratedContractionOfRationalBridges k fX fY c) :
    c ≫ fY = fX := by
  induction h with
  | identity => exact Category.id_comp _
  | step _ _ hbase _ ih => rw [Category.assoc, ih, hbase]

/-- **Chains of contractions of rational bridges compose.** -/
theorem comp {X Y Z : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
    {fZ : Z ⟶ Spec (.of k)} {c : X ⟶ Y} {d : Y ⟶ Z}
    (hc : IsIteratedContractionOfRationalBridges k fX fY c)
    (hd : IsIteratedContractionOfRationalBridges k fY fZ d) :
    IsIteratedContractionOfRationalBridges k fX fZ (c ≫ d) := by
  induction hc with
  | identity => rwa [Category.id_comp]
  | step C hC hbase _ ih => rw [Category.assoc]; exact step C hC hbase (ih hd)

end IsIteratedContractionOfRationalBridges

end AlgebraicGeometry
