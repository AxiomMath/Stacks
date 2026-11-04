module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.RationalTail
public import StacksCore.Tactic.StacksAttribute

/-!
# Contractions of rational tails

Let `C` be a rational tail of a curve `X`, and let `X'` be the scheme-theoretic closure of its
complement. A contraction of `C` is a morphism from `X` to `X'` that is the identity on `X'`
and sends `C` to its attaching point.

## Main definitions

* `AlgebraicGeometry.canonicalMapToAttachingPoint` maps the tail to the spectrum of the
  residue field of its attaching point.
* `AlgebraicGeometry.IsContractionOfRationalTail` is the predicate for a morphism contracting
  a rational tail.
* `AlgebraicGeometry.IsIteratedContractionOfRationalTails` records a finite sequence of such
  contractions and its composite morphism.

## Main results

* `AlgebraicGeometry.isContractionOfRationalTail_iff` characterizes contractions by their two
  restrictions.

## Implementation notes

The restriction to `C` is the canonical map from `C` to the spectrum of the residue field at
its attaching point, followed by the inclusion of that point in `X'`. The inclusion is
recorded by a morphism `p` whose composite with the closed immersion `X' ⟶ X` is the canonical
residue-field point of `C` in `X`. Such a `p` is unique because the closed immersion is a
monomorphism. The ambient properness, dimension, nodality and global-sections conditions are
standing hypotheses for applications, but are not needed to define the contraction.

The finite-sequence predicate is the one used by the choice-independence,
base-field-extension and genus-zero statements for iterated contractions; it is stated here
so that those statements do not depend on each other.

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The canonical morphism from a rational tail to the residue field of its attaching point,
using the isomorphism between that field and its global sections. -/
abbrev canonicalMapToAttachingPoint {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {C : X.IdealSheafData} (hC : IsRationalTail k X C) :
    C.subscheme ⟶ Spec (C.subscheme.residueField hC.attachingPoint) :=
  letI := hC.isIso_Γevaluation_attachingPoint
  C.subscheme.toSpecΓ ≫ Spec.map (inv (C.subscheme.Γevaluation hC.attachingPoint))

/-- A morphism contracting a rational tail onto its complementary curve. -/
@[stacks 0E3H "contraction_of_a_rational_tail"]
def IsContractionOfRationalTail {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {C : X.IdealSheafData} (hC : IsRationalTail k X C)
    (c : X ⟶ complementaryCurve C) : Prop :=
  complementaryCurveι C ≫ c = 𝟙 (complementaryCurve C) ∧
    ∃ p : Spec (C.subscheme.residueField hC.attachingPoint) ⟶ complementaryCurve C,
      p ≫ complementaryCurveι C =
          C.subscheme.fromSpecResidueField hC.attachingPoint ≫ C.subschemeι ∧
        C.subschemeι ≫ c = canonicalMapToAttachingPoint hC ≫ p

/-- The two restrictions that characterize a contraction of a rational tail. -/
@[simp] theorem isContractionOfRationalTail_iff {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {C : X.IdealSheafData} (hC : IsRationalTail k X C)
    (c : X ⟶ complementaryCurve C) :
    IsContractionOfRationalTail hC c ↔
      complementaryCurveι C ≫ c = 𝟙 (complementaryCurve C) ∧
        ∃ p : Spec (C.subscheme.residueField hC.attachingPoint) ⟶ complementaryCurve C,
          p ≫ complementaryCurveι C =
              C.subscheme.fromSpecResidueField hC.attachingPoint ≫ C.subschemeι ∧
            C.subschemeι ≫ c = canonicalMapToAttachingPoint hC ≫ p := Iff.rfl

/-- A finite chain of rational-tail contractions over a field, recording its composite map.
The zero-length chain is allowed. -/
inductive IsIteratedContractionOfRationalTails
    (k : Type u) [Field k] :
    {X Y : Scheme.{u}} → (fX : X ⟶ Spec (.of k)) →
      (fY : Y ⟶ Spec (.of k)) → (c : X ⟶ Y) → Prop
  | identity (X : Scheme.{u}) (fX : X ⟶ Spec (.of k)) :
      IsIteratedContractionOfRationalTails k fX fX (𝟙 X)
  | step {X Y Z : Scheme.{u}}
      {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
      {fZ : Z ⟶ Spec (.of k)}
      {c : X ⟶ Y} {d : Y ⟶ Z}
      (C : X.IdealSheafData)
      (hC : letI : X.Over (Spec (.of k)) := ⟨fX⟩
        IsRationalTail k X C)
      (e : complementaryCurve C ≅ Y)
      (hc : letI : X.Over (Spec (.of k)) := ⟨fX⟩
        IsContractionOfRationalTail hC (c ≫ e.inv))
      (hbase : c ≫ fY = fX)
      (hd : IsIteratedContractionOfRationalTails k fY fZ d) :
      IsIteratedContractionOfRationalTails k fX fZ (c ≫ d)

namespace IsIteratedContractionOfRationalTails

variable {k : Type u} [Field k]

/-- The composite of a chain of rational-tail contractions is a morphism over the base
field. -/
theorem comp_structureMap {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
    {c : X ⟶ Y} (hseq : IsIteratedContractionOfRationalTails k fX fY c) : c ≫ fY = fX := by
  induction hseq with
  | identity X fX => simp
  | step C hC e hc hbase hd ih => simpa only [Category.assoc, ih] using hbase

/-- A single contraction of a rational tail is a chain of length one. -/
theorem single {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)} {c : X ⟶ Y}
    (C : X.IdealSheafData)
    (hC : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      IsRationalTail k X C)
    (e : complementaryCurve C ≅ Y)
    (hc : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      IsContractionOfRationalTail hC (c ≫ e.inv))
    (hbase : c ≫ fY = fX) :
    IsIteratedContractionOfRationalTails k fX fY c := by
  simpa using step C hC e hc hbase (identity Y fY)

/-- Chains of rational-tail contractions compose. -/
theorem trans {X Y Z : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
    {fZ : Z ⟶ Spec (.of k)} {c : X ⟶ Y} {d : Y ⟶ Z}
    (hc : IsIteratedContractionOfRationalTails k fX fY c)
    (hd : IsIteratedContractionOfRationalTails k fY fZ d) :
    IsIteratedContractionOfRationalTails k fX fZ (c ≫ d) := by
  induction hc with
  | identity X fX => simpa using hd
  | step C hC e hc' hbase hseq ih =>
    simpa only [Category.assoc] using step C hC e hc' hbase (ih hd)

end IsIteratedContractionOfRationalTails

end AlgebraicGeometry
