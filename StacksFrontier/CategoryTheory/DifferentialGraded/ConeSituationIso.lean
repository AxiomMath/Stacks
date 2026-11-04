module

public import StacksFrontier.CategoryTheory.DifferentialGraded.ConeSituation
public import StacksFrontier.CategoryTheory.DifferentialGraded.TriangleIso

/-!
# Differential graded categories with cones, for a shift additive up to isomorphism

`DGCategory.ConeSituation` is axioms (A), (B) and (C) of Tag 09QJ: a zero object and binary
direct sums, the shift functors with their identifications of Hom complexes, and a cone for every
closed degree-zero morphism. Its axiom (B) is the strict `DGCategory.ShiftAxiomB`, which the
differential graded category of complexes does not satisfy — the shift of a complex is additive
on objects only up to isomorphism.

This file is the same package over `DGCategory.ShiftAxiomBIso`, the isomorphism-valued axiom (B).
Only the type of the shift datum changes; axiom (A) is untouched, and axiom (C) is stated with
the connecting arrow of the isomorphism-valued triangle layer,
`DGCategory.ShiftAxiomBIso.connectingCocycle`, which is built from the same `toShift` as the
strict one.

## Main definitions

* `DGCategory.ConeSituationIso`: axioms (A), (B) and (C), with the shift additive on objects up
  to isomorphism.
* `DGCategory.ConeSituation.toConeSituationIso`: a cone situation with a strict shift is one
  with the shift additive up to isomorphism.

## References

* [Stacks Project, Tag 09QJ](https://stacks.math.columbia.edu/tag/09QJ);
  [Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), axioms (A) and (B).
-/

@[expose] public section

namespace DGCategory

universe u v w

/-- Axioms (A), (B) and (C) of a differential graded category with cones, with the shift additive
on objects only up to isomorphism: for every closed degree-zero arrow `f : x ⟶ y`, the sequence
`y ⟶ c(f) ⟶ x[1]` is admissible and its connecting arrow `x[1] ⟶ y[1]` is `f[1]`. -/
structure ConeSituationIso {R : Type w} [CommRing R] (A : DGCategory.{v, u} R) where
  /-- Axiom (A): a zero object and binary direct sums. -/
  directSum : DirectSumAxiomA A
  /-- Axiom (B): the shift functors, additive on objects up to isomorphism. -/
  shift : ShiftAxiomBIso A
  /-- Axiom (C): a chosen cone for every closed degree-zero morphism. -/
  cone : ∀ {x y : A.Obj}, A.Cocycle x y → A.Obj
  /-- The chosen admissible short exact sequence `y ⟶ c(f) ⟶ x[1]`. -/
  coneSequence : ∀ {x y : A.Obj} (f : A.Cocycle x y),
    GradedSplitShortExact (A := A) y (cone f) ((shift.shiftFunctor 1).obj x)
  /-- Its connecting arrow `x[1] ⟶ y[1]` is `f[1]`. -/
  cone_connecting : ∀ {x y : A.Obj} (f : A.Cocycle x y),
    shift.connectingCocycle (coneSequence f) = (shift.shiftFunctor 1).mapCocycle f

/-- A cone situation in the strict sense, as a cone situation with the shift additive up to
isomorphism. -/
@[reducible] def ConeSituation.toConeSituationIso {R : Type w} [CommRing R]
    {A : DGCategory.{v, u} R} (s : ConeSituation A) : ConeSituationIso A where
  directSum := s.directSum
  shift := s.shift.toShiftAxiomBIso
  cone := s.cone
  coneSequence := s.coneSequence
  cone_connecting f := Subtype.ext (congrArg Subtype.val (s.cone_connecting f))

end DGCategory
