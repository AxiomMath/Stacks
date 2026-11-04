module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated

/-!
# Differential graded categories with cones

A differential graded category satisfying the direct-sum axiom (A) and the shift axiom (B) *has
cones* when every closed degree-zero morphism `f : x ⟶ y` fits into an admissible short exact
sequence `y ⟶ c(f) ⟶ x[1]` whose connecting arrow `x[1] ⟶ y[1]` is `f[1]`. This is axiom (C),
and it is the hypothesis under which the homotopy category becomes triangulated.

## Main definitions

* `DGCategory.ConeSituation`: axioms (A), (B) and (C), the last of them including a choice of
  cone and of admissible sequence for every closed degree-zero morphism, the sequence given by its
  graded splitting `DGCategory.GradedSplitShortExact`.
* `DGCategory.HomotopyCommutativeSquare`: a square of closed degree-zero morphisms of such a
  category together with a homotopy witnessing its commutativity.

## References

* [Stacks Project, Tag 09QJ](https://stacks.math.columbia.edu/tag/09QJ)
-/

@[expose] public section

namespace DGCategory

universe u v w

/-- Axioms (A), (B), and (C) for a differential graded category. For every closed degree-zero
arrow `f : x ⟶ y`, the sequence `y ⟶ c(f) ⟶ x[1]` is admissible and its connecting arrow
`x[1] ⟶ y[1]` is `f[1]`. -/
@[stacks 09QJ]
structure ConeSituation {R : Type w} [CommRing R] (A : DGCategory.{v, u} R) where
  /-- Axiom (A): a zero object and binary direct sums. -/
  directSum : DirectSumAxiomA A
  /-- Axiom (B): the shift functors and their identifications of Hom complexes. -/
  shift : ShiftAxiomB A
  /-- Axiom (C): a chosen cone for every closed degree-zero morphism. -/
  cone : ∀ {x y : A.Obj}, A.Cocycle x y → A.Obj
  /-- The chosen admissible short exact sequence `y ⟶ c(f) ⟶ x[1]`. -/
  coneSequence : ∀ {x y : A.Obj} (f : A.Cocycle x y),
    GradedSplitShortExact (A := A) y (cone f) ((shift.shiftFunctor 1).obj x)
  /-- Its connecting arrow `x[1] ⟶ y[1]` is `f[1]`. -/
  cone_connecting : ∀ {x y : A.Obj} (f : A.Cocycle x y),
    GradedSplitShortExact.connectingCocycle shift (coneSequence f) =
      (shift.shiftFunctor 1).mapCocycle f

/-- A square of closed degree-zero morphisms whose two composites differ by the differential of a
degree `-1` morphism. -/
structure HomotopyCommutativeSquare {R : Type w} [CommRing R]
    {A : DGCategory.{v, u} R} (_s : ConeSituation A) where
  /-- The upper-left object. -/
  x : A.Obj
  /-- The upper-right object. -/
  y : A.Obj
  /-- The lower-left object. -/
  z : A.Obj
  /-- The lower-right object. -/
  w : A.Obj
  /-- The upper horizontal morphism. -/
  f : A.Cocycle x y
  /-- The left vertical morphism. -/
  a : A.Cocycle x z
  /-- The right vertical morphism. -/
  b : A.Cocycle y w
  /-- The lower horizontal morphism. -/
  g : A.Cocycle z w
  /-- The chosen degree `-1` homotopy. -/
  h : A.Hom x w (-1)
  /-- The two composites differ by the differential of `h`. -/
  commutes_up_to_homotopy :
    (A.compCocycle b f).1 - (A.compCocycle g a).1 =
      A.d' (show (-1 : ℤ) + 1 = 0 by omega) h

end DGCategory
