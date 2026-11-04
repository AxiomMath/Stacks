module

public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexConeSituationIso
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexRoundTripCoherence
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomotopyCategoryTriangulated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The homotopy category of the differential graded category of complexes is triangulated

`CochainComplex.dgCategory B` is the differential graded category of complexes of Tag 09L9 — the
`C` of Tag 09LK. It satisfies axioms (A), (B) and (C) of Tag 09QJ with the shift additive on
objects only up to isomorphism (`CochainComplex.dgConeSituationIso`), and that is the strongest
form available: Mathlib's shift reindexes a complex by `p + n`, so `X[0] = X` and
`X[n + m] = X[n][m]` are not equalities of objects. The one identity an isomorphism-valued
axiom (B) does not imply holds here (`CochainComplex.dgShiftAxiomBIso_roundTripCoherent`), so
Tag 09QY applies.

## Main definitions

* `CochainComplex.dgCategoryKPreadditive` and `CochainComplex.dgCategoryKPretriangulated`: the
  preadditive and pretriangulated structures of `K(Comp^dg(B))`, as instances.

## Main results

* `CochainComplex.dgCategoryK_isTriangulated`: **`K(Comp^dg(B))` is a triangulated category**,
  with no strictness hypothesis.
* `CochainComplex.dgCategoryKIsTriangulated`: the same, as an instance.
* `CochainComplex.distinguishedTriangles_dgCategoryK`: the distinguished triangles of the
  registered pretriangulated structure are those of admissible short exact sequences.

## Implementation notes

The statement of `CochainComplex.dgCategoryK_isTriangulated` reinstalls the preadditive,
zero-object, translation, additivity and pretriangulated structures with `letI` in exactly the
order `DGCategory.homotopyCategory_isTriangulatedIso` asks for them, because the three axioms are
a hypothesis bundle rather than a typeclass. Nothing can then recover them, so the four of the
five that are not already instances are registered here, each as the term the corresponding
`letI` installs applied to `CochainComplex.dgConeSituationIso`; every statement proved about the
`letI` structures is therefore a statement about these instances.

The fifth, the translation, is already the instance `CochainComplex.dgCategoryKShift`, and it is
the very same structure: the field `kShift` of `CochainComplex.dgShiftAxiomBIso` is that
instance, so `(CochainComplex.dgConeSituationIso B).shift.kShift` is it by `rfl` and no second
translation competes. Nothing else in the development puts a preadditive structure, a zero
object or a pretriangulated structure on `(CochainComplex.dgCategory B).K` either:
`DGCategory.K` is a plain definition, so the structures Mathlib puts on `CochainComplex B ℤ` and
on `HomotopyCategory B (ComplexShape.up ℤ)` do not reach it, and the registrations for the
differential graded categories of right modules and of sheaves of modules are on different
differential graded categories.

## References

* [Stacks Project, Tag 09QY](https://stacks.math.columbia.edu/tag/09QY);
  [Tag 09LK](https://stacks.math.columbia.edu/tag/09LK);
  [Tag 09L9](https://stacks.math.columbia.edu/tag/09L9).
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace CochainComplex

universe v u

variable (B : Type u) [Category.{v} B] [Preadditive B] [HasZeroObject B]
  [HasBinaryBiproducts B]

/-- **The homotopy category of the differential graded category of complexes is triangulated.**
This is Tag 09QY for the `C` of Tag 09LK, and it carries no strictness hypothesis: the axiom (B)
of `CochainComplex.dgConeSituationIso` is additive on objects only up to isomorphism, and its
round-trip coherence is `CochainComplex.dgShiftAxiomBIso_roundTripCoherent`. -/
@[sga "6 I 1.1.5" "partial"]
theorem dgCategoryK_isTriangulated :
    letI : Preadditive (dgCategory B).K := DGCategory.homotopyPreadditive (dgCategory B)
    letI : HasZeroObject (dgCategory B).K :=
      DGCategory.homotopyHasZeroObjectIso (dgCategory B) (dgConeSituationIso B)
    letI : HasShift (dgCategory B).K ℤ := (dgConeSituationIso B).shift.kShift
    letI : ∀ n : ℤ, (CategoryTheory.shiftFunctor (dgCategory B).K n).Additive := fun n =>
      DGCategory.homotopyShiftAdditiveIso (dgCategory B) (dgConeSituationIso B) n
    letI : Pretriangulated (dgCategory B).K :=
      DGCategory.homotopyPretriangulatedIso (dgCategory B) (dgConeSituationIso B)
        (dgShiftAxiomBIso_roundTripCoherent B)
    IsTriangulated (dgCategory B).K :=
  DGCategory.homotopyCategory_isTriangulatedIso (dgCategory B) (dgConeSituationIso B)
    (dgShiftAxiomBIso_roundTripCoherent B)

/-- **`K(Comp^dg(B))` is preadditive**: homotopy classes of closed degree-zero morphisms of
complexes form an abelian group and composition is bilinear. -/
@[instance_reducible]
noncomputable instance dgCategoryKPreadditive : Preadditive (dgCategory B).K :=
  DGCategory.homotopyPreadditive (dgCategory B)

/-- **`K(Comp^dg(B))` has a zero object**, the zero complex of axiom (A). -/
instance dgCategoryKHasZeroObject : HasZeroObject (dgCategory B).K :=
  DGCategory.homotopyHasZeroObjectIso (dgCategory B) (dgConeSituationIso B)

/-- **Each translation functor of `K(Comp^dg(B))` is additive.** -/
instance dgCategoryKShiftAdditive (n : ℤ) :
    (CategoryTheory.shiftFunctor (dgCategory B).K n).Additive :=
  DGCategory.homotopyShiftAdditiveIso (dgCategory B) (dgConeSituationIso B) n

/-- **`K(Comp^dg(B))` is pretriangulated**, its distinguished triangles being those isomorphic to
the triangle of an admissible short exact sequence of complexes. -/
@[instance_reducible]
noncomputable instance dgCategoryKPretriangulated : Pretriangulated (dgCategory B).K :=
  DGCategory.homotopyPretriangulatedIso (dgCategory B) (dgConeSituationIso B)
    (dgShiftAxiomBIso_roundTripCoherent B)

/-- **`K(Comp^dg(B))` is triangulated**, as an instance: this is
`CochainComplex.dgCategoryK_isTriangulated` read off the registered structures. -/
instance dgCategoryKIsTriangulated : IsTriangulated (dgCategory B).K :=
  dgCategoryK_isTriangulated B

/-- The distinguished triangles of `K(Comp^dg(B))` are exactly the triangles isomorphic to that
of an admissible short exact sequence of complexes. -/
theorem distinguishedTriangles_dgCategoryK :
    distinguishedTriangles (C := (dgCategory B).K) =
      {U | DGCategory.IsDistinguishedTriangleIso (dgCategory B) (dgConeSituationIso B) U} :=
  DGCategory.distinguishedTriangles_homotopyPretriangulatedIso (dgCategory B)
    (dgConeSituationIso B) (dgShiftAxiomBIso_roundTripCoherent B)

end CochainComplex
