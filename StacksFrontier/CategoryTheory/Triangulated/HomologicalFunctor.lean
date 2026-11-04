module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

@[expose] public section


/-
# Problem Description

This is Stacks Project Lemma 13.4.20 (Tag 05QZ), concerning the composition of
homological functors with exact (triangulated) functors and with exact functors
of abelian categories.

## Main Definitions (Stacks Chapter 13, Section 13.3)

Definition 1 (Pre-triangulated category, Tag 0145): a triple `(D, [], T)` where
`D` is additive, `[1]` is an additive auto-equivalence (the shift functor), and
`T` is a set of distinguished triangles satisfying TR1, TR2, TR3.

Definition 2 (Exact / triangulated functor, Tag 014V): a functor
`F : D → D'` between pre-triangulated categories together with functorial
isomorphisms `ξ_X : F(X[1]) → F(X)[1]` sending distinguished triangles to
distinguished triangles.

Definition 3 (Homological functor, Tag 0147): an additive functor
`H : D → A` from a pre-triangulated category to an abelian category, such that
for every distinguished triangle `(X, Y, Z, f, g, h)` the sequence
`H(X) → H(Y) → H(Z)` is exact at `H(Y)`.

Definition 4 (Exact functor of abelian categories): an additive functor
`G : A → A'` that preserves exact sequences.

## Main Statements (Lemma 13.4.20)

Let `H : D → A` be a homological functor.
- Statement 1: if `F : D' → D` is an exact (triangulated) functor, then
  `F ⋙ H` is homological.
- Statement 2: if `G : A → A'` is an exact functor of abelian categories, then
  `H ⋙ G` is homological.
-/

/-
## Formalization notes

The relevant notions are already present in Mathlib:

- Pre-triangulated category: `CategoryTheory.Pretriangulated`. This bundles the
  additive structure, the shift functor `[1]` (via `HasShift _ ℤ` together with
  the additivity of the shifts), the zero object, and the set
  `CategoryTheory.Pretriangulated.distinguishedTriangles` of distinguished
  triangles satisfying TR1, TR2, TR3. This corresponds to Definition 1.

- Exact (triangulated) functor: `CategoryTheory.Functor.IsTriangulated`, where
  the functorial isomorphism `ξ` of Definition 2 is supplied by the
  `CategoryTheory.Functor.CommShift` instance. This corresponds to Definition 2.

- Homological functor: `CategoryTheory.Functor.IsHomological`. Its defining
  property is that, for every distinguished triangle, the associated short
  complex `shortComplexOfDistTriangle` (which is `H(X) → H(Y) → H(Z)`) maps to an
  exact short complex (`ShortComplex.Exact`), i.e. exactness at the middle term.
  This corresponds to Definition 3, and is the predicate appearing in the
  conclusions of Lemma 13.4.20.

- Exact functor of abelian categories: an additive functor preserving finite
  limits and finite colimits, i.e.
  `[G.Additive] [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]`.
  Such a functor preserves `ShortComplex.Exact` (via
  `ShortComplex.Exact.map_of_preservesLeftHomologyOf`). This corresponds to
  Definition 4.
-/

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

-- Main Statement(s)

/-- **Statement 1** (Stacks 13.4.20, first part). If `F : D' → D` is an exact
(triangulated) functor between pre-triangulated categories and `H : D → A` is a
homological functor to an abelian category, then the composition `F ⋙ H` is a
homological functor. -/
@[stacks 05QZ "(1)"]
theorem main_statement_comp_triangulated_homological
    {D' : Type u₁} {D : Type u₂} {A : Type u₃}
    [Category.{v₁} D'] [Category.{v₂} D] [Category.{v₃} A]
    [HasShift D' ℤ] [HasShift D ℤ]
    [HasZeroObject D'] [HasZeroObject D]
    [Preadditive D'] [Preadditive D]
    [∀ (n : ℤ), (shiftFunctor D' n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
    [Pretriangulated D'] [Pretriangulated D] [Abelian A]
    (F : D' ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (H : D ⥤ A) [H.IsHomological] :
    (F ⋙ H).IsHomological := by
  constructor
  intro T hT
  rw [ShortComplex.map_comp]
  exact Functor.IsHomological.exact (F := H) _ (F.map_distinguished T hT)

/-- **Statement 2** (Stacks 13.4.20, second part). If `H : D → A` is a
homological functor and `G : A → A'` is an exact functor of abelian categories
(additive and preserving finite limits and colimits), then the composition
`H ⋙ G` is a homological functor. -/
@[stacks 05QZ "(2)"]
theorem main_statement_comp_homological_exact
    {D : Type u₁} {A : Type u₂} {A' : Type u₃}
    [Category.{v₁} D] [Category.{v₂} A] [Category.{v₃} A']
    [HasShift D ℤ] [HasZeroObject D] [Preadditive D]
    [∀ (n : ℤ), (shiftFunctor D n).Additive]
    [Pretriangulated D] [Abelian A] [Abelian A']
    (H : D ⥤ A) [H.IsHomological]
    (G : A ⥤ A') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (H ⋙ G).IsHomological := by
  constructor
  intro T hT
  rw [ShortComplex.map_comp]
  exact (Functor.IsHomological.exact (F := H) T hT).map G
