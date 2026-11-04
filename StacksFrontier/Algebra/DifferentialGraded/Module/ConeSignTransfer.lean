module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.ConeSignClasses
public import StacksFrontier.Algebra.DGA.Pretriangulated
public import StacksFrontier.CategoryTheory.Shift.SignTwist

/-!
# Transferring exactness between the two pretriangulated structures on `K(Mod_(A, d))`

The homotopy category `K(A, d)` of right differential graded `A`-modules carries two
pretriangulated structures in this repository: the default instance
`instPretriangulatedHomotopyCategory`, whose distinguished triangles are the cone triangles, and
the definition `instPretriangulatedHomotopyCategory'`, not an instance, whose distinguished
triangles are the triangles of admissible short exact sequences (Tag 09KH). By
`mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_negMor₃` the two classes are the two
sign conventions for the third arrow; negating the third arrow of a distinguished triangle does
not in general produce a distinguished one, so the two classes need not agree.

Consequently a functor out of `K(A, d)` that is exact for one of the two structures **need not**
be exact for the other: its image of a cone triangle differs from its image of the corresponding
admissible triangle by a sign on the third arrow (some functors, such as a zero functor, are
exact for both). What does transfer is the composite with the
*sign-twisted identity* of this file: the identity endofunctor of `K(A, d)`, carrying the shift
comparison `ε(n) = (-1)^n` instead of the identity. Its `mapTriangle` is exactly the negation of
the third arrow, so it is an exact functor from either of the two structures to the other, and
precomposing with it converts exactness for the admissible structure into exactness for the cone
structure.

## Main definitions

* `DifferentialGradedModule.signTwist`: the identity endofunctor of `K(A, d)`, under a name of
  its own — the sign-twisted identity `CategoryTheory.signTwist` of
  `StacksFrontier.CategoryTheory.Shift.SignTwist`, whose shift comparison is twisted by the sign of
  the shift.

## Main results

* `DifferentialGradedModule.mem_distinguishedTriangles_admissible_iff` and
  `DifferentialGradedModule.mem_distinguishedTriangles_cone_iff`: the sign comparison between the
  default cone-triangle pretriangulated structure
  `DifferentialGradedModule.instPretriangulatedHomotopyCategory` and the admissible-sequence
  structure `DifferentialGradedModule.instPretriangulatedHomotopyCategory'`, which is not an
  instance: a triangle is distinguished for one exactly when negating its third arrow makes it
  distinguished for the other.
* `DifferentialGradedModule.signTwist_mapTriangle_obj`: `signTwist A` carries a triangle to the
  same triangle with its third arrow negated.
* `DifferentialGradedModule.isDistinguishedTriangle_signTwist_mapTriangle` and
  `DifferentialGradedModule.signTwist_mapTriangle_mem_distinguishedConeTriangles`: `signTwist A`
  carries the cone triangles to the triangles of admissible short exact sequences and back.
* `DifferentialGradedModule.mapTriangle_signTwist_comp_mem_distTriang` and
  `DifferentialGradedModule.isTriangulated_signTwist_comp`: a functor out of `K(A, d)` carrying
  the triangles of admissible short exact sequences to distinguished triangles gives, after
  precomposition with `signTwist A`, a functor exact for the cone structure.
* `DifferentialGradedModule.mapTriangle_mem_distTriang_of_isTriangulated`: the hypothesis the
  previous two consume, extracted from exactness for the structure of Tag 09KH.

## Implementation notes

`signTwist A` is the identity endofunctor, but it is *not* `CategoryTheory.Functor.id`: a second
`CommShift` structure on `𝟭 _` would clash with Mathlib's, which is the trivial one. It is
therefore given a constant of its own, definitionally the identity, so that the twisted
`CommShift` attaches to it alone. That constant is the general one of
`StacksFrontier.CategoryTheory.Shift.SignTwist`, which exists for any preadditive category with a
shift by `ℤ` whose shift functors are additive; the names here are abbreviations for it, so that
the general lemmas about the twist apply to them.

The sign `ε(n) = (-1)^n` is a unit, which is what makes `ε(n) • 𝟙` an isomorphism, and it is
multiplicative, which is the `commShiftIso_add` axiom; `ε(0) = 1` is `commShiftIso_zero`. At
`n = 1` the comparison is `-𝟙`, which is the whole of the discrepancy between the two structures.

The two pretriangulated structures live on the *same* category, so a statement naming both
through `distTriang` cannot be made with one of them in scope. The transfer is therefore stated
in two halves, each with only the structure it needs in scope (the default cone structure, or the
admissible-sequence structure activated explicitly as a local instance), and the other class of
triangles named directly as a set (`distinguishedConeTriangles`, `IsDistinguishedTriangle`)
rather than through an instance.

## References

* [Stacks Project, Tag 09KH](https://stacks.math.columbia.edu/tag/09KH)
* [Stacks Project, Tag 09KF](https://stacks.math.columbia.edu/tag/09KF)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, v} R)

/-- The identity endofunctor of the homotopy category of right differential graded `A`-modules,
under a name of its own so that the sign-twisted shift comparison can be attached to it: the
sign-twisted identity `CategoryTheory.signTwist` of the homotopy category. -/
abbrev signTwist : HomotopyCategory.{u, v, w} A ⥤ HomotopyCategory.{u, v, w} A :=
  CategoryTheory.signTwist (HomotopyCategory.{u, v, w} A)

/-- The automorphism of the shift by `n` of the homotopy category given by the sign `(-1)^n`. -/
noncomputable abbrev signAut (n : ℤ) :
    CategoryTheory.shiftFunctor (HomotopyCategory.{u, v, w} A) n ≅
      CategoryTheory.shiftFunctor (HomotopyCategory.{u, v, w} A) n :=
  CategoryTheory.shiftSignAut (HomotopyCategory.{u, v, w} A) n

/-- The comparison of `DifferentialGradedModule.signTwist` with the shift by `n`: the sign
`(-1)^n` on the identity. -/
noncomputable abbrev signTwistCommShiftIso (n : ℤ) :
    CategoryTheory.shiftFunctor (HomotopyCategory.{u, v, w} A) n ⋙ signTwist.{u, v, w} A ≅
      signTwist.{u, v, w} A ⋙
        CategoryTheory.shiftFunctor (HomotopyCategory.{u, v, w} A) n :=
  CategoryTheory.signTwistCommShiftIso (HomotopyCategory.{u, v, w} A) n

/-- **The sign-twisted identity negates the third arrow.** `signTwist A` carries a triangle of
the homotopy category to the same triangle with its third arrow negated. -/
theorem signTwist_mapTriangle_obj (T : Triangle (HomotopyCategory.{u, v, w} A)) :
    (signTwist.{u, v, w} A).mapTriangle.obj T =
      Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) :=
  CategoryTheory.signTwist_mapTriangle_obj (HomotopyCategory.{u, v, w} A) T

/-- `signTwist A` carries a triangle isomorphic to a cone triangle to the triangle of an
admissible short exact sequence. -/
theorem isDistinguishedTriangle_signTwist_mapTriangle
    (T : Triangle (HomotopyCategory.{u, v, w} A))
    (hT : T ∈ distinguishedConeTriangles.{u, v, w} (A := A)) :
    IsDistinguishedTriangle A ((signTwist.{u, v, w} A).mapTriangle.obj T) := by
  rw [signTwist_mapTriangle_obj]
  exact (mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_negMor₃ T).mp hT

/-- `signTwist A` carries the triangle of an admissible short exact sequence to a triangle
isomorphic to a cone triangle. -/
theorem signTwist_mapTriangle_mem_distinguishedConeTriangles
    (T : Triangle (HomotopyCategory.{u, v, w} A)) (hT : IsDistinguishedTriangle A T) :
    (signTwist.{u, v, w} A).mapTriangle.obj T ∈
      distinguishedConeTriangles.{u, v, w} (A := A) := by
  rw [signTwist_mapTriangle_obj]
  exact mem_distinguishedConeTriangles_negMor₃_of_isDistinguishedTriangle T hT

/-- **The two pretriangulated structures on `K(Mod_(A, d))` are exchanged by the sign-twisted
identity.** A triangle lies in the cone class exactly when its image under `signTwist A` is the
triangle of an admissible short exact sequence, and symmetrically. The two structures are
therefore equivalent as pretriangulated categories, by an equivalence which is the identity on
objects and on morphisms and twists only the comparison with the shift; they are *not* the same
structure, the two classes of triangles being the two sign conventions for the third arrow. -/
@[stacks 09KH "the cone-triangle structure against the admissible-sequence structure: the two
are exchanged by the sign-twisted identity of the homotopy category"]
theorem mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_signTwist_mapTriangle
    (T : Triangle (HomotopyCategory.{u, v, w} A)) :
    T ∈ distinguishedConeTriangles.{u, v, w} (A := A) ↔
      IsDistinguishedTriangle A ((signTwist.{u, v, w} A).mapTriangle.obj T) := by
  rw [signTwist_mapTriangle_obj]
  exact mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_negMor₃ T

/-- **The sign comparison of the two pretriangulated structures on `K(Mod_(A, d))`.** A triangle
is distinguished for the admissible-sequence structure
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'` exactly when negating its third
arrow gives a triangle distinguished for the default cone-triangle structure
`DifferentialGradedModule.instPretriangulatedHomotopyCategory`. -/
@[stacks 09KF "the admissible-sequence pretriangulated structure against the cone-triangle one"]
theorem mem_distinguishedTriangles_admissible_iff
    (T : Triangle (HomotopyCategory.{u, v, w} A)) :
    T ∈ (instPretriangulatedHomotopyCategory' A).distinguishedTriangles ↔
      Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈
        (instPretriangulatedHomotopyCategory (A := A)).distinguishedTriangles := by
  rw [distinguishedTriangles_eq]
  change IsDistinguishedTriangle A T ↔
    Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈ distinguishedConeTriangles.{u, v, w} (A := A)
  rw [mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_negMor₃]
  exact ⟨fun h => isDistinguishedTriangle_of_iso A (negMor₃NegMor₃Iso T).symm h,
    fun h => isDistinguishedTriangle_of_iso A (negMor₃NegMor₃Iso T) h⟩

/-- **The sign comparison, from the side of the default structure.** A triangle is distinguished
for the cone-triangle structure `DifferentialGradedModule.instPretriangulatedHomotopyCategory`
exactly when negating its third arrow gives a triangle distinguished for the admissible-sequence
structure `DifferentialGradedModule.instPretriangulatedHomotopyCategory'`. -/
@[stacks 09KF "the cone-triangle pretriangulated structure against the admissible-sequence one"]
theorem mem_distinguishedTriangles_cone_iff
    (T : Triangle (HomotopyCategory.{u, v, w} A)) :
    T ∈ (instPretriangulatedHomotopyCategory (A := A)).distinguishedTriangles ↔
      Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈
        (instPretriangulatedHomotopyCategory' A).distinguishedTriangles := by
  rw [distinguishedTriangles_eq]
  exact mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_negMor₃ T

section Transfer

variable {D : Type*} [Category D] [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

/-- **The transfer, as a statement about triangles.** If `F` carries the triangles of admissible
short exact sequences to distinguished triangles, then `signTwist A ⋙ F` carries the triangles
isomorphic to a cone triangle to distinguished triangles. -/
theorem mapTriangle_signTwist_comp_mem_distTriang
    (F : HomotopyCategory.{u, v, w} A ⥤ D) [F.CommShift ℤ]
    (hF : ∀ T : Triangle (HomotopyCategory.{u, v, w} A), IsDistinguishedTriangle A T →
      F.mapTriangle.obj T ∈ distTriang D)
    (T : Triangle (HomotopyCategory.{u, v, w} A))
    (hT : T ∈ distinguishedConeTriangles.{u, v, w} (A := A)) :
    (signTwist.{u, v, w} A ⋙ F).mapTriangle.obj T ∈ distTriang D :=
  isomorphic_distinguished _ (hF _ (isDistinguishedTriangle_signTwist_mapTriangle A T hT)) _
    ((Functor.mapTriangleCompIso (signTwist.{u, v, w} A) F).app T)

section Cone

attribute [local instance 10000] instPretriangulatedHomotopyCategory
  instPreadditiveHomotopyCategory

/-- **The transfer.** A functor out of `K(A, d)` that carries the triangles of admissible short
exact sequences to distinguished triangles becomes, after precomposition with the sign-twisted
identity, an exact functor for the pretriangulated structure whose distinguished triangles are
the cone triangles.

This is the shape in which exactness proved against
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'` — the structure of Tag 09KH, in
which admissibility supplies the degreewise splittings — is consumed by material read against
`DifferentialGradedModule.instPretriangulatedHomotopyCategory`. The precomposition is not
cosmetic: `signTwist A ⋙ F` has the same underlying functor as `F` but the opposite comparison
with the shift at odd shifts, and `F` itself need not be exact for the cone structure. -/
theorem isTriangulated_signTwist_comp (F : HomotopyCategory.{u, v, w} A ⥤ D) [F.CommShift ℤ]
    (hF : ∀ T : Triangle (HomotopyCategory.{u, v, w} A), IsDistinguishedTriangle A T →
      F.mapTriangle.obj T ∈ distTriang D) :
    (signTwist.{u, v, w} A ⋙ F).IsTriangulated where
  map_distinguished T hT := by
    refine mapTriangle_signTwist_comp_mem_distTriang A F hF T ?_
    exact hT

end Cone

section Admissible

attribute [local instance 10000] instPretriangulatedHomotopyCategory'

/-- The hypothesis of `DifferentialGradedModule.isTriangulated_signTwist_comp`, extracted from
exactness for the pretriangulated structure of Tag 09KH. -/
theorem mapTriangle_mem_distTriang_of_isTriangulated
    (F : HomotopyCategory.{u, v, w} A ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (T : Triangle (HomotopyCategory.{u, v, w} A)) (hT : IsDistinguishedTriangle A T) :
    F.mapTriangle.obj T ∈ distTriang D :=
  F.map_distinguished T (by rw [distinguishedTriangles_eq]; exact hT)

end Admissible

end Transfer

end DifferentialGradedModule

end
