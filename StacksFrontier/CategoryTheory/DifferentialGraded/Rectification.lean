module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.ConeSituation

/-!
# Rectifying homotopy-commutative squares in a differential graded category

A square of closed degree-zero morphisms of a differential graded category which commutes only
up to a coboundary can be made to commute strictly, by replacing one of its two vertical arrows
by a homotopic one, provided that the horizontal arrow opposite to it is admissible: an
admissible monomorphism along the top rectifies the right arrow, and an admissible epimorphism
along the bottom rectifies the left one. In each case the replacement differs from the original
by the coboundary of the chosen homotopy composed with the splitting.

## Main definitions

* `DGCategory.IsAdmissibleMono`: a closed degree-zero morphism admitting a degree-zero
  retraction in the underlying graded category.

## Main results

* `DGCategory.exists_rectification_of_isAdmissibleMono`: the rectified right arrow.
* `DGCategory.exists_rectification_left`: the rectified left arrow, for a square presented as a
  `DGCategory.HomotopyCommutativeSquare` of a cone situation.

## Implementation notes

For a general differential graded category admissibility is expressed by a degree-zero
retraction, respectively a degree-zero section, which is not required to be closed; this is the
graded splitting the source proof uses, and the admissibility predicate for differential graded
modules does not apply to the objects of an arbitrary differential graded category. In the
monomorphism case the square is given by its four arrows together with a homotopy between its
two composites rather than as a bundled object, since no other part of such a bundle is needed.

## References

* [Stacks Project, Tag 09QL](https://stacks.math.columbia.edu/tag/09QL)
-/

@[expose] public section

universe u v w

namespace DGCategory

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R}

/-- A closed degree-zero morphism that admits a degree-zero retraction in the underlying graded
category. The retraction is not required to be closed. -/
abbrev IsAdmissibleMono {x y : A.Obj} (f : A.Cocycle x y) : Prop :=
  ∃ π : A.Hom y x 0, A.comp (show (0 : ℤ) + 0 = 0 by omega) π f.1 = A.id x

/-- Adding a coboundary `d' k` to a cocycle gives a homotopic cocycle. -/
private theorem exists_homotopic_add_d' {x y : A.Obj} (c : A.Cocycle x y) (k : A.Hom x y (-1)) :
    ∃ c' : A.Cocycle x y,
      c'.1 = c.1 + A.d' (show (-1 : ℤ) + 1 = 0 by omega) k ∧ A.Homotopic c c' := by
  refine ⟨⟨c.1 + A.d' (show (-1 : ℤ) + 1 = 0 by omega) k, ?_⟩, rfl, -k, ?_⟩
  · simp only [DGCategory.d']; rw [A.d_add, c.2, A.d_d, add_zero]
  · simp only [DGCategory.d']
    rw [show -k = (-1 : R) • k by rw [neg_one_smul], A.d_smul, neg_one_smul]; abel

/-- Rectify the right arrow of a homotopy-commutative square along an admissible
monomorphism. -/
@[stacks 09QL "adjust_right"]
theorem exists_rectification_of_isAdmissibleMono {x y z w : A.Obj}
    (f : A.Cocycle x y) (a : A.Cocycle x z) (b : A.Cocycle y w) (g : A.Cocycle z w)
    (hcomm : A.Homotopic (A.compCocycle b f) (A.compCocycle g a))
    (hf : IsAdmissibleMono f) :
    ∃ b' : A.Cocycle y w,
      A.Homotopic b b' ∧ A.compCocycle b' f = A.compCocycle g a := by
  obtain ⟨h, hh⟩ := A.homotopic_symm hcomm
  obtain ⟨π, hπ⟩ := hf
  obtain ⟨b', hb', hbb'⟩ :=
    exists_homotopic_add_d' b (A.comp (show (-1 : ℤ) + 0 = -1 by omega) h π)
  refine ⟨b', hbb', Subtype.ext ?_⟩
  simp only [DGCategory.compCocycle] at hh ⊢
  rw [hb', A.comp_add_left, A.comp_dboundary_left f.1 f.2,
    ← A.assoc (show (0 : ℤ) + 0 = 0 by omega) (show (-1 : ℤ) + 0 = -1 by omega)
      (show (-1 : ℤ) + 0 = -1 by omega) (show (-1 : ℤ) + 0 = -1 by omega) h π f.1,
    hπ, A.comp_id, ← hh]
  abel

/-- Rectify the left arrow of a homotopy-commutative square along an admissible epimorphism,
presented by a degree-zero section of its lower horizontal arrow. -/
@[stacks 09QL "adjust_left"]
theorem exists_rectification_left (C : ConeSituation A) (S : HomotopyCommutativeSquare C)
    (hg : ∃ s : A.Hom S.w S.z 0,
      A.comp (show (0 : ℤ) + 0 = 0 by omega) S.g.1 s = A.id S.w) :
    ∃ a' : A.Cocycle S.x S.z,
      A.Homotopic S.a a' ∧ A.compCocycle S.g a' = A.compCocycle S.b S.f := by
  rcases hg with ⟨s, hs⟩
  obtain ⟨a', ha', haa'⟩ :=
    exists_homotopic_add_d' S.a (A.comp (show (0 : ℤ) + (-1) = -1 by omega) s S.h)
  refine ⟨a', haa', Subtype.ext ?_⟩
  change A.comp (show (0 : ℤ) + 0 = 0 by omega) S.g.1 a'.1 =
    A.comp (show (0 : ℤ) + 0 = 0 by omega) S.b.1 S.f.1
  rw [ha', A.comp_add_right, A.comp_dboundary_right S.g.1 S.g.2,
    A.assoc (show (0 : ℤ) + (-1) = -1 by omega) (show (0 : ℤ) + (-1) = -1 by omega)
      (show (0 : ℤ) + 0 = 0 by omega) (show (0 : ℤ) + (-1) = -1 by omega) S.g.1 s S.h,
    hs, A.id_comp, ← S.commutes_up_to_homotopy]
  dsimp only [DGCategory.compCocycle]
  abel

end DGCategory
