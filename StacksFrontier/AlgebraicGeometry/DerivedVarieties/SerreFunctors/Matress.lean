module

public import StacksCore.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Ring.NegOnePow
public import StacksCore.Tactic.StacksAttribute

/-!
# Matresses

A *matress* is a double complex of abelian groups whose rows and columns are all exact, which
carries a three-periodicity `K^{p,q} ≅ K^{p+3,q-3}` compatible with both differentials, and in
which every compatible pair on a diagonal admits a prescribed filling one step further along the
diagonal. The definition is made in an arbitrary concrete additive category, so that it applies
to complexes of modules and to their linear periodic identifications as well as to abelian
groups.

## Main definitions

* `HomologicalComplex₂.reindexIso` is the identification of two entries of a double complex
  obtained from equalities of their indices.
* `HomologicalComplex₂.Matress` is the additional structure that makes a double complex into a
  matress.

## Implementation notes

The periodic identifications are retained as morphisms of the ambient category rather than
merely asserted to exist; in `ModuleCat` they are therefore linear. The reindexing isomorphisms
appearing in the compatibility and filling fields make the integer index arithmetic explicit, so
that users of the structure can use the specified periodicity without choosing further
identifications. The filling field carries the sign `(-1)^(p+q)`, which is the convention under
which the periodic identifications commute with both differentials.

## References

* [Stacks Project, Tag 0H8B](https://stacks.math.columbia.edu/tag/0H8B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

universe u v w

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {FC : C → C → Type*} {CC : C → Type w}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory C FC] [∀ X, AddCommGroup (CC X)]

/-- The canonical identification of two entries of a double complex obtained from equalities of
their two indices. -/
def reindexIso (K : HomologicalComplex₂.DoubleComplex C)
    {p q p' q' : ℤ} (hp : p = p') (hq : q = q') : K.X p q ≅ K.X p' q' := by
  subst p'
  subst q'
  exact Iso.refl _

/-- **Stacks Project, Tag 0H8B.** A matress structure on a concrete double complex of abelian
groups: its rows and columns are exact, it is compatibly three-periodic, and every compatible
pair on a diagonal admits the prescribed filling. -/
@[stacks 0H8B "matress"]
structure Matress (K : HomologicalComplex₂.DoubleComplex C) where
  /-- Exactness of every row. -/
  row_exact (p q : ℤ) : Function.Exact (ConcreteCategory.hom (K.d₁ p q))
    (ConcreteCategory.hom (K.d₁ (p + 1) q))
  /-- Exactness of every column. -/
  column_exact (p q : ℤ) : Function.Exact (ConcreteCategory.hom (K.d₂ p q))
    (ConcreteCategory.hom (K.d₂ p (q + 1)))
  /-- The identification `K^{p,q} ≅ K^{p+3,q-3}`. -/
  periodic (p q : ℤ) : K.X p q ≅ K.X (p + 3) (q - 3)
  /-- The periodic identifications commute with the first differential. -/
  periodic_d₁ (p q : ℤ) :
    K.d₁ p q ≫ (periodic (p + 1) q).hom ≫
        (reindexIso K (p := (p + 1) + 3) (q := q - 3)
          (p' := p + 4) (q' := q - 3) (by omega) rfl).hom =
      (periodic p q).hom ≫ K.d₁ (p + 3) (q - 3) ≫
        (reindexIso K (p := (p + 3) + 1) (q := q - 3)
          (p' := p + 4) (q' := q - 3) (by omega) rfl).hom
  /-- The periodic identifications commute with the second differential. -/
  periodic_d₂ (p q : ℤ) :
    K.d₂ p q ≫ (periodic p (q + 1)).hom ≫
        (reindexIso K (p := p + 3) (q := (q + 1) - 3)
          (p' := p + 3) (q' := q - 2) rfl (by omega)).hom =
      (periodic p q).hom ≫ K.d₂ (p + 3) (q - 3) ≫
        (reindexIso K (p := p + 3) (q := (q - 3) + 1)
          (p' := p + 3) (q' := q - 2) rfl (by omega)).hom
  /-- The additional diagonal filling condition, with the signed shift convention. -/
  fill (p q : ℤ) (alpha : CC (K.X p q)) (beta : CC (K.X (p - 1) (q + 1)))
      (h : ConcreteCategory.hom (K.d₂ p q) alpha =
        (reindexIso K (p := (p - 1) + 1) (q := q + 1)
          (p' := p) (q' := q + 1) (by omega) rfl).hom
            (ConcreteCategory.hom (K.d₁ (p - 1) (q + 1)) beta)) :
      ∃ gamma : CC (K.X (p - 2) (q + 2)),
        (reindexIso K (p := (p - 2) + 1) (q := q + 2)
          (p' := p - 1) (q' := q + 2) (by omega) rfl).hom
            (ConcreteCategory.hom (K.d₁ (p - 2) (q + 2)) gamma) =
          (reindexIso K (p := p - 1) (q := (q + 1) + 1)
            (p' := p - 1) (q' := q + 2) rfl (by omega)).hom
              (ConcreteCategory.hom (K.d₂ (p - 1) (q + 1)) beta) ∧
          (reindexIso K (p := (p - 2) + 3) (q := (q + 3) - 3)
            (p' := p + 1) (q' := q) (by omega) (by omega)).hom
              ((periodic (p - 2) (q + 3)).hom
                ((reindexIso K (p := p - 2) (q := (q + 2) + 1)
                  (p' := p - 2) (q' := q + 3) rfl (by omega)).hom
                    (ConcreteCategory.hom (K.d₂ (p - 2) (q + 2)) gamma))) =
            (p + q).negOnePow • ConcreteCategory.hom (K.d₁ p q) alpha

end HomologicalComplex₂
