module

public import Mathlib.Algebra.Homology.Functor

/-!
# A functor to complexes as a complex of functors

A complex of functors `T ⥤ V` gives a functor `T ⥤ HomologicalComplex V c`, which is
`HomologicalComplex.asFunctor`. This file supplies the other direction: a functor to complexes
read as a complex of functors, degreewise by evaluation.

## Main definitions

* `HomologicalComplex.ofFunctorToComplex`: the complex of functors attached to a functor to
  complexes.

## Implementation notes

Mathlib's `Mathlib/Algebra/Homology/Functor.lean` records the equivalence
`HomologicalComplex (T ⥤ V) c ≌ T ⥤ HomologicalComplex V c` as future work and constructs only
the forgetful direction; this is the construction in the other direction, which is what a
levelwise complex over an index category needs in order to be read as a complex of presheaves.
-/
@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {T : Type*} [Category* T] {V : Type*} [Category* V] [HasZeroMorphisms V]
  {ι : Type*} {c : ComplexShape ι}

/-- A functor to complexes gives a complex of functors. This is the direction opposite to
`HomologicalComplex.asFunctor`. -/
@[simps]
def ofFunctorToComplex (F : T ⥤ HomologicalComplex V c) : HomologicalComplex (T ⥤ V) c where
  X i := F ⋙ eval V c i
  d i j :=
    { app t := (F.obj t).d i j
      naturality _ _ f := (F.map f).comm i j }
  shape i j h := by
    ext t
    exact (F.obj t).shape i j h
  d_comp_d' i j k _ _ := by
    ext t
    exact (F.obj t).d_comp_d i j k

end HomologicalComplex

end
