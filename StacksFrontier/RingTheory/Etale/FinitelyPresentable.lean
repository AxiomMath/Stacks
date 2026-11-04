module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic

/-!
# Étale algebras are finitely presentable objects

An étale algebra is of finite presentation as a ring map, and under the equivalence between
`CommAlgCat R` and the category of rings under `R` finite presentation of a ring map is exactly
finite presentability of the corresponding object. So an étale `R`-algebra is a finitely
presentable object of `CommAlgCat R`.

## Main results

* `CommAlgCat.isFinitelyPresentable_of_etale`: an étale `R`-algebra is a finitely presentable
  object of `CommAlgCat R`.
-/

@[expose] public section

open CategoryTheory

universe u

attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace CommAlgCat

/-- Étale algebras are finitely presentable objects of `CommAlgCat R`. -/
theorem isFinitelyPresentable_of_etale {R : Type u} [CommRing R] (A : CommAlgCat.{u} R)
    [Algebra.Etale R A] : IsFinitelyPresentable.{u} A := by
  rw [IsFinitelyPresentable, ← isCardinalPresentable_iff_of_isEquivalence A _
    (commAlgCatEquivUnder (CommRingCat.of R)).functor]
  exact CommRingCat.isFinitelyPresentable_under (CommRingCat.of R) _
    ((RingHom.finitePresentation_algebraMap (A := R) (B := A)).mpr inferInstance)

end CommAlgCat
