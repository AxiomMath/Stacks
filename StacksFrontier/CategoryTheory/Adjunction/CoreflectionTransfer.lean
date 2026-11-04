module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Transferring an adjunction across a square of fully faithful functors

Let `k : C ⥤ D` and `j : D ⥤ P` with `j` fully faithful, let `i : A ⥤ P` have a right adjoint
`Q : P ⥤ A`, and let an equivalence `E : C ≌ A` make the square commute, in the sense that
`E.functor ⋙ i ≅ k ⋙ j`. Then `j ⋙ Q ⋙ E.inverse` is a right adjoint of `k`.

When `k` is in addition fully faithful, the counit of the resulting adjunction is invertible at
every object of the form `k.obj X`; that is already
`CategoryTheory.Adjunction.instIsIsoCounitApp` in Mathlib and needs nothing from here.

## Main definitions

* `CategoryTheory.Adjunction.transferredRightAdjoint` — the functor `j ⋙ Q ⋙ E.inverse`.
* `CategoryTheory.Adjunction.transferAlongEquivalence` — the adjunction `k ⊣ j ⋙ Q ⋙ E.inverse`.

## Implementation notes

The adjunction is `CategoryTheory.Adjunction.restrictFullyFaithful` applied to `i ⊣ Q` along the
two vertical functors `E.functor` and `j` of the square. Its second compatibility datum, relating
`j ⋙ Q` to `(j ⋙ Q ⋙ E.inverse) ⋙ E.functor`, is the counit of `E` and is supplied here as
`CategoryTheory.Adjunction.transferredCompIso`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {P : Type u₃} [Category.{v₃} P] {A : Type u₄} [Category.{v₄} A]
  (k : C ⥤ D) (j : D ⥤ P) {i : A ⥤ P} {Q : P ⥤ A} (E : C ≌ A)

/-- The functor `j ⋙ Q ⋙ E.inverse`, a right adjoint of `k` as soon as `j` is fully faithful and
the square `E.functor ⋙ i ≅ k ⋙ j` commutes. -/
public def transferredRightAdjoint : D ⥤ C := j ⋙ Q ⋙ E.inverse

/-- The identification of `j ⋙ Q` with `(j ⋙ Q ⋙ E.inverse) ⋙ E.functor` given by the counit of
the equivalence `E`. -/
public def transferredCompIso :
    j ⋙ Q ≅ transferredRightAdjoint j (Q := Q) E ⋙ E.functor :=
  NatIso.ofComponents (fun X ↦ (E.counitIso.app (Q.obj (j.obj X))).symm)
    fun f ↦ E.counitIso.inv.naturality (Q.map (j.map f))

/-- Transfer of an adjunction across a commuting square whose vertical functors are fully
faithful: if `i ⊣ Q`, if `j` is fully faithful and if the equivalence `E` satisfies
`E.functor ⋙ i ≅ k ⋙ j`, then `j ⋙ Q ⋙ E.inverse` is a right adjoint of `k`. -/
public noncomputable def transferAlongEquivalence (adj : i ⊣ Q) (hj : j.FullyFaithful)
    (comm : E.functor ⋙ i ≅ k ⋙ j) :
    k ⊣ transferredRightAdjoint j (Q := Q) E :=
  adj.restrictFullyFaithful E.fullyFaithfulFunctor hj comm (transferredCompIso j E)

end CategoryTheory.Adjunction

end
