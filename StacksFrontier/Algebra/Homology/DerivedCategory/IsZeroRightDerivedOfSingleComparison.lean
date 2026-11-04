module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective

/-!
# Vanishing of the higher right derived functors from the unbounded comparison

Let `w : A ⥤ B` be an additive functor between abelian categories, `A` with enough injectives,
and let `Rw` with unit `α` be a right derived functor of `w` on unbounded derived categories.
If the comparison `α : Qh(w(X[0])) ⟶ Rw(Qh(X[0]))` is an isomorphism at an object `X` placed in
degree `0`, then `Rⁿw(X) = 0` for `n > 0`: by `Hⁿ(Rw(X[0])) ≅ Rⁿw(X)` the left side is
`Hⁿ((wX)[0])`, which vanishes away from degree `0`.

## Main results

* `isZero_rightDerived_obj_of_isIso_app_singleFunctor_isZeroRightDerivedOfSingleComparison`:
  if `α` is invertible at `X[0]`, then `Rⁿw(X) = 0` for `n > 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe wA vA uA wB vB uB

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (w : A ⥤ B) [w.Additive]
  (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw)
  [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **The higher right derived functors vanish where the unbounded comparison is invertible on
the single complex.** If `α` is invertible at `X[0]`, then `Rw(X[0]) ≅ (wX)[0]`, so
`Rⁿw(X) ≅ Hⁿ(Rw(X[0]))` vanishes for `n > 0`. -/
theorem isZero_rightDerived_obj_of_isIso_app_singleFunctor_isZeroRightDerivedOfSingleComparison
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (X : A) (hX : IsIso (α.app ((HomotopyCategory.singleFunctor A 0).obj X)))
    (n : ℕ) (hn : 0 < n) :
    IsZero ((w.rightDerived n).obj X) := by
  have hz : IsZero ((DerivedCategory.homologyFunctor B (n : ℤ)).obj
      ((DerivedCategory.singleFunctor B 0).obj (w.obj X))) :=
    DerivedCategory.isZero_of_isLE _ 0 (n : ℤ) (by exact_mod_cast hn)
  refine hz.of_iso ?_
  refine ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived w Rw α hres
    n).app X).symm ≪≫ (DerivedCategory.homologyFunctor B (n : ℤ)).mapIso ?_
  exact Rw.mapIso ((DerivedCategory.singleFunctorIsoCompQh A 0).app X) ≪≫
    (asIso (α.app ((HomotopyCategory.singleFunctor A 0).obj X))).symm ≪≫
      DerivedCategory.Qh.mapIso ((Functor.mapHomotopyCategorySingleFunctor w 0).app X) ≪≫
        ((DerivedCategory.singleFunctorIsoCompQh B 0).app (w.obj X)).symm

end CategoryTheory.Functor

end
