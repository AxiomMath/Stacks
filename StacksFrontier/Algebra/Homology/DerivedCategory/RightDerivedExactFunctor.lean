module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-! # Higher right derived functors of an exact functor vanish

An additive functor `F : A ⥤ B` between abelian categories that preserves finite limits and
finite colimits has `R ⁿ F = 0` for every `n > 0`.

## Main results

* `CategoryTheory.Functor.isZero_rightDerived_of_exact`: `R ⁿ F (X) = 0` for `n > 0` when `F`
  is exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasInjectiveResolutions A]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **An exact functor has vanishing higher right derived functors.** For an additive functor
`F : A ⥤ B` of abelian categories preserving finite limits and finite colimits,
`R ⁿ F (X) = 0` for every object `X` and every `n > 0`. -/
theorem isZero_rightDerived_of_exact (X : A) (n : ℕ) (hn : 0 < n) :
    IsZero ((F.rightDerived n).obj X) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let I := injectiveResolution X
  have hExact : I.cocomplex.ExactAt (n + 1) :=
    (HomologicalComplex.exactAt_iff' I.cocomplex n (n + 1) (n + 2) (by simp) (by simp)).2
      (I.exact_succ n)
  exact ((F.map_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hExact)).of_iso
    ((I.cocomplex.sc (n + 1)).mapHomologyIso F)).of_iso (I.isoRightDerivedObj F (n + 1))

/-- **An exact functor has vanishing higher right derived functors**, stated for the
`ObjectProperty` spelling `CategoryTheory.exactFunctor` of exactness. -/
theorem isZero_rightDerived_of_exactFunctor (G : A ⥤ B) [G.Additive]
    (hG : exactFunctor A B G) (X : A) (n : ℕ) (hn : 0 < n) :
    IsZero ((G.rightDerived n).obj X) :=
  have h := (exactFunctor_iff G).1 hG
  have _ : PreservesFiniteLimits G := h.1
  have _ : PreservesFiniteColimits G := h.2
  isZero_rightDerived_of_exact G X n hn

end CategoryTheory.Functor

end
