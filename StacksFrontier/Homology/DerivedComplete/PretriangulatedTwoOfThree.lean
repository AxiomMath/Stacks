module

public import StacksFrontier.Homology.DerivedComplete

/-!
# Two-out-of-three for derived completeness in a pretriangulated category

`isDerivedCompleteAt_of_distTriang` proves that derived completeness at a scalar `f`, the
invertibility of `1 - f` on a countable product, satisfies two-out-of-three in a distinguished
triangle of the derived category `D(A)` of a commutative ring. The proof uses only that products
of distinguished triangles are distinguished and that `1 - f` commutes with the shift, so it holds
in every `A`-linear pretriangulated category with countable products and `A`-linear shift
functors; this file records that statement.

## Main results

* `isDerivedCompleteAt_of_distTriang_of_pretriangulated`: if the second and third objects of a
  distinguished triangle are derived complete at `f`, then so is the first.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

section Pretriangulated

variable {A : Type*} [CommRing A] {D : Type*} [Category D] [Preadditive D] [Linear A D]
  [HasProductsOfShape ℕ D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D n).Linear A]
  [Pretriangulated D]

/-- Derived completeness at `f` satisfies two-out-of-three in a distinguished triangle of an
`A`-linear pretriangulated category with countable products: if the second and third objects of
a distinguished triangle are derived complete at `f`, then so is the first. -/
theorem isDerivedCompleteAt_of_distTriang_of_pretriangulated {T : Triangle D}
    (hT : T ∈ distTriang D) {f : A}
    (h₂ : IsDerivedCompleteAt T.obj₂ f) (h₃ : IsDerivedCompleteAt T.obj₃ f) :
    IsDerivedCompleteAt T.obj₁ f := by
  rw [isDerivedCompleteAt_iff_isIso]
  have hPTdist := productTriangle_distinguished (J := ℕ) (fun _ : ℕ => T) (fun _ => hT)
  let φ : productTriangle (fun _ : ℕ => T) ⟶ productTriangle (fun _ : ℕ => T) :=
    Triangle.homMk (productTriangle (fun _ : ℕ => T)) (productTriangle (fun _ : ℕ => T))
      (oneSubSmulShift T.obj₁ f) (oneSubSmulShift T.obj₂ f) (oneSubSmulShift T.obj₃ f)
      (by
        rw [productTriangle_mor₁]
        exact (oneSubSmulShift_naturality f _).symm)
      (by
        rw [productTriangle_mor₂]
        exact (oneSubSmulShift_naturality f _).symm)
      (by
        rw [productTriangle_mor₃]
        change (Limits.Pi.map (fun _ : ℕ => T.mor₃) ≫
            inv (piComparison (shiftFunctor D (1 : ℤ))
              (fun _ : ℕ => T.obj₁))) ≫
              (shiftFunctor D (1 : ℤ)).map
                (oneSubSmulShift T.obj₁ f)
          = oneSubSmulShift T.obj₃ f ≫
            (Limits.Pi.map (fun _ : ℕ => T.mor₃) ≫
              inv (piComparison (shiftFunctor D (1 : ℤ))
                (fun _ : ℕ => T.obj₁)))
        set pc := piComparison (shiftFunctor D (1 : ℤ))
          (fun _ : ℕ => T.obj₁)
        have hnat := oneSubSmulShift_naturality f T.mor₃
        have hshift' :
            oneSubSmulShift ((shiftFunctor D (1 : ℤ)).obj T.obj₁) f
                ≫ inv pc
              = inv pc ≫ (shiftFunctor D (1 : ℤ)).map
                  (oneSubSmulShift T.obj₁ f) := by
          rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
          exact piComparison_comp_oneSubSmulShift T.obj₁ f
        rw [Category.assoc, ← hshift', ← Category.assoc, ← hnat, Category.assoc])
  exact isIso₁_of_isIso₂₃ φ hPTdist hPTdist (isDerivedCompleteAt_iff_isIso.mp h₂)
    (isDerivedCompleteAt_iff_isIso.mp h₃)

end Pretriangulated

end
