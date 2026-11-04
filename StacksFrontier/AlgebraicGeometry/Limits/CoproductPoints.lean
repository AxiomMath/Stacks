module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Morphisms from a one-point scheme into a coproduct

A coproduct of schemes is the disjoint union of its summands, so a morphism into it from a
scheme with exactly one point has image inside a single summand, and therefore factors
through that summand's coproduct inclusion.

## Main results

* `AlgebraicGeometry.exists_factorization_sigmaι_of_unique`: such a factorization exists.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism into a coproduct of schemes from a scheme with exactly one point factors
through one of the coproduct inclusions. -/
theorem exists_factorization_sigmaι_of_unique {A : Scheme.{u}} [Unique A] {ι : Type u}
    [Small.{u} ι] (X : ι → Scheme.{u}) (f : A ⟶ ∐ X) :
    ∃ (i : ι) (g : A ⟶ X i), g ≫ Sigma.ι X i = f := by
  let q := (sigmaMk X).symm (f.base default)
  have hpoint : f.base default = (Sigma.ι X q.1).base q.2 := by
    calc
      f.base default = sigmaMk X q := ((sigmaMk X).apply_symm_apply _).symm
      _ = sigmaMk X ⟨q.1, q.2⟩ := congrArg _ (Sigma.eta q).symm
      _ = (Sigma.ι X q.1).base q.2 := sigmaMk_mk X q.1 q.2
  have hrange : Set.range f.base ⊆ Set.range (Sigma.ι X q.1).base := by
    rintro y ⟨z, rfl⟩
    exact ⟨q.2, by rw [show z = default from Subsingleton.elim _ _]; exact hpoint.symm⟩
  exact ⟨q.1, IsOpenImmersion.lift (Sigma.ι X q.1) f hrange, IsOpenImmersion.lift_fac _ _ _⟩

end AlgebraicGeometry

end
