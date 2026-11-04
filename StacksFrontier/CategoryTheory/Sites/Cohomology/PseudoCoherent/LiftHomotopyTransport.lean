module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Transport of a lift up to homotopy along an isomorphism of functors

Let `P : A₁ ⥤ A₂`, `Q : A₂ ⥤ A₃` and `T : A₁ ⥤ A₃` be additive functors with an isomorphism
`P ⋙ Q ≅ T` on cochain complexes. A lift up to homotopy of `(P ⋙ Q) α` through `(P ⋙ Q) f`
becomes a lift up to homotopy of `T α` through `T f`.

## Main results

* `AlgebraicGeometry.RingedSite.exists_lift_homotopy_of_natIso_comp`: transport of a lift up to
  homotopy along an isomorphism of the functors restricting it, with the lift given over the
  composite of the two factors.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.RingedSite

/-- Transport of a lift up to homotopy along an isomorphism `P ⋙ Q ≅ T` of functors, with the
lift given over the composite `P ⋙ Q`. -/
theorem exists_lift_homotopy_of_natIso_comp {A₁ A₂ A₃ : Type*}
    [Category A₁] [Category A₂] [Category A₃]
    [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
    (P : A₁ ⥤ A₂) (Q : A₂ ⥤ A₃) (T : A₁ ⥤ A₃) [P.Additive] [Q.Additive] [T.Additive]
    (ε : P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Q.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      T.mapHomologicalComplex (ComplexShape.up ℤ))
    {E F G : CochainComplex A₁ ℤ} (α : E ⟶ F) (f : G ⟶ F)
    (γ : (P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Q.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
      (P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Q.mapHomologicalComplex (ComplexShape.up ℤ)).obj G)
    (hγ : Homotopy (γ ≫ (P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Q.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
      ((P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Q.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) :
    ∃ δ : (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
        (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj G,
      Nonempty (Homotopy (δ ≫ (T.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map α)) := by
  refine ⟨ε.inv.app E ≫ γ ≫ ε.hom.app G, ⟨?_⟩⟩
  have h := (hγ.compLeft (ε.inv.app E)).compRight (ε.hom.app F)
  have hf := ε.hom.naturality f
  have hα := NatIso.naturality_1 ε α
  dsimp only [Functor.comp_map] at h hf hα
  simpa only [Functor.map_comp, Category.assoc, hf, hα] using h

end AlgebraicGeometry.RingedSite

end
