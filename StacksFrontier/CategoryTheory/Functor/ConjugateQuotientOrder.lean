module

public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotient

/-!
# Comparing conjugate quotients

Let `e : P₂ ≅ P₁ ⋙ L` be a comparison of functors into abelian categories, with `L` right exact.
For two subobjects `K, K'` of `P₁ M`, the conjugate `CategoryTheory.Functor.conjSubobject e K` is
contained in `CategoryTheory.Functor.conjSubobject e K'` exactly when the composite
`K ⟶ P₁ M ⟶ P₁ M / K'` becomes zero after applying `L`.

## Main results

* `CategoryTheory.Functor.conjSubobject_le_conjSubobject_iff`: `conjSubobject e K` is contained in
  `conjSubobject e K'` if and only if `L` kills `K ⟶ P₁ M ⟶ P₁ M / K'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type*} {D₁ : Type*} {D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
  [Abelian D₁] [Abelian D₂] {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}

/-- **Order of conjugate quotients.** For a right exact `L` and a comparison `e : P₂ ≅ P₁ ⋙ L`, the
conjugate of `K` is contained in the conjugate of `K'` exactly when `L` kills the composite of the
inclusion of `K` with the projection onto the quotient by `K'`. -/
theorem conjSubobject_le_conjSubobject_iff (hL : PreservesFiniteColimits L)
    (e : P₂ ≅ P₁ ⋙ L) {M : C} (K K' : Subobject (P₁.obj M)) :
    conjSubobject e K ≤ conjSubobject e K' ↔ L.map (K.arrow ≫ cokernel.π K'.arrow) = 0 := by
  change kernelSubobject (conjQuotientProjection e K) ≤
    kernelSubobject (conjQuotientProjection e K') ↔ _
  constructor
  · intro hle
    let w : L.obj (K : D₁) ⟶ P₂.obj M := L.map K.arrow ≫ CategoryTheory.inv (e.hom.app M)
    have hw : (kernelSubobject (conjQuotientProjection e K)).Factors w := by
      rw [kernelSubobject_factors_iff]
      simp only [w, conjQuotientProjection, Category.assoc, IsIso.inv_hom_id_assoc,
        ← L.map_comp, cokernel.condition, L.map_zero]
    simpa only [w, conjQuotientProjection, Category.assoc, IsIso.inv_hom_id_assoc, L.map_comp]
      using (kernelSubobject_factors_iff _ w).1 (Subobject.factors_of_le w hle hw)
  · intro h
    let φ : L.obj (cokernel K.arrow) ⟶ L.obj (cokernel K'.arrow) :=
      (PreservesCokernel.iso L K.arrow).hom ≫
        cokernel.desc (L.map K.arrow) (L.map (cokernel.π K'.arrow))
          (by rwa [← L.map_comp])
    have heq : conjQuotientProjection e K ≫ φ = conjQuotientProjection e K' := by
      simp [φ, conjQuotientProjection]
    exact heq ▸ kernelSubobject_comp_le _ φ

end CategoryTheory.Functor

end
