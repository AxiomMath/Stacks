module

public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Linearity of a functor checked on a class of objects reaching every object

Let `L : C ⥤ D` be an `R`-linear functor and `G : D ⥤ E` an additive functor between
`R`-linear categories. If every object of `D` is isomorphic to `L Y` for some `Y` in a class `P`
of objects of `C`, then `G` is `R`-linear as soon as `G (L (r • 𝟙 Y)) = r • 𝟙` for every `Y ∈ P`
and `r ∈ R`.

## Main results

* `CategoryTheory.Functor.linear_of_map_smul_id_of_resolving`: the criterion above.

## References

* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public section

namespace CategoryTheory

open Category

universe w v₁ v₂ v₃ u₁ u₂ u₃

/-- If every object of `D` is isomorphic to the image under the `R`-linear functor `L` of an object
of the class `P`, and `G` carries `L (r • 𝟙 Y)` to `r • 𝟙` for `Y ∈ P`, then `G` is
`R`-linear. -/
theorem Functor.linear_of_map_smul_id_of_resolving {R : Type w} [Semiring R] {C : Type u₁}
    [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
    [Preadditive C] [Preadditive D] [Preadditive E] [CategoryTheory.Linear R C]
    [CategoryTheory.Linear R D] [CategoryTheory.Linear R E]
    (L : C ⥤ D) [L.Linear R] (G : D ⥤ E)
    [G.Additive] (P : C → Prop) (hP : ∀ X : D, ∃ Y : C, P Y ∧ Nonempty (L.obj Y ≅ X))
    (h : ∀ (Y : C), P Y → ∀ r : R, G.map (L.map (r • 𝟙 Y)) = r • 𝟙 (G.obj (L.obj Y))) :
    G.Linear R := by
  rw [Functor.linear_iff]
  intro X r
  obtain ⟨Y, hY, ⟨e⟩⟩ := hP X
  have hX : r • 𝟙 X = e.inv ≫ L.map (r • 𝟙 Y) ≫ e.hom := by
    rw [L.map_smul, L.map_id, Linear.smul_comp, Linear.comp_smul, id_comp, e.inv_hom_id]
  rw [hX, G.map_comp, G.map_comp, h Y hY r, Linear.smul_comp, Linear.comp_smul, id_comp,
    ← G.map_comp, e.inv_hom_id, G.map_id]

end CategoryTheory
