module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TransitionCocycle

/-!
# Cartesian sheaves are detected by the face maps

Let `S` be a simplicial-site situation. A sheaf on its total site is cartesian when the canonical
transition `f_φ⁻¹ Fₘ ⟶ Fₙ` is an isomorphism for every arrow `φ` of the simplex category. This
file shows that it suffices to test the face maps `δ i`, for both sheaves of sets and sheaves of
abelian groups. For sheaves of abelian groups the condition is stated with the abelian transition
`CategoryTheory.SimplicialSiteSituation.abelianFiberTransition`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isCartesianSheaf_iff_faces`: **Stacks 07TG** for a
  sheaf of sets.
* `CategoryTheory.SimplicialSiteSituation.isCartesianAbSheaf_iff_faces`: **Stacks 07TG** for a
  sheaf of abelian groups.

## References

* [Stacks Project, Tag 07TG](https://stacks.math.columbia.edu/tag/07TG)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- **Stacks 07TG.** A sheaf of sets on the total site of a simplicial site is cartesian if and
only if the canonical transition along every face map is an isomorphism. -/
@[stacks 07TG "face criterion for sheaves of sets"]
theorem isCartesianSheaf_iff_faces (F : Sheaf S.totalTopology (Type u)) :
    IsCartesianSheaf S F ↔
      ∀ (n : ℕ) (i : Fin (n + 2)),
        IsIso ((fiberTransition S (SimplexCategory.δ i)).app F) := by
  refine ⟨fun h n i => h _, fun h => ?_⟩
  let W : MorphismProperty SimplexCategory := fun _ _ φ => IsIso ((fiberTransition S φ).app F)
  have hid (n : SimplexCategory) : W (𝟙 n) := by
    change IsIso _
    rw [fiberTransition_id]
    infer_instance
  have : W.IsMultiplicative :=
    { id_mem := hid
      comp_mem ψ φ (_ : IsIso _) (_ : IsIso _) := by
        change IsIso _
        rw [fiberTransition_comp]
        infer_instance }
  have hσ {n : ℕ} (i : Fin (n + 1)) : W (SimplexCategory.σ i) := by
    have : IsIso ((fiberTransition S (SimplexCategory.δ i.castSucc)).app F) := h _ i.castSucc
    have hc : IsIso ((fiberTransition S
        (SimplexCategory.δ i.castSucc ≫ SimplexCategory.σ i)).app F) := by
      rw [SimplexCategory.δ_comp_σ_self]
      exact hid _
    rw [fiberTransition_comp] at hc
    exact (isIso_comp_left_iff _ _).mp ((isIso_comp_left_iff _ _).mp hc)
  intro m n φ
  exact show W φ from SimplexCategory.morphismProperty_eq_top W (fun i => h _ i) hσ ▸ trivial

/-- **Stacks 07TG.** A sheaf of abelian groups on the total site of a simplicial site is
cartesian if and only if the canonical transition along every face map is an isomorphism. -/
@[stacks 07TG "face criterion for sheaves of abelian groups"]
theorem isCartesianAbSheaf_iff_faces (F : Sheaf S.totalTopology Ab.{u}) :
    IsCartesianAbSheaf S F ↔
      ∀ (n : ℕ) (i : Fin (n + 2)),
        IsIso ((abelianFiberTransition S (SimplexCategory.δ i)).app F) := by
  rw [IsCartesianAbSheaf, isCartesianSheaf_iff_faces]
  exact forall_congr' fun n => forall_congr' fun i =>
    (abelianFiberTransition_isIso_iff S (SimplexCategory.δ i) F).symm

end CategoryTheory.SimplicialSiteSituation

end
