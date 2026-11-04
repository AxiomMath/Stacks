module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AssociatedDerivedSystem

/-!
# Cartesian objects of `D(C_total)` are detected by the face maps

Let `S` be a simplicial-site situation. An object `K` of the derived category of abelian
sheaves on the total site is cartesian when the canonical derived transition
`L(f_φ)^{-1} K_m ⟶ K_n` is an isomorphism for every arrow `φ` of the simplex category. This
file shows that it suffices to test the face maps `δ i`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isCartesianDerived_iff_faces`: **Stacks 07TG (2)**.

## Implementation notes

The simplex maps whose derived transition is invertible form a multiplicative class of
morphisms: the identity and composition laws for that class are the unit and cocycle laws
`CategoryTheory.SimplicialSiteSituation.derivedTransition_id_app` and
`derivedTransition_comp_app` of Stacks 0D9H. Since every arrow of the simplex category is a
composite of faces and degeneracies (`SimplexCategory.morphismProperty_eq_top`), the criterion
follows once the degeneracies are covered, and `SimplexCategory.δ_comp_σ_self` exhibits each
degeneracy as the second factor of a composite that is an identity. So no separate hypothesis
on the degeneracies is needed, exactly as in the underived case
`CategoryTheory.SimplicialSiteSituation.isCartesianSheaf_iff_faces`.

## References

* [Stacks Project, Tag 07TG](https://stacks.math.columbia.edu/tag/07TG)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 0D9H](https://stacks.math.columbia.edu/tag/0D9H)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.SimplicialSiteSituation

attribute [local implicit_reducible] CategoryTheory.derivedInverseImage

variable (S : SimplicialSiteSituation.{u})
  [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})]
  [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})]

/-- **Stacks 07TG (2).** An object of the derived category of abelian sheaves on the total site
of a simplicial site is cartesian if and only if the canonical derived transition along every
face map is an isomorphism. -/
@[stacks 07TG "face criterion for objects of D(C_total)"]
theorem isCartesianDerived_iff_faces (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    S.IsCartesianDerived K ↔
      ∀ (k : ℕ) (i : Fin (k + 2)),
        IsIso ((derivedTransition S (SimplexCategory.δ i)).app K) := by
  refine ⟨fun h k i => h _, fun h => ?_⟩
  have hid : ∀ n : SimplexCategory, IsIso ((derivedTransition S (𝟙 n)).app K) := by
    intro n
    rw [derivedTransition_id_app]
    infer_instance
  have hcomp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      IsIso ((derivedTransition S ψ).app K) → IsIso ((derivedTransition S φ).app K) →
        IsIso ((derivedTransition S (ψ ≫ φ)).app K) := by
    intro l m n ψ φ _ _
    rw [derivedTransition_comp_app]
    infer_instance
  let W : MorphismProperty SimplexCategory :=
    fun _ _ φ => IsIso ((derivedTransition S φ).app K)
  have : W.ContainsIdentities := ⟨hid⟩
  have : W.IsStableUnderComposition := ⟨fun ψ φ hψ hφ => hcomp ψ φ hψ hφ⟩
  have : W.IsMultiplicative := ⟨⟩
  have hδ : ∀ {k : ℕ} (i : Fin (k + 2)), W (SimplexCategory.δ i) := fun i => h _ i
  have hσ : ∀ {k : ℕ} (i : Fin (k + 1)), W (SimplexCategory.σ i) := by
    intro k i
    have hψ : IsIso ((derivedTransition S (SimplexCategory.δ i.castSucc)).app K) :=
      hδ i.castSucc
    have hc : IsIso ((derivedTransition S
        (SimplexCategory.δ i.castSucc ≫ SimplexCategory.σ i)).app K) := by
      rw [SimplexCategory.δ_comp_σ_self]
      exact hid _
    rw [derivedTransition_comp_app] at hc
    have hmap : IsIso ((derivedInverseImage S (SimplexCategory.σ i)).map
        ((derivedTransition S (SimplexCategory.δ i.castSucc)).app K)) :=
      inferInstance
    exact (isIso_comp_left_iff _ _).mp ((isIso_comp_left_iff _ _).mp hc)
  have hW := SimplexCategory.morphismProperty_eq_top W hδ hσ
  intro m n φ
  exact show W φ by rw [hW]; trivial

end CategoryTheory.SimplicialSiteSituation

end
