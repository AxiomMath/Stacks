module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import StacksCore.CategoryTheory.GradedObject.Abelian
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotivesUniversalProperty
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilRealization

/-!
# Realizations are determined by their restriction to correspondences of degree zero

A realization `G : M_k ⥤ graded F-vector spaces` (side (2) of Stacks 0FHM,
`Stacks.WeilCohomology.WeilRealization`) is determined up to monoidal isomorphism by its
restriction along `X ↦ (X, 1, 0)` to the category of smooth projective schemes with
correspondences of degree zero: this is the uniqueness half of the universal property of
`M_k` (Stacks 0FGH, `Stacks.WeilCohomology.ChowMotiveCat.universalProperty`).

The file also records the combinatorics of the proof of Stacks 0FHM: a relation `R` between two
setoids that relates every element of either side to the image of a map, is compatible with the
equivalences, and is "functional" in both directions, induces a bijection of the quotients
(`Stacks.WeilCohomology.exists_quotientEquiv_of_rel`).

## Main results

* `Stacks.WeilCohomology.WeilRealization.rel_of_untwisted`: two realizations whose restrictions to
  correspondences of degree zero are monoidally isomorphic to the same functor are monoidally
  isomorphic.
* `Stacks.WeilCohomology.exists_quotientEquiv_of_rel`: the bijection of quotients.

## References

* [Stacks Project, Tag 0FGH](https://stacks.math.columbia.edu/tag/0FGH)
* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.GradedCategory

universe u w

namespace Stacks.WeilCohomology

/-- **A relation between two setoids inducing a bijection of the quotients.** Let `R` relate `a`
to `Φ a` and `Ψ b` to `b`, be compatible with the equivalence relations on both sides, relate
`a` and `a'` to a common `b` only if `a ≈ a'`, and relate `a` to `b` only if `Φ a ≈ b`. Then
`Φ` and `Ψ` induce mutually inverse bijections of the quotients. -/
theorem exists_quotientEquiv_of_rel {α : Type*} {β : Type*} [sα : Setoid α] [sβ : Setoid β]
    (R : α → β → Prop) (Φ : α → β) (Ψ : β → α) (hΦ : ∀ a, R a (Φ a)) (hΨ : ∀ b, R (Ψ b) b)
    (hRα : ∀ a a' b, a ≈ a' → R a b → R a' b) (hRβ : ∀ a b b', b ≈ b' → R a b → R a b')
    (hα : ∀ a a' b, R a b → R a' b → a ≈ a') (hβ : ∀ a b, R a b → Φ a ≈ b) :
    ∃ e : Quotient sα ≃ Quotient sβ, (∀ a, e ⟦a⟧ = ⟦Φ a⟧) ∧ ∀ b, e.symm ⟦b⟧ = ⟦Ψ b⟧ := by
  have hΦ' : ∀ a a', a ≈ a' → Φ a ≈ Φ a' := fun a a' h ↦
    Setoid.symm (hβ a' _ (hRα a a' _ h (hΦ a)))
  have hΨ' : ∀ b b', b ≈ b' → Ψ b ≈ Ψ b' := fun b b' h ↦ hα _ _ b' (hRβ _ b b' h (hΨ b)) (hΨ b')
  refine ⟨⟨Quotient.map Φ hΦ', Quotient.map Ψ hΨ', ?_, ?_⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  · refine Quotient.ind fun a ↦ Quotient.sound ?_
    exact hα _ _ (Φ a) (hΨ (Φ a)) (hΦ a)
  · refine Quotient.ind fun b ↦ Quotient.sound ?_
    exact hβ _ b (hΨ b)

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F]

namespace WeilRealization

attribute [local instance] GradedObject.koszulSymmetricCategory

/-- **Stacks 0FGH, uniqueness, for realizations.** If the restrictions of two realizations `G`
and `G'` along `X ↦ (X, 1, 0)` are monoidally isomorphic to the same symmetric monoidal functor
`F₀` on correspondences of degree zero, then `G` and `G'` are monoidally isomorphic. -/
theorem rel_of_untwisted (G G' : WeilRealization k F)
    (F₀ : DegreeZero ℚ (CorrespondenceCategory k) ⥤ GradedObject ℤ (ModuleCat.{w} F))
    [@Functor.Braided _ _ _ _ _ _ _ GradedObject.koszulBraidedCategory F₀]
    (φ : TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ G.functor ≅ F₀)
    (φ' : TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ G'.functor ≅ F₀)
    [NatTrans.IsMonoidal φ.hom] [NatTrans.IsMonoidal φ'.hom] :
    (isoSetoid k F).r G G' := by
  let := G.braided
  let := G'.braided
  obtain ⟨θ, ⟨hθ, -⟩, -⟩ := TwistedKaroubi.existsUnique_iso_of_uniqueness
    (ChowMotiveCat.lefschetzKaroubi (ChowMotiveCat.projectiveLineZero k)
      ChowMotiveCat.projectiveLineZero_comp)
    (ChowMotiveCat.lefschetzKaroubiIso (ChowMotiveCat.projectiveLineZero k)
      ChowMotiveCat.projectiveLineZero_comp)
    (InvertingObject.uniqueness _ _ _ _) F₀ G.functor G'.functor φ φ'
  exact ⟨⟨θ, hθ⟩⟩

end WeilRealization

end Stacks.WeilCohomology

end
