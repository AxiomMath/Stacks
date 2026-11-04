module

public import StacksFrontier.CategoryTheory.Triangulated.CoproductComparison

/-!
# Transporting a generating family along an adjunction

The hypothesis of weak Brown representability [Stacks, Tag 0GYG] and of its adjoint form
[Stacks, Tag 0GYH] is a family `E : ι → D` of objects such that

1. every nonzero object of `D` receives a nonzero morphism from some `E i`, and
2. every morphism from some `E i` into a countable direct sum `∐ X` factors as a direct sum of
   morphisms `E (j n) ⟶ X n` preceded by a morphism `E i ⟶ ∐ₙ E (j n)`.

This file moves such a family from one category to another along an adjunction `Λ ⊣ Ψ`: the
family `fun i ↦ Λ.obj (E i)` satisfies the same two conditions in the target, provided `Ψ`
reflects zero objects and transforms countable direct sums into countable direct sums.

Nothing triangulated is used — only zero morphisms and countable coproducts — so the statement is
made for plain categories. The two conditions are written out rather than named, matching the way
[Stacks, Tag 0GYG] and its consumers in this library spell them.

## Main results

* `CategoryTheory.exists_generating_family_of_adjunction`: the transport along an adjunction.
* `CategoryTheory.exists_generating_family_of_equivalence`: the special case of an equivalence,
  where both side conditions on the right adjoint are automatic.

## Implementation notes

Condition (1) transports by the bijection `Adjunction.homEquiv`, which sends `0` to `0` in both
directions, so a nonzero morphism `E i ⟶ Ψ K` becomes a nonzero morphism `Λ (E i) ⟶ K`. Only
`Ψ.PreservesZeroMorphisms` is needed for that: if the transpose of `f` vanishes then
`f = adj.unit ≫ Ψ.map 0 = 0`.

Condition (2) is the computation that makes the file worth having. The factorization produced in
the source category is a factorization through `∐ₙ E (j n)` *there*, and the one wanted is a
factorization through `∐ₙ Λ (E (j n))` *here*; the two coproducts are compared by
`CategoryTheory.Limits.sigmaComparison`, invertible for `Λ` because `Λ` preserves the coproduct
and for `Ψ` by hypothesis. The identity that joins them,
proved by `CategoryTheory.Limits.Sigma.hom_ext`, is

`Sigma.map β' ≫ sigmaComparison Ψ K
  = adj.homEquiv _ _ (inv (sigmaComparison Λ _)) ≫ Ψ.map (Sigma.map β)`

where `β n` is the transpose of `β' n`; on the `n`-th summand both sides are
`β' n ≫ Ψ.map (Sigma.ι K n)`.

## References

* [Stacks Project, Tag 0GYG](https://stacks.math.columbia.edu/tag/0GYG)
* [Stacks Project, Tag 0GYH](https://stacks.math.columbia.edu/tag/0GYH)
-/

@[expose] public section

open CategoryTheory.Limits

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  [HasZeroMorphisms A] [HasZeroMorphisms B]
  [HasColimitsOfShape (Discrete ℕ) A] [HasColimitsOfShape (Discrete ℕ) B]

/-- **A generating family in the sense of [Stacks, Tag 0GYG] transports along an adjunction.**
Let `Λ ⊣ Ψ` be an adjunction between categories with countable direct sums, with `Ψ` preserving
zero morphisms and countable direct sums and reflecting zero objects, and let `Λ` preserve
countable direct sums (which it does, being a left adjoint). If `E : ι → B` detects nonzero
objects of `B` and morphisms out of its members into countable direct sums factor through
countable direct sums of its members, then `fun i ↦ Λ.obj (E i)` does the same in `A`.

These are exactly the two hypotheses carried, in the namespace
`CategoryTheory.Pretriangulated`, by
`exists_iso_preadditiveYoneda_of_generating_of_factorsThroughSigma` ([Stacks, Tag 0GYG]) and by
`exists_isTriangulated_rightAdjoint_of_generating_of_factorsThroughSigma` ([Stacks, Tag 0GYH]),
so this is how a family produced on one triangulated category is moved to another. -/
theorem exists_generating_family_of_adjunction {Λ : B ⥤ A} {Ψ : A ⥤ B} (adj : Λ ⊣ Ψ)
    [Ψ.PreservesZeroMorphisms] [PreservesColimitsOfShape (Discrete ℕ) Ψ]
    [PreservesColimitsOfShape (Discrete ℕ) Λ]
    (hcons : ∀ K : A, IsZero (Ψ.obj K) → IsZero K)
    {ι : Type w} (E : ι → B)
    (hE : ∀ L : B, ¬ IsZero L → ∃ (i : ι) (f : E i ⟶ L), f ≠ 0)
    (hE' : ∀ (L : ℕ → B) (i : ι) (α : E i ⟶ ∐ L),
      ∃ (j : ℕ → ι) (β : ∀ n, E (j n) ⟶ L n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
        α = γ ≫ Limits.Sigma.map β) :
    (∀ K : A, ¬ IsZero K → ∃ (i : ι) (f : Λ.obj (E i) ⟶ K), f ≠ 0) ∧
      ∀ (K : ℕ → A) (i : ι) (α : Λ.obj (E i) ⟶ ∐ K),
        ∃ (j : ℕ → ι) (β : ∀ n, Λ.obj (E (j n)) ⟶ K n)
          (γ : Λ.obj (E i) ⟶ ∐ fun n ↦ Λ.obj (E (j n))),
          α = γ ≫ Limits.Sigma.map β := by
  constructor
  · intro K hK
    obtain ⟨i, f, hf⟩ := hE (Ψ.obj K) fun hz ↦ hK (hcons K hz)
    refine ⟨i, (adj.homEquiv _ _).symm f, fun h0 ↦ hf ?_⟩
    rw [← (adj.homEquiv _ _).apply_symm_apply f, h0, Adjunction.homEquiv_unit, Functor.map_zero,
      Limits.comp_zero]
  · intro K i α
    have hΨ : IsIso (sigmaComparison Ψ K) :=
      isIso_sigmaComparison_of_preservesColimit Ψ K inferInstance
    obtain ⟨j, β', γ', hfac⟩ :=
      hE' (fun n ↦ Ψ.obj (K n)) i (adj.homEquiv _ _ α ≫ inv (sigmaComparison Ψ K))
    have hΛ : IsIso (sigmaComparison Λ fun n ↦ E (j n)) :=
      isIso_sigmaComparison_of_preservesColimit Λ _ inferInstance
    -- The transposes of the morphisms the source category supplies.
    have hι : ∀ n, Λ.map (Limits.Sigma.ι (fun m ↦ E (j m)) n) ≫
        inv (sigmaComparison Λ fun m ↦ E (j m)) =
          Limits.Sigma.ι (fun m ↦ Λ.obj (E (j m))) n := fun n ↦ by
      rw [← ι_comp_sigmaComparison Λ (fun m ↦ E (j m)) n, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    have e1 : ∀ n, Limits.Sigma.ι (fun m ↦ E (j m)) n ≫
          adj.homEquiv _ _ (inv (sigmaComparison Λ fun m ↦ E (j m))) =
        adj.homEquiv _ _ (Limits.Sigma.ι (fun m ↦ Λ.obj (E (j m))) n) := fun n ↦ by
      rw [← Adjunction.homEquiv_naturality_left adj (Limits.Sigma.ι (fun m ↦ E (j m)) n)
        (inv (sigmaComparison Λ fun m ↦ E (j m))), hι n]
    -- The identity that joins the two coproducts, checked on each summand.
    have key : (Limits.Sigma.map β' ≫ sigmaComparison Ψ K :
          (∐ fun n ↦ E (j n)) ⟶ Ψ.obj (∐ K)) =
        adj.homEquiv _ _ (inv (sigmaComparison Λ fun n ↦ E (j n))) ≫
          Ψ.map (Limits.Sigma.map fun n ↦ (adj.homEquiv (E (j n)) (K n)).symm (β' n)) := by
      refine Limits.Sigma.hom_ext _ _ fun n ↦ ?_
      rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, ι_comp_sigmaComparison,
        ← Category.assoc, e1 n, ← Adjunction.homEquiv_naturality_right adj
          (Limits.Sigma.ι (fun m ↦ Λ.obj (E (j m))) n)
          (Limits.Sigma.map fun m ↦ (adj.homEquiv (E (j m)) (K m)).symm (β' m)),
        Limits.Sigma.ι_map, Adjunction.homEquiv_naturality_right,
        (adj.homEquiv _ _).apply_symm_apply]
    refine ⟨j, fun n ↦ (adj.homEquiv _ _).symm (β' n),
      Λ.map γ' ≫ inv (sigmaComparison Λ fun n ↦ E (j n)), (adj.homEquiv _ _).injective ?_⟩
    calc adj.homEquiv _ _ α
        = (γ' ≫ Limits.Sigma.map β') ≫ sigmaComparison Ψ K := by
          rw [← hfac, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      _ = γ' ≫ adj.homEquiv _ _ (inv (sigmaComparison Λ fun n ↦ E (j n))) ≫
            Ψ.map (Limits.Sigma.map fun n ↦ (adj.homEquiv (E (j n)) (K n)).symm (β' n)) := by
          rw [Category.assoc, key]
      _ = adj.homEquiv _ _ ((Λ.map γ' ≫ inv (sigmaComparison Λ fun n ↦ E (j n))) ≫
            Limits.Sigma.map fun n ↦ (adj.homEquiv (E (j n)) (K n)).symm (β' n)) := by
          rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
            Category.assoc]

/-- **A generating family in the sense of [Stacks, Tag 0GYG] transports along an equivalence.**
If `e : B ≌ A` is an equivalence of categories with countable direct sums and preserving zero
morphisms, a family satisfying the two conditions of [Stacks, Tag 0GYG] in `B` is carried by
`e.functor` to one in `A`. The two side conditions on the right adjoint in
`CategoryTheory.exists_generating_family_of_adjunction` are automatic here: an equivalence
preserves direct sums and reflects zero objects. -/
theorem exists_generating_family_of_equivalence (e : B ≌ A)
    [e.functor.PreservesZeroMorphisms] [e.inverse.PreservesZeroMorphisms]
    {ι : Type w} (E : ι → B)
    (hE : ∀ L : B, ¬ IsZero L → ∃ (i : ι) (f : E i ⟶ L), f ≠ 0)
    (hE' : ∀ (L : ℕ → B) (i : ι) (α : E i ⟶ ∐ L),
      ∃ (j : ℕ → ι) (β : ∀ n, E (j n) ⟶ L n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
        α = γ ≫ Limits.Sigma.map β) :
    (∀ K : A, ¬ IsZero K → ∃ (i : ι) (f : e.functor.obj (E i) ⟶ K), f ≠ 0) ∧
      ∀ (K : ℕ → A) (i : ι) (α : e.functor.obj (E i) ⟶ ∐ K),
        ∃ (j : ℕ → ι) (β : ∀ n, e.functor.obj (E (j n)) ⟶ K n)
          (γ : e.functor.obj (E i) ⟶ ∐ fun n ↦ e.functor.obj (E (j n))),
          α = γ ≫ Limits.Sigma.map β :=
  exists_generating_family_of_adjunction e.toAdjunction
    (fun K hz ↦ by
      rw [IsZero.iff_id_eq_zero] at hz ⊢
      refine e.inverse.map_injective ?_
      rw [e.inverse.map_id, hz, Functor.map_zero])
    E hE hE'

end CategoryTheory

end
