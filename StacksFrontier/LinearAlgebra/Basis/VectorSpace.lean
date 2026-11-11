module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
import StacksCore.Tactic.StacksAttribute

/-! # Exact sequences of vector spaces split

Stacks tag 09FP: every exact sequence of modules over a field splits.
`Function.Exact.exists_split_of_field` splits an exact sequence `M → N → P` at `N`, and
`Function.Exact.split_of_field` is the short exact case.

Stacks 09FP is still registered in `StacksCore/Algebra/Module/Projective.lean` on
`Module.projective_lifting_property`, which says nothing about fields or split exact sequences;
that registration should be removed when these statements are promoted.
-/

@[expose] public section

section Field

variable {k M N P : Type*} [Field k] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module k M] [Module k N] [Module k P] {f : M →ₗ[k] N} {g : N →ₗ[k] P}

/-- Every exact sequence of modules over a field splits: an exact sequence `M → N → P` of
`k`-modules splits at `N`, i.e. there are `l : N → M` and `s : P → N` with `f ∘ l ∘ f = f`,
`g ∘ s ∘ g = g` and `f ∘ l + s ∘ g = id`. Applied at every term, this splits an exact
sequence of any length; for short exact sequences see `Function.Exact.split_of_field`. -/
@[stacks 09FP "Splitting of an exact sequence `M → N → P` at its middle term; the short exact
case is `Function.Exact.split_of_field`."]
theorem Function.Exact.exists_split_of_field (h : Function.Exact f g) :
    ∃ (l : N →ₗ[k] M) (s : P →ₗ[k] N),
      f ∘ₗ l ∘ₗ f = f ∧ g ∘ₗ s ∘ₗ g = g ∧ f ∘ₗ l + s ∘ₗ g = LinearMap.id := by
  obtain ⟨w, hw⟩ := (LinearMap.range g).subtype.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  obtain ⟨t, ht⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  set s : P →ₗ[k] N := t ∘ₗ w
  have hsg : g ∘ₗ s ∘ₗ g = g := by
    ext n
    have h1 := congr($ht (w (g n)))
    have h2 := congr($hw (g.rangeRestrict n))
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
    simp only [s, LinearMap.comp_apply]
    calc g (t (w (g n))) = (g.rangeRestrict (t (w (g n))) : P) := rfl
      _ = (w (g n) : P) := by rw [h1]
      _ = g n := congr_arg Subtype.val h2
  have hp : ∀ n, n - s (g n) ∈ LinearMap.range f := fun n ↦ by
    rw [h.linearMap_ker_eq.symm, LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact (congr($hsg n)).symm
  obtain ⟨u, hu⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  set p : N →ₗ[k] LinearMap.range f :=
    LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ g) fun n ↦ hp n
  have hfu : ∀ n, f (u (p n)) = n - s (g n) := fun n ↦ by
    have := congr_arg Subtype.val congr($hu (p n))
    simpa [p] using this
  refine ⟨u ∘ₗ p, s, ?_, hsg, ?_⟩
  · ext m
    simp only [LinearMap.comp_apply, hfu, h.apply_apply_eq_zero, map_zero, sub_zero]
  · ext n
    simp [hfu]

/-- Every short exact sequence `0 → M → N → P → 0` of modules over a field splits: `f` has
a retraction, `g` has a section, and `N ≅ M × P` compatibly with `f` and `g`. -/
@[stacks 09FP "Short exact case; the case of an arbitrary exact sequence is
`Function.Exact.exists_split_of_field`."]
theorem Function.Exact.split_of_field (h : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    (∃ l : N →ₗ[k] M, l ∘ₗ f = LinearMap.id) ∧ (∃ s : P →ₗ[k] N, g ∘ₗ s = LinearMap.id) ∧
      ∃ e : N ≃ₗ[k] M × P, f = e.symm ∘ₗ LinearMap.inl k M P ∧ g = LinearMap.snd k M P ∘ₗ e := by
  have hs : ∃ s : P →ₗ[k] N, g ∘ₗ s = LinearMap.id :=
    g.exists_rightInverse_of_surjective (LinearMap.range_eq_top_of_surjective g hg)
  have tfae := h.split_tfae hf hg
  exact ⟨(tfae.out 1 2).mp hs, hs, (tfae.out 1 3).mp hs⟩

end Field
