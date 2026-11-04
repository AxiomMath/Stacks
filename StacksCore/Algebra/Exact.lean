module

public import StacksCore.Algebra.Homology.ShortComplex.ModuleCat

/-! ## Exactness and `Hom`

Stacks tag 0582: for `R`-modules `M₁`, `M₂`, `M₃` and maps `f : M₁ →ₗ[R] M₂`,
`g : M₂ →ₗ[R] M₃`,

* `M₁ → M₂ → M₃ → 0` is exact if and only if `0 → Hom(M₃, N) → Hom(M₂, N) → Hom(M₁, N)` is
  exact for every `N` (`LinearMap.exact_iff_homRight`), and
* `0 → M₁ → M₂ → M₃` is exact if and only if `0 → Hom(N, M₁) → Hom(N, M₂) → Hom(N, M₃)` is
  exact for every `N` (`LinearMap.exact_iff_homLeft`).

The Stacks project proves this for modules and then deduces the abelian category version,
tag 05AA, from it. Here the dependency runs the other way: 05AA is proved directly in
`StacksCore.Algebra.Homology.ShortComplex.ExactFunctor`, and the statements below are obtained
by instantiating it at `ModuleCat R`, which is abelian. The translation between hom-groups
of `ModuleCat R` and spaces of linear maps is carried out once and for all in
`StacksCore.Algebra.Homology.ShortComplex.ModuleCat`.

Pre- and post-composition are written with `LinearMap.lcomp` and `LinearMap.compRight`.
Since `R` is not assumed commutative these are only `ℕ`-linear; over a commutative ring one
could equally use `LinearMap.lcomp R` and `LinearMap.llcomp R`.

Note that `N` ranges over modules in the same universe as `M₁`, `M₂`, `M₃`. This loses
nothing: the substantive direction of 05AA only ever tests against `S.cycles`, which lives
in that universe.
-/

@[expose] public section

universe u v

open CategoryTheory Limits ShortComplex Opposite

namespace LinearMap

variable {R : Type u} [Ring R] {M₁ M₂ M₃ : Type v}
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)

/-- **Stacks 0582 (2)**, for a complex: `0 → M₁ → M₂ → M₃` is exact if and only if
`0 → Hom(N, M₁) → Hom(N, M₂) → Hom(N, M₃)` is exact for every `N`. -/
theorem exact_iff_homLeft_of_comp_eq_zero (w : g.comp f = 0) :
    (Function.Injective f ∧ Function.Exact f g) ↔
      ∀ (N : Type v) [AddCommGroup N] [Module R N],
        Function.Injective (compRight (M := N) ℕ f) ∧
        Function.Exact (compRight (M := N) ℕ f) (compRight (M := N) ℕ g) := by
  have key := exact_iff_homLeft (.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (ModuleCat.hom_ext w))
  simp only [ShortComplex.moduleCat_exact_map_preadditiveCoyoneda_iff,
    ShortComplex.moduleCat_mono_map_preadditiveCoyoneda_iff,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
    ModuleCat.mono_iff_injective] at key
  exact ⟨fun h N _ _ => (key.1 h.symm (ModuleCat.of R N)).symm,
    fun h => (key.2 fun N => (h N).symm).symm⟩

@[stacks 0582 "part 2"]
theorem exact_iff_homLeft : (Function.Injective f ∧ Function.Exact f g) ↔
    ∀ (N : Type v) [AddCommGroup N] [Module R N],
      Function.Injective (compRight (M := N) ℕ f) ∧
      Function.Exact (compRight (M := N) ℕ f) (compRight (M := N) ℕ g) :=
  ⟨fun h => (exact_iff_homLeft_of_comp_eq_zero f g h.2.linearMap_comp_eq_zero).1 h,
  fun h => (exact_iff_homLeft_of_comp_eq_zero f g <| ((h M₁).2 f).2 ⟨LinearMap.id, by simp⟩).2 h⟩

/-- **Stacks 0582 (1)**, for a complex: `M₁ → M₂ → M₃ → 0` is exact if and only if
`0 → Hom(M₃, N) → Hom(M₂, N) → Hom(M₁, N)` is exact for every `N`. -/
theorem exact_iff_homRight_of_comp_eq_zero (w : g.comp f = 0) :
    (Function.Exact f g ∧ Function.Surjective g) ↔
      ∀ (N : Type v) [AddCommGroup N] [Module R N],
        Function.Injective (lcomp ℕ N g) ∧ Function.Exact (lcomp ℕ N g) (lcomp ℕ N f) := by
  have key := exact_iff_homRight (.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (ModuleCat.hom_ext w))
  simp only [ShortComplex.moduleCat_exact_op_map_preadditiveYoneda_iff,
    ShortComplex.moduleCat_mono_op_map_preadditiveYoneda_iff,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
    ModuleCat.epi_iff_surjective] at key
  exact ⟨fun h N _ _ => (key.1 h (ModuleCat.of R N)).symm,
    fun h => key.2 fun N => (h N).symm⟩

@[stacks 0582 "part 1"]
theorem exact_iff_homRight : (Function.Exact f g ∧ Function.Surjective g) ↔ ∀ (N : Type v)
    [AddCommGroup N] [Module R N], Function.Injective (lcomp ℕ N g) ∧
    Function.Exact (lcomp ℕ N g) (lcomp ℕ N f) := ⟨fun h ↦ (exact_iff_homRight_of_comp_eq_zero f g
  h.1.linearMap_comp_eq_zero).1 h, fun h ↦ (exact_iff_homRight_of_comp_eq_zero f g <|
  ((h M₃).2 g).2 ⟨LinearMap.id, by rw [lcomp_apply', id_comp]⟩).2 h⟩

end LinearMap
