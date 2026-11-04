module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Cyclic subquotients and filtrations of spans

This file collects two span-level ingredients used to build filtrations of finite modules by
cyclic quotients (see `Module.Finite.exists_relSeries_isQuotientEquivQuotientCyclic`, Stacks 00KZ):

* `Submodule.exists_quotient_sup_span_singleton_equiv`: the subquotient `(N' ⊔ R ∙ a) ⧸ N'` is
  cyclic, i.e. isomorphic to `R ⧸ I` for some ideal `I`.
* `Submodule.filtrationOfFinGeneratingFamily`: the closed-form filtration of `span R (Set.range g)`
  attached to a finite family `g : Fin n → M`, whose `i`-th term is spanned by the first `i`
  generators, together with lemmas computing its endpoints, its successive terms, and their finite
  generation.
-/

@[expose] public section

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The subquotient `(N' ⊔ R ∙ a) ⧸ N'` is cyclic: it is isomorphic to `R ⧸ I` for the ideal `I`
annihilating the image of `a`. -/
theorem exists_quotient_sup_span_singleton_equiv (N' : Submodule R M) (a : M) :
    ∃ I : Ideal R, Nonempty (
      (↥(N' ⊔ Submodule.span R {a}) ⧸
        (N'.submoduleOf (N' ⊔ Submodule.span R {a}))) ≃ₗ[R] R ⧸ I) := by
  set N : Submodule R M := N' ⊔ Submodule.span R {a} with hN
  have haN : a ∈ N := mem_sup_right (mem_span_singleton_self a)
  set a' : N := ⟨a, haN⟩ with ha'
  -- `f r = [r • a]` in the subquotient; it is surjective since `N = N' + R ∙ a`.
  set f : R →ₗ[R] (N ⧸ N'.submoduleOf N) :=
    (N'.submoduleOf N).mkQ.comp (LinearMap.toSpanSingleton R N a') with hf
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨⟨v, hv⟩, rfl⟩ := (N'.submoduleOf N).mkQ_surjective y
    rw [hN] at hv
    obtain ⟨n', hn', w, hw, rfl⟩ := mem_sup.1 hv
    obtain ⟨r, rfl⟩ := mem_span_singleton.1 hw
    refine ⟨r, ?_⟩
    simp only [hf, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    rw [Submodule.submoduleOf, Submodule.mem_comap]
    simp only [Submodule.coe_subtype, AddSubgroupClass.coe_sub, SetLike.val_smul, ha']
    change r • a - (n' + r • a) ∈ N'
    rw [add_comm, ← sub_sub, sub_self, zero_sub]
    exact N'.neg_mem hn'
  exact ⟨LinearMap.ker f, ⟨(LinearMap.quotKerEquivOfSurjective f hsurj).symm⟩⟩

variable (R)

/-- The closed-form filtration of `span R (Set.range g)` attached to a finite family
`g : Fin n → M`: the `i`-th term `filtrationOfFinGeneratingFamily R g i` is the submodule spanned by
the generators `g j` with `j < i`.

Its endpoints are `⊥` (`filtrationOfFinGeneratingFamily_zero`) and `span R (Set.range g)`
(`filtrationOfFinGeneratingFamily_last`), and consecutive terms differ by a single generator
(`filtrationOfFinGeneratingFamily_succ`). -/
def filtrationOfFinGeneratingFamily {n : ℕ} (g : Fin n → M) (i : Fin (n + 1)) : Submodule R M :=
  Submodule.span R {x | ∃ j : Fin n, (j : ℕ) < (i : ℕ) ∧ g j = x}

/-- The bottom term of `filtrationOfFinGeneratingFamily` involves no generators, hence is `⊥`. -/
@[simp] theorem filtrationOfFinGeneratingFamily_zero {n : ℕ} (g : Fin n → M) :
    filtrationOfFinGeneratingFamily R g 0 = ⊥ := by
  rw [filtrationOfFinGeneratingFamily, ← Submodule.span_empty]
  congr 1
  ext x
  simp

/-- The top term of `filtrationOfFinGeneratingFamily` involves all generators, hence is
`span R (Set.range g)`. -/
@[simp] theorem filtrationOfFinGeneratingFamily_last {n : ℕ} (g : Fin n → M) :
    filtrationOfFinGeneratingFamily R g (Fin.last n) = Submodule.span R (Set.range g) := by
  rw [filtrationOfFinGeneratingFamily]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_range, Fin.val_last]
  exact ⟨fun ⟨j, _, h⟩ => ⟨j, h⟩, fun ⟨j, h⟩ => ⟨j, j.isLt, h⟩⟩

/-- Consecutive terms of `filtrationOfFinGeneratingFamily` differ by adjoining one generator:
the `i.succ`-th term is the `i.castSucc`-th term together with `R ∙ g i`. -/
theorem filtrationOfFinGeneratingFamily_succ {n : ℕ} (g : Fin n → M) (i : Fin n) :
    filtrationOfFinGeneratingFamily R g i.succ =
      filtrationOfFinGeneratingFamily R g i.castSucc ⊔ Submodule.span R {g i} := by
  rw [filtrationOfFinGeneratingFamily, filtrationOfFinGeneratingFamily, ← Submodule.span_union]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, Fin.val_succ,
    Fin.val_castSucc]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · exact Or.inl ⟨j, h, rfl⟩
    · exact Or.inr (congrArg g (Fin.ext h))
  · rintro (⟨j, hj, rfl⟩ | rfl)
    · exact ⟨j, by omega, rfl⟩
    · exact ⟨i, by omega, rfl⟩

/-- Every term of `filtrationOfFinGeneratingFamily` is spanned by a finite subfamily, hence is
finitely generated. -/
theorem filtrationOfFinGeneratingFamily_finite {n : ℕ} (g : Fin n → M) (i : Fin (n + 1)) :
    Module.Finite R (filtrationOfFinGeneratingFamily R g i) := by
  rw [filtrationOfFinGeneratingFamily, Module.Finite.iff_fg]
  exact fg_span ((Set.finite_range g).subset (by rintro x ⟨j, _, rfl⟩; exact ⟨j, rfl⟩))

end Submodule
