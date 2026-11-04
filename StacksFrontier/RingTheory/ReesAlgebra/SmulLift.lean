module

public import StacksFrontier.RingTheory.ReesAlgebra.ExtendRelations

/-!
# Lifting a linear functional on an ideal to the ideal multiple of a module

Let `A` be a commutative ring, `K ⊆ A` an ideal, `f : A →+* R` a ring map and `M` an
`R`-module. A linear functional `λ : K →ₗ[A] A` prescribes a value `λ(g) · x` for each
product `g · x` with `g ∈ K` and `x ∈ M`. Those products span `K R · M`, so the prescription
determines at most one `R`-linear map on it, and it determines one exactly when it respects
every relation among the products:

> whenever `∑ₖ gₖ · xₖ = 0` with `gₖ ∈ K`, also `∑ₖ λ(gₖ) · xₖ = 0`.

That is the relation-killing hypothesis of `Stacks.ReesAlgebra.KillsRelations`. This file turns
it into the map itself. The map is what a sheaf-level construction consumes one open at a time:
on an open `W` the subsheaf `I ^ k F` has `I(W) ^ k · Γ(F, W)` as its span of products, and the
component of the graded map of [Stacks, Tag 0EH6] over `W` must send `g · s` to `Φ(g)_σ · s`.

## Main results

* `Stacks.ReesAlgebra.linearMap_ext_of_smul` — two `R`-linear maps on `K R · M` agreeing on the
  products `g · x` are equal.
* `Stacks.ReesAlgebra.exists_linearMap_of_kills_relations` — relation-killing produces the map.
* `Stacks.ReesAlgebra.KillsRelations.exists_linearMap` — the same for the coefficient
  `Stacks.ReesAlgebra.extendCoeff` of the extension of a splitting, which is the case needed by
  [Stacks, Tag 0EH6].
* `Stacks.ReesAlgebra.KillsRelations.of_jointlyInjective` — relation-killing passes from a
  family of modules to one that injects into their product. For the sheaf `F = lim F_n` of
  [Stacks, Tag 0EH6] this is what replaces the sections of the limit, a module over a
  completion, by the sections of the terms, which are finite modules over the Noetherian ring
  of sections.

## Implementation notes

The map is built from the free `R`-module on the pairs `(g, x)` with `g ∈ K`: the two
prescriptions `(g, x) ↦ g · x` and `(g, x) ↦ λ(g) · x` are linear combinations on it, the first
is surjective onto `K R · M`, and relation-killing is exactly the inclusion of kernels that lets
the second factor through the first.

`Stacks.ReesAlgebra.KillsRelations` quantifies over families indexed by `Fin m`, which is the
shape [Stacks, Tag 0EIC] delivers; a linear combination is indexed by the support of a
finitely supported function. `kills_relations_finset` is the one reindexing between the two.

## References

* [Stacks Project, Tag 0EIC](https://stacks.math.columbia.edu/tag/0EIC)
* [Stacks Project, Tag 0EH6](https://stacks.math.columbia.edu/tag/0EH6)
-/

@[expose] public noncomputable section

namespace Stacks.ReesAlgebra

universe u v w

section Lift

variable {A : Type u} [CommRing A] {R : Type v} [CommRing R]
  {M : Type w} [AddCommGroup M] [Module R M]

/-- The products `g · x` with `g ∈ K` span the submodule `K R · M` of `M`. -/
public lemma span_smul_pairs (f : A →+* R) (K : Ideal A) :
    Submodule.span R (Set.range fun p : ↥K × M => f (p.1 : A) • p.2) =
      Ideal.map f K • (⊤ : Submodule R M) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.smul_le.2 fun r hr m _ => ?_)
  · rintro _ ⟨p, rfl⟩
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ p.1.2) Submodule.mem_top
  · refine Submodule.span_induction ?_ ?_ ?_ ?_
      (show r ∈ Ideal.span (f '' (K : Set A)) from hr)
    · rintro x ⟨g, hg, rfl⟩
      exact Submodule.subset_span ⟨(⟨g, hg⟩, m), rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [add_smul]
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ a hx

/-- Two `R`-linear maps on `K R · M` which agree on the products `g · x` with `g ∈ K` are
equal. -/
public lemma linearMap_ext_of_smul (f : A →+* R) (K : Ideal A)
    (μ μ' : ↥(Ideal.map f K • (⊤ : Submodule R M)) →ₗ[R] M)
    (h : ∀ (g : A), g ∈ K → ∀ (x : M)
      (hmem : f g • x ∈
        Ideal.map f K • (⊤ : Submodule R M)),
      μ ⟨f g • x, hmem⟩ = μ' ⟨f g • x, hmem⟩) :
    μ = μ' := by
  have hsub : ∀ {z : M}, z ∈ Submodule.span R
      (Set.range fun p : ↥K × M => f (p.1 : A) • p.2) →
      z ∈ Ideal.map f K • (⊤ : Submodule R M) :=
    fun hz => (span_smul_pairs (M := M) f K).le hz
  have key : ∀ z ∈ Submodule.span R
      (Set.range fun p : ↥K × M => f (p.1 : A) • p.2),
      ∀ hz : z ∈ Ideal.map f K • (⊤ : Submodule R M),
        μ ⟨z, hz⟩ = μ' ⟨z, hz⟩ := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
        intro hw'
        obtain ⟨p, rfl⟩ := hw
        exact h (p.1 : A) p.1.2 p.2 hw'
    | zero =>
        intro h0
        rw [show (⟨(0 : M), h0⟩ :
          ↥(Ideal.map f K • (⊤ : Submodule R M))) = 0 from rfl,
          map_zero, map_zero]
    | add a b ha hb iha ihb =>
        intro hab
        rw [show (⟨a + b, hab⟩ :
            ↥(Ideal.map f K • (⊤ : Submodule R M))) =
            ⟨a, hsub ha⟩ + ⟨b, hsub hb⟩ from rfl, map_add, map_add, iha, ihb]
    | smul c a ha iha =>
        intro hca
        rw [show (⟨c • a, hca⟩ :
            ↥(Ideal.map f K • (⊤ : Submodule R M))) =
            c • ⟨a, hsub ha⟩ from rfl, map_smul, map_smul, iha]
  ext y
  obtain ⟨y, hy⟩ := y
  exact key y ((span_smul_pairs (M := M) f K).ge hy) hy

/-- A relation-killing hypothesis stated for families indexed by `Fin m`, reindexed to families
indexed by a finite subset of an arbitrary type. -/
private lemma kills_relations_finset {ι : Type*} (f : A →+* R) (K : Ideal A) (lam : ↥K →ₗ[A] A)
    (hk : ∀ (m : ℕ) (g : Fin m → A) (hg : ∀ k, g k ∈ K) (x : Fin m → M),
      (∑ k, f (g k) • x k) = 0 →
      (∑ k, f (lam ⟨g k, hg k⟩) • x k) = 0)
    (s : Finset ι) (g : ι → A) (hg : ∀ i, g i ∈ K) (x : ι → M)
    (hsum : (∑ i ∈ s, f (g i) • x i) = 0) :
    (∑ i ∈ s, f (lam ⟨g i, hg i⟩) • x i) = 0 := by
  classical
  have key : ∀ F : ι → M, (∑ i ∈ s, F i) = ∑ k : Fin s.card, F (s.equivFin.symm k) := by
    intro F
    rw [← Finset.sum_attach s F, ← Finset.univ_eq_attach,
      ← Equiv.sum_comp s.equivFin.symm (fun i : {y // y ∈ s} => F i)]
  rw [key] at hsum ⊢
  exact hk s.card (fun k => g (s.equivFin.symm k)) (fun k => hg _)
    (fun k => x (s.equivFin.symm k)) hsum

/-- **A linear functional on an ideal which kills every relation lifts to the ideal multiple.**

Given `λ : K →ₗ[A] A` such that every vanishing combination `∑ₖ gₖ · xₖ = 0` in `M` with
`gₖ ∈ K` has `∑ₖ λ(gₖ) · xₖ = 0`, there is an `R`-linear map on `K R · M` sending `g · x` to
`λ(g) · x`. It is unique by `Stacks.ReesAlgebra.linearMap_ext_of_smul`. -/
public theorem exists_linearMap_of_kills_relations (f : A →+* R) (K : Ideal A) (lam : ↥K →ₗ[A] A)
    (hk : ∀ (m : ℕ) (g : Fin m → A) (hg : ∀ k, g k ∈ K) (x : Fin m → M),
      (∑ k, f (g k) • x k) = 0 →
      (∑ k, f (lam ⟨g k, hg k⟩) • x k) = 0) :
    ∃ μ : ↥(Ideal.map f K • (⊤ : Submodule R M)) →ₗ[R] M,
      ∀ (g : A) (hg : g ∈ K) (x : M)
        (hmem : f g • x ∈
          Ideal.map f K • (⊤ : Submodule R M)),
        μ ⟨f g • x, hmem⟩ = f (lam ⟨g, hg⟩) • x := by
  classical
  set S : Submodule R M := Ideal.map f K • (⊤ : Submodule R M) with hS
  set gen : ↥K × M → M := fun p => f (p.1 : A) • p.2 with hgen
  set gen' : ↥K × M → M := fun p => f (lam p.1) • p.2 with hgen'
  set α : (↥K × M →₀ R) →ₗ[R] M := Finsupp.linearCombination R gen with hα
  set β : (↥K × M →₀ R) →ₗ[R] M := Finsupp.linearCombination R gen' with hβ
  have hrange : LinearMap.range α = S := by
    rw [hα, Finsupp.range_linearCombination, hgen, hS]
    exact span_smul_pairs (M := M) f K
  have hker : LinearMap.ker α ≤ LinearMap.ker β := by
    intro c hc
    have hcomb : ∀ F : ↥K × M → A, Finsupp.linearCombination R (fun p => f (F p) • p.2) c =
        ∑ p ∈ c.support, f (F p) • (c p • p.2) := fun F => by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      exact Finset.sum_congr rfl fun p _ => smul_comm _ _ _
    exact (hcomb fun p => lam p.1).trans (kills_relations_finset (M := M) f K lam hk c.support
      (fun p => (p.1 : A)) (fun p => p.1.2) (fun p => c p • p.2)
      ((hcomb fun p => (p.1 : A)).symm.trans hc))
  let α' : (↥K × M →₀ R) →ₗ[R] ↥S :=
    α.codRestrict S fun c => hrange.le (LinearMap.mem_range_self α c)
  have hsurj : Function.Surjective α' := by
    intro y
    obtain ⟨c, hc⟩ := hrange.ge y.2
    exact ⟨c, Subtype.ext hc⟩
  have hker' : LinearMap.ker α' ≤ LinearMap.ker β := by
    rw [show LinearMap.ker α' = LinearMap.ker α from LinearMap.ker_codRestrict S α _]
    exact hker
  let e := LinearMap.quotKerEquivOfSurjective α' hsurj
  refine ⟨(Submodule.liftQ (LinearMap.ker α') β hker').comp e.symm.toLinearMap, ?_⟩
  intro g hg x hmem
  have hc : α' (Finsupp.single (⟨⟨g, hg⟩, x⟩ : ↥K × M) 1) =
      (⟨f g • x, hmem⟩ : ↥S) := by
    refine Subtype.ext ?_
    show α (Finsupp.single (⟨⟨g, hg⟩, x⟩ : ↥K × M) 1) = f g • x
    rw [hα, Finsupp.linearCombination_single, one_smul]
  have hmk : e (Submodule.Quotient.mk (Finsupp.single (⟨⟨g, hg⟩, x⟩ : ↥K × M) 1)) =
      α' (Finsupp.single (⟨⟨g, hg⟩, x⟩ : ↥K × M) 1) := rfl
  have he : e.symm (⟨f g • x, hmem⟩ : ↥S) =
      Submodule.Quotient.mk (Finsupp.single (⟨⟨g, hg⟩, x⟩ : ↥K × M) 1) := by
    rw [← hc, ← hmk, e.symm_apply_apply]
  show Submodule.liftQ (LinearMap.ker α') β hker'
    (e.symm (⟨f g • x, hmem⟩ : ↥S)) = _
  rw [he, Submodule.liftQ_apply, hβ, Finsupp.linearCombination_single, one_smul]

end Lift

/-- **The coefficient map of the extension of a splitting, on the ideal multiple of a module.**

If the splitting `ψ` on `I ^ d` kills the relations of the `B`-module `N`, then for every degree
`n` and every monomial `σ` there is a `B`-linear map on `(I ^ d) ^ n B · N` sending a product
`g · x` with `g ∈ (I ^ d) ^ n` to `Φ(g)_σ · x`. It is unique by
`Stacks.ReesAlgebra.linearMap_ext_of_smul`.

This is the value of the component at `σ` of the graded map of [Stacks, Tag 0EH6] on the
sections over one open, the module `N` being the sections of the sheaf there. -/
public theorem KillsRelations.exists_linearMap {A : Type u} {B : Type v} {N : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup N] [Module B N]
    {I : Ideal A} {r d : ℕ} {ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A}
    (h : KillsRelations A B N I d ψ) (n : ℕ) (σ : Fin r →₀ ℕ) :
    ∃ μ : ↥(Ideal.map (algebraMap A B) ((I ^ d : Ideal A) ^ n) •
      (⊤ : Submodule B N)) →ₗ[B] N,
      ∀ (g : A) (hg : g ∈ ((I ^ d : Ideal A) ^ n)) (x : N)
        (hmem : algebraMap A B g • x ∈
          Ideal.map (algebraMap A B) ((I ^ d : Ideal A) ^ n) • (⊤ : Submodule B N)),
        μ ⟨algebraMap A B g • x, hmem⟩ =
          algebraMap A B (extendCoeff I d n ψ σ ⟨g, hg⟩) • x :=
  exists_linearMap_of_kills_relations (algebraMap A B) _ (extendCoeff I d n ψ σ)
    fun m g hg x => h n σ m g hg x

/-- **Relation-killing passes to a module which injects into a product of modules that have
it.**

A relation in the small module is a relation in each of the large ones, and the combination
the splitting's coefficients produce is carried to the corresponding combination there, so it
is killed by every map of the family and hence zero.

For [Stacks, Tag 0EH6] the family is the projections of `Γ(lim F_n, W)` to the
`Γ(F_m, W)`: the sections of the limit form a module over a completion, while those of the
terms are finite modules over the Noetherian ring `Γ(X, W)`, which is what
`Stacks.ReesAlgebra.exists_extendLinearMaps_kills_relations` can be applied to. -/
public lemma KillsRelations.of_jointlyInjective {A : Type u} {B : Type v} {N : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup N] [Module B N]
    {I : Ideal A} {r d : ℕ} {ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A}
    {ι : Type*} {N' : ι → Type w} [∀ i, AddCommGroup (N' i)] [∀ i, Module B (N' i)]
    (π : ∀ i, N →ₗ[B] N' i) (hinj : ∀ x : N, (∀ i, π i x = 0) → x = 0)
    (h : ∀ i, KillsRelations A B (N' i) I d ψ) :
    KillsRelations A B N I d ψ := by
  intro n σ m g hg x hsum
  refine hinj _ fun i => ?_
  have hπ : ∀ (c : Fin m → B) (y : Fin m → N),
      π i (∑ k, c k • y k) = ∑ k, c k • π i (y k) := by
    intro c y
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
  have h1 : (∑ k, algebraMap A B (g k) • π i (x k)) = 0 := by
    rw [← hπ, hsum, map_zero]
  exact (hπ (fun k => algebraMap A B (extendCoeff I d n ψ σ ⟨g k, hg k⟩)) x).trans
    (h i n σ m g hg (fun k => π i (x k)) h1)

end Stacks.ReesAlgebra

end
