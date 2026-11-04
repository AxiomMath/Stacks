module

public import StacksFrontier.RingTheory.ReesAlgebra.ExtendEnlarge
public import StacksFrontier.RingTheory.ReesAlgebra.ExtendToModule

/-!
# The relation-killing form of the extension to a finite module

Let `I = (f_1, …, f_r)` be an ideal of a commutative ring `A`, let `φ_j : I ^ c ⟶ A` split the
inclusion of `I ^ c` into `A` against the generators, let `B` be a Noetherian `A`-algebra and `N`
a finite `B`-module. [Stacks, Tag 0EIC] — here
`Stacks.ReesAlgebra.exists_unique_extendLinearMaps_module` — enlarges `c` to a `d` and adjusts the
`φ_j` to a family `ψ_j` on `I ^ d`, and produces a graded `B`-module map on `⨁ₙ I^(nd) N`.

This file records the consequence of that map which a construction *on a scheme* needs. A graded
`𝒪_X`-module map out of the subsheaf `I ^ (nd) F` cannot be written down on sections, because a
section of that subsheaf is only locally a sum of products `g · m`. What one can do is write down
the map on a presentation of the subsheaf by generators of `I ^ (nd)` and check that it kills the
relations; the statement that it does is exactly:

> whenever `∑ₖ gₖ · xₖ = 0` in `N` with `gₖ ∈ (I ^ d) ^ n`, also `∑ₖ Φ(gₖ)_σ · xₖ = 0`,

for every monomial `σ`, where `Φ(g)_σ` is `Stacks.ReesAlgebra.extendCoeff`. That is what is
proved here, by applying the degree-`n` component of the graded map of [Stacks, Tag 0EIC] to the
vanishing sum and reading off its coefficient at `σ`.

## Main results

* `Stacks.ReesAlgebra.exists_extendLinearMaps_kills_relations` — the enlarged exponent, the
  adjusted splitting, and the relation-killing property.

## Implementation notes

The scalar formula of [Stacks, Tag 0EIC] is stated for an element `p` of `reesAlgebra (I ^ d)`
supported in a single degree; the element used here is `Polynomial.monomial n (g k)`, whose
`n`-th coefficient is `g k`. Rewriting that coefficient is the only friction in the derivation:
the membership proof carried by the argument of the graded map has to be transported along it,
which is `Subtype.ext` on the value.

## References

* [Stacks Project, Tag 0EIC](https://stacks.math.columbia.edu/tag/0EIC)
* [Stacks Project, Tag 0EH6](https://stacks.math.columbia.edu/tag/0EH6)
-/

@[expose] public noncomputable section

namespace Stacks.ReesAlgebra

universe u v w

/-- A monomial whose coefficient lies in the right power of `I ^ d` is an element of the Rees
algebra of `I ^ d`. -/
public lemma monomial_mem_reesAlgebra_pow {A : Type u} [CommRing A] (J : Ideal A) (n : ℕ)
    {g : A} (hg : g ∈ (J ^ n : Ideal A)) :
    Polynomial.monomial n g ∈ reesAlgebra J :=
  reesAlgebra.monomial_mem.mpr hg

/-- **A splitting on `I ^ d` kills the relations of a `B`-module `N`** when, for every monomial
`σ` and every degree `n`, the coefficient map `Stacks.ReesAlgebra.extendCoeff` of its extension
sends a vanishing combination `∑ₖ gₖ · xₖ = 0` with `gₖ ∈ (I ^ d) ^ n` to a vanishing
combination.

This is exactly what is needed to define a graded map on the subsheaf `I ^ (nd) F` of a sheaf of
modules by its values on products: the products generate, and this says the prescribed values
respect every relation among them. -/
public def KillsRelations (A : Type u) (B : Type v) (N : Type w) [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup N] [Module B N] (I : Ideal A) {r : ℕ} (d : ℕ)
    (ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A) : Prop :=
  ∀ (n : ℕ) (σ : Fin r →₀ ℕ) (m : ℕ) (g : Fin m → A)
    (hg : ∀ k, g k ∈ ((I ^ d : Ideal A) ^ n)) (x : Fin m → N),
    (∑ k, algebraMap A B (g k) • x k) = 0 →
    (∑ k, algebraMap A B (extendCoeff I d n ψ σ ⟨g k, hg k⟩) • x k) = 0

/-- **Relation-killing is inherited by a further enlargement of the exponent.** The coefficients
of the extension do not change, and the new relations are a subset of the old ones. -/
public lemma KillsRelations.of_restrictsSplitting {A : Type u} {B : Type v} {N : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup N] [Module B N]
    {I : Ideal A} {r d e : ℕ} {hde : d ≤ e}
    {ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A} {χ : Fin r → (I ^ e : Ideal A) →ₗ[A] A}
    (h : KillsRelations A B N I d ψ) (hres : RestrictsSplitting I hde ψ χ) :
    KillsRelations A B N I e χ := by
  intro n σ m g hg x hsum
  have hgd : ∀ k, g k ∈ ((I ^ d : Ideal A) ^ n) := fun k =>
    pow_pow_le_pow_pow I hde n (hg k)
  refine (Finset.sum_congr rfl fun k _ => ?_).trans (h n σ m g hgd x hsum)
  rw [extendCoeff_of_restrictsSplitting I hde ψ χ hres n σ (g k) (hg k) (hgd k)]

/-- **The relation-killing form of [Stacks, Tag 0EIC].** After enlarging `c` to a `d` and
adjusting the splitting accordingly, the coefficient maps
`Stacks.ReesAlgebra.extendCoeff` of the extension kill every relation among the elements of
`(I ^ d) ^ n` acting on a finite module over a Noetherian `A`-algebra. -/
public theorem exists_extendLinearMaps_kills_relations
    (A : Type u) (B : Type v) (N : Type w)
    [CommRing A]
    [CommRing B] [Algebra A B] [IsNoetherianRing B]
    [AddCommGroup N] [Module B N] [Module.Finite B N]
    (I : Ideal A) {r : ℕ} (f : Fin r → A)
    (hf : I = Ideal.span (Set.range f))
    (c : ℕ) (hc : 1 ≤ c)
    (φ : Fin r → (I ^ c : Ideal A) →ₗ[A] A)
    (hφ : ∀ g : (I ^ c : Ideal A), (∑ j, f j * φ j g) = (g : A)) :
    ∃ d : ℕ, ∃ hcd : c ≤ d, ∃ ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A,
      RestrictsSplitting I hcd φ ψ ∧
      (∀ g : (I ^ d : Ideal A), (∑ j, f j * ψ j g) = (g : A)) ∧
      KillsRelations A B N I d ψ := by
  classical
  obtain ⟨d, hcd, ψ, hres, hsplit, Ψ, ⟨_hgrade, hscalar, _heval⟩, _huniq⟩ :=
    exists_unique_extendLinearMaps_module A B N I f hf c hc φ hφ
  refine ⟨d, hcd, ψ, hres, hsplit, fun n σ m g hg x hsum => ?_⟩
  -- Each product `g k • x k` is a section of the degree-`n` piece of the Rees module.
  have hmemI : ∀ k, g k ∈ (I ^ (n * d) : Ideal A) := by
    intro k
    have h := hg k
    rwa [← pow_mul, mul_comm d n] at h
  have hpiece : ∀ k, algebraMap A B (g k) • x k ∈
      reesModulePiece (B := B) (N := N) I d n := by
    intro k
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hmemI k)
  set y : Fin m → reesModulePiece (B := B) (N := N) I d n :=
    fun k => ⟨algebraMap A B (g k) • x k, hpiece k⟩ with hy
  have hysum : (∑ k, y k) = 0 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    simpa [hy] using hsum
  -- The degree-`n` component of the graded map kills that sum.
  have hΨsum : (∑ k, Ψ n (y k)) = 0 := by
    rw [← map_sum, hysum, map_zero]
  -- Its coefficient at `σ` is the required relation.
  have hcoeff : ∀ k, (Ψ n (y k)) σ =
      algebraMap A B (extendCoeff I d n ψ σ ⟨g k, hg k⟩) • x k := by
    intro k
    have hmono : Polynomial.monomial n (g k) ∈ reesAlgebra (I ^ d) :=
      monomial_mem_reesAlgebra_pow (I ^ d) n (hg k)
    set p : reesAlgebra (I ^ d) := ⟨Polynomial.monomial n (g k), hmono⟩ with hp
    have hpcoeff : (p : Polynomial A).coeff n = g k := by
      simp [hp]
    have hpvanish : ∀ j : ℕ, j ≠ n → (p : Polynomial A).coeff j = 0 := by
      intro j hj
      simp [hp, Polynomial.coeff_monomial, Ne.symm hj]
    have hx : (algebraMap A B ((p : Polynomial A).coeff n)) • x k ∈
        reesModulePiece (B := B) (N := N) I d n := by
      rw [hpcoeff]
      exact hpiece k
    have hkey := hscalar n p hpvanish (x k) hx σ
    have hyk : (⟨(algebraMap A B ((p : Polynomial A).coeff n)) • x k, hx⟩ :
        reesModulePiece (B := B) (N := N) I d n) = y k :=
      Subtype.ext (show (algebraMap A B ((p : Polynomial A).coeff n)) • x k =
        algebraMap A B (g k) • x k by rw [hpcoeff])
    rw [hyk] at hkey
    rw [hkey, extendCoeff_apply I d n ψ σ (g k) (hg k) hmono]
  calc (∑ k, algebraMap A B (extendCoeff I d n ψ σ ⟨g k, hg k⟩) • x k)
      = ∑ k, (Ψ n (y k)) σ := Finset.sum_congr rfl fun k _ => (hcoeff k).symm
    _ = (∑ k, Ψ n (y k)) σ := by simp
    _ = 0 := by
      rw [hΨsum]
      simp

end Stacks.ReesAlgebra

end
