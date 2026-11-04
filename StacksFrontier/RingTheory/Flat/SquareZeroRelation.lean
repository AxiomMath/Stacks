module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Relations with square-zero coefficients in a flat module

Let `ρ : R →+* k` be a ring homomorphism onto a field, `M` a `k`-vector space and
`ι : M → R` an additive map whose values multiply as `ι v * a = ι (ρ a • v)`, so that the image
of `ι` is a square-zero ideal on which `R` acts through `ρ`, and which is injective. If `N` is a
flat `R`-module, `(b_j)` a basis of `M` and `∑_j ι(b_j) · n_j = 0` in `N`, then every `n_j` lies
in `ker ρ · N`.

This is the flatness input of the classification of first order deformations of a module over
an `R` of the shape `k[M]`, read without fixing an identification of `R` with the trivial
square-zero extension. The proof is the equational criterion of flatness: the relation is
trivial, so the `n_j` are combinations of finitely many elements with coefficients `a_{jl}`
satisfying `∑_j ι(b_j) a_{jl} = 0`, that is `ι(∑_j ρ(a_{jl}) b_j) = 0`; injectivity of `ι` and
linear independence of the `b_j` force `ρ(a_{jl}) = 0`.

## Main results

* `Module.Flat.mem_ker_smul_top_of_sum_smul_eq_zero`.
-/

@[expose] public section

namespace Module.Flat

variable {R : Type*} [CommRing R] {k : Type*} [Field k] (ρ : R →+* k)
  {M : Type*} [AddCommGroup M] [Module k M] (ι : M →+ R)

/-- **In a flat module, a relation whose coefficients are a basis of a square-zero ideal has all
its terms in `ker ρ · N`.** -/
theorem mem_ker_smul_top_of_sum_smul_eq_zero (hinj : Function.Injective ι)
    (hmul : ∀ (v : M) (a : R), ι v * a = ι (ρ a • v))
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Flat R N]
    {J : Type*} [Fintype J] (b : Module.Basis J k M) (n : J → N)
    (h : ∑ j, ι (b j) • n j = 0) (j : J) :
    n j ∈ (RingHom.ker ρ) • (⊤ : Submodule R N) := by
  obtain ⟨l, a, y, hx, hrel⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h
  have hfst : ∀ i l', ρ (a i l') = 0 := by
    intro i l'
    have h2 : ι (∑ i, ρ (a i l') • b i) = 0 := by
      rw [map_sum]
      simp_rw [← hmul]
      exact hrel l'
    have h3 := hinj (h2.trans (map_zero ι).symm)
    exact (Fintype.linearIndependent_iff.mp b.linearIndependent (fun i => ρ (a i l')) h3) i
  rw [hx j]
  refine Submodule.sum_mem _ fun l' _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
  exact hfst j l'

end Module.Flat

end
